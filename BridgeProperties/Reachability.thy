theory Reachability
imports Main BridgeDefinition.Definition BridgeDefinition.TokenDepositState BridgeDefinition.BridgeState
begin

section \<open>Steps\<close>

(* FIXME: clarify block numbers and messages *)
definition message where 
  "message sender' val' = \<lparr> sender = sender', val = val' \<rparr>"

lemma senderMessage [simp]:
  shows "sender (message sender' val') = sender'"
  by (simp add: message_def)

context HashProofVerifier
begin

datatype Step = 
  DEPOSIT address address uint256 address uint256 (* address caller ID token amount *)
| CLAIM address address uint256 address uint256 bytes (* address caller ID token amount proof *) 
| BURN address address uint256 address uint256 (* address caller ID token amount *)
| RELEASE address address uint256 address uint256 bytes (* address caller ID token amount proof *)
| TRANSFER address address address address uint256 (* address caller receiver token amount *)
| UPDATE address bytes32 (* address stateRoot *)
| CANCEL_WD address address uint256 address uint256 bytes (* addres caller ID token amount proof *)
| WITHDRAW_WD address address address uint256 bytes (* address caller token amount proof *)

primrec executeStep :: "Contracts \<Rightarrow> nat \<Rightarrow> Block \<Rightarrow> Step \<Rightarrow> Status \<times> Contracts" where
  "executeStep contracts blockNum block (DEPOSIT address caller ID token amount) = 
    callDeposit contracts address block (message caller amount) ID token amount"
| "executeStep contracts blockNum block (CLAIM address caller ID token amount proof) = 
    callClaim contracts address (message caller amount) ID token amount proof"
| "executeStep contracts blockNum block (BURN address caller ID token amount) = 
    callWithdraw contracts address (message caller 0) ID token amount"
| "executeStep contracts blockNum block (RELEASE address caller ID token amount proof) = 
    callRelease contracts address (message caller 0) ID token amount proof"  
| "executeStep contracts blockNum block (TRANSFER address caller receiver token amount) = 
    callTransfer contracts address caller receiver token amount"
| "executeStep contracts blockNum block (UPDATE address stateRoot) = 
    callUpdate contracts address block blockNum stateRoot"
| "executeStep contracts blockNum block (CANCEL_WD address caller ID token amount proof) = 
    callCancelDepositWhileDead contracts address (message caller 0) block ID token amount proof"
| "executeStep contracts blockNum block (WITHDRAW_WD address caller token amount proof) = 
    callWithdrawWhileDead contracts address (message caller 0) block token amount proof"

inductive reachable :: "Contracts \<Rightarrow> Contracts \<Rightarrow> Step list \<Rightarrow> bool" where
  reachable_base: "\<And> contracts. reachable contracts contracts []"
| reachable_step: "\<And> contracts contracts' blockNum block step. 
                       \<lbrakk>reachable contracts contracts' steps; 
                        executeStep contracts' blockNum block step = (Success, contracts'')\<rbrakk> \<Longrightarrow> 
                        reachable contracts contracts'' (step # steps)" 

lemma reachableCons':
  assumes "reachable contracts contracts' (step # steps)"
  obtains contracts'' blockNum block where 
   "reachable contracts contracts'' steps"
   "executeStep contracts'' blockNum block step = (Success, contracts')"
  by (smt (verit, best) assms list.discI list.inject reachable.cases)

lemma reachableSingleton:
  assumes "reachable contracts contracts' [step]"
  obtains block blockNum where 
    "executeStep contracts block blockNum step = (Success, contracts')"
  using assms
  by (smt (verit, ccfv_SIG) neq_Nil_conv reachable.cases reachableCons')

lemma reachableTrans:
  assumes "reachable s2 s3 steps2" "reachable s1 s2 steps1"
  shows "reachable s1 s3 (steps2 @ steps1)"
  using assms
  by (induction s2 s3 steps2 rule: reachable.induct, auto simp add: reachable_step)

lemma reachableAppend:
  assumes "reachable contracts contracts' (steps1 @ steps2)"
  obtains c where "reachable contracts c steps2" "reachable c contracts' steps1"
  using assms
proof (induction steps1 arbitrary: contracts contracts' rule: list.induct)
  case Nil
  then show ?case
    using reachable_base by auto
next
  case (Cons step steps1)
  then show ?case
    by (smt (verit, ccfv_threshold) reachable_step add_is_0 append_Cons length_0_conv list.inject list.size(4) nat.simps(3) reachable.cases)
qed

lemma reachableStepInSteps:
  assumes "reachable contracts contracts' steps"
  assumes "step \<in> set steps"
  obtains c1 c2 block blockNum steps1 steps2 where
  "reachable contracts c1 steps2" 
  "executeStep c1 blockNum block step = (Success, c2)"
  "reachable c2 contracts' steps1"
  "steps = steps1 @ [step] @ steps2"
proof-
  obtain steps1 steps2 where *: "steps = steps1 @ [step] @ steps2"
    using \<open>step \<in> set steps\<close>
    by (metis append_Cons append_self_conv2 in_set_conv_decomp_last)
  
  moreover

  obtain c2 where
    "reachable contracts c2 ([step] @ steps2)" 
    "reachable c2 contracts' steps1"
    using \<open>reachable contracts contracts' steps\<close> * reachableAppend[of contracts contracts' "steps1" "[step] @ steps2"]
    by auto
  
  moreover

  obtain c1 blockNum block
    where "reachable contracts c1 steps2" "executeStep c1 blockNum block step = (Success, c2)"
    using \<open>reachable contracts c2 ([step] @ steps2)\<close> reachableCons'[of contracts c2 step steps2]
    by auto

  ultimately
  show ?thesis
    using  that 
    by auto
qed

lemma reachableRepeatedStepNonDistinct:
  assumes "reachable contracts contracts' (step # steps)"
  assumes "step \<in> set steps"
  obtains c1 c2 c3 blockNum1 block1 blockNum2 block2 steps1 steps2 where
  "reachable contracts c1 steps2" 
  "executeStep c1 blockNum1 block1 step = (Success, c2)"
  "reachable c2 c3 steps1"
  "executeStep c3 blockNum2 block2 step = (Success, contracts')"
  "steps = steps1 @ [step] @ steps2"
  using assms
  by (smt (verit, ccfv_threshold) append_Cons append_self_conv2 in_set_conv_decomp_first reachableCons' reachableAppend)

(* --------------------------------------------------------------------------------- *)

subsection \<open>Split steps into steps issued by one caller and steps issued by other callers\<close>

primrec isCaller where
  "isCaller caller (DEPOSIT address' caller' ID' token' amount') \<longleftrightarrow> caller' = caller"
| "isCaller caller (CLAIM address' caller' ID' token' amount' proof') \<longleftrightarrow> caller' = caller"
| "isCaller caller (BURN address' caller' ID' token' amount') \<longleftrightarrow> caller' = caller"
| "isCaller caller (RELEASE address' caller' ID' token' amount' proof') \<longleftrightarrow> caller' = caller"
| "isCaller caller (TRANSFER address' caller' receiver' token' amount') \<longleftrightarrow> caller' = caller"
| "isCaller caller (UPDATE address' stateRoot') \<longleftrightarrow> False"
| "isCaller caller (CANCEL_WD address' caller' ID' token' amount' proof') \<longleftrightarrow> caller' = caller"
| "isCaller caller (WITHDRAW_WD address' caller' token' amount' proof') \<longleftrightarrow> caller' = caller"

text \<open>A target state is reachable from the source state by only applying steps given by a given callers\<close>
definition reachableCaller :: "address \<Rightarrow> Contracts \<Rightarrow> Contracts \<Rightarrow> Step list \<Rightarrow> bool" where
  "reachableCaller caller contracts contracts' stepsCaller \<longleftrightarrow>
    reachable contracts contracts' stepsCaller \<and>
    (\<forall> step \<in> set stepsCaller. isCaller caller step)"

text \<open>A target state is reachable from the source state by only applying steps given by other callers\<close>
definition reachableOtherCaller :: "address \<Rightarrow> Contracts \<Rightarrow> Contracts \<Rightarrow> Step list \<Rightarrow> bool" where
  "reachableOtherCaller caller contracts contracts' stepsOther \<longleftrightarrow>
    reachable contracts contracts' stepsOther \<and>
    (\<forall> step \<in> set stepsOther. \<not> isCaller caller step)"

text \<open>A target state is reachable from the source state by alternatingly executing steps given by other callers and steps given by the given caller\<close>
inductive reachableInterleaved :: "address \<Rightarrow> Contracts \<Rightarrow> Contracts \<Rightarrow> Step list \<Rightarrow> Step list list \<Rightarrow> bool" where
  reachableInterleaved_base:
   "\<And> caller contracts. reachableInterleaved caller contracts contracts [] []"
 | reachableInterleaved_step: 
   "\<And> caller contracts contractsS' block blockNum contractsS'' contracts'. 
       \<lbrakk> reachableInterleaved caller contracts contractsS' stepsCaller stepListsOther;
         reachableOtherCaller caller contractsS' contractsS'' stepsOther;
         isCaller caller stepCaller;
         executeStep contractsS'' block blockNum stepCaller = (Success, contracts') \<rbrakk> \<Longrightarrow> 
         reachableInterleaved caller contracts contracts' (stepCaller # stepsCaller) (stepsOther # stepListsOther)"

lemma reachableInterleavedLength:
  assumes "reachableInterleaved caller contracts contracts' stepsCaller stepListsOther"
  shows "length stepsCaller = length stepListsOther"
  using assms
  by (induction caller contracts contracts' stepsCaller stepListsOther rule: reachableInterleaved.induct) auto

text \<open>Interleaving of steps given by other callers and this caller. 
      For example interleaveSteps [a, b] [[c, d], [e, f, g]] = [c, d, a, e, f, g, b].\<close>
abbreviation interleaveSteps where
  "interleaveSteps steps stepsListsOther \<equiv> concat (map2 (#) steps stepsListsOther)"

lemma setInterleaveSteps:
  assumes "length stepsCaller = length stepListsOther"
  shows "set (interleaveSteps stepsCaller stepListsOther) =
         set stepsCaller \<union> set (concat stepListsOther)"
  using assms
  apply auto (* FIXME: methods after auto *)
     apply (meson set_zip_leftD)
    apply (meson set_zip_rightD)
   apply (metis in_set_impl_in_set_zip1)
  apply (metis in_set_impl_in_set_zip2)
  done

lemma reachableInterleavedReachable:
  assumes "reachableInterleaved caller contracts contracts' stepsCaller stepListsOther"
  shows "reachable contracts contracts' (interleaveSteps stepsCaller stepListsOther)"
  using assms
proof (induction caller contracts contracts' stepsCaller stepListsOther rule: reachableInterleaved.induct)
  case (reachableInterleaved_base caller contracts)
  show ?case
    using reachable_base
    by auto
next
  case (reachableInterleaved_step steps stepListsOther stepsOther step caller contracts contractsS' block blockNum contractsS'' contracts')
  then show ?case
  proof-
    have "reachable contractsS' contracts' (step # stepsOther)"
      using reachableInterleaved_step.hyps reachableOtherCaller_def reachable_step 
      by blast
    moreover
    have "interleaveSteps (step # steps) (stepsOther # stepListsOther) = 
          (step # stepsOther) @ interleaveSteps steps stepListsOther"
      by auto
    ultimately show ?thesis
      using reachableInterleaved_step.IH reachableTrans
      by fastforce
  qed
qed

lemma reachableInterleavedCaller:
  assumes "reachableInterleaved caller contracts contracts' stepsCaller stepListsOther"
  shows "\<forall> step \<in> set stepsCaller. isCaller caller step"
  using assms
  by (induction caller contracts contracts' stepsCaller stepListsOther rule: reachableInterleaved.induct) auto

lemma reachableInterleavedOtherCaller:
  assumes "reachableInterleaved caller contracts contracts' stepsCaller stepListsOther"
  shows "\<forall> step \<in> set (concat stepListsOther). \<not> isCaller caller step"
  using assms
  by (induction caller contracts contracts' stepsCaller stepListsOther rule: reachableInterleaved.induct) (auto simp add: reachableOtherCaller_def)

lemma reachableInterleavedCons:
  assumes "reachableInterleaved caller contracts contracts' (stepCaller # stepsCaller) stepListsOther"
  obtains contracts'' stepsOther stepListsOther' where
   "reachableInterleaved caller contracts contracts'' stepsCaller stepListsOther'"
   "reachableInterleaved caller contracts'' contracts' [stepCaller] [stepsOther]"
   "stepListsOther = stepsOther # stepListsOther'"
  using assms
  by (smt (verit) list.distinct(1) list.inject reachableInterleaved.simps)

lemma reachableInterleavedTrans:
  assumes "reachableInterleaved caller contracts' contracts'' stepsCaller'' stepListsOther''"
  assumes "reachableInterleaved caller contracts contracts' stepsCaller' stepListsOther'"
  shows "reachableInterleaved caller contracts contracts'' (stepsCaller'' @ stepsCaller') (stepListsOther'' @ stepListsOther')"
  using assms
  using reachableInterleaved_step
  by (induction caller contracts' contracts'' stepsCaller'' stepListsOther'' rule: reachableInterleaved.induct) auto

lemma reachableInterleavedAppend:
  assumes "reachableInterleaved caller contracts contracts' (stepsCaller' @ stepsCaller) stepListsOther"
  shows "\<exists> contracts'' stepListsOther1 stepListsOther2.
    reachableInterleaved caller contracts contracts'' stepsCaller stepListsOther1 \<and>
    reachableInterleaved caller contracts'' contracts' stepsCaller' stepListsOther2 \<and> 
    stepListsOther = stepListsOther2 @ stepListsOther1"
  using assms
proof (induction stepsCaller' arbitrary: contracts contracts' stepListsOther rule: list.induct)
  case Nil
  then show ?case
    using reachableInterleaved_base by fastforce
next
  case (Cons stepCaller stepsCaller')
  obtain contracts'' stepListsOther' stepsOther where *: 
  "reachableInterleaved caller contracts contracts'' (stepsCaller' @ stepsCaller) stepListsOther'"
  "reachableInterleaved caller contracts'' contracts' [stepCaller] [stepsOther]"
  "stepListsOther = stepsOther # stepListsOther'"
    using reachableInterleavedCons Cons
    by (metis Cons_eq_appendI)
  obtain contracts1 stepListsOther1 stepListsOther2 where
   "reachableInterleaved caller contracts contracts1 stepsCaller stepListsOther1"
   "reachableInterleaved caller contracts1 contracts'' stepsCaller' stepListsOther2"
   "stepListsOther' = stepListsOther2 @ stepListsOther1"
    using Cons.IH[of contracts contracts'' stepListsOther'] *(1)
    by auto
  then show ?case
    using *(2-3)
    by (smt (z3) Cons_eq_appendI append_Nil reachableInterleavedTrans)
qed

text \<open>The given step can always be executed (whatever steps preceede it)\<close>
definition executableStep :: "address \<Rightarrow> Contracts \<Rightarrow> Step \<Rightarrow> bool" where
  "executableStep caller contracts step \<longleftrightarrow> 
     (\<forall> contracts' stepsOther.
         reachableOtherCaller caller contracts contracts' stepsOther \<longrightarrow> 
         (\<forall> block blockNum. fst (executeStep contracts' block blockNum step) = Success))" (* FIXME: block *)

text \<open>The given step can always be executed (whatever steps are interleaved with them)\<close>
fun executableSteps :: "address \<Rightarrow> Contracts \<Rightarrow> Step list \<Rightarrow> bool" where
  "executableSteps caller contracts [] = True"
| "executableSteps caller contracts (stepCaller # stepsCaller) \<longleftrightarrow> 
     executableSteps caller contracts stepsCaller \<and>
     (\<forall> contracts' stepListsOther. 
        reachableInterleaved caller contracts contracts' stepsCaller stepListsOther \<longrightarrow> 
              executableStep caller contracts' stepCaller)"

lemma executableStepsReachableInterleaved:
  assumes "executableSteps caller contracts stepsCaller"
          "\<forall> step \<in> set stepsCaller. isCaller caller step"
  shows "\<exists> contracts' stepListsOther. reachableInterleaved caller contracts contracts' stepsCaller stepListsOther"
  using assms
proof (induction stepsCaller arbitrary: contracts)
  case Nil
  then show ?case
    using reachableInterleaved_base[of caller contracts]
    by auto
next
  case (Cons stepCaller stepsCaller)
  obtain contracts' stepListsOther where
    "reachableInterleaved caller contracts contracts' stepsCaller stepListsOther"
    using Cons.IH[of contracts] Cons.prems
    using executableSteps.simps(2)
    by (meson list.set_intros(2))
  then have "executableStep caller contracts' stepCaller"
    using Cons.prems
    by auto
  then obtain block blockNum where "fst (executeStep contracts' block blockNum stepCaller) = Success" (* FIXME: block *)
    by (metis empty_iff executableStep_def list.set(1) reachable.simps reachableOtherCaller_def)
  then obtain contracts'' where "executeStep contracts' block blockNum stepCaller = (Success, contracts'')"
    by (metis fst_conv surj_pair)
  then have "reachableInterleaved caller contracts contracts'' (stepCaller # stepsCaller) ([] # stepListsOther)"
    using \<open>reachableInterleaved caller contracts contracts' stepsCaller stepListsOther\<close> Cons.prems
    using reachableInterleaved_step[of caller contracts contracts' stepsCaller stepListsOther contracts' "[]" stepCaller block blockNum contracts'']
    by (simp add: reachableOtherCaller_def reachable_base)
  then show ?case
    by blast
qed

lemma executableStepsAppend:
  assumes "executableSteps caller contracts steps"
  assumes "\<forall> contracts' stepListsOther. reachableInterleaved caller contracts contracts' steps stepListsOther \<longrightarrow> 
           executableSteps caller contracts' steps'"
  shows "executableSteps caller contracts (steps' @ steps)"
  using assms
proof (induction steps')
  case Nil
  then show ?case
    by simp
next
  case (Cons step steps')
  have "executableSteps caller contracts (steps' @ steps)"
    using Cons executableSteps.simps(2) by blast
  moreover
  {
    fix contracts' stepListsOther
    assume "executableSteps caller contracts (steps' @ steps)" 
           "reachableInterleaved caller contracts contracts' (steps' @ steps) stepListsOther"
    then obtain contracts'' stepListsOther1 stepsOther2 where
    "reachableInterleaved caller contracts contracts'' steps stepListsOther1" 
    "reachableInterleaved caller contracts'' contracts' steps' stepsOther2" 
    "stepListsOther = stepsOther2 @ stepListsOther1"
      using reachableInterleavedAppend
      by blast
    then have "executableSteps caller contracts'' (step # steps')"
      using Cons.prems(2)[rule_format, of contracts'' stepListsOther1]
      by auto
    then have "executableStep caller contracts' step"
      using \<open>reachableInterleaved caller contracts'' contracts' steps' stepsOther2\<close> 
      by auto
  }
  ultimately 
  show ?case
    by auto
qed

end
(* --------------------------------------------------------------------------------- *)

context HashProofVerifier
begin

lemma reachableITokenPairs [simp]:
  assumes "reachable contracts contracts' steps"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableIProofVerifier [simp]:
  assumes "reachable contracts contracts' steps"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableBridgeDeposit [simp]:
  assumes "reachable contracts contracts' steps"
  shows "depositAddressB contracts' address = depositAddressB contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableBridgeTokenPairs [simp]:
  assumes "reachable contracts contracts' steps"
  shows "tokenPairsAddressB contracts' address = tokenPairsAddressB contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableBridgeStateOracle [simp]:
  assumes "reachable contracts contracts' steps"
  shows "stateOracleAddressB contracts' address = stateOracleAddressB contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableBridgeProofVerifier [simp]:
  assumes "reachable contracts contracts' steps"
  shows "proofVerifierAddressB contracts' address = proofVerifierAddressB contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableDepositStateOracle [simp]:
  assumes "reachable contracts contracts' steps"
  shows "stateOracleAddressTD contracts' address = stateOracleAddressTD contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableBridgeMintedToken [simp]:
  assumes "reachable contracts contracts' steps"
  shows "mintedTokenB contracts' bridgeAddress token =
         mintedTokenB contracts bridgeAddress token"
  using assms
  unfolding Let_def
  by simp

lemma reachableOriginalToMinted [simp]:
  assumes "reachable contracts contracts' steps" 
        "callOriginalToMinted contracts tokenPairsAddr original = (Success, minted)"
  shows "callOriginalToMinted contracts' tokenPairsAddr original = (Success, minted)"
  using assms
  unfolding callOriginalToMinted_def
  by simp

lemma reachableBridgeState:
  assumes "reachable contracts contracts' steps"
  assumes "bridgeState contracts address \<noteq> None"
  shows "bridgeState contracts' address \<noteq> None"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using callClaimBridgeState(2)[of contracts'] callClaimOtherAddress
      using reachable_step
      by (metis executeStep.simps(2))
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using callWithdrawBridgeState(2)[of contracts'] callWithdrawOtherAddress
      using reachable_step
      by (metis executeStep.simps(3))
  qed auto
qed

lemma reachableTokenDepositState:
  assumes "reachable contracts contracts' steps"
  assumes "tokenDepositState contracts address \<noteq> None"
  shows "tokenDepositState contracts' address \<noteq> None"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachable_step
      using callDepositOtherAddress callDepositE
      by (metis executeStep.simps(1))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callWithdrawWhileDeadE callWithdrawWhileDeadOtherAddress 
      by (metis executeStep.simps(8))
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callCancelDepositWhileDeadE callCancelDepositWhileDeadOtherAddress 
      by (metis executeStep.simps(7))
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callReleaseE callReleaseOtherAddress
      by (metis executeStep.simps(4))
  qed auto
qed

lemma reachableERC20State:
  assumes "reachable contracts contracts' steps"
  assumes "ERC20state contracts token \<noteq> None"
  shows "ERC20state contracts' token \<noteq> None"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof(cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachable_step callDepositERC20state(2) callDepositOtherToken
      by (cases "token = token'") auto
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadOtherToken
      by (metis executeStep.simps(7))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callWithdrawWhileDeadERC20state(2) callWithdrawWhileDeadOtherToken
      by (metis executeStep.simps(8))
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callReleaseERC20state(2) callReleaseOtherToken
      by (metis executeStep.simps(4))
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step callClaimERC20state
      by simp
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachable_step callWithdrawERC20state 
      by simp
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using reachable_step callTransferERC20state
      by simp
  qed auto
qed

lemma reachableDeadState:
  assumes "reachable contracts contracts' steps"
  assumes "deadStateTD contracts tokenDepositAddress = stateRoot"
  assumes "stateRoot \<noteq> 0"
  shows "deadStateTD contracts' tokenDepositAddress = stateRoot"
  using assms
proof (induction contracts contracts' steps)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachable_step callDepositInDeadState
      by (metis executeStep.simps(1))
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step callCancelDepositWhileDeadInDeadState
      by (metis executeStep.simps(7))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachable_step callWithdrawWhileDeadInDeadState
      by (metis executeStep.simps(8))
  qed auto
qed

end

context HashProofVerifier
begin

text \<open>Dead state is never unset\<close>
lemma reachableBridgeDead:
  assumes "reachable contracts contracts' steps"
  assumes "bridgeDead contracts tokenDepositAddress"
  shows "bridgeDead contracts' tokenDepositAddress"
  using assms
  using reachableDeadState
  by auto

lemma BridgeDiesDeadState:
  assumes "\<not> bridgeDead contracts tokenDepositAddress"
  assumes "executeStep contracts block blockNum step = (Success, contracts')"
  assumes "bridgeDead contracts' tokenDepositAddress"
  shows "deadStateTD contracts' tokenDepositAddress = lastStateTD contracts tokenDepositAddress"
  using assms
proof (cases step)
  case (DEPOSIT address' caller' ID' token' amount')
  then show ?thesis
    using assms
    using callDepositOtherAddress callDepositNotBridgeDead'
    by (metis executeStep.simps(1))
next
  case (CANCEL_WD address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms
    using callCancelDepositWhileDeadOtherAddress callCancelDepositWhileDeadSetsDeadState
    by (metis executeStep.simps(7))
next
  case (WITHDRAW_WD address' caller' token' amount' proof')
  then show ?thesis
    using assms
    using callWithdrawWhileDeadOtherAddress callWithdrawWhileDeadSetsDeadState 
    by (metis executeStep.simps(8))
qed auto


lemma executeSameStepBridgeDead:
  assumes "bridgeDead contracts1' tokenDepositAddress = bridgeDead contracts2' tokenDepositAddress"
  assumes "executeStep contracts1' blockNum1 block1 step = (Success, contracts1)"
  assumes "executeStep contracts2' blockNum2 block2 step = (Success, contracts2)"
  shows "bridgeDead contracts1 tokenDepositAddress = bridgeDead contracts2 tokenDepositAddress"
  using assms
proof (cases step)
  case (DEPOSIT address caller ID token amount)
  then show ?thesis
    using assms
    by (metis callDepositNotBridgeDead' callDepositOtherAddress executeStep.simps(1))
next
  case (CANCEL_WD address caller ID token amount "proof")
  then show ?thesis
    using assms
    by (metis (no_types, lifting) callCancelDepositWhileDeadBridgeDead callCancelDepositWhileDeadOtherAddress executeStep.simps(7))
next
  case (WITHDRAW_WD address caller token amount "proof")
  then show ?thesis
    using assms
    by (metis (no_types, lifting) HashProofVerifier.executeStep.simps(8) HashProofVerifier_axioms callWithdrawWhileDeadBridgeDead callWithdrawWhileDeadOtherAddress)
qed auto

lemma reachableSameStepsBridgeDead:
  assumes "reachable contracts contracts1 steps"
  assumes "reachable contracts contracts2 steps"
  shows "bridgeDead contracts1 tokenDepositAddress = bridgeDead contracts2 tokenDepositAddress"
  using assms
proof (induction contracts contracts1 steps arbitrary: contracts2 rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    using reachable.cases by blast
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then obtain contracts0 blockNum' block' where 
   "reachable contracts contracts0 steps"
    "executeStep contracts0 blockNum' block' step = (Success, contracts2)"
    using reachableCons' by blast
  then have "bridgeDead contracts0 tokenDepositAddress = bridgeDead contracts' tokenDepositAddress"
    using reachable_step.IH
    by simp
  then show ?case
    using \<open>executeStep contracts0 blockNum' block' step = (Success, contracts2)\<close>
    using \<open>executeStep contracts' blockNum block step = (Success, contracts'')\<close>
    using executeSameStepBridgeDead by blast
qed

end

(* --------------------------------------------------------------------------------- *)

context HashProofVerifier
begin

lemma reachableFiniteBalances:
  assumes "reachable contracts contracts' steps"
  assumes "finiteBalances contracts token"
  shows "finiteBalances contracts' token"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case by (simp add: finiteBalances_def)
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachable_step
      using callDepositFiniteBalances
      by (metis executeStep.simps(1)) 
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callClaimFiniteBalances
      by (metis executeStep.simps(2))
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callCancelDepositWhileDeadFiniteBalances
      by (metis executeStep.simps(7))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callWithdrawWhileDeadFiniteBalances
      by (metis executeStep.simps(8))
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachable_step
      using callUpdateFiniteBalances
      by (metis executeStep.simps(6))
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using reachable_step
      using callTransferFiniteBalances
      by (metis executeStep.simps(5))
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachable_step
      using callWithdrawFiniteBalances
      by (metis executeStep.simps(3))
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callReleaseFiniteBalances
      by (metis executeStep.simps(4))
  qed  
qed

end

(* ----------------------------------------------------------------------------------- *)

context HashProofVerifier
begin

text \<open>Conditions that are necessary for bridge functioning (address memorized in contracts should be
      synchronized and all constructors must have been called)\<close>
definition properSetup :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> bool" where
  "properSetup contracts tokenDepositAddress bridgeAddress \<longleftrightarrow> 
    (let stateTokenDeposit = tokenDepositState contracts tokenDepositAddress;
         stateBridge = bridgeState contracts bridgeAddress;
         stateTokenPairs = tokenPairsState contracts (BridgeState.tokenPairs (the stateBridge))
      in stateTokenDeposit \<noteq> None \<and>
         stateBridge \<noteq> None \<and>
         BridgeState.deposit (the stateBridge) = tokenDepositAddress \<and>
         TokenDepositState.bridge (the stateTokenDeposit) = bridgeAddress \<and>
         TokenDepositState.stateOracle (the stateTokenDeposit) =
         BridgeState.stateOracle (the stateBridge) \<and>
         TokenDepositState.tokenPairs (the stateTokenDeposit) =
         BridgeState.tokenPairs (the stateBridge) \<and>
         TokenDepositState.proofVerifier (the stateTokenDeposit) =
         BridgeState.proofVerifier (the stateBridge) \<and>
         stateOracleState contracts (BridgeState.stateOracle (the stateBridge)) \<noteq> None \<and>
         proofVerifierState contracts (BridgeState.proofVerifier (the stateBridge)) \<noteq> None \<and>
         tokenPairsState contracts (BridgeState.tokenPairs (the stateBridge)) \<noteq> None)"

lemma properSetup_stateOracleAddress:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows "stateOracleAddressTD contracts tokenDepositAddress = stateOracleAddressB contracts bridgeAddress"
  using assms
  unfolding properSetup_def
  by (simp add: Let_def)

lemma properSetup_getLastState:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows "lastStateB contracts bridgeAddress = lastStateTD contracts tokenDepositAddress"
  using assms
  by (simp add: properSetup_stateOracleAddress)

lemma callDepositProperSetup [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  by (smt (verit, ccfv_SIG) Hash.callDepositOtherAddress Hash.callDepositOtherToken callDepositBridge callDepositProofVerifier callDepositE callDepositERC20state(2) callDepositIBridge callDepositIProofVerifier callDepositIStateOracle callDepositITokenPairs callDepositStateOracle callDepositTokenPairs properSetup_def)

lemma callClaimProperSetup [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def Let_def
  by (smt (verit, ccfv_SIG) callClaimBridgeState(2) callClaimDeposit callClaimIProofVerifier callClaimIStateOracle callClaimITokenDeposit callClaimITokenPairs callClaimOtherAddress callClaimProofVerifier callClaimStateOracle callClaimTokenPairs)

lemma callUpdateProperSetup [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  by (smt (verit, best) callUpdateIBridge callUpdateIERC20 callUpdateIProofVerifier callUpdateITokenDeposit callUpdateITokenPairs callUpdateOtherAddress callUpdateStateOracleState(2))

lemma callCancelDepositWhileDeadProperSetup [simp]:
  assumes "callCancelDepositWhileDead contracts address block msg ID token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  by (smt (z3) callCancelDepositWhileDeadOtherToken callCancelDepositWhileDeadBridge callCancelDepositWhileDeadProofVerifier callCancelDepositWhileDeadE callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadIBridge callCancelDepositWhileDeadIProofVerifier callCancelDepositWhileDeadIStateOracle callCancelDepositWhileDeadITokenPairs callCancelDepositWhileDeadOtherAddress callCancelDepositWhileDeadStateOracle callCancelDepositWhileDeadTokenPairs)

lemma callWithdrawWhileDeadProperSetup [simp]:
  assumes "callWithdrawWhileDead contracts address block msg token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  by (smt (z3) callWithdrawWhileDeadBridge callWithdrawWhileDeadProofVerifier callWithdrawWhileDeadE callWithdrawWhileDeadERC20state(2) callWithdrawWhileDeadIBridge callWithdrawWhileDeadIProofVerifier callWithdrawWhileDeadIStateOracle callWithdrawWhileDeadITokenPairs callWithdrawWhileDeadOtherAddress callWithdrawWhileDeadOtherToken callWithdrawWhileDeadStateOracle callWithdrawWhileDeadTokenPairs)

lemma callWithdrawProperSetup [simp]:
  assumes "callWithdraw contracts address msg ID token amount = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  by (smt (z3) callWithdrawBridgeState(2) callWithdrawDeposit callWithdrawIProofVerifier callWithdrawIStateOracle callWithdrawITokenDeposit callWithdrawITokenPairs callWithdrawOtherAddress callWithdrawProofVerifier callWithdrawStateOracle callWithdrawTokenPairs)


lemma callTransferProperSetup [simp]:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  using callTransferIBridge callTransferIProofVerifier callTransferIStateOracle callTransferITokenDeposit callTransferITokenPairs by presburger

lemma callReleaseProperSetup [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  by (smt (verit, best) callReleaseBridgeAddress callReleaseE callReleaseIBridge callReleaseIProofVerifier callReleaseIStateOracle callReleaseITokenPairs callReleaseOtherAddress callReleaseProofVerifier callReleaseStateOracleAddress callReleaseTokenPairs) 

lemma properSetupReachable [simp]:
  assumes "reachable contracts contracts' steps"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
proof (induction contracts contracts' steps)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

abbreviation totalMinted where
  "totalMinted contracts bridgeAddress token \<equiv>
   totalTokenBalance contracts (mintedTokenB contracts bridgeAddress token)"

definition properToken :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> bool" where
  "properToken contracts tokenDepositAddress bridgeAddress token \<longleftrightarrow>
    (let stateBridge = bridgeState contracts bridgeAddress;
         stateTokenPairs = tokenPairsState contracts (BridgeState.tokenPairs (the stateBridge))
      in stateTokenPairs \<noteq> None \<and>
         ERC20state contracts token \<noteq> None \<and>
         getMinted (the stateTokenPairs) token \<noteq> 0 \<and>
         getMinted (the stateTokenPairs) token \<noteq> token \<and>
         ERC20state contracts (getMinted (the stateTokenPairs) token) \<noteq> None)"

lemma callDepositProperToken [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  by (metis (no_types, lifting) Hash.callDepositIBridge Hash.callDepositITokenPairs Hash.callDepositOtherToken callDepositERC20state(2) properToken_def)

lemma callClaimProperToken [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def Let_def
  by (smt (verit, best) callClaimERC20state callClaimITokenPairs callClaimOtherAddress callClaimTokenPairs)

lemma callUpdateProperToken [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  using callUpdateIBridge callUpdateIERC20 callUpdateITokenPairs 
  by presburger

lemma callReleaseProperToken [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  by (metis callReleaseERC20state(2) callReleaseIBridge callReleaseITokenPairs callReleaseOtherToken)

lemma callTransferProperToken [simp]:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  by (metis callTransferERC20state callTransferIBridge callTransferITokenPairs)

lemma callWithdrawProperToken [simp]:
  assumes "callWithdraw contracts address caller receiver token amount = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  by (smt (verit, best) callWithdrawERC20state callWithdrawITokenPairs callWithdrawOtherAddress callWithdrawTokenPairs)

lemma callCancelDepositWhileDeadProperToken [simp]:
  assumes "callCancelDepositWhileDead contracts address block msg ID token amount proof = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  by (metis callCancelDepositWhileDeadOtherToken callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadIBridge callCancelDepositWhileDeadITokenPairs)

lemma callWithdrawWhileDeadProperToken [simp]:
  assumes "callWithdrawWhileDead contracts address block msg token amount proof = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  by (metis callWithdrawWhileDeadERC20state(2) callWithdrawWhileDeadIBridge callWithdrawWhileDeadITokenPairs callWithdrawWhileDeadOtherToken)

lemma properTokenReachable [simp]:
  assumes "reachable contracts contracts' steps"
  assumes "properToken contracts tokenDepositAddress bridgeAddress token"
  shows "properToken contracts' tokenDepositAddress bridgeAddress token"
  using assms
proof (induction contracts contracts' steps)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

end

end