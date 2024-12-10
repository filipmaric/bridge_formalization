theory Reachability
imports Main Definition TokenDepositState BridgeState
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
| UPDATE address bytes32 (* address stateRoot *)
| CANCEL address address uint256 address uint256 bytes (* addres caller ID token amount proof *)
| WITHDRAW address address address uint256 bytes (* address caller token amount proof *)

primrec executeStep :: "Contracts \<Rightarrow> nat \<Rightarrow> Block \<Rightarrow> Step \<Rightarrow> Status \<times> Contracts" where
  "executeStep contracts blockNum block (DEPOSIT address caller ID token amount) = 
    callDeposit contracts address block (message caller amount) ID token amount"
| "executeStep contracts blockNum block (CLAIM address caller ID token amount proof) = 
    callClaim contracts address (message caller amount) ID token amount proof"
| "executeStep contracts blockNum block (UPDATE address stateRoot) = 
    callUpdate contracts address block blockNum stateRoot"
| "executeStep contracts blockNum block (CANCEL address caller ID token amount proof) = 
    callCancelDepositWhileDead contracts address (message caller 0) block ID token amount proof"
| "executeStep contracts blockNum block (WITHDRAW address caller token amount proof) = 
    callWithdrawWhileDead contracts address (message caller 0) block token amount proof"

inductive reachableFrom :: "Contracts \<Rightarrow> Contracts \<Rightarrow> Step list \<Rightarrow> bool" where
  reachableFrom_base: "\<And> contracts. reachableFrom contracts contracts []"
| reachableFrom_step: "\<And> contracts contracts' blockNum block step. 
                       \<lbrakk>reachableFrom contracts contracts' steps; 
                        executeStep contracts' blockNum block step = (Success, contracts'')\<rbrakk> \<Longrightarrow> 
                        reachableFrom contracts contracts'' (step # steps)" 


lemma reachableFromCons':
  assumes "reachableFrom contracts contracts' (step # steps)"
  obtains contracts'' blockNum block where 
   "reachableFrom contracts contracts'' steps"
   "executeStep contracts'' blockNum block step = (Success, contracts')"
  by (smt (verit, best) assms list.discI list.inject reachableFrom.cases)

lemma reachableFromSingleton:
  assumes "reachableFrom contracts contracts' [step]"
  obtains block blockNum where "executeStep contracts block blockNum step = (Success, contracts')"
  using assms
  by (smt (verit, ccfv_SIG) neq_Nil_conv reachableFrom.cases reachableFromCons')

lemma reachableFromTrans:
  assumes "reachableFrom s2 s3 steps2" "reachableFrom s1 s2 steps1"
  shows "reachableFrom s1 s3 (steps2 @ steps1)"
  using assms
  by (induction s2 s3 steps2 rule: reachableFrom.induct, auto simp add: reachableFrom_step)

lemma reachableFromAppend:
  assumes "reachableFrom contracts contracts' (steps1 @ steps2)"
  obtains c where "reachableFrom contracts c steps2" "reachableFrom c contracts' steps1"
  using assms
proof (induction steps1 arbitrary: contracts contracts' rule: list.induct)
  case Nil
  then show ?case
    using reachableFrom_base by auto
next
  case (Cons step steps1)
  then show ?case
    by (smt (verit, ccfv_threshold) reachableFrom_step add_is_0 append_Cons length_0_conv list.inject list.size(4) nat.simps(3) reachableFrom.cases)
qed

lemma reachableFromStepInSteps:
  assumes "reachableFrom contracts contracts' steps"
  assumes "step \<in> set steps"
  obtains c1 c2 block blockNum steps1 steps2 where
  "reachableFrom contracts c1 steps2" 
  "executeStep c1 blockNum block step = (Success, c2)"
  "reachableFrom c2 contracts' steps1"
  "steps = steps1 @ [step] @ steps2"
proof-
  obtain steps1 steps2 where *: "steps = steps1 @ [step] @ steps2"
    using \<open>step \<in> set steps\<close>
    by (metis append_Cons append_self_conv2 in_set_conv_decomp_last)
  
  moreover

  obtain c2 where
    "reachableFrom contracts c2 ([step] @ steps2)" 
    "reachableFrom c2 contracts' steps1"
    using \<open>reachableFrom contracts contracts' steps\<close> * reachableFromAppend[of contracts contracts' "steps1" "[step] @ steps2"]
    by auto
  
  moreover

  obtain c1 blockNum block
    where "reachableFrom contracts c1 steps2" "executeStep c1 blockNum block step = (Success, c2)"
    using \<open>reachableFrom contracts c2 ([step] @ steps2)\<close> reachableFromCons'[of contracts c2 step steps2]
    by auto

  ultimately
  show ?thesis
    using  that 
    by auto
qed

lemma reachableFromRepeatedStepNonDistinct:
  assumes "reachableFrom contracts contracts' (step # steps)"
  assumes "step \<in> set steps"
  obtains c1 c2 c3 blockNum1 block1 blockNum2 block2 steps1 steps2 where
  "reachableFrom contracts c1 steps2" 
  "executeStep c1 blockNum1 block1 step = (Success, c2)"
  "reachableFrom c2 c3 steps1"
  "executeStep c3 blockNum2 block2 step = (Success, contracts')"
  "steps = steps1 @ [step] @ steps2"
  using assms
  by (smt (verit, ccfv_threshold) append_Cons append_self_conv2 in_set_conv_decomp_first reachableFromCons' reachableFromAppend)

(* --------------------------------------------------------------------------------- *)

lemma reachableFromITokenPairs [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableFromIProofVerifier [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableFromBridgeDeposit [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "BridgeState.deposit (the (bridgeState contracts' address)) = 
         BridgeState.deposit (the (bridgeState contracts address))"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  qed
qed

lemma reachableFromBridgeTokenPairs [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "tokenPairsAddressB contracts' address = tokenPairsAddressB contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromBridgeStateOracle [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "stateOracleAddressB contracts' address = stateOracleAddressB contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next   
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next   
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromBridgeProofVerifier [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "proofVerifierAddressB contracts' address = proofVerifierAddressB contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromDepositStateOracle [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "stateOracleAddressTD contracts' address = stateOracleAddressTD contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by auto
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by auto
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromBridgeMintedToken [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "mintedTokenB contracts' bridgeAddress token =
         mintedTokenB contracts bridgeAddress token"
  using assms
  unfolding Let_def
  by simp

lemma reachableFromGetTokenWithdrawn:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getTokenWithdrawn ((the (tokenDepositState contracts address))) h = True"
  shows "getTokenWithdrawn ((the (tokenDepositState contracts' address))) h = True"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableFromBridgeState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "bridgeState contracts address \<noteq> None"
  shows "bridgeState contracts' address \<noteq> None"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    using callClaimBridgeState[of contracts'] callClaimOtherAddress
    by (cases step, simp, metis executeStep.simps(2), simp, simp, simp)
qed

lemma reachableFromTokenDepositState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "tokenDepositState contracts address \<noteq> None"
  shows "tokenDepositState contracts' address \<noteq> None"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, 
        metis callDepositOtherAddress callDepositE executeStep.simps(1),
        simp, 
        simp, 
        metis callCancelDepositWhileDeadE callCancelDepositWhileDeadOtherAddress executeStep.simps(4),
        metis callWithdrawWhileDeadE callWithdrawWhileDeadOtherAddress executeStep.simps(5))
qed

lemma reachableFromERC20State:
  assumes "reachableFrom contracts contracts' steps"
  assumes "ERC20state contracts token \<noteq> None"
  shows "ERC20state contracts' token \<noteq> None"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof(cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step callDepositERC20state(2)
      by (cases "token = token'") auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (simp add: callClaimERC20state)
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step callCancelDepositWhileDeadERC20state(2)
      by (cases "token = token'") auto
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "token = token'") (auto simp add: callWithdrawWhileDeadERC20state(2))
  qed
qed

lemma reachableFromOriginalToMinted [simp]:
  assumes "reachableFrom contracts contracts' steps" 
        "callOriginalToMinted contracts tokenPairsAddr original = (Success, minted)"
  shows "callOriginalToMinted contracts' tokenPairsAddr original = (Success, minted)"
  using assms
  unfolding callOriginalToMinted_def
  by simp

lemma reachableFromDeadState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "deadStateTD contracts tokenDepositAddress = stateRoot"
  assumes "stateRoot \<noteq> 0"
  shows "deadStateTD contracts' tokenDepositAddress = stateRoot"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then have *: "deadStateTD contracts' tokenDepositAddress = stateRoot"
    by simp
  then show ?case
    using reachableFrom_step.hyps(2)
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step *
      by (metis callDepositInDeadState executeStep.simps(1))
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step *
      by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step *
      by (metis callCancelDepositWhileDeadInDeadState executeStep.simps(4))
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step *
      by (metis callWithdrawWhileDeadInDeadState executeStep.simps(5))
  qed
qed

text \<open>Dead state is never unset\<close>
lemma reachableFromBridgeDead:
  assumes "reachableFrom contracts contracts' steps"
  assumes "bridgeDead contracts tokenDepositAddress"
  shows "bridgeDead contracts' tokenDepositAddress"
  using assms
  using reachableFromDeadState
  by auto

lemma BridgeDiesDeadState:
  assumes "\<not> bridgeDead contracts tokenDepositAddress"
  assumes "executeStep contracts block blockNum step = (Success, contracts')"
  assumes "bridgeDead contracts' tokenDepositAddress"
  shows "deadStateTD contracts' tokenDepositAddress = 
         lastStateTD contracts tokenDepositAddress"
proof (cases step)
  case (DEPOSIT address' caller' ID' token' amount')
  then show ?thesis
    using assms
    by (metis callDepositOtherAddress executeStep.simps(1) callDepositNotBridgeDead')
next
  case (CLAIM address' caller' ID' token' amount' proof')
  then show ?thesis 
    using assms 
    by fastforce
next
  case (UPDATE address' stateRoot')
  then show ?thesis
    using assms 
    by fastforce
next
  case (CANCEL address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms
    by (metis callCancelDepositWhileDeadOtherAddress callCancelDepositWhileDeadSetsDeadState executeStep.simps(4))
next
  case (WITHDRAW address' caller' token' amount' proof')
  then show ?thesis
    using assms
    by (metis callWithdrawWhileDeadOtherAddress callWithdrawWhileDeadSetsDeadState executeStep.simps(5))
qed

text \<open>State root is never zero in an update\<close>
definition updatesNonZero where
  "updatesNonZero steps \<longleftrightarrow> 
     (\<forall> address stateRoot. UPDATE address stateRoot \<in> set steps \<longrightarrow> stateRoot \<noteq> 0)"

lemma updatesNonZeroCons:
  assumes "updatesNonZero (step # steps)"
  shows "updatesNonZero steps" "\<forall> address stateRoot. step = UPDATE address stateRoot \<longrightarrow> stateRoot \<noteq> 0"
  using assms
  unfolding updatesNonZero_def
  by auto

declare updatesNonZeroCons(1)[simp]

lemma updatesNonZeroAppend:
  assumes "updatesNonZero (steps1 @ steps2)"
  shows "updatesNonZero steps1" "updatesNonZero steps2"
  using assms
  by (auto simp add: updatesNonZero_def)

lemma reachableFromStateRootNonZero:
  assumes "reachableFrom contracts contracts' steps" 
  assumes "updatesNonZero steps"
  assumes "lastStateSO contracts address \<noteq> 0"
  shows "lastStateSO contracts' address \<noteq> 0"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step updatesNonZeroCons[of step steps]
      by (metis callUpdateLastState callUpdateOtherAddress executeStep.simps(3))
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  qed
qed

lemma reachableFromGetLastStateTDNonzero:
  assumes "reachableFrom contracts contracts' steps"
  assumes "updatesNonZero steps"
  assumes "lastStateTD contracts tokenDepositAddress \<noteq> 0"
  shows "lastStateTD contracts' tokenDepositAddress \<noteq> 0"
  using assms reachableFromStateRootNonZero
  by simp

text \<open>If there was at least one update and no updates set zero state, 
      then the last state is not zero\<close>
lemma lastStateNonZero:
  assumes "reachableFrom initContracts contracts steps"
  assumes "UPDATE (stateOracleAddressB contracts bridgeAddress) stateRoot \<in> set steps"
  assumes "updatesNonZero steps"
  shows "lastStateB contracts bridgeAddress \<noteq> 0"
  using assms
proof (induction initContracts contracts steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "step = (let stateOracleAddress = stateOracleAddressB contracts bridgeAddress 
                         in UPDATE stateOracleAddress stateRoot)")
    case True
    then show ?thesis
      using reachableFrom_step updatesNonZero_def 
      by (auto simp add: Let_def)
  next
    case False
    then have *: "lastStateB contracts' bridgeAddress \<noteq> 0"
      using reachableFrom_step updatesNonZeroCons
      by (smt (verit, ccfv_SIG) reachableFromBridgeStateOracle reachableFrom.reachableFrom_step set_ConsD)
    show "lastStateB contracts'' bridgeAddress \<noteq> 0"
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      then show ?thesis
        using reachableFrom_step *
        by simp
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      then show ?thesis
        using * reachableFrom_step
        by (cases "bridgeAddress = address'", auto)
    next
      case (UPDATE address' stateRoot')
      then have "stateRoot' \<noteq> 0"
        using reachableFrom_step.prems updatesNonZeroCons
        by blast
      then show ?thesis
        using * reachableFrom_step UPDATE
        by (metis (mono_tags, lifting) callUpdateIBridge callUpdateLastState callUpdateOtherAddress executeStep.simps(3))
    next
      case (CANCEL address' caller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step *
        by simp
    next
      case (WITHDRAW address' caller' token' amount' proof')
      then show ?thesis
        using reachableFrom_step *
        by simp
    qed
  qed
qed


\<comment> \<open>Once written deposit hash can be unset only by a cancel step\<close>
lemma reachableFromGetDepositBridgeNoCancel:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = h"
  assumes "h \<noteq> 0"
  assumes "\<nexists> caller amount token proof. CANCEL tokenDepositAddress caller ID token amount proof \<in> set steps"
  shows "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = h"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by auto
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis using reachableFrom_step
      by (metis callDepositOtherAddress callDepositOtherID callDepositWrittenHash executeStep.simps(1) fst_conv list.set_intros(2))
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis using reachableFrom_step
      by (metis callClaimITokenDeposit executeStep.simps(2) list.set_intros(2))
  next
    case (UPDATE address' stateRoot')
    then show ?thesis using reachableFrom_step by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis using reachableFrom_step 
     by (metis callCancelDepositWhileDeadOtherAddress callCancelDepositWhileDeadDeposits executeStep.simps(4) list.set_intros(1) list.set_intros(2) lookupNat_delete')
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis using reachableFrom_step
      by (metis callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress executeStep.simps(5) list.set_intros(2))
  qed
qed

text \<open>Once written deposit entry cannot be unset while the bridge is alive\<close>
lemma reachableFromGetDepositBridgeNotDead:
  assumes "reachableFrom contracts contracts' steps"
  \<comment> \<open>Hash of the transaction is not zero\<close>
  assumes "h \<noteq> 0"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = h"
  \<comment> \<open>The bridge is not dead\<close>
  assumes "\<not> bridgeDead contracts' tokenDepositAddress"
  shows "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = h"
  using assms
(* FIXME: simplify proof by applying previous lemma *)
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)

  show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (DEPOSIT address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' \<noteq> tokenDepositAddress")
      case True
      then show ?thesis
        using DEPOSIT reachableFrom_step
        using callDepositOtherAddress[of tokenDepositAddress address']
        by simp
    next
      case False
      show ?thesis
      proof (cases "ID = ID'")
        case True
        then have False
          using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close> callDepositWrittenHash
          by (metis callDepositFailsInDeadState executeStep.simps(1) fst_conv)
        then show ?thesis
          by simp
      next
        case False
        then show ?thesis
          using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close>
          by (metis callDepositInDeadState callDepositOtherID executeStep.simps(1))
      qed
    qed
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
    proof (cases "address' = tokenDepositAddress")
      case False
      then show ?thesis
        using reachableFrom_step CANCEL
        by (metis callCancelDepositWhileDeadOtherAddress executeStep.simps(4))
    next
      case True
      have "bridgeDead contracts' tokenDepositAddress"
        using callCancelDepositWhileDeadBridgeDead[of contracts' tokenDepositAddress "message caller' 0" block ID' token' amount' proof' contracts'']
        using CANCEL reachableFrom_step True
        by auto
      then have "bridgeDead contracts'' tokenDepositAddress"
        using callCancelDepositWhileDeadInDeadState CANCEL \<open>executeStep contracts' blockNum block step = (Success, contracts'')\<close> 
        by (metis executeStep.simps(4))
      then have False
        using \<open>\<not> bridgeDead contracts'' tokenDepositAddress\<close>
        by simp
      then show ?thesis
        by simp
    qed
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then have "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = h"
      using reachableFrom_step 
      by (metis callWithdrawWhileDeadInDeadState executeStep.simps(5))
    then show ?thesis
      using WITHDRAW reachableFrom_step.hyps
      by (cases "address' = tokenDepositAddress") 
         (simp, metis callWithdrawWhileDeadOtherAddress executeStep.simps(5))
  qed
qed

lemma reachableFromGetDepositBridgeDead:
  assumes "reachableFrom contracts contracts' steps"
  assumes "bridgeDead contracts tokenDepositAddress"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = 0"
  shows "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = 0"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    apply (cases step)
        apply (metis Hash.callDepositOtherAddress callDepositFailsInDeadState executeStep.simps(1) fst_conv reachableFromDeadState)
       apply simp
      apply simp
     apply (metis callCancelDepositWhileDeadDeposits callCancelDepositWhileDeadOtherAddress executeStep.simps(4) lookupNat_delete lookupNat_delete')
    apply (metis callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress executeStep.simps(5))
    done
qed

text \<open>Once written deposit entry cannot only remain the same or be unset to zero\<close>
lemma reachableFromGetDeposit:
  assumes "reachableFrom contracts contracts' steps"
  assumes "h \<noteq> 0"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = h"
  shows "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = h \<or> 
         getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = 0"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    apply (cases step)
        apply (metis (no_types, lifting) Hash.callDepositOtherAddress callDepositNotBridgeDead' executeStep.simps(1) reachableFrom.reachableFrom_step reachableFromGetDepositBridgeNotDead)
       apply simp
      apply simp
     apply (metis (no_types, lifting) callCancelDepositWhileDeadDeposits callCancelDepositWhileDeadOtherAddress executeStep.simps(4) lookupNat_delete lookupNat_delete')
    apply (metis callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress executeStep.simps(5))
    done
qed

text \<open>Once written claim entry cannot be unset\<close>
lemma reachableFromGetClaim:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getClaim (the (bridgeState contracts address)) ID = True"
  shows "getClaim (the (bridgeState contracts' address)) ID = True"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step callClaimPreservesTrueClaim callClaimOtherAddress
      by (metis executeStep.simps(2))
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CANCEL address' caller' ID' token' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (WITHDRAW address' caller' token' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  qed
qed

text \<open>When there are no updates, then the last state remains the same\<close>

(* FIXME: arbitrary address *)
lemma noUpdateGetLastValidStateTD:
  assumes "executeStep contracts block blockNum step = (Success, contracts')"
  assumes "\<nexists>stateRoot'. step = UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot'"
  shows "lastValidStateTD contracts' tokenDepositAddress = 
         lastValidStateTD contracts tokenDepositAddress"
  using assms
proof (cases step)
  case (DEPOSIT address' caller' ID' token' amount')
  then show ?thesis
    using assms
    by simp
next
  case (CLAIM address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms
    by (metis callClaimGetLastValidStateTD executeStep.simps(2))
next
  case (UPDATE address' stateRoot')
  then show ?thesis
    using assms
    by (metis StateOracleState.callWithdrawWhileDeadGetLastValidStateTD executeStep.simps(3))
next
  case (CANCEL address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms
    by (smt (verit, ccfv_SIG) callCancelDepositWhileDeadIStateOracle callCancelDepositWhileDeadOtherAddress callCancelWhileDeadGetLastValidStateTD executeStep.simps(4) callLastState_def lastValidState_def)
next
  case (WITHDRAW address' caller' token' amount' proof')
  then show ?thesis
    using assms
    by (smt (verit, ccfv_SIG) callWithdrawWhileDeadGetLastValidStateTD callWithdrawWhileDeadOtherAddress executeStep.simps(5) callLastState_def callWithdrawWhileDeadIStateOracle lastValidState_def)
qed

lemma noUpdateLastState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<nexists> stateRoot. UPDATE address stateRoot \<in> set steps"
  shows "lastStateSO contracts address = lastStateSO contracts' address"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' calller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then have "address \<noteq> address'"
      using reachableFrom_step.prems by auto
    then show ?thesis
      by (metis UPDATE callUpdateOtherAddress executeStep.simps(3) list.set_intros(2) reachableFrom_step.IH reachableFrom_step.hyps(2) reachableFrom_step.prems)
  next
    case (CANCEL address' calller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (WITHDRAW address' calller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  qed
qed

end

context StrongHashProofVerifier
begin

lemma hashWrittenOnlyByDeposit:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = 0"
  assumes "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = hash3 caller token amount"
  shows "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  show False
    using assms *
  proof (induction contracts contracts' steps rule: reachableFrom.induct)
    case (reachableFrom_base contracts)
    then show ?case
      using hash3_nonzero
      by simp
  next
    case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
    show ?case
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' \<noteq> tokenDepositAddress")
        case True
        then show ?thesis
          using DEPOSIT reachableFrom_step callDepositOtherAddress[OF True[symmetric]]
          by simp
      next
        case False
        show ?thesis
        proof (cases "ID \<noteq> ID'")
          case True
          then show ?thesis
            using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close> callDepositOtherID
            by simp
        next
          case False
          then have "getDeposit (the (tokenDepositState contracts'' tokenDepositAddress)) ID =
                     hash3 caller' token' amount'"
            using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close> callDepositWritesHash
            by auto
          then have "hash3 caller token amount = hash3 caller' token' amount'"
            using reachableFrom_step
            by auto
          then have "caller = caller'" "token = token'" "amount = amount'"
            using hash3_inj unfolding hash3_inj_def
            by blast+
          then show False
            using DEPOSIT reachableFrom_step \<open>\<not> ID \<noteq> ID'\<close>
            by auto
        qed
      qed
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        by auto
    next
      case (UPDATE address' stateRoot')
      then show ?thesis
        using reachableFrom_step
        by auto
    next
      case (CANCEL address' caller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step callCancelDepositWhileDeadDeposits hash3_nonzero
        by (smt (verit, ccfv_SIG) callCancelDepositWhileDeadOtherAddress executeStep.simps(4) list.set_intros(2) lookupNat_delete lookupNat_delete')
    next
      case (WITHDRAW address' caller' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        by (cases "address' \<noteq> tokenDepositAddress")
           (metis callWithdrawWhileDeadOtherAddress executeStep.simps(5) list.set_intros(2),
            simp)
    qed
  qed
qed

end

context HashProofVerifier
begin

text \<open>If claim is executed, it it noted in the bridge in the claims array\<close>
lemma claimStepSetsClaim:
  assumes "reachableFrom contracts contracts' steps"
  assumes "CLAIM bridgeAddress caller ID token amount p \<in> set steps"
  shows "getClaim (the (bridgeState contracts' bridgeAddress)) ID = True"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "step = CLAIM bridgeAddress caller ID token amount p")
    case True
    then show ?thesis
      using reachableFrom_step.hyps callClaimWritesClaim
      by simp
  next
    case False
    then show ?thesis
      using reachableFrom_step
      by (cases step,
          simp,
          metis callClaimOtherAddress callClaimPreservesTrueClaim executeStep.simps(2) set_ConsD,
          simp,
          simp,
          simp)
  qed
qed


text \<open>If state oracle last state has changed, it must have been due to an update step.
      One of those updates must be the last update applied.\<close>
lemma lastUpdateHappened:
  assumes "reachableFrom contracts contracts' steps"
  assumes "lastStateSO contracts address \<noteq> lastStateSO contracts' address"
  shows "\<exists> contractsU contractsU' block blockNum steps1 steps2 stateRoot. 
                       reachableFrom contracts contractsU steps1 \<and> 
                       stateRoot = generateStateRoot contractsU \<and>
                       callUpdate contractsU address block blockNum stateRoot = (Success, contractsU') \<and>
                       reachableFrom contractsU' contracts' steps2 \<and>
                       (\<nexists> stateRoot'. UPDATE address stateRoot' \<in> set steps2) \<and>
                       set steps1 \<subseteq> set steps" (* FIXME: add steps2 *)
using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using executeStep.simps(1) reachableFrom_step
      by auto
    then show ?thesis
      using reachableFrom_step DEPOSIT
      by (meson Step.simps(9) dual_order.trans reachableFrom.reachableFrom_step set_ConsD set_subset_Cons)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step CLAIM
      by (meson Step.simps(15) dual_order.trans reachableFrom.reachableFrom_step set_ConsD set_subset_Cons)
  next
    case (UPDATE address' stateRoot')
    then have *: "stateRoot' = generateStateRoot contracts'"
      using reachableFrom_step updateSuccess
      by simp
    show ?thesis
    proof (cases "address = address'")
      case True
      then show ?thesis
        using reachableFrom_step.hyps UPDATE *
        using reachableFrom_base 
        by (rule_tac x="contracts'" in exI, rule_tac x="contracts''" in exI, force)
    next
      case False
      then obtain contractsU contractsU' block blockNum steps1 steps2 stateRoot
        where "reachableFrom contracts contractsU steps1 \<and>
               stateRoot = generateStateRoot contractsU \<and>
               callUpdate contractsU address block blockNum stateRoot = (Success, contractsU') \<and>
               reachableFrom contractsU' contracts' steps2 \<and>
               (\<nexists>stateRoot'. UPDATE address stateRoot' \<in> set steps2) \<and> set steps1 \<subseteq> set steps"
        using reachableFrom_step UPDATE callUpdateOtherAddress
        by (smt (verit, best) Step.simps(3) executeStep.simps(3) reachableFrom.reachableFrom_step set_ConsD) 
      then show ?thesis
        by (smt (verit, best) False Step.simps(3) UPDATE dual_order.trans reachableFrom.reachableFrom_step reachableFrom_step.hyps(2) set_ConsD set_subset_Cons)
    qed
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step CANCEL
      by (meson Step.simps(20) reachableFrom.reachableFrom_step set_ConsD set_subset_Cons subset_trans)
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step WITHDRAW
      by (meson Step.simps(22) reachableFrom.reachableFrom_step set_ConsD set_subset_Cons subset_trans)
  qed
qed

lemma lastUpdateHappened':
  assumes "reachableFrom contracts contractsUx steps1x"
  assumes update: "callUpdate contractsUx address blockx blockNumx stateRootx = (Success, contractsU'x)"
  assumes "reachableFrom contractsU'x contracts' steps2x"
  shows "\<exists> contractsU contractsU' block blockNum steps1 steps2 stateRoot. 
                       reachableFrom contracts contractsU steps1 \<and> 
                       stateRoot = generateStateRoot contractsU \<and>
                       callUpdate contractsU address block blockNum stateRoot = (Success, contractsU') \<and>
                       reachableFrom contractsU' contracts' steps2 \<and>
                       (\<nexists> stateRoot'. UPDATE address stateRoot' \<in> set steps2) \<and>
                       set steps1x \<subseteq> set steps1" (* FIXME: add steps2 *)
  using assms(3) assms(1-2)
proof (induction contractsU'x contracts' steps2x rule: reachableFrom.induct)
  case (reachableFrom_base contracts')
  then show ?case
    by (metis list.distinct(1) list.set_cases reachableFrom.reachableFrom_base subset_refl updateSuccess)
next
  case (reachableFrom_step stepsa contracts''a contractsa contracts'a blockNuma blocka stepa)
  then obtain contractsU contractsU' block blockNum steps1 steps2 stateRoot
    where *: "reachableFrom contracts contractsU steps1"
          "stateRoot = generateStateRoot contractsU"
          "callUpdate contractsU address block blockNum stateRoot = (Success, contractsU')"
          "reachableFrom contractsU' contracts'a steps2"
          "(\<nexists>stateRoot'. UPDATE address stateRoot' \<in> set steps2)"
          "set steps1x \<subseteq> set steps1"
    by blast
  show ?case
  proof (cases stepa)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(9) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(15) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(20) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case False
      then show ?thesis
        using * reachableFrom_step.prems reachableFrom_step.hyps
        by (smt (verit, ccfv_SIG) Step.simps(3) UPDATE reachableFrom.reachableFrom_step set_ConsD)
    next
      case True
      let ?u = "UPDATE address stateRootx"
      let ?steps = "stepsa @ [?u] @ steps1x"
      have "reachableFrom contracts contracts'a ?steps"
        using reachableFrom_step.prems reachableFrom_step.hyps UPDATE
        by (simp add: reachableFrom.reachableFrom_step reachableFromTrans)
      then show ?thesis
        using reachableFrom_step.prems reachableFrom_step.hyps UPDATE True
        using updateSuccess reachableFrom_base
        apply (rule_tac x="contracts'a" in exI)
        apply (rule_tac x="contracts''a" in exI)
        apply (rule_tac x="blocka" in exI)
        apply (rule_tac x="blockNuma" in exI)
        apply (rule_tac x="?steps" in exI)
        by force
    qed
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(22) reachableFrom.reachableFrom_step set_ConsD)
  qed
qed

lemma lastUpdateHappenedSteps:
  assumes "reachableFrom contracts contracts' steps"
  assumes "lastStateSO contracts address \<noteq> lastStateSO contracts' address"
  shows "\<exists> contractsU steps1 steps2 stateRoot. 
                       reachableFrom contracts contractsU steps1 \<and> 
                       stateRoot = generateStateRoot contractsU \<and>
                       steps = steps2 @ [UPDATE address stateRoot] @ steps1 \<and>
                       reachableFrom contractsU contracts' (steps2 @ [UPDATE address stateRoot]) \<and>
                       (\<nexists> stateRoot'. UPDATE address stateRoot' \<in> set steps2)"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
      by force
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step  reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
      by force
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
      by force
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
      by force
  next
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case True
      then show ?thesis
        using reachableFrom_step.hyps reachableFrom_step.prems UPDATE
        by (rule_tac x="contracts'" in exI,
            rule_tac x="steps" in exI,
            rule_tac x="[]" in exI,
            metis Cons_eq_appendI append_Nil empty_iff executeStep.simps(3) list.set(1) reachableFrom.reachableFrom_step reachableFrom_base updateSuccess)
    next
      case False
      then have "lastState (the (stateOracleState contracts address)) \<noteq> lastState (the (stateOracleState contracts' address))"
        by (metis UPDATE callUpdateOtherAddress executeStep.simps(3) local.reachableFrom_step(2) reachableFrom_step.prems)
      then show ?thesis
        using reachableFrom_step UPDATE False reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
        by force
    qed
  qed
qed

lemma lastUpdateHappenedSteps':
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<exists> stateRoot. UPDATE address stateRoot \<in> set steps"
  shows "\<exists> contractsU steps1 steps2 stateRoot. 
                       reachableFrom contracts contractsU steps1 \<and> 
                       stateRoot = generateStateRoot contractsU \<and>
                       steps = steps2 @ [UPDATE address stateRoot] @ steps1 \<and>
                       reachableFrom contractsU contracts' (steps2 @ [UPDATE address stateRoot]) \<and>
                       (\<nexists> stateRoot'. UPDATE address stateRoot' \<in> set steps2)"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
      by force
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
      by force
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
      by force
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
      by force
  next
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case True
      then show ?thesis
        using reachableFrom_step.hyps reachableFrom_step.prems UPDATE
        by (rule_tac x="contracts'" in exI,
            rule_tac x="steps" in exI,
            rule_tac x="[]" in exI,
            metis Cons_eq_appendI append_Nil empty_iff executeStep.simps(3) list.set(1) reachableFrom.reachableFrom_step reachableFrom_base updateSuccess)
    next
      case False
      then show ?thesis
        using UPDATE reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
        by force
    qed
  qed
qed


lemma reachableFromGetClaimNoClaim:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<nexists> caller token amount proof. CLAIM bridgeAddress caller ID token amount proof \<in> set steps" 
  shows "getClaim (the (bridgeState contracts' bridgeAddress)) ID = 
         getClaim (the (bridgeState contracts bridgeAddress)) ID"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis using reachableFrom_step by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis using reachableFrom_step
      by (metis callClaimGetClaimOther executeStep.simps(2) list.set_intros(1) list.set_intros(2))
  next
    case (UPDATE address' stateRoot')
    then show ?thesis using reachableFrom_step by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis using reachableFrom_step by simp
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis using reachableFrom_step by simp
  qed
qed

(* ----------------------------------------------------------------------------------- *)

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

definition properToken :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> bool" where
  "properToken contracts tokenDepositAddress bridgeAddress token \<longleftrightarrow>
    (let stateBridge = bridgeState contracts bridgeAddress;
         stateTokenPairs = tokenPairsState contracts (BridgeState.tokenPairs (the stateBridge))
      in stateTokenPairs \<noteq> None \<and>
         ERC20state contracts token \<noteq> None \<and>
         getMinted (the stateTokenPairs) token \<noteq> 0 \<and>
         ERC20state contracts (getMinted (the stateTokenPairs) token) \<noteq> None)"

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

lemma callDepositProperToken [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  by (metis (no_types, lifting) Hash.callDepositIBridge Hash.callDepositITokenPairs Hash.callDepositOtherToken callDepositERC20state(2) properToken_def)

lemma callClaimProperSetup [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def Let_def
  by (smt (verit, ccfv_SIG) callClaimBridgeState(2) callClaimDeposit callClaimIProofVerifier callClaimIStateOracle callClaimITokenDeposit callClaimITokenPairs callClaimOtherAddress callClaimProofVerifier callClaimStateOracle callClaimTokenPairs)

lemma callClaimProperToken [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def Let_def
  by (smt (verit, best) callClaimERC20state callClaimITokenPairs callClaimOtherAddress callClaimTokenPairs)

lemma callUpdateProperSetup [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  by (smt (verit, best) callUpdateIBridge callUpdateIERC20 callUpdateIProofVerifier callUpdateITokenDeposit callUpdateITokenPairs callUpdateOtherAddress callUpdateStateOracleState(2))

lemma callUpdateProperToken [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  using callUpdateIBridge callUpdateIERC20 callUpdateITokenPairs 
  by presburger

lemma callCancelDepositWhileDeadProperSetup [simp]:
  assumes "callCancelDepositWhileDead contracts address block msg ID token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  by (smt (z3) callCancelDepositOtherToken callCancelDepositWhileDeadBridge callCancelDepositWhileDeadProofVerifier callCancelDepositWhileDeadE callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadIBridge callCancelDepositWhileDeadIProofVerifier callCancelDepositWhileDeadIStateOracle callCancelDepositWhileDeadITokenPairs callCancelDepositWhileDeadOtherAddress callCancelDepositWhileDeadStateOracle callCancelDepositWhileDeadTokenPairs)

lemma callCancelDepositWhileDeadProperToken [simp]:
  assumes "callCancelDepositWhileDead contracts address block msg ID token amount proof = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  by (metis callCancelDepositOtherToken callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadIBridge callCancelDepositWhileDeadITokenPairs)

lemma callWithdrawWhileDeadProperSetup [simp]:
  assumes "callWithdrawWhileDead contracts address block msg token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  by (smt (z3) callWithdrawWhileDeadBridge callWithdrawWhileDeadProofVerifier callWithdrawWhileDeadE callWithdrawWhileDeadERC20state(2) callWithdrawWhileDeadIBridge callWithdrawWhileDeadIProofVerifier callWithdrawWhileDeadIStateOracle callWithdrawWhileDeadITokenPairs callWithdrawWhileDeadOtherAddress callWithdrawWhileDeadOtherToken callWithdrawWhileDeadStateOracle callWithdrawWhileDeadTokenPairs)

lemma callWithdrawWhileDeadProperToken [simp]:
  assumes "callWithdrawWhileDead contracts address block msg token amount proof = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  by (metis callWithdrawWhileDeadERC20state(2) callWithdrawWhileDeadIBridge callWithdrawWhileDeadITokenPairs callWithdrawWhileDeadOtherToken)

lemma properSetupReachable [simp]:
  assumes "reachableFrom contracts contracts' steps"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma properTokenReachable [simp]:
  assumes "reachableFrom contracts contracts' steps"
  assumes "properToken contracts tokenDepositAddress bridgeAddress token"
  shows "properToken contracts' tokenDepositAddress bridgeAddress token"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

end
end