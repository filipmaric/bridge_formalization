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
| "executeStep contracts blockNum block (TRANSFER address caller receiver token amount) = 
    callTransfer contracts address caller receiver token amount"
| "executeStep contracts blockNum block (UPDATE address stateRoot) = 
    callUpdate contracts address block blockNum stateRoot"
| "executeStep contracts blockNum block (CANCEL_WD address caller ID token amount proof) = 
    callCancelDepositWhileDead contracts address (message caller 0) block ID token amount proof"
| "executeStep contracts blockNum block (WITHDRAW_WD address caller token amount proof) = 
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
  shows "depositAddressB contracts' address = depositAddressB contracts address"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (cases "address = address'", auto)
  qed auto
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
  then show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed auto
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
  then show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed auto
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
  then show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed auto
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
  then show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed auto
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
  proof (cases step)
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadTokenWithdrawn'
      by (metis executeStep.simps(7))
  qed auto
qed

lemma reachableFromGetTokenWithdrawnNoWithdraw:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getTokenWithdrawn (the (tokenDepositState contracts' tokenDepositAddress)) (hash2 caller token) = False"
  shows "\<nexists> amount proof. WITHDRAW_WD tokenDepositAddress caller token amount proof \<in> set steps"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  have "getTokenWithdrawn (the (tokenDepositState contracts' tokenDepositAddress)) (hash2 caller token) = False"
    using reachableFrom_step.prems reachableFrom_step.hyps 
  proof (cases step)
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step.prems reachableFrom_step.hyps 
      using callWithdrawWhileDeadTokenWithdrawn'
      by (metis executeStep.simps(7))
  qed auto
  then have *: "\<nexists> amount proof. WITHDRAW_WD tokenDepositAddress caller token amount proof \<in> set steps"
    using reachableFrom_step.IH
    by blast
  show ?case
  proof (cases "\<nexists> address' token' caller' amount' proof'. WITHDRAW_WD address' caller' token' amount' proof' = step")
    case True
    then show ?thesis
      using reachableFrom_step.hyps *
      by (cases step, auto)
  next
    case False
    then obtain address' token' caller' amount' proof' where
      step: "step = WITHDRAW_WD address' caller' token' amount' proof'"
      by auto
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token \<and> caller' = caller")
      case False
      then show ?thesis
        using step reachableFrom_step.hyps *
        by auto
    next
      case True
      then show ?thesis
        using reachableFrom_step.hyps step reachableFrom_step.prems
        using callWithdrawWhileDeadTokenWithdrawn[of contracts' tokenDepositAddress "message caller 0" block token  amount' proof']
        by simp
    qed
  qed
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
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using callClaimBridgeState[of contracts'] callClaimOtherAddress
      using reachableFrom_step
      by (metis executeStep.simps(2))
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using callWithdrawBridgeState(2)[of contracts'] 
      using callWithdrawOtherAddress(1)
      using reachableFrom_step.prems(1) reachableFrom_step.IH reachableFrom_step.hyps(2)
      by (metis executeStep.simps(3))      
  qed auto
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
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (metis callDepositOtherAddress callDepositE executeStep.simps(1))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (metis callWithdrawWhileDeadE callWithdrawWhileDeadOtherAddress executeStep.simps(7))
  next
    case (CANCEL_WD address' caller'ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (metis callCancelDepositWhileDeadE callCancelDepositWhileDeadOtherAddress executeStep.simps(6))
  qed auto
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
      using reachableFrom_step callDepositERC20state(2) callDepositOtherToken
      by (cases "token = token'") auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (simp add: callClaimERC20state)
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadOtherToken
      by (metis executeStep.simps(6))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadERC20state(2) callWithdrawWhileDeadOtherToken
      by (metis executeStep.simps(7))
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using reachableFrom_step 
      by (simp add: callTransferERC20state)
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step 
      by (simp add: callWithdrawERC20state)
  qed auto
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
  then show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (metis callDepositInDeadState executeStep.simps(1))
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (metis callCancelDepositWhileDeadInDeadState executeStep.simps(6))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (metis callWithdrawWhileDeadInDeadState executeStep.simps(7))
  qed auto
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
    by (metis executeStep.simps(6))
next
  case (WITHDRAW_WD address' caller' token' amount' proof')
  then show ?thesis
    using assms
    using callWithdrawWhileDeadOtherAddress callWithdrawWhileDeadSetsDeadState 
    by (metis executeStep.simps(7))
qed auto

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
  then show ?case
  proof (cases step)
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step updatesNonZeroCons[of step steps]
      by (metis callUpdateLastState callUpdateOtherAddress executeStep.simps(5))
  qed auto
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
  proof (cases "step = UPDATE (stateOracleAddressB contracts bridgeAddress) stateRoot")
    case True
    then show ?thesis
      using reachableFrom_step 
      using callUpdateLastState
      unfolding updatesNonZero_def 
      by auto
  next
    case False
    then have *: "lastStateB contracts' bridgeAddress \<noteq> 0"
      using reachableFrom_step updatesNonZeroCons
      by (smt (verit, ccfv_SIG) reachableFromBridgeStateOracle reachableFrom.reachableFrom_step set_ConsD)
    then show "lastStateB contracts'' bridgeAddress \<noteq> 0"
      using reachableFrom_step
    proof (cases step)
      case (CLAIM address' caller' ID' token' amount' proof')
      then show ?thesis
        using * reachableFrom_step
        by (cases "bridgeAddress = address'", auto)
    next
      case (BURN address' caller' ID' token' amount')
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
        using callUpdateIBridge callUpdateLastState callUpdateOtherAddress
        by (metis (mono_tags, lifting) executeStep.simps(5))
    qed auto
  qed
qed


\<comment> \<open>Once written deposit hash can be unset only by a cancel step\<close>
lemma reachableFromGetDepositBridgeNoCancel:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = h"
  assumes "h \<noteq> 0"
  assumes "\<nexists> caller amount token proof. CANCEL_WD tokenDepositAddress caller ID token amount proof \<in> set steps"
  shows "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = h"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by auto
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      using callDepositOtherAddress callDepositOtherID callDepositWrittenHash
      by (metis executeStep.simps(1) fst_conv list.set_intros(2))
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis using reachableFrom_step 
      using callCancelDepositWhileDeadOtherAddress callCancelDepositWhileDeadDeposits
      by (metis  executeStep.simps(6) list.set_intros(1) list.set_intros(2) lookupNat_delete')
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis using reachableFrom_step
      by (metis callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress executeStep.simps(7) list.set_intros(2))
  qed auto
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
  then show ?case
  proof (cases step)
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
          using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close> 
          using callDepositWrittenHash callDepositFailsInDeadState
          by (metis executeStep.simps(1) fst_conv)
        then show ?thesis
          by simp
      next
        case False
        then show ?thesis
          using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close>
          using callDepositInDeadState callDepositOtherID
          by (metis executeStep.simps(1))
      qed
    qed
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
    proof (cases "address' = tokenDepositAddress")
      case False
      then show ?thesis
        using reachableFrom_step CANCEL_WD
        using callCancelDepositWhileDeadOtherAddress 
        by (metis executeStep.simps(6))
    next
      case True
      have "bridgeDead contracts' tokenDepositAddress"
        using callCancelDepositWhileDeadBridgeDead[where msg="message caller' 0"]
        using CANCEL_WD reachableFrom_step True
        by auto
      then have "bridgeDead contracts'' tokenDepositAddress"
        using reachableFrom_step.hyps
        using callCancelDepositWhileDeadInDeadState CANCEL_WD
        by (metis executeStep.simps(6))
      then have False
        using \<open>\<not> bridgeDead contracts'' tokenDepositAddress\<close>
        by simp
      then show ?thesis
        by simp
    qed
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then have "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = h"
      using reachableFrom_step callWithdrawWhileDeadInDeadState 
      by (metis executeStep.simps(7))
    then show ?thesis
      using WITHDRAW_WD reachableFrom_step.hyps
      by (cases "address' = tokenDepositAddress") 
         (simp, metis callWithdrawWhileDeadOtherAddress executeStep.simps(7))
  qed auto
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
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      using callDepositOtherAddress callDepositFailsInDeadState reachableFromDeadState
      by (metis executeStep.simps(1) fst_conv)
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callCancelDepositWhileDeadDeposits callCancelDepositWhileDeadOtherAddress
      by (metis executeStep.simps(6) lookupNat_delete lookupNat_delete')
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress
      by (metis executeStep.simps(7))
  qed auto
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
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      using callDepositOtherAddress callDepositNotBridgeDead' reachableFromGetDepositBridgeNotDead
      by (metis (no_types, lifting) executeStep.simps(1) reachableFrom.reachableFrom_step)
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using  callCancelDepositWhileDeadDeposits callCancelDepositWhileDeadOtherAddress
      by (metis (no_types, lifting) executeStep.simps(6) lookupNat_delete lookupNat_delete')
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress
      by (metis executeStep.simps(7))
  qed auto
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
  then show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step callClaimPreservesTrueClaim callClaimOtherAddress
      by (metis executeStep.simps(2))
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      using  callWithdrawOtherAddress callWithdrawPreservesClaims
      by (metis executeStep.simps(3))
  qed auto
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
  case (CANCEL_WD address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms
    using callCancelDepositWhileDeadLastValidStateTD callCancelDepositWhileDeadIStateOracle callCancelDepositWhileDeadOtherAddress 
    by (smt (verit, best) callLastState_def lastValidState_def executeStep.simps(6))
next
  case (WITHDRAW_WD address' caller' token' amount' proof')
  then show ?thesis
    using assms
    using callWithdrawWhileDeadLastValidStateTD callWithdrawWhileDeadOtherAddress callWithdrawWhileDeadIStateOracle 
    by (smt (verit, ccfv_SIG) callLastState_def lastValidState_def executeStep.simps(7))
next
  case (CLAIM address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms callClaimLastValidStateTD 
    by (metis executeStep.simps(2))
next
  case (BURN address' caller' ID' token' amount')
  then show ?thesis
    using assms callWithdrawtLastValidStateTD
    by (metis executeStep.simps(3))
next
  case (UPDATE address' stateRoot')
  then show ?thesis
    using assms
    using callUpdateLastValidStateTD
    by (metis executeStep.simps(5))
next
  case (TRANSFER address' caller' receiver' token' amount')
  then show ?thesis
    using assms reachableFrom_step
    unfolding lastValidState_def Let_def callLastState_def
    by auto
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
  then show ?case
  proof (cases step)
    case (UPDATE address' stateRoot')
    then have "address \<noteq> address'"
      using reachableFrom_step.prems by auto
    then show ?thesis
      using UPDATE reachableFrom_step
      using callUpdateOtherAddress
      by (metis executeStep.simps(5) list.set_intros(2))
  qed auto
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
    then show ?case
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
      case (CANCEL_WD address' caller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        using callCancelDepositWhileDeadDeposits callCancelDepositWhileDeadOtherAddress hash3_nonzero
        by (metis (no_types, lifting) executeStep.simps(6) list.set_intros(2) lookupNat_delete lookupNat_delete')
    next
      case (WITHDRAW_WD address' caller' token' amount' proof')
      then show ?thesis
        using reachableFrom_step callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress
        by (metis executeStep.simps(7) list.set_intros(2))
    qed auto
  qed
qed

end

context HashProofVerifier
begin

text \<open>If claim is executed, it it noted in the bridge in the claims array\<close>
lemma claimStepSetsClaim:
  assumes "reachableFrom contracts contracts' steps"
  assumes "CLAIM bridgeAddress caller ID token amount proof \<in> set steps"
  shows "getClaim (the (bridgeState contracts' bridgeAddress)) ID = True"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "step = CLAIM bridgeAddress caller ID token amount proof")
    case True
    then show ?thesis
      using reachableFrom_step.hyps callClaimWritesClaim
      by simp
  next
    case False
    then show ?thesis
      using reachableFrom_step
      by (metis reachableFrom.simps reachableFromGetClaim set_ConsD)
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
      by (meson Step.simps(15) dual_order.trans reachableFrom.reachableFrom_step set_ConsD set_subset_Cons)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step CLAIM
      by (meson Step.simps(25) dual_order.trans reachableFrom.reachableFrom_step set_ConsD set_subset_Cons)
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
        by (metis (no_types, lifting) executeStep.simps(5))
      then show ?thesis
        using False UPDATE
        by (smt (verit, best) Step.simps(5) reachableFrom.reachableFrom_step reachableFrom_step.hyps(2) set_ConsD set_subset_Cons subset_trans)
    qed
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step CANCEL_WD
      by (meson Step.simps(44) reachableFrom.reachableFrom_step set_ConsD set_subset_Cons subset_trans)
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step WITHDRAW_WD
      by (meson Step.simps(46) reachableFrom.reachableFrom_step set_ConsD set_subset_Cons subset_trans)
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step TRANSFER
      by auto (metis (no_types, opaque_lifting) Step.simps(38) insertE list.simps(15) reachableFrom.reachableFrom_step reachableFrom_step.hyps(2) subset_insertI2)
      (* FIXME: avoid calling methods after auto *)
  next
    case (BURN address' caller' receiver' token' amount')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step BURN
      by auto (metis (no_types, opaque_lifting) Step.simps(32) executeStep.simps(3) insertE list.simps(15) reachableFrom.reachableFrom_step subset_insertI2)
      (* FIXME: avoid calling methods after auto *)
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
      by (meson Step.simps(15) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(25) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(44) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case False
      then show ?thesis
        using * reachableFrom_step.prems reachableFrom_step.hyps
        by (smt (verit, best) Step.simps(5) UPDATE reachableFrom.reachableFrom_step set_ConsD)
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
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(46) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(39) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (metis (no_types, opaque_lifting) Step.simps(32) reachableFrom.reachableFrom_step set_ConsD)
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
  then show ?case
    using reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
  proof (cases step)
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case True
      then show ?thesis
        using reachableFrom_step.hyps reachableFrom_step.prems UPDATE
        by (rule_tac x="contracts'" in exI,
            rule_tac x="steps" in exI,
            rule_tac x="[]" in exI,
            metis Cons_eq_appendI append_Nil empty_iff executeStep.simps(5) list.set(1) reachableFrom.reachableFrom_step reachableFrom_base updateSuccess)
    next
      case False
      then have "lastState (the (stateOracleState contracts address)) \<noteq> lastState (the (stateOracleState contracts' address))"
        by (metis UPDATE callUpdateOtherAddress executeStep.simps(5) local.reachableFrom_step(2) reachableFrom_step.prems)
      then show ?thesis
        using reachableFrom_step UPDATE False reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
        by force
    qed
  qed force+
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
  then show ?case
    using reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
  proof (cases step)
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case True
      then show ?thesis
        using reachableFrom_step.hyps reachableFrom_step.prems UPDATE
        by (rule_tac x="contracts'" in exI,
            rule_tac x="steps" in exI,
            rule_tac x="[]" in exI,
            metis Cons_eq_appendI append_Nil empty_iff executeStep.simps(5) list.set(1) reachableFrom.reachableFrom_step reachableFrom_base updateSuccess)
    next
      case False
      then show ?thesis
        using UPDATE reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
        by force
    qed
  qed force+
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
  then show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callClaimGetClaimOther
      by (metis executeStep.simps(2) list.set_intros(1) list.set_intros(2))
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawOtherAddress callWithdrawPreservesClaims
      by (metis (full_types) executeStep.simps(3) list.set_intros(2))
  qed auto
qed


lemma reachableFromFiniteBalances:
  assumes "reachableFrom contracts contracts' steps"
  assumes "finiteBalances contracts token"
  shows "finiteBalances contracts' token"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case by (simp add: finiteBalances_def)
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      using callDepositFiniteBalances
      by (metis executeStep.simps(1)) 
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callClaimFiniteBalances
      by (metis executeStep.simps(2))
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callCancelDepositWhileDeadFiniteBalances
      by (metis executeStep.simps(6))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadFiniteBalances
      by (metis executeStep.simps(7))
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      using callUpdateFiniteBalances
      by (metis executeStep.simps(5))
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using reachableFrom_step
      using callTransferFiniteBalances
      by (metis executeStep.simps(4))
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawFiniteBalances
      by (metis executeStep.simps(3))
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
  by (smt (z3) callCancelDepositWhileDeadOtherToken callCancelDepositWhileDeadBridge callCancelDepositWhileDeadProofVerifier callCancelDepositWhileDeadE callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadIBridge callCancelDepositWhileDeadIProofVerifier callCancelDepositWhileDeadIStateOracle callCancelDepositWhileDeadITokenPairs callCancelDepositWhileDeadOtherAddress callCancelDepositWhileDeadStateOracle callCancelDepositWhileDeadTokenPairs)

lemma callCancelDepositWhileDeadProperToken [simp]:
  assumes "callCancelDepositWhileDead contracts address block msg ID token amount proof = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  by (metis callCancelDepositWhileDeadOtherToken callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadIBridge callCancelDepositWhileDeadITokenPairs)

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


lemma callWithdrawWhileDeadProperToken [simp]:
  assumes "callWithdrawWhileDead contracts address block msg token amount proof = (Success, contracts')"
  assumes "properToken contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properToken contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properToken_def
  by (metis callWithdrawWhileDeadERC20state(2) callWithdrawWhileDeadIBridge callWithdrawWhileDeadITokenPairs callWithdrawWhileDeadOtherToken)

lemma callTransferProperSetup [simp]:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress"
  using assms
  unfolding properSetup_def
  using callTransferIBridge callTransferIProofVerifier callTransferIStateOracle callTransferITokenDeposit callTransferITokenPairs by presburger

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