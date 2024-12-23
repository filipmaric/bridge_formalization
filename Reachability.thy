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
    by (cases step, auto)
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
    by (cases step, auto)
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
    by (cases step, auto)
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
    by (cases step, auto)
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
    by (cases step, auto)
qed

lemma reachableFromBridgeMintedToken [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "mintedTokenB contracts' bridgeAddress token =
         mintedTokenB contracts bridgeAddress token"
  using assms
  unfolding Let_def
  by simp

lemma reachableFromOriginalToMinted [simp]:
  assumes "reachableFrom contracts contracts' steps" 
        "callOriginalToMinted contracts tokenPairsAddr original = (Success, minted)"
  shows "callOriginalToMinted contracts' tokenPairsAddr original = (Success, minted)"
  using assms
  unfolding callOriginalToMinted_def
  by simp

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
      using callClaimBridgeState(2)[of contracts'] callClaimOtherAddress
      using reachableFrom_step
      by (metis executeStep.simps(2))
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using callWithdrawBridgeState(2)[of contracts'] callWithdrawOtherAddress
      using reachableFrom_step
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
      using callDepositOtherAddress callDepositE
      by (metis executeStep.simps(1))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadE callWithdrawWhileDeadOtherAddress 
      by (metis executeStep.simps(8))
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callCancelDepositWhileDeadE callCancelDepositWhileDeadOtherAddress 
      by (metis executeStep.simps(7))
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callReleaseE callReleaseOtherAddress
      by (metis executeStep.simps(4))
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
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadOtherToken
      by (metis executeStep.simps(7))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadERC20state(2) callWithdrawWhileDeadOtherToken
      by (metis executeStep.simps(8))
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callReleaseERC20state(2) callReleaseOtherToken
      by (metis executeStep.simps(4))
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step callClaimERC20state
      by simp
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step callWithdrawERC20state 
      by simp
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using reachableFrom_step callTransferERC20state
      by simp
  qed auto
qed

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
      using reachableFrom_step callDepositInDeadState
      by (metis executeStep.simps(1))
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step callCancelDepositWhileDeadInDeadState
      by (metis executeStep.simps(7))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step callWithdrawWhileDeadInDeadState
      by (metis executeStep.simps(8))
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

(* --------------------------------------------------------------------------------- *)


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
      by (metis executeStep.simps(7))
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadFiniteBalances
      by (metis executeStep.simps(8))
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      using callUpdateFiniteBalances
      by (metis executeStep.simps(6))
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using reachableFrom_step
      using callTransferFiniteBalances
      by (metis executeStep.simps(5))
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawFiniteBalances
      by (metis executeStep.simps(3))
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callReleaseFiniteBalances
      by (metis executeStep.simps(4))
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

context HashProofVerifier
begin

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

end
end