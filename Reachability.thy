theory Reachability
imports Main Definition TokenDepositState BridgeState
begin

section \<open>Steps\<close>

(* FIXME: clarify block numbers and messages *)
definition message where 
  "message sender' val' = \<lparr> sender = sender', val = val' \<rparr>"

context ProofVerifier
begin

datatype Step = 
  DEPOSIT address address uint256 address uint256 (* address caller ID token amount *)
| CLAIM address address uint256 address uint256 bytes (* address caller ID token amount proof *) 
| UPDATE address bytes32 (* address stateRoot *)
| CANCEL address address uint256 address uint256 bytes (* addres caller ID token amount proof *)

primrec executeStep :: "Contracts \<Rightarrow> nat \<Rightarrow> Block \<Rightarrow> Step \<Rightarrow> Status \<times> Contracts" where
  "executeStep contracts blockNum block (DEPOSIT address caller ID token amount) = 
    callDeposit contracts address block (message caller amount) ID token amount"
| "executeStep contracts blockNum block (CLAIM address caller ID token amount proof) = 
    callClaim contracts address (message caller amount) ID token amount proof"
| "executeStep contracts blockNum block (UPDATE address stateRoot) = 
    callUpdate contracts address block blockNum stateRoot"
| "executeStep contracts blockNum block (CANCEL address caller ID token amount proof) = 
    callCancelDepositWhileDead contracts address (message caller 0) block ID token amount proof"

inductive reachableFrom :: "Contracts \<Rightarrow> Contracts \<Rightarrow> Step list \<Rightarrow> bool" where
  reachableFrom_base: "\<And> contracts. reachableFrom contracts contracts []"
| reachableFrom_step: "\<And> contracts contracts' blockNum block step. 
                       \<lbrakk>reachableFrom contracts contracts' steps; 
                        executeStep contracts' blockNum block step = (Success, contracts'')\<rbrakk> \<Longrightarrow> 
                        reachableFrom contracts contracts'' (step # steps)" 

lemma reachableFromTrans:
  assumes "reachableFrom s2 s3 steps2" "reachableFrom s1 s2 steps1"
  shows "reachableFrom s1 s3 (steps2 @ steps1)"
  using assms
  by (induction s2 s3 steps2 rule: reachableFrom.induct, auto simp add: reachableFrom_step)

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
    case (CANCEL addres' caller' ID' token' amount' proof')
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

lemma reachableFromBridgeTokenPairs [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "BridgeState.tokenPairs (the (bridgeState contracts' address)) = 
         BridgeState.tokenPairs (the (bridgeState contracts address))"
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
  qed
qed

lemma reachableFromBridgeStateOracle [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "BridgeState.stateOracle (the (bridgeState contracts' address)) = 
         BridgeState.stateOracle (the (bridgeState contracts address))"
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
  qed
qed

lemma reachableFromBridgeProofVerifier [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "BridgeState.proofVerifier (the (bridgeState contracts' address)) = 
         BridgeState.proofVerifier (the (bridgeState contracts address))"
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
  qed
qed

lemma reachableFromDepositStateOracle [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "TokenDepositState.stateOracle (the (tokenDepositState contracts' address)) =
         TokenDepositState.stateOracle (the (tokenDepositState contracts address))"
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
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
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
    using callClaimBridgeState[of contracts'] callClaimOtherAddress
    by (cases step, simp, metis executeStep.simps(2), simp, simp)
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
        metis callCancelDepositWhileDeadE callCancelDepositWhileDeadOtherAddress executeStep.simps(4))
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
  qed
qed

lemma reachableFromOriginalToMinted [simp]:
  assumes "reachableFrom contracts contracts' steps" 
        "callOriginalToMinted contracts tokenPairsAddr original = (Success, minted)"
  shows "callOriginalToMinted contracts' tokenPairsAddr original = (Success, minted)"
  using assms
  unfolding callOriginalToMinted_def
  by simp

text \<open>Dead state is never unset\<close>
lemma reachableFromDeadState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then have *: "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
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
  qed
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

lemma reachableFromStateRootNonZero:
  assumes "reachableFrom contracts contracts' steps" "updatesNonZero steps"
  assumes "lastState (the (stateOracleState contracts address)) \<noteq> 0"
  shows "lastState (the (stateOracleState contracts' address)) \<noteq> 0"
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
      using reachableFrom_step updatesNonZeroCons
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step updatesNonZeroCons
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step updatesNonZeroCons[of step steps]
      by (metis callUpdateLastState callUpdateOtherAddress executeStep.simps(3))
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step updatesNonZeroCons
      by simp
  qed
qed

lemma reachableFromGetLastStateTDNonzero:
  assumes "reachableFrom contracts contracts' steps" "updatesNonZero steps"
  assumes "getLastStateTD contracts tokenDepositAddress \<noteq> 0"
  shows "getLastStateTD contracts' tokenDepositAddress \<noteq> 0"
  using assms reachableFromStateRootNonZero
  by simp


text \<open>Once written deposit entry cannot be unset while the bridge is alive\<close>
lemma reachableFromGetDepositBridgeNotDead:
  assumes "reachableFrom contracts contracts' steps"
  \<comment> \<open>At least one update must have happened\<close>
  assumes "getLastStateTD contracts tokenDepositAddress \<noteq> 0"
  \<comment> \<open>State root always remains non-zero\<close>
  assumes "updatesNonZero steps"
  \<comment> \<open>Hash of the transaction is not zero\<close>
  assumes "h \<noteq> 0"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = h"
  \<comment> \<open>The bridge is not dead\<close>
  assumes "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 0"
  shows "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = h"
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
      using reachableFrom_step reachableFromGetLastStateTDNonzero updatesNonZeroCons
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step reachableFromGetLastStateTDNonzero updatesNonZeroCons
      by simp
  next
    case (DEPOSIT address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' \<noteq> tokenDepositAddress")
      case True
      then show ?thesis
        using DEPOSIT reachableFrom_step callDepositOtherAddress[of tokenDepositAddress address']
        using reachableFromGetLastStateTDNonzero updatesNonZeroCons
        by simp
    next
      case False
      show ?thesis
      proof (cases "ID = ID'")
        case True
        then have False
          using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close> callDepositWrittenHash
          using reachableFromGetLastStateTDNonzero updatesNonZeroCons
          by (metis callDepositFailsInDeadState executeStep.simps(1) fst_conv)
        then show ?thesis
          by simp
      next
        case False
        then show ?thesis
          using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close>
          using reachableFromGetLastStateTDNonzero updatesNonZeroCons
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
        using reachableFromGetLastStateTDNonzero updatesNonZeroCons
        by (metis callCancelDepositWhileDeadOtherAddress executeStep.simps(4))
    next
      case True
      have "getLastStateTD contracts' tokenDepositAddress \<noteq> 0"
        using reachableFromGetLastStateTDNonzero[OF \<open>reachableFrom contracts contracts' steps\<close> _ 
                                                    \<open>getLastStateTD contracts tokenDepositAddress \<noteq> 0\<close>]
        using \<open>updatesNonZero (step # steps)\<close> updatesNonZeroCons
        by simp
      then have "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
        using callCancelDepositWhileDeadBridgeDead[of contracts' tokenDepositAddress "message caller' 0" block ID' token' amount' proof' contracts'']
        using CANCEL reachableFrom_step True
        by auto
      then have "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) \<noteq> 0"
        using callCancelDepositWhileDeadInDeadState CANCEL \<open>executeStep contracts' blockNum block step = (Success, contracts'')\<close> \<open>getLastStateTD contracts' tokenDepositAddress \<noteq> 0\<close>
        by (metis executeStep.simps(4))
      then have False
        using \<open>deadState (the (tokenDepositState contracts'' tokenDepositAddress)) = 0\<close>
        by simp
      then show ?thesis
        by simp
    qed
  qed
qed

text \<open>Once written deposit entry cannot only remain the same or be unset to zero\<close>
lemma reachableFromGetDeposit:
  assumes "reachableFrom contracts contracts' steps"
  assumes "h \<noteq> 0"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = h"
  shows "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = h \<or> 
         getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = 0"
  using assms
  sorry


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
  qed
qed

text \<open>When there are no updates, then the last state remains the same\<close>
lemma noUpdateLastState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<nexists> stateRoot. UPDATE address stateRoot \<in> set steps"
  shows "StateOracleState.lastState (the (stateOracleState contracts address)) =  
         StateOracleState.lastState (the (stateOracleState contracts' address))"
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
  qed
qed

lemma hashWrittenOnlyByDeposit:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = 0"
  assumes "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = hash caller token amount"
  (* NOTE: additional assumptions *)
  assumes "hash caller token amount \<noteq> 0"
  assumes hash_inj
  shows "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  show False
    using assms(1-4) *
  proof (induction contracts contracts' steps rule: reachableFrom.induct)
    case (reachableFrom_base contracts)
    then show ?case
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
                     hash caller' token' amount'"
            using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close> callDepositWritesHash
            by (auto simp add: message_def)
          then have "hash caller token amount = hash caller' token' amount'"
            using reachableFrom_step
            by auto
          then have "caller = caller'" "token = token'" "amount = amount'"
            using \<open>hash_inj\<close> unfolding hash_inj_def
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
        using reachableFrom_step callCancelDepositWhileDeadDeposits
        by (smt (verit, ccfv_SIG) ProofVerifier.callCancelDepositWhileDeadOtherAddress ProofVerifier_axioms executeStep.simps(4) list.set_intros(2) lookupNat_delete lookupNat_delete')
    qed
  qed
qed

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
          simp)
  qed
qed


text \<open>If there was at least one update and no updates set zero state, 
      then the last state is not zero\<close>
lemma lastStateNonZero:
  assumes "reachableFrom initContracts contracts steps"
  assumes "let stateOracleAddress = stateOracleAddressB contracts bridgeAddress 
            in UPDATE stateOracleAddress stateRoot \<in> set steps"
  assumes "updatesNonZero steps"
  shows "getLastStateB contracts bridgeAddress \<noteq> 0"
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
    then have *: "getLastStateB contracts' bridgeAddress \<noteq> 0"
      using reachableFrom_step updatesNonZeroCons
      by (smt (verit, ccfv_SIG) reachableFromBridgeStateOracle reachableFrom.reachableFrom_step set_ConsD)
    show "getLastStateB contracts'' bridgeAddress \<noteq> 0"
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
    qed
  qed
qed

(* ----------------------------------------------------------------------------------- *)

text \<open>Conditions that are necessary for bridge functioning (address memorized in contracts should be
      synchronized and all constructors must have been called)\<close>
definition properSetup :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> bool" where
  "properSetup contracts tokenDepositAddress bridgeAddress token = 
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
         stateOracleState contracts (BridgeState.stateOracle (the stateBridge)) \<noteq> None \<and>
         proofVerifierState contracts (BridgeState.proofVerifier (the stateBridge)) \<noteq> None \<and>
         tokenPairsState contracts (BridgeState.tokenPairs (the stateBridge)) \<noteq> None \<and>
         ERC20state contracts token \<noteq> None \<and>
         getMinted (the stateTokenPairs) token \<noteq> 0 \<and>
         ERC20state contracts (getMinted (the stateTokenPairs) token) \<noteq> None)"

lemma properSetup_stateOracleAddress:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
  shows "TokenDepositState.stateOracle (the (tokenDepositState contracts tokenDepositAddress)) = 
         BridgeState.stateOracle (the (bridgeState contracts bridgeAddress))"
  using assms
  unfolding properSetup_def
  by (simp add: Let_def)

lemma properSetup_getLastState:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
  shows "getLastStateB contracts bridgeAddress = getLastStateTD contracts tokenDepositAddress"
  using assms
  by (simp add: properSetup_stateOracleAddress)

lemma callDepositProperSetup [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  by (smt (verit, ccfv_SIG) Hash.callDepositOtherAddress Hash.callDepositOtherToken callDepositBridge callDepositE callDepositERC20state(2) callDepositIBridge callDepositIProofVerifier callDepositIStateOracle callDepositITokenPairs callDepositStateOracle callDepositTokenPairs properSetup_def)

lemma callClaimProperSetup [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  by (smt (verit, best) ProofVerifier.callClaimOtherAddress ProofVerifier.callClaimTokenPairs ProofVerifier_axioms callClaimBridgeState(2) callClaimDeposit callClaimERC20state callClaimIProofVerifier callClaimIStateOracle callClaimITokenDeposit callClaimITokenPairs callClaimProofVerifier callClaimStateOracle properSetup_def)

lemma callUpdateProperSetup [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properSetup_def
  by (smt (verit, best) callUpdateIBridge callUpdateIERC20 callUpdateIProofVerifier callUpdateITokenDeposit callUpdateITokenPairs callUpdateOtherAddress callUpdateStateOracleState(2))

lemma callCancelWhileDeadProperSetup [simp]:
  assumes "callCancelDepositWhileDead contracts address block msg ID token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  unfolding properSetup_def
  by (smt (z3) ProofVerifier.callCancelDepositOtherToken ProofVerifier_axioms callCancelDepositWhileDeadBridge callCancelDepositWhileDeadE callCancelDepositWhileDeadERC20state(2) callCancelDepositWhileDeadIBridge callCancelDepositWhileDeadIProofVerifier callCancelDepositWhileDeadIStateOracle callCancelDepositWhileDeadITokenPairs callCancelDepositWhileDeadOtherAddress callCancelDepositWhileDeadStateOracle callCancelDepositWhileDeadTokenPairse)

lemma properSetupReachable [simp]:
  assumes "reachableFrom contracts contracts' steps"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows "properSetup contracts' tokenDepositAddress bridgeAddress tokenAddress"
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


text \<open>If state oracle last state has changed, it must have been due to an update step.
      One of those updates must be the last update applied.\<close>
lemma lastUpdateHappened:
  assumes "reachableFrom contracts contracts' steps"
  assumes "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
           StateOracleState.lastState (the (stateOracleState contracts' address))"
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
      by (meson Step.simps(8) dual_order.trans reachableFrom.reachableFrom_step set_ConsD set_subset_Cons)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step CLAIM
      by (meson Step.simps(12) dual_order.trans reachableFrom.reachableFrom_step set_ConsD set_subset_Cons)
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
      by (meson Step.simps(15) dual_order.trans reachableFrom.reachableFrom_step set_ConsD set_subset_Cons)
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
      by (meson Step.simps(8) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(12) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(15) reachableFrom.reachableFrom_step set_ConsD)
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
  qed
qed

end

end