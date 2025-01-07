theory DepositClaimProperties
  imports Main Reachability Locales MoreList
begin

context HashProofVerifier
begin

text \<open>Once written deposit hash can be unset only by a @{term "CANCEL_WD"} step\<close>
lemma reachableFromGetDepositBridgeNoCancel:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getDepositTD contracts tokenDepositAddress ID \<noteq> 0"
  assumes "\<nexists> caller amount token proof. CANCEL_WD tokenDepositAddress caller ID token amount proof \<in> set steps"
  shows "getDepositTD contracts' tokenDepositAddress ID = getDepositTD contracts tokenDepositAddress ID"
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
      by (metis executeStep.simps(7) list.set_intros(1) list.set_intros(2) lookupNat_delete')
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis using reachableFrom_step
      using callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress
      by (metis executeStep.simps(8) list.set_intros(2))
  qed auto
qed

text \<open>If the bridge is not dead, there was no @{term "CANCEL_WD"} step\<close>
lemma reachableFromNotBridgeDeadNoCancel:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<not> bridgeDead contracts' tokenDepositAddress"
  shows "\<nexists> caller amount token proof. CANCEL_WD tokenDepositAddress caller ID token amount proof \<in> set steps"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by auto
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  have "\<not> bridgeDead contracts' tokenDepositAddress"
    using reachableFromBridgeDead reachableFrom_step.prems
    by (meson reachableFrom.intros(1) reachableFrom.intros(2) reachableFrom_step(2))
  then have "\<nexists>caller amount token proof. CANCEL_WD tokenDepositAddress caller ID token amount proof \<in> set steps"
    using reachableFrom_step.IH
    by simp
  moreover have "\<nexists>caller amount token proof. CANCEL_WD tokenDepositAddress caller ID token amount proof = step"
    using  callCancelDepositWhileDeadBridgeDead reachableFrom_step.hyps(2) reachableFrom_step.prems
    by (metis executeStep.simps(7))
  ultimately show ?case
    by simp
qed

text \<open>Once written deposit entry cannot be unset while the bridge is alive\<close>
lemma reachableFromGetDepositBridgeNotDead:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<not> bridgeDead contracts' tokenDepositAddress"
  assumes "getDepositTD contracts tokenDepositAddress ID \<noteq> 0"
  shows "getDepositTD contracts' tokenDepositAddress ID = getDepositTD contracts tokenDepositAddress ID"
  using assms reachableFromGetDepositBridgeNoCancel reachableFromNotBridgeDeadNoCancel 
  by meson


text \<open>When the bridge is dead, deposit flags that are zero remain zero\<close>
lemma reachableFromGetDepositBridgeDead:
  assumes "reachableFrom contracts contracts' steps"
  assumes "bridgeDead contracts tokenDepositAddress"
  assumes "getDepositTD contracts tokenDepositAddress ID = 0"
  shows "getDepositTD contracts' tokenDepositAddress ID = 0"
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
      by (metis executeStep.simps(7) lookupNat_delete lookupNat_delete')
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress
      by (metis executeStep.simps(8))
  qed auto
qed

text \<open>Once written deposit entry cannot only remain the same or be unset to zero\<close>
lemma reachableFromGetDeposit:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getDepositTD contracts tokenDepositAddress ID \<noteq> 0"
  shows "getDepositTD contracts' tokenDepositAddress ID = getDepositTD contracts tokenDepositAddress ID \<or>
         getDepositTD contracts' tokenDepositAddress ID = 0"
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
      using callCancelDepositWhileDeadDeposits callCancelDepositWhileDeadOtherAddress
      by (metis (no_types, lifting) executeStep.simps(7) lookupNat_delete lookupNat_delete')
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      using callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress
      by (metis executeStep.simps(8))
  qed auto
qed

end

context StrongHashProofVerifier
begin

text \<open>deposit flag can be set only by an appropriate DEPOSIT step\<close>
lemma getDepositWrittenOnlyByDeposit:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getDepositTD contracts tokenDepositAddress ID = 0"
  assumes "getDepositTD contracts' tokenDepositAddress ID = hash3 caller token amount"
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
          then have "getDepositTD contracts'' tokenDepositAddress ID =
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
        by (metis (no_types, lifting) executeStep.simps(7) list.set_intros(2) lookupNat_delete lookupNat_delete')
    next
      case (WITHDRAW_WD address' caller' token' amount' proof')
      then show ?thesis
        using reachableFrom_step callWithdrawWhileDeadDeposits callWithdrawWhileDeadOtherAddress
        by (metis executeStep.simps(8) list.set_intros(2))
    qed auto
  qed
qed

end

context HashProofVerifier
begin

text \<open>Only a CLAIM step can change the claim flag value\<close>
lemma reachableFromGetClaimNoClaim:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<nexists> caller token amount proof. CLAIM bridgeAddress caller ID token amount proof \<in> set steps" 
  shows "getClaimB contracts' bridgeAddress ID = 
         getClaimB contracts bridgeAddress ID"
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

text \<open>Once written claim entry cannot be unset\<close>
lemma reachableFromGetClaim:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getClaimB contracts address ID = True"
  shows "getClaimB contracts' address ID = True"
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

text \<open>If a claim is executed, then the claims entry is set\<close>
lemma claimStepSetsClaim:
  assumes "reachableFrom contracts contracts' steps"
  assumes "CLAIM bridgeAddress caller ID token amount proof \<in> set steps"
  shows "getClaimB contracts' bridgeAddress ID = True"
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

(* ----------------------------------------------------------------------------------- *)

text \<open>No DEPOSIT after the bridge dies\<close>
theorem noDepositBridgeDead: 
  assumes "bridgeDead contracts tokenDepositAddress"
  assumes "reachableFrom contracts contracts' steps"
  shows "fst (callDeposit contracts' tokenDepositAddress block msg ID token amount) \<noteq> Success"
  using assms callDepositFailsInDeadState reachableFromBridgeDead
  by blast

text \<open>No DEPOSIT after the deposits entry is set\<close>
lemma noDepositAfterGetDepositNonzero:
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
  assumes "getDepositTD contracts tokenDepositAddress ID \<noteq> 0"
  assumes "reachableFrom contracts contracts' steps"
  shows False
  using assms
  by (smt (verit, best) executeStep.simps(1) callDepositFailsInDeadState callDepositWrittenHash fst_conv reachableFromGetDepositBridgeNotDead reachableFromStepInSteps)

end

context StrongHashProofVerifier
begin

text \<open>There are no double deposits\<close>
theorem callDepositNoDouble:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"         
  assumes "reachableFrom contracts' contracts'' steps"
  shows "fst (callDeposit contracts'' address block' msg' ID token' amount') \<noteq> Success"
proof (cases "bridgeDead contracts'' address")
  case False
  have "getDepositTD contracts' address ID = hash3 (sender msg) token amount"
    using callDepositWritesHash[OF assms(1)]
    by simp
  then have "getDepositTD contracts'' address ID \<noteq> 0"
    using False reachableFromGetDepositBridgeNotDead hash3_nonzero[of "sender msg" token amount] assms
    by auto
  then show ?thesis
    using callDepositWrittenHash by blast
next
  case True
  then show ?thesis
    using callDepositFailsInDeadState 
    by presburger
qed

end

context HashProofVerifier
begin

text \<open>There are no double claims\<close>
theorem callClaimNoDouble:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
          "reachableFrom contracts' contracts'' steps"
    shows "fst (callClaim contracts'' address msg' ID token' amount' proof') \<noteq> Success"
proof-
  define state' where "state' = the (bridgeState contracts' address)"
  have "getClaim state' ID = True"
    using assms
    by (simp add: callClaimWritesClaim state'_def)
  then have "getClaimB contracts'' address ID = True"
    using \<open>reachableFrom contracts' contracts'' steps\<close>
    unfolding state'_def
    using reachableFromGetClaim
    by blast
  then show ?thesis
    using callClaimGetClaimFalse
    by (metis prod.collapse)
qed

end

context StrongHashProofVerifier
begin

text \<open>We prove that there cannot be two DEPOSIT steps with the same ID on the same tokenDeposit address\<close>

lemma DEPOSITNoDoubleCons:
  assumes "reachableFrom contracts contracts' (DEPOSIT tokenDepositAddress caller ID token amount # steps)"
  shows "\<nexists> token' caller' amount'. DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps"
  by (smt (verit) assms callDepositNoDouble executeStep.simps(1) fst_conv reachableFromCons' reachableFromStepInSteps)


lemma DEPOSITNoDouble:
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps3"
  shows False
  using assms
  by (metis DEPOSITNoDoubleCons Un_iff append_Cons list.set_intros(1) reachableFromAppend set_append)

lemma DEPOSITNoDouble':
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2"
  shows "\<nexists> token' caller' amount'. DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set (steps1 @ steps2)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain token' caller' amount' where
    "DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps1 \<or> 
     DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps2"
    by auto
  then show False
  proof
    assume "DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps1"
    then obtain steps1' steps1'' where "steps1 = steps1' @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps1''"
      by (metis Cons_eq_appendI in_set_conv_decomp_first self_append_conv2)
    then show False
      using DEPOSITNoDouble[OF assms(1), of steps1' tokenDepositAddress caller' ID token' amount' steps1'' caller token amount steps2] assms
      by auto
  next
    assume "DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps2"
    then obtain steps2' steps2'' where "steps2 = steps2' @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps2''"
      by (metis Cons_eq_appendI in_set_conv_decomp_first self_append_conv2)
    then show False
      using DEPOSITNoDouble[OF assms(1), of steps1 tokenDepositAddress caller ID token amount steps2' caller' token' amount' steps2''] assms
      by auto
  qed
qed

lemma DEPOSITNoDoubleCTA:
  assumes "reachableFrom contracts contracts' steps"
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
  assumes "DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps"
  shows "caller' = caller \<and> token' = token \<and> amount' = amount"
proof-
  obtain steps1 steps2 where steps: "steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2"
    using assms(1) assms(2) reachableFromStepInSteps by blast
  then have "DEPOSIT tokenDepositAddress caller' ID token' amount' \<notin> set steps1 \<union> set steps2"
    using DEPOSITNoDouble'[OF assms(1)]
    by auto
  then show ?thesis
    using steps assms
    by auto
qed

text \<open>We prove that there cannot be two CLAIM steps with the same ID on the same bridge address\<close>

lemma CLAIMNoDoubleCons:
  assumes "reachableFrom contracts contracts' (CLAIM bridgeAddress caller ID token amount proof # steps)"
  shows "\<nexists> token' caller' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set steps"
proof (rule ccontr)
  obtain contracts'' where *:
   "reachableFrom contracts contracts'' steps"
   "callClaim contracts'' bridgeAddress (message caller amount) ID token amount proof = (Success, contracts')"
    using reachableFromCons'[OF assms(1)]
    by auto

  moreover

  assume "~ ?thesis"
  then obtain token' caller' amount' proof' where **: "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set steps"
    by auto
  obtain c1 c2 steps1 steps2 where ***:
    "steps = steps1 @ [CLAIM bridgeAddress caller' ID token' amount' proof'] @ steps2"
    "reachableFrom contracts c1 steps2" "reachableFrom c2 contracts'' steps1"
    "callClaim c1 bridgeAddress (message caller' amount') ID token' amount' proof' = (Success, c2)"
    using reachableFromStepInSteps[OF *(1) **]
    by auto metis

  then have "fst (callClaim contracts'' bridgeAddress (message caller amount) ID token amount proof) \<noteq> Success"
    using callClaimNoDouble
    by auto

  ultimately
  show False
    by simp
qed

lemma CLAIMNoDouble:
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [CLAIM bridgeAddress caller ID token amount proof] @ steps2 @ [CLAIM bridgeAddress caller' ID token' amount' proof'] @ steps3"
  shows False
proof-
  obtain contracts'' where *: 
    "reachableFrom contracts'' contracts' steps1"
    "reachableFrom contracts contracts'' (CLAIM bridgeAddress caller ID token amount proof # (steps2 @ [CLAIM bridgeAddress caller' ID token' amount' proof'] @ steps3))"
    using assms(1-2) reachableFromAppend[of contracts contracts' steps1]
    by auto
  then show False
    using CLAIMNoDoubleCons[OF *(2)]
    by auto
qed

lemma CLAIMNoDouble':
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [CLAIM bridgeAddress caller ID token amount proof] @ steps2"
  shows "\<nexists> token' caller' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set (steps1 @ steps2)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain token' caller' amount' proof' where
    "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set steps1 \<or> 
     CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set steps2"
    by auto
  then show False
  proof
    assume "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set steps1"
    then obtain steps1' steps1'' where "steps1 = steps1' @ [CLAIM bridgeAddress caller' ID token' amount' proof'] @ steps1''"
      by (metis Cons_eq_appendI in_set_conv_decomp_first self_append_conv2)
    then show False
      using CLAIMNoDouble[OF assms(1), of steps1' bridgeAddress caller' ID token' amount' proof' steps1'' caller token amount "proof" steps2] assms
      by auto
  next
    assume "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set steps2"
    then obtain steps2' steps2'' where "steps2 = steps2' @ [CLAIM bridgeAddress caller' ID token' amount' proof'] @ steps2''"
      by (metis Cons_eq_appendI in_set_conv_decomp_first self_append_conv2)
    then show False
      using CLAIMNoDouble[OF assms(1), of steps1 bridgeAddress caller ID token amount "proof" steps2' caller' token' amount' proof' steps2''] assms
      by auto
  qed
qed

end


context LastUpdate
begin

text \<open>CLAIM succeeds only if the appropriate deposits entry is set\<close>
theorem callClaimGetDeposit:
  assumes "callClaim contractsLU bridgeAddress msg ID token amount proof = (Success, contractsClaim)"
  shows "getDepositTD contractsLastUpdate' tokenDepositAddress ID = 
         hash3 (sender msg) token amount"
proof-
  have "verifyDepositProof () tokenDepositAddress ID (hash3 (sender msg) token amount) stateRoot proof = True"
    using callClaimVerifyProof[OF assms] lastStateBLU
    using depositLU by blast
  then show ?thesis
    using verifyDepositProofE
    by (metis generateStateRootUpdate' option.collapse tokenDepositStateUpdate'NotNone)
qed

end


context StrongHashProofVerifier
begin

(* ------------------------------------------------------------------------------------ *)
(*
               deposit           [steps]            claim
    contractsD   \<rightarrow>   contractsD'  \<rightarrow>*   contractsC    \<rightarrow>   contractsC'
    properSetup                  UPDATE
*)
text \<open>Only user who made the deposit can make a successful claim with the same ID\<close>
lemma onlyDepositorCanClaim:
  \<comment> \<open>deposit is done a properly configured state state\<close>
  assumes "properSetup contractsD tokenDepositAddress bridgeAddress"
  assumes deposit: "callDeposit contractsD tokenDepositAddress block msg ID token amount = (Success, contractsD')"
  \<comment> \<open>after a while a  claim is made\<close>
  assumes "reachableFrom contractsD' contractsC steps"
  assumes claim: "callClaim contractsC bridgeAddress msg' ID token' amount' proof = (Success, contractsC')"
  \<comment> \<open>in the meantime a state oracle update is made\<close>
  assumes update: "\<exists> stateRoot. UPDATE (stateOracleAddressB contractsD bridgeAddress) stateRoot \<in> set steps"

  (* FIXME: amount must be the same as the value of the message - this assumption can be removed when the definition of executeStep is changed *)
  assumes "val msg = amount"

  shows "sender msg = sender msg'" "token = token'" "amount = amount'"
proof-
  have "getDepositTD contractsD' tokenDepositAddress ID = hash3 (sender msg) token amount"
    using callDepositWritesHash deposit
    by simp

  define stateOracleAddress where "stateOracleAddress = stateOracleAddressB contractsD bridgeAddress"

  obtain stateRoot where update: "UPDATE (stateOracleAddressB contractsD bridgeAddress) stateRoot \<in> set steps"
    using assms
    by auto

  let ?update = "UPDATE (stateOracleAddressB contractsD bridgeAddress) stateRoot"

  obtain steps1 steps2 contractsU contractsU' blockU blockNumU where *:
   "reachableFrom contractsD' contractsU steps2"
   "executeStep contractsU blockU blockNumU ?update = (Success, contractsU')"
   "reachableFrom contractsU' contractsC steps1"
    using reachableFromStepInSteps[OF \<open>reachableFrom contractsD' contractsC steps\<close> update]
    by (smt (verit, ccfv_threshold) assms(3) in_set_conv_decomp_last reachableFromAppend reachableFromCons' update)

  let ?d = "DEPOSIT tokenDepositAddress (sender msg) ID token amount"
  let ?u = "UPDATE stateOracleAddress stateRoot"

  have "stateOracleAddressB contractsD' bridgeAddress = stateOracleAddressB contractsD bridgeAddress"
    using Hash.callDepositIBridge deposit 
    by presburger

  have **: "callUpdate contractsU stateOracleAddress blockNumU blockU stateRoot = (Success, contractsU')"
    using \<open>executeStep contractsU blockU blockNumU (UPDATE (stateOracleAddressB contractsD bridgeAddress) stateRoot) = (Success, contractsU')\<close> 
    unfolding stateOracleAddress_def 
    by auto

  obtain contractsUx contractsU'x blockx blockNumx steps1x steps2x stateRootx where *:
    "reachableFrom contractsD' contractsUx steps1x"
    "stateRootx = generateStateRoot contractsUx"
    "callUpdate contractsUx stateOracleAddress blockx blockNumx stateRootx = (Success, contractsU'x)"
    "reachableFrom contractsU'x contractsC steps2x"
    "\<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps2x"
    using lastUpdateHappened'[OF \<open>reachableFrom contractsD' contractsU steps2\<close> ** \<open>reachableFrom contractsU' contractsC steps1\<close>]
    by metis

  interpret LastUpdate': LastUpdate where
     contractsLastUpdate'=contractsUx and 
     contractsLastUpdate=contractsU'x and
     contractsLU=contractsC and
     stepsNoUpdate=steps2x and
     blockLastUpdate=blockx and
     blockNumLastUpdate=blockNumx and
     stateRoot = stateRootx
  proof
    show "properSetup contractsUx tokenDepositAddress bridgeAddress"
      using \<open>reachableFrom contractsD' contractsUx steps1x\<close> assms(1) deposit by auto
  next
    show "let stateOracleAddress = stateOracleAddressB contractsUx bridgeAddress
           in callUpdate contractsUx stateOracleAddress blockx blockNumx stateRootx = (Success, contractsU'x)"
      using * \<open>stateOracleAddressB contractsD' bridgeAddress = stateOracleAddressB contractsD bridgeAddress\<close> 
      unfolding stateOracleAddress_def
      by simp
  next
    show "reachableFrom contractsU'x contractsC steps2x"
      by fact
  next
    show "let stateOracleAddress = stateOracleAddressB contractsU'x bridgeAddress
           in \<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps2x"
      using * \<open>stateOracleAddressB contractsD' bridgeAddress = stateOracleAddressB contractsD bridgeAddress\<close>
      unfolding stateOracleAddress_def
      by simp
  qed

  have "getDepositTD contractsUx tokenDepositAddress ID = hash3 (sender msg') token' amount'"
    using LastUpdate'.callClaimGetDeposit[OF claim]
    by simp

  have "hash3 (sender msg) token amount = hash3 (sender msg') token' amount'"
    using reachableFromGetDeposit
    using \<open>getDepositTD contractsD' tokenDepositAddress ID = hash3 (sender msg) token amount\<close> 
    using \<open>getDepositTD contractsUx tokenDepositAddress ID = hash3 (sender msg') token' amount'\<close>
    using \<open>callUpdate contractsUx stateOracleAddress blockx blockNumx stateRootx = (Success, contractsU'x)\<close>
    using hash3_nonzero
    using \<open>reachableFrom contractsD' contractsUx steps1x\<close>
    by (metis callUpdateITokenDeposit)
  then show "sender msg = sender msg'" "token = token'" "amount = amount'"
    using hash3_inj
    unfolding hash3_inj_def
    by metis+
qed

end


context InitFirstUpdate
begin

text \<open>Before every successful claim, a deposit must have been made\<close>
theorem depositBeforeClaim:
  \<comment> \<open>Claim was successful\<close>
  assumes "callClaim contractsI bridgeAddress msg ID token amount proof = (Success, contractsClaim)"
  \<comment> \<open>The correct deposit must have happened\<close>
  shows "DEPOSIT tokenDepositAddress (sender msg) ID token amount \<in> set stepsInit"
proof-
  define stateOracleAddress where "stateOracleAddress = stateOracleAddressB contractsInit bridgeAddress"
  have "lastState (the (stateOracleState contractsInit stateOracleAddress)) = 0"
    using lastStateBZero stateOracleAddress_def by blast
  moreover
  have "lastState (the (stateOracleState contractsI stateOracleAddress)) \<noteq> 0"
    by (metis getLastStateBContractsUNonZero reachableFromBridgeStateOracle reachableFromInitI stateOracleAddress_def)
  ultimately
  obtain contractsU contractsU' block blockNum steps1 steps2 stateRoot' where *:
    "reachableFrom contractsInit contractsU steps1"
    "stateRoot' = generateStateRoot contractsU"
    "callUpdate contractsU stateOracleAddress block blockNum stateRoot' = (Success, contractsU')"
    "reachableFrom contractsU' contractsI steps2"
    "\<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps2"
    "set steps1 \<subseteq> set stepsInit"
    using lastUpdateHappened[OF reachableFromInitI, of stateOracleAddress]
    by auto

  interpret LastUpdate': LastUpdate where 
    contractsLastUpdate'=contractsU and
    contractsLastUpdate=contractsU' and
    contractsLU=contractsI and
    stepsNoUpdate=steps2 and
    blockLastUpdate=block and
    blockNumLastUpdate=blockNum and
    stateRoot=stateRoot'
  proof
    show "properSetup contractsU tokenDepositAddress bridgeAddress"
      using \<open>reachableFrom contractsInit contractsU steps1\<close> assms(1) 
      by auto
  next
    show "let stateOracleAddress = stateOracleAddressB contractsU bridgeAddress
           in callUpdate contractsU stateOracleAddress block blockNum stateRoot' = (Success, contractsU')"
      by (metis "*"(1) "*"(3) reachableFromBridgeStateOracle stateOracleAddress_def)
  next
    show "reachableFrom contractsU' contractsI steps2"
      by fact
  next
    show "let stateOracleAddress = stateOracleAddressB contractsU' bridgeAddress
           in \<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps2"
      by (metis "*"(4) "*"(5) reachableFromBridgeStateOracle reachableFromInitI stateOracleAddress_def)
  qed

  have "getDepositTD contractsU tokenDepositAddress ID = hash3 (sender msg) token amount"
    using assms LastUpdate'.callClaimGetDeposit
    by (smt (verit, best) reachableFromBridgeStateOracle callUpdateITokenDeposit properSetupReachable stateOracleAddress_def)
  then show ?thesis
    using getDepositWrittenOnlyByDeposit
    using depositsEmpty assms
    using \<open>reachableFrom contractsInit contractsU steps1\<close> \<open>set steps1 \<subseteq> set stepsInit\<close>
    by blast
qed

lemma UpdateBetweenDepositAndClaim:
  assumes steps: "steps = [CLAIM bridgeAddress caller' ID token' amount' proof'] @ steps2 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps1" 
  assumes "reachableFrom contractsI contracts steps" 
  shows "\<exists> stateRoot. UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRoot \<in> set steps2"
proof-
  interpret Init: Init where contractsI = contracts and stepsInit = "steps @ stepsInit"
    using Init'_axioms Init_axioms.intro Init_def assms(2) reachableFromTrans by auto

  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"
  let ?CLAIM_step = "CLAIM bridgeAddress caller' ID token' amount' proof'"
  obtain contractsD' contractsD contractsC' contractsC where reach:
   "reachableFrom contractsI contractsD' steps1"
   "reachableFrom contractsD' contractsD [?DEPOSIT_step]"
   "reachableFrom contractsD contractsC' steps2"
   "reachableFrom contractsC' contractsC [?CLAIM_step]"
    using assms
    by (meson reachableFromAppend)

  let ?soAddress = "stateOracleAddressB contractsInit bridgeAddress"
  have *: "\<exists> stateRoot. UPDATE ?soAddress stateRoot \<in> set (tl steps @ stepsInit)"
    by (metis Nil_is_append_conv firstUpdate last_appendR last_in_set)

  have **: "reachableFrom contractsInit contractsC' (tl steps @ stepsInit)"
    by (smt (verit, ccfv_threshold) Cons_eq_appendI list.sel(3) reach(1) reach(2) reach(3) reachableFromInitI reachableFromTrans self_append_conv2 steps)

  obtain contracts' steps1' steps2' stateRoot
    where "reachableFrom contractsInit contracts' steps1'" 
          "stateRoot = generateStateRoot contracts'"
          "tl steps @ stepsInit = steps2' @ [UPDATE ?soAddress stateRoot] @ steps1'"
          "\<nexists> stateRoot'. UPDATE ?soAddress stateRoot' \<in> set steps2'" and
  reach': "reachableFrom contracts' contractsC' (steps2' @ [UPDATE ?soAddress stateRoot])"
    using lastUpdateHappenedSteps'[OF ** *]
    by auto

  then obtain contracts1 blockU blockNumU where
    "callUpdate contracts' ?soAddress blockU blockNumU stateRoot = (Success, contracts1)"
    "reachableFrom contracts1 contractsC' steps2'"
    by (metis executeStep.simps(6) reachableFromAppend reachableFromSingleton)

  interpret LU: LastUpdate where 
        stateRoot=stateRoot and 
        contractsLastUpdate=contracts1 and 
        blockLastUpdate=blockU and blockNumLastUpdate=blockNumU and
        contractsLastUpdate'=contracts' and contractsLU=contractsC' and stepsNoUpdate = steps2'
  proof
    show "properSetup contracts' tokenDepositAddress bridgeAddress"
      using \<open>reachableFrom contractsInit contracts' steps1'\<close> by auto
  next
    show "let stateOracleAddress = stateOracleAddressB contracts' bridgeAddress
           in callUpdate contracts' stateOracleAddress blockU blockNumU stateRoot =
              (Success, contracts1)"
      by (metis HashProofVerifier.reachableFromBridgeStateOracle HashProofVerifier_axioms \<open>callUpdate contracts' (stateOracleAddressB contractsInit bridgeAddress) blockU blockNumU stateRoot = (Success, contracts1)\<close> \<open>reachableFrom contractsInit contracts' steps1'\<close>)
  next
    show "reachableFrom contracts1 contractsC' steps2'"
      by fact
  next
    show "let stateOracleAddress = stateOracleAddressB contracts1 bridgeAddress
           in \<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps2'"
      using \<open>\<nexists>stateRoot'. UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRoot' \<in> set steps2'\<close> \<open>callUpdate contracts' (stateOracleAddressB contractsInit bridgeAddress) blockU blockNumU stateRoot = (Success, contracts1)\<close> \<open>reachableFrom contractsInit contracts' steps1'\<close> by auto
  qed

  have getDeposit: "getDepositTD contracts' tokenDepositAddress ID = hash3 caller' token' amount'"
    using LU.callClaimGetDeposit
    by (metis executeStep.simps(2) reach(4) reachableFromSingleton senderMessage)

  have "steps2 @ [?DEPOSIT_step] @ steps1 @ stepsInit = steps2' @ [UPDATE ?soAddress stateRoot] @ steps1'" (is "?lhs = ?rhs")
    using steps \<open>tl steps @ stepsInit = steps2' @ [UPDATE ?soAddress stateRoot] @ steps1'\<close> by auto
  moreover
  have "length steps1' \<ge> length (steps1 @ stepsInit)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "length (steps1 @ stepsInit) \<ge> length steps1'"
      by simp
    then have "?DEPOSIT_step \<in> set (steps2' @ [UPDATE ?soAddress stateRoot])"
      using \<open>?lhs = ?rhs\<close> append_subset(1)[where xs="steps2' @ [UPDATE ?soAddress stateRoot]" and xs'="steps2 @ [?DEPOSIT_step]" and ys=steps1' and ys'="steps1@stepsInit"]
      by auto
    then show False
      using getDeposit reach' noDepositAfterGetDepositNonzero hash3_nonzero
      by metis
  qed
  then have "UPDATE ?soAddress stateRoot \<in> set ([?DEPOSIT_step] @ rev steps2)"
    using \<open>?lhs = ?rhs\<close> append_subset(1)[where ys="steps1@stepsInit" and ys'="steps1'" and xs="steps2 @ [?DEPOSIT_step]" and xs'="steps2' @ [UPDATE ?soAddress stateRoot]"]
    by auto
  then show ?thesis
    by force
qed

lemma depositBeforeClaimSteps:
  assumes "stepsInit = steps2 @ [CLAIM bridgeAddress caller ID token amount proof] @ steps1"
  shows "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps1"
proof-
  obtain steps1' where bl: "butlast stepsInit = steps2 @ [CLAIM bridgeAddress caller ID token amount proof] @ steps1'"
    using firstUpdate
    by (metis Step.simps(29) append.assoc append.right_neutral assms butlast_append last.simps last_appendR list.discI)

  obtain contractsC' contractsC where CC':
     "reachableFrom contractsInit contractsC (steps1' @ [last stepsInit])"
     "reachableFrom contractsC contractsC' [CLAIM bridgeAddress caller ID token amount proof]"
    using bl
    by (smt (verit, del_insts) append_butlast_last_id firstUpdate reachableFromAppend reachableFromInitI reachableFromTrans)
  interpret IFU: InitFirstUpdate where
      contractsI=contractsC and stepsInit="steps1' @ [last stepsInit]"
    using bl
    by (metis Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def CC'(1) append.assoc append_butlast_last_id append_is_Nil_conv firstUpdate last_snoc not_Cons_self2 stateRootInitNonZero)
  have "DEPOSIT tokenDepositAddress caller ID token amount \<in> set (steps1' @ [last stepsInit])"
    using IFU.depositBeforeClaim CC'(2)
    by (metis executeStep.simps(2) reachableFromSingleton senderMessage)
  then show ?thesis
    using bl assms
    by (metis append.assoc append_butlast_last_id firstUpdate same_append_eq)
qed

lemma noClaimBeforeDeposit:
  assumes CLAIM_in_steps: "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
  assumes reach: "reachableFrom contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
  shows "False"
proof-
  define DEPOSIT_step where "DEPOSIT_step = DEPOSIT tokenDepositAddress caller ID token amount"
  define CLAIM_step where "CLAIM_step = CLAIM bridgeAddress caller' ID token' amount' proof'"

  have reach: "reachableFrom contractsInit contractsDeposit (DEPOSIT_step # stepsInit)"
    using reach
    using DEPOSIT_step_def reachableFromTrans by fastforce

  have CLAIM_in_steps: "CLAIM_step \<in> set (DEPOSIT_step # stepsInit)"
    using CLAIM_in_steps
    unfolding CLAIM_step_def
    by simp
  obtain steps1 steps2 c1 c2 blockNum block where *:
    "reachableFrom contractsInit c1 steps2"
    "executeStep c1 blockNum block CLAIM_step = (Success, c2)"
    "reachableFrom c2 contractsDeposit steps1"
    "DEPOSIT_step # stepsInit = steps1 @ [CLAIM_step] @ steps2"
    using reachableFromStepInSteps reach CLAIM_in_steps
    unfolding DEPOSIT_step_def
    by metis

  define DEPOSIT_step' where "DEPOSIT_step' = DEPOSIT tokenDepositAddress (sender (message caller' amount')) ID token' amount'"

  interpret Init': Init
    by unfold_locales

  interpret InitFirstUpdate': InitFirstUpdate where contractsI=c1 and stepsInit=steps2
    by (metis (no_types, lifting) "*"(1) "*"(4) CLAIM_step_def HashProofVerifier.Step.distinct(22) HashProofVerifier_axioms Init'_axioms Init.intro InitFirstUpdate.intro InitFirstUpdate_axioms.intro Init_axioms.intro append_is_Nil_conv firstUpdate last.simps last_append not_Cons_self stateRootInitNonZero)

  have "DEPOSIT_step' \<in> set steps2"
    using * InitFirstUpdate'.depositBeforeClaim
    unfolding CLAIM_step_def DEPOSIT_step'_def
   by fastforce

  moreover

  obtain steps1' where "steps1 = DEPOSIT_step # steps1'"
    using *(4)
    unfolding DEPOSIT_step_def CLAIM_step_def
    by (metis Cons_eq_append_conv Step.simps(9) list.sel(1))

  ultimately

  have "DEPOSIT_step' \<in> set stepsInit"
    using *(4)
    by auto
  then obtain d1 d2 where "DEPOSIT_step # stepsInit = [] @ [DEPOSIT_step] @ d1 @ [DEPOSIT_step'] @ d2"
    by (metis append.left_neutral append_Cons split_list_first)
  then show False
    using DEPOSITNoDouble reach
    unfolding DEPOSIT_step_def DEPOSIT_step'_def
     by blast
qed

lemma noClaimBeforeDepositSteps:
  assumes "stepsInit = steps3 @ [DEPOSIT tokenDepositAddress caller' ID token' amount']  @ steps2 @ [CLAIM bridgeAddress caller ID token amount proof] @ steps1"
  shows False
proof-
  let ?claimStep = "CLAIM bridgeAddress caller ID token amount proof"
  obtain contracts where C: "reachableFrom contractsInit contracts ([?claimStep] @ steps1)"
    by (metis assms reachableFromAppend reachableFromInitI)
  interpret IFU: InitFirstUpdate where contractsI=contracts and stepsInit="[?claimStep] @ steps1"
    using C Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def assms firstUpdate stateRootInitNonZero by auto
  have "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps1"
    using IFU.depositBeforeClaimSteps
    by auto
  then show False
    using assms 
    by (metis DEPOSITNoDouble' Un_iff reachableFromInitI set_append)
qed

lemma noClaimBeforeDepositSteps':
  assumes "stepsInit = steps1 @ steps2" 
  assumes "DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps1" (is "?D \<in> set steps1")
          "CLAIM bridgeAddress caller ID token amount proof \<in> set steps2" (is "?C \<in> set steps2")
  shows False
proof-
  obtain s1' s1'' where "steps1 = s1' @ [?D] @ s1''"
    using assms
    by (metis append_Cons self_append_conv2 split_list_first)
  moreover
  obtain s2' s2'' where "steps2 = s2' @ [?C] @ s2''"
    using assms
    by (metis append_Cons self_append_conv2 split_list_first)
  ultimately
  show False
    using assms noClaimBeforeDepositSteps
    by (metis append.assoc)
qed

end

context InitFirstUpdate
begin

lemma onlyDepositorCanClaimSteps:
  assumes "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set stepsInit"
  shows "caller' = caller" "token' = token" "amount' = amount"
  using onlyDepositorCanClaim
proof-
  obtain steps1 steps2 where *: "stepsInit = steps1 @ [CLAIM bridgeAddress caller' ID token' amount' proof'] @ steps2"
    using assms
    by (metis append_Cons append_Nil in_set_conv_decomp_first)
  then have D1: "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps2"
    using assms noClaimBeforeDepositSteps
    by (cases "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps1",
        smt (verit, best) append.assoc reachableFromAppend reachableFromInitI reachableFromStepInSteps,
        auto)
  then have D2: "DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps2"
    using depositBeforeClaimSteps *
    by auto
  moreover
  obtain c where "reachableFrom contractsInit c steps2"
    by (metis "*" reachableFromAppend reachableFromInitI)
  then have "caller' = caller \<and> token' = token \<and> amount' = amount"
    using DEPOSITNoDoubleCTA[OF _ D1 D2]
    by simp
  then show "caller' = caller" "token' = token" "amount' = amount"
    by auto
qed

end


end
