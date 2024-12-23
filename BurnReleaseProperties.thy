theory BurnReleaseProperties
  imports Reachability Locales
begin

context HashProofVerifier
begin

\<comment> \<open>Once written withdraw hash cannot be unset\<close>
lemma reachableFromGetWithdrawalNoUnset:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getWithdrawal (the (bridgeState contracts bridgeAddress)) ID \<noteq> 0"
  shows "getWithdrawal (the (bridgeState contracts' bridgeAddress)) ID = 
         getWithdrawal (the (bridgeState contracts bridgeAddress)) ID"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (BURN address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' = bridgeAddress \<and> ID'=ID")
      case True
      then show ?thesis
        using BURN reachableFrom_step
        using callWithdrawGetWithdrawalZero 
        by (metis executeStep.simps(3))
    next
      case False
      then show ?thesis
        using BURN reachableFrom_step
        using callWithdrawOtherAddress callWithdrawOtherID
        by (metis executeStep.simps(3))
    qed
  qed auto
qed

end

context StrongHashProofVerifier
begin

text \<open>deposit flag can be set only by an appropriate DEPOSIT step\<close>
lemma getWithrawalWrittenOnlyByBURN:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getWithdrawal (the (bridgeState contracts bridgeAddress)) ID = 0"
  assumes "getWithdrawal (the (bridgeState contracts' bridgeAddress)) ID = hash3 caller token amount"
  shows "BURN bridgeAddress caller ID token amount \<in> set steps"
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
      case (BURN address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' \<noteq> bridgeAddress")
        case True
        then show ?thesis
          using BURN reachableFrom_step callWithdrawOtherAddress[OF True[symmetric]]
          by (metis executeStep.simps(3) list.set_intros(2))
      next
        case False
        show ?thesis
        proof (cases "ID \<noteq> ID'")
          case True
          then show ?thesis
            using BURN reachableFrom_step \<open>\<not> address' \<noteq> bridgeAddress\<close>
            by simp
        next
          case False
          then have "getWithdrawal (the (bridgeState contracts'' bridgeAddress)) ID =
                     hash3 caller' token' amount'"
            using BURN reachableFrom_step \<open>\<not> address' \<noteq> bridgeAddress\<close> callWithdrawWritesWithdrawal
            by (metis executeStep.simps(3) senderMessage)
          then have "hash3 caller token amount = hash3 caller' token' amount'"
            using reachableFrom_step
            by auto
          then have "caller = caller'" "token = token'" "amount = amount'"
            using hash3_inj unfolding hash3_inj_def
            by blast+
          then show False
            using BURN reachableFrom_step \<open>\<not> ID \<noteq> ID'\<close>
            by auto
        qed
      qed
    qed auto
  qed
qed

\<comment> \<open>Only BURN step can set withrawal flag to non-zero\<close>
lemma reachableFromGetWithdrawalBurn:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getWithdrawal (the (bridgeState contracts bridgeAddress)) ID = 0"
  assumes "getWithdrawal (the (bridgeState contracts' bridgeAddress)) ID \<noteq> 0"
  shows "\<exists> caller token amount. BURN bridgeAddress caller ID token amount \<in> set steps"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "getWithdrawal (the (bridgeState contracts' bridgeAddress)) ID \<noteq> 0")
    case True
    then show ?thesis
      using reachableFrom_step
      by auto
  next
    case False
    then show ?thesis
      using reachableFrom_step.hyps reachableFrom_step.prems(2)
    proof (cases step)
      case (BURN address' caller' ID' token' amount')
      then show ?thesis
        using reachableFrom_step.hyps reachableFrom_step.prems(2)
        using callWithdrawOtherAddress callWithdrawOtherID
        by (metis False executeStep.simps(3) list.set_intros(1))
    qed auto
  qed
qed


\<comment> \<open>BURN is not executable once the withdrawal flag is set\<close>
lemma reachableFromGetWithrawalNoBurn:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getWithdrawal (the (bridgeState contracts bridgeAddress)) ID \<noteq> 0"
  shows "\<nexists> caller token amount. BURN bridgeAddress caller ID token amount \<in> set steps"
  using assms
  by (smt (verit, best) HashProofVerifier.reachableFromStepInSteps HashProofVerifier_axioms callWithdrawGetWithdrawalZero executeStep.simps(3) reachableFromGetWithdrawalNoUnset)

text \<open>Once written release entry cannot be unset\<close>
lemma reachableFromGetReleaseTrue:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getRelease (the (tokenDepositState contracts address)) ID = True"
  shows "getRelease (the (tokenDepositState contracts' address)) ID = True"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step callReleaseNotReleased[of contracts'] callReleaseOtherID callReleaseOtherAddress
      by (metis executeStep.simps(4))
  qed auto
qed

end

context StrongHashProofVerifier
begin


(* ------------------------------------------------------------------------------------ *)
text \<open>There are no double burns\<close>
lemma callWithdrawNoDouble:
  assumes "callWithdraw contracts address msg ID token amount = (Success, contracts')"         
  assumes "reachableFrom contracts' contracts'' steps"
  shows "fst (callWithdraw contracts'' address msg' ID token' amount') \<noteq> Success"
  using assms
  using callWithdrawGetWithdrawalZero callWithdrawWritesWithdrawal reachableFromGetWithdrawalNoUnset
  by (metis hash3_nonzero prod.collapse)

text \<open>There are no double releases\<close>
theorem callReleaseNoDouble:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
          "reachableFrom contracts' contracts'' steps"
    shows "fst (callRelease contracts'' address msg' ID token' amount' proof') \<noteq> Success"
proof-
  define state' where "state' = the (tokenDepositState contracts' address)"
  have "getRelease state' ID = True"
    using assms
    by (simp add: state'_def)
  then have *: "getRelease (the (tokenDepositState contracts' address)) ID = True"
    using state'_def
    by simp
  from \<open>reachableFrom contracts' contracts'' steps\<close>
  have "getRelease (the (tokenDepositState contracts'' address)) ID = True"
    using *
    using reachableFromGetReleaseTrue by blast
  then show ?thesis
    using callReleaseNotReleased
    by (metis split_pairs)
qed

end

context StrongHashProofVerifier
begin

text \<open>We want to prove that there cannot be two BURN steps with the same ID on the same bridge address\<close>

lemma BURNNoDoubleCons:
  assumes "reachableFrom contracts contracts' (BURN bridgeAddress caller ID token amount # steps)"
  shows "\<nexists> token' caller' amount'. BURN bridgeAddress caller' ID token' amount' \<in> set steps"
  using assms callWithdrawNoDouble 
  by (smt (verit) executeStep.simps(3) fst_eqD reachableFromCons' reachableFromStepInSteps)
 

lemma BURNNoDouble:
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [BURN bridgeAddress caller ID token amount] @ steps2 @ [BURN bridgeAddress caller' ID token' amount'] @ steps3"
  shows False
  using assms
  by (metis BURNNoDoubleCons Un_iff append_Cons list.set_intros(1) reachableFromAppend set_append)

lemma BURNNoDouble':
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [BURN bridgeAddress caller ID token amount] @ steps2"
  shows "\<nexists> token' caller' amount'. BURN bridgeAddress caller' ID token' amount' \<in> set (steps1 @ steps2)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain token' caller' amount' where
    "BURN bridgeAddress caller' ID token' amount' \<in> set steps1 \<or> 
     BURN bridgeAddress caller' ID token' amount' \<in> set steps2"
    by auto
  then show False
  proof
    assume "BURN bridgeAddress caller' ID token' amount' \<in> set steps1"
    then obtain steps1' steps1'' where "steps1 = steps1' @ [BURN bridgeAddress caller' ID token' amount'] @ steps1''"
      by (metis Cons_eq_appendI in_set_conv_decomp_first self_append_conv2)
    then show False
      using BURNNoDouble[OF assms(1), of steps1' bridgeAddress caller' ID token' amount' steps1'' caller token amount steps2] assms
      by auto
  next
    assume "BURN bridgeAddress caller' ID token' amount' \<in> set steps2"
    then obtain steps2' steps2'' where "steps2 = steps2' @ [BURN bridgeAddress caller' ID token' amount'] @ steps2''"
      by (metis Cons_eq_appendI in_set_conv_decomp_first self_append_conv2)
    then show False
      using BURNNoDouble[OF assms(1), of steps1 bridgeAddress caller ID token amount steps2' caller' token' amount' steps2''] assms
      by auto
  qed
qed

lemma BURNNoDoubleCTA:
  assumes "reachableFrom contracts contracts' steps"
  assumes "BURN bridgeAddress caller ID token amount \<in> set steps"
  assumes "BURN bridgeAddress caller' ID token' amount' \<in> set steps"
  shows "caller' = caller \<and> token' = token \<and> amount' = amount"
proof-
  obtain steps1 steps2 where steps: "steps = steps1 @ [BURN bridgeAddress caller ID token amount] @ steps2"
    using assms(1) assms(2) reachableFromStepInSteps by blast
  then have "BURN bridgeAddress caller' ID token' amount' \<notin> set steps1 \<union> set steps2"
    using BURNNoDouble'[OF assms(1)]
    by auto
  then show ?thesis
    using steps assms
    by auto
qed

end

context StrongHashProofVerifier
begin

text \<open>We want to prove that there cannot be two RELEASE steps with the same ID on the same tokenDeposit address\<close>

lemma RELEASENoDoubleCons:
  assumes "reachableFrom contracts contracts' (RELEASE tokenDepositAddress caller ID token amount proof # steps)"
  shows "\<nexists> token' caller' amount' proof'. RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set steps"
proof (rule ccontr)
  obtain contracts'' where *:
   "reachableFrom contracts contracts'' steps"
   "callRelease contracts'' tokenDepositAddress (message caller 0) ID token amount proof = (Success, contracts')"
    using reachableFromCons'[OF assms(1)]
    by auto

  moreover

  assume "~ ?thesis"
  then obtain token' caller' amount' proof' where **: "RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set steps"
    by auto
  obtain c1 c2 steps1 steps2 where ***:
    "steps = steps1 @ [RELEASE tokenDepositAddress caller' ID token' amount' proof'] @ steps2"
    "reachableFrom contracts c1 steps2" "reachableFrom c2 contracts'' steps1"
    "callRelease c1 tokenDepositAddress (message caller' 0) ID token' amount' proof' = (Success, c2)"
    using reachableFromStepInSteps[OF *(1) **]
    by auto metis

  then have "fst (callRelease contracts'' tokenDepositAddress (message caller 0) ID token amount proof) \<noteq> Success"
    using callReleaseNoDouble
    by blast
    
  ultimately
  show False
    by simp
qed

lemma RELEASENoDouble:
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [RELEASE tokenDepositAddress caller ID token amount proof] @ steps2 @ [RELEASE tokenDepositAddress caller' ID token' amount' proof'] @ steps3"
  shows False
proof-
  obtain contracts'' where *: 
    "reachableFrom contracts'' contracts' steps1"
    "reachableFrom contracts contracts'' (RELEASE tokenDepositAddress caller ID token amount proof # (steps2 @ [RELEASE tokenDepositAddress caller' ID token' amount' proof'] @ steps3))"
    using assms(1-2) reachableFromAppend[of contracts contracts' steps1]
    by auto
  then show False
    using RELEASENoDoubleCons[OF *(2)]
    by auto
qed

lemma RELEASENoDouble':
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [RELEASE tokenDepositAddress caller ID token amount proof] @ steps2"
  shows "\<nexists> token' caller' amount' proof'. RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set (steps1 @ steps2)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain token' caller' amount' proof' where
    "RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set steps1 \<or> 
     RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set steps2"
    by auto
  then show False
  proof
    assume "RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set steps1"
    then obtain steps1' steps1'' where "steps1 = steps1' @ [RELEASE tokenDepositAddress caller' ID token' amount' proof'] @ steps1''"
      by (metis Cons_eq_appendI in_set_conv_decomp_first self_append_conv2)
    then show False
      using RELEASENoDouble[OF assms(1), of steps1' tokenDepositAddress caller' ID token' amount' proof' steps1'' caller token amount "proof" steps2] assms
      by auto
  next
    assume "RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set steps2"
    then obtain steps2' steps2'' where "steps2 = steps2' @ [RELEASE tokenDepositAddress caller' ID token' amount' proof'] @ steps2''"
      by (metis Cons_eq_appendI in_set_conv_decomp_first self_append_conv2)
    then show False
      using RELEASENoDouble[OF assms(1), of steps1 tokenDepositAddress caller ID token amount "proof" steps2' caller' token' amount' proof' steps2''] assms
      by auto
  qed
qed

end

context HashProofVerifier
begin

(* FIXME: move *)
lemma callUpdateBridgeNotDeadLastValidState:
  assumes "callUpdate contracts (stateOracleAddressTD contracts address) block blockNum stateRoot = (Success, contracts')"
  assumes "\<not> bridgeDead contracts address"
  shows "snd (lastValidStateTD contracts' address) = stateRoot"
  using assms
  by (metis callLastState callLastStateI callUpdateITokenDeposit callUpdateLastState callUpdateStateOracleState(2) lastValidState_def surjective_pairing)

end

context HashProofVerifier
begin

(* FIXME: move *)
lemma noUpdateNotBridgeDead:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<not> bridgeDead contracts tokenDepositAddress" "lastStateTD contracts tokenDepositAddress = 0"
  assumes "\<nexists> stateRoot. UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot \<in> set steps"
  shows "\<not> bridgeDead contracts' tokenDepositAddress"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (metis (no_types, lifting) BridgeDiesDeadState reachableFromDepositStateOracle list.set_intros(2) noUpdateLastState)
qed

end

context Init
begin

(* FIXME: move *)
lemma UPDATEToLastValidStateExists:
  assumes "\<exists> stateRoot. UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) stateRoot \<in> set stepsInit"
  shows "UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) (snd (lastValidStateTD contractsI tokenDepositAddress)) \<in> set stepsInit"
  using reachableFromInitI assms Init_axioms
proof (induction contractsInit contractsI stepsInit rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    unfolding InitFirstUpdate_def InitFirstUpdate_axioms_def
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "steps = []")
    case True
    then obtain stateRoot where step: "step = UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot"
      using reachableFrom_step.prems(1)
      by auto
    interpret Init' where contractsInit=contracts
      by (meson InitFirstUpdate_def Init_def reachableFrom_step.prems)
    interpret I: Init where contractsInit=contracts and contractsI=contracts'' and stepsInit="[step]"
      using True reachableFrom_step.prems by force
    show ?thesis
      using True reachableFrom_step.hyps step callUpdateBridgeNotDeadLastValidState notDead
      by (smt (verit, best)  executeStep.simps(6) list.discI list.set_intros(1) reachableFrom.simps)
  next
    case False
    interpret I: Init where contractsInit=contracts and contractsI=contracts'' and stepsInit="step#steps"
      using reachableFrom_step.prems by blast
    interpret I': Init where contractsInit=contracts and contractsI=contracts' and stepsInit=steps
      by (simp add: I.Init'_axioms Init.intro Init_axioms.intro reachableFrom_step.hyps(1))

    show ?thesis
    proof (cases "\<exists>stateRoot. UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot \<in> set steps")
      case True
      then have *: "UPDATE (stateOracleAddressTD contracts tokenDepositAddress) (snd (lastValidStateTD contracts' tokenDepositAddress)) \<in> set steps"
        using reachableFrom_step.IH I'.Init_axioms 
        by fastforce
      show ?thesis
        using * noUpdateGetLastValidStateTD[OF reachableFrom_step.hyps(2), of tokenDepositAddress]
      proof (cases step)
        case (UPDATE address' stateRoot')
        then show ?thesis
          using * reachableFrom_step.hyps
          using  \<open>\<nexists>stateRoot'. step = UPDATE (stateOracleAddressTD contracts' tokenDepositAddress) stateRoot' \<Longrightarrow> lastValidStateTD contracts'' tokenDepositAddress = lastValidStateTD contracts' tokenDepositAddress\<close>
          by (smt (verit, ccfv_SIG) callUpdateBridgeNotDeadLastValidState executeStep.simps(6) I'.stateOracleAddressTDI callUpdateDeadState lastValidState_def list.set_intros(1) list.set_intros(2))
      qed auto
    next
      case False
      then obtain stateRoot where step: "step = UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot"
        using reachableFrom_step.prems
        by auto

      have "\<not> bridgeDead contracts' tokenDepositAddress"
        using noUpdateNotBridgeDead[OF reachableFrom_step.hyps(1) I.notDead I.lastStateTDZeroInit False]
        by blast
      then show ?thesis
        by (metis False I'.stateOracleAddressTDI callUpdateBridgeNotDeadLastValidState executeStep.simps(6) reachableFrom_step.hyps(2) reachableFrom_step.prems(1) set_ConsD)
    qed
  qed
qed

end


context InitFirstUpdate
begin

text \<open>Before every successful release, a burn must have been made\<close>
theorem burnBeforeRelease:
  \<comment> \<open>Claim was successful\<close>
  assumes "callRelease contractsI tokenDepositAddress msg ID token amount proof = (Success, contractsRelease)"
  \<comment> \<open>The correct burn must have happened\<close>
  shows "BURN bridgeAddress (sender msg) ID token amount \<in> set stepsInit"
proof-
  from assms 
  have *: "verifyBurnProof () bridgeAddress ID (hash3 (sender msg) token amount)
       (snd (lastValidStateTD contractsI tokenDepositAddress)) proof = True"
    using callReleaseVerifyBurnProof[OF assms(1)]
    by simp

  let ?stateRoot = "snd (lastValidStateTD contractsI tokenDepositAddress)"
  let ?UPDATE_step = "UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) ?stateRoot"
  obtain steps1 steps2 where steps: "stepsInit = steps1 @ [?UPDATE_step] @ steps2" 
    using UPDATEToLastValidStateExists
    using reachableFromStepInSteps reachableFromInitI 
    by (metis firstUpdate last_in_set properSetupI properSetup_stateOracleAddress stateOracleAddressBI stateOracleAddressTDI)

  then obtain contracts where 
    **: "reachableFrom contractsInit contracts steps2" "reachableFrom contracts contractsI (steps1 @ [?UPDATE_step])"
    by (metis append_eq_appendI reachableFromAppend reachableFromInitI)

  then obtain contracts' where "reachableFrom contracts contracts' [?UPDATE_step]"
    by (meson reachableFromAppend)
  then obtain blockNum block where "callUpdate contracts (stateOracleAddressTD contracts tokenDepositAddress) block blockNum ?stateRoot = (Success, contracts')"
    by (metis "**"(1) executeStep.simps(6) reachableFromDepositStateOracle reachableFromSingleton)
  then have ***: "generateStateRoot contracts = ?stateRoot"
    using updateSuccess[of contracts "stateOracleAddressTD contracts tokenDepositAddress" _ _ ?stateRoot]
    by simp

  have "getWithdrawal (the (bridgeState contractsInit bridgeAddress)) ID = 0"
    using withdrawalsEmpty by blast
  moreover
  have "getWithdrawal (the (bridgeState contracts bridgeAddress)) ID = hash3 (sender msg) token amount"
    using verifyBurnProofE[OF *** *] **
    by (meson option.exhaust_sel properSetupInit properSetupReachable properSetup_def)
  ultimately 
  have "BURN bridgeAddress (sender msg) ID token amount \<in> set steps2"
    using getWithrawalWrittenOnlyByBURN **
    by presburger
  then show ?thesis
    using steps
    by auto
qed


lemma burnBeforeReleaseSteps:
  assumes "stepsInit = steps2 @ [RELEASE tokenDepositAddress caller ID token amount proof] @ steps1"
  shows "BURN bridgeAddress caller ID token amount \<in> set steps1"
proof-
  obtain steps1' where bl: "butlast stepsInit = steps2 @ [RELEASE tokenDepositAddress caller ID token amount proof] @ steps1'"
    using firstUpdate assms
    by (metis (no_types, lifting) Nil_is_append_conv Step.simps(47) butlast_append snoc_eq_iff_butlast)

  obtain contractsC' contractsC where CC':
     "reachableFrom contractsInit contractsC (steps1' @ [last stepsInit])"
     "reachableFrom contractsC contractsC' [RELEASE tokenDepositAddress caller ID token amount proof]"
    using bl
    by (smt (verit, del_insts) append_butlast_last_id firstUpdate reachableFromAppend reachableFromInitI reachableFromTrans)
  interpret IFU: InitFirstUpdate where contractsI=contractsC and stepsInit="steps1' @ [last stepsInit]"
    using bl
    by (metis Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def CC'(1) append.assoc append_butlast_last_id append_is_Nil_conv firstUpdate last_snoc not_Cons_self2 updatesNonZeroAppend(2) updatesNonZeroInit)
  have "BURN bridgeAddress caller ID token amount \<in> set (steps1' @ [last stepsInit])"
    using IFU.burnBeforeRelease CC'(2)
    by (metis executeStep.simps(4) reachableFromSingleton senderMessage)
  then show ?thesis
    using bl assms
    by (metis append.assoc append_butlast_last_id firstUpdate same_append_eq)
qed

lemma noReleaseBeforeBurn:
  assumes RELEASE_in_steps: "RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set stepsInit"
  assumes reach: "reachableFrom contractsI contractsBurn [BURN bridgeAddress caller ID token amount]"
  shows "False"
proof-
  define BURN_step where "BURN_step = BURN bridgeAddress caller ID token amount"
  define RELEASE_step where "RELEASE_step = RELEASE tokenDepositAddress caller' ID token' amount' proof'"

  have reach: "reachableFrom contractsInit contractsBurn (BURN_step # stepsInit)"
    using reach
    using BURN_step_def reachableFromTrans by fastforce

  have RELEASE_in_steps: "RELEASE_step \<in> set (BURN_step # stepsInit)"
    using RELEASE_in_steps
    unfolding RELEASE_step_def
    by simp
  obtain steps1 steps2 c1 c2 blockNum block where *:
    "reachableFrom contractsInit c1 steps2"
    "executeStep c1 blockNum block RELEASE_step = (Success, c2)"
    "reachableFrom c2 contractsBurn steps1"
    "BURN_step # stepsInit = steps1 @ [RELEASE_step] @ steps2"
    using reachableFromStepInSteps reach RELEASE_in_steps
    unfolding BURN_step_def
    by metis

  define BURN_step' where "BURN_step' = BURN bridgeAddress (sender (message caller' amount')) ID token' amount'"

  interpret Init': Init
    by unfold_locales

  interpret IFU: InitFirstUpdate where contractsI=c1 and stepsInit=steps2
  proof
    show "reachableFrom contractsInit c1 steps2" by fact
   next
    show "updatesNonZero steps2"
      by (metis "*"(4) Cons_eq_append_conv add_cancel_right_right list.size(4) nat.simps(3) updatesNonZeroAppend(2) updatesNonZeroInit)
  next
    show "steps2 \<noteq> [] \<and> last steps2 = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
      by (metis "*"(4) HashProofVerifier.Step.distinct(40) HashProofVerifier_axioms Nil_is_append_conv RELEASE_step_def firstUpdate last.simps last_append not_Cons_self)
  qed

  have "BURN_step' \<in> set steps2"
    using * IFU.burnBeforeRelease
    unfolding RELEASE_step_def BURN_step'_def
   by fastforce

  moreover

  obtain steps1' where "steps1 = BURN_step # steps1'"
    using *(4)
    unfolding BURN_step_def RELEASE_step_def
    by (metis Step.simps(35) append_eq_Cons_conv list.sel(1))

  ultimately

  have "BURN_step' \<in> set stepsInit"
    using *(4)
    by auto
  then obtain d1 d2 where "BURN_step # stepsInit = [] @ [BURN_step] @ d1 @ [BURN_step'] @ d2"
    by (metis append.left_neutral append_Cons split_list_first)
  then show False
    using BURNNoDouble reach
    unfolding BURN_step_def BURN_step'_def
    by blast
qed

lemma noReleaseBeforeBurnSteps:
  assumes "stepsInit = steps3 @ [BURN bridgeAddress caller' ID token' amount'] @ steps2 @ [RELEASE tokenDepositAddress caller ID token amount proof] @ steps1"
  shows False
  using assms
proof-
  let ?releaseStep = "RELEASE tokenDepositAddress caller ID token amount proof"
  obtain contracts where C: "reachableFrom contractsInit contracts ([?releaseStep] @ steps1)"
    by (metis assms reachableFromAppend reachableFromInitI)
  interpret IFU: InitFirstUpdate where contractsI=contracts and stepsInit="[?releaseStep] @ steps1"
  proof
    show "[?releaseStep] @ steps1 \<noteq> [] \<and> last ([?releaseStep] @ steps1) = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
      using assms firstUpdate by force
  next
    show "updatesNonZero ([?releaseStep] @ steps1)"
      using assms updatesNonZeroAppend(2) updatesNonZeroInit by blast
  next 
    show "reachableFrom contractsInit contracts ([?releaseStep] @ steps1)"
      by fact
  qed

  have "BURN bridgeAddress caller ID token amount \<in> set steps1"
    using IFU.burnBeforeReleaseSteps
    by auto
  then show False
    using assms 
    by (metis BURNNoDouble' Un_iff reachableFromInitI set_append)
qed

lemma noReleaseBeforBurnSteps':
  assumes "stepsInit = steps1 @ steps2" 
  assumes "BURN bridgeAddress caller' ID token' amount' \<in> set steps1" (is "?B \<in> set steps1")
          "RELEASE tokenDepositAddress caller ID token amount proof \<in> set steps2" (is "?R \<in> set steps2")
    shows False
proof-
  obtain s1' s1'' where "steps1 = s1' @ [?B] @ s1''"
    using assms
    by (metis append_Cons self_append_conv2 split_list_first)
  moreover
  obtain s2' s2'' where "steps2 = s2' @ [?R] @ s2''"
    using assms
    by (metis append_Cons self_append_conv2 split_list_first)
  ultimately
  show False
    using assms noReleaseBeforeBurnSteps
    by (metis append.assoc)
qed

end

context InitUpdateBridgeNotDeadLastValidState
begin

text \<open>Before every successful release, a burn before the last state update must have been made\<close>
theorem burnBeforeRelease:
  \<comment> \<open>Claim was successful\<close>
  assumes "callRelease contractsLVS tokenDepositAddress msg ID token amount proof = (Success, contractsRelease)"
  \<comment> \<open>The correct burn must have happened\<close>
  shows "BURN bridgeAddress (sender msg) ID token amount \<in> set stepsInit"
proof-
  have *: "verifyBurnProof () bridgeAddress ID (hash3 (sender msg) token amount)
           stateRoot proof = True"
    using callReleaseVerifyBurnProof[OF assms(1)] getLastValidStateLVS
    by simp

  have "getWithdrawal (the (bridgeState contractsInit bridgeAddress)) ID = 0"
    using withdrawalsEmpty by blast
  moreover
  have "getWithdrawal (the (bridgeState contractsUpdate' bridgeAddress)) ID = hash3 (sender msg) token amount"
    using verifyBurnProofE[OF _ *] bridgeStateINotNone generateStateRootUpdate' 
    by (metis option.collapse)
  ultimately 
  show "BURN bridgeAddress (sender msg) ID token amount \<in> set stepsInit"
    using getWithrawalWrittenOnlyByBURN
    using reachableFromInitI 
    by blast
qed

end

end