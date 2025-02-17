theory BurnReleaseProperties
  imports Reachability Locales
begin

context HashProofVerifier
begin


\<comment> \<open>Once written withdraw hash cannot be unset\<close>
lemma reachableGetWithdrawalNoUnset:
  assumes "reachable contracts contracts' steps"
  assumes "getWithdrawalB contracts bridgeAddress ID \<noteq> 0"
  shows "getWithdrawalB contracts' bridgeAddress ID = getWithdrawalB contracts bridgeAddress ID"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (BURN address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' = bridgeAddress \<and> ID'=ID")
      case True
      then show ?thesis
        using BURN reachable_step
        using callWithdrawGetWithdrawalZero 
        by (metis executeStep.simps(3))
    next
      case False
      then show ?thesis
        using BURN reachable_step
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
  assumes "reachable contracts contracts' steps"
  assumes "getWithdrawalB contracts bridgeAddress ID = 0"
  assumes "getWithdrawalB contracts' bridgeAddress ID = hash3 caller token amount"
  shows "BURN bridgeAddress caller ID token amount \<in> set steps"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  show False
    using assms *
  proof (induction contracts contracts' steps rule: reachable.induct)
    case (reachable_base contracts)
    then show ?case
      using hash3_nonzero
      by simp
  next
    case (reachable_step steps contracts'' contracts contracts' blockNum block step)
    then show ?case
    proof (cases step)
      case (BURN address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' \<noteq> bridgeAddress")
        case True
        then show ?thesis
          using BURN reachable_step callWithdrawOtherAddress[OF True[symmetric]]
          by (metis executeStep.simps(3) list.set_intros(2))
      next
        case False
        show ?thesis
        proof (cases "ID \<noteq> ID'")
          case True
          then show ?thesis
            using BURN reachable_step \<open>\<not> address' \<noteq> bridgeAddress\<close>
            by simp
        next
          case False
          then have "getWithdrawalB contracts'' bridgeAddress ID = hash3 caller' token' amount'"
            using BURN reachable_step \<open>\<not> address' \<noteq> bridgeAddress\<close> callWithdrawWritesWithdrawal
            by (metis executeStep.simps(3) senderMessage)
          then have "hash3 caller token amount = hash3 caller' token' amount'"
            using reachable_step
            by auto
          then have "caller = caller'" "token = token'" "amount = amount'"
            using hash3_inj unfolding hash3_inj_def
            by blast+
          then show False
            using BURN reachable_step \<open>\<not> ID \<noteq> ID'\<close>
            by auto
        qed
      qed
    qed auto
  qed
qed

\<comment> \<open>Only BURN step can set withrawal flag to non-zero\<close>
lemma reachableGetWithdrawalBurn:
  assumes "reachable contracts contracts' steps"
  assumes "getWithdrawalB contracts bridgeAddress ID = 0"
  assumes "getWithdrawalB contracts' bridgeAddress ID \<noteq> 0"
  shows "\<exists> caller token amount. BURN bridgeAddress caller ID token amount \<in> set steps"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "getWithdrawalB contracts' bridgeAddress ID \<noteq> 0")
    case True
    then show ?thesis
      using reachable_step
      by auto
  next
    case False
    then show ?thesis
      using reachable_step.hyps reachable_step.prems(2)
    proof (cases step)
      case (BURN address' caller' ID' token' amount')
      then show ?thesis
        using reachable_step.hyps reachable_step.prems(2)
        using callWithdrawOtherAddress callWithdrawOtherID
        by (metis False executeStep.simps(3) list.set_intros(1))
    qed auto
  qed
qed

\<comment> \<open>BURN is not executable once the withdrawal flag is set\<close>
lemma reachableGetWithrawalNoBurn:
  assumes "reachable contracts contracts' steps"
  assumes "getWithdrawalB contracts bridgeAddress ID \<noteq> 0"
  shows "\<nexists> caller token amount. BURN bridgeAddress caller ID token amount \<in> set steps"
  using assms
  by (smt (verit, best) HashProofVerifier.reachableStepInSteps HashProofVerifier_axioms callWithdrawGetWithdrawalZero executeStep.simps(3) reachableGetWithdrawalNoUnset)

\<comment> \<open>BURN step sets the withdrawal flag\<close>
lemma reachableBurnSetsFlag:
  assumes "reachable contracts contracts' steps"
  assumes "BURN address caller ID token amount \<in> set steps"
  shows "getWithdrawalB contracts' address ID = hash3 caller token amount"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases "BURN address caller ID token amount \<in> set steps")
    case True
    then have "getWithdrawalB contracts' address ID = hash3 caller token amount"
      using reachable_step.IH by auto
    then show ?thesis
      using hash3_nonzero[of caller token amount]
      using reachableGetWithdrawalNoUnset[of contracts' contracts'' "[step]"]
      by (metis reachable.reachable_step reachable_base reachable_step.hyps(2))
  next
    case False
    then have "step = BURN address caller ID token amount"
      using reachable_step.prems
      by simp
    then show ?thesis
      using reachable_step.hyps(2)
      by (simp add: callWithdrawWritesWithdrawal)
  qed
qed

(* ---------------------------------------------------------------------_ *)

text \<open>Once written release entry cannot be unset\<close>
lemma reachableGetReleaseTrue:
  assumes "reachable contracts contracts' steps"
  assumes "getReleaseTD contracts address ID = True"
  shows "getReleaseTD contracts' address ID = True"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step callReleaseNotReleased[of contracts'] callReleaseOtherID callReleaseOtherAddress
      by (metis executeStep.simps(4))
  qed auto
qed

lemma reachableReleaseSetsFlag:
  assumes "reachable contracts contracts' steps"
  assumes "RELEASE address caller ID token amount proof \<in> set steps"
  shows "getReleaseTD contracts' address ID = True"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases "RELEASE address caller ID token amount proof \<in> set steps")
    case True
    then show ?thesis
      using reachable.reachable_step reachableGetReleaseTrue reachable_base reachable_step.IH reachable_step.hyps(2) 
      by blast
  next
    case False
    then have "step = RELEASE address caller ID token amount proof"
      using reachable_step.prems
      by simp
    then show ?thesis
      using reachable_step.hyps(2)
      by simp
  qed
qed

lemma getReleaseNoReleaseFalse:
  assumes "reachable contracts contracts' steps"
  assumes "\<nexists> token caller amount proof. RELEASE tokenDepositAddress caller ID token amount proof \<in> set steps"
  assumes "getReleaseTD contracts tokenDepositAddress ID = False"
  shows "getReleaseTD contracts' tokenDepositAddress ID = False"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case 
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (RELEASE address' caller' ID' token' amount' proof')
    show ?thesis
      using reachable_step.prems RELEASE reachable_step.IH reachable_step.hyps(2)
      using callReleaseOtherAddress callReleaseOtherID
      by (metis executeStep.simps(4) list.set_intros(1) list.set_intros(2))
  qed auto
qed

end

context StrongHashProofVerifier
begin


(* ------------------------------------------------------------------------------------ *)
text \<open>There are no double burns\<close>
lemma callWithdrawNoDouble:
  assumes "callWithdraw contracts address msg ID token amount = (Success, contracts')"         
  assumes "reachable contracts' contracts'' steps"
  shows "fst (callWithdraw contracts'' address msg' ID token' amount') \<noteq> Success"
  using assms
  using callWithdrawGetWithdrawalZero callWithdrawWritesWithdrawal reachableGetWithdrawalNoUnset
  by (metis hash3_nonzero prod.collapse)

text \<open>There are no double releases\<close>
theorem callReleaseNoDouble:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
          "reachable contracts' contracts'' steps"
    shows "fst (callRelease contracts'' address msg' ID token' amount' proof') \<noteq> Success"
proof-
  define state' where "state' = the (tokenDepositState contracts' address)"
  have "getRelease state' ID = True"
    using assms
    by (simp add: state'_def)
  then have *: "getReleaseTD contracts' address ID = True"
    using state'_def
    by simp
  from \<open>reachable contracts' contracts'' steps\<close>
  have "getReleaseTD contracts'' address ID = True"
    using *
    using reachableGetReleaseTrue by blast
  then show ?thesis
    using callReleaseNotReleased
    by (metis split_pairs)
qed

end

context StrongHashProofVerifier
begin

text \<open>We want to prove that there cannot be two BURN steps with the same ID on the same bridge address\<close>

lemma BURNNoDoubleCons:
  assumes "reachable contracts contracts' (BURN bridgeAddress caller ID token amount # steps)"
  shows "\<nexists> token' caller' amount'. BURN bridgeAddress caller' ID token' amount' \<in> set steps"
  using assms callWithdrawNoDouble 
  by (smt (verit) executeStep.simps(3) fst_eqD reachableCons' reachableStepInSteps)
 

lemma BURNNoDouble:
  assumes "reachable contracts contracts' steps"
  assumes "steps = steps1 @ [BURN bridgeAddress caller ID token amount] @ steps2 @ [BURN bridgeAddress caller' ID token' amount'] @ steps3"
  shows False
  using assms
  by (metis BURNNoDoubleCons Un_iff append_Cons list.set_intros(1) reachableAppend set_append)

lemma BURNNoDouble':
  assumes "reachable contracts contracts' steps"
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
  assumes "reachable contracts contracts' steps"
  assumes "BURN bridgeAddress caller ID token amount \<in> set steps"
  assumes "BURN bridgeAddress caller' ID token' amount' \<in> set steps"
  shows "caller' = caller \<and> token' = token \<and> amount' = amount"
proof-
  obtain steps1 steps2 where steps: "steps = steps1 @ [BURN bridgeAddress caller ID token amount] @ steps2"
    using assms(1) assms(2) reachableStepInSteps by blast
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
  assumes "reachable contracts contracts' (RELEASE tokenDepositAddress caller ID token amount proof # steps)"
  shows "\<nexists> token' caller' amount' proof'. RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set steps"
proof (rule ccontr)
  obtain contracts'' where *:
   "reachable contracts contracts'' steps"
   "callRelease contracts'' tokenDepositAddress (message caller 0) ID token amount proof = (Success, contracts')"
    using reachableCons'[OF assms(1)]
    by auto

  moreover

  assume "~ ?thesis"
  then obtain token' caller' amount' proof' where **: "RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set steps"
    by auto
  obtain c1 c2 steps1 steps2 where ***:
    "steps = steps1 @ [RELEASE tokenDepositAddress caller' ID token' amount' proof'] @ steps2"
    "reachable contracts c1 steps2" "reachable c2 contracts'' steps1"
    "callRelease c1 tokenDepositAddress (message caller' 0) ID token' amount' proof' = (Success, c2)"
    using reachableStepInSteps[OF *(1) **]
    by auto metis

  then have "fst (callRelease contracts'' tokenDepositAddress (message caller 0) ID token amount proof) \<noteq> Success"
    using callReleaseNoDouble
    by blast
    
  ultimately
  show False
    by simp
qed

lemma RELEASENoDouble:
  assumes "reachable contracts contracts' steps"
  assumes "steps = steps1 @ [RELEASE tokenDepositAddress caller ID token amount proof] @ steps2 @ [RELEASE tokenDepositAddress caller' ID token' amount' proof'] @ steps3"
  shows False
proof-
  obtain contracts'' where *: 
    "reachable contracts'' contracts' steps1"
    "reachable contracts contracts'' (RELEASE tokenDepositAddress caller ID token amount proof # (steps2 @ [RELEASE tokenDepositAddress caller' ID token' amount' proof'] @ steps3))"
    using assms(1-2) reachableAppend[of contracts contracts' steps1]
    by auto
  then show False
    using RELEASENoDoubleCons[OF *(2)]
    by auto
qed

lemma RELEASENoDouble':
  assumes "reachable contracts contracts' steps"
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


context Init
begin

(* FIXME: move *)
lemma UPDATEToLastValidStateExists:
  assumes "\<exists> stateRoot. UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) stateRoot \<in> set stepsInit"
  shows "UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) (snd (lastValidStateTD contractsI tokenDepositAddress)) \<in> set stepsInit"
  using reachableInitI assms Init_axioms
proof (induction contractsInit contractsI stepsInit rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    unfolding InitFirstUpdate_def InitFirstUpdate_axioms_def
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "steps = []")
    case True
    then obtain stateRoot where step: "step = UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot"
      using reachable_step.prems(1)
      by auto
    interpret Init' where contractsInit=contracts
      by (meson InitFirstUpdate_def Init_def reachable_step.prems)
    interpret I: Init where contractsInit=contracts and contractsI=contracts'' and stepsInit="[step]"
      using True reachable_step.prems by force
    show ?thesis
      using True reachable_step.hyps step callUpdateBridgeNotDeadLastValidState notDead
      by (smt (verit, best)  executeStep.simps(6) list.discI list.set_intros(1) reachable.simps)
  next
    case False
    interpret I: Init where contractsInit=contracts and contractsI=contracts'' and stepsInit="step#steps"
      using reachable_step.prems by blast
    interpret I': Init where contractsInit=contracts and contractsI=contracts' and stepsInit=steps
      by (simp add: I.Init'_axioms Init.intro Init_axioms.intro reachable_step.hyps(1))

    show ?thesis
    proof (cases "\<exists>stateRoot. UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot \<in> set steps")
      case True
      then have *: "UPDATE (stateOracleAddressTD contracts tokenDepositAddress) (snd (lastValidStateTD contracts' tokenDepositAddress)) \<in> set steps"
        using reachable_step.IH I'.Init_axioms 
        by fastforce
      show ?thesis
        using * noUpdateGetLastValidStateTD[OF reachable_step.hyps(2), of tokenDepositAddress]
      proof (cases step)
        case (UPDATE address' stateRoot')
        then show ?thesis
          using * reachable_step.hyps
          using  \<open>\<nexists>stateRoot'. step = UPDATE (stateOracleAddressTD contracts' tokenDepositAddress) stateRoot' \<Longrightarrow> lastValidStateTD contracts'' tokenDepositAddress = lastValidStateTD contracts' tokenDepositAddress\<close>
          by (smt (verit, ccfv_SIG) callUpdateBridgeNotDeadLastValidState executeStep.simps(6) I'.stateOracleAddressTDI callUpdateDeadState lastValidState_def list.set_intros(1) list.set_intros(2))
      qed auto
    next
      case False
      then obtain stateRoot where step: "step = UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot"
        using reachable_step.prems
        by auto

      have "\<not> bridgeDead contracts' tokenDepositAddress"
        using noUpdateNotBridgeDead[OF reachable_step.hyps(1) I.notDead I.lastStateTDZeroInit False]
        by blast
      then show ?thesis
        by (metis False I'.stateOracleAddressTDI callUpdateBridgeNotDeadLastValidState executeStep.simps(6) reachable_step.hyps(2) reachable_step.prems(1) set_ConsD)
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
    using reachableStepInSteps reachableInitI 
    by (metis firstUpdate last_in_set properSetupI properSetup_stateOracleAddress stateOracleAddressBI stateOracleAddressTDI)

  then obtain contracts where 
    **: "reachable contractsInit contracts steps2" "reachable contracts contractsI (steps1 @ [?UPDATE_step])"
    by (metis append_eq_appendI reachableAppend reachableInitI)

  then obtain contracts' where "reachable contracts contracts' [?UPDATE_step]"
    by (meson reachableAppend)
  then obtain blockNum block where "callUpdate contracts (stateOracleAddressTD contracts tokenDepositAddress) block blockNum ?stateRoot = (Success, contracts')"
    by (metis "**"(1) executeStep.simps(6) reachableDepositStateOracle reachableSingleton)
  then have ***: "generateStateRoot contracts = ?stateRoot"
    using updateSuccess[of contracts "stateOracleAddressTD contracts tokenDepositAddress" _ _ ?stateRoot]
    by simp

  have "getWithdrawalB contractsInit bridgeAddress ID = 0"
    using withdrawalsEmpty by blast
  moreover
  have "getWithdrawalB contracts bridgeAddress ID = hash3 (sender msg) token amount"
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
     "reachable contractsInit contractsC (steps1' @ [last stepsInit])"
     "reachable contractsC contractsC' [RELEASE tokenDepositAddress caller ID token amount proof]"
    using bl
    by (smt (verit, del_insts) append_butlast_last_id firstUpdate reachableAppend reachableInitI reachableTrans)
  interpret IFU: InitFirstUpdate where contractsI=contractsC and stepsInit="steps1' @ [last stepsInit]"
    using bl
    by (metis Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def CC'(1) append.assoc append_butlast_last_id append_is_Nil_conv firstUpdate last_snoc not_Cons_self2 stateRootInitNonZero)
  have "BURN bridgeAddress caller ID token amount \<in> set (steps1' @ [last stepsInit])"
    using IFU.burnBeforeRelease CC'(2)
    by (metis executeStep.simps(4) reachableSingleton senderMessage)
  then show ?thesis
    using bl assms
    by (metis append.assoc append_butlast_last_id firstUpdate same_append_eq)
qed

lemma noReleaseBeforeBurn:
  assumes RELEASE_in_steps: "RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set stepsInit"
  assumes reach: "reachable contractsI contractsBurn [BURN bridgeAddress caller ID token amount]"
  shows "False"
proof-
  define BURN_step where "BURN_step = BURN bridgeAddress caller ID token amount"
  define RELEASE_step where "RELEASE_step = RELEASE tokenDepositAddress caller' ID token' amount' proof'"

  have reach: "reachable contractsInit contractsBurn (BURN_step # stepsInit)"
    using reach
    using BURN_step_def reachableTrans by fastforce

  have RELEASE_in_steps: "RELEASE_step \<in> set (BURN_step # stepsInit)"
    using RELEASE_in_steps
    unfolding RELEASE_step_def
    by simp
  obtain steps1 steps2 c1 c2 blockNum block where *:
    "reachable contractsInit c1 steps2"
    "executeStep c1 blockNum block RELEASE_step = (Success, c2)"
    "reachable c2 contractsBurn steps1"
    "BURN_step # stepsInit = steps1 @ [RELEASE_step] @ steps2"
    using reachableStepInSteps reach RELEASE_in_steps
    unfolding BURN_step_def
    by metis

  define BURN_step' where "BURN_step' = BURN bridgeAddress (sender (message caller' amount')) ID token' amount'"

  interpret Init': Init
    by unfold_locales

  interpret IFU: InitFirstUpdate where contractsI=c1 and stepsInit=steps2
  proof
    show "reachable contractsInit c1 steps2"
      by (simp add: "*"(1))
  next
    show "steps2 \<noteq> [] \<and> last steps2 = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
      by (metis "*"(4) RELEASE_step_def Step.distinct(40) append_is_Nil_conv firstUpdate last.simps last_append not_Cons_self2)
  next
    show "stateRootInit \<noteq> 0"
      by (simp add: stateRootInitNonZero)
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
  obtain contracts where C: "reachable contractsInit contracts ([?releaseStep] @ steps1)"
    by (metis assms reachableAppend reachableInitI)
  interpret IFU: InitFirstUpdate where contractsI=contracts and stepsInit="[?releaseStep] @ steps1"
    using C Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def assms firstUpdate stateRootInitNonZero by auto

  have "BURN bridgeAddress caller ID token amount \<in> set steps1"
    using IFU.burnBeforeReleaseSteps
    by auto
  then show False
    using assms 
    by (metis BURNNoDouble' Un_iff reachableInitI set_append)
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

  have "getWithdrawalB contractsInit bridgeAddress ID = 0"
    using withdrawalsEmpty by blast
  moreover
  have "getWithdrawalB contractsUpdate' bridgeAddress ID = hash3 (sender msg) token amount"
    using verifyBurnProofE[OF _ *] bridgeStateINotNone generateStateRootUpdate' 
    by (metis option.collapse)
  ultimately 
  show "BURN bridgeAddress (sender msg) ID token amount \<in> set stepsInit"
    using getWithrawalWrittenOnlyByBURN
    using reachableInitI 
    by blast
qed

end

context InitFirstUpdate
begin

lemma onlyBurnerCanReleaseSteps:
  assumes "RELEASE tokenDepositAddress caller' ID token' amount' proof' \<in> set stepsInit"
  assumes "BURN bridgeAddress caller ID token amount \<in> set stepsInit"
  shows "caller' = caller" "token' = token" "amount' = amount"
proof-
  obtain steps1 steps2 where *: "stepsInit = steps1 @ [RELEASE tokenDepositAddress caller' ID token' amount' proof'] @ steps2"
    using assms
    by (metis append_Cons append_Nil in_set_conv_decomp_first)
  then have B1: "BURN bridgeAddress caller ID token amount \<in> set steps2"
    using assms noReleaseBeforeBurnSteps
    by (cases "BURN bridgeAddress caller ID token amount \<in> set steps1",
        smt (verit, best) append.assoc reachableAppend reachableInitI reachableStepInSteps,
        auto)
  then have B2: "BURN bridgeAddress caller' ID token' amount' \<in> set steps2"
    using burnBeforeReleaseSteps *
    by auto
  moreover
  obtain c where "reachable contractsInit c steps2"
    by (metis "*" reachableAppend reachableInitI)
  then have "caller' = caller \<and> token' = token \<and> amount' = amount"
    using BURNNoDoubleCTA[OF _ B1 B2]
    by simp
  then show "caller' = caller" "token' = token" "amount' = amount"
    by auto
qed

end


end