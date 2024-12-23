theory UpdateProperties
  imports Reachability
begin

context HashProofVerifier
begin

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
      using callUpdateLastState callUpdateOtherAddress
      by (metis executeStep.simps(6))
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
  then show ?case
  proof (cases step)
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      using callUpdateLastState callUpdateOtherAddress reachableFromBridgeStateOracle
      by (smt (verit, ccfv_threshold) executeStep.simps(6) updatesNonZeroCons reachableFrom.reachableFrom_step set_ConsD)
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
    by (smt (verit, best) callLastState_def lastValidState_def executeStep.simps(7))
next
  case (WITHDRAW_WD address' caller' token' amount' proof')
  then show ?thesis
    using assms
    using callWithdrawWhileDeadLastValidStateTD callWithdrawWhileDeadOtherAddress callWithdrawWhileDeadIStateOracle 
    by (smt (verit, ccfv_SIG) callLastState_def lastValidState_def executeStep.simps(8))
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
    by (metis executeStep.simps(6))
next
  case (TRANSFER address' caller' receiver' token' amount')
  then show ?thesis
    using assms reachableFrom_step
    unfolding lastValidState_def Let_def callLastState_def
    by auto
next
  case (RELEASE address' caller' ID' token' amount' proof')
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
      by (metis executeStep.simps(6) list.set_intros(2))
  qed auto
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
      by (meson Step.simps(18) dual_order.trans reachableFrom.reachableFrom_step set_ConsD set_subset_Cons)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step CLAIM
      by (meson Step.simps(30) dual_order.trans reachableFrom.reachableFrom_step set_ConsD set_subset_Cons)
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
        by (metis (no_types, lifting) executeStep.simps(6))
      then show ?thesis
        using False UPDATE
        by (smt (verit, best) Step.simps(6) reachableFrom.reachableFrom_step reachableFrom_step.hyps(2) set_ConsD set_subset_Cons subset_trans)
    qed
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step CANCEL_WD
      by (meson Step.simps(59) reachableFrom.reachableFrom_step set_ConsD set_subset_Cons subset_trans)
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step WITHDRAW_WD
      by (meson Step.simps(61) reachableFrom.reachableFrom_step set_ConsD set_subset_Cons subset_trans)
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step TRANSFER
      by auto (metis (no_types, opaque_lifting) Step.simps(53) insertE list.simps(15) reachableFrom.reachableFrom_step reachableFrom_step.hyps(2) subset_insertI2)
      (* FIXME: avoid calling methods after auto *)
  next
    case (BURN address' caller' receiver' token' amount')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step BURN
      by auto (metis (no_types, opaque_lifting) Step.simps(39) executeStep.simps(3) insertE list.simps(15) reachableFrom.reachableFrom_step subset_insertI2)
      (* FIXME: avoid calling methods after auto *)
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachableFrom_step by auto
    then show ?thesis
      using reachableFrom_step RELEASE
      by auto (metis (no_types, opaque_lifting) Step.simps(47) reachableFrom.reachableFrom_step reachableFrom_step.hyps(2) set_ConsD subset_insertI2)
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
      by (meson Step.simps(18) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(30) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(59) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case False
      then show ?thesis
        using * reachableFrom_step.prems reachableFrom_step.hyps
        by (smt (verit, best) Step.simps(6) UPDATE reachableFrom.reachableFrom_step set_ConsD)
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
      by (meson Step.simps(61) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (meson Step.simps(54) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (metis (no_types, opaque_lifting) Step.simps(39) reachableFrom.reachableFrom_step set_ConsD)
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems reachableFrom_step.hyps
      by (metis Step.simps(47) reachableFrom.simps set_ConsD)
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
            metis Cons_eq_appendI append_Nil empty_iff executeStep.simps(6) list.set(1) reachableFrom.reachableFrom_step reachableFrom_base updateSuccess)
    next
      case False
      then have "lastState (the (stateOracleState contracts address)) \<noteq> lastState (the (stateOracleState contracts' address))"
        by (metis UPDATE callUpdateOtherAddress executeStep.simps(6) local.reachableFrom_step(2) reachableFrom_step.prems)
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
            metis Cons_eq_appendI append_Nil empty_iff executeStep.simps(6) list.set(1) reachableFrom.reachableFrom_step reachableFrom_base updateSuccess)
    next
      case False
      then show ?thesis
        using UPDATE reachableFrom_step reachableFrom.reachableFrom_step[OF _ reachableFrom_step.hyps(2)]
        by force
    qed
  qed force+
qed


end

end