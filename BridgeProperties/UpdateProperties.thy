theory UpdateProperties
  imports Reachability
begin

context HashProofVerifier
begin

lemma reachableStateRootNonZero:
  assumes "reachable contracts contracts' steps" 
  assumes "lastStateSO contracts address \<noteq> 0"
  shows "lastStateSO contracts' address \<noteq> 0"
  using assms
proof (induction contracts contracts' steps)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachable_step
      using callUpdateLastState callUpdateOtherAddress callUpdateStateRootNonZero
      by (metis executeStep.simps(6))
  qed auto
qed

lemma reachableGetLastStateTDNonzero:
  assumes "reachable contracts contracts' steps"
  assumes "lastStateTD contracts tokenDepositAddress \<noteq> 0"
  shows "lastStateTD contracts' tokenDepositAddress \<noteq> 0"
  using assms reachableStateRootNonZero
  by simp

text \<open>If there was at least one update and no updates set zero state, 
      then the last state is not zero\<close>
lemma lastStateNonZero:
  assumes "reachable initContracts contracts steps"
  assumes "UPDATE (stateOracleAddressB contracts bridgeAddress) stateRoot \<in> set steps"
  shows "lastStateB contracts bridgeAddress \<noteq> 0"
  using assms
proof (induction initContracts contracts steps)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachable_step
      using callUpdateLastState callUpdateOtherAddress callUpdateStateRootNonZero reachableBridgeStateOracle
      by (smt (verit, ccfv_threshold) executeStep.simps(6) reachable.reachable_step set_ConsD)
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
    using assms reachable_step
    unfolding lastValidState_def Let_def callLastState_def
    by auto
next
  case (RELEASE address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms reachable_step
    unfolding lastValidState_def Let_def callLastState_def
    by auto
qed

lemma noUpdateLastState:
  assumes "reachable contracts contracts' steps"
  assumes "\<nexists> stateRoot. UPDATE address stateRoot \<in> set steps"
  shows "lastStateSO contracts address = lastStateSO contracts' address"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (UPDATE address' stateRoot')
    then have "address \<noteq> address'"
      using reachable_step.prems by auto
    then show ?thesis
      using UPDATE reachable_step
      using callUpdateOtherAddress
      by (metis executeStep.simps(6) list.set_intros(2))
  qed auto
qed

lemma reachableNoUpdateLastValidState:
  assumes "reachable contracts contracts' steps"
  assumes "\<nexists> stateRoot. UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot \<in> set steps"
  shows "lastValidStateTD contracts' tokenDepositAddress = lastValidStateTD contracts tokenDepositAddress"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
    using noUpdateGetLastValidStateTD reachable_step reachableDepositStateOracle
    by (metis list.set_intros(1) list.set_intros(2))
qed

lemma noUpdateNotBridgeDead:
  assumes "reachable contracts contracts' steps"
  assumes "\<not> bridgeDead contracts tokenDepositAddress" "lastStateTD contracts tokenDepositAddress = 0"
  assumes "\<nexists> stateRoot. UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot \<in> set steps"
  shows "\<not> bridgeDead contracts' tokenDepositAddress"
  using assms
proof (induction contracts contracts' steps)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (metis (no_types, lifting) BridgeDiesDeadState reachableDepositStateOracle list.set_intros(2) noUpdateLastState)
qed


text \<open>If state oracle last state has changed, it must have been due to an update step.
      One of those updates must be the last update applied.\<close>
lemma lastUpdateHappened:
  assumes "reachable contracts contracts' steps"
  assumes "lastStateSO contracts address \<noteq> lastStateSO contracts' address"
  shows "\<exists> contractsU contractsU' block blockNum steps1 steps2 stateRoot. 
                       reachable contracts contractsU steps1 \<and> 
                       stateRoot = generateStateRoot contractsU \<and>
                       callUpdate contractsU address block blockNum stateRoot = (Success, contractsU') \<and>
                       reachable contractsU' contracts' steps2 \<and>
                       (\<nexists> stateRoot'. UPDATE address stateRoot' \<in> set steps2) \<and>
                       set steps1 \<subseteq> set steps" (* FIXME: add steps2 *)
using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using executeStep.simps(1) reachable_step
      by auto
    then show ?thesis
      using reachable_step DEPOSIT
      by (meson Step.simps(18) dual_order.trans reachable.reachable_step set_ConsD set_subset_Cons)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachable_step by auto
    then show ?thesis
      using reachable_step CLAIM
      by (meson Step.simps(30) dual_order.trans reachable.reachable_step set_ConsD set_subset_Cons)
  next
    case (UPDATE address' stateRoot')
    then have *: "stateRoot' = generateStateRoot contracts'"
      using reachable_step updateSuccess
      by simp
    show ?thesis
    proof (cases "address = address'")
      case True
      then show ?thesis
        using reachable_step.hyps UPDATE *
        using reachable_base 
        by (rule_tac x="contracts'" in exI, rule_tac x="contracts''" in exI, force)
    next
      case False
      then obtain contractsU contractsU' block blockNum steps1 steps2 stateRoot
        where "reachable contracts contractsU steps1 \<and>
               stateRoot = generateStateRoot contractsU \<and>
               callUpdate contractsU address block blockNum stateRoot = (Success, contractsU') \<and>
               reachable contractsU' contracts' steps2 \<and>
               (\<nexists>stateRoot'. UPDATE address stateRoot' \<in> set steps2) \<and> set steps1 \<subseteq> set steps"
        using reachable_step UPDATE callUpdateOtherAddress
        by (metis (no_types, lifting) executeStep.simps(6))
      then show ?thesis
        using False UPDATE
        by (smt (verit, best) Step.simps(6) reachable.reachable_step reachable_step.hyps(2) set_ConsD set_subset_Cons subset_trans)
    qed
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachable_step by auto
    then show ?thesis
      using reachable_step CANCEL_WD
      by (meson Step.simps(59) reachable.reachable_step set_ConsD set_subset_Cons subset_trans)
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachable_step by auto
    then show ?thesis
      using reachable_step WITHDRAW_WD
      by (meson Step.simps(61) reachable.reachable_step set_ConsD set_subset_Cons subset_trans)
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachable_step by auto
    then show ?thesis
      using reachable_step TRANSFER
      by auto (metis (no_types, opaque_lifting) Step.simps(53) insertE list.simps(15) reachable.reachable_step reachable_step.hyps(2) subset_insertI2)
      (* FIXME: avoid calling methods after auto *)
  next
    case (BURN address' caller' receiver' token' amount')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachable_step by auto
    then show ?thesis
      using reachable_step BURN
      by auto (metis (no_types, opaque_lifting) Step.simps(39) executeStep.simps(3) insertE list.simps(15) reachable.reachable_step subset_insertI2)
      (* FIXME: avoid calling methods after auto *)
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then have "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
               StateOracleState.lastState (the (stateOracleState contracts' address))"
      using reachable_step by auto
    then show ?thesis
      using reachable_step RELEASE
      by auto (metis (no_types, opaque_lifting) Step.simps(47) reachable.reachable_step reachable_step.hyps(2) set_ConsD subset_insertI2)
      (* FIXME: avoid calling methods after auto *)
  qed
qed

lemma lastUpdateHappened':
  assumes "reachable contracts contractsUx steps1x"
  assumes update: "callUpdate contractsUx address blockx blockNumx stateRootx = (Success, contractsU'x)"
  assumes "reachable contractsU'x contracts' steps2x"
  shows "\<exists> contractsU contractsU' block blockNum steps1 steps2 stateRoot. 
                       reachable contracts contractsU steps1 \<and> 
                       stateRoot = generateStateRoot contractsU \<and>
                       callUpdate contractsU address block blockNum stateRoot = (Success, contractsU') \<and>
                       reachable contractsU' contracts' steps2 \<and>
                       (\<nexists> stateRoot'. UPDATE address stateRoot' \<in> set steps2) \<and>
                       set steps1x \<subseteq> set steps1" (* FIXME: add steps2 *)
  using assms(3) assms(1-2)
proof (induction contractsU'x contracts' steps2x rule: reachable.induct)
  case (reachable_base contracts')
  then show ?case
    by (metis list.distinct(1) list.set_cases reachable.reachable_base subset_refl updateSuccess)
next
  case (reachable_step stepsa contracts''a contractsa contracts'a blockNuma blocka stepa)
  then obtain contractsU contractsU' block blockNum steps1 steps2 stateRoot
    where *: "reachable contracts contractsU steps1"
          "stateRoot = generateStateRoot contractsU"
          "callUpdate contractsU address block blockNum stateRoot = (Success, contractsU')"
          "reachable contractsU' contracts'a steps2"
          "(\<nexists>stateRoot'. UPDATE address stateRoot' \<in> set steps2)"
          "set steps1x \<subseteq> set steps1"
    by blast
  show ?case
  proof (cases stepa)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using * reachable_step.prems reachable_step.hyps
      by (meson Step.simps(18) reachable.reachable_step set_ConsD)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachable_step.prems reachable_step.hyps
      by (meson Step.simps(30) reachable.reachable_step set_ConsD)
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachable_step.prems reachable_step.hyps
      by (meson Step.simps(59) reachable.reachable_step set_ConsD)
  next
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case False
      then show ?thesis
        using * reachable_step.prems reachable_step.hyps
        by (smt (verit, best) Step.simps(6) UPDATE reachable.reachable_step set_ConsD)
    next
      case True
      let ?u = "UPDATE address stateRootx"
      let ?steps = "stepsa @ [?u] @ steps1x"
      have "reachable contracts contracts'a ?steps"
        using reachable_step.prems reachable_step.hyps UPDATE
        by (simp add: reachable.reachable_step reachableTrans)
      then show ?thesis
        using reachable_step.prems reachable_step.hyps UPDATE True
        using updateSuccess reachable_base
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
      using * reachable_step.prems reachable_step.hyps
      by (meson Step.simps(61) reachable.reachable_step set_ConsD)
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using * reachable_step.prems reachable_step.hyps
      by (meson Step.simps(54) reachable.reachable_step set_ConsD)
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using * reachable_step.prems reachable_step.hyps
      by (metis (no_types, opaque_lifting) Step.simps(39) reachable.reachable_step set_ConsD)
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachable_step.prems reachable_step.hyps
      by (metis Step.simps(47) reachable.simps set_ConsD)
  qed
qed

lemma lastUpdateHappenedSteps:
  assumes "reachable contracts contracts' steps"
  assumes "lastStateSO contracts address \<noteq> lastStateSO contracts' address"
  shows "\<exists> contractsU steps1 steps2 stateRoot. 
                       reachable contracts contractsU steps1 \<and> 
                       stateRoot = generateStateRoot contractsU \<and>
                       steps = steps2 @ [UPDATE address stateRoot] @ steps1 \<and>
                       reachable contractsU contracts' (steps2 @ [UPDATE address stateRoot]) \<and>
                       (\<nexists> stateRoot'. UPDATE address stateRoot' \<in> set steps2)"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    using reachable.reachable_step[OF _ reachable_step.hyps(2)]
  proof (cases step)
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case True
      then show ?thesis
        using reachable_step.hyps reachable_step.prems UPDATE
        by (rule_tac x="contracts'" in exI,
            rule_tac x="steps" in exI,
            rule_tac x="[]" in exI,
            metis Cons_eq_appendI append_Nil empty_iff executeStep.simps(6) list.set(1) reachable.reachable_step reachable_base updateSuccess)
    next
      case False
      then have "lastState (the (stateOracleState contracts address)) \<noteq> lastState (the (stateOracleState contracts' address))"
        by (metis UPDATE callUpdateOtherAddress executeStep.simps(6) local.reachable_step(2) reachable_step.prems)
      then show ?thesis
        using reachable_step UPDATE False reachable.reachable_step[OF _ reachable_step.hyps(2)]
        by force
    qed
  qed force+
qed

lemma lastUpdateHappenedSteps':
  assumes "reachable contracts contracts' steps"
  assumes "\<exists> stateRoot. UPDATE address stateRoot \<in> set steps"
  shows "\<exists> contractsU steps1 steps2 stateRoot. 
                       reachable contracts contractsU steps1 \<and> 
                       stateRoot = generateStateRoot contractsU \<and>
                       steps = steps2 @ [UPDATE address stateRoot] @ steps1 \<and>
                       reachable contractsU contracts' (steps2 @ [UPDATE address stateRoot]) \<and>
                       (\<nexists> stateRoot'. UPDATE address stateRoot' \<in> set steps2)"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    using reachable.reachable_step[OF _ reachable_step.hyps(2)]
  proof (cases step)
    case (UPDATE address' stateRoot')
    show ?thesis
    proof (cases "address = address'")
      case True
      then show ?thesis
        using reachable_step.hyps reachable_step.prems UPDATE
        by (rule_tac x="contracts'" in exI,
            rule_tac x="steps" in exI,
            rule_tac x="[]" in exI,
            metis Cons_eq_appendI append_Nil empty_iff executeStep.simps(6) list.set(1) reachable.reachable_step reachable_base updateSuccess)
    next
      case False
      then show ?thesis
        using UPDATE reachable_step reachable.reachable_step[OF _ reachable_step.hyps(2)]
        by force
    qed
  qed force+
qed


end

end