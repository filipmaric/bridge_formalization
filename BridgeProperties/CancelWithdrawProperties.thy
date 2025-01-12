theory CancelWithdrawProperties
  imports Reachability DepositClaimProperties
begin

context HashProofVerifier
begin

\<comment> \<open>Once set tokenWithdrawn flag cannot be unset\<close>
lemma reachableGetTokenWithdrawn:
  assumes "reachable contracts contracts' steps"
  assumes "getTokenWithdrawnTD contracts address h = True"
  shows "getTokenWithdrawnTD contracts' address h = True"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callWithdrawWhileDeadTokenWithdrawn'
      by (metis executeStep.simps(8))
  qed auto
qed

lemma reachableGetTokenWithdrawnNoWithdraw:
  assumes "reachable contracts contracts' steps"
  assumes "getTokenWithdrawnTD contracts' tokenDepositAddress (hash2 caller token) = False"
  shows "\<nexists> amount proof. WITHDRAW_WD tokenDepositAddress caller token amount proof \<in> set steps"
  using assms
proof (induction contracts contracts' steps)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  have "getTokenWithdrawnTD contracts' tokenDepositAddress (hash2 caller token) = False"
    using reachable_step.prems reachable_step.hyps 
  proof (cases step)
    case (WITHDRAW_WD address' caller' token' amount' proof')
    then show ?thesis
      using reachable_step.prems reachable_step.hyps 
      using callWithdrawWhileDeadTokenWithdrawn'
      by (metis executeStep.simps(8))
  qed auto
  then have *: "\<nexists> amount proof. WITHDRAW_WD tokenDepositAddress caller token amount proof \<in> set steps"
    using reachable_step.IH
    by blast
  show ?case
  proof (cases "\<nexists> address' token' caller' amount' proof'. WITHDRAW_WD address' caller' token' amount' proof' = step")
    case True
    then show ?thesis
      using reachable_step.hyps *
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
        using step reachable_step.hyps *
        by auto
    next
      case True
      then show ?thesis
        using reachable_step.hyps step reachable_step.prems
        using callWithdrawWhileDeadTokenWithdrawn[where msg="message caller 0"]
        by simp
    qed
  qed
qed

end


context StrongHashProofVerifier
begin

lemma reachableGetTokenWithdrawnNoWithdrawNoChange:
  assumes "reachable contracts contracts' steps"
  assumes "\<nexists> amount proof. WITHDRAW_WD tokenDepositAddress caller token amount proof \<in> set steps"
  shows "getTokenWithdrawnTD contracts' tokenDepositAddress (hash2 caller token) = 
         getTokenWithdrawnTD contracts tokenDepositAddress (hash2 caller token)"
  using assms
proof (induction contracts contracts' steps)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (WITHDRAW_WD address' caller' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token \<and> caller' = caller")
      case True
      then have False
        using WITHDRAW_WD reachable_step.prems
        by auto
      then show ?thesis
        by simp
    next
      case False
      show ?thesis
      proof (cases "address' = tokenDepositAddress")
        case False
        then show ?thesis
          using callWithdrawWhileDeadOtherAddress WITHDRAW_WD reachable_step
          by (metis executeStep.simps(8) list.set_intros(2))
      next
        case True
        then have "hash2 caller token \<noteq> hash2 caller' token'"
          using hash2_inj \<open>\<not> (address' = tokenDepositAddress \<and> token' = token \<and> caller' = caller)\<close>
          unfolding hash2_inj_def
          by blast
        then show ?thesis
          using True WITHDRAW_WD reachable_step
          using callWithdrawWhileDeadGetTokenWithdrawnOtherHash
          by (metis executeStep.simps(8) list.set_intros(2) senderMessage)
      qed
    qed
  qed auto
qed

end

context HashProofVerifier
begin

(* ------------------------------------------------------------------------------------ *)

text \<open>No cancel before the bridge dies\<close>
lemma noCancelBeforeBridgeDead:
  assumes "reachable contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
  shows "\<nexists> step. step \<in> set steps \<and> (\<exists> caller ID token amount proof. step = CANCEL_WD tokenDepositAddress caller ID token amount proof)"
  using assms
proof (induction contractsInit contracts steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts' contractsInit contracts blockNum block step)
  have notDead: "\<not> bridgeDead contracts tokenDepositAddress"
    using reachable.reachable_step reachableBridgeDead reachable_base reachable_step.hyps(2) reachable_step.prems
    by blast
  then show ?case
    using reachable_step callCancelDepositWhileDeadBridgeDead
    by (metis executeStep.simps(7) set_ConsD)
qed


text \<open>No withdraw before the bridge dies\<close>
lemma noWithdrawBeforeBridgeDead:
  assumes "reachable contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
  shows "\<nexists> step. step \<in> set steps \<and> (\<exists> caller token amount proof. step = WITHDRAW_WD tokenDepositAddress caller token amount proof)"
  using assms
proof (induction contractsInit contracts steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts' contractsInit contracts blockNum block step)
  have notDead: "\<not> bridgeDead contracts tokenDepositAddress"
    using reachable.reachable_step reachableBridgeDead reachable_base reachable_step.hyps(2) reachable_step.prems
    by blast
  then show ?case
    using reachable_step callWithdrawWhileDeadBridgeDead
    by (metis executeStep.simps(8) set_ConsD)
qed

end

context StrongHashProofVerifier
begin

text \<open>There are no double cancels\<close>
theorem callCancelNoDouble:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  assumes "reachable contracts' contracts'' steps"
  shows "fst (callCancelDepositWhileDead contracts'' address msg' block' ID token' amount' proof') \<noteq> Success"
proof-
  have "getDepositTD contracts' address ID = 0"
    using callCancelDepositWhileDeadDeposits assms(1)
    by (metis lookupNat_delete)
  moreover
  have "bridgeDead contracts' address"
    using callCancelDepositWhileDeadBridgeDead assms(1)
    by simp
  ultimately have "getDepositTD contracts'' address ID = 0"
    using `reachable contracts' contracts'' steps` reachableGetDepositBridgeDead 
    by blast
  then show ?thesis
    using callCancelDepositWhileDeadGetDepositNonzero assms
    by (metis fstI surj_pair)
qed

end

context HashProofVerifier
begin

lemma callWithdrawWhileDeadNoDouble:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  assumes "reachable contracts' contracts'' steps"
  shows "fst (callWithdrawWhileDead contracts'' address msg block' token amount' proof') \<noteq> Success"
proof-
  have "getTokenWithdrawnTD contracts' address (hash2 (sender msg) token) = True"
    using assms
    using callWithdrawWhileDeadTokenWithdrawn by blast
  then have "getTokenWithdrawnTD contracts'' address (hash2 (sender msg) token) = True"
    using assms
    using reachableGetTokenWithdrawn by blast
  then show ?thesis
    using callWithdrawWhileDeadNotTokenWithdrawn[of contracts'' address msg block' token amount' proof']
    by (metis prod.collapse)
qed

end

(* ------------------------------------------------------------------------------------ *)
context StrongHashProofVerifier
begin

text \<open>We want to prove that there cannot be two CANCEL steps with the same ID on the same tokenDeposit address\<close>

lemma CANCELNoDoubleCons:
  assumes "reachable contracts contracts' (CANCEL_WD tokenDepositAddress caller ID token amount proof # steps)"
  shows "\<nexists> token' caller' amount' proof'. CANCEL_WD tokenDepositAddress caller' ID token' amount' proof' \<in> set steps"
  using assms callCancelNoDouble 
  by (smt (verit, ccfv_SIG) executeStep.simps(7)fst_conv reachableCons' reachableStepInSteps)

lemma CANCELNoDouble:
  assumes "reachable contracts contracts' steps"
  assumes "steps = steps1 @ [CANCEL_WD tokenDepositAddress caller ID token amount proof] @ steps2 @ [CANCEL_WD tokenDepositAddress caller' ID token' amount' proof'] @ steps3"
  shows False
  using assms
  by (metis CANCELNoDoubleCons Un_iff append_Cons list.set_intros(1) reachableAppend set_append)

end

context HashProofVerifier
begin

lemma noCancelBeforeDepositSteps:
  assumes "reachable contracts contracts' (steps1 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps @ [CANCEL_WD tokenDepositAddress caller ID token amount proof] @ steps2)"
  shows False
proof-
  obtain contractsA contractsB contracts1 contracts2 where
   "reachable contractsA contracts1 [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
   "reachable contracts1 contracts2 steps"
   "reachable contracts2 contractsB [DEPOSIT tokenDepositAddress caller' ID token' amount']"
    using assms
    by (meson reachableAppend)
  then have "bridgeDead contracts1 tokenDepositAddress"
    by (meson list.set_intros(1) noCancelBeforeBridgeDead)
  then have "bridgeDead contracts2 tokenDepositAddress"
    by (metis \<open>reachable contracts1 contracts2 steps\<close> reachableDeadState)
  then show False
    using \<open>reachable contracts2 contractsB [DEPOSIT tokenDepositAddress caller' ID token' amount']\<close>
    by (metis executeStep.simps(1)  callDepositNotBridgeDead' reachableBridgeDead reachableCons')
qed


lemma noCancelBeforeDeposit:
  assumes CANCEL_in_steps: "CANCEL_WD tokenDepositAddress caller' ID token' amount' proof' \<in> set stepsInit"
  assumes reachableInitI: "reachable contractsInit contractsI stepsInit"
  assumes reach: "reachable contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
  shows "False"
proof-
  let ?CANCEL_step = "CANCEL_WD tokenDepositAddress caller' ID token' amount' proof'"
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"
  obtain steps1 steps2 where "stepsInit = steps1 @ [?CANCEL_step] @ steps2"
    using CANCEL_in_steps
    using reachableInitI reachableStepInSteps 
    by blast
  then have "reachable contractsInit contractsDeposit ([] @ [?DEPOSIT_step] @ steps1 @ [?CANCEL_step] @ steps2 )"
    using reach reachableInitI reachableTrans by fastforce
  then show False
    using noCancelBeforeDepositSteps
    by blast
qed


end


context StrongHashProofVerifier
begin

lemma callCancelDepositWhileDeadGetDepositBefore:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "getDepositTD contracts address ID = hash3 (sender msg) token amount"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma onlyDepositorCanCancel:
  assumes deposit: "callDeposit contractsD tokenDepositAddress block msg ID token amount = (Success, contractsD')"
  \<comment> \<open>after a while a  claim is made\<close>
  assumes "reachable contractsD' contractsC steps"
  assumes cancel: "callCancelDepositWhileDead contractsC tokenDepositAddress msg' block' ID token' amount' proof = (Success, contractsC')"
  shows "sender msg' = sender msg" "token' = token" "amount' = amount"
proof-
  have "getDepositTD contractsD' tokenDepositAddress ID = hash3 (sender msg) token amount"
    using callDepositWritesHash deposit
    by simp
  moreover
  have "getDepositTD contractsC tokenDepositAddress ID = hash3 (sender msg') token' amount'"
    using callCancelDepositWhileDeadGetDepositBefore[OF cancel]
    by simp
  moreover
  have "getDepositTD contractsC tokenDepositAddress ID = getDepositTD contractsD' tokenDepositAddress ID \<or>
        getDepositTD contractsC tokenDepositAddress ID = 0"
    using assms
    by (metis reachableGetDeposit calculation(1) hash3_nonzero)
  ultimately
  show "sender msg' = sender msg" "token' = token" "amount' = amount"
    using hash3_nonzero hash3_inj
    by (smt (verit, best) hash3_inj_def)+
qed

lemma onlyDepositorCanCancelSteps:
  assumes "reachable contracts contracts' steps"
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
  assumes "CANCEL_WD tokenDepositAddress caller' ID token' amount' proof \<in> set steps"
  shows "caller' = caller" "token' = token" "amount' = amount"
proof-
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"
  let ?CANCEL_step = "CANCEL_WD tokenDepositAddress caller' ID token' amount' proof"
  obtain steps1 steps2 where A: "steps = steps1 @ [?DEPOSIT_step] @ steps2"
    using assms
    using reachableStepInSteps by blast
  have "?CANCEL_step \<notin> set steps2"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain steps1' steps2' where B: "steps2 = steps1' @ [?CANCEL_step] @ steps2'"
      by (metis append_Cons append_Nil split_list_first)
    then show False
      using noCancelBeforeDepositSteps[of contracts contracts' steps1  tokenDepositAddress caller ID token amount steps1' caller' token' amount' "proof" steps2']
      using A B assms
      by simp
  qed
  then have "?CANCEL_step \<in> set steps1"
    using assms A
    by auto
  then obtain steps1' steps2' where B: "steps1 = steps1' @ [?CANCEL_step] @ steps2'"
    by (metis append_Cons eq_Nil_appendI split_list)
  then obtain contracts1 contracts2 contracts3 contracts4 where 
    "reachable contracts1 contracts2 [?DEPOSIT_step]"
    "reachable contracts2 contracts3 steps2'"
    "reachable contracts3 contracts4 [?CANCEL_step]"
    using A
    by (metis assms(1) reachableAppend)
  then have "caller' = caller \<and> token' = token \<and> amount' = amount"
    using reachableSingleton onlyDepositorCanCancel
    by (smt (verit, best) executeStep.simps(1) executeStep.simps(7) senderMessage)
  then show "caller' = caller" "token' = token" "amount' = amount"
    by auto
qed

end

context Init
begin

(*
                  [steps]              cancel
  contractsInit     \<rightarrow>*      contracts   \<rightarrow>   contracts'
  properSetup    DEPOSIT?
  getDeposit=0
*)
text \<open>Cancel deposit can succeed only if there was a previous successful deposit with the same ID\<close>
theorem cancelDepositOnlyAfterDeposit:
  assumes cancel: 
    "callCancelDepositWhileDead contractsI tokenDepositAddress msg block ID token amount proof = 
     (Success, contracts')"
  \<comment> \<open>there must had been a previous deposit with the same ID\<close>
  shows "DEPOSIT tokenDepositAddress (sender msg) ID token amount \<in> set stepsInit"
proof-
  have "getDepositTD contractsI tokenDepositAddress ID = hash3 (sender msg) token amount"
    using cancel
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
    by (simp add: Let_def split: option.splits prod.splits if_split_asm)
  then show ?thesis
    using assms getDepositWrittenOnlyByDeposit depositsEmpty reachableInitI
    by blast
qed

end

context InitUpdateBridgeNotDeadLastValidState
begin

text \<open>Only deposits that are not claimed can successfully be canceled\<close>
theorem cancelDepositWhileDeadNoClaim:
  assumes cancel:
    "callCancelDepositWhileDead contractsLVS tokenDepositAddress msg block ID token amount proof = 
      (Success, contractsCancel)"
  shows "\<nexists> caller' token' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain caller' token' amount' proof' where 
    *: "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
    by auto
  then have "getClaimB contractsUpdate' bridgeAddress ID = True"
    using claimStepSetsClaim reachableInitI
    by blast

  moreover

  have "verifyClaimProof () bridgeAddress ID stateRoot proof = True"
    using callCancelDepositWhileDeadVerifyClaimProof[OF assms]
    using getLastValidStateLVS
    by simp
    
  then have "getClaimB contractsUpdate' bridgeAddress ID = False"
    by (metis generateStateRootUpdate' option.collapse properSetupUpdate' properSetup_def verifyClaimProofE)

  ultimately

  show False
    by simp
qed

text \<open>Withdrawal can succeed only if the bridge is dead and 
      the user had the exact amount of tokens in the state in which the bridge died\<close>
theorem withdrawSufficientBalance:
  \<comment> \<open>Token deposit can accept token\<close>
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  \<comment> \<open>Withdraw succeded\<close>
  assumes withdraw:
    "callWithdrawWhileDead contractsLVS tokenDepositAddress msg block token amount proof = (Success, contractsW)"
  \<comment> \<open>Caller had sufficient balance\<close>
  shows "callBalanceOf contractsUpdate' (mintedTokenTD contractsInit tokenDepositAddress token) (sender msg) = (Success, amount)"
proof-
  let ?mintedToken = "mintedTokenTD contractsInit tokenDepositAddress token"
  have "verifyBalanceProof () ?mintedToken (sender msg) amount stateRoot proof"
    using callWithdrawWhileDeadVerifyBalanceProof[OF withdraw]
    using getLastValidStateLVS
    by (simp add: Let_def)
  then have "balanceOf (the (ERC20state contractsUpdate' ?mintedToken)) (sender msg) = amount"
    using assms
    using verifyBalanceProofE[of contractsUpdate' stateRoot]
    by (smt (verit, ccfv_SIG) properSetup_def reachableERC20State generateStateRootUpdate' option.exhaust_sel properSetupInit properToken_def reachableInitI)
  then show ?thesis
    using assms
    unfolding callBalanceOf_def
    by (auto split: option.splits)
qed

end

context Init
begin

lemma getTokenWithdrawnNotBridgeDead:
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "getTokenWithdrawnTD contractsI tokenDepositAddress (hash2 caller token) = False"
  using tokenWithdrawnEmpty reachableGetTokenWithdrawnNoWithdrawNoChange[OF reachableInitI]
  using assms noWithdrawBeforeBridgeDead reachableInitI
  by blast
end


context StrongHashProofVerifier
begin

lemma nonCanceledDepositGetDeposit:
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
  assumes "\<nexists>caller amount proof. CANCEL_WD tokenDepositAddress caller ID token amount proof \<in> set steps"
  assumes "reachable contracts contracts' steps"
  shows "getDepositTD contracts' tokenDepositAddress ID = hash3 caller token amount"
  using assms
proof-
  have *: "\<nexists>caller amount proof token'. CANCEL_WD tokenDepositAddress caller ID token' amount proof \<in> set steps"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain caller' amount' proof' token' where "CANCEL_WD tokenDepositAddress caller' ID token' amount' proof' \<in> set steps"
      by auto
    moreover
    have "token = token'"
      using onlyDepositorCanCancelSteps(2)
      using assms(1) assms(3) calculation by blast
    ultimately show False
      using assms
      by auto
  qed
  obtain steps1 steps2 where
  "steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2"
    using assms
    using reachableStepInSteps by blast
  then obtain contractsD where 
    "reachable contractsD contracts' steps1"
    "getDepositTD contractsD tokenDepositAddress ID = 
     hash3 caller token amount"
    by (smt (verit, ccfv_threshold) DEPOSITNoDouble' HashProofVerifier.executeStep.simps(1) HashProofVerifier_axioms Un_iff append_Cons append_Cons_eq_iff assms(1) assms(3) callDepositWritesHash reachableStepInSteps self_append_conv2 senderMessage set_append)
  then show ?thesis
    using hash3_nonzero[of caller token amount] *
    by (simp add: \<open>steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2\<close> reachableGetDepositBridgeNoCancel)
qed

end

end