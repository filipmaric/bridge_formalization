theory CancelWithdrawProperties
  imports Reachability DepositClaimProperties
begin

context HashProofVerifier
begin



\<comment> \<open>Once set tokenWithdrawn flag cannot be unset\<close>
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
      by (metis executeStep.simps(8))
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
      by (metis executeStep.simps(8))
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
        using callWithdrawWhileDeadTokenWithdrawn[where msg="message caller 0"]
        by simp
    qed
  qed
qed

(* ------------------------------------------------------------------------------------ *)

text \<open>No cancel before the bridge dies\<close>
lemma noCancelBeforeBridgeDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
  shows "\<nexists> step. step \<in> set steps \<and> (\<exists> caller ID token amount proof. step = CANCEL_WD tokenDepositAddress caller ID token amount proof)"
  using assms
proof (induction contractsInit contracts steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts' contractsInit contracts blockNum block step)
  have notDead: "\<not> bridgeDead contracts tokenDepositAddress"
    using reachableFrom.reachableFrom_step reachableFromBridgeDead reachableFrom_base reachableFrom_step.hyps(2) reachableFrom_step.prems
    by blast
  then show ?case
    using reachableFrom_step callCancelDepositWhileDeadBridgeDead
    by (metis executeStep.simps(7) set_ConsD)
qed


text \<open>No withdraw before the bridge dies\<close>
lemma noWithdrawBeforeBridgeDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
  shows "\<nexists> step. step \<in> set steps \<and> (\<exists> caller token amount proof. step = WITHDRAW_WD tokenDepositAddress caller token amount proof)"
  using assms
proof (induction contractsInit contracts steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts' contractsInit contracts blockNum block step)
  have notDead: "\<not> bridgeDead contracts tokenDepositAddress"
    using reachableFrom.reachableFrom_step reachableFromBridgeDead reachableFrom_base reachableFrom_step.hyps(2) reachableFrom_step.prems
    by blast
  then show ?case
    using reachableFrom_step callWithdrawWhileDeadBridgeDead
    by (metis executeStep.simps(8) set_ConsD)
qed

end

context StrongHashProofVerifier
begin

text \<open>There are no double cancels\<close>
theorem callCancelNoDouble:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  assumes "reachableFrom contracts' contracts'' steps"
  shows "fst (callCancelDepositWhileDead contracts'' address msg' block' ID token' amount' proof') \<noteq> Success"
proof-
  have "getDeposit (the (tokenDepositState contracts' address)) ID = 0"
    using callCancelDepositWhileDeadDeposits assms(1)
    by (metis lookupNat_delete)
  moreover
  have "bridgeDead contracts' address"
    using callCancelDepositWhileDeadBridgeDead assms(1)
    by simp
  ultimately have "getDeposit (the (tokenDepositState contracts'' address)) ID = 0"
    using `reachableFrom contracts' contracts'' steps` reachableFromGetDepositBridgeDead 
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
  assumes "reachableFrom contracts' contracts'' steps"
  shows "fst (callWithdrawWhileDead contracts'' address msg block' token amount' proof') \<noteq> Success"
proof-
  have "getTokenWithdrawn ((the (tokenDepositState contracts' address))) (hash2 (sender msg) token) = True"
    using assms
    using callWithdrawWhileDeadTokenWithdrawn by blast
  then have "getTokenWithdrawn ((the (tokenDepositState contracts'' address))) (hash2 (sender msg) token) = True"
    using assms
    using reachableFromGetTokenWithdrawn by blast
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
  assumes "reachableFrom contracts contracts' (CANCEL_WD tokenDepositAddress caller ID token amount proof # steps)"
  shows "\<nexists> token' caller' amount' proof'. CANCEL_WD tokenDepositAddress caller' ID token' amount' proof' \<in> set steps"
  using assms callCancelNoDouble 
  by (smt (verit, ccfv_SIG) executeStep.simps(7)fst_conv reachableFromCons' reachableFromStepInSteps)

lemma CANCELNoDouble:
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [CANCEL_WD tokenDepositAddress caller ID token amount proof] @ steps2 @ [CANCEL_WD tokenDepositAddress caller' ID token' amount' proof'] @ steps3"
  shows False
  using assms
  by (metis CANCELNoDoubleCons Un_iff append_Cons list.set_intros(1) reachableFromAppend set_append)

end

context HashProofVerifier
begin

lemma noCancelBeforeDepositSteps:
  assumes "reachableFrom contracts contracts' (steps1 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps @ [CANCEL_WD tokenDepositAddress caller ID token amount proof] @ steps2)"
  shows False
proof-
  obtain contractsA contractsB contracts1 contracts2 where
   "reachableFrom contractsA contracts1 [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
   "reachableFrom contracts1 contracts2 steps"
   "reachableFrom contracts2 contractsB [DEPOSIT tokenDepositAddress caller' ID token' amount']"
    using assms
    by (meson reachableFromAppend)
  then have "bridgeDead contracts1 tokenDepositAddress"
    by (meson list.set_intros(1) noCancelBeforeBridgeDead)
  then have "bridgeDead contracts2 tokenDepositAddress"
    by (metis \<open>reachableFrom contracts1 contracts2 steps\<close> reachableFromDeadState)
  then show False
    using \<open>reachableFrom contracts2 contractsB [DEPOSIT tokenDepositAddress caller' ID token' amount']\<close>
    by (metis executeStep.simps(1)  callDepositNotBridgeDead' reachableFromBridgeDead reachableFromCons')
qed

end


context StrongHashProofVerifier
begin

lemma callCancelDepositWhileDeadGetDepositBefore:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "getDeposit (the (tokenDepositState contracts address)) ID = hash3 (sender msg) token amount"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma onlyDepositorCanCancel:
  assumes deposit: "callDeposit contractsD tokenDepositAddress block msg ID token amount = (Success, contractsD')"
  \<comment> \<open>after a while a  claim is made\<close>
  assumes "reachableFrom contractsD' contractsC steps"
  assumes cancel: "callCancelDepositWhileDead contractsC tokenDepositAddress msg' block' ID token' amount' proof = (Success, contractsC')"
  shows "sender msg' = sender msg" "token' = token" "amount' = amount"
proof-
  have "getDeposit (the (tokenDepositState contractsD' tokenDepositAddress)) ID = hash3 (sender msg) token amount"
    using callDepositWritesHash deposit
    by simp
  moreover
  have "getDeposit (the (tokenDepositState contractsC tokenDepositAddress)) ID = hash3 (sender msg') token' amount'"
    using callCancelDepositWhileDeadGetDepositBefore[OF cancel]
    by simp
  moreover
  have "getDeposit (the (tokenDepositState contractsC tokenDepositAddress)) ID = 
        getDeposit (the (tokenDepositState contractsD' tokenDepositAddress)) ID \<or>
        getDeposit (the (tokenDepositState contractsC tokenDepositAddress)) ID = 0"
    using assms
    by (metis reachableFromGetDeposit calculation(1) hash3_nonzero)
  ultimately
  show "sender msg' = sender msg" "token' = token" "amount' = amount"
    using hash3_nonzero hash3_inj
    by (smt (verit, best) hash3_inj_def)+
qed

lemma onlyDepositorCanCancelSteps:
  assumes "reachableFrom contracts contracts' steps"
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
  assumes "CANCEL_WD tokenDepositAddress caller' ID token' amount' proof \<in> set steps"
  shows "caller' = caller" "token' = token" "amount' = amount"
proof-
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"
  let ?CANCEL_step = "CANCEL_WD tokenDepositAddress caller' ID token' amount' proof"
  obtain steps1 steps2 where A: "steps = steps1 @ [?DEPOSIT_step] @ steps2"
    using assms
    using reachableFromStepInSteps by blast
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
    "reachableFrom contracts1 contracts2 [?DEPOSIT_step]"
    "reachableFrom contracts2 contracts3 steps2'"
    "reachableFrom contracts3 contracts4 [?CANCEL_step]"
    using A
    by (metis assms(1) reachableFromAppend)
  then have "caller' = caller \<and> token' = token \<and> amount' = amount"
    using reachableFromSingleton onlyDepositorCanCancel
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
  have "getDeposit (the (tokenDepositState contractsI tokenDepositAddress)) ID = hash3 (sender msg) token amount"
    using cancel
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
    by (simp add: Let_def split: option.splits prod.splits if_split_asm)
  then show ?thesis
    using assms getDepositWrittenOnlyByDeposit depositsEmpty reachableFromInitI
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
  then have "getClaim (the (bridgeState contractsUpdate' bridgeAddress)) ID = True"
    using claimStepSetsClaim reachableFromInitI
    by blast

  moreover

  have "verifyClaimProof () bridgeAddress ID stateRoot proof = True"
    using callCancelDepositWhileDeadVerifyClaimProof[OF assms]
    using getLastValidStateLVS
    by simp
    
  then have "getClaim (the (bridgeState contractsUpdate' bridgeAddress)) ID = False"
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
    by (smt (verit, ccfv_SIG) properSetup_def reachableFromERC20State generateStateRootUpdate' option.exhaust_sel properSetupInit properToken_def reachableFromInitI)
  then show ?thesis
    using assms
    unfolding callBalanceOf_def
    by (auto split: option.splits)
qed

end

end