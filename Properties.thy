theory Properties
  imports Reachability MoreList
begin

(* ------------------------------------------------------------------------------------ *)
context HashProofVerifier
begin

text \<open>No deposit after the bridge dies\<close>
theorem noDepositBridgeDead: 
  assumes "bridgeDead contracts tokenDepositAddress"
  assumes "reachableFrom contracts contracts' steps"
  shows "fst (callDeposit contracts' tokenDepositAddress block msg ID token amount) \<noteq> Success"
  using assms callDepositFailsInDeadState reachableFromBridgeDead
  by blast

(* ------------------------------------------------------------------------------------ *)
text \<open>No cancel before the bridge dies\<close>
lemma noCancelBeforeBridgeDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
  shows "\<nexists> step. step \<in> set steps \<and> (\<exists> caller ID token amount proof. step = CANCEL tokenDepositAddress caller ID token amount proof)"
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
    by (metis executeStep.simps(4) set_ConsD)
qed

end

context StrongHashProofVerifier
begin

(* ------------------------------------------------------------------------------------ *)
text \<open>There are no double deposits\<close>
theorem callDepositNoDouble:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"         
  assumes "reachableFrom contracts' contracts'' steps"
  shows "fst (callDeposit contracts'' address block' msg' ID token' amount') \<noteq> Success"
proof (cases "bridgeDead contracts'' address")
  case False
  have "getDeposit (the (tokenDepositState contracts' address)) ID = hash3 (sender msg) token amount"
    using callDepositWritesHash[OF assms(1)]
    by simp
  then have "getDeposit (the (tokenDepositState contracts'' address)) ID \<noteq> 0"
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
  then have *: "getClaim (the (bridgeState contracts' address)) ID = True"
    using state'_def
    by simp
  from \<open>reachableFrom contracts' contracts'' steps\<close>
  have "getClaim (the (bridgeState contracts'' address)) ID = True"
    using *
    using reachableFromGetClaim by blast
  then show ?thesis
    unfolding callClaim_def claim_def
    by (auto simp add: Let_def split: option.splits prod.splits)
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

text \<open>We want to prove that there cannot be two DEPOSIT steps with the same ID on the same tokenDeposit address\<close>

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



text \<open>We want to prove that there cannot be two CANCEL steps with the same ID on the same tokenDeposit address\<close>

lemma CANCELNoDoubleCons:
  assumes "reachableFrom contracts contracts' (CANCEL tokenDepositAddress caller ID token amount proof # steps)"
  shows "\<nexists> token' caller' amount' proof'. CANCEL tokenDepositAddress caller' ID token' amount' proof' \<in> set steps"
  by (smt (verit, ccfv_SIG) HashProofVerifier.executeStep.simps(4) HashProofVerifier_axioms assms callCancelNoDouble fst_conv reachableFromCons' reachableFromStepInSteps)

lemma CANCELNoDouble:
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [CANCEL tokenDepositAddress caller ID token amount proof] @ steps2 @ [CANCEL tokenDepositAddress caller' ID token' amount' proof'] @ steps3"
  shows False
  using assms
  by (metis CANCELNoDoubleCons Un_iff append_Cons list.set_intros(1) reachableFromAppend set_append)

end

context HashProofVerifier
begin

text \<open>We want to prove that there cannot be two CLAIM steps with the same ID on the same bridge address\<close>

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

lemma noCancelBeforeDepositSteps:
  assumes "reachableFrom contracts contracts' (steps1 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps @ [CANCEL tokenDepositAddress caller ID token amount proof] @ steps2)"
  shows False
proof-
  obtain contractsA contractsB contracts1 contracts2 where
   "reachableFrom contractsA contracts1 [CANCEL tokenDepositAddress caller ID token amount proof]"
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

(* ------------------------------------------------------------------------------------ *)

(*
                     update                                
   contractsUpdate'    \<rightarrow>   contractsUpdate
   properSetup
*)
locale Update = StrongHashProofVerifier +
  fixes tokenDepositAddress :: address
  fixes bridgeAddress :: address
  fixes contractsUpdate' :: Contracts
  fixes contractsUpdate :: Contracts
  fixes blockUpdate :: Block
  fixes blockNumUpdate :: uint256
  fixes stateRoot :: bytes32
  \<comment> \<open>starting from a properly configured state\<close>
  assumes properSetupUpdate':
   "properSetup contractsUpdate' tokenDepositAddress bridgeAddress"
  \<comment> \<open>the last update that happened\<close>
  assumes update:
    "let stateOracleAddress = stateOracleAddressB contractsUpdate' bridgeAddress
      in callUpdate contractsUpdate' stateOracleAddress blockUpdate blockNumUpdate stateRoot = (Success, contractsUpdate)"
begin
definition UPDATE_step where
  "UPDATE_step = UPDATE (stateOracleAddressB contractsUpdate' bridgeAddress) stateRoot"

lemma reachableFromUpdate'Update [simp]:
  shows "reachableFrom contractsUpdate' contractsUpdate [UPDATE_step]"
proof-
  have "executeStep contractsUpdate' blockNumUpdate blockUpdate (UPDATE_step) = (Success, contractsUpdate)"
    using update
    unfolding UPDATE_step_def
    by simp
  then show ?thesis
    using reachableFrom_base reachableFrom_step by blast
qed

lemma tokenDepositStateUpdate'NotNone [simp]:
  shows "tokenDepositState contractsUpdate' tokenDepositAddress \<noteq> None"
  by (meson properSetupUpdate' properSetup_def)

lemma properSetupUpdate [simp]:
  shows "properSetup contractsUpdate tokenDepositAddress bridgeAddress"
  using callUpdateProperSetup update properSetupUpdate' 
  by presburger

lemma depositUpdate' [simp]: 
  shows "BridgeState.deposit (the (bridgeState contractsUpdate' bridgeAddress)) = tokenDepositAddress"
  by (meson properSetupUpdate' properSetup_def)

lemma generateStateRootUpdate' [simp]:
  shows "generateStateRoot contractsUpdate' = stateRoot"
  using update updateSuccess 
  by force

end


(* ------------------------------------------------------------------------------------ *)

(*
                         update                    [stepsNoUpdate]             
   contractsLastUpdate'    \<rightarrow>   contractsLastUpdate      \<rightarrow>*    contractsLU
   properSetup                                        noUpdates                  
*)
locale LastUpdate = 
  Update where
    contractsUpdate=contractsLastUpdate and 
    contractsUpdate'=contractsLastUpdate' and
    blockUpdate=blockLastUpdate and
    blockNumUpdate=blockNumLastUpdate
    for contractsLastUpdate and  contractsLastUpdate' and blockLastUpdate and blockNumLastUpdate + 
  fixes contractsLU :: Contracts
  fixes stepsNoUpdate :: "Step list"
  \<comment> \<open>there were no updates since the last update\<close>
  assumes reachableFromLastUpdateLU [simp]: 
    "reachableFrom contractsLastUpdate contractsLU stepsNoUpdate"
  assumes noUpdate:
    "let stateOracleAddress = stateOracleAddressB contractsLastUpdate bridgeAddress
      in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set stepsNoUpdate"
begin

lemma reachableFromLastUpdate'LU [simp]:
  shows "reachableFrom contractsLastUpdate' contractsLU (stepsNoUpdate @ [UPDATE_step])"
  using reachableFromLastUpdateLU reachableFromTrans reachableFromUpdate'Update by blast

lemma properSetupLU [simp]:
  shows "properSetup contractsLU tokenDepositAddress bridgeAddress"
  using properSetupReachable properSetupUpdate' reachableFromLastUpdate'LU by blast

lemma stateOracleAddressBLU [simp]:
  shows "stateOracleAddressB contractsLU bridgeAddress =
         stateOracleAddressB contractsLastUpdate' bridgeAddress"
  using reachableFromBridgeStateOracle reachableFromLastUpdate'LU 
  by blast

lemma depositLU [simp]:
  "BridgeState.deposit (the (bridgeState contractsLU bridgeAddress)) = tokenDepositAddress"
  using reachableFromBridgeDeposit reachableFromLastUpdate'LU depositUpdate'
  by blast

lemma callLastStateLU [simp]:
  shows "callLastState contractsLU (stateOracleAddressB contractsLU bridgeAddress) = 
         (Success, stateRoot)"
  using noUpdate noUpdateLastState callUpdateLastState update
  using reachableFromBridgeStateOracle reachableFromLastUpdate'LU reachableFromLastUpdateLU
  by (smt (verit, ccfv_threshold) callLastState_def  option.case_eq_if properSetupLU properSetup_def )

lemma getLastStateBLU [simp]:
  shows "getLastStateB contractsLU bridgeAddress = stateRoot"
  using callLastState callLastStateLU
  by blast

lemma  getLastStateTDLU [simp]:
  shows "getLastStateTD contractsLU tokenDepositAddress = stateRoot"
  by (metis getLastStateBLU properSetupLU properSetup_getLastState)

theorem callClaimGetDeposit:
  \<comment> \<open>claim succeded\<close>
  assumes claim: "callClaim contractsLU bridgeAddress msg ID token amount proof = (Success, contractsClaim)"
  shows "getDeposit (the (tokenDepositState contractsLastUpdate' tokenDepositAddress)) ID = hash3 (sender msg) token amount"
proof-
  define stateBridge where "stateBridge = the (bridgeState contractsLU bridgeAddress)"
  have "callVerifyDepositProof contractsLU (BridgeState.proofVerifier stateBridge) (BridgeState.deposit stateBridge) ID (hash3 (sender msg) token amount)
         stateRoot proof = Success"
    using callClaimCallVerifyProof[OF claim] getLastStateBLU
    unfolding stateBridge_def Let_def
    by simp
  then have "verifyDepositProof () tokenDepositAddress ID (hash3 (sender msg) token amount) stateRoot proof = True"
    unfolding callVerifyDepositProof_def stateBridge_def
    by (simp split: option.splits if_split_asm)
  then show ?thesis
    using verifyDepositProofE
    by (metis generateStateRootUpdate' option.collapse tokenDepositStateUpdate'NotNone)
qed

end

(*
   contractsInit
   properSetup
   getDeposit=0
   lastStateB=0
*)

locale Init' = StrongHashProofVerifier + 
  fixes tokenDepositAddress :: address
  fixes bridgeAddress :: address
  fixes contractsInit :: Contracts
  \<comment> \<open>The operation starts from an initial state that is properly setup\<close>
  assumes properSetupInit [simp]:
    "properSetup contractsInit tokenDepositAddress bridgeAddress"
  \<comment> \<open>All relevant data is still empty\<close>
  assumes depositsEmpty [simp]: 
    "\<And> ID. getDeposit (the (tokenDepositState contractsInit tokenDepositAddress)) ID = 0"
  assumes claimsEmpty [simp]:
    "\<And> ID. getClaim (the (bridgeState contractsInit bridgeAddress)) ID = False"
  assumes lastStateBZero [simp]:
    "getLastStateB contractsInit bridgeAddress = 0"

(*
                  [stepsI]
   contractsInit      \<rightarrow>*       contractsI
   properSetup
   getDeposit=0
   lastStateB=0
*)
locale Init = Init' + 
  fixes contractsI :: Contracts
  fixes stepsInit :: "Step list"
  assumes reachableFromInitI [simp]:
    "reachableFrom contractsInit contractsI stepsInit"
begin

lemma properSetupI [simp]: 
  shows "properSetup contractsI tokenDepositAddress bridgeAddress"
  using properSetupInit properSetupReachable reachableFromInitI
  by blast

lemma lastStateTDZeroInit [simp]:
  shows "getLastStateTD contractsInit tokenDepositAddress = 0"
  by (metis lastStateBZero properSetupInit properSetup_getLastState)

lemma tokenDepositStateINotNone [simp]:
  shows "tokenDepositState contractsI tokenDepositAddress \<noteq> None"
  by (meson properSetupI properSetup_def)

lemma bridgeStateINotNone [simp]:
  shows "bridgeState contractsI bridgeAddress \<noteq> None"
  by (meson properSetupI properSetup_def)

lemma bridgeBridgeAddress [simp]:
  shows "TokenDepositState.bridge (the (tokenDepositState contractsI tokenDepositAddress)) = bridgeAddress"
  by (meson properSetupI properSetup_def)

lemma tokenDepositTokenDepositAddress [simp]:
  shows "BridgeState.deposit (the (bridgeState contractsI bridgeAddress)) = tokenDepositAddress"
  by (meson properSetupI properSetup_def)

lemma stateOracleAddressBI [simp]:
  shows "stateOracleAddressB contractsI bridgeAddress =
         stateOracleAddressB contractsInit bridgeAddress"
  using reachableFromBridgeStateOracle reachableFromInitI by blast

lemma stateOracleAddressTDI [simp]:
  shows "stateOracleAddressTD contractsI tokenDepositAddress =
         stateOracleAddressTD contractsInit tokenDepositAddress"
  using reachableFromDepositStateOracle reachableFromInitI
  by blast

lemma ERC20stateINonNone [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "ERC20state contractsI token \<noteq> None"
  using assms
  by (meson reachableFromERC20State properToken_def reachableFromInitI)

end

locale InitUpdate = Init where contractsI=contractsUpdate' + Update
begin
lemma reachableFromInitLastUpdate [simp]:
  shows "reachableFrom contractsInit contractsUpdate (UPDATE_step # stepsInit)"
    using reachableFromInitI reachableFromUpdate'Update
    by (meson reachableFromSingleton reachableFrom_step)
end

sublocale InitUpdate \<subseteq> InitUpdate: Init where contractsI=contractsUpdate and stepsInit="UPDATE_step # stepsInit"
  by (unfold_locales, simp)


(*
                  [stepsI]
   contractsInit      \<rightarrow>*       contractsI
   properSetup    _ @ [UPDATE]
   getDeposit=0
   lastStateB=0
*)
locale InitFirstUpdate = Init + 
  fixes stateRootInit :: "bytes32"
  assumes firstUpdate:
    "stepsInit \<noteq> [] \<and> last stepsInit = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
  assumes updatesNonZeroInit [simp]:
    "updatesNonZero stepsInit"
begin

lemma stateRootInitNonZero:
  "stateRootInit \<noteq> 0"
  using firstUpdate updatesNonZeroInit
  unfolding updatesNonZero_def
  by (metis last_in_set)

definition UPDATE1_step where 
  "UPDATE1_step = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"

lemma obtainContractsU:
  obtains blockU blockNumU contractsU where
  "callUpdate contractsInit (stateOracleAddressB contractsInit bridgeAddress) blockU blockNumU stateRootInit = (Success, contractsU)" and
  "reachableFrom contractsU contractsI (butlast stepsInit)"
proof-
  obtain steps where "stepsInit = steps @ [UPDATE1_step]"
    using firstUpdate
    unfolding UPDATE1_step_def
    by (metis append_butlast_last_id)
  then show ?thesis
    using reachableFromInitI that
    unfolding UPDATE1_step_def
    by (smt (verit, best) \<open>\<And>thesis. (\<And>steps. stepsInit = steps @ [UPDATE1_step] \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>stepsInit = steps @ [UPDATE1_step]\<close> append.right_neutral butlast.simps(2) butlast_append executeStep.simps(3) list.distinct(1) reachableFrom.cases reachableFromAppend reachableFromCons')
qed

lemma getLastStateBContractsU:
  assumes "callUpdate contractsInit (stateOracleAddressB contractsInit bridgeAddress) blockU blockNumU stateRootInit = (Success, contractsU)"
  shows "getLastStateB contractsU bridgeAddress = stateRootInit"
  using assms
  using callUpdateIBridge callUpdateLastState 
  by presburger

lemma generateStateRootInit:
  shows "generateStateRoot contractsInit = stateRootInit"
proof-
  obtain blockU blockNumU contractsU
    where "callUpdate contractsInit (stateOracleAddressB contractsInit bridgeAddress) blockU blockNumU stateRootInit = (Success, contractsU)"
    by (meson obtainContractsU)
  then show ?thesis
    using updateSuccess 
    by blast
qed

lemma getLastStateBContractsUNonZero:
  shows "getLastStateB contractsI bridgeAddress \<noteq> 0"
  by (metis lastStateNonZero reachableFromBridgeStateOracle firstUpdate last_in_set reachableFromInitI updatesNonZeroInit)

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

  have "getDeposit (the (tokenDepositState contractsU tokenDepositAddress)) ID = hash3 (sender msg) token amount"
    using assms LastUpdate'.callClaimGetDeposit
    by (smt (verit, best) reachableFromBridgeStateOracle callUpdateITokenDeposit properSetupReachable stateOracleAddress_def)
  then show ?thesis
    using hashWrittenOnlyByDeposit
    using depositsEmpty assms
    using \<open>reachableFrom contractsInit contractsU steps1\<close> \<open>set steps1 \<subseteq> set stepsInit\<close>
    by blast
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
  have "getDeposit (the (tokenDepositState contractsD' tokenDepositAddress)) ID = hash3 (sender msg) token amount"
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

  have "getDeposit (the (tokenDepositState contractsUx tokenDepositAddress)) ID = hash3 (sender msg') token' amount'"
    using LastUpdate'.callClaimGetDeposit[OF claim]
    by simp

  have "hash3 (sender msg) token amount = hash3 (sender msg') token' amount'"
    using reachableFromGetDeposit
    using \<open>getDeposit (the (tokenDepositState contractsD' tokenDepositAddress)) ID = hash3 (sender msg) token amount\<close> 
    using \<open>getDeposit (the (tokenDepositState contractsUx tokenDepositAddress)) ID = hash3 (sender msg') token' amount'\<close>
    using \<open>callUpdate contractsUx stateOracleAddress blockx blockNumx stateRootx = (Success, contractsU'x)\<close>
    using hash3_nonzero
    using \<open>reachableFrom contractsD' contractsUx steps1x\<close>
    by (metis callUpdateITokenDeposit)
  then show "sender msg = sender msg'" "token = token'" "amount = amount'"
    using hash3_inj
    unfolding hash3_inj_def
    by metis+
qed

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
  assumes "CANCEL tokenDepositAddress caller' ID token' amount' proof \<in> set steps"
  shows "caller' = caller" "token' = token" "amount' = amount"
proof-
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"
  let ?CANCEL_step = "CANCEL tokenDepositAddress caller' ID token' amount' proof"
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
    by (metis executeStep.simps(1) executeStep.simps(4) onlyDepositorCanCancel(1) onlyDepositorCanCancel(2) onlyDepositorCanCancel(3) reachableFromSingleton senderMessage)
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
    using assms hashWrittenOnlyByDeposit depositsEmpty reachableFromInitI
    by blast
qed

end

context HashProofVerifier
begin

(* ------------------------------------------------------------------------------------ *)

primrec DEPOSIT_amount where
  "DEPOSIT_amount (DEPOSIT address caller ID token amount) = amount"

primrec CLAIM_amount where
  "CLAIM_amount (CLAIM address caller ID token amount proof) = amount"

primrec WITHDRAW_amount where
  "WITHDRAW_amount (WITHDRAW address caller token amount proof) = amount"

primrec CANCEL_amount where
  "CANCEL_amount (CANCEL address caller ID token amount proof) = amount"

fun isTokenDeposit :: "address \<Rightarrow> address \<Rightarrow> Step \<Rightarrow> bool" where
  "isTokenDeposit address token (DEPOSIT address' caller ID token' amount) \<longleftrightarrow> address' = address \<and> token' = token"
| "isTokenDeposit address token _ = False"

\<comment> \<open>All deposits of the given token on the given address\<close>
definition tokenDeposits where
  "tokenDeposits address token steps = filter (isTokenDeposit address token) steps"

\<comment> \<open>Total amount of the given token deposited on the given address\<close>
definition depositedTokenAmount where
  "depositedTokenAmount address token steps = sum_list (map DEPOSIT_amount (tokenDeposits address token steps))"

lemma tokenDepositsConsDeposit [simp]:
  shows "tokenDeposits tokenDepositAddress token (DEPOSIT tokenDepositAddress caller ID token amount # steps) =
         DEPOSIT tokenDepositAddress caller ID token amount # tokenDeposits tokenDepositAddress token steps"
  unfolding tokenDeposits_def
  by simp

lemma tokenDepositsConsDepositOther [simp]:
  assumes "tokenDepositAddress \<noteq> tokenDepositAddress' \<or> token \<noteq> token'"
  shows "tokenDeposits tokenDepositAddress token (DEPOSIT tokenDepositAddress' caller ID token' amount # steps) =
         tokenDeposits tokenDepositAddress token steps"
  using assms
  unfolding tokenDeposits_def
  by auto

lemma tokenDepositsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "tokenDeposits tokenDepositAddress token (step # steps) = tokenDeposits tokenDepositAddress token steps"
  using assms
  by (cases step, auto simp add: tokenDeposits_def)

lemma depositedTokenAmountConsDeposit [simp]:
  shows "depositedTokenAmount address token (DEPOSIT address caller ID token amount # steps) = 
         amount + depositedTokenAmount address token steps"
  by (simp add: depositedTokenAmount_def)

lemma depositedTokenAmountConsDepositOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "depositedTokenAmount address token (DEPOSIT address' caller ID token' amount # steps) = 
         depositedTokenAmount address token steps"
  using assms
  by (auto simp add: depositedTokenAmount_def)

lemma depositedTokenAmoutConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount'. step = DEPOSIT address' caller' ID' token' amount'"
  shows "depositedTokenAmount address token (step # steps) = depositedTokenAmount address token steps"
  using assms 
  unfolding depositedTokenAmount_def
  by (cases step, auto)


fun isTokenClaim where
  "isTokenClaim address token (CLAIM address' caller ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isTokenClaim address token _ = False"

\<comment> \<open>All claims of a given token on the given bridge\<close>
definition tokenClaims where 
  "tokenClaims address token steps = 
   filter (isTokenClaim address token) steps"

\<comment> \<open>Total amount of a given token claimed on the given bridge\<close>
definition claimedTokenAmount where
  "claimedTokenAmount address token steps = 
   sum_list (map CLAIM_amount (tokenClaims address token steps))"

lemma claimedTokenAmoutConsClaim [simp]:
  shows "claimedTokenAmount address token (CLAIM address caller ID token amount proof # steps) = claimedTokenAmount address token steps + amount"
  unfolding claimedTokenAmount_def tokenClaims_def
  by auto

lemma claimedTokenAmoutConsClaimOther [simp]:
  assumes "address' \<noteq> address \<or> token' \<noteq> token"
  shows "claimedTokenAmount address token (CLAIM address' caller ID token' amount proof # steps) = claimedTokenAmount address token steps"
  using assms
  unfolding claimedTokenAmount_def tokenClaims_def
  by auto

lemma claimedTokenAmoutConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CLAIM address' caller' ID' token' amount' proof'"
  shows "claimedTokenAmount address token (step # steps) = claimedTokenAmount address token steps"
  using assms 
  unfolding claimedTokenAmount_def tokenClaims_def
  by (cases step, auto)

primrec DEPOSIT_id where
  "DEPOSIT_id (DEPOSIT address caller ID token amount) = ID"

(* NOTE: only for the given token *)
definition isClaimedID where
 "isClaimedID bridgeAddress token ID steps \<longleftrightarrow> (\<exists> caller' amount' proof'. CLAIM bridgeAddress caller' ID token amount' proof' \<in> set steps)"

\<comment> \<open>All deposits of the given token on the given address that have been claimed\<close>
definition claimedTokenDeposits where
  "claimedTokenDeposits tokenDepositAddress bridgeAddress token steps = 
     filter 
      (\<lambda> step. isClaimedID bridgeAddress token (DEPOSIT_id step) steps) 
      (tokenDeposits tokenDepositAddress token steps)"

\<comment> \<open>Total amount of tokens that have been deposited on the given address and then claimed\<close>
definition claimedTokenDepositsAmount where
  "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps = 
   sum_list (map DEPOSIT_amount (claimedTokenDeposits tokenDepositAddress bridgeAddress token steps))"

lemma claimedTokenDepositsAmountConsOther: 
  assumes "\<nexists> caller ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"
  shows "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token (step # steps) =
         claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps"
proof-
  have "tokenDeposits tokenDepositAddress token (step # steps) = tokenDeposits tokenDepositAddress token steps"
    using assms
    unfolding tokenDeposits_def
    by (cases step, auto)
  then have "claimedTokenDeposits tokenDepositAddress bridgeAddress token (step # steps) = 
             claimedTokenDeposits tokenDepositAddress bridgeAddress token steps"
    using assms
    unfolding claimedTokenDeposits_def isClaimedID_def
    by (smt (verit, del_insts) filter_cong list.set_intros(2) set_ConsD)
  then show ?thesis
    unfolding claimedTokenDepositsAmount_def
    by simp
qed

end

context InitFirstUpdate
begin


(*
                   stepsInit                CLAIM
contractsInit        \<rightarrow>*         contractsI   \<rightarrow>   contractsClaim
properSetup        UPDATE
getDeposit=0
lastState=0
*)

lemma claimedTokenDepositsAmountConsClaim:
  assumes "reachableFrom contractsI contractsClaim [CLAIM bridgeAddress caller ID token amount proof]"
  shows   "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token
             (CLAIM bridgeAddress caller ID token amount proof # stepsInit) = 
           claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit + amount"
proof-
  define CLAIM_step where 
  "CLAIM_step = CLAIM bridgeAddress caller ID token amount proof"
  define DEPOSIT_step where
  "DEPOSIT_step = DEPOSIT tokenDepositAddress caller ID token amount"
  define claimed where
  "claimed = claimedTokenDeposits tokenDepositAddress bridgeAddress token (CLAIM_step # stepsInit)"

  have deposits: "tokenDeposits tokenDepositAddress token (CLAIM_step # stepsInit) = 
                  tokenDeposits tokenDepositAddress token stepsInit"
    unfolding CLAIM_step_def
    by (simp add: tokenDeposits_def)

  have "callClaim contractsI bridgeAddress (message caller amount) ID token amount proof = (Success, contractsClaim)"
    using assms
    by (metis executeStep.simps(2) reachableFromSingleton)
  then have "DEPOSIT_step \<in> set stepsInit"
    using depositBeforeClaim[where msg="message caller amount"]
    unfolding DEPOSIT_step_def
    by simp
  then have "DEPOSIT_step \<in> set claimed"
    unfolding DEPOSIT_step_def CLAIM_step_def claimed_def
    unfolding claimedTokenDeposits_def tokenDeposits_def isClaimedID_def
    by auto

  obtain steps1 steps2 where steps: "stepsInit = steps1 @ [DEPOSIT_step] @ steps2"
    using \<open>DEPOSIT_step \<in> set stepsInit\<close>
    by (metis Cons_eq_append_conv in_set_conv_decomp self_append_conv2)

  have *: "\<forall> step \<in> set (steps1 @ steps2). (\<forall> caller' amount' ID'. step = DEPOSIT tokenDepositAddress caller' ID' token amount' \<longrightarrow> ID' \<noteq> ID)"
    using DEPOSITNoDouble'[OF reachableFromInitI] steps
    unfolding DEPOSIT_step_def
    by auto
  then have "DEPOSIT_step \<notin> set (steps1 @ steps2)"
    unfolding DEPOSIT_step_def
    by auto

  define P where "P = (\<lambda> step. isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit)"
  define P' where "P' = (\<lambda> step. isClaimedID bridgeAddress token (DEPOSIT_id step) (CLAIM_step # stepsInit))"
  define Q where "Q = (\<lambda> step. isTokenDeposit tokenDepositAddress token step)"

  define depositsInit where "depositsInit = tokenDeposits tokenDepositAddress token stepsInit"

  have "depositsInit = (filter Q steps1) @ [DEPOSIT_step] @ (filter Q steps2)"
    using \<open>stepsInit = steps1 @ [DEPOSIT_step] @ steps2\<close>
    unfolding depositsInit_def tokenDeposits_def Q_def DEPOSIT_step_def
    by auto
  then have claimed:
    "claimed = filter P' (filter Q steps1) @ filter P' [DEPOSIT_step] @ filter P' (filter Q steps2)"
    using deposits
    unfolding depositsInit_def claimed_def claimedTokenDeposits_def P'_def
    by auto

  define c1 where "c1 = filter P' (filter Q steps1)" 
  define c2 where "c2 = filter P' (filter Q steps2)" 

  have "DEPOSIT_step \<notin> set (c1 @ c2)"
    using \<open>DEPOSIT_step \<notin> set (steps1 @ steps2)\<close>
    unfolding c1_def c2_def
    by auto
  then have claimed: "claimed = c1 @ [DEPOSIT_step] @ c2"
    using claimed \<open>DEPOSIT_step \<in> set claimed\<close> 
    unfolding c1_def c2_def
    by (metis append.assoc append.right_neutral filter.simps(1) filter.simps(2))
  
  moreover

  have "set (c1 @ c2) \<subseteq> set (steps1 @ steps2)"
    unfolding c1_def c2_def
    by auto

  have "filter P depositsInit = c1 @ c2"
  proof (rule filter')
    show "DEPOSIT_step \<notin> set (c1 @ c2)"
      by fact
  next
    show "filter P' depositsInit = c1 @ [DEPOSIT_step] @ c2"
      using \<open>claimed = c1 @ [DEPOSIT_step] @ c2\<close> deposits
      unfolding depositsInit_def claimed_def claimedTokenDeposits_def P'_def
      by simp
  next
    show "\<forall> step \<in> set depositsInit. (P' step \<and> step \<noteq> DEPOSIT_step) \<longleftrightarrow> P step"
    proof safe
      fix step
      assume "step \<in> set depositsInit" "P' step" "step \<noteq> DEPOSIT_step"
      have "DEPOSIT_id step \<noteq> ID"
      proof-
        have "step \<in> set (filter Q steps1 @ filter Q steps2)"
          using \<open>step \<in> set depositsInit\<close> \<open>step \<noteq> DEPOSIT_step\<close>
          using \<open>depositsInit = (filter Q steps1) @ [DEPOSIT_step] @ (filter Q steps2)\<close>
          by auto
        then have "step \<in> set (steps1 @ steps2)" "Q step"
          by auto
        then obtain ID' caller' amount' where "step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
          unfolding Q_def
          by (metis isTokenDeposit.elims(2))
        then show ?thesis
          using * \<open>step \<in> set (steps1 @ steps2)\<close>
          by simp
      qed
      then show "P step"
        using \<open>P' step\<close>
        unfolding P_def P'_def CLAIM_step_def isClaimedID_def
        by auto
    next
      fix step
      assume "step \<in> set depositsInit" "P step"
      then show "P' step"
        unfolding P_def P'_def isClaimedID_def
        by auto
    next
      assume "P DEPOSIT_step"
      have "reachableFrom contractsInit contractsClaim (CLAIM bridgeAddress caller ID token amount proof # stepsInit)"
        by (meson assms(1) reachableFromInitI reachableFromSingleton reachableFrom_step)
      then show False
        using CLAIMNoDoubleCons \<open>P DEPOSIT_step\<close>
        unfolding P_def DEPOSIT_step_def isClaimedID_def depositsInit_def
        by auto
    qed
  qed
  then have "claimedTokenDeposits tokenDepositAddress bridgeAddress token stepsInit = c1 @ c2"
    unfolding claimed_def P_def claimedTokenDeposits_def depositsInit_def
    by auto
  ultimately
  show ?thesis
    unfolding claimed_def claimedTokenDepositsAmount_def
    unfolding CLAIM_step_def DEPOSIT_step_def depositsInit_def
    by simp
qed

lemma noClaimBeforeDeposit:
  assumes CLAIM_in_steps: "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
  assumes reach: "reachableFrom contractsInit contractsDeposit (DEPOSIT tokenDepositAddress caller ID token amount # stepsInit)"
  shows "False"
proof-
  define DEPOSIT_step where "DEPOSIT_step = DEPOSIT tokenDepositAddress caller ID token amount"
  define CLAIM_step where "CLAIM_step = CLAIM bridgeAddress caller' ID token' amount' proof'"
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
  proof
    show "reachableFrom contractsInit c1 steps2" by fact
   next
    show "updatesNonZero steps2"
      by (metis "*"(4) Cons_eq_append_conv add_cancel_right_right list.size(4) nat.simps(3) updatesNonZeroAppend(2) updatesNonZeroInit)
  next
    show "steps2 \<noteq> [] \<and> last steps2 = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
      by (metis "*"(4) CLAIM_step_def Nil_is_append_conv Step.distinct(10) firstUpdate last.simps last_append not_Cons_self)
  qed

  have "DEPOSIT_step' \<in> set steps2"
    using * InitFirstUpdate'.depositBeforeClaim
    unfolding CLAIM_step_def DEPOSIT_step'_def
   by fastforce

  moreover

  obtain steps1' where "steps1 = DEPOSIT_step # steps1'"
    using *(4)
    unfolding DEPOSIT_step_def CLAIM_step_def
    by (metis Cons_eq_append_conv Step.simps(6) list.sel(1))

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

(*
                steps               DEPOSIT
contractsInit    \<rightarrow>*     contractsI    \<rightarrow>   contractsDeposit
properSetup
getDeposit=0
lastState=0
*)
lemma claimedTokenDepositsAmountConsDeposit:
  assumes "reachableFrom contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
  shows "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token
            (DEPOSIT tokenDepositAddress caller ID token amount # stepsInit) =
         claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit"
proof-
  define DEPOSIT_step where "DEPOSIT_step = DEPOSIT tokenDepositAddress caller ID token amount"
  have "claimedTokenDeposits tokenDepositAddress bridgeAddress token (DEPOSIT_step # stepsInit) = 
        claimedTokenDeposits tokenDepositAddress bridgeAddress token stepsInit"
  proof-
    have "tokenDeposits tokenDepositAddress token (DEPOSIT_step # stepsInit) = 
          DEPOSIT_step # tokenDeposits tokenDepositAddress token stepsInit"
      unfolding tokenDeposits_def DEPOSIT_step_def
      by simp

    moreover

    have reach: "reachableFrom contractsInit contractsDeposit (DEPOSIT_step # stepsInit)"
      by (metis DEPOSIT_step_def assms reachableFromInitI reachableFromSingleton reachableFrom_step)
    then have "\<nexists> caller' token' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
      using noClaimBeforeDeposit
      unfolding DEPOSIT_step_def
      by blast

    ultimately
    
    show ?thesis
      unfolding claimedTokenDeposits_def
      using DEPOSIT_id.simps DEPOSIT_step_def isClaimedID_def
      by auto
  qed
  then show ?thesis
    unfolding claimedTokenDepositsAmount_def DEPOSIT_step_def
    by simp
qed

end

context HashProofVerifier
begin

lemma InitInduction [simp]:
assumes "Init hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof generateClaimProof
         verifyBalanceProof generateBalanceProof tokenDepositAddress bridgeAddress contractsInit contractsI
         (step # steps)"
assumes "reachableFrom contractsInit contractsI' steps"
assumes "executeStep contractsI' blockNum block step = (Success, contractsI)"
shows "Init hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof generateClaimProof
       verifyBalanceProof generateBalanceProof tokenDepositAddress bridgeAddress contractsInit contractsI' steps"
  using assms
  by (simp add: Init_def Init_axioms_def)

lemma InitFirstUpdateAxiomsInduction [simp]:
  assumes "InitFirstUpdate hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof
     generateClaimProof verifyBalanceProof generateBalanceProof tokenDepositAddress bridgeAddress contractsInit
     contractsI (step # steps) stateRootInit"
  assumes "reachableFrom contractsInit contractsI' steps"
  assumes "executeStep contractsI' blockNum block step = (Success, contractsI)"
  assumes "steps \<noteq> []"
  shows "InitFirstUpdate hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof
      generateClaimProof verifyBalanceProof generateBalanceProof tokenDepositAddress bridgeAddress contractsInit
      contractsI' steps stateRootInit"
  using assms
  unfolding InitFirstUpdate_def InitFirstUpdate_axioms_def
  by (metis InitInduction last_ConsR updatesNonZeroCons(1))
end


context InitFirstUpdate
begin

(*               [steps]
   contractsInit   \<rightarrow>*    contracts 
                           \<not> dead
*)
lemma totalBalanceMintedTokenBridgeNotDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "bridgeMintedToken contractsInit bridgeAddress token = mintedToken"
  assumes "mintedToken \<noteq> token"
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "totalBalance (the (ERC20state contractsI mintedToken)) = 
         totalBalance (the (ERC20state contractsInit mintedToken)) + claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit"
  using reachableFromInitI assms InitFirstUpdate_axioms
proof (induction contractsInit contractsI stepsInit rule: reachableFrom.induct)
  case (reachableFrom_base contractsInit)
  then show ?case
    by (simp add: claimedTokenDepositsAmount_def claimedTokenDeposits_def isClaimedID_def)
next
  case (reachableFrom_step steps contractsI contractsInit contractsI' blockNum block step)

  show ?case
  proof (cases "steps = []")
    case True
    then have "reachableFrom contractsInit contractsI' []"
      using reachableFrom_step.hyps
      by simp
    then have "contractsInit = contractsI'"
      using reachableFrom.cases
      by blast
    then have "totalBalance (the (ERC20state contractsI' mintedToken)) =
        totalBalance (the (ERC20state contractsInit mintedToken))"
      by simp
    moreover
    have "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token
          [UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit] = 0"
      by (simp add: claimedTokenDepositsAmount_def claimedTokenDeposits_def tokenDeposits_def)
    moreover
    have "step = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
      by (metis InitFirstUpdate.firstUpdate True last.simps reachableFrom_step.prems(5))
    ultimately
    show ?thesis
      using reachableFrom_step.prems reachableFrom_step.hyps firstUpdate True
      by simp
  next
    case False

    interpret InitFirstUpdate': InitFirstUpdate  where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
      using False InitFirstUpdateAxiomsInduction reachableFrom_step.hyps(1) reachableFrom_step.hyps(2) reachableFrom_step.prems(5) by blast

    have *: "reachableFrom contractsInit contractsI (step # steps)"
      using reachableFrom.reachableFrom_step reachableFrom_step
      by blast
    have notDead: "\<not> bridgeDead contractsI' tokenDepositAddress"
      using False
      using reachableFrom.reachableFrom_step reachableFromBridgeDead reachableFrom_base reachableFrom_step.hyps(2) reachableFrom_step.prems(4)
      by blast

    have *: "totalBalance (the (ERC20state contractsI' mintedToken)) =
             totalBalance (the (ERC20state contractsInit mintedToken)) +
             claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps"
      using reachableFrom_step.IH reachableFrom_step.prems
      using InitFirstUpdate'.InitFirstUpdate_axioms notDead 
      by fastforce

    show ?thesis
    proof (cases step)
      case (DEPOSIT address' caller ID token' amount)
      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token")
        case False
        have "token' \<noteq> mintedToken"
          sorry (* no direct deposit on minted token *)
        then have "ERC20state contractsI mintedToken = ERC20state contractsI' mintedToken"
          using DEPOSIT reachableFrom_step.prems reachableFrom_step.hyps callDepositOtherToken
          by (metis executeStep.simps(1))
        moreover 
        have "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps =
              claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token (DEPOSIT address' caller ID token' amount # steps)"
          using claimedTokenDepositsAmountConsOther False
          using False
          by auto
        ultimately show ?thesis
          using * reachableFrom_step.prems DEPOSIT
          by simp
      next
        case True
        have "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token (step # steps) = 
              claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps"
          using InitFirstUpdate'.claimedTokenDepositsAmountConsDeposit
          using DEPOSIT True reachableFrom.reachableFrom_step reachableFrom_base reachableFrom_step.hyps(2) 
          by blast
        then show ?thesis
          using * 
          using DEPOSIT True callDepositOtherToken executeStep.simps(1) reachableFrom_step.hyps(2) reachableFrom_step.prems(3)
          by metis
      qed
    next
      case (CLAIM address' caller ID token' amount proof')
      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token' = token")
        case True
        have "totalBalance (the (ERC20state contractsI mintedToken))  = 
              totalBalance (the (ERC20state contractsI' mintedToken)) + amount"
        proof (rule callClaimTotalBalance)
          show "finite (Mapping.keys (balances (the (ERC20state contractsI' mintedToken))))"
            sorry
        next
          show "callClaim contractsI' bridgeAddress (message caller amount) ID token' amount proof' = (Success, contractsI)"
            using True CLAIM reachableFrom_step.hyps
            by simp
        next
          show "bridgeMintedToken contractsI' bridgeAddress token' = mintedToken"
            using True reachableFromBridgeMintedToken reachableFrom_step.hyps(1) reachableFrom_step.prems(2) 
            by blast
        qed

        moreover

        have "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token
                  (CLAIM bridgeAddress caller ID token amount proof' # steps) =
              claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps + amount"
        proof (rule InitFirstUpdate'.claimedTokenDepositsAmountConsClaim)
          show "reachableFrom contractsI' contractsI [CLAIM bridgeAddress caller ID token amount proof']"
            using CLAIM True reachableFrom.reachableFrom_step reachableFrom_base reachableFrom_step.hyps(2) by blast
        qed

        ultimately
        
        show ?thesis
          using * CLAIM True
          by simp
      next
        case False
        have "mintedToken \<noteq> bridgeMintedToken contractsInit address' token'" (* no cancel of minted tokens *)
          sorry
        then have "ERC20state contractsI mintedToken = ERC20state contractsI' mintedToken"
          using CLAIM callClaimOtherToken[where msg="message caller amount"]
          by (metis executeStep.simps(2) reachableFromBridgeMintedToken InitFirstUpdate'.reachableFromInitI reachableFrom_step.hyps(2))
        then show ?thesis
          using False CLAIM reachableFrom_step * 
          by (simp add: claimedTokenDepositsAmountConsOther)
      qed
    next
      case (UPDATE address' stateRoot')
      then show ?thesis
        using reachableFrom_step *
        using claimedTokenDepositsAmountConsOther
        by simp
    next
      case (CANCEL address' caller' ID' token' amount' proof')
      have "mintedToken \<noteq> token'" (* no cancel of minted tokens *)
        sorry
      then have "ERC20state contractsI mintedToken = ERC20state contractsI' mintedToken"
        using CANCEL reachableFrom_step.hyps(2) by auto
      then show ?thesis
        using CANCEL reachableFrom_step *
        using claimedTokenDepositsAmountConsOther
        by simp
    next
      case (WITHDRAW address' caller token' amount proof')
      have "mintedToken \<noteq> token'" (* no withdrawal of minted tokens *)
        sorry
      then have "ERC20state contractsI mintedToken = ERC20state contractsI' mintedToken"
        using WITHDRAW reachableFrom_step.hyps(2) by auto
      moreover
      have "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token (step # steps) = 
            claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps"
        using claimedTokenDepositsAmountConsOther WITHDRAW
        by simp
      ultimately
      show ?thesis
        using WITHDRAW reachableFrom_step *
        by simp
    qed
  qed
qed

end

context HashProofVerifier
begin

lemma balanceOfTokenDepositContractBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
  assumes "\<not> bridgeDead contracts tokenDepositAddress"
  shows "balanceOf (the (ERC20state contracts token)) tokenDepositAddress = 
         balanceOf (the (ERC20state contractsInit token)) tokenDepositAddress + depositedTokenAmount tokenDepositAddress token steps"
  using assms
proof (induction contractsInit contracts steps rule: reachableFrom.induct)
  case (reachableFrom_base contractsInit)
  then show ?case
    by (simp add: depositedTokenAmount_def tokenDeposits_def)
next
  case (reachableFrom_step steps contracts' contractsInit contracts blockNum block step)
  have notDead: "\<not> bridgeDead contracts tokenDepositAddress"
    by (meson reachableFrom.intros(1) reachableFrom.reachableFrom_step reachableFromBridgeDead reachableFrom_step.hyps(2) reachableFrom_step.prems)

  then have *: 
    "balanceOf (the (ERC20state contracts token)) tokenDepositAddress =
     balanceOf (the (ERC20state contractsInit token)) tokenDepositAddress +
     depositedTokenAmount tokenDepositAddress token steps"
    using reachableFrom_step.IH
    by simp

  show ?case
  proof (cases step)
    case (DEPOSIT address' caller ID token' amount)
    have "caller \<noteq> tokenDepositAddress"
      sorry
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case False
      then show ?thesis
        using reachableFrom_step DEPOSIT \<open>caller \<noteq> tokenDepositAddress\<close>
        using callDepositBalanceOfOther notDead callDepositOtherToken depositedTokenAmountConsDepositOther 
        by (metis executeStep.simps(1) senderMessage)
    next
      case True
      then show ?thesis
        using reachableFrom_step DEPOSIT
        using callDepositBalanceOfContract notDead
        by auto
    qed
  next
    case (CLAIM address' caller ID token' amount proof')
    have "bridgeMintedToken contractsInit address' token' \<noteq> token"
      sorry (* no tokens are minted on the token contract *)
    then show ?thesis
      using * reachableFrom_step.hyps CLAIM
      using callClaimOtherToken
      by auto
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using * reachableFrom_step.hyps
      by simp
  next
    case (WITHDRAW address' caller token' amount proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress")
      case True
      then show ?thesis
        using WITHDRAW * reachableFrom_step.hyps reachableFrom_step.prems
        by (simp add: callWithdrawWhileDeadBridgeDead)
    next
      case False
      show ?thesis
      proof (cases "token = token'")
        case True
        have "caller \<noteq> tokenDepositAddress"
          sorry
        then have "balanceOf (the (ERC20state contracts' token)) tokenDepositAddress =
                   balanceOf (the (ERC20state contracts token)) tokenDepositAddress"
          using WITHDRAW reachableFrom_step notDead
          using True False callWithdrawWhileDead_balanceOfOther[of contracts address' "message caller 0"]
          by auto
        then show ?thesis
          using False WITHDRAW reachableFrom_step notDead
          by auto
      next
        case False
        then show ?thesis
          using WITHDRAW reachableFrom_step.hyps *
          by (metis Step.simps(12) callWithdrawWhileDeadOtherToken depositedTokenAmoutConsOther executeStep.simps(5))
      qed
    qed
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress")
      case True
      then have "bridgeDead contracts' tokenDepositAddress"
        using CANCEL reachableFrom_step
        using callCancelDepositWhileDeadBridgeDead 
        by (metis executeStep.simps(4))
      then show ?thesis
        using reachableFrom_step
        by blast
    next
      case False
      have "caller' \<noteq> tokenDepositAddress"
        sorry
      then show ?thesis
        using callCancelDepositWhileDead_balanceOfOther callCancelDepositOtherToken 
        using False CANCEL reachableFrom_step notDead
        by (metis Message.select_convs(1) Step.simps(10) depositedTokenAmoutConsOther executeStep.simps(4) message_def)
    qed
  qed
qed

end

context HashProofVerifier
begin

lemma noUpdateGetLastValidStateTD:
  assumes "executeStep contracts block blockNum step = (Success, contracts')"
  assumes "let stateOracleAddress = stateOracleAddressTD contracts tokenDepositAddress
            in \<nexists>stateRoot'. step = UPDATE stateOracleAddress stateRoot'"
  shows "getLastValidStateTD contracts' tokenDepositAddress = 
         getLastValidStateTD contracts tokenDepositAddress"
  using assms
proof (cases step)
  case (DEPOSIT address' caller' ID' token' amount')
  then show ?thesis
    using assms
    by simp
next
  case (CLAIM address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms
    by (metis callClaimGetLastValidStateTD executeStep.simps(2))
next
  case (UPDATE address' stateRoot')
  then show ?thesis
    using assms
    by (metis StateOracleState.callWithdrawWhileDeadGetLastValidStateTD executeStep.simps(3))
next
  case (CANCEL address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms
    by (smt (verit, ccfv_SIG) callCancelDepositWhileDeadIStateOracle callCancelDepositWhileDeadOtherAddress callCancelWhileDeadGetLastValidStateTD executeStep.simps(4) callLastState_def lastValidState_def)
next
  case (WITHDRAW address' caller' token' amount' proof')
  then show ?thesis
    using assms
    by (smt (verit, ccfv_SIG) callWithdrawWhileDeadGetLastValidStateTD callWithdrawWhileDeadOtherAddress executeStep.simps(5) callLastState_def callWithdrawWhileDeadIStateOracle lastValidState_def)
qed
end

(*
                         update                    [stepsNoUpdate]             
   contractsLastUpdate'    \<rightarrow>   contractsLastUpdate      \<rightarrow>*    contractsLU
   properSetup                      noUpdates
   bridgeNotDead                 
*)
locale LastUpdateBridgeNotDead = LastUpdate + 
  assumes bridgeNotDeadLastUpdate' [simp]:
    "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
begin

lemma lastValidStateLU [simp]:
  shows "let stateTokenDeposit = the (tokenDepositState contractsLU tokenDepositAddress)
          in snd (lastValidState contractsLU stateTokenDeposit) = stateRoot"
  using reachableFromLastUpdateLU LastUpdateBridgeNotDead_axioms
proof (induction contractsLastUpdate contractsLU stepsNoUpdate rule: reachableFrom.induct)
  case (reachableFrom_base contractsLastUpdate)
  then interpret LU': LastUpdateBridgeNotDead where contractsLastUpdate=contractsLastUpdate and contractsLU=contractsLastUpdate and stepsNoUpdate="[]"
    by simp    
  show ?case
    by (metis LU'.callLastStateLU LU'.update LU'.properSetupUpdate bridgeNotDeadLastUpdate' callUpdateITokenDeposit lastValidState_def properSetup_stateOracleAddress snd_eqD)
next
  case (reachableFrom_step steps contractsLU contractsLastUpdate contractsLU' blockNum block step)
  then interpret LU': LastUpdateBridgeNotDead where contractsLastUpdate=contractsLastUpdate and contractsLU=contractsLU' and stepsNoUpdate=steps
    unfolding LastUpdateBridgeNotDead_def LastUpdate_def LastUpdate_axioms_def Let_def
    by simp
  have "let stateTokenDeposit = the (tokenDepositState contractsLU' tokenDepositAddress)
    in snd (lastValidState contractsLU' stateTokenDeposit) = stateRoot"
    using reachableFrom_step.IH
    using LU'.LastUpdateBridgeNotDead_axioms by blast
  moreover
  have "let stateOracleAddress = stateOracleAddressB contractsLU' bridgeAddress
         in \<nexists>stateRoot'. step = UPDATE stateOracleAddress stateRoot'"
    by (metis HashProofVerifier.reachableFromBridgeStateOracle HashProofVerifier_axioms LU'.reachableFromLastUpdateLU LastUpdate.noUpdate LastUpdateBridgeNotDead.axioms(1) list.set_intros(1) reachableFrom_step.prems)
  ultimately
  show ?case
    using noUpdateGetLastValidStateTD
    using LU'.properSetupLU properSetup_stateOracleAddress reachableFrom_step.hyps(2) 
    by presburger
qed

end


(*
               [stepsInit]               update                     
  contractsInit  \<rightarrow>*   contractsUpdate'    \<rightarrow>   contractsUpdate  \<rightarrow>*  contractsLVS
  properSetup            properSetup                               getLastValidState=
                         bridgeNotDead                 
*)
locale InitUpdateBridgeNotDeadLastValidState = InitUpdate + 
  fixes contractsLVS :: Contracts
  fixes stepsLVS :: "Step list"
  assumes bridgeNotDead [simp]: 
    "\<not> bridgeDead contractsUpdate' tokenDepositAddress"
  assumes reachableFromUpdate'LVS [simp]: 
    "reachableFrom contractsUpdate contractsLVS stepsLVS"
  assumes getLastValidStateLVS: 
    "getLastValidStateTD contractsLVS tokenDepositAddress = (Success, stateRoot)"
begin
definition stepsAllLVS where
  "stepsAllLVS = stepsLVS @ [UPDATE_step] @ stepsInit"

lemma reachableFromInitLVS [simp]: 
  shows "reachableFrom contractsInit contractsLVS stepsAllLVS"
  unfolding stepsAllLVS_def
  using reachableFromTrans reachableFromUpdate'LVS  reachableFromInitI reachableFromUpdate'Update
  by blast

end

sublocale InitUpdateBridgeNotDeadLastValidState \<subseteq> InitLVS: Init where contractsI=contractsLVS and stepsInit="stepsAllLVS"
  using reachableFromInitLVS 
  by unfold_locales auto

context InitUpdateBridgeNotDeadLastValidState
begin

theorem cancelDepositWhileDeadNoClaim:
  \<comment> \<open>Cancel deposit succeded\<close>
  assumes cancel:
    "callCancelDepositWhileDead contractsLVS tokenDepositAddress msg block ID token amount proof = 
      (Success, contractsCancel)"
  \<comment> \<open>Claim did not happen before that last update\<close>
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
    by (simp add: Let_def)
  then have "getClaim (the (bridgeState contractsUpdate' bridgeAddress)) ID = False"
    by (metis generateStateRootUpdate' option.collapse properSetupUpdate' properSetup_def verifyClaimProofE)

  ultimately

  show False
    by simp
qed

text \<open>If withdrawal succeeds, then the bridge is dead and 
      the user had the exact amount of tokens in the state in which the bridge died\<close>
theorem withdrawSufficientBalance:
  \<comment> \<open>Token deposit can accept token\<close>
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  \<comment> \<open>Withdraw succeded\<close>
  assumes withdraw:
    "callWithdrawWhileDead contractsLVS tokenDepositAddress msg block token amount proof = (Success, contractsW)"
  \<comment> \<open>Caller had sufficient balance\<close>
  shows "callBalanceOf contractsUpdate' token (sender msg) = (Success, amount)"
proof-
  have "verifyBalanceProof () token (sender msg) amount stateRoot proof"
    using callWithdrawWhileDeadVerifyBalanceProof[OF withdraw]
    using getLastValidStateLVS
    by (simp add: Let_def)
  then have "balanceOf (the (ERC20state contractsUpdate' token)) (sender msg) = amount"
    using assms
    using verifyBalanceProofE[of contractsUpdate' stateRoot]
    by auto
  then show ?thesis
    using assms
    unfolding callBalanceOf_def
    by (auto split: option.splits)
qed

end


context HashProofVerifier
begin

fun isTokenCancel where
  "isTokenCancel address token (CANCEL address' caller ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isTokenCancel address token _ = False"

definition tokenCancels where
  "tokenCancels address token steps = 
   filter (isTokenCancel address token) steps"

definition canceledTokenAmount where
  "canceledTokenAmount address token steps = 
   sum_list (map CANCEL_amount (tokenCancels address token steps))"

lemma canceledTokenAmountCancel [simp]:
  shows "canceledTokenAmount address token (CANCEL address caller ID token amount proof # steps) = 
         amount + canceledTokenAmount address token steps"
  unfolding canceledTokenAmount_def tokenCancels_def
  by auto

lemma canceledTokenAmountConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CANCEL address' caller' ID' token' amount' proof'"
  shows "canceledTokenAmount address token (step # steps) = canceledTokenAmount address token steps"
  using assms 
  unfolding canceledTokenAmount_def tokenCancels_def
  by (cases step, auto)

lemma canceledTokenAmountConsCancelOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "canceledTokenAmount address token (CANCEL address' caller' ID' token' amount' proof' # steps) = 
         canceledTokenAmount address token steps"
  using assms
  unfolding canceledTokenAmount_def tokenCancels_def
  by auto


lemma canceledTokenAmountBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
    shows "canceledTokenAmount tokenDepositAddress token steps = 0"
  using assms noCancelBeforeBridgeDead[OF assms]
  unfolding canceledTokenAmount_def tokenCancels_def
  by (metis filter_False isTokenCancel.elims(2) list.simps(8) sum_list.Nil)


definition nonClaimedBeforeDeathTokenDeposits where
  "nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore) 
            (tokenDeposits tokenDepositAddress token steps)"

definition nonClaimedBeforeDeathTokenDepositsAmount where
  "nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps))"

(* NOTE: only on the given token *)
definition isCanceledID where
  "isCanceledID tokenDepositAddress token ID steps \<longleftrightarrow> 
   (\<exists> caller amount proof. CANCEL tokenDepositAddress caller ID token amount proof \<in> set steps)"

definition nonCanceledNonClaimedBeforeDeathTokenDeposits where
  "nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore \<and>
                     \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) steps)
            (tokenDeposits tokenDepositAddress token steps)"

definition nonCanceledNonClaimedBeforeDeathTokenDepositsAmount where
  "nonCanceledNonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma nonClaimedTokenDepositsBeforeDeathConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeDeathTokenDeposits_def
  by (cases step, auto)

lemma nonClaimedBeforeDeathTokenDepositsAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms nonClaimedBeforeDeathTokenDepositsAmount_def)

lemma nonCanceledNonClaimedBeforeDeathTokenDepositsConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  assumes "\<nexists> caller' ID' amount' proof'. step = CANCEL tokenDepositAddress caller' ID' token amount' proof'"
  shows "nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonCanceledNonClaimedBeforeDeathTokenDeposits_def tokenDeposits_def
  by (smt (verit, ccfv_SIG) filter.simps(2) filter_cong isCanceledID_def isTokenDeposit.elims(2) list.set_intros(2) set_ConsD)


lemma nonCanceledNonClaimedBeforeDeathTokenDepositsAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  assumes "\<nexists> caller' ID' amount' proof'. step = CANCEL tokenDepositAddress caller' ID' token amount' proof'"
  shows "nonCanceledNonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonCanceledNonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms nonCanceledNonClaimedBeforeDeathTokenDepositsAmount_def)

definition tokenWithdrawals where
  "tokenWithdrawals address token steps = filter (\<lambda> step. case step of WITHDRAW address' caller token' amount proof \<Rightarrow> address = address' \<and> token = token' | _ \<Rightarrow> False) steps"

definition tokenWithdrawnAmount where
  "tokenWithdrawnAmount address token steps = 
   sum_list (map WITHDRAW_amount (tokenWithdrawals address token steps))"

lemma tokenWithdrawnAmoutConsOther [simp]:
  assumes "\<nexists> address' caller' token' amount' proof'. step = WITHDRAW address' caller' token' amount' proof'"
  shows "tokenWithdrawnAmount address token (step # steps) = tokenWithdrawnAmount address token steps"
  using assms 
  unfolding tokenWithdrawnAmount_def tokenWithdrawals_def
  by (cases step, auto)

end

context StrongHashProofVerifier
begin

lemma nonCanceledNonClaimedBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
    shows "nonCanceledNonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
           nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms noCancelBeforeBridgeDead[OF assms]
  unfolding nonCanceledNonClaimedBeforeDeathTokenDepositsAmount_def nonClaimedBeforeDeathTokenDepositsAmount_def
  unfolding nonCanceledNonClaimedBeforeDeathTokenDeposits_def nonClaimedBeforeDeathTokenDeposits_def isCanceledID_def
  by metis

end


(*
               [stepsInit]                  update                  [stepsNoUpdate]               stepDeath               stepsBD
   contractsInit  \<rightarrow>*   contractsLastUpdate'  \<rightarrow>  contractsLastUpdate       \<rightarrow>*     contractsDead'     \<rightarrow>    contractsDead   \<rightarrow>*  contractsBD
   properSetup

                  [stepsI]
   contractsInit      \<rightarrow>*       contractsI
   properSetup
   getDeposit=0
   lastStateB=0
*)


context InitUpdateBridgeNotDeadLastValidState
begin


lemma nonCanceledNonClaimedBeforeDeathTokenDepositsConsCancel:
  assumes "reachableFrom contractsLVS contractsCancel [CANCEL tokenDepositAddress caller ID token amount proof]"
  shows "\<exists> steps1 steps2.
           nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS = 
           steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2 \<and>
           nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsInit (CANCEL tokenDepositAddress caller ID token amount proof # stepsAllLVS) = 
           steps1 @ steps2"
proof-
  define CANCEL_step where "CANCEL_step = CANCEL tokenDepositAddress caller ID token amount proof"
  define DEPOSIT_step where "DEPOSIT_step = DEPOSIT tokenDepositAddress (sender (message caller 0)) ID token amount"
  define P where "P = (\<lambda>step.
         \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
         \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsAllLVS)"
  define P' where "P' = (\<lambda>step.
         \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
         \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) (CANCEL_step # stepsAllLVS))"
  define Q where "Q = (\<lambda> step. isTokenDeposit tokenDepositAddress token step)"
  define depositsAll where "depositsAll = tokenDeposits tokenDepositAddress token stepsAllLVS"
  define non where "non = nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS"
  define nonCancel where "nonCancel = nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsInit (CANCEL_step # stepsAllLVS)"

  obtain block "proof" where 
    cancel: "callCancelDepositWhileDead contractsLVS tokenDepositAddress (message caller 0) block ID token amount proof =
    (Success, contractsCancel)"
    using assms
    by (metis executeStep.simps(4) reachableFromSingleton)

  then have "DEPOSIT_step \<in> set stepsAllLVS"
    unfolding DEPOSIT_step_def
    by  (rule InitLVS.cancelDepositOnlyAfterDeposit)
  then obtain steps1 steps2 where steps: "stepsAllLVS = steps1 @ [DEPOSIT_step] @ steps2"
    by (metis append_Cons append_self_conv2 split_list)
  then have "DEPOSIT_step \<in> set (tokenDeposits tokenDepositAddress token stepsAllLVS)"
    unfolding tokenDeposits_def DEPOSIT_step_def
    by auto

  moreover

  have "\<nexists> caller' token' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
    using cancel
    by (simp add: cancelDepositWhileDeadNoClaim)

  moreover

  have noCancel: "\<nexists> caller' token' amount' proof'. 
          CANCEL tokenDepositAddress caller' ID token' amount' proof' \<in> set stepsAllLVS"
    using CANCELNoDoubleCons assms reachableFromSingleton reachableFrom_step reachableFromInitLVS
    by meson

  ultimately

  have "DEPOSIT_step \<in> set non"
    unfolding non_def
    unfolding nonCanceledNonClaimedBeforeDeathTokenDeposits_def DEPOSIT_step_def isClaimedID_def isCanceledID_def
    by auto
  have *: "\<forall> step \<in> set (steps1 @ steps2). (\<forall> caller' amount' ID'. step = DEPOSIT tokenDepositAddress caller' ID' token amount' \<longrightarrow> ID' \<noteq> ID)"
    using steps DEPOSITNoDouble' InitLVS.reachableFromInitI 
    unfolding DEPOSIT_step_def
    by blast
  then have "DEPOSIT_step \<notin> set (steps1 @ steps2)"
    unfolding DEPOSIT_step_def
    by auto

  have depositsAll: "depositsAll = (filter Q steps1) @ [DEPOSIT_step] @ (filter Q steps2)"
    using steps
    unfolding depositsAll_def tokenDeposits_def Q_def DEPOSIT_step_def
    by auto

  define c1 where "c1 = filter P' (filter Q steps1)" 
  define c2 where "c2 = filter P' (filter Q steps2)" 

  have "\<not> P' DEPOSIT_step"
    unfolding P'_def DEPOSIT_step_def CANCEL_step_def
    by (auto simp add: isCanceledID_def)
  then have nonCancel:
    "nonCancel = c1 @ c2"
    using depositsAll \<open>\<not> P' DEPOSIT_step\<close>
    unfolding nonCancel_def c1_def c2_def depositsAll_def nonCanceledNonClaimedBeforeDeathTokenDeposits_def P'_def
    by (simp add: CANCEL_step_def)

  have "DEPOSIT_step \<notin> set (c1 @ c2)"
    using \<open>DEPOSIT_step \<notin> set (steps1 @ steps2)\<close>
    unfolding c1_def c2_def
    by auto

  have "\<And> steps. set steps \<subseteq> set steps1 \<union> set steps2 \<Longrightarrow> filter P (filter Q steps) = filter P' (filter Q steps)"
  proof (rule filter_cong)
    fix steps step
    assume "set steps \<subseteq> set steps1 \<union> set steps2" "step \<in> set (filter Q steps)"
    then obtain caller' ID' amount' where "step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
      unfolding Q_def
      by (smt (verit, best) isTokenDeposit.elims(2) mem_Collect_eq set_filter)
    then show "P step \<longleftrightarrow> P' step"
      using * \<open>set steps \<subseteq> set steps1 \<union> set steps2\<close> \<open>step \<in> set (filter Q steps)\<close>
      unfolding P_def P'_def CANCEL_step_def
      by (auto simp add: isCanceledID_def)
  qed simp
  then have "non = c1 @ filter P [DEPOSIT_step] @ c2"
    unfolding non_def nonCanceledNonClaimedBeforeDeathTokenDeposits_def P_def c1_def c2_def
    using depositsAll depositsAll_def
    by auto
  then have non: "non = c1 @ [DEPOSIT_step] @ c2"
    using \<open>DEPOSIT_step \<in> set non\<close> \<open>DEPOSIT_step \<notin> set (c1 @ c2)\<close>
    by (metis append.assoc append.right_neutral filter.simps(1) filter.simps(2))

  show ?thesis
    using nonCancel non
    using CANCEL_step_def DEPOSIT_step_def nonCancel_def non_def 
    by auto
qed

lemma nonCanceledNonClaimedBeforeDeathTokenDepositsAmountCancel:
  assumes "reachableFrom contractsLVS contractsCancel [CANCEL tokenDepositAddress caller ID token amount proof]"
  shows "nonCanceledNonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit (CANCEL tokenDepositAddress caller ID token amount proof # stepsAllLVS) =
         nonCanceledNonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS - amount"
        "amount \<le> nonCanceledNonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS"
  using nonCanceledNonClaimedBeforeDeathTokenDepositsConsCancel[OF assms]
  unfolding nonCanceledNonClaimedBeforeDeathTokenDepositsAmount_def
  by auto

end


(*
               [stepsInit]                  update                  [stepsNoUpdate]               stepDeath               stepsBD
   contractsInit  \<rightarrow>*   contractsLastUpdate'  \<rightarrow>  contractsLastUpdate       \<rightarrow>*     contractsDead'     \<rightarrow>    contractsDead   \<rightarrow>*  contractsBD
   properSetup
*)
locale BridgeDead =
  InitUpdate where contractsUpdate=contractsLastUpdate and contractsUpdate'=contractsLastUpdate' and blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate +
  LastUpdate where contractsLU=contractsDead' for contractsDead'::Contracts + 
  fixes stepDeath :: Step
  fixes contractsDead :: Contracts
  fixes contractsBD :: Contracts
  fixes stepsBD :: "Step list"
  \<comment> \<open>Bridge died\<close>
  assumes notBridgeDead' [simp]:
    "\<not> bridgeDead contractsDead' tokenDepositAddress"
  assumes deathStep [simp]: 
    "reachableFrom contractsDead' contractsDead [stepDeath]"
  assumes bridgeDead [simp]:
    "bridgeDead contractsDead tokenDepositAddress"
  \<comment> \<open>Current contracts are reached\<close>
  assumes reachableFromContractsBD [simp]:
    "reachableFrom contractsDead contractsBD stepsBD"
 (* NOTE: additional assumptions *)
  \<comment> \<open>state root hash is not zero\<close>
  assumes stateRootNonZero:
    "stateRoot \<noteq> 0"
begin
definition stepsAllBD where
  "stepsAllBD = stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step] @ stepsInit"

definition stepsBeforeDeath where
  "stepsBeforeDeath = stepsNoUpdate @ [UPDATE_step] @ stepsInit"

lemma notBridgeDeadContractsLastUpdate' [simp]:
  shows "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
  using notBridgeDead' reachableFromBridgeDead reachableFromLastUpdate'LU 
  by blast

lemma bridgeDeadContractsBD [simp]:
  shows "bridgeDead contractsBD tokenDepositAddress"
  using reachableFromBridgeDead bridgeDead reachableFromContractsBD
  by blast

lemma stepDeathNoUpdate [simp]:
  shows "\<nexists> address stateRoot. stepDeath = UPDATE address stateRoot"
  by (metis bridgeDead callUpdateITokenDeposit deathStep executeStep.simps(3) notBridgeDead' reachableFromSingleton)
 
lemma getLastStateBLastUpdate [simp]:
  shows "getLastStateB contractsLastUpdate bridgeAddress = stateRoot"
  using callUpdateLastState update 
  by (metis InitUpdate.stateOracleAddressBI stateOracleAddressBI)

lemma deadStateContractsDead [simp]: 
  shows "deadState (the (tokenDepositState contractsDead tokenDepositAddress)) = stateRoot"
  by (metis BridgeDiesDeadState bridgeDead deathStep getLastStateTDLU notBridgeDead' reachableFromSingleton)

lemma deadStateContractsBD [simp]: 
  shows "deadState (the (tokenDepositState contractsBD tokenDepositAddress)) = stateRoot"
  using stateRootNonZero reachableFromContractsBD deadStateContractsDead reachableFromDeadState
  by blast

end

sublocale BridgeDead \<subseteq> InitDead': Init where contractsI=contractsDead' and stepsInit=stepsBeforeDeath
proof
  show "reachableFrom contractsInit contractsDead' stepsBeforeDeath"
    using reachableFromInitI reachableFromLastUpdateLU reachableFromTrans reachableFromUpdate'Update stepsBeforeDeath_def
    by presburger
qed

sublocale BridgeDead \<subseteq> InitDead: Init where contractsI=contractsDead and stepsInit="[stepDeath] @ stepsBeforeDeath"
proof
  show "reachableFrom contractsInit contractsDead  ([stepDeath] @ stepsBeforeDeath)"
    using InitDead'.reachableFromInitI deathStep reachableFromTrans 
    by blast
qed

sublocale BridgeDead \<subseteq> InitBD: Init where contractsI=contractsBD and stepsInit=stepsAllBD
proof
  show "reachableFrom contractsInit contractsBD stepsAllBD"
    unfolding stepsAllBD_def
    by (metis InitDead.reachableFromInitI reachableFromContractsBD reachableFromTrans stepsBeforeDeath_def)
qed

sublocale BridgeDead \<subseteq> LastUpdateBridgeNotDead where contractsLU=contractsDead'
proof
  show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using notBridgeDeadContractsLastUpdate' by blast
qed

sublocale BridgeDead \<subseteq> LVSDead': InitUpdateBridgeNotDeadLastValidState where
  contractsUpdate=contractsLastUpdate and 
  contractsUpdate'=contractsLastUpdate' and 
  blockUpdate=blockLastUpdate and 
  blockNumUpdate=blockNumLastUpdate and 
  contractsLVS=contractsDead' and 
  stepsLVS=stepsNoUpdate
proof
  show "getLastValidStateTD contractsDead' tokenDepositAddress = (Success, stateRoot)"
    using callLastStateLU lastValidState_def notBridgeDead' properSetupLU properSetup_stateOracleAddress 
    by presburger
next
  show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using notBridgeDeadContractsLastUpdate'
    by simp
qed simp_all

sublocale BridgeDead \<subseteq> LVSBD: InitUpdateBridgeNotDeadLastValidState where 
  contractsUpdate=contractsLastUpdate and 
  contractsUpdate'=contractsLastUpdate' and 
  blockUpdate=blockLastUpdate and 
  blockNumUpdate=blockNumLastUpdate and 
  contractsLVS=contractsBD and 
  stepsLVS="stepsBD @ [stepDeath] @ stepsNoUpdate"
proof
  show "reachableFrom contractsLastUpdate contractsBD (stepsBD @ [stepDeath] @ stepsNoUpdate)"
    using deathStep reachableFromContractsBD reachableFromTrans reachableFromLastUpdateLU
    by blast
next
  show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using notBridgeDeadContractsLastUpdate'
    by blast
next
  show "getLastValidStateTD contractsBD tokenDepositAddress = (Success, stateRoot)"
    using bridgeDeadContractsBD deadStateContractsBD lastValidState_def by presburger
qed

context BridgeDead
begin

lemma canceledAmountInvariant:
  shows
  "nonCanceledNonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit  ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) + 
   canceledTokenAmount tokenDepositAddress token ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) = 
   nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit)" (is "?NCC (stepsBD @ [stepDeath]) + ?C (stepsBD @ [stepDeath]) = ?NC (stepsBD @ [stepDeath])")
  using reachableFromContractsBD BridgeDead_axioms
proof (induction contractsDead contractsBD stepsBD rule: reachableFrom.induct)
  case (reachableFrom_base contractsBD)
  then interpret BD: BridgeDead where contractsBD=contractsBD and stepsBD="[]" and contractsDead=contractsBD
    .
  have *: "?NCC [] + ?C [] = ?NC []"
    using LVSDead'.reachableFromInitLVS canceledTokenAmountBridgeNotDead nonCanceledNonClaimedBridgeNotDead notBridgeDead'
    unfolding LVSDead'.stepsAllLVS_def
    by auto

  show ?case
  proof (cases stepDeath)
    case (DEPOSIT address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case True
      have "bridgeDead contractsBD tokenDepositAddress"
        using  BD.bridgeDead DEPOSIT
        by auto
      then show ?thesis
        using DEPOSIT True callDepositNotBridgeDead'
        using reachableFromSingleton[OF BD.deathStep] 
        by (metis executeStep.simps(1))
    next
      case False
      then show ?thesis
        using * DEPOSIT 
        by force
    qed
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using *
      by simp
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using *
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using *
      by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case False
      then show ?thesis
        using * CANCEL
        by (cases "address' = tokenDepositAddress") auto
    next
      case True
      have "?NC [stepDeath] = ?NC []"
        using CANCEL
        by auto
      moreover
      have "?NCC [stepDeath] = ?NCC [] - amount' \<and> amount' \<le> ?NCC []"
        using LVSDead'.nonCanceledNonClaimedBeforeDeathTokenDepositsAmountCancel
        using BD.deathStep CANCEL LVSDead'.stepsAllLVS_def True by auto
      moreover
      have "?C [stepDeath] = ?C [] + amount'"
        by (simp add: CANCEL True)
      ultimately
      show ?thesis
        using *
        by simp
    qed
  qed
next
  case (reachableFrom_step steps contractsBD contractsDead contractsBD' blockNum block step)

  interpret BD: BridgeDead where contractsBD=contractsBD' and stepsBD=steps and contractsDead=contractsDead
  proof
    show "\<not> bridgeDead contractsDead' tokenDepositAddress"
      using notBridgeDead' by blast
  next
    show "reachableFrom contractsDead contractsBD' steps"
      using reachableFrom_step.hyps
      by simp
  next
    show "reachableFrom contractsDead' contractsDead [stepDeath]"
      by (meson BridgeDead.deathStep reachableFrom_step.prems)
  next
    show "bridgeDead contractsDead tokenDepositAddress"
      by (meson BridgeDead.bridgeDead reachableFrom_step.prems)
  next
    show "stateRoot \<noteq> 0"
      using stateRootNonZero
      by simp
  qed

  have *: "?NCC (steps @ [stepDeath]) + ?C (steps @ [stepDeath]) = ?NC (steps @ [stepDeath])"
    using reachableFrom_step.IH[OF BD.BridgeDead_axioms]
    by simp

  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case True
      have "bridgeDead contractsBD' tokenDepositAddress"
        using reachableFrom_step.hyps BD.bridgeDead DEPOSIT
        by auto
      then show ?thesis
        using DEPOSIT reachableFrom_step.hyps True
        by (metis callDepositFailsInDeadState executeStep.simps(1) fst_conv)
    next
      case False
      then show ?thesis
        using * DEPOSIT 
        by force
    qed
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using *
      by simp
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using *
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using *
      by simp
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case False
      then show ?thesis
        using * CANCEL
        by auto
    next
      case True
      have "?NC (step # (steps @ [stepDeath])) = ?NC (steps @ [stepDeath])"
        using CANCEL
        by auto
      moreover
      have "?NCC (step # steps @ [stepDeath]) = ?NCC (steps @ [stepDeath]) - amount' \<and> amount' \<le> ?NCC (steps @ [stepDeath])"
        by (metis BD.LVSBD.nonCanceledNonClaimedBeforeDeathTokenDepositsAmountCancel(1) BD.LVSBD.nonCanceledNonClaimedBeforeDeathTokenDepositsAmountCancel(2) BD.LVSBD.stepsAllLVS_def CANCEL Cons_eq_append_conv True append_eq_appendI reachableFrom.reachableFrom_step reachableFrom_base reachableFrom_step.hyps(2))
      moreover
      have "?C (step # steps @ [stepDeath]) = ?C (steps @ [stepDeath]) + amount'"
        by (simp add: CANCEL True)
      ultimately
      show ?thesis
        using *
        by simp
    qed
  qed
qed

end

(**************************************************************************************************)
section \<open>Liveness\<close>
(**************************************************************************************************)

context LastUpdate
begin

(*
               deposit                [steps]                      update                        [steps']                   claim?        
   contracts      \<rightarrow>    contractsD       \<rightarrow>*   contractsLastUpdate'     \<rightarrow>   contractsLastUpdate   \<rightarrow>*      contractsU'      \<rightarrow>    contractsC?
  properSetup                                     \<not> bridgeDead                                   noUpdates   \<not> getClaim ID
  properToken
*)

text \<open>After a successful deposit and a state update, 
      if a bridge is still alive a claim can be made \<close>
theorem claimPossibleAfterDepositAndUpdate:
  \<comment> \<open>contracts are setup properly in the initial state, for the given token\<close>
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  assumes "properToken contracts tokenDepositAddress bridgeAddress token"

  \<comment> \<open>A deposit is successfully made\<close>
  assumes "callDeposit contracts tokenDepositAddress block msg ID token amount = (Success, contractsD)"
  \<comment> \<open>after a deposit a new state is reached\<close>
  assumes "reachableFrom contractsD contractsLastUpdate' steps"
  \<comment> \<open>the bridge is not dead in the reached state\<close>
  assumes "\<not> bridgeDead  contractsLastUpdate' tokenDepositAddress"

  \<comment> \<open>there was no previous claim\<close>
  assumes "getClaim (the (bridgeState contractsLU bridgeAddress)) ID = False"

  \<comment> \<open>The same person who made the deposit can make the claim\<close>
  assumes "sender msg' = sender msg"

  \<comment> \<open>A claim can be made with the state root and the proof obtained from the state that
      was used for the last update\<close>
  shows "let proof = generateDepositProof contractsLastUpdate' ID
          in \<exists> contractsC. callClaim contractsLU bridgeAddress msg' ID token amount proof = (Success, contractsC)"
proof-
  define "proof" where "proof = generateDepositProof contractsLastUpdate' ID"
  define stateBridge where "stateBridge = the (bridgeState contractsLU bridgeAddress)"

  have *: "verifyDepositProof () tokenDepositAddress ID (hash3 (sender msg) token amount) stateRoot proof = True"
    unfolding proof_def
  proof (rule verifyDepositProofI)
    show "getDeposit (the (tokenDepositState contractsLastUpdate' tokenDepositAddress)) ID = hash3 (sender msg) token amount"
    proof (rule reachableFromGetDepositBridgeNotDead)
      show "reachableFrom contractsD contractsLastUpdate' steps" 
        by fact
    next
      show "hash3 (sender msg) token amount \<noteq> 0"
        using hash3_nonzero
        by simp
    next
      show "getDeposit (the (tokenDepositState contractsD tokenDepositAddress)) ID = hash3 (sender msg) token amount"
        using callDepositWritesHash assms
        by blast
    next
      show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
        using assms
        by simp
    qed
  qed simp_all
  then have "verifyDepositProof () (BridgeState.deposit stateBridge) ID (hash3 (sender msg') token amount)
     (getLastStateB contractsLU bridgeAddress) proof"
    using \<open>sender msg' = sender msg\<close> depositLU getLastStateBLU stateBridge_def
    by argo

  then have "fst (callClaim contractsLU bridgeAddress msg' ID token amount proof) = Success"
    by (smt (verit, ccfv_threshold) HashProofVerifier.callClaimI HashProofVerifier_axioms assms(2) assms(3) assms(4) assms(6) callDepositProperToken option.collapse properSetupLU properSetup_def properTokenReachable properToken_def reachableFromLastUpdate'LU stateBridge_def)
  then show ?thesis 
    unfolding Let_def proof_def
    by (metis eq_fst_iff)
qed

end

context StrongHashProofVerifier
begin

lemma callLastUpdateTimeI:
  assumes "stateOracleState contracts (stateOracleAddressTD contracts address) \<noteq> None"
  shows "fst (callLastUpdateTime contracts (stateOracleAddressTD contracts address)) = Success"
  using assms
  unfolding callLastUpdateTime_def
  by (simp split: option.splits)

lemma lastValidStateI:
  assumes "stateOracleState contracts (stateOracleAddressTD contracts address) \<noteq> None"
  shows "fst (getLastValidStateTD contracts address) = Success"
  using assms callLastStateI
  unfolding lastValidState_def Let_def
  by auto

lemma getDeadStatusI:
  assumes "stateOracleState contracts (stateOracleAddressTD contracts address) \<noteq> None"
  shows "fst (getDeadStatus contracts (the (tokenDepositState contracts address)) block) = Success"
  using assms callLastStateI[OF assms(1)]  callLastUpdateTimeI[OF assms(1)]
  unfolding getDeadStatus_def 
  by (auto split: option.splits prod.splits if_split_asm)

lemma callVerifyClaimProofI:
  assumes "proofVerifierState contracts proofVerifierAddress \<noteq> None"
  assumes "verifyClaimProof () bridgeAddress ID stateRoot proof"
  shows "callVerifyClaimProof contracts proofVerifierAddress bridgeAddress ID stateRoot proof = Success"
  using assms
  unfolding callVerifyClaimProof_def
  by (auto split: option.splits prod.splits)


lemma callCancelDepositWhileDeadI:
  assumes "tokenDepositState contracts address \<noteq> None"
  assumes "stateOracleState contracts (stateOracleAddressTD contracts address) \<noteq> None"
  assumes "proofVerifierState contracts (TokenDepositState.proofVerifier (the (tokenDepositState contracts address))) \<noteq> None"
  assumes "ERC20state contracts token \<noteq> None"
  assumes "getDeposit (the (tokenDepositState contracts address)) ID = hash3 (sender msg) token amount"
  assumes "fst (snd (getDeadStatus contracts (the (tokenDepositState contracts address)) block)) = True"
  assumes "bridgeDead contracts address \<longrightarrow> deadState (the (tokenDepositState contracts address)) = stateRoot"
  assumes "\<not> bridgeDead contracts address \<longrightarrow> lastState (the (stateOracleState contracts (stateOracleAddressTD contracts address))) = stateRoot"
  assumes "verifyClaimProof () (TokenDepositState.bridge (the (tokenDepositState contracts address))) ID stateRoot proof"
  assumes "amount \<le> balanceOf (the (ERC20state contracts token)) address"
  assumes "sender msg \<noteq> address"
  shows "fst (callCancelDepositWhileDead contracts address msg block ID token amount proof) = Success"
proof-
  define stateTD where "stateTD = the (tokenDepositState contracts address)"

  have "lastValidState contracts stateTD = (Success, stateRoot)"
    using assms lastValidStateI[OF assms(2)]
    unfolding stateTD_def
    by (auto simp add: lastValidState_def callLastState_def)
  moreover
  have "callVerifyClaimProof contracts (TokenDepositState.proofVerifier stateTD) (bridge stateTD) ID stateRoot proof =
         Success"
    unfolding stateTD_def
    using callVerifyClaimProofI[OF assms(3)] assms
    by presburger
  moreover
  have "fst (callSafeTransferFrom contracts token address (sender msg) amount) = Success"
    using assms callSafeTransferFromI
    by (metis option.collapse)
  ultimately
  show ?thesis
    using assms getDeadStatusI[OF assms(2), of block] 
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def stateTD_def
    by (auto split: option.splits prod.splits if_split_asm)
qed

end

context StrongHashProofVerifier
begin

lemma nonCanceledDepositGetDeposit:
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
  assumes "\<not> isCanceledID tokenDepositAddress token ID steps"
  assumes "reachableFrom contracts contracts' steps"
  shows "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID =
            hash3 caller token amount"
proof-
  have *: "\<nexists>caller amount proof token'. CANCEL tokenDepositAddress caller ID token' amount proof \<in> set steps"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain caller' amount' proof' token' where "CANCEL tokenDepositAddress caller' ID token' amount' proof' \<in> set steps"
      by auto
    moreover
    have "token = token'"
      using onlyDepositorCanCancelSteps(2)
      using assms(1) assms(3) calculation by blast
    ultimately show False
      using \<open>\<not> isCanceledID tokenDepositAddress token ID steps\<close>
      unfolding isCanceledID_def
      by auto
  qed
  obtain steps1 steps2 where
  "steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2"
    using assms
    using reachableFromStepInSteps by blast
  then obtain contractsD where 
    "reachableFrom contractsD contracts' steps1"
    "getDeposit (the (tokenDepositState contractsD tokenDepositAddress)) ID = 
     hash3 caller token amount"
    by (smt (verit, ccfv_threshold) DEPOSITNoDouble' HashProofVerifier.executeStep.simps(1) HashProofVerifier_axioms Un_iff append_Cons append_Cons_eq_iff assms(1) assms(3) callDepositWritesHash reachableFromStepInSteps self_append_conv2 senderMessage set_append)
  then show ?thesis
    using hash3_nonzero[of caller token amount] *
    by (simp add: \<open>steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2\<close> reachableFromGetDepositBridgeNoCancel)
qed

end

context BridgeDead
begin

lemma onlyDepositorCanClaimSteps:
  assumes "reachableFrom contracts contracts' steps"
  assumes "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set steps"
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
  shows "caller' = caller" "token' = token" "amount' = amount"
  sorry

theorem cancelPossible:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set stepsAllBD"
  assumes "\<not> isClaimedID bridgeAddress token ID stepsInit"
  assumes "\<not> isCanceledID tokenDepositAddress token ID stepsAllBD"
  assumes "caller \<noteq> tokenDepositAddress"
  shows "\<exists> contractsCancel. reachableFrom contractsBD contractsCancel [CANCEL tokenDepositAddress caller ID token amount (generateClaimProof contractsLastUpdate' ID)]"
proof-
  obtain block where "fst (callCancelDepositWhileDead contractsBD tokenDepositAddress (message caller 0) block ID token amount (generateClaimProof contractsLastUpdate' ID)) = Success"
  proof-
    fix block
    have "fst (callCancelDepositWhileDead contractsBD tokenDepositAddress (message caller 0)
              block ID token amount (generateClaimProof contractsLastUpdate' ID)) =
        Success"
    proof (rule callCancelDepositWhileDeadI)
      show "tokenDepositState contractsBD tokenDepositAddress \<noteq> None"
        by simp
    next
      show "stateOracleState contractsBD (stateOracleAddressTD contractsBD tokenDepositAddress) \<noteq> None"
        by (metis LVSBD.InitLVS.properSetupI properSetup_def)
    next
      show "proofVerifierState contractsBD (TokenDepositState.proofVerifier (the (tokenDepositState contractsBD tokenDepositAddress))) \<noteq> None"
        by (metis LVSBD.InitLVS.properSetupI properSetup_def)
    next
      show "ERC20state contractsBD token \<noteq> None"
        using LVSBD.InitLVS.ERC20stateINonNone assms(1) by blast
    next
      show "sender (message caller 0) \<noteq> tokenDepositAddress"
        using assms
        by simp
    next
      show "fst (snd (getDeadStatus contractsBD
                (the (tokenDepositState contractsBD tokenDepositAddress)) block)) = True"
        using bridgeDeadContractsBD
        by (simp add: getDeadStatus_def)
    next
      show "bridgeDead contractsBD tokenDepositAddress \<longrightarrow>
            deadState (the (tokenDepositState contractsBD tokenDepositAddress)) = stateRoot"
        using deadStateContractsBD by blast
    next
      show "\<not> bridgeDead contractsBD tokenDepositAddress \<longrightarrow>
            getLastStateTD contractsBD tokenDepositAddress = stateRoot"
        using bridgeDeadContractsBD by blast
    next
      have "getClaim (the (bridgeState contractsLastUpdate' bridgeAddress)) ID = False"
      proof-
        have "\<nexists>caller token amount proof.
              CLAIM bridgeAddress caller ID token amount proof \<in> set stepsInit"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain caller' token' amount' proof' where claim: "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
            by auto
          then have "token' = token"
            using \<open>DEPOSIT tokenDepositAddress caller ID token amount \<in> set stepsAllBD\<close>
            using onlyDepositorCanClaimSteps(2)[OF InitBD.reachableFromInitI]
            unfolding stepsAllBD_def
            by (metis Un_iff set_append)
         then show False
            using \<open>\<not> isClaimedID bridgeAddress token ID stepsInit\<close> claim
            unfolding isClaimedID_def
            by auto
        qed
        moreover
        have "getClaim (the (bridgeState contractsInit bridgeAddress)) ID = False"
          using claimsEmpty by blast
        ultimately show ?thesis
          using reachableFromGetClaimNoClaim[OF reachableFromInitI]
          by simp
      qed
      then show "verifyClaimProof () (bridge (the (tokenDepositState contractsBD tokenDepositAddress))) ID
            stateRoot (generateClaimProof contractsLastUpdate' ID)"
        using verifyClaimProofI
        by (metis bridgeStateINotNone generateStateRootUpdate' option.collapse)
    next
      show "amount \<le> balanceOf (the (ERC20state contractsBD token)) tokenDepositAddress"
        using canceledAmountInvariant
        sorry
    next
      show "getDeposit (the (tokenDepositState contractsBD tokenDepositAddress)) ID =
            hash3 (sender (message caller 0)) token amount"
        using  nonCanceledDepositGetDeposit[OF 
             \<open>DEPOSIT tokenDepositAddress caller ID token amount \<in> set stepsAllBD\<close>
             \<open>\<not> isCanceledID tokenDepositAddress token ID stepsAllBD\<close>
             InitBD.reachableFromInitI]
        by simp
    qed
    then show thesis
      using that
      by simp
  qed
  then show ?thesis
    by (metis executeStep.simps(4) prod.collapse reachableFrom_base reachableFrom_step)
qed

text \<open>If the user had some amount of tokens in the state in which the bridge died, 
      he can withdraw that amount\<close>
theorem sufficientBalanceCanWithdraw:
  \<comment> \<open>Token deposit can accept token\<close>
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  \<comment> \<open>Caller had sufficient balance\<close>
  assumes "callBalanceOf contractsLastUpdate' token (sender msg) = (Success, amount)"
  \<comment> \<open>Caller has not yet withdrawn his balance\<close>
  assumes notWithdrawn: 
    "getTokenWithdrawn (the (tokenDepositState contractsBD tokenDepositAddress)) (hash2 (sender msg) token) = False"
  \<comment> \<open>Sender is not the bridge itself\<close>
  assumes "tokenDepositAddress \<noteq> sender msg"
  \<comment> \<open>Withdraw succedes\<close>
  shows "fst (callWithdrawWhileDead contractsBD tokenDepositAddress msg block token amount 
                                    (generateBalanceProof contractsLastUpdate' token (sender msg) amount)) = Success"
proof-
  define stateTokenDeposit where "stateTokenDeposit = the (tokenDepositState contractsBD tokenDepositAddress)"
  define stateTokenDeposit' where "stateTokenDeposit' = snd (snd (getDeadStatus contractsBD stateTokenDeposit block))"
  define Proof where "Proof =  generateBalanceProof contractsLastUpdate' token (sender msg) amount"

  have "verifyBalanceProof () token (sender msg) amount stateRoot Proof = True"
    using verifyBalanceProofI \<open>callBalanceOf contractsLastUpdate' token (sender msg) = (Success, amount)\<close>
    unfolding Proof_def
    by (metis callBalanceOf callBalanceOfERC20state generateStateRootUpdate' option.collapse)

  moreover

  have "proofVerifierState contractsBD (TokenDepositState.proofVerifier stateTokenDeposit) \<noteq> None"
    by (metis LVSBD.InitLVS.properSetupI properSetup_def stateTokenDeposit_def)

  moreover

  have "deadState stateTokenDeposit' = stateRoot"
    by (metis bridgeDeadContractsBD deadStateContractsBD getDeadStatusInDeadState prod.exhaust_sel stateTokenDeposit'_def stateTokenDeposit_def)

  ultimately
  
  have "callVerifyBalanceProof contractsBD (TokenDepositState.proofVerifier stateTokenDeposit) token (sender msg) amount
        (deadState stateTokenDeposit') Proof = Success"
    unfolding callVerifyBalanceProof_def
    by (auto split: option.splits)

  moreover

  have "getDeadStatus contractsBD stateTokenDeposit block = (Success, True, stateTokenDeposit')"
    by (metis deadStateContractsBD getDeadStatus_def split_pairs stateRootNonZero stateTokenDeposit'_def stateTokenDeposit_def)

  moreover

  have "fst (callSafeTransferFrom contractsBD token tokenDepositAddress (sender msg) amount) = Success"
  proof (rule callSafeTransferFromI)
    show "ERC20state contractsBD token = Some (the (ERC20state contractsBD token))"
      using \<open>properToken contractsInit tokenDepositAddress bridgeAddress token\<close>
      by simp
  next
    show "tokenDepositAddress \<noteq> sender msg"
      by fact
  next
    show "amount \<le> balanceOf (the (ERC20state contractsBD token)) tokenDepositAddress"
      sorry
  qed

  ultimately

  show ?thesis
    using notWithdrawn
    unfolding stateTokenDeposit'_def stateTokenDeposit_def Proof_def
    unfolding callWithdrawWhileDead_def withdrawWhileDead_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
qed

end
end
