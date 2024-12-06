theory Properties
  imports Reachability MoreList
begin

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
proof (rule ccontr)
  obtain contracts'' block where *:
   "reachableFrom contracts contracts'' steps"
   "callDeposit contracts'' tokenDepositAddress block (message caller amount) ID token amount = (Success, contracts')"
    using reachableFromCons'[OF assms(1)]
    by auto

  moreover

  assume "\<not> ?thesis"
  then obtain token' caller' amount' where **: "DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps"
    by auto
  obtain c1 c2 steps1 steps2 block' where ***:
    "steps = steps1 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps2"
    "reachableFrom contracts c1 steps2" "reachableFrom c2 contracts'' steps1"
    "callDeposit c1 tokenDepositAddress block' (message caller' amount') ID token' amount' = (Success, c2)"
    using reachableFromStepInSteps[OF *(1) **]
    by auto metis

  have "fst (callDeposit contracts'' tokenDepositAddress block (message caller amount) ID token amount) \<noteq> Success"
  proof (rule callDepositNoDouble)
    show "callDeposit c1 tokenDepositAddress block' (message caller' amount') ID token' amount' = (Success, c2)"
      by fact
  next
    show "reachableFrom c2 contracts'' steps1"
      by fact
  qed

  ultimately
  show False
    by simp
qed


lemma DEPOSITNoDouble:
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps3"
  shows False
proof-
  obtain contracts'' where *: 
    "reachableFrom contracts'' contracts' steps1"
    "reachableFrom contracts contracts'' (DEPOSIT tokenDepositAddress caller ID token amount # (steps2 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps3))"
    using assms(1-2) reachableFromAppend[of contracts contracts' steps1]
    by auto
 
  have "\<nexists> token'' caller'' amount''. DEPOSIT tokenDepositAddress caller'' ID token'' amount'' \<in> set (steps2 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps3)"
    using DEPOSITNoDoubleCons[OF *(2)] assms
    by metis
  then show False
    by auto
qed

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

end

(* ------------------------------------------------------------------------------------ *)

(*
                         update                    [stepsNoUpdate]             
   contractsLastUpdate'    \<rightarrow>   contractsLastUpdate      \<rightarrow>*    contractsLU
   properSetup                      noUpdates                  
*)
locale LastUpdate = StrongHashProofVerifier + 
  fixes contractsLastUpdate' :: Contracts
  fixes contractsLastUpdate :: Contracts
  fixes contractsLU :: Contracts
  fixes stepsNoUpdate :: "Step list"
  fixes blockLU :: Block
  fixes blockNumLU :: uint256
  fixes stateRoot :: bytes32
  fixes tokenDepositAddress :: address
  fixes bridgeAddress :: address

  \<comment> \<open>starting from a properly configured state\<close>
  assumes properSetupLastUpdate':
   "properSetup contractsLastUpdate' tokenDepositAddress bridgeAddress"
  \<comment> \<open>the last update that happened\<close>
  assumes lastUpdate:
    "let stateOracleAddress = stateOracleAddressB contractsLastUpdate' bridgeAddress
      in callUpdate contractsLastUpdate' stateOracleAddress blockLU blockNumLU stateRoot = (Success, contractsLastUpdate)"
  \<comment> \<open>there were no updates since then\<close>
  assumes reachableFromLastUpdateLU: 
    "reachableFrom contractsLastUpdate contractsLU stepsNoUpdate"
  assumes noUpdate:
    "let stateOracleAddress = stateOracleAddressB contractsLastUpdate bridgeAddress
      in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set stepsNoUpdate"
begin

definition UPDATE_step where
  "UPDATE_step = UPDATE (stateOracleAddressB contractsLastUpdate' bridgeAddress) stateRoot"

lemma reachableFromLastUpdate'LastUpdate [simp]:
  shows "reachableFrom contractsLastUpdate' contractsLastUpdate [UPDATE_step]"
proof-
  have "executeStep contractsLastUpdate' blockNumLU blockLU (UPDATE_step) = (Success, contractsLastUpdate)"
    using lastUpdate
    unfolding UPDATE_step_def
    by simp
  then show ?thesis
    using reachableFrom_base reachableFrom_step by blast
qed

lemma reachableFromLastUpdate'LU [simp]:
  shows "reachableFrom contractsLastUpdate' contractsLU (stepsNoUpdate @ [UPDATE_step])"
  using reachableFromTrans[OF reachableFromLastUpdateLU reachableFromLastUpdate'LastUpdate]
  by simp

lemma properSetupLastUpdate [simp]:
  shows "properSetup contractsLastUpdate tokenDepositAddress bridgeAddress"
  using callUpdateProperSetup lastUpdate properSetupLastUpdate' 
  by presburger

lemma properSetupLU [simp]:
  shows "properSetup contractsLU tokenDepositAddress bridgeAddress"
  using reachableFromLastUpdateLU 
  by auto

lemma stateOracleAddressBLU [simp]:
  shows "stateOracleAddressB contractsLU bridgeAddress =
         stateOracleAddressB contractsLastUpdate' bridgeAddress"
  using reachableFromBridgeStateOracle reachableFromLastUpdate'LU 
  by blast

lemma depositLastUpdate' [simp]: 
  shows "BridgeState.deposit (the (bridgeState contractsLastUpdate' bridgeAddress)) = tokenDepositAddress"
  by (meson properSetupLastUpdate' properSetup_def)

lemma depositLU [simp]:
  "BridgeState.deposit (the (bridgeState contractsLU bridgeAddress)) = tokenDepositAddress"
  using reachableFromBridgeDeposit reachableFromLastUpdate'LU depositLastUpdate'
  by blast

lemma tokenDepositStateLastUpdate'NotNone [simp]:
  shows "tokenDepositState contractsLastUpdate' tokenDepositAddress \<noteq> None"
  by (meson properSetupLastUpdate' properSetup_def)

lemma callLastStateLU [simp]:
  shows "callLastState contractsLU (stateOracleAddressB contractsLU bridgeAddress) = 
         (Success, stateRoot)"
  using noUpdate noUpdateLastState callUpdateLastState lastUpdate
  using reachableFromBridgeStateOracle reachableFromLastUpdate'LU reachableFromLastUpdateLU
  by (smt (verit, ccfv_threshold) callLastState_def  option.case_eq_if properSetupLU properSetup_def )

lemma getLastStateBLU [simp]:
  shows "getLastStateB contractsLU bridgeAddress = stateRoot"
  using callLastState callLastStateLU
  by blast

lemma  getLastStateTDLU [simp]:
  shows "getLastStateTD contractsLU tokenDepositAddress = stateRoot"
  by (metis getLastStateBLU properSetupLU properSetup_getLastState)

lemma generateStateRootLastUpdate' [simp]:
  shows "generateStateRoot contractsLastUpdate' = stateRoot"
  using lastUpdate updateSuccess 
  by force

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
    by (metis generateStateRootLastUpdate' option.collapse tokenDepositStateLastUpdate'NotNone)
qed

end

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

locale Init = Init' + 
  fixes contractsI :: Contracts
  fixes stepsInit :: "Step list"
  assumes reachableFromInitI [simp]:
    "reachableFrom contractsInit contractsI stepsInit"
begin
lemma lastStateTDZero [simp]:
  shows "getLastStateTD contractsInit tokenDepositAddress = 0"
  by (metis lastStateBZero properSetupInit properSetup_getLastState)
end

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
    blockLU=block and
    blockNumLU=blockNum and
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
  assumes update: "UPDATE (stateOracleAddressB contractsD bridgeAddress) stateRoot \<in> set steps"

  (* FIXME: amount must be the same as the value of the message - this assumption can be removed when the definition of executeStep is changed *)
  assumes "val msg = amount"

  shows "sender msg = sender msg'" "token = token'" "amount = amount'"
proof-
  have "getDeposit (the (tokenDepositState contractsD' tokenDepositAddress)) ID = hash3 (sender msg) token amount"
    using callDepositWritesHash deposit
    by simp

  define stateOracleAddress where "stateOracleAddress = stateOracleAddressB contractsD bridgeAddress"

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
     blockLU=blockx and
     blockNumLU=blockNumx and
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

lemma depositedTokenAmountCons [simp]:
  shows "depositedTokenAmount address token (DEPOSIT address caller ID token amount # steps) = 
         amount + depositedTokenAmount address token steps"
  by (simp add: tokenDeposits_def depositedTokenAmount_def)

lemma depositedTokenAmountConsOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "depositedTokenAmount address token (DEPOSIT address' caller ID token' amount # steps) = 
         depositedTokenAmount address token steps"
  using assms
  by (auto simp add: tokenDeposits_def depositedTokenAmount_def)

lemma depositedTokenAmoutConsNonDeposit [simp]:
  assumes "\<nexists> address' caller' ID' token' amount'. step = DEPOSIT address' caller' ID' token' amount'"
  shows "depositedTokenAmount address token (step # steps) = depositedTokenAmount address token steps"
  using assms 
  unfolding depositedTokenAmount_def tokenDeposits_def
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

lemma claimedTokenAmoutConsNonClaim [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CLAIM address' caller' ID' token' amount' proof'"
  shows "claimedTokenAmount address token (step # steps) = claimedTokenAmount address token steps"
  using assms 
  unfolding claimedTokenAmount_def tokenClaims_def
  by (cases step, auto)

primrec DEPOSIT_id where
  "DEPOSIT_id (DEPOSIT address caller ID token amount) = ID"

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

lemma claimedDepositsAmountOther: 
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

lemma claimedTokenDepositsAmountsClaim:
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

(*
                steps               DEPOSIT
contractsInit    \<rightarrow>*     contractsI    \<rightarrow>   contractsDeposit
properSetup
getDeposit=0
lastState=0
*)
lemma claimedTokenDepositsAmountDeposit:
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

    have "\<nexists> caller' amount' proof'. CLAIM bridgeAddress caller' ID token amount' proof' \<in> set stepsInit"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain caller' amount' proof' where CLAIM_in_steps: "CLAIM bridgeAddress caller' ID token amount' proof' \<in> set stepsInit"
        by auto
      define CLAIM_step where "CLAIM_step = CLAIM bridgeAddress caller' ID token amount' proof'"
      have CLAIM_in_steps: "CLAIM_step \<in> set (DEPOSIT_step # stepsInit)"
        using CLAIM_in_steps
        unfolding CLAIM_step_def
        by simp
      obtain steps1 steps2 c1 c2 blockNum block where *:
        "reachableFrom contractsInit c1 steps2"
        "executeStep c1 blockNum block CLAIM_step = (Success, c2)"
        "reachableFrom c2 contractsDeposit steps1"
        "DEPOSIT_step # stepsInit = steps1 @ [CLAIM_step] @ steps2"
        using reachableFromStepInSteps[OF reach CLAIM_in_steps]
        unfolding DEPOSIT_step_def
        by metis

      define DEPOSIT_step' where "DEPOSIT_step' = DEPOSIT tokenDepositAddress (sender (message caller' amount')) ID token amount'"

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
    ultimately show ?thesis
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

lemma InitFirstAxiomsInduction [simp]:
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
      using False InitFirstAxiomsInduction reachableFrom_step.hyps(1) reachableFrom_step.hyps(2) reachableFrom_step.prems(5) by blast

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
          using claimedDepositsAmountOther False
          using False
          by auto
        ultimately show ?thesis
          using * reachableFrom_step.prems DEPOSIT
          by simp
      next
        case True
        have "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token (step # steps) = 
              claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps"
          using InitFirstUpdate'.claimedTokenDepositsAmountDeposit
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
        proof (rule InitFirstUpdate'.claimedTokenDepositsAmountsClaim)
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
          by (auto simp add: claimedDepositsAmountOther)
      qed
    next
      case (UPDATE address' stateRoot')
      then show ?thesis
        using reachableFrom_step *
        using claimedDepositsAmountOther
        by simp
    next
      case (CANCEL address' caller' ID' token' amount' proof')
      have "mintedToken \<noteq> token'" (* no cancel of minted tokens *)
        sorry
      then have "ERC20state contractsI mintedToken = ERC20state contractsI' mintedToken"
        using CANCEL reachableFrom_step.hyps(2) by auto
      then show ?thesis
        using CANCEL reachableFrom_step *
        using claimedDepositsAmountOther
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
        using claimedDepositsAmountOther WITHDRAW
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

lemma
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
        using callDepositBalanceOfOther notDead callDepositOtherToken depositedTokenAmountConsOther 
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
          by (metis Step.simps(12) callWithdrawWhileDeadOtherToken depositedTokenAmoutConsNonDeposit executeStep.simps(5))
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
        by (metis Message.select_convs(1) Step.simps(10) depositedTokenAmoutConsNonDeposit executeStep.simps(4) message_def)
    qed
  qed
qed

end

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

end

(*
               [stepsInit]                  update                  [stepsNoUpdate]               stepDeath               stepsBD
   contractsInit  \<rightarrow>*   contractsLastUpdate'  \<rightarrow>  contractsLastUpdate       \<rightarrow>*     contractsDead'     \<rightarrow>    contractsDead   \<rightarrow>*  contractsBD
   properSetup
*)
locale BridgeDead = StrongHashProofVerifier +
  fixes contractsInit :: Contracts
  fixes contractsLastUpdate' :: Contracts
  fixes contractsLastUpdate  :: Contracts
  fixes contractsDead' :: Contracts
  fixes contractsDead :: Contracts
  fixes contractsBD :: Contracts
  fixes tokenDepositAddress :: address
  fixes bridgeAddress :: address
  fixes stepsInit :: "Step list"
  fixes stepsNoUpdate :: "Step list"
  fixes stepsBD :: "Step list"
  fixes stepDeath :: Step
  fixes stateRoot :: bytes32
  fixes blockLU :: Block
  fixes blockNumLU :: uint256

  assumes properSetupInit [simp]:
    "properSetup contractsInit tokenDepositAddress bridgeAddress"
  assumes reachableFromInitLastUpdate' [simp]: 
    "reachableFrom contractsInit contractsLastUpdate' stepsInit"
  \<comment> \<open>The last update that happened when the bridge was still alive\<close>
  assumes lastUpdate [simp]:
    "let stateOracleAddress = stateOracleAddressB contractsInit bridgeAddress
      in callUpdate contractsLastUpdate' stateOracleAddress blockLU blockNumLU stateRoot = (Success, contractsLastUpdate)"
  \<comment> \<open>There were no updates since then until the bridge died\<close>
  assumes reachableFromLastUpdateDead [simp]: 
    "reachableFrom contractsLastUpdate contractsDead' stepsNoUpdate"
  assumes noUpdatesLastUpdateDead [simp]:
    "let stateOracleAddress = stateOracleAddressB contractsInit bridgeAddress
      in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set stepsNoUpdate"
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
  assumes stateRootNonZero:
    "stateRoot \<noteq> 0"
begin
lemma properSetupLastUpdate' [simp]:
  shows "properSetup contractsLastUpdate' tokenDepositAddress bridgeAddress"
  using properSetupReachable properSetupInit reachableFromInitLastUpdate'
  by blast

lemma stateOracleAddressBLastUpdate' [simp]:
  shows "stateOracleAddressB contractsLastUpdate' bridgeAddress =
         stateOracleAddressB contractsInit bridgeAddress"
  using reachableFromBridgeStateOracle reachableFromInitLastUpdate' 
  by blast

lemma stateOracleAddressBLastUpdate [simp]:
  shows "stateOracleAddressB contractsLastUpdate bridgeAddress =
         stateOracleAddressB contractsInit bridgeAddress"
  using callUpdateIBridge lastUpdate stateOracleAddressBLastUpdate' 
  by presburger
end

sublocale BridgeDead \<subseteq> LastUpdate
  where contractsLU=contractsDead'
proof
  show "let stateOracleAddress = stateOracleAddressB contractsLastUpdate bridgeAddress
         in \<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set stepsNoUpdate"
    using noUpdatesLastUpdateDead
    by simp
next
qed simp_all

context BridgeDead
begin

lemma reachableFromInitDead' [simp]: 
  shows "reachableFrom contractsInit contractsDead' (stepsNoUpdate @ [UPDATE_step] @ stepsInit)"
  using reachableFromInitLastUpdate' reachableFromLastUpdate'LastUpdate reachableFromLastUpdateDead reachableFromTrans
  by presburger

lemma reachableFromInitBD [simp]: 
  shows "reachableFrom contractsInit contractsBD (stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step] @ stepsInit)"
  using reachableFromContractsBD deathStep reachableFromInitDead' reachableFromTrans
  by blast

lemma properSetupDead [simp]:
  shows "properSetup contractsDead tokenDepositAddress bridgeAddress"
  using properSetupReachable deathStep properSetupLU 
  by blast

lemma properSetupBD [simp]:
  shows "properSetup contractsBD tokenDepositAddress bridgeAddress"
  using reachableFromContractsBD properSetupDead properSetupReachable 
  by blast


lemma tokenDepositStateContractsCurrentNotNone [simp]:
  shows "tokenDepositState contractsBD tokenDepositAddress \<noteq> None"
  by (meson properSetupBD properSetup_def)

lemma ERC20stateLastUpdate' [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "ERC20state contractsLastUpdate' token \<noteq> None"
  using properTokenReachable[OF reachableFromInitLastUpdate' assms(1)]
  by (meson properToken_def)

lemma ERC20stateContractsCurrentNotNone [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "ERC20state contractsBD token \<noteq> None"
  using assms
  by (meson reachableFromERC20State properToken_def reachableFromInitBD)

lemma notBridgeDeadContractsLastUpdate':
  shows "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
proof-
  have "reachableFrom contractsLastUpdate' contractsDead' (stepsNoUpdate @ [UPDATE_step])"
    using reachableFromLastUpdate'LastUpdate reachableFromLastUpdateDead reachableFromTrans
    by blast
  then show ?thesis
    using notBridgeDead' reachableFromBridgeDead
    by blast
qed

lemma bridgeDeadContractsBD [simp]:
  shows "bridgeDead contractsBD tokenDepositAddress"
  using reachableFromBridgeDead bridgeDead reachableFromContractsBD
  by blast

lemma getLastStateBLastUpdate [simp]:
  shows "getLastStateB contractsLastUpdate bridgeAddress = stateRoot"
  using callUpdateLastState lastUpdate stateOracleAddressBLastUpdate
  by presburger

lemmas properSetupDead' = properSetupLU
lemmas getLastStateBDead' = getLastStateBLU
lemmas getLastStateTDDead' = getLastStateTDLU

lemma stepDeathNoUpdate [simp]:
  shows "\<nexists> address stateRoot. stepDeath = UPDATE address stateRoot"
  using bridgeDead callUpdateDeadState deathStep notBridgeDead'
  by (smt (verit) executeStep.simps(3) list.distinct(1) reachableFrom.simps reachableFromCons')

lemma deadStateContractsDead [simp]: 
  shows "deadState (the (tokenDepositState contractsDead tokenDepositAddress)) = stateRoot"
  using BridgeDiesDeadState bridgeDead deathStep getLastStateTDLU notBridgeDead'  
  by (smt (verit) list.discI reachableFrom.simps reachableFromCons')

lemma deadStateContractsBD [simp]: 
  shows "deadState (the (tokenDepositState contractsBD tokenDepositAddress)) = stateRoot"
  using stateRootNonZero reachableFromContractsBD deadStateContractsDead reachableFromDeadState
  by blast

theorem cancelDepositWhileDeadNoClaim:
  \<comment> \<open>Cancel deposit succeded\<close>
  assumes cancel:
     "callCancelDepositWhileDead contractsBD tokenDepositAddress msg block ID token amount proof = 
      (Success, contractsCancel)"
  \<comment> \<open>Claim did not happen before that last update\<close>
  shows "\<nexists> caller' token' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain caller' token' amount' proof' where 
    *: "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
    by auto
  then have "getClaim (the (bridgeState contractsLastUpdate' bridgeAddress)) ID = True"
    using claimStepSetsClaim reachableFromInitLastUpdate'
    by blast

  moreover

  have "verifyClaimProof () bridgeAddress ID stateRoot proof = True"
    by (metis properSetupBD properSetup_def bridgeDeadContractsBD callCancelDepositWhileDeadVerifyClaimProof cancel deadStateContractsBD lastValidState_def snd_conv)
  then have "getClaim (the (bridgeState contractsLastUpdate' bridgeAddress)) ID = False"
    by (metis generateStateRootLastUpdate' option.collapse properSetupLastUpdate' properSetup_def verifyClaimProofE)

  ultimately

  show False
    by simp
qed

(* FIXME: could this special case be somehow avoided? *)
theorem cancelDepositWhileDeadNoClaimDeathStep:
  assumes "stepDeath = CANCEL tokenDepositAddress caller ID token amount proof"
  shows "\<nexists> caller' token' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain caller' token' amount' proof' where 
    *: "CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
    by auto
  then have "getClaim (the (bridgeState contractsLastUpdate' bridgeAddress)) ID = True"
    using claimStepSetsClaim reachableFromInitLastUpdate'
    by blast

  moreover

  thm callCancelDepositWhileDead_def
  obtain block where cancel: "callCancelDepositWhileDead contractsDead' tokenDepositAddress (message caller 0) block ID token amount proof = (Success, contractsDead)"
    using deathStep assms
    by (smt (verit, ccfv_threshold) executeStep.simps(4) list.discI list.inject reachableFrom.cases)
  have "verifyClaimProof () bridgeAddress ID stateRoot proof = True"
    using callCancelDepositWhileDeadVerifyClaimProof[OF cancel]
    by (smt (verit, best) callLastState callLastStateI getLastStateBDead' lastValidState_def notBridgeDead' prod.exhaust_sel properSetupDead' properSetup_def)
  then have "getClaim (the (bridgeState contractsLastUpdate' bridgeAddress)) ID = False"
    by (metis generateStateRootLastUpdate' option.collapse properSetupLastUpdate' properSetup_def verifyClaimProofE)

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
    "callWithdrawWhileDead contractsBD tokenDepositAddress msg block token amount proof = (Success, contractsW)"
  \<comment> \<open>Caller had sufficient balance\<close>
  shows "callBalanceOf contractsLastUpdate' token (sender msg) = (Success, amount)"
proof-
  have "verifyBalanceProof () token (sender msg) amount stateRoot proof"
    using callWithdrawWhileDeadVerifyBalanceProof[OF withdraw]
    by (metis bridgeDeadContractsBD deadStateContractsBD lastValidState_def snd_conv)
  then have "balanceOf (the (ERC20state contractsLastUpdate' token)) (sender msg) = amount"
    using assms
    using verifyBalanceProofE[of contractsLastUpdate' stateRoot]
    by auto
  then show ?thesis
    using assms
    unfolding callBalanceOf_def
    by (auto split: option.splits)
qed


(* FIXME: could this special case be somehow avoided? *)
theorem withdrawSufficientBalanceDeathStep:
  \<comment> \<open>Token deposit can accept token\<close>
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  \<comment> \<open>Withdraw succeded\<close>
  assumes "stepDeath = WITHDRAW tokenDepositAddress caller token amount proof"
  \<comment> \<open>Caller had sufficient balance\<close>
  shows "callBalanceOf contractsLastUpdate' token caller = (Success, amount)"
proof-
  obtain block where
    withdraw: "callWithdrawWhileDead contractsDead' tokenDepositAddress (message caller 0) block token amount proof = 
    (Success, contractsDead)"
    using deathStep assms
    by (smt (verit) executeStep.simps(5) list.discI reachableFrom.simps reachableFromCons')
  have "verifyBalanceProof () token caller amount stateRoot proof"
    using callWithdrawWhileDeadVerifyBalanceProof[OF withdraw]
    by (smt (verit) callLastState callLastStateI getLastStateTDDead' lastValidState_def notBridgeDead' prod.exhaust_sel properSetupDead' properSetup_def senderMessage)
  then have "balanceOf (the (ERC20state contractsLastUpdate' token)) caller = amount"
    using assms
    using verifyBalanceProofE[of contractsLastUpdate' stateRoot]
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

lemma canceledAmountConsNonCancel [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CANCEL address' caller' ID' token' amount' proof'"
  shows "canceledTokenAmount address token (step # steps) = canceledTokenAmount address token steps"
  using assms 
  unfolding canceledTokenAmount_def tokenCancels_def
  by (cases step, auto)

lemma canceledTokenAmountConsOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "canceledTokenAmount address token (CANCEL address' caller' ID' token' amount' proof' # steps) = 
         canceledTokenAmount address token steps"
  using assms
  unfolding canceledTokenAmount_def tokenCancels_def
  by auto

definition nonClaimedBeforeDeathTokenDeposits where
  "nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore) 
            (tokenDeposits tokenDepositAddress token steps)"

definition isCanceledID where
  "isCanceledID tokenDepositAddress token ID steps \<longleftrightarrow> 
   (\<exists> caller amount proof. CANCEL tokenDepositAddress caller ID token amount proof \<in> set steps)"

definition nonCanceledNonClaimedBeforeDeathTokenDeposits where
  "nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore \<and>
                     \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) steps)
            (tokenDeposits tokenDepositAddress token steps)"

definition tokenWithdrawals where
  "tokenWithdrawals address token steps = filter (\<lambda> step. case step of WITHDRAW address' caller token' amount proof \<Rightarrow> address = address' \<and> token = token' | _ \<Rightarrow> False) steps"

definition tokenWithdrawnAmount where
  "tokenWithdrawnAmount address token steps = 
   sum_list (map WITHDRAW_amount (tokenWithdrawals address token steps))"

lemma tokenWithdrawnAmoutConsNonWithdraw [simp]:
  assumes "\<nexists> address' caller' token' amount' proof'. step = WITHDRAW address' caller' token' amount' proof'"
  shows "tokenWithdrawnAmount address token (step # steps) = tokenWithdrawnAmount address token steps"
  using assms 
  unfolding tokenWithdrawnAmount_def tokenWithdrawals_def
  by (cases step, auto)

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


context BridgeDead
begin

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
    by (metis callBalanceOf callBalanceOfERC20state generateStateRootLastUpdate' option.collapse)

  moreover

  have "proofVerifierState contractsBD (TokenDepositState.proofVerifier stateTokenDeposit) \<noteq> None"
     by (metis properSetupBD properSetup_def stateTokenDeposit_def)

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


(*

(* ------------------------------------------------------------------------------------ *)


context ProofVerifier
begin

(* ----------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------- *)


lemma nonClaimedBeforeDeathTokenDepositsDeposit:
  assumes "reachableFrom contractsInit contracts (DEPOSIT tokenDepositAddress caller ID token amount # steps @ stepsBefore)"
  shows "nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (DEPOSIT tokenDepositAddress caller ID token amount # steps @ stepsBefore) =
         (DEPOSIT tokenDepositAddress caller ID token amount) # nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
  using assms
  unfolding nonClaimedBeforeDeathTokenDeposits_def
  apply (auto simp add: tokenDeposits_def)
  sorry

lemma nonCanceledNonClaimedTokenDepositsBeforeDeathDeposit:
  assumes "reachableFrom contractsInit contracts (DEPOSIT tokenDepositAddress caller ID token amount # steps @ stepsBefore)"
  shows "nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (DEPOSIT tokenDepositAddress caller ID token amount # steps @ stepsBefore) =
         (DEPOSIT tokenDepositAddress caller ID token amount) # nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
  using assms
  unfolding nonCanceledNonClaimedBeforeDeathTokenDeposits_def
  apply (auto simp add: tokenDeposits_def)
  sorry


lemma nonCanceledNonClaimedBeforeDeathTokenDepositsCancel:
  assumes "reachableFrom contractsInit contracts stepsBefore"
  \<comment> \<open>The last update that happened when the bridge was still alive\<close>
  assumes update:
          "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState contractsInit bridgeAddress))
            in callUpdate contracts stateOracleAddress block blockNum stateRoot = (Success, contracts')"
  assumes "stateRoot \<noteq> 0" (* NOTE: additional assumption *)
  assumes "\<not> (bridgeDead contracts tokenDepositAddress)"
  \<comment> \<open>There were no updates since then\<close>
  assumes "reachableFrom contracts' contracts'' steps'"
  assumes noUpdate: "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState contractsInit bridgeAddress))
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"
  \<comment> \<open>Bridge was dead\<close>
  assumes "\<not> (bridgeDead contracts'' tokenDepositAddress)"
  assumes "stepsF = [CANCEL tokenDepositAddress caller ID token amount proof] @ steps'' @ steps' @ [UPDATE tokenDepositAddress stateRoot] @ stepsBefore"
  shows "\<exists> steps1 steps2.
           nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore) = 
           steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2 \<and>
           nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (CANCEL tokenDepositAddress caller ID token amount proof # steps @ stepsBefore) = 
           steps1 @ steps2"
proof-
  define CANCEL_step where "CANCEL_step = CANCEL tokenDepositAddress caller ID token amount proof"
  define DEPOSIT_step where "DEPOSIT_step = DEPOSIT tokenDepositAddress (sender (message caller 0)) ID token amount"

  obtain contracts' block where 
     "reachableFrom contractsInit contracts' (steps @ stepsBefore)" 
     "callCancelDepositWhileDead contracts' tokenDepositAddress (message caller 0) block ID token amount proof = (Success, contracts)"
    using reachableFromCons'[OF assms(1)]
    by auto

  then obtain contractsLast where
    "reachableFrom contractsInit contractsLast stepsBefore"
    "reachableFrom contractsLast contracts' steps"
    using reachableFromAppend by blast

  have "DEPOSIT_step \<in> set (steps @ stepsBefore)"
    unfolding DEPOSIT_step_def
  proof (rule cancelDepositOnlyAfterDeposit)
    show "callCancelDepositWhileDead contracts' tokenDepositAddress (message caller 0) block ID token amount proof = (Success, contracts)"
      by fact
  next
    show "reachableFrom contractsInit contracts' (steps @ stepsBefore)"
      by fact
  next
    show "properSetup contractsInit tokenDepositAddress bridgeAddress"
      by fact
  next
    show "getDeposit (the (tokenDepositState contractsInit tokenDepositAddress)) ID = 0"
      sorry
  next
    show "hash3 (sender (message caller 0)) token amount \<noteq> 0"
      sorry
  next
    show "hash3_inj"
      sorry
  qed
  then obtain steps1 steps2 where steps: "steps @ stepsBefore = steps1 @ [DEPOSIT_step] @ steps2"
    by (metis append_Cons append_self_conv2 split_list)
  then have "DEPOSIT_step \<in> set (tokenDeposits tokenDepositAddress token (steps @ stepsBefore))"
    unfolding tokenDeposits_def DEPOSIT_step_def
    by auto

  moreover

  have "\<nexists> caller' token' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsBefore"
  proof (rule cancelDepositNoClaim)
    show "callCancelDepositWhileDead contracts' tokenDepositAddress (message caller 0) block ID token amount proof = (Success, contracts)"
      by fact
  next
    show "reachableFrom contractsInit contractsLast stepsBefore"
      by fact
  next
    show "properSetup contractsInit tokenDepositAddress bridgeAddress"
      by fact
  next
  qed

  moreover
  have "\<nexists> caller' amount' proof'. 
          CANCEL tokenDepositAddress caller' ID token amount' proof' \<in> set (steps @ stepsBefore)"
    sorry

  ultimately

  have "DEPOSIT_step \<in> set (nonCanceledNonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore))"
    unfolding nonCanceledNonClaimedBeforeDeathTokenDeposits_def DEPOSIT_step_def isClaimedID_def isCanceledID_def
    by auto

  have *: "\<forall> step \<in> set (steps1 @ steps2). (\<forall> caller' amount' ID'. step = DEPOSIT tokenDepositAddress caller' ID' token amount' \<longrightarrow> ID' \<noteq> ID)"
  proof safe
    fix caller' amount' proof' 
    assume "DEPOSIT tokenDepositAddress caller' ID token amount' \<in> set (steps1 @ steps2)"
    moreover
    have "\<nexists>token' caller' amount'.
         DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set (steps1 @ steps2)"
    proof (rule DEPOSITNoDouble')
      show "steps @ stepsBefore = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2"
        using steps
        unfolding DEPOSIT_step_def
        by simp
    next
      show "depositHashesNonZero (steps @ stepsBefore)"
        sorry
    next
      show "reachableFrom contractsInit contracts' (steps @ stepsBefore)"
        by fact
    qed
    ultimately
    show False
      by simp
  qed
  then have "DEPOSIT_step \<notin> set (steps1 @ steps2)"
    unfolding DEPOSIT_step_def
    by auto

  show ?thesis
    using cancelDepositNoClaim
    sorry
qed

lemma nonClaimedTokenDepositsBeforeDeathOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "nonClaimedTokenDepositsBeforeDeath tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedTokenDepositsBeforeDeath tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonClaimedTokenDepositsBeforeDeath_def tokenDeposits_def
  by (auto split: Step.splits)

lemma nonCanceledNonClaimedTokenDepositsBeforeDeathOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  assumes "\<nexists> caller' ID' amount' proof'. step = CANCEL tokenDepositAddress caller' ID' token amount' proof'"
  shows "nonCanceledNonClaimedTokenDepositsBeforeDeath tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonCanceledNonClaimedTokenDepositsBeforeDeath tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonCanceledNonClaimedTokenDepositsBeforeDeath_def tokenDeposits_def
  by (auto split: Step.splits)

definition nonCanceledNonClaimedTokenDepositsBeforeDeathAmount where
  "nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (nonCanceledNonClaimedTokenDepositsBeforeDeath tokenDepositAddress bridgeAddress token stepsBefore steps))"

definition nonClaimedTokenDepositsBeforeDeathAmount where
  "nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (nonClaimedTokenDepositsBeforeDeath tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma nonClaimedTokenDepositsBeforeDeathAmountDeposit [simp]:
  assumes "reachableFrom contractsInit contracts (DEPOSIT tokenDepositAddress caller ID token amount # steps @ stepsBefore)"
  shows "nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (DEPOSIT tokenDepositAddress caller ID token amount # steps @ stepsBefore) =
         amount + nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
  using assms nonClaimedTokenDepositsBeforeDeathAmount_def nonClaimedTokenDepositsBeforeDeathDeposit by auto

lemma nonCanceledNonClaimedTokenDepositsBeforeDeathAmountDeposit [simp]:
  assumes "reachableFrom contractsInit contracts (DEPOSIT tokenDepositAddress caller ID token amount # steps @ stepsBefore)"
  shows "nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (DEPOSIT tokenDepositAddress caller ID token amount # steps @ stepsBefore) =
         amount + nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
  using assms nonCanceledNonClaimedTokenDepositsBeforeDeathAmount_def nonCanceledNonClaimedTokenDepositsBeforeDeathDeposit by auto

lemma nonCanceledNonClaimedTokenDepositsBeforeDeathAmountOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  assumes "\<nexists> caller' ID' amount' proof'. step = CANCEL tokenDepositAddress caller' ID' token amount' proof'"
  shows "nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms nonCanceledNonClaimedTokenDepositsBeforeDeathAmount_def)

lemma nonClaimedTokenDepositsBeforeDeathAmountOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms nonClaimedTokenDepositsBeforeDeathAmount_def)

lemma nonCanceledNonClaimedTokenDepositsBeforeDeathAmountCancel:
  assumes "reachableFrom contractsInit contracts (CANCEL tokenDepositAddress caller ID token amount proof # steps @ stepsBefore)"
  shows "nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (CANCEL tokenDepositAddress caller ID token amount proof # steps @ stepsBefore) =
         nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore) - amount"
        "amount \<le> nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
  using nonCanceledNonClaimedTokenDepositsBeforeDeathCancel[OF assms, of bridgeAddress]
  unfolding nonCanceledNonClaimedTokenDepositsBeforeDeathAmount_def
  by auto


lemma noCancelBeforeBridgeDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> (bridgeDead contracts tokenDepositAddress)"
  shows "\<nexists> step. step \<in> set steps \<and> (\<exists> caller ID token amount proof. step = CANCEL tokenDepositAddress caller ID token amount proof)"
  using assms
proof (induction contractsInit contracts steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts' contractsInit contracts blockNum block step)
  have notDead: "\<not> bridgeDead contracts tokenDepositAddress"
    by (meson ProofVerifier.reachableFromDeadState ProofVerifier.reachableFrom_step ProofVerifier_axioms reachableFrom_base reachableFrom_step.hyps(2) reachableFrom_step.prems)
  then show ?case
    using reachableFrom_step callCancelDepositWhileDeadBridgeDead
    by (metis executeStep.simps(4) set_ConsD)
qed

lemma canceledTokenAmountBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> (bridgeDead contracts tokenDepositAddress)"
    shows "canceledTokenAmount tokenDepositAddress token steps = 0"
  using assms noCancelBeforeBridgeDead[OF assms]
  unfolding canceledTokenAmount_def tokenCancels_def
  by (auto split: Step.splits)


lemma nonCanceledNonClaimedBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> (bridgeDead contracts tokenDepositAddress)"
    shows "nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
           nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms noCancelBeforeBridgeDead[OF assms]
  unfolding nonCanceledNonClaimedTokenDepositsBeforeDeathAmount_def nonClaimedTokenDepositsBeforeDeathAmount_def
  unfolding nonCanceledNonClaimedTokenDepositsBeforeDeath_def nonClaimedTokenDepositsBeforeDeath_def
  by metis

lemma
  assumes "reachableFrom contracts'' contractsF steps''"
  assumes "properSetup contractsInit tokenDepositAddress bridgeAddress"
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"

  assumes "reachableFrom contractsInit contracts stepsBefore"
  \<comment> \<open>The last update that happened when the bridge was still alive\<close>
  assumes update:
          "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState contractsInit bridgeAddress))
            in callUpdate contracts stateOracleAddress block blockNum stateRoot = (Success, contracts')"
  assumes "stateRoot \<noteq> 0" (* NOTE: additional assumption *)
  assumes "\<not> (bridgeDead contracts tokenDepositAddress)"
  \<comment> \<open>There were no updates since then\<close>
  assumes "reachableFrom contracts' contracts'' steps'"
  assumes noUpdate: "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState contractsInit bridgeAddress))
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"
  \<comment> \<open>Bridge was dead\<close>
  assumes "\<not> (bridgeDead contracts'' tokenDepositAddress)"
  assumes "stepsF = steps'' @ steps' @ [UPDATE tokenDepositAddress stateRoot] @ stepsBefore"
  shows
  "nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF + 
   canceledTokenAmount tokenDepositAddress token stepsF = 
   nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF"
  using assms
proof (induction contracts'' contractsF steps'' arbitrary: stepsF rule: reachableFrom.induct )
  case (reachableFrom_base contractsF)
  have "reachableFrom contracts contracts' [UPDATE tokenDepositAddress stateRoot]"
    sorry
  then have "reachableFrom contractsInit contractsF stepsF"
    using reachableFrom_base
    by (smt (verit, ccfv_threshold) append_Nil reachableFromTrans)
  moreover
  have "\<not> (bridgeDead contracts tokenDepositAddress)"
    using reachableFrom_base
    by simp
  ultimately
  show ?case
    using canceledTokenAmountBridgeNotDead nonCanceledNonClaimedBridgeNotDead reachableFrom_base
    by simp
next
  case (reachableFrom_step steps contractsF contracts'' contractsF' blockNum block step)

  have "reachableFrom contracts contracts' [UPDATE tokenDepositAddress stateRoot]"
    sorry
  then have "reachableFrom contractsInit contractsF stepsF"
    using reachableFrom_step
    by (meson reachableFrom.reachableFrom_step reachableFromTrans)
  
  define stepsF' where "stepsF' = steps @ steps' @ [UPDATE tokenDepositAddress stateRoot] @ stepsBefore"
  have *: "nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF' +
           canceledTokenAmount tokenDepositAddress token stepsF' =
           nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF'"
    unfolding stepsF'_def
    using reachableFrom_step
    by auto
  show ?case
  proof (cases step)
    case (UPDATE address' stateRoot')
    then show ?thesis
      using * reachableFrom_step.prems(10)
      unfolding stepsF'_def
      by simp
  next
    case (WITHDRAW address' caller' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems(10)
      unfolding stepsF'_def
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step.prems(10)
      unfolding stepsF'_def
      by simp
  next
    case (DEPOSIT address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case False
      then show ?thesis
        using * DEPOSIT reachableFrom_step.prems(10)
        unfolding stepsF'_def
        by simp
    next
      case True
      have "nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF =
            amount' + nonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF'"
        using nonClaimedTokenDepositsBeforeDeathAmountDeposit[where steps="steps @ steps' @ [UPDATE tokenDepositAddress stateRoot]"]
        using \<open>reachableFrom contractsInit contractsF stepsF\<close>
        unfolding stepsF'_def reachableFrom_step.prems(10)
        using True * DEPOSIT 
        by auto
      moreover
      have "nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF =
            amount' + nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF'"
        using nonCanceledNonClaimedTokenDepositsBeforeDeathAmountDeposit[where steps="steps @ steps' @ [UPDATE tokenDepositAddress stateRoot]"]
        using \<open>reachableFrom contractsInit contractsF stepsF\<close>
        unfolding stepsF'_def reachableFrom_step.prems(10)
        using True * DEPOSIT 
        by auto
      ultimately
      show ?thesis
        using True * DEPOSIT reachableFrom_step.prems(10)
        unfolding stepsF'_def
        by simp
    qed
  next
    case (CANCEL address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case False
      then show ?thesis
        using * CANCEL
        unfolding stepsF'_def reachableFrom_step.prems(10)
        by auto
    next
      case True
      have "nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF = 
            nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF' - 
            amount'"
           "amount' \<le> nonCanceledNonClaimedTokenDepositsBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore stepsF'"
        using \<open>reachableFrom contractsInit contractsF stepsF\<close> nonCanceledNonClaimedTokenDepositsBeforeDeathAmountCancel
        by (smt (verit, best) CANCEL True append.assoc append_Cons reachableFrom_step.prems(10) stepsF'_def)+
      then show ?thesis
        using * True CANCEL
        unfolding stepsF'_def reachableFrom_step.prems(10)
        by simp
    qed
  qed
qed




end

*)
end