theory Properties
  imports Reachability
begin

context ProofVerifier
begin


(* ------------------------------------------------------------------------------------ *)

text \<open>There are no double deposits\<close>
theorem callDepositNoDouble:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"         
  assumes "reachableFrom contracts' contracts'' steps"
  (* NOTE: additional assumption *)
  assumes "hash3 (sender msg) token amount \<noteq> 0"
  shows "fst (callDeposit contracts'' address block' msg' ID token' amount') \<noteq> Success"
proof (cases "bridgeDead contracts'' address")
  case False
  have "getDeposit (the (tokenDepositState contracts' address)) ID = hash3 (sender msg) token amount"
    using callDepositWritesHash[OF assms(1)]
    by simp
  then have "getDeposit (the (tokenDepositState contracts'' address)) ID \<noteq> 0"
    using False reachableFromGetDepositBridgeNotDead assms
    by auto
  then show ?thesis
    using callDepositWrittenHash by blast
next
  case True
  then show ?thesis
    using callDepositFailsInDeadState 
    by presburger
qed

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

text \<open>There are no double cancels\<close>
theorem callCancelNoDouble:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  assumes "reachableFrom contracts' contracts'' steps"
  (* NOTE: additional assumption *)
  assumes "hash3 (sender msg') token' amount' \<noteq> 0"
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

(* ------------------------------------------------------------------------------------ *)

text \<open>We want to prove that there cannot be two DEPOSIT steps with the same ID on the same tokenDeposit address\<close>

lemma DEPOSITNoDoubleCons:
  assumes "reachableFrom contracts contracts' (DEPOSIT tokenDepositAddress caller ID token amount # steps)"
  assumes "\<forall> step \<in> set steps. \<forall> caller' amount' ID' token'. step = DEPOSIT tokenDepositAddress caller' ID' token' amount' \<longrightarrow> hash3 caller' token' amount' \<noteq> 0"
  shows "\<nexists> token' caller' amount'. DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set steps"
proof (rule ccontr)
  obtain contracts'' block where *:
   "reachableFrom contracts contracts'' steps"
   "callDeposit contracts'' tokenDepositAddress block (message caller amount) ID token amount = (Success, contracts')"
    using reachableFromCons'[OF assms(1)]
    by auto

  moreover

  assume "~ ?thesis"
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
  next
    show "hash3 (sender (message caller' amount')) token' amount' \<noteq> 0"
      using "**" assms message_def by force
  qed

  ultimately
  show False
    by simp
qed


lemma DEPOSITNoDouble:
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps3"
  assumes "\<forall> step \<in> set steps. \<forall> caller' amount' ID' token'. step = DEPOSIT tokenDepositAddress caller' ID' token' amount' \<longrightarrow> hash3 caller' token' amount' \<noteq> 0"
  shows False
proof-
  obtain contracts'' where *: 
    "reachableFrom contracts'' contracts' steps1"
    "reachableFrom contracts contracts'' (DEPOSIT tokenDepositAddress caller ID token amount # (steps2 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps3))"
    using assms(1-2) reachableFromAppend[of contracts contracts' steps1]
    by auto
 
  have "\<nexists> token'' caller'' amount''. DEPOSIT tokenDepositAddress caller'' ID token'' amount'' \<in> set (steps2 @ [DEPOSIT tokenDepositAddress caller' ID token' amount'] @ steps3)"
    using DEPOSITNoDoubleCons[OF *(2)] assms
    by (metis Un_iff set_append)
  then show False
    by auto
qed

lemma DEPOSITNoDouble':
  assumes "reachableFrom contracts contracts' steps"
  assumes "steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2"
  assumes "\<forall> step \<in> set steps. \<forall> caller' amount' ID' token'. step = DEPOSIT tokenDepositAddress caller' ID' token' amount' \<longrightarrow> hash3 caller' token' amount' \<noteq> 0"
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

(* ------------------------------------------------------------------------------------ *)

text \<open>No deposit after the bridge dies\<close>
theorem  noDepositBridgeDead: 
  assumes "bridgeDead contracts tokenDepositAddress"
  assumes "reachableFrom contracts contracts' steps"
  shows "fst (callDeposit contracts' tokenDepositAddress block msg ID token amount) \<noteq> Success"
  using assms callDepositFailsInDeadState reachableFromDeadState
  by blast


text \<open>After a successful deposit and a state update, 
      if a bridge is still alive a claim can be made \<close>
theorem claimPossibleAfterDepositAndUpdate:
  \<comment> \<open>contracts are setup properly in the initial state, for the given token\<close>
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  assumes "properToken contracts tokenDepositAddress bridgeAddress token"

  \<comment> \<open>A deposit is successfully made\<close>
  assumes "callDeposit contracts tokenDepositAddress block msg ID token amount = (Success, contractsD)"
  \<comment> \<open>after a deposit a new state is reached\<close>
  assumes "reachableFrom contractsD contractsD' steps"
  \<comment> \<open>the bridge is not dead in the reached state\<close>
  assumes "\<not> bridgeDead  contractsD' tokenDepositAddress"
  \<comment> \<open>A last update is made\<close>
  assumes "let stateOracleAddress = stateOracleAddressTD contractsD' tokenDepositAddress
            in callUpdate contractsD' stateOracleAddress block blockNum stateRoot = (Success, contractsU)"
  \<comment> \<open>A new state is reached after that last update\<close>
  assumes "reachableFrom contractsU contractsU' steps'"
  assumes noUpdates:
          "let stateOracleAddress = stateOracleAddressTD contractsU tokenDepositAddress
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"

  \<comment> \<open>there was no previous claim\<close>
  assumes "getClaim (the (bridgeState contractsU' bridgeAddress)) ID = False"

  \<comment> \<open>The same person who made the deposit can make the claim\<close>
  assumes "sender msg' = sender msg"

  assumes "hash3 (sender msg) token amount \<noteq> 0" (* Additional assumption *)

  \<comment> \<open>A claim can be made with the state root and the proof obtained from the state that
      was used for the last update\<close>
  shows "let stateRoot = generateStateRoot contractsD';
             proof = generateDepositProof contractsD' ID
          in \<exists> contractsC. callClaim contractsU' bridgeAddress msg' ID token amount proof = (Success, contractsC)"
proof-
  define stateOracleAddress where 
       "stateOracleAddress = BridgeState.stateOracle (the (bridgeState contracts bridgeAddress))"
  define proofVerifierAddress where 
       "proofVerifierAddress = BridgeState.proofVerifier (the (bridgeState contracts bridgeAddress))"
  define tokenPairsAddress where 
       "tokenPairsAddress = BridgeState.tokenPairs (the (bridgeState contracts bridgeAddress))"
  define "proof" where "proof = generateDepositProof contractsD' ID"
  define stateRoot where "stateRoot = generateStateRoot contractsD'"

  have "verifyDepositProof () tokenDepositAddress ID (hash3 (sender msg) token amount) stateRoot proof = True"
  proof (rule verifyDepositProofI)
    show "generateDepositProof contractsD' ID = proof"
      unfolding proof_def
      by simp
  next
    show "generateStateRoot contractsD' = stateRoot"
      unfolding stateRoot_def
      by simp
  next
    have "tokenDepositState contractsD tokenDepositAddress \<noteq> None"
      using \<open>callDeposit contracts tokenDepositAddress block msg ID token amount = (Success, contractsD)\<close>
      using callDepositE by blast
    then have "tokenDepositState contractsD' tokenDepositAddress \<noteq> None"
      using \<open>reachableFrom contractsD contractsD' steps\<close>
      using reachableFromTokenDepositState by blast
    then show "tokenDepositState contractsD' tokenDepositAddress = Some (the (tokenDepositState contractsD' tokenDepositAddress))"
      by simp
  next
    show "getDeposit (the (tokenDepositState contractsD' tokenDepositAddress)) ID = hash3 (sender msg) token amount"
    proof (rule reachableFromGetDepositBridgeNotDead)
      show "reachableFrom contractsD contractsD' steps" 
        by fact
    next
      show "hash3 (sender msg) token amount \<noteq> 0"
        by fact
    next
      show "getDeposit (the (tokenDepositState contractsD tokenDepositAddress)) ID = hash3 (sender msg) token amount"
        using callDepositWritesHash assms
        by blast
    next
      show "\<not> bridgeDead contractsD' tokenDepositAddress"
        using assms
        by simp
    qed
  qed

  have "bridgeState contractsU bridgeAddress \<noteq> None"
    using reachableFromBridgeState assms
    unfolding properSetup_def
    by (auto simp add: Let_def)
  then have "bridgeState contractsU' bridgeAddress \<noteq> None"
    using \<open>reachableFrom contractsU contractsU' steps'\<close> reachableFromBridgeState
    by blast
  then obtain stateBridgeU' where 
    "bridgeState contractsU' bridgeAddress = Some stateBridgeU'"
    by auto
  then have stateBridgeU: "stateBridgeU' = the (bridgeState contractsU' bridgeAddress)"
    using \<open>bridgeState contractsU bridgeAddress \<noteq> None\<close>
    by auto

  have "stateOracleAddressTD contractsU tokenDepositAddress = stateOracleAddress"
    using assms stateOracleAddress_def properSetup_def
    by (auto simp add: Let_def)
  then have "stateOracleAddressTD contractsU' tokenDepositAddress = stateOracleAddress"
    using \<open>reachableFrom contractsU contractsU' steps'\<close> reachableFromDepositStateOracle by blast

  have "BridgeState.stateOracle stateBridgeU' = stateOracleAddress"
       "BridgeState.proofVerifier stateBridgeU' = proofVerifierAddress"
       "BridgeState.deposit stateBridgeU' = tokenDepositAddress"
       "tokenPairsState contractsU' (BridgeState.tokenPairs stateBridgeU') \<noteq> None"
    using assms stateBridgeU \<open>bridgeState contractsU bridgeAddress \<noteq> None\<close> properSetup_def stateOracleAddress_def proofVerifierAddress_def
    by (auto simp add: Let_def)

  then obtain stateTokenPairs where
    stateTokenPairs: "tokenPairsState contractsU' (BridgeState.tokenPairs stateBridgeU') = Some stateTokenPairs"
    by auto

  have "StateOracleState.lastState (the (stateOracleState contractsU stateOracleAddress)) = stateRoot"
    using assms \<open>stateOracleAddressTD contractsU tokenDepositAddress = stateOracleAddress\<close>
    unfolding stateRoot_def
    by (simp add: updateSuccess)
  then have "StateOracleState.lastState (the (stateOracleState contractsU' stateOracleAddress)) = stateRoot"
    using \<open>reachableFrom contractsU contractsU' steps'\<close> noUpdates
    using  \<open>stateOracleAddressTD contractsU tokenDepositAddress = stateOracleAddress\<close> 
    by (metis  noUpdateLastState)

  have "fst (callClaim contractsU' bridgeAddress msg' ID token amount proof) = Success"
  proof (rule callClaimI)
    show "bridgeState contractsU' bridgeAddress = Some stateBridgeU'"
      by fact
  next
    show "verifyDepositProof () (BridgeState.deposit stateBridgeU') ID (hash3 (sender msg') token amount)  
          (StateOracleState.lastState (the (stateOracleState contractsU' (BridgeState.stateOracle stateBridgeU')))) proof"
      using \<open>BridgeState.deposit stateBridgeU' = tokenDepositAddress\<close>
      using \<open>bridgeState contractsU' bridgeAddress = Some stateBridgeU'\<close>
      using \<open>BridgeState.stateOracle stateBridgeU' = stateOracleAddress\<close>
      using \<open>StateOracleState.lastState (the (stateOracleState contractsU' stateOracleAddress)) = stateRoot\<close>
      using \<open>verifyDepositProof () tokenDepositAddress ID (hash3 (sender msg) token amount) stateRoot proof = True\<close>
      using \<open>sender msg' = sender msg\<close>
      by simp
  next
    show "tokenPairsState contractsU' (BridgeState.tokenPairs stateBridgeU') = Some stateTokenPairs"
      using \<open>bridgeState contractsU' bridgeAddress = Some stateBridgeU'\<close>
            \<open>tokenPairsState contractsU' (BridgeState.tokenPairs stateBridgeU') = Some stateTokenPairs\<close> 
      by auto
  next
    show "stateOracleState contractsU' (BridgeState.stateOracle stateBridgeU') =
          Some (the (stateOracleState contractsU' (BridgeState.stateOracle stateBridgeU')))"
      using assms
      by (metis callDepositProperSetup callUpdateProperSetup option.collapse properSetupReachable properSetup_def stateBridgeU)
  next
    show "proofVerifierState contractsU' (BridgeState.proofVerifier stateBridgeU') \<noteq> None"
      using \<open>BridgeState.proofVerifier stateBridgeU' = proofVerifierAddress\<close> 
            stateBridgeU 
      using assms
      using callDepositIProofVerifier callUpdateIProofVerifier reachableFromIProofVerifier
      unfolding proofVerifierAddress_def properSetup_def
      by metis
  next
    show "getMinted stateTokenPairs token \<noteq> 0"
      using stateTokenPairs assms stateBridgeU
      unfolding properToken_def
      by (auto simp add: Let_def)
  next
    show "ERC20state contractsU' (getMinted stateTokenPairs token) \<noteq> None"
      using assms
      unfolding properToken_def
      by (smt (verit, ccfv_SIG) assms(2) callDepositProperToken callUpdateIBridge callUpdateIERC20 callUpdateITokenPairs option.sel properToken_def reachableFromBridgeTokenPairs reachableFromERC20State reachableFromITokenPairs stateBridgeU stateTokenPairs)
  next
    show "getClaim stateBridgeU' ID = False"
      using \<open>bridgeState contractsU' bridgeAddress = Some stateBridgeU'\<close> assms 
      by auto
  qed
  then show ?thesis 
    unfolding Let_def proof_def
    by (metis eq_fst_iff)
qed

(* ------------------------------------------------------------------------------------ *)

text \<open>If claim succeeds, then there must be a previous deposit transaction hash written in the deposits array\<close>
lemma callClaimGetDeposit:
  \<comment> \<open>starting from a properly configured state\<close>
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  \<comment> \<open>the last update that happened\<close>
  assumes update:
          "let stateOracleAddress = stateOracleAddressB contracts bridgeAddress
            in callUpdate contracts stateOracleAddress block blockNum stateRoot = (Success, contracts')"
  \<comment> \<open>there were no updates since then\<close>
  assumes "reachableFrom contracts' contracts'' steps'"
  assumes noUpdate:
          "let stateOracleAddress = stateOracleAddressB contracts bridgeAddress
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"

  \<comment> \<open>claim succeded\<close>
  assumes claim: "callClaim contracts'' bridgeAddress msg ID token amount proof = (Success, contracts''')"

  shows "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = hash3 (sender msg) token amount"
proof-
  define stateBridge where "stateBridge = the (bridgeState contracts'' bridgeAddress)"
  define stateStateOracle where "stateStateOracle = the (stateOracleState contracts'' (BridgeState.stateOracle stateBridge))"
  define stateTokenDeposit where "stateTokenDeposit = the (tokenDepositState contracts'' tokenDepositAddress)"

  have dB: "BridgeState.deposit stateBridge = tokenDepositAddress"
    using assms
    unfolding stateBridge_def properSetup_def Let_def
    by auto

  have sOB: "BridgeState.stateOracle stateBridge = stateOracleAddressB contracts bridgeAddress"
    using assms
    unfolding stateBridge_def
    by simp

  have "properSetup contracts' tokenDepositAddress bridgeAddress"
    using assms
    by (meson callUpdateProperSetup properSetupReachable)

  obtain stateRoot where stateLast: "callLastState contracts'' (BridgeState.stateOracle stateBridge) = (Success, stateRoot)"
    using claim
    by (metis callClaimCallLastState stateBridge_def)
  then have 1: "StateOracleState.lastState stateStateOracle = stateRoot"
    unfolding stateStateOracle_def
    using callLastState 
    by blast
  then have "getLastStateB contracts'' bridgeAddress = stateRoot"
    using stateBridge_def stateStateOracle_def by blast
  then have "getLastStateB contracts' bridgeAddress = stateRoot"
    using \<open>reachableFrom contracts' contracts'' steps'\<close> noUpdate
    using reachableFromBridgeStateOracle
    using noUpdateLastState sOB
    by (metis stateBridge_def)

  have "callVerifyDepositProof contracts'' (BridgeState.proofVerifier stateBridge) (BridgeState.deposit stateBridge) ID (hash3 (sender msg) token amount)
         stateRoot proof = Success"
    using callClaimCallVerifyProof[OF claim] 1
    unfolding stateBridge_def Let_def stateStateOracle_def
    by blast
  then have *: "verifyDepositProof () (BridgeState.deposit stateBridge) ID (hash3 (sender msg) token amount) stateRoot proof = True"
    unfolding callVerifyDepositProof_def
    by (simp split: option.splits if_split_asm)
  show "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID =
        hash3 (sender msg) token amount"
  proof (rule verifyDepositProofE[OF _  *])
    show "generateStateRoot contracts = stateRoot"
      using updateSuccess update
      using \<open>getLastStateB contracts' bridgeAddress = stateRoot\<close> by auto
  next
    show "tokenDepositState contracts (BridgeState.deposit stateBridge) =
          Some (the (tokenDepositState contracts' tokenDepositAddress))"
      using \<open>properSetup contracts' tokenDepositAddress bridgeAddress\<close> 
      by (metis callUpdateITokenDeposit dB option.collapse properSetup_def update)
  qed
qed

text \<open>Before every successful claim, a deposit must have been made\<close>
theorem depositBeforeClaim:
  \<comment> \<open>The operation starts from an initial state that is properly setup, but all data is still empty\<close>
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress"
  assumes "getDeposit (the (tokenDepositState initContracts tokenDepositAddress)) ID = 0"
  assumes "getLastStateB initContracts bridgeAddress = 0"

  \<comment> \<open>From the initial state, the state in which claim is successful is reached\<close>
  assumes "reachableFrom initContracts contracts steps"
  \<comment> \<open>There has been at least one state update\<close>
  assumes update:
          "let stateOracleAddress = stateOracleAddressB initContracts bridgeAddress
            in UPDATE stateOracleAddress stateRoot \<in> set steps"
  \<comment> \<open>Claim was successful\<close>
  assumes "callClaim contracts bridgeAddress msg ID token amount proof = (Success, contracts')"

  (* NOTE: additional assumptions *)
  \<comment> \<open>Updates never set zero state root\<close>
  assumes "updatesNonZero steps"
  \<comment> \<open>hash of the transaction is non-zero\<close>
  assumes "hash3 (sender msg) token amount \<noteq> 0"
  \<comment> \<open>hash function is injective\<close>
  assumes hash3_inj

  \<comment> \<open>The correct deposit must have happened\<close>
  shows "DEPOSIT tokenDepositAddress (sender msg) ID token amount \<in> set steps"
proof-
  define stateOracleAddress where "stateOracleAddress = stateOracleAddressB initContracts bridgeAddress"

  have "lastState (the (stateOracleState contracts stateOracleAddress)) \<noteq> 0"
    using \<open>reachableFrom initContracts contracts steps\<close> update \<open>updatesNonZero steps\<close> 
    using lastStateNonZero stateOracleAddress_def
    by force

  moreover

  have "lastState (the (stateOracleState initContracts stateOracleAddress)) = 0"
    using assms lastStateNonZero stateOracleAddress_def
    by force

  ultimately 

  obtain contractsU contractsU' block blockNum steps1 steps2 stateRoot' where
    "reachableFrom initContracts contractsU steps1"
    "stateRoot' = generateStateRoot contractsU"
    "callUpdate contractsU stateOracleAddress block blockNum stateRoot' = (Success, contractsU')"
    "reachableFrom contractsU' contracts steps2"
    "\<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps2"
    "set steps1 \<subseteq> set steps"
    using lastUpdateHappened[OF \<open>reachableFrom initContracts contracts steps\<close>, of stateOracleAddress]
    by auto
  
  then have "getDeposit (the (tokenDepositState contractsU tokenDepositAddress)) ID = hash3 (sender msg) token amount"
    using assms callClaimGetDeposit 
    by (smt (verit, best) reachableFromBridgeStateOracle callUpdateITokenDeposit properSetupReachable stateOracleAddress_def)
  then show ?thesis
    using hashWrittenOnlyByDeposit
    using assms 
    using \<open>reachableFrom initContracts contractsU steps1\<close> \<open>set steps1 \<subseteq> set steps\<close> by blast
qed

(* ------------------------------------------------------------------------------------ *)

text \<open>Only user who made the deposit can make a successful claim with the same ID\<close>

lemma onlyDepositorCanClaim:
  \<comment> \<open>deposit is done a properly configured state state\<close>
  assumes "properSetup contractsD tokenDepositAddress bridgeAddress"
  assumes deposit: "callDeposit contractsD tokenDepositAddress block msg ID token amount = (Success, contractsD')"
  (* FIXME: amount must be the same as the value of the message - this assumption can be removed when the definition of executeStep is changed *)
  assumes "val msg = amount"

  \<comment> \<open>in some state after the deposit a state oracle update is made\<close>
  assumes "reachableFrom contractsD' contractsU steps2"
  assumes update: "callUpdate contractsU (stateOracleAddressB contractsU bridgeAddress) block blockNum stateRoot = (Success, contractsU')"

  \<comment> \<open>in some state after the update a successfull claim is made with the same ID\<close>
  assumes "reachableFrom contractsU' contractsC steps3"
  assumes claim: "callClaim contractsC bridgeAddress msg' ID token' amount' proof = (Success, contractsC')"

  (* NOTE: additional assumptions *)
  \<comment> \<open>transaction hashes are not zero\<close>
  assumes "hash3 (sender msg) token amount \<noteq> 0"
  assumes "hash3 (sender msg') token' amount' \<noteq> 0"
  \<comment> \<open>the hash function is injective\<close>
  assumes hash3_inj

  shows "sender msg = sender msg'" "token = token'" "amount = amount'"
proof-
  have "getDeposit (the (tokenDepositState contractsD' tokenDepositAddress)) ID = hash3 (sender msg) token amount"
    using callDepositWritesHash deposit
    by simp

  define stateOracleAddress where "stateOracleAddress = stateOracleAddressB contractsD bridgeAddress"

  let ?d = "DEPOSIT tokenDepositAddress (sender msg) ID token amount"
  let ?u = "UPDATE stateOracleAddress stateRoot"
  let ?steps = "steps2 @ [?d]"

  obtain contractsUx contractsU'x blockx blockNumx steps1x steps2x stateRootx where
    "reachableFrom contractsD' contractsUx steps1x"
    "stateRootx = generateStateRoot contractsUx"
    "callUpdate contractsUx stateOracleAddress blockx blockNumx stateRootx = (Success, contractsU'x)"
    "reachableFrom contractsU'x contractsC steps2x"
    "\<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps2x"
    using lastUpdateHappened'[of contractsD' contractsU _ stateOracleAddress block blockNum stateRoot contractsU' contractsC steps3] update
    using \<open>reachableFrom contractsD' contractsU steps2\<close>
    using \<open>reachableFrom contractsU' contractsC steps3\<close>
    by (metis callDepositIBridge deposit reachableFromBridgeStateOracle stateOracleAddress_def)

  have "getDeposit (the (tokenDepositState contractsU'x tokenDepositAddress)) ID = hash3 (sender msg') token' amount'"
  proof (rule callClaimGetDeposit)
    show "callClaim contractsC bridgeAddress msg' ID token' amount' proof = (Success, contractsC')"
      by fact
  next
    show "let stateOracleAddress = stateOracleAddressB contractsUx bridgeAddress
           in callUpdate contractsUx stateOracleAddress blockx blockNumx stateRootx =
              (Success, contractsU'x)"
      using \<open>callUpdate contractsUx stateOracleAddress blockx blockNumx stateRootx = (Success, contractsU'x)\<close>
      using \<open>reachableFrom contractsD' contractsUx steps1x\<close>
      by (metis Hash.callDepositIBridge deposit reachableFromBridgeStateOracle stateOracleAddress_def)
  next
    show "properSetup contractsUx tokenDepositAddress bridgeAddress"
      using \<open>reachableFrom contractsD' contractsUx steps1x\<close> 
      using \<open>properSetup contractsD tokenDepositAddress bridgeAddress\<close> 
      using properSetupReachable callDepositProperSetup deposit
      by blast
  next
    show "reachableFrom contractsU'x contractsC steps2x"
      by fact
  next
    show "let stateOracleAddress = stateOracleAddressB contractsUx bridgeAddress
           in \<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps2x"
      using \<open>\<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps2x\<close>
             \<open>reachableFrom contractsD' contractsUx steps1x\<close> stateOracleAddress_def
      by (metis callDepositIBridge deposit reachableFromBridgeStateOracle)
  qed

  have "hash3 (sender msg) token amount = hash3 (sender msg') token' amount'"
    using reachableFromGetDeposit
    using \<open>getDeposit (the (tokenDepositState contractsD' tokenDepositAddress)) ID = hash3 (sender msg) token amount\<close> \<open>getDeposit (the (tokenDepositState contractsU'x tokenDepositAddress)) ID = hash3 (sender msg') token' amount'\<close>
    using \<open>callUpdate contractsUx stateOracleAddress blockx blockNumx stateRootx = (Success, contractsU'x)\<close>
    using \<open>hash3 (sender msg) token amount \<noteq> 0\<close>  \<open>hash3 (sender msg') token' amount' \<noteq> 0\<close>
    using \<open>reachableFrom contractsD' contractsUx steps1x\<close>
    by (metis callUpdateITokenDeposit)

  then show "sender msg = sender msg'" "token = token'" "amount = amount'"
    using \<open>hash3_inj\<close>
    unfolding hash3_inj_def
    by metis+
qed

(* ------------------------------------------------------------------------------------ *)

text \<open>Cancel deposit can succeed only if there was a previous successful deposit with the same ID\<close>
theorem cancelDepositOnlyAfterDeposit:
  \<comment> \<open>contracts start working from a properly setup initial state\<close>
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress"
  assumes "getDeposit (the (tokenDepositState initContracts tokenDepositAddress)) ID = 0"

  \<comment> \<open>at some later state cancel deposit succeeded\<close>
  assumes "reachableFrom initContracts contracts steps"
  assumes cancel: "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof = (Success, contracts')"

  (* NOTE: additional assumptions *)
  \<comment> \<open>hash value of the transaction is not zero\<close>
  assumes "hash3 (sender msg) token amount \<noteq> 0"
  \<comment> \<open>the hash function is injective\<close>
  assumes hash3_inj

  \<comment> \<open>there must had been a previous deposit with the same ID\<close>
  shows "DEPOSIT tokenDepositAddress (sender msg) ID token amount \<in> set steps"
proof-
  have "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = hash3 (sender msg) token amount"
    using cancel
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
    by (simp add: Let_def split: option.splits prod.splits if_split_asm)
  then show ?thesis
    using assms hashWrittenOnlyByDeposit
    by blast
qed

text \<open>When the bridge dies the dead state is set to the state root set in the last update\<close>
lemma deadStateLastState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  assumes noUpdate:
          "let stateOracleAddress = stateOracleAddressB contracts bridgeAddress
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps"
  assumes "\<not>bridgeDead contracts tokenDepositAddress"
  assumes "bridgeDead contracts' tokenDepositAddress"
  assumes "let stateOracleAddress = stateOracleAddressB contracts bridgeAddress
            in callLastState contracts stateOracleAddress = (Success, stateRoot)"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = stateRoot"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by blast
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0")
    case True
    then show ?thesis
      using reachableFrom_step
      apply (cases step)
      apply (metis callDepositInDeadState executeStep.simps(1) list.set_intros(2))
      apply simp
      apply (metis callUpdateDeadState executeStep.simps(3) list.set_intros(2))
      apply (metis callCancelDepositWhileDeadInDeadState executeStep.simps(4) list.set_intros(2))
      apply (metis callWithdrawWhileDeadInDeadState executeStep.simps(5) list.set_intros(2))
      done
  next
    case False
    show ?thesis
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' = tokenDepositAddress")
        case False
        then show ?thesis
          using reachableFrom_step
          by (metis DEPOSIT callDepositOtherAddress executeStep.simps(1) list.set_intros(2))
      next
        case True
        show ?thesis
        proof (rule callDepositSetsDeadState)
          show "getLastStateTD contracts' tokenDepositAddress = stateRoot"
            using reachableFrom_step.prems reachableFrom_step.hyps
            by (smt (verit, ccfv_threshold) noUpdateLastState callLastState callLastStateI list.set_intros(2) prod.exhaust_sel properSetupReachable properSetup_def reachableFromBridgeStateOracle)
        next
          show "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) \<noteq> 0"
            by fact
        next
          show "callDeposit contracts' tokenDepositAddress block (message caller' amount') ID' token' amount' =
                (Success, contracts'')"
            using reachableFrom_step DEPOSIT \<open>address' = tokenDepositAddress\<close>
            by simp
        qed
      qed
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        by simp
    next
      case (UPDATE address' stateRoot')
      then show ?thesis
        using reachableFrom_step
        by (metis False callUpdateDeadState executeStep.simps(3))
    next
      case (CANCEL address' caller' ID' token' amount' proof')
      show ?thesis
      proof (cases "address' = tokenDepositAddress")
        case False
        then show ?thesis
          using reachableFrom_step
          by (metis CANCEL callCancelDepositWhileDeadOtherAddress executeStep.simps(4) list.set_intros(2))
      next
        case True
        have "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) = getLastStateTD contracts' tokenDepositAddress"
        proof (rule callCancelDepositWhileDeadSetsDeadState)
          show "\<not> bridgeDead contracts' tokenDepositAddress"
            by fact
        next
          show "callCancelDepositWhileDead contracts' tokenDepositAddress (message caller' 0) block ID' token' amount' proof' =
               (Success, contracts'')"
            using CANCEL reachableFrom_step.prems reachableFrom_step.hyps True
            by auto
        qed
        then show ?thesis
          using reachableFrom_step.prems reachableFrom_step.hyps
          by (smt (verit, ccfv_threshold) noUpdateLastState callLastState callLastStateI list.set_intros(2) prod.exhaust_sel properSetupReachable properSetup_def reachableFromBridgeStateOracle)
      qed
    next
      case (WITHDRAW address' caller' token' amount' proof')
      show ?thesis
      proof (cases "address' = tokenDepositAddress")
        case False
        then show ?thesis
          using reachableFrom_step
          by (metis callWithdrawWhileDeadOtherAddress WITHDRAW executeStep.simps(5) list.set_intros(2))
      next
        case True
        have "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) = getLastStateTD contracts' tokenDepositAddress"
        proof (rule callWithdrawWhileDeadSetsDeadState)
          show "\<not> bridgeDead contracts' tokenDepositAddress"
            by fact
        next
          show "callWithdrawWhileDead contracts' tokenDepositAddress (message caller' 0) block token' amount' proof' =
               (Success, contracts'')"
            using WITHDRAW reachableFrom_step.prems reachableFrom_step.hyps True
            by auto
        qed
        then show ?thesis
          using reachableFrom_step.prems reachableFrom_step.hyps
          by (smt (verit, ccfv_threshold) noUpdateLastState callLastState callLastStateI list.set_intros(2) prod.exhaust_sel properSetupReachable properSetup_def reachableFromBridgeStateOracle)
      qed
    qed
  qed
qed

lemma deadStateLastStateRoot:
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress"
  assumes "reachableFrom initContracts contracts steps"
  \<comment> \<open>The last update that happened when the bridge was still alive\<close>
  assumes update:
          "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in callUpdate contracts stateOracleAddress block blockNum stateRoot = (Success, contracts')"
  assumes "stateRoot \<noteq> 0" (* NOTE: additional assumption *)
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) = 0"
  \<comment> \<open>There were no updates since then\<close>
  assumes "reachableFrom contracts' contracts'' steps'"
  assumes noUpdate: "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"
  \<comment> \<open>The bridge is dead\<close>
  assumes status: "let stateTokenDeposit = the (tokenDepositState contracts'' tokenDepositAddress)
                    in getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')"

  shows "generateStateRoot contracts = deadState stateTokenDeposit'"
proof-
  define stateBridge where "stateBridge = the (bridgeState contracts'' bridgeAddress)"
  define stateStateOracle where "stateStateOracle = the (stateOracleState contracts'' (BridgeState.stateOracle stateBridge))"
  define stateTokenDeposit where "stateTokenDeposit = the (tokenDepositState contracts'' tokenDepositAddress)"
  define stateERC20 where "stateERC20 = the (ERC20state contracts' token)"

  have sOB: "BridgeState.stateOracle stateBridge = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))"
    using assms
    unfolding stateBridge_def
    by simp

  have "properSetup contracts' tokenDepositAddress bridgeAddress"
    using assms
    by (meson callUpdateProperSetup properSetupReachable)

  from update have "generateStateRoot contracts = stateRoot"
    using updateSuccess
    by simp

  have "lastState stateStateOracle = stateRoot"
    using assms
    by (metis (no_types, lifting) callUpdateLastState noUpdateLastState sOB stateStateOracle_def)
  then have "getLastStateB contracts'' bridgeAddress = stateRoot"
    using stateBridge_def stateStateOracle_def
    by argo
  then have "getLastStateTD contracts'' tokenDepositAddress = stateRoot"
    using assms properSetup_stateOracleAddress update
    by auto

  have "deadState stateTokenDeposit' = stateRoot"
  proof (cases "bridgeDead contracts'' tokenDepositAddress")
    case True 
    have "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) = stateRoot"
    proof (rule deadStateLastState)
      show "reachableFrom contracts' contracts'' steps'"
        by fact
    next
      show "properSetup contracts' tokenDepositAddress bridgeAddress" 
        by fact 
    next
      show "let stateOracleAddress = stateOracleAddressB contracts' bridgeAddress
             in \<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"
        using \<open>reachableFrom contracts' contracts'' steps'\<close>
        by (metis noUpdate reachableFromBridgeStateOracle sOB stateBridge_def)
    next
      show "\<not> bridgeDead contracts' tokenDepositAddress"
        using \<open>deadState (the (tokenDepositState contracts tokenDepositAddress)) = 0\<close> update
        using callUpdateDeadState
        by presburger
    next
      show "bridgeDead contracts'' tokenDepositAddress"
        by fact
    next
      show "let stateOracleAddress = stateOracleAddressB contracts' bridgeAddress
             in callLastState contracts' stateOracleAddress = (Success, stateRoot)"
        using \<open>properSetup contracts' tokenDepositAddress bridgeAddress\<close> 
              \<open>reachableFrom contracts' contracts'' steps'\<close>
        by (smt (verit, best) callLastState_def callUpdateLastState option.case_eq_if properSetup_def reachableFromBridgeStateOracle sOB stateBridge_def update)
    qed
    then show ?thesis
      using \<open>stateRoot \<noteq> 0\<close> 
      using getDeadStatusInDeadState status
      unfolding Let_def stateTokenDeposit_def
      by blast
  next
    case False
    then have "deadState stateTokenDeposit' = stateRoot"
      using getDeadStatusSetsDeadState status
      using \<open>getLastStateTD contracts'' tokenDepositAddress = stateRoot\<close>
      unfolding stateTokenDeposit_def
      by fastforce
    then show ?thesis
      by simp
  qed

  then show ?thesis
    using \<open>generateStateRoot contracts = stateRoot\<close>
    by simp
qed


text \<open>If cancel deposit succeeds, then the bridge is dead and 
      there was no claim previous to the state in which the bridge died\<close>
theorem cancelDepositNoClaim:
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress"
  assumes "reachableFrom initContracts contracts steps"
  \<comment> \<open>The last update that happened when the bridge was still alive\<close>
  assumes update:
          "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in callUpdate contracts stateOracleAddress block blockNum stateRoot = (Success, contracts')"
  assumes "stateRoot \<noteq> 0" (* NOTE: additional assumption *)
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) = 0"
  \<comment> \<open>There were no updates since then\<close>
  assumes "reachableFrom contracts' contracts'' steps'"
  assumes noUpdate: "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"
  \<comment> \<open>Cancel deposit succeded\<close>
  assumes cancel:
          "callCancelDepositWhileDead contracts'' tokenDepositAddress msg block' ID token amount proof = (Success, contracts''')"
  \<comment> \<open>Claim did not happen before that last update\<close>
  shows "\<nexists> proof. CLAIM bridgeAddress (sender msg) ID token amount proof \<in> set steps"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain p where *: "CLAIM bridgeAddress (sender msg) ID token amount p \<in> set steps"
    by auto
  have "getClaim (the (bridgeState contracts bridgeAddress)) ID = True"
    using \<open>reachableFrom initContracts contracts steps\<close> *
    by (simp add: claimStepSetsClaim)

  moreover

  define stateTokenDeposit where "stateTokenDeposit = the (tokenDepositState contracts'' tokenDepositAddress)"
  define stateTokenDeposit' where "stateTokenDeposit' = snd (snd (getDeadStatus contracts'' stateTokenDeposit block'))"
  define stateBridge where "stateBridge = the (bridgeState contracts'' bridgeAddress)"

  have bD: "TokenDepositState.bridge stateTokenDeposit = bridgeAddress"
    using assms
    unfolding stateTokenDeposit_def
    by (meson callUpdateProperSetup properSetupReachable properSetup_def)

  have status: "getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')" 
    using cancel
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def stateTokenDeposit_def stateTokenDeposit'_def lastValidState_def
    by (simp add: Let_def split: option.splits prod.splits if_split_asm)

  then have lVS: "lastValidState contracts'' stateTokenDeposit' = (Success, deadState stateTokenDeposit')" 
    using cancel
    using callLastState getDeadStatusTrueDeadState assms
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def stateTokenDeposit_def stateTokenDeposit'_def lastValidState_def
    by (smt (verit, ccfv_SIG) deadStateLastStateRoot noUpdate update updateSuccess)
    
  then have vCP: "callVerifyClaimProof contracts'' (TokenDepositState.proofVerifier stateTokenDeposit') (bridge stateTokenDeposit') ID
                  (deadState stateTokenDeposit') proof = Success"
    using cancel
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def stateTokenDeposit_def stateTokenDeposit'_def lastValidState_def
    by (simp add: Let_def split: option.splits prod.splits if_split_asm)
    
  have "generateStateRoot contracts = deadState stateTokenDeposit'"
    using assms status
    by (metis deadStateLastStateRoot stateTokenDeposit_def)
 
  from update have "generateStateRoot contracts = stateRoot"
    using updateSuccess
    by simp

  have "getClaim (the (bridgeState contracts bridgeAddress)) ID = False"
  proof (rule verifyClaimProofE)
    show "generateStateRoot contracts = stateRoot"
      by fact
  next
    show "verifyClaimProof () bridgeAddress ID stateRoot proof = True"
      using status vCP bD \<open>generateStateRoot contracts = deadState stateTokenDeposit'\<close> \<open>generateStateRoot contracts = stateRoot\<close> 
      unfolding callVerifyClaimProof_def stateTokenDeposit'_def stateTokenDeposit_def
      by (auto split: option.splits prod.splits if_split_asm)
  next
    have "bridgeState contracts bridgeAddress \<noteq> None"
      using assms
      by (meson \<open>reachableFrom initContracts contracts steps\<close> properSetup_def reachableFromBridgeState)
    then show "bridgeState contracts bridgeAddress = Some (the (bridgeState contracts bridgeAddress))"
      by simp
  qed

  ultimately

  show False
    by simp
qed


text \<open>If withdrawal succeeds, then the bridge is dead and 
      the user had the exact amount of tokens in the state in which the bridge died\<close>
theorem withdrawSufficientBalance:
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress"
  assumes "properToken initContracts tokenDepositAddress bridgeAddress token"
  assumes "reachableFrom initContracts contracts steps"
  \<comment> \<open>The last update that happened when the bridge was still alive\<close>
  assumes update:
          "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in callUpdate contracts stateOracleAddress block blockNum stateRoot = (Success, contracts')"
  assumes "stateRoot \<noteq> 0" (* NOTE: additional assumption *)
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) = 0"
  \<comment> \<open>There were no updates since then\<close>
  assumes "reachableFrom contracts' contracts'' steps'"
  assumes noUpdate: "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"
  \<comment> \<open>Withdraw succeded\<close>
  assumes withdraw:
          "callWithdrawWhileDead contracts'' tokenDepositAddress msg block' token amount proof = (Success, contracts''')"
  \<comment> \<open>Caller had sufficient balance\<close>
  shows "callBalanceOf contracts token (sender msg) = (Success, amount)"
proof-
  have "properSetup contracts' tokenDepositAddress bridgeAddress"
    using assms
    by (meson callUpdateProperSetup properSetupReachable)

  have "properToken contracts' tokenDepositAddress bridgeAddress token"
    using assms
    by (meson callUpdateProperToken properTokenReachable)

  from update have "generateStateRoot contracts = stateRoot"
    using updateSuccess
    by simp

  define stateTokenDeposit where "stateTokenDeposit = the (tokenDepositState contracts'' tokenDepositAddress)"
  define stateTokenDeposit' where "stateTokenDeposit' = snd (snd (getDeadStatus contracts'' stateTokenDeposit block'))"
  define stateERC20 where "stateERC20 = the (ERC20state contracts' token)"
 
  have status: "getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')" and
       vCP: "callVerifyBalanceProof contracts'' (TokenDepositState.proofVerifier stateTokenDeposit') token (sender msg) amount
             (deadState stateTokenDeposit') proof = Success"
    using withdraw
    unfolding stateTokenDeposit_def stateTokenDeposit'_def
    unfolding callWithdrawWhileDead_def withdrawWhileDead_def
    by (simp_all add: Let_def split: option.splits prod.splits if_split_asm)

  have "generateStateRoot contracts = deadState stateTokenDeposit'"
    using assms status
    by (metis deadStateLastStateRoot stateTokenDeposit_def)

  have "ERC20state contracts token \<noteq> None"
    using \<open>properToken contracts' tokenDepositAddress bridgeAddress token\<close> update
    by (metis callUpdateIERC20 properToken_def)

  have "balanceOf (the (ERC20state contracts token)) (sender msg) = amount"
  proof (rule verifyBalanceProofE)
    show "verifyBalanceProof () token (sender msg) amount stateRoot proof = True"
      using vCP \<open>generateStateRoot contracts = stateRoot\<close> \<open>generateStateRoot contracts = deadState stateTokenDeposit'\<close>
      unfolding callVerifyBalanceProof_def
      by (simp split: option.splits if_split_asm)
  next
    show "generateStateRoot contracts = stateRoot"
      by fact
  next
    show "ERC20state contracts token = Some (the (ERC20state contracts token))"
      using \<open>ERC20state contracts token \<noteq> None\<close>
      by simp
  qed
  then show ?thesis
    using \<open>ERC20state contracts token \<noteq> None\<close>
    unfolding callBalanceOf_def
    by (auto split: option.splits)
qed


text \<open>If the user had some amount of tokens in the state in which the bridge died, 
      he can withdraw that amount\<close>
theorem sufficientBalanceCanWithdraw:
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress"
  assumes "properToken initContracts tokenDepositAddress bridgeAddress token"

  assumes "reachableFrom initContracts contracts steps"
  \<comment> \<open>The last update that happened when the bridge was still alive\<close>
  assumes update:
          "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in callUpdate contracts stateOracleAddress block blockNum stateRoot = (Success, contracts')"
  assumes "stateRoot \<noteq> 0" (* NOTE: additional assumption *)
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) = 0"
  \<comment> \<open>There were no updates since then\<close>
  assumes "reachableFrom contracts' contracts'' steps'"
  assumes noUpdate: "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"
  \<comment> \<open>Caller had sufficient balance\<close>
  assumes "callBalanceOf contracts token (sender msg) = (Success, amount)"

  \<comment> \<open>Caller has not yet withdrawn his balance\<close>
  assumes notWithdrawn: "getTokenWithdrawn (the (tokenDepositState contracts'' tokenDepositAddress)) (hash2 (sender msg) token) = False"

  \<comment> \<open>The bridge is dead\<close>
  assumes dead: "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) \<noteq> 0"

  \<comment> \<open>Sender is not the bridge itself\<close>
  assumes "tokenDepositAddress \<noteq> sender msg"

  \<comment> \<open>Withdraw succedes\<close>
  shows "fst (callWithdrawWhileDead contracts'' tokenDepositAddress msg block' token amount (generateBalanceProof contracts token (sender msg) amount)) = Success"
proof-
  define stateTokenDeposit where "stateTokenDeposit = the (tokenDepositState contracts'' tokenDepositAddress)"
  define stateTokenDeposit' where "stateTokenDeposit' = snd (snd (getDeadStatus contracts'' stateTokenDeposit block'))"

  have proper: "properSetup contracts tokenDepositAddress bridgeAddress"
               "properToken contracts tokenDepositAddress bridgeAddress token"
    using assms
    by (meson properSetupReachable, meson properTokenReachable)
  then have proper'': "properSetup contracts'' tokenDepositAddress bridgeAddress"
                      "properToken contracts'' tokenDepositAddress bridgeAddress token"
    using assms
    by (meson callUpdateProperSetup properSetupReachable update, meson callUpdateProperToken properTokenReachable update)

  have tds: "tokenDepositState contracts'' tokenDepositAddress \<noteq> None"
    using proper''
    by (metis properSetup_def)

  have dead: "getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')"
    using dead
    unfolding stateTokenDeposit_def stateTokenDeposit'_def
    unfolding getDeadStatus_def
    by auto

  have bp: "callVerifyBalanceProof contracts'' (TokenDepositState.proofVerifier stateTokenDeposit') token (sender msg) amount
            (deadState stateTokenDeposit') (generateBalanceProof contracts token (sender msg) amount) = Success"
  proof-
    have "verifyBalanceProof () token (sender msg) amount (deadState stateTokenDeposit') (generateBalanceProof contracts token (sender msg) amount) = True"
    proof (rule verifyBalanceProofI)
      show "generateBalanceProof contracts token (sender msg) amount = generateBalanceProof contracts token (sender msg) amount"
        by simp
    next
      show "generateStateRoot contracts = deadState stateTokenDeposit'"
        using assms
        by (metis dead deadStateLastStateRoot noUpdate stateTokenDeposit_def update)
    next
      show "ERC20state contracts token = Some (the (ERC20state contracts token))"
        using proper
        unfolding properToken_def Let_def
        by simp
    next
      show "balanceOf (the (ERC20state contracts token)) (sender msg) = amount"
        using \<open>callBalanceOf contracts token (sender msg) = (Success, amount)\<close>
        using callBalanceOf
        by blast
    qed
    moreover 
    have "proofVerifierState contracts'' (TokenDepositState.proofVerifier stateTokenDeposit) \<noteq> None"
      using proper''
      unfolding properSetup_def stateTokenDeposit_def
      by (simp add: Let_def)
    then have "proofVerifierState contracts'' (TokenDepositState.proofVerifier stateTokenDeposit') \<noteq> None"
      using dead getDeadStatusProofVerifier by presburger
    ultimately show ?thesis
      unfolding callVerifyBalanceProof_def
      by (auto split: option.splits)
  qed

  have transfer: "fst (callSafeTransferFrom contracts'' token tokenDepositAddress (sender msg) amount) = Success"
  proof (rule callSafeTransferFromI)
    show "ERC20state contracts'' token = Some (the (ERC20state contracts'' token))"
      using proper''
      by (metis option.collapse properToken_def)
  next
    show "tokenDepositAddress \<noteq> sender msg"
      by fact
  next
    show "amount \<le> balanceOf (the (ERC20state contracts'' token)) tokenDepositAddress"
      using \<open>callBalanceOf contracts token (sender msg) = (Success, amount)\<close>
      sorry      
  qed

  show ?thesis
    using tds dead bp transfer notWithdrawn
    unfolding callWithdrawWhileDead_def withdrawWhileDead_def
    unfolding stateTokenDeposit_def stateTokenDeposit'_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split)
qed

primrec DEPOSIT_amount where
  "DEPOSIT_amount (DEPOSIT address caller ID token amount) = amount"

primrec CLAIM_amount where
  "CLAIM_amount (CLAIM address caller ID token amount proof) = amount"

primrec WITHDRAW_amount where
  "WITHDRAW_amount (WITHDRAW address caller token amount proof) = amount"

primrec CANCEL_amount where
  "CANCEL_amount (CANCEL address caller ID token amount proof) = amount"

definition deposits where
  "deposits address token steps = 
   filter (\<lambda> step. case step of DEPOSIT address' caller ID token' amount \<Rightarrow> address = address' \<and> token = token' | _ \<Rightarrow> False) steps"

definition depositedAmount where
  "depositedAmount address token steps = 
   sum_list (map DEPOSIT_amount (deposits address token steps))"

lemma depositedAmountCons [simp]:
  shows "depositedAmount address token (DEPOSIT address caller ID token amount # steps) = 
         amount + depositedAmount address token steps"
  by (simp add: deposits_def depositedAmount_def)

lemma depositedAmountConsOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "depositedAmount address token (DEPOSIT address' caller ID token' amount # steps) = 
         depositedAmount address token steps"
  using assms
  by (auto simp add: deposits_def depositedAmount_def)

lemma depositedAmoutConsNonDeposit [simp]:
  assumes "\<nexists> address' caller' ID' token' amount'. step = DEPOSIT address' caller' ID' token' amount'"
  shows "depositedAmount address token (step # steps) = depositedAmount address token steps"
  using assms 
  unfolding depositedAmount_def deposits_def
  by (cases step, auto)



definition claims where 
  "claims address token steps = 
   filter (\<lambda> step. case step of CLAIM address' caller ID token' amount proof \<Rightarrow> address = address' \<and> token = token' | _ \<Rightarrow> False) steps"

definition claimedAmount where
  "claimedAmount address token steps = 
   sum_list (map CLAIM_amount (claims address token steps))"

lemma claimedAmoutConsNonClaim [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CLAIM address' caller' ID' token' amount' proof'"
  shows "claimedAmount address token (step # steps) = claimedAmount address token steps"
  using assms 
  unfolding claimedAmount_def claims_def
  by (cases step, auto)

definition withdrawals where
  "withdrawals address token steps = filter (\<lambda> step. case step of WITHDRAW address' caller token' amount proof \<Rightarrow> address = address' \<and> token = token' | _ \<Rightarrow> False) steps"

definition withdrawnAmount where
  "withdrawnAmount address token steps = 
   sum_list (map WITHDRAW_amount (withdrawals address token steps))"

lemma withdrawnAmoutConsNonWithdraw [simp]:
  assumes "\<nexists> address' caller' token' amount' proof'. step = WITHDRAW address' caller' token' amount' proof'"
  shows "withdrawnAmount address token (step # steps) = withdrawnAmount address token steps"
  using assms 
  unfolding withdrawnAmount_def withdrawals_def
  by (cases step, auto)

definition cancels where
  "cancels address token steps = 
   filter (\<lambda> step. case step of CANCEL address' caller ID token' amount proof \<Rightarrow> address = address' \<and> token = token' | _ \<Rightarrow> False) steps"

definition canceledAmount where
  "canceledAmount address token steps = 
   sum_list (map CANCEL_amount (cancels address token steps))"

lemma canceledAmountCancel [simp]:
  shows "canceledAmount address token (CANCEL address caller ID token amount proof # steps) = 
         amount + canceledAmount address token steps"
  unfolding canceledAmount_def cancels_def
  by auto

lemma canceledAmountConsNonCancel [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CANCEL address' caller' ID' token' amount' proof'"
  shows "canceledAmount address token (step # steps) = canceledAmount address token steps"
  using assms 
  unfolding canceledAmount_def cancels_def
  by (cases step, auto)

lemma canceledAmountConsOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "canceledAmount address token ((CANCEL address' caller' ID' token' amount' proof') # steps) = canceledAmount address token steps"
  using assms
  unfolding canceledAmount_def cancels_def
  by auto

primrec DEPOSIT_id where
  "DEPOSIT_id (DEPOSIT address caller ID token amount) = ID"

definition claimedDeposits where
  "claimedDeposits tokenDepositAddress bridgeAddress token steps = 
     filter (\<lambda> step. \<exists> caller' amount' proof'. CLAIM bridgeAddress caller' (DEPOSIT_id step) token amount' proof' \<in> set steps) (deposits tokenDepositAddress token steps)"

definition claimedDepositsAmount where
  "claimedDepositsAmount tokenDepositAddress bridgeAddress token steps = 
   sum_list (map DEPOSIT_amount (claimedDeposits tokenDepositAddress bridgeAddress token steps))"

lemma claimedDepositsAmountOther: 
  assumes "\<nexists> caller ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"
  shows "claimedDepositsAmount tokenDepositAddress bridgeAddress token (step # steps) =
         claimedDepositsAmount tokenDepositAddress bridgeAddress token steps"
proof-
  have "deposits tokenDepositAddress token (step # steps) = deposits tokenDepositAddress token steps"
    using assms
    unfolding deposits_def
    by (cases step, auto)
  then have "claimedDeposits tokenDepositAddress bridgeAddress token (step # steps) = 
             claimedDeposits tokenDepositAddress bridgeAddress token steps"
    using assms
    unfolding claimedDeposits_def
    by (smt (verit, del_insts) filter_cong list.set_intros(2) set_ConsD)
  then show ?thesis
    unfolding claimedDepositsAmount_def
    by simp
qed

lemma filter':
  assumes "filter P xs = ys1 @ [y] @ ys2" "y \<notin> set (ys1 @ ys2)"
  assumes "\<forall> x \<in> set xs. P x \<and> x \<noteq> y \<longleftrightarrow> P' x"
  shows "filter P' xs = ys1 @ ys2"
  using assms
proof-
  have "filter (\<lambda>x. x \<noteq> y) ys1 = ys1"
    using assms(2)
    by (induction ys1, auto)
  moreover
  have "filter (\<lambda>x. x \<noteq> y) ys2 = ys2"
    using assms(2)
    by (induction ys2, auto)
  moreover
  have "filter P' xs = filter (\<lambda>x. P x \<and> x \<noteq> y) xs"
  proof (rule filter_cong)
    fix x
    assume "x \<in> set xs" then 
    show "P' x \<longleftrightarrow> P x \<and> x \<noteq> y"
      using assms
      by simp
  qed simp
  then have "filter P' xs = filter (\<lambda> x. x \<noteq> y) (filter P xs)"
    by simp
  ultimately show ?thesis
    using assms \<open>y \<notin> set (ys1 @ ys2)\<close>
    by auto
qed

lemma claimedDepositAmountsClaim [simp]:
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress"
  assumes "properToken initContracts tokenDepositAddress bridgeAddress token"
  assumes "getDeposit (the (tokenDepositState initContracts tokenDepositAddress)) ID = 0"
  assumes "getLastStateB initContracts bridgeAddress = 0"
  assumes "let stateOracleAddress = stateOracleAddressB initContracts bridgeAddress
            in UPDATE stateOracleAddress stateRoot \<in> set steps"
  assumes "updatesNonZero steps"

  assumes "\<forall> step \<in> set steps. \<forall>caller' amount' ID' token'.
             step = DEPOSIT tokenDepositAddress caller' ID' token' amount' \<longrightarrow>
             hash3 caller' token' amount' \<noteq> 0"
  assumes "hash3 caller token amount \<noteq> 0"
  assumes "hash3_inj"

  assumes "reachableFrom initContracts contracts' (CLAIM bridgeAddress caller ID token amount proof' # steps)"
  shows   "claimedDepositsAmount tokenDepositAddress bridgeAddress token
             (CLAIM bridgeAddress caller ID token amount proof # steps) = 
           claimedDepositsAmount tokenDepositAddress bridgeAddress token steps + amount"
proof-  
  define CLAIM_step where 
  "CLAIM_step = CLAIM bridgeAddress caller ID token amount proof"
  define DEPOSIT_step where
  "DEPOSIT_step = DEPOSIT tokenDepositAddress caller ID token amount"
  define claimed where
  "claimed = claimedDeposits tokenDepositAddress bridgeAddress token (CLAIM_step # steps)"

  have deposits: "deposits tokenDepositAddress token (CLAIM_step # steps) = 
                  deposits tokenDepositAddress token steps"
    unfolding CLAIM_step_def
    by (simp add: local.deposits_def)

  obtain contracts'' where
     "reachableFrom initContracts contracts'' steps"
     "callClaim contracts'' bridgeAddress (message caller amount) ID token amount proof' = (Success, contracts')"
    using assms
    unfolding CLAIM_step_def
    by (smt (verit) executeStep.simps(2) list.discI list.inject reachableFrom.simps)
  then have "DEPOSIT_step \<in> set steps"
    using assms depositBeforeClaim
    unfolding DEPOSIT_step_def
    by (metis Message.select_convs(1) message_def)
  then have "DEPOSIT_step \<in> set claimed"
    unfolding DEPOSIT_step_def CLAIM_step_def claimed_def
    unfolding claimedDeposits_def deposits_def
    by auto

  obtain steps1 steps2 where steps: "steps = steps1 @ [DEPOSIT_step] @ steps2"
    using \<open>DEPOSIT_step \<in> set steps\<close>
    by (metis Cons_eq_append_conv in_set_conv_decomp self_append_conv2)

  have *: "\<forall> step \<in> set (steps1 @ steps2). (\<forall> caller' amount' ID'. step = DEPOSIT tokenDepositAddress caller' ID' token amount' \<longrightarrow> ID' \<noteq> ID)"
  proof safe
    fix caller' amount' proof' 
    assume "DEPOSIT tokenDepositAddress caller' ID token amount' \<in> set (steps1 @ steps2)"
    moreover
    have "\<nexists>token' caller' amount'.
         DEPOSIT tokenDepositAddress caller' ID token' amount' \<in> set (steps1 @ steps2)"
    proof (rule DEPOSITNoDouble'[OF \<open>reachableFrom initContracts contracts'' steps\<close>])
      show "steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2"
        using steps
        unfolding DEPOSIT_step_def
        by simp
    next
      show "\<forall>step\<in>set steps. \<forall>caller' amount' ID' token'.
          step = DEPOSIT tokenDepositAddress caller' ID' token' amount' \<longrightarrow>
          hash3 caller' token' amount' \<noteq> 0"
        by fact
    qed
    ultimately
    show False
      by simp
  qed
  then have "DEPOSIT_step \<notin> set (steps1 @ steps2)"
    unfolding DEPOSIT_step_def
    by auto

  define P' where "P' = (\<lambda> x. ((\<exists>caller' amount' proof'.
            CLAIM bridgeAddress caller' (DEPOSIT_id x) token amount' proof' \<in> set (CLAIM_step # steps))))"
  define P where "P = (\<lambda> x. ((\<exists>caller' amount' proof'.
            CLAIM bridgeAddress caller' (DEPOSIT_id x) token amount' proof' \<in> set steps)))"
  define Q where "Q = (\<lambda> step. case step of DEPOSIT address' caller ID token' amount \<Rightarrow> tokenDepositAddress = address' \<and> token = token' | _ \<Rightarrow> False)"

  have "deposits tokenDepositAddress token steps = 
        (filter Q steps1) @ [DEPOSIT_step] @ (filter Q steps2)"
    using \<open>steps = steps1 @ [DEPOSIT_step] @ steps2\<close>
    unfolding deposits_def Q_def DEPOSIT_step_def
    by auto
  then have **: "claimed = filter P' (filter Q steps1) @ filter P' [DEPOSIT_step] @ filter P' (filter Q steps2)"
    using deposits
    unfolding claimed_def claimedDeposits_def P'_def
    by auto

  define c1 where "c1 = filter P' (filter Q steps1)" 
  define c2 where "c2 = filter P' (filter Q steps2)" 

  have "DEPOSIT_step \<notin> set (c1 @ c2)"
    using \<open>DEPOSIT_step \<notin> set (steps1 @ steps2)\<close>
    unfolding c1_def c2_def
    by auto
  then have claimed: "claimed = c1 @ [DEPOSIT_step] @ c2"
    using ** \<open>DEPOSIT_step \<in> set claimed\<close> 
    unfolding c1_def c2_def
    by (metis append.assoc append.right_neutral filter.simps(1) filter.simps(2))
  
  moreover

  have "set (c1 @ c2) \<subseteq> set (steps1 @ steps2)"
    unfolding c1_def c2_def
    by auto

  have "filter P (deposits tokenDepositAddress token steps) = c1 @ c2"
  proof (rule filter')
    show "DEPOSIT_step \<notin> set (c1 @ c2)"
      by fact
  next
    show "filter P' (deposits tokenDepositAddress token steps) = c1 @ [DEPOSIT_step] @ c2"
      using \<open>claimed = c1 @ [DEPOSIT_step] @ c2\<close> deposits
      unfolding claimed_def claimedDeposits_def P'_def
      by simp
  next
    show "\<forall> step \<in> set (deposits tokenDepositAddress token steps). (P' step \<and> step \<noteq> DEPOSIT_step) \<longleftrightarrow> P step"
    proof safe
      fix step
      assume "step \<in> set (deposits tokenDepositAddress token steps)" "P' step" "step \<noteq> DEPOSIT_step"
      have "DEPOSIT_id step \<noteq> ID"
      proof-
        have "step \<in> set (filter Q steps1 @ filter Q steps2)"
          using \<open>step \<in> set (deposits tokenDepositAddress token steps)\<close> \<open>step \<noteq> DEPOSIT_step\<close>
          using \<open>deposits tokenDepositAddress token steps = (filter Q steps1) @ [DEPOSIT_step] @ (filter Q steps2)\<close>
          by auto
        then have "step \<in> set (steps1 @ steps2)" "Q step"
          by auto
        then obtain ID' caller' amount' where "step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
          unfolding Q_def
          by (cases step, auto split: Step.splits)
        then show ?thesis
          using * \<open>step \<in> set (steps1 @ steps2)\<close>
          by simp
      qed
      then show "P step"
        using \<open>P' step\<close>
        unfolding P_def P'_def CLAIM_step_def
        by auto
    next
      fix x
      assume "x \<in> set (deposits tokenDepositAddress token steps)" "P x"
      then show "P' x"
        unfolding P_def P'_def
        by auto
    next
      fix x
      assume "P DEPOSIT_step"
      then show False
        unfolding P_def DEPOSIT_step_def
        using CLAIMNoDoubleCons[OF assms(10)]
        by auto
    qed
  qed
  then have "claimedDeposits tokenDepositAddress bridgeAddress token steps = c1 @ c2"
    unfolding claimed_def P_def claimedDeposits_def
    by auto
  ultimately
  show ?thesis
    unfolding claimed_def claimedDepositsAmount_def
    unfolding CLAIM_step_def DEPOSIT_step_def
    by simp
qed

lemma claimedDepositAmountsClaimOtherAddress [simp]:
  assumes "address \<noteq> bridgeAddress"
  shows "claimedDepositsAmount tokenDepositAddress bridgeAddress token
          (CLAIM address caller ID token amount proof' # steps) = 
         claimedDepositsAmount tokenDepositAddress bridgeAddress token steps"
  using assms
  by (simp add: claimedDepositsAmountOther)

lemma
  assumes "reachableFrom initContracts contracts steps"
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress"
  assumes "properToken initContracts tokenDepositAddress bridgeAddress token"
  assumes "bridgeMintedToken contracts bridgeAddress token = mintedToken"
  assumes "mintedToken \<noteq> token"
  assumes "\<not> (bridgeDead contracts tokenDepositAddress)"
  shows "totalBalance (the (ERC20state contracts mintedToken)) = 
         totalBalance (the (ERC20state initContracts mintedToken)) + claimedDepositsAmount tokenDepositAddress bridgeAddress token steps"
  using assms
proof (induction initContracts contracts steps rule: reachableFrom.induct)
  case (reachableFrom_base initContracts)
  then show ?case
    by (simp add: claimedDepositsAmount_def claimedDeposits_def)
next
  case (reachableFrom_step steps contracts' initContracts contracts blockNum block step)
  then have *: "reachableFrom initContracts contracts' (step # steps)"
    using reachableFrom.reachableFrom_step by blast
  have notDead: "\<not> bridgeDead contracts tokenDepositAddress"
    by (metis reachableFrom.simps reachableFromDeadState reachableFrom_step.hyps(2) reachableFrom_step.prems(5))
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller ID token' amount)
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token = token'")
      case False
      have "token' \<noteq> mintedToken"
        sorry (* no direct deposit on minted token *)
      then have "ERC20state contracts' mintedToken = ERC20state contracts mintedToken"
        using DEPOSIT reachableFrom_step.prems reachableFrom_step.hyps callDepositOtherToken
        by (metis executeStep.simps(1))
      moreover 
      have "claimedDepositsAmount tokenDepositAddress bridgeAddress token steps =
            claimedDepositsAmount tokenDepositAddress bridgeAddress token (DEPOSIT address' caller ID token' amount # steps)"
        using claimedDepositsAmountOther False
        using False
        by auto
      ultimately show ?thesis
        using * notDead reachableFrom_step DEPOSIT
        by simp
    next
      case True
      have "claimedDepositsAmount tokenDepositAddress bridgeAddress token (step # steps) = 
            claimedDepositsAmount tokenDepositAddress bridgeAddress token steps"
        sorry
      then show ?thesis
        using True * notDead reachableFrom_step DEPOSIT
        by simp
    qed
  next
    case (CLAIM address' caller ID token' amount proof')
    show ?thesis
    proof (cases "address' = bridgeAddress \<and> token' = token")
      case True
      have "totalBalance (the (ERC20state contracts' mintedToken))  = 
            totalBalance (the (ERC20state contracts mintedToken)) + amount"
      proof (rule callClaimTotalBalance)
        show "finite (Mapping.keys (balances (the (ERC20state contracts mintedToken))))"
          sorry
      next
        show "callClaim contracts bridgeAddress (message caller amount) ID token' amount proof' = (Success, contracts')"
          using True CLAIM reachableFrom_step
          by simp
      next
        show "bridgeMintedToken contracts bridgeAddress token' = mintedToken"
          by (metis ProofVerifier.reachableFromBridgeMintedToken ProofVerifier.reachableFrom_step ProofVerifier_axioms True reachableFrom_step.hyps(1) reachableFrom_step.hyps(2) reachableFrom_step.prems(3))
      qed
      then show ?thesis
        using True CLAIM reachableFrom_step * notDead
        sorry
    next
      case False
      have "mintedToken \<noteq> bridgeMintedToken initContracts address' token'" (* no cancel of minted tokens *)
        sorry
      then have "ERC20state contracts' mintedToken = ERC20state contracts mintedToken"
        using CLAIM reachableFrom_step callClaimOtherToken[of contracts address' "message caller amount" ID token' amount proof' contracts' _ mintedToken]
        by auto
      then show ?thesis
        using False CLAIM reachableFrom_step * notDead
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
    then have "ERC20state contracts' mintedToken = ERC20state contracts mintedToken"
      using CANCEL reachableFrom_step.hyps(2) by auto
    then show ?thesis
      using CANCEL reachableFrom_step * notDead
      using claimedDepositsAmountOther
      by simp
  next
    case (WITHDRAW address' caller token' amount proof')
    have "mintedToken \<noteq> token'" (* no withdrawal of minted tokens *)
      sorry
   then have "ERC20state contracts' mintedToken = ERC20state contracts mintedToken"
      using WITHDRAW reachableFrom_step.hyps(2) by auto
    then show ?thesis
      using WITHDRAW reachableFrom_step * notDead
      using claimedDepositsAmountOther
      by simp
  qed
qed

end

end