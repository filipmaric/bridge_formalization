theory Properties
  imports Reachability
begin

context ProofVerifier
begin

(* ------------------------------------------------------------------------------------ *)

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
  proof (induction contracts' contracts'' steps rule: reachableFrom.induct)
    case (reachableFrom_base contracts')
    then show ?case 
      by simp
  next
    case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
    show ?case
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      then show ?thesis
        using reachableFrom_step
        by simp
    next 
      case (UPDATE address' stateRoot')
      then show ?thesis
        using reachableFrom_step
        by simp
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      show ?thesis
      proof (cases "address = address'")
        case True
        then show ?thesis
          using reachableFrom_step CLAIM
          by simp
      next
        case False
        then show ?thesis
          using reachableFrom_step CLAIM
          by (simp add: Let_def split: option.splits prod.splits)
      qed
    next
      case (CANCEL address' caller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        by simp
    next
      case (WITHDRAW address' caller' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        by simp
    qed
  qed
  then show ?thesis
    unfolding callClaim_def claim_def
    by (auto simp add: Let_def split: option.splits prod.splits)
qed

(* ------------------------------------------------------------------------------------ *)

text \<open>After a successful deposit and a state update, 
      if a bridge is still alive a claim can be made \<close>
theorem claimPossibleAfterDepositAndUpdate:
  \<comment> \<open>contracts are setup properly in the initial state\<close>
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
  \<comment> \<open>state root is nonzero in a starting state (there was at least one update)\<close>
  assumes "getLastStateTD contracts tokenDepositAddress \<noteq> 0"
  \<comment> \<open>A deposit is successfully made\<close>
  assumes "callDeposit contracts tokenDepositAddress block msg ID token amount = (Success, contractsD)"
  \<comment> \<open>after a deposit a new state is reached\<close>
  assumes "reachableFrom contractsD contractsD' steps"
  (* NOTE: additional assumption *)
  \<comment> \<open>if updates were made, state root was never zero\<close>
  assumes "updatesNonZero steps"
  \<comment> \<open>the bridge is not dead in the reached state\<close>
  assumes "deadState (the (tokenDepositState contractsD' tokenDepositAddress)) = 0"
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
      show "getLastStateTD contractsD tokenDepositAddress \<noteq> 0"
        using assms
        by simp
    next
      show "updatesNonZero steps"
        by fact
    next
      show "deadState (the (tokenDepositState contractsD' tokenDepositAddress)) = 0"
        by fact
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
    show "getMinted stateTokenPairs token \<noteq> 0"
      using stateTokenPairs assms stateBridgeU
      unfolding properSetup_def
      by (auto simp add: Let_def)
  next
    show "ERC20state contractsU' (getMinted stateTokenPairs token) \<noteq> None"
      using assms
      unfolding properSetup_def
      by (smt (verit, best) callDepositProperSetup callUpdateIBridge callUpdateIERC20 callUpdateITokenPairs option.sel properSetup_def reachableFromBridgeTokenPairs reachableFromERC20State reachableFromITokenPairs stateBridgeU stateTokenPairs)
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
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
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

  have "properSetup contracts' tokenDepositAddress bridgeAddress token"
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
      using \<open>properSetup contracts' tokenDepositAddress bridgeAddress token\<close> 
      by (metis callUpdateITokenDeposit dB option.collapse properSetup_def update)
  qed
qed

text \<open>Before every successful claim, a deposit must have been made\<close>
theorem depositBeforeClaim:
  \<comment> \<open>The operation starts from an initial state that is properly setup, but all data is still empty\<close>
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token"
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
  assumes "properSetup contractsD tokenDepositAddress bridgeAddress token'"
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
    show "properSetup contractsUx tokenDepositAddress bridgeAddress token'"
      using \<open>reachableFrom contractsD' contractsUx steps1x\<close> 
      using \<open>properSetup contractsD tokenDepositAddress bridgeAddress token'\<close> 
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

text \<open>No deposit after the bridge dies\<close>
theorem  noDepositBridgeDead: 
  assumes "bridgeDead contracts tokenDepositAddress"
  assumes "reachableFrom contracts contracts' steps"
  shows "fst (callDeposit contracts' tokenDepositAddress block msg ID token amount) \<noteq> Success"
  using assms callDepositFailsInDeadState reachableFromDeadState
  by blast

text \<open>Cancel deposit can succeed only if there was a previous successful deposit with the same ID\<close>
theorem cancelDepositOnlyAfterDeposit:
  \<comment> \<open>contracts start working from a properly setup initial state\<close>
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token"
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
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
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
        show ?thesis
        proof (rule callCancelDepositWhileDeadSetsDeadState)
          show "getLastStateTD contracts' tokenDepositAddress = stateRoot"
            using reachableFrom_step.prems reachableFrom_step.hyps
            by (smt (verit, ccfv_threshold) noUpdateLastState callLastState callLastStateI list.set_intros(2) prod.exhaust_sel properSetupReachable properSetup_def reachableFromBridgeStateOracle)
        next
          show "\<not> bridgeDead contracts' tokenDepositAddress"
            by fact
        next
          show "callCancelDepositWhileDead contracts' tokenDepositAddress (message caller' 0) block ID' token' amount' proof' =
               (Success, contracts'')"
            using CANCEL reachableFrom_step.prems reachableFrom_step.hyps True
            by auto
        qed
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
        show ?thesis
        proof (rule callWithdrawWhileDeadSetsDeadState)
          show "getLastStateTD contracts' tokenDepositAddress = stateRoot"
            using reachableFrom_step.prems reachableFrom_step.hyps
            by (smt (verit, ccfv_threshold) noUpdateLastState callLastState callLastStateI list.set_intros(2) prod.exhaust_sel properSetupReachable properSetup_def reachableFromBridgeStateOracle)
        next
          show "\<not> bridgeDead contracts' tokenDepositAddress"
            by fact
        next
          show "callWithdrawWhileDead contracts' tokenDepositAddress (message caller' 0) block token' amount' proof' =
               (Success, contracts'')"
            using WITHDRAW reachableFrom_step.prems reachableFrom_step.hyps True
            by auto
        qed
      qed
    qed
  qed
qed

text \<open>If cancel deposit succeeds, then the bridge is dead and 
      there was no claim previous to the state in which the bridge died\<close>
theorem cancelDepositNoClaim:
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token"
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

  define stateBridge where "stateBridge = the (bridgeState contracts'' bridgeAddress)"
  define stateStateOracle where "stateStateOracle = the (stateOracleState contracts'' (BridgeState.stateOracle stateBridge))"
  define stateTokenDeposit where "stateTokenDeposit = the (tokenDepositState contracts'' tokenDepositAddress)"
  define stateTokenDeposit' where "stateTokenDeposit' = snd (snd (getDeadStatus contracts'' stateTokenDeposit block'))"

  have bD: "TokenDepositState.bridge stateTokenDeposit = bridgeAddress"
    using assms
    unfolding stateTokenDeposit_def
    by (meson callUpdateProperSetup properSetupReachable properSetup_def)

  have sOB: "BridgeState.stateOracle stateBridge = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))"
    using assms
    unfolding stateBridge_def
    by simp

  have "properSetup contracts' tokenDepositAddress bridgeAddress token"
    using assms
    by (meson callUpdateProperSetup properSetupReachable)

  from cancel
  obtain stateRoot' where
    lVS: "lastValidState contracts'' stateTokenDeposit' = (Success, stateRoot')" and
    vCP: "callVerifyClaimProof contracts'' (TokenDepositState.proofVerifier stateTokenDeposit') (bridge stateTokenDeposit') ID
          stateRoot' proof = Success" and
         "getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')"
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def stateTokenDeposit_def stateTokenDeposit'_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

  have "lastState stateStateOracle = stateRoot"
    using assms
    by (metis (no_types, lifting) callUpdateLastState noUpdateLastState sOB stateStateOracle_def)
  then have "getLastStateB contracts'' bridgeAddress = stateRoot"
    using stateBridge_def stateStateOracle_def
    by argo
  then have "getLastStateTD contracts'' tokenDepositAddress = stateRoot"
    using assms properSetup_stateOracleAddress update
    by auto

  have "stateRoot' = stateRoot"
  proof (cases "bridgeDead contracts'' tokenDepositAddress")
    case True
    have "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) = stateRoot"
    proof (rule deadStateLastState)
      show "reachableFrom contracts' contracts'' steps'"
        by fact
    next
      show "properSetup contracts' tokenDepositAddress bridgeAddress token" 
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
        using \<open>properSetup contracts' tokenDepositAddress bridgeAddress token\<close> \<open>reachableFrom contracts' contracts'' steps'\<close> 
        by (smt (verit, best) callLastState_def callUpdateLastState option.case_eq_if properSetup_def reachableFromBridgeStateOracle sOB stateBridge_def update)
    qed
    then show ?thesis
      using \<open>getLastStateB contracts'' bridgeAddress = stateRoot\<close> lVS True
      using \<open>getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')\<close>
      unfolding lastValidState_def
      by (metis Pair_inject getDeadStatusInDeadState stateTokenDeposit_def)
  next
    case False
    then show ?thesis
      using \<open>getLastStateB contracts'' bridgeAddress = stateRoot\<close> lVS
            \<open>getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')\<close> 
            \<open>getLastStateTD contracts'' tokenDepositAddress = stateRoot\<close> \<open>stateRoot \<noteq> 0\<close> 
      unfolding lastValidState_def stateTokenDeposit_def
      by (metis getDeadStatusSetsDeadState snd_conv)
  qed

  from update have "generateStateRoot contracts = stateRoot"
    using updateSuccess
    by simp

  have "getClaim (the (bridgeState contracts bridgeAddress)) ID = False"
  proof (rule verifyClaimProofE)
    show "generateStateRoot contracts = stateRoot"
      by fact
  next
    show "verifyClaimProof () bridgeAddress ID stateRoot proof = True"
      using vCP bD \<open>stateRoot' = stateRoot\<close>
      unfolding callVerifyClaimProof_def
      unfolding stateTokenDeposit'_def stateTokenDeposit_def
      by (simp add: snd_def split: option.splits prod.splits if_split_asm)
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
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token"
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
  define stateBridge where "stateBridge = the (bridgeState contracts'' bridgeAddress)"
  define stateStateOracle where "stateStateOracle = the (stateOracleState contracts'' (BridgeState.stateOracle stateBridge))"
  define stateTokenDeposit where "stateTokenDeposit = the (tokenDepositState contracts'' tokenDepositAddress)"
  define stateTokenDeposit' where "stateTokenDeposit' = snd (snd (getDeadStatus contracts'' stateTokenDeposit block'))"
  define stateERC20 where "stateERC20 = the (ERC20state contracts' token)"

  have sOB: "BridgeState.stateOracle stateBridge = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))"
    using assms
    unfolding stateBridge_def
    by simp

  have "properSetup contracts' tokenDepositAddress bridgeAddress token"
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

  from withdraw
  obtain stateRoot' where
    dS: "deadState stateTokenDeposit' = stateRoot'" and
    vCP: "callVerifyBalanceProof contracts'' (TokenDepositState.proofVerifier stateTokenDeposit') token (sender msg) amount
          stateRoot' proof = Success" and
    status: "getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')"
    unfolding callWithdrawWhileDead_def withdrawWhileDead_def stateTokenDeposit_def stateTokenDeposit'_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

  have "stateRoot' = stateRoot"
  proof (cases "bridgeDead contracts'' tokenDepositAddress")
    case True 
    have "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) = stateRoot"
    proof (rule deadStateLastState)
      show "reachableFrom contracts' contracts'' steps'"
        by fact
    next
      show "properSetup contracts' tokenDepositAddress bridgeAddress token" 
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
        using \<open>properSetup contracts' tokenDepositAddress bridgeAddress token\<close> 
              \<open>reachableFrom contracts' contracts'' steps'\<close>
        by (smt (verit, best) callLastState_def callUpdateLastState option.case_eq_if properSetup_def reachableFromBridgeStateOracle sOB stateBridge_def update)
    qed
    then show ?thesis
      using dS \<open>stateRoot \<noteq> 0\<close> 
      using getDeadStatusInDeadState stateTokenDeposit_def status
      by blast
  next
    case False
    then have "deadState stateTokenDeposit' = stateRoot"
      using getDeadStatusSetsDeadState[OF status]
      using \<open>getLastStateTD contracts'' tokenDepositAddress = stateRoot\<close>
      unfolding stateTokenDeposit_def
      by fastforce
    then show ?thesis
      using dS
      by simp
  qed

  have "ERC20state contracts token \<noteq> None"
    using \<open>properSetup contracts' tokenDepositAddress bridgeAddress token\<close> update
    by (metis callUpdateIERC20 properSetup_def)

  have "balanceOf (the (ERC20state contracts token)) (sender msg) = amount"
  proof (rule verifyBalanceProofE)
    show "verifyBalanceProof () token (sender msg) amount stateRoot proof = True"
      using vCP \<open>stateRoot' = stateRoot\<close>
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

end

end