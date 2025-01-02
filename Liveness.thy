theory Liveness
imports TokenInvariants
begin



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

text \<open>After a successful deposit and a state update (while the bridge is alive), a claim can be made \<close>
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

  \<comment> \<open>The user who made the deposit can make the claim\<close>
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
      using reachableFromGetDepositBridgeNotDead
      using \<open>reachableFrom contractsD contractsLastUpdate' steps\<close> hash3_nonzero assms callDepositWritesHash
      by auto
  qed simp_all
  then have "verifyDepositProof ()
              (depositAddressB contractsLU bridgeAddress)
               ID (hash3 (sender msg') token amount)
              (lastStateB contractsLU bridgeAddress) proof"
    using \<open>sender msg' = sender msg\<close> depositLU lastStateBLU stateBridge_def
    by argo

  then have "fst (callClaim contractsLU bridgeAddress msg' ID token amount proof) = Success"
    using assms
    by (smt (verit, ccfv_threshold) HashProofVerifier.callClaimI HashProofVerifier_axioms callDepositProperToken option.collapse properSetupLU properSetup_def properTokenReachable properToken_def reachableFromLastUpdate'LU stateBridge_def)
  then show ?thesis 
    unfolding Let_def proof_def
    by (metis eq_fst_iff)
qed

end


context HashProofVerifier
begin

text \<open>Burn can always be made provided a fresh ID and enough tokens on the bridge\<close>
lemma burnPossible:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress"
  assumes "properToken contracts tokenDepositAddress bridgeAddress token"
  assumes "0 < amount \<and> amount \<le> accountBalance contracts (mintedTokenB contracts bridgeAddress token) caller"
  assumes "getWithdrawal (the (bridgeState contracts bridgeAddress)) ID = 0"
  shows "fst (callWithdraw contracts bridgeAddress (message caller 0) ID token amount) = Success"
proof (rule callWithdrawI)
  show "bridgeState contracts bridgeAddress \<noteq> None"
       "tokenPairsState contracts (tokenPairsAddressB contracts bridgeAddress) \<noteq> None"
       "stateOracleState contracts (stateOracleAddressB contracts bridgeAddress) \<noteq> None"
       "proofVerifierState contracts (proofVerifierAddressB contracts bridgeAddress) \<noteq> None"
    by (meson assms(1) properSetup_def)+
next
  show "mintedTokenB contracts bridgeAddress token \<noteq> 0"
       "ERC20state contracts (mintedTokenB contracts bridgeAddress token) \<noteq> None"
    by (meson assms(2) properToken_def)+
next
  show "amount \<le> accountBalance contracts (mintedTokenB contracts bridgeAddress token) (sender (message caller 0))"
       "0 < amount"
    using assms(3)
    by simp_all
next
  show "getWithdrawal (the (bridgeState contracts bridgeAddress)) ID = 0"
    by fact
qed

end

context InitFirstUpdateLastUpdate
begin

text \<open>After a successful burn and a state update (while the bridge is alive), a release can be made\<close>
theorem releasePossibleAfterBurnAndUpdateBridgeNotDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"

  \<comment> \<open>A burn is successfully made\<close>
  assumes "BURN bridgeAddress caller ID token amount \<in> set stepsInit"
  \<comment> \<open>the bridge is not dead in the reached state\<close>
  assumes "\<not> bridgeDead  contractsLU tokenDepositAddress"
  \<comment> \<open>there was no previous release\<close>
  assumes "getRelease (the (tokenDepositState contractsLU tokenDepositAddress)) ID = False"

  \<comment> \<open>The user who burned the tokens can release them\<close>
  assumes "sender msg' = caller"
  assumes "caller \<noteq> tokenDepositAddress"

  \<comment> \<open>A release can be made with the state root and the proof obtained from the state that
      was used for the last update\<close>
  shows "let proof = generateBurnProof contractsLastUpdate' ID
          in fst (callRelease contractsLU tokenDepositAddress msg' ID token amount proof) = Success"
  unfolding Let_def
proof (rule callReleaseI)
  show "tokenDepositState contractsLU tokenDepositAddress \<noteq> None"
       "stateOracleState contractsLU (stateOracleAddressTD contractsLU tokenDepositAddress) \<noteq> None"
       "proofVerifierState contractsLU (proofVerifierAddressTD contractsLU tokenDepositAddress) \<noteq> None"
    by (metis properSetupLU properSetup_def)+
next
  show "ERC20state contractsLU token \<noteq> None"
    using IFLU.ERC20stateINonNone assms(1) by blast
next
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  have "?BURN_step \<in> set (nonReleasedBurns tokenDepositAddress bridgeAddress token stepsInit stepsAllLU)"
  proof-
    have "?BURN_step \<in> set (burns bridgeAddress token stepsInit)"
      unfolding nonReleasedBurns_def
      using assms(3)
      by (simp add: burns_def)
    moreover
    have "\<not> isReleasedID tokenDepositAddress token ID stepsAllLU"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain caller' amount' proof' where "RELEASE tokenDepositAddress caller' ID token amount' proof' \<in> set stepsAllLU"
        unfolding isReleasedID_def
        by auto
      then have "getRelease (the (tokenDepositState contractsLU tokenDepositAddress)) ID = True"
        using reachableFromInitLU reachableFromReleaseSetsFlag by blast
      then show False
        using assms
        by blast
    qed
    ultimately
    show ?thesis
      unfolding nonReleasedBurns_def
      by simp
  qed
  
  then have "amount \<le> nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLU"
    unfolding nonReleasedBurnsAmount_def
    by (simp add: sum_list_map_remove1)
  then show "amount \<le> accountBalance contractsLU token tokenDepositAddress"
    using tokenDepositBalanceBridgeNotDead[OF assms(1) assms(4) assms(2)]
    by simp
next
  show "getRelease (the (tokenDepositState contractsLU tokenDepositAddress)) ID = False"
    by fact
next
  show "tokenDepositAddress \<noteq> sender msg'"
    using assms
    by blast
next
  have "verifyBurnProof () (bridgeAddressTD contractsLU tokenDepositAddress) ID (hash3 (sender msg') token amount)
     (snd (lastValidStateTD contractsLU tokenDepositAddress)) (generateBurnProof contractsLastUpdate' ID) = True" (is "?P = True")
  proof (rule verifyBurnProofI)
    show "generateBurnProof contractsLastUpdate' ID = generateBurnProof contractsLastUpdate' ID"
      by simp
  next
    have "bridgeState contractsLastUpdate' (bridgeAddressTD contractsLU tokenDepositAddress) \<noteq> None"
      by (metis bridgeAddressLU properSetupUpdate' properSetup_def)
    then show "bridgeState contractsLastUpdate' (bridgeAddressTD contractsLU tokenDepositAddress)  = 
               Some (the (bridgeState contractsLastUpdate' (bridgeAddressTD contractsLU tokenDepositAddress)))"
      by simp
  next
    have "getWithdrawal (the (bridgeState contractsLastUpdate' bridgeAddress)) ID =
          hash3 caller token amount"
      using reachableFromBurnSetsFlag[OF reachableFromInitI \<open>BURN bridgeAddress caller ID token amount \<in> set stepsInit\<close>]
      by blast
    then show "getWithdrawal (the (bridgeState contractsLastUpdate' (bridgeAddressTD contractsLU tokenDepositAddress))) ID =
          hash3 (sender msg') token amount"
      using \<open>sender msg' = caller\<close> bridgeAddressLU by blast
  next
    have "generateStateRoot contractsLastUpdate' = stateRoot"
      by simp
    moreover
    have "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
      by (metis assms(4) reachableFromDeadState reachableFromLastUpdate'LU)
    then have "snd (lastValidStateTD contractsLastUpdate tokenDepositAddress) = stateRoot"
      using callUpdateBridgeNotDeadLastValidState properSetupUpdate' 
      by (smt (verit, ccfv_SIG) properSetup_def update)
    ultimately
    show "generateStateRoot contractsLastUpdate' = snd (lastValidStateTD contractsLU tokenDepositAddress)"
      using \<open>\<not> bridgeDead contractsLastUpdate' tokenDepositAddress\<close>
      by (metis LastUpdateBridgeNotDead.intro LastUpdateBridgeNotDead.lastValidStateLU LastUpdateBridgeNotDead_axioms.intro LastUpdate_axioms)
  qed
  then show "?P"
    by simp
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

context BridgeDeadInitFirstUpdate 
begin

text \<open>After a successful burn and a state update (while the bridge is alive), a release can be made even if the bridge is dead\<close>
theorem releasePossibleAfterBurnAndUpdateBridgeDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"

  \<comment> \<open>A burn is successfully made\<close>
  assumes "BURN bridgeAddress caller ID token amount \<in> set stepsInit"
  \<comment> \<open>there was no previous release\<close>
  assumes "getRelease (the (tokenDepositState contractsBD tokenDepositAddress)) ID = False"

  \<comment> \<open>The user who burned the tokens can release them\<close>
  assumes "sender msg' = caller"
  assumes "caller \<noteq> tokenDepositAddress"

  \<comment> \<open>A release can be made with the state root and the proof obtained from the state that
      was used for the last update\<close>
  shows "let proof = generateBurnProof contractsLastUpdate' ID
          in fst (callRelease contractsBD tokenDepositAddress msg' ID token amount proof) = Success"
  unfolding Let_def
proof (rule callReleaseI)
  show "tokenDepositState contractsBD tokenDepositAddress \<noteq> None"
       "stateOracleState contractsBD (stateOracleAddressTD contractsBD tokenDepositAddress) \<noteq> None"
       "proofVerifierState contractsBD (proofVerifierAddressTD contractsBD tokenDepositAddress) \<noteq> None"
    using LVSBD.InitLVS.tokenDepositStateINotNone LVSBD.InitLVS.stateOracleAddressTDI LVSBD.InitLVS.stateOracleStateINotNone LVSBD.InitLVS.proofVerifierStateNotNone
    by presburger+
next
  show "ERC20state contractsBD token \<noteq> None"
    using LVSBD.InitLVS.ERC20stateINonNone assms(1) by blast
next
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  have "?BURN_step \<in> set (nonReleasedBurns tokenDepositAddress bridgeAddress token stepsInit stepsAllBD)"
  proof-
    have "?BURN_step \<in> set (burns bridgeAddress token stepsInit)"
      unfolding nonReleasedBurns_def
      using assms(3)
      by (simp add: burns_def)
    moreover
    have "\<not> isReleasedID tokenDepositAddress token ID stepsAllBD"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain caller' amount' proof' where "RELEASE tokenDepositAddress caller' ID token amount' proof' \<in> set stepsAllBD"
        unfolding isReleasedID_def
        by auto
      then have "getRelease (the (tokenDepositState contractsBD tokenDepositAddress)) ID = True"
        using reachableFromReleaseSetsFlag InitBD.reachableFromInitI 
        by blast
      then show False
        using assms
        by blast
    qed
    ultimately
    show ?thesis
      unfolding nonReleasedBurns_def
      by simp
  qed
  
  then have "amount \<le> nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
    unfolding nonReleasedBurnsAmount_def
    by (simp add: sum_list_map_remove1)
  then show "amount \<le> accountBalance contractsBD token tokenDepositAddress"
    using tokenDepositBalance
    using assms(1) assms(2) le_add2
    by presburger
next
  show "getRelease (the (tokenDepositState contractsBD tokenDepositAddress)) ID = False"
    by fact
next
  show "tokenDepositAddress \<noteq> sender msg'"
    using assms
    by blast
next
  have "verifyBurnProof () (bridgeAddressTD contractsBD tokenDepositAddress) ID (hash3 (sender msg') token amount)
     (snd (lastValidStateTD contractsBD tokenDepositAddress)) (generateBurnProof contractsLastUpdate' ID) = True" (is "?P = True")
  proof (rule verifyBurnProofI)
    show "generateBurnProof contractsLastUpdate' ID = generateBurnProof contractsLastUpdate' ID"
      by simp
  next
    have "bridgeState contractsLastUpdate' (bridgeAddressTD contractsBD tokenDepositAddress) \<noteq> None"
      using LVSBD.InitLVS.bridgeBridgeAddress bridgeStateINotNone by blast
    then show "bridgeState contractsLastUpdate' (bridgeAddressTD contractsBD tokenDepositAddress)  = 
               Some (the (bridgeState contractsLastUpdate' (bridgeAddressTD contractsBD tokenDepositAddress)))"
      by simp
  next
    have "getWithdrawal (the (bridgeState contractsLastUpdate' bridgeAddress)) ID =
          hash3 caller token amount"
      using reachableFromBurnSetsFlag[OF reachableFromInitI \<open>BURN bridgeAddress caller ID token amount \<in> set stepsInit\<close>]
      by blast
    then show "getWithdrawal (the (bridgeState contractsLastUpdate' (bridgeAddressTD contractsBD tokenDepositAddress))) ID =
          hash3 (sender msg') token amount"
      using \<open>sender msg' = caller\<close> 
      using LVSBD.InitLVS.bridgeBridgeAddress by blast
  next
    show "generateStateRoot contractsLastUpdate' = snd (lastValidStateTD contractsBD tokenDepositAddress)"
      by (simp add: LVSBD.getLastValidStateLVS)
  qed
  then show "?P"
    by simp
qed


theorem cancelPossible:
  \<comment> \<open>Tokens are properly initialized\<close>
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  \<comment> \<open>Initially there are no minted tokens\<close>
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  \<comment> \<open>User has made a deposit that he has not claimed before the bridge died\<close>
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set stepsAllBD"
  assumes "\<not> isClaimedID bridgeAddress token ID stepsInit"
  \<comment> \<open>User has not canceled this deposit\<close>
  assumes "\<not> isCanceledID tokenDepositAddress token ID stepsAllBD"
  \<comment> \<open>Caller is not the bridge itself\<close>
  assumes "caller \<noteq> tokenDepositAddress"
  shows "\<exists> contractsCancel. reachableFrom contractsBD contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount (generateClaimProof contractsLastUpdate' ID)]"
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
        using senderMessage by presburger
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
            lastStateTD contractsBD tokenDepositAddress = stateRoot"
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
            using onlyDepositorCanClaimSteps(2)
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
      show "amount \<le> accountBalance contractsBD token tokenDepositAddress"
      proof-
        have "amount \<le> nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
            unfolding nonClaimedBeforeNonCanceledDepositsAmount_def
        proof (rule member_le_sum_list)
          have "DEPOSIT tokenDepositAddress caller ID token amount \<in> set (nonClaimedBeforeNonCanceledDeposits tokenDepositAddress bridgeAddress token stepsInit stepsAllBD)"
            using assms
            by (simp add: nonClaimedBeforeNonCanceledDeposits_def deposits_def)
          then show "amount \<in> set (map DEPOSIT_amount (nonClaimedBeforeNonCanceledDeposits tokenDepositAddress bridgeAddress token stepsInit stepsAllBD))"
            by (metis HashProofVerifier.DEPOSIT_amount.simps HashProofVerifier_axioms image_eqI image_set)
        qed
        then show ?thesis
          using tokenDepositBalance[of token] assms
          by simp
      qed
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
    by (metis executeStep.simps(7) prod.collapse reachableFrom_base reachableFrom_step)
qed

text \<open>If the user had some amount of tokens in the state in which the bridge died, 
      he can withdraw that amount\<close>
theorem withdrawPossibe:
  \<comment> \<open>Tokens are properly initialized\<close>
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  \<comment> \<open>Initially there are no minted tokens\<close>
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  \<comment> \<open>Caller had sufficient balance before the bridge died\<close>
  assumes "accountBalance contractsLastUpdate' (mintedTokenB contractsInit bridgeAddress token) (sender msg) = amount"
  \<comment> \<open>Caller has not yet withdrawn his balance\<close>
  assumes notWithdrawn: 
    "getTokenWithdrawn (the (tokenDepositState contractsBD tokenDepositAddress)) (hash2 (sender msg) token) = False"
  \<comment> \<open>Sender is not the bridge itself\<close>
  assumes "tokenDepositAddress \<noteq> sender msg"
  \<comment> \<open>Withdraw succedes\<close>
  shows "fst (callWithdrawWhileDead contractsBD tokenDepositAddress msg block token amount 
                                    (generateBalanceProof contractsLastUpdate' (mintedTokenB contractsInit bridgeAddress token) (sender msg) amount)) = Success"
proof-
  have "accountBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) (sender msg) = 0"
    using assms(1) assms(2) finiteBalances_def properTokenFiniteBalancesMinted totalBalanceZero by presburger

  show ?thesis
  proof (rule callWithdrawWhileDeadI)
    show "tokenDepositState contractsBD tokenDepositAddress \<noteq> None"
      by simp
  next
    show "tokenPairsState contractsBD (tokenPairsAddressTD contractsBD tokenDepositAddress) \<noteq> None"
      by simp
  next
    show "stateOracleState contractsBD (stateOracleAddressTD contractsBD tokenDepositAddress) \<noteq> None"
      by simp
  next 
    show "proofVerifierState contractsBD (proofVerifierAddressTD contractsBD tokenDepositAddress) \<noteq> None"
      by simp
  next
    show "ERC20state contractsBD token \<noteq> None"
      using assms(1)
      by simp
  next
    show "getTokenWithdrawn (the (tokenDepositState contractsBD tokenDepositAddress)) (hash2 (sender msg) token) = False"
      by fact
  next
    show "fst (snd (getDeadStatus contractsBD (the (tokenDepositState contractsBD tokenDepositAddress)) block)) = True"
      by (metis deadStateContractsBD getDeadStatus_def split_pairs stateRootNonZero)
  next
    show "tokenDepositAddress \<noteq> sender msg"
      by fact
  next
    show "mintedTokenTD contractsBD tokenDepositAddress token \<noteq> 0"
      using assms(1)
      by simp
  next
    show "amount \<le> accountBalance contractsBD token tokenDepositAddress"
    proof-
      have "amount \<le> nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
      proof-
        let ?N = "nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
        have "balanceOf ?N (sender msg) = amount"
        proof-
          have "balanceOf (mintedUserBalances bridgeAddress token stepsInit) (sender msg) = amount"
          proof (subst mintedUserBalancesAccountBalance)
            show "reachableFrom contractsInit contractsLastUpdate' stepsInit"
              by simp
          next
            let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
            show "accountBalance contractsLastUpdate' ?mintedToken (sender msg) = amount"
              using assms
              using callBalanceOf by blast
          next
            show "accountBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) (sender msg) = 0"
              by fact              
          qed
          moreover 
          have "\<nexists> amount proof. WITHDRAW_WD tokenDepositAddress (sender msg) token amount proof \<in> set stepsAllBD"
            using \<open>getTokenWithdrawn (the (tokenDepositState contractsBD tokenDepositAddress)) (hash2 (sender msg) token) = False\<close>
            using InitBD.reachableFromInitI reachableFromGetTokenWithdrawnNoWithdraw by blast
          ultimately show ?thesis
            using nonWithdrawnMintedUserBalancesNoWithdraw
            by blast
        qed
        moreover 
        have "finite (Mapping.keys (balances ?N))"
          by simp
        ultimately
        show ?thesis
          unfolding nonWithdrawnNonBurnedClaimedBeforeAmount_def
          by (metis order_refl totalBalance_removeFromBalance(1))
      qed
      then show ?thesis
        using tokenDepositBalance assms
        by presburger
    qed
  next
    let ?mintedToken = "mintedTokenTD contractsBD tokenDepositAddress token"
    define Proof where "Proof =  generateBalanceProof contractsLastUpdate' (mintedTokenB contractsInit bridgeAddress token) (sender msg) amount"

    have "verifyBalanceProof () ?mintedToken (sender msg) amount 
            (snd (lastValidStateTD contractsBD tokenDepositAddress)) Proof = True"
    proof (rule verifyBalanceProofI)
      show "generateStateRoot contractsLastUpdate' = snd (lastValidStateTD contractsBD tokenDepositAddress)"
        by (simp add: LVSBD.getLastValidStateLVS)
    next
      show "ERC20state contractsLastUpdate' (mintedTokenTD contractsBD tokenDepositAddress token) =
            Some (the (ERC20state contractsLastUpdate' (mintedTokenTD contractsBD tokenDepositAddress token)))"
        using assms(1)
        by (metis ERC20StateMintedTokenINotNone LVSBD.InitLVS.mintedTokenTDI option.exhaust_sel)
    next
      show "accountBalance contractsLastUpdate' (mintedTokenTD contractsBD tokenDepositAddress token) (sender msg) = amount"
        by (metis LVSBD.InitLVS.mintedTokenTDI assms(3) mintedTokenITDB)
    next
      show "generateBalanceProof contractsLastUpdate' (mintedTokenTD contractsBD tokenDepositAddress token) (sender msg) amount = Proof"
        unfolding Proof_def
        using LVSBD.InitLVS.mintedTokenTDI mintedTokenITDB by presburger
    qed
    then show "verifyBalanceProof () ?mintedToken (sender msg) amount 
               (snd (lastValidStateTD contractsBD tokenDepositAddress)) Proof"
      by blast
  qed    
qed

end

context HashProofVerifier
begin
(* FIXME: move *)
lemma getReleaseNoReleaseFalse:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<not> isReleasedID tokenDepositAddress token ID steps"
  assumes "getRelease (the (tokenDepositState contracts tokenDepositAddress)) ID = False"
  shows "getRelease (the (tokenDepositState contracts' tokenDepositAddress)) ID = False"
  sorry

end

context HashProofVerifier
begin

lemma releasedAmountFromAppend [simp]:
  shows "releasedAmountFrom tokenDepositAddres token caller (steps1 @ steps2) = 
         releasedAmountFrom tokenDepositAddres token caller steps1 + 
         releasedAmountFrom tokenDepositAddres token caller steps2"
  by (auto simp add: releasedAmountFrom_def releasesFrom_def)

lemma withdrawnAmountFromAppend [simp]:
  shows "withdrawnAmountFrom tokenDepositAddres token caller (steps1 @ steps2) = 
         withdrawnAmountFrom tokenDepositAddres token caller steps1 + 
         withdrawnAmountFrom tokenDepositAddres token caller steps2"
  by (auto simp add: withdrawnAmountFrom_def withdrawalsFrom_def)

lemma canceledAmountFromAppend [simp]:
  shows "canceledAmountFrom tokenDepositAddres token caller (steps1 @ steps2) = 
         canceledAmountFrom tokenDepositAddres token caller steps1 + 
         canceledAmountFrom tokenDepositAddres token caller steps2"
  by (auto simp add: canceledAmountFrom_def cancelsFrom_def)

lemma paidBackAmountFromAppend [simp]:
  shows "paidBackAmountFrom tokenDepositAddres token caller (steps1 @ steps2) = 
         paidBackAmountFrom tokenDepositAddres token caller steps1 + 
         paidBackAmountFrom tokenDepositAddres token caller steps2"
  by (simp add: paidBackAmountFrom_def)

lemma paidBackAmountFromCons:
  shows "paidBackAmountFrom tokenDepositAddres token caller (step # steps) = 
         paidBackAmountFrom tokenDepositAddres token caller [step] + 
         paidBackAmountFrom tokenDepositAddres token caller steps"
  by (metis append.left_neutral append_Cons paidBackAmountFromAppend)
end

context BridgeDeadInitFirstUpdate
begin

theorem paybackPossibleBridgeDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"
  assumes "caller \<noteq> tokenDepositAddress"
  assumes X: "depositedAmountTo tokenDepositAddress token caller stepsAllBD = X"
  assumes Y: "transferredAmountTo bridgeAddress token caller stepsInit = Y"
  assumes Z: "transferredAmountFrom bridgeAddress token caller stepsInit = Z"
  assumes W: "paidBackAmountFrom tokenDepositAddress token caller stepsAllBD = W"
  shows "\<exists> contracts' steps. reachableFrom contractsBD contracts' steps \<and>
                             paidBackAmountFrom tokenDepositAddress token caller steps + W + Z = X + Y \<and>
                             (\<nexists> stateRoot. UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) stateRoot \<in> set steps)"
proof-

  define NCDepositSteps where
    "NCDepositSteps = nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllBD"
  define CANCEL_fun where 
    "CANCEL_fun = (\<lambda> step. CANCEL_WD tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step)
                                    (generateClaimProof contractsLastUpdate' (DEPOSIT_id step)))"
  define CANCEL_WD_steps where 
    "CANCEL_WD_steps = map CANCEL_fun NCDepositSteps"
  define contractsC where 
    "contractsC = foldr (\<lambda> s c. snd (executeStep c 0 \<lparr> timestamp = 0 \<rparr> s)) CANCEL_WD_steps contractsBD"


  have "\<forall> step \<in> set NCDepositSteps. 
           step = DEPOSIT tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step) \<and>
           step \<in> set (depositsTo tokenDepositAddress token caller stepsAllBD) \<and>
           \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
           \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsAllBD"
    unfolding NCDepositSteps_def nonClaimedBeforeNonCanceledDepositsTo_def depositsTo_def
    by auto

  moreover 
  have "distinct (map DEPOSIT_id NCDepositSteps)"
    by (metis (mono_tags, lifting) InitBD.reachableFromInitI NCDepositSteps_def distinctDepositsToIDs distinct_map_filter nonClaimedBeforeNonCanceledDepositsTo_def)

  ultimately 
  
  have "reachableFrom contractsBD contractsC CANCEL_WD_steps"
    unfolding contractsC_def CANCEL_WD_steps_def
  proof (induction NCDepositSteps)
    case Nil
    then show ?case
      by (simp add: reachableFrom_base)
  next
    case (Cons step NCDepositSteps)
    define C where "C = foldr (\<lambda>s c. snd (executeStep c 0 \<lparr>timestamp = 0\<rparr> s)) (map CANCEL_fun NCDepositSteps) contractsBD"
    interpret BD': BridgeDead where contractsBD = C and stepsBD = "map CANCEL_fun NCDepositSteps @ stepsBD"
      by (smt (verit, ccfv_threshold) BridgeDead.intro BridgeDead_axioms_def C_def Cons.IH Cons.prems(1) Cons.prems(2) InitUpdate_axioms LastUpdate_axioms bridgeDead deathStep distinct.simps(2) list.set_intros(2) list.simps(9) notBridgeDead' reachableFromContractsBD reachableFromTrans stateRootNonZero)
    interpret BD: BridgeDeadInitFirstUpdate where contractsBD = C and stepsBD = "map CANCEL_fun NCDepositSteps @ stepsBD"
    proof
      have "updatesNonZero (map CANCEL_fun NCDepositSteps)"
        unfolding CANCEL_fun_def updatesNonZero_def
        by auto
      then show "updatesNonZero BD'.stepsAllBD"
        using updatesNonZeroInit
        unfolding BD'.stepsAllBD_def stepsAllBD_def
        by (simp add: updatesNonZero_def)
    next
      show "BD'.stepsAllBD \<noteq> [] \<and>
            last BD'.stepsAllBD = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
        using firstUpdate
        unfolding BD'.stepsAllBD_def stepsAllBD_def
        by auto
    qed

    have "\<exists>contractsCancel.
         reachableFrom C contractsCancel
          [CANCEL_WD tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step) (generateClaimProof contractsLastUpdate' (DEPOSIT_id step))]"
    proof (rule BD.cancelPossible)
      show "DEPOSIT tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step) \<in> set BD'.stepsAllBD"
        using Cons.prems unfolding BD'.stepsAllBD_def stepsAllBD_def depositsTo_def
        by (auto split: if_split_asm)
    next
      show "properToken contractsInit tokenDepositAddress bridgeAddress token"
        by fact
    next
      show "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"
        by fact
    next
      show "caller \<noteq> tokenDepositAddress"
        by fact
    next
      show "\<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit"
        by (simp add: Cons.prems)
    next
      have "\<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) (map CANCEL_fun NCDepositSteps)"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain caller' amount' proof' where
         "CANCEL_WD tokenDepositAddress caller' (DEPOSIT_id step) token amount' proof'
         \<in> set (map CANCEL_fun NCDepositSteps)"
          unfolding isCanceledID_def
          by auto
        then have "DEPOSIT_id step \<in> set (map DEPOSIT_id NCDepositSteps)"
          unfolding CANCEL_fun_def
          by auto
        then show False
          using Cons.prems(2)
          by auto
      qed
      then show "\<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) BD'.stepsAllBD"
        using Cons.prems
        unfolding stepsAllBD_def BD'.stepsAllBD_def
        unfolding isCanceledID_def
        by auto
    qed

    then have "fst (executeStep C 0 \<lparr>timestamp = 0\<rparr> (CANCEL_fun step)) = Success"
      unfolding CANCEL_fun_def (* WRONG BLOCK *)
      sorry
    then have "executeStep C 0 \<lparr>timestamp = 0\<rparr> (CANCEL_fun step) = (Success, snd (executeStep C 0 \<lparr>timestamp = 0\<rparr> (CANCEL_fun step)))"
      by (metis prod.collapse)
    then show ?case
      using Cons C_def reachableFrom_step 
      by auto
  qed

  have pbC: "paidBackAmountFrom tokenDepositAddress token caller CANCEL_WD_steps = 
             nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllBD"
    unfolding paidBackAmountFrom_def CANCEL_WD_steps_def CANCEL_fun_def releasedAmountFrom_def releasesFrom_def withdrawnAmountFrom_def withdrawalsFrom_def canceledAmountFrom_def cancelsFrom_def nonClaimedBeforeNonCanceledDepositsAmountTo_def NCDepositSteps_def
    by (auto simp add: comp_def)

  define NRBurnSteps where 
    "NRBurnSteps = nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllBD"
  define RELEASE_fun where 
    "RELEASE_fun = (\<lambda> step. RELEASE tokenDepositAddress caller (BURN_id step) token (BURN_amount step)
                            (generateBurnProof contractsLastUpdate' (BURN_id step)))"
  define RELEASE_steps where
    "RELEASE_steps = map RELEASE_fun NRBurnSteps"
  define contractsR where 
    "contractsR = foldr (\<lambda> s c. snd (executeStep c 0 \<lparr> timestamp = 0 \<rparr> s)) RELEASE_steps contractsC"


  have "\<forall> step \<in> set NRBurnSteps. 
           step = BURN bridgeAddress caller (BURN_id step) token (BURN_amount step) \<and>
           step \<in> set (burnsTo bridgeAddress token caller stepsInit) \<and>
           \<not> isReleasedID tokenDepositAddress token (BURN_id step) stepsAllBD"
    unfolding NRBurnSteps_def nonReleasedBurnsTo_def burnsTo_def
    by auto

  moreover 

  have "distinct (map BURN_id NRBurnSteps)"
    by (metis NRBurnSteps_def distinctBurnsToIDs distinct_map_filter nonReleasedBurnsTo_def reachableFromInitI)

  ultimately

  have "reachableFrom contractsC contractsR RELEASE_steps"
    unfolding contractsR_def RELEASE_steps_def
  proof (induction NRBurnSteps)
    case Nil
    then show ?case
      by (simp add: reachableFrom_base)
  next
    case (Cons step NRBurnSteps)
    define R where "R = foldr (\<lambda>s c. snd (executeStep c 0 \<lparr>timestamp = 0\<rparr> s)) (map RELEASE_fun NRBurnSteps) contractsC"
    have "reachableFrom contractsDead R (map RELEASE_fun NRBurnSteps @ CANCEL_WD_steps @ stepsBD)"
      using Cons.prems(2) R_def \<open>reachableFrom contractsBD contractsC CANCEL_WD_steps\<close> local.Cons(1) local.Cons(2) reachableFromTrans by force
    then interpret BD': BridgeDead where contractsBD = R and stepsBD = "map RELEASE_fun NRBurnSteps @ CANCEL_WD_steps @ stepsBD"
      by (metis BridgeDead.intro BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms bridgeDead deathStep notBridgeDead' stateRootNonZero)
    interpret BD: BridgeDeadInitFirstUpdate where contractsBD = R and stepsBD = "map RELEASE_fun NRBurnSteps @ CANCEL_WD_steps @ stepsBD"
    proof
      show "BD'.stepsAllBD \<noteq> [] \<and> last BD'.stepsAllBD = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
        using firstUpdate
        unfolding BD'.stepsAllBD_def stepsAllBD_def
        by auto
    next
      have "updatesNonZero (map RELEASE_fun NRBurnSteps @ CANCEL_WD_steps)"
        unfolding CANCEL_WD_steps_def CANCEL_fun_def RELEASE_fun_def updatesNonZero_def
        by auto
      then show "updatesNonZero BD'.stepsAllBD"
        unfolding BD'.stepsAllBD_def
        using updatesNonZeroInit
        unfolding BD'.stepsAllBD_def stepsAllBD_def
        by (simp add: updatesNonZero_def)
    qed

    have "let proof = generateBurnProof contractsLastUpdate' (BURN_id step)
           in fst (callRelease R tokenDepositAddress (message caller 0) (BURN_id step) token (BURN_amount step) proof) = Success"
    proof (rule BD.releasePossibleAfterBurnAndUpdateBridgeDead)
      show "properToken contractsInit tokenDepositAddress bridgeAddress token"
        by fact
    next
      show "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"
        by fact
    next
      show "caller \<noteq> tokenDepositAddress"
        by fact
    next
      show "sender (message caller 0) = caller"
        by simp
    next
      show "BURN bridgeAddress caller (BURN_id step) token (BURN_amount step) \<in> set stepsInit"
        using Cons.prems
        unfolding burnsTo_def
        by auto
    next
      show "getRelease (the (tokenDepositState R tokenDepositAddress)) (BURN_id step) = False"
      proof (rule getReleaseNoReleaseFalse)
        show "reachableFrom contractsInit R (map RELEASE_fun NRBurnSteps @ CANCEL_WD_steps @ stepsAllBD)"
          using BD'.InitBD.reachableFromInitI BD'.stepsAllBD_def stepsAllBD_def by force
      next
        show "getRelease (the (tokenDepositState contractsInit tokenDepositAddress)) (BURN_id step) = False"
          using releasesEmpty by presburger
      next
        show "\<not> isReleasedID tokenDepositAddress token (BURN_id step)
             (map RELEASE_fun NRBurnSteps @ CANCEL_WD_steps @ stepsAllBD)"
        proof-
          have "\<not> isReleasedID tokenDepositAddress token (BURN_id step) CANCEL_WD_steps"
            unfolding CANCEL_WD_steps_def isReleasedID_def CANCEL_fun_def
            by auto
          moreover
          have "\<not> isReleasedID tokenDepositAddress token (BURN_id step) (map RELEASE_fun NRBurnSteps)"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then obtain caller' amount' proof' where
              "RELEASE tokenDepositAddress caller' (BURN_id step) token amount' proof' \<in> set (map RELEASE_fun NRBurnSteps)"
              unfolding isReleasedID_def
              by auto
            then have "BURN_id step \<in> set (map BURN_id NRBurnSteps)"
              unfolding RELEASE_fun_def
              by auto
            then show False
              using Cons.prems(2)
              by simp
          qed
          ultimately
          show ?thesis
            using Cons.prems(1)
            by (simp add: isReleasedID_def)
        qed
      qed
    qed
    then have "fst (executeStep R 0 \<lparr>timestamp = 0\<rparr> (RELEASE_fun step)) = Success"
      unfolding RELEASE_fun_def
      by (simp add: Let_def)
    then have "executeStep R 0 \<lparr>timestamp = 0\<rparr> (RELEASE_fun step) = (Success, snd (executeStep R 0 \<lparr>timestamp = 0\<rparr> (RELEASE_fun step)))"
      by (metis prod.collapse)
    then show ?case
      using Cons R_def reachableFrom_step 
      by auto
  qed

  have pbR: "paidBackAmountFrom tokenDepositAddress token caller RELEASE_steps =
             nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllBD"
    unfolding paidBackAmountFrom_def RELEASE_steps_def RELEASE_fun_def releasedAmountFrom_def releasesFrom_def withdrawnAmountFrom_def withdrawalsFrom_def canceledAmountFrom_def cancelsFrom_def nonReleasedBurnedAmountTo_def NRBurnSteps_def
    by (simp add: comp_def)

  let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
  define amount where "amount = accountBalance contractsLastUpdate' ?mintedToken caller"


  interpret BD': BridgeDead where contractsBD=contractsR and stepsBD = "RELEASE_steps @ CANCEL_WD_steps @ stepsBD"
    using BridgeDead_axioms_def BridgeDead_def InitUpdate_axioms LastUpdate_axioms \<open>reachableFrom contractsBD contractsC CANCEL_WD_steps\<close> \<open>reachableFrom contractsC contractsR RELEASE_steps\<close> bridgeDead deathStep notBridgeDead' reachableFromContractsBD reachableFromTrans stateRootNonZero by presburger
  interpret BD: BridgeDeadInitFirstUpdate where contractsBD=contractsR and stepsBD = "RELEASE_steps @ CANCEL_WD_steps @ stepsBD"
  proof
    show "BD'.stepsAllBD \<noteq> [] \<and> last BD'.stepsAllBD = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
      using firstUpdate
      unfolding BD'.stepsAllBD_def stepsAllBD_def
      by auto
  next
    have "updatesNonZero (RELEASE_steps @ CANCEL_WD_steps)"
      unfolding CANCEL_WD_steps_def CANCEL_fun_def RELEASE_steps_def RELEASE_fun_def updatesNonZero_def
      by auto
    then show "updatesNonZero BD'.stepsAllBD"
      unfolding BD'.stepsAllBD_def
      using updatesNonZeroInit
      unfolding BD'.stepsAllBD_def stepsAllBD_def
      by (simp add: updatesNonZero_def)
  qed


  have noDeposits:
     "depositsTo tokenDepositAddress token caller (RELEASE_steps @ CANCEL_WD_steps @ stepsAllBD) =
      depositsTo tokenDepositAddress token caller stepsAllBD"
  proof-
    have "depositsTo tokenDepositAddress token caller RELEASE_steps = []"
      unfolding RELEASE_steps_def RELEASE_fun_def
      by (induction NRBurnSteps, auto)
    moreover
    have "depositsTo tokenDepositAddress token caller CANCEL_WD_steps = []"
      unfolding CANCEL_WD_steps_def CANCEL_fun_def
      by (induction NCDepositSteps, auto)
    ultimately
    show ?thesis
      by (auto simp add: depositedAmountTo_def depositsTo_def)
  qed


  have allCanceled: "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit (RELEASE_steps @ CANCEL_WD_steps @ stepsAllBD) = []"
  proof-
    have "\<forall> step \<in> set (depositsTo tokenDepositAddress token caller stepsAllBD). 
         \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<longrightarrow>
         isCanceledID tokenDepositAddress token (DEPOSIT_id step) (RELEASE_steps @ CANCEL_WD_steps @ stepsAllBD)"
    proof safe
      fix step
      assume *: "step \<in> set (depositsTo tokenDepositAddress token caller stepsAllBD)"
                "\<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit"
      show "isCanceledID tokenDepositAddress token (DEPOSIT_id step) (RELEASE_steps @ CANCEL_WD_steps @ stepsAllBD)"
      proof (cases "isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsAllBD")
        case True
        then show ?thesis
          by (auto simp add: isCanceledID_def)
      next
        case False
        then have "step \<in> set NCDepositSteps"
          using *
          unfolding NCDepositSteps_def nonClaimedBeforeNonCanceledDepositsTo_def
          by auto
        then have "isCanceledID tokenDepositAddress token (DEPOSIT_id step) CANCEL_WD_steps"
          unfolding isCanceledID_def CANCEL_WD_steps_def CANCEL_fun_def
          by auto
        then show ?thesis
           by (auto simp add: isCanceledID_def)
      qed
    qed
    then show ?thesis
       using noDeposits
       unfolding nonClaimedBeforeNonCanceledDepositsTo_def
       by (metis (no_types, lifting) filter_False)
  qed

  have allReleased: "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit (RELEASE_steps @ CANCEL_WD_steps @ stepsAllBD) = []"
  proof-
    have "\<forall> step \<in> set (burnsTo bridgeAddress token caller stepsInit). isReleasedID tokenDepositAddress token (BURN_id step) (RELEASE_steps @ CANCEL_WD_steps @ stepsAllBD)"
    proof safe
      fix step
      assume "step \<in> set (burnsTo bridgeAddress token caller stepsInit)"
      show "isReleasedID tokenDepositAddress token (BURN_id step) (RELEASE_steps @ CANCEL_WD_steps @ stepsAllBD)"
      proof (cases "isReleasedID tokenDepositAddress token (BURN_id step) stepsAllBD")
        case True
        then show ?thesis
          by (auto simp add: isReleasedID_def)
      next
        case False
        then have "step \<in> set NRBurnSteps"
          using \<open>step \<in> set (burnsTo bridgeAddress token caller stepsInit)\<close>
          unfolding NRBurnSteps_def nonReleasedBurnsTo_def
          by auto
        then have "isReleasedID tokenDepositAddress token (BURN_id step) (RELEASE_steps)"
          unfolding RELEASE_steps_def RELEASE_fun_def isReleasedID_def
          by auto
        then show ?thesis
          unfolding isReleasedID_def
          by auto
      qed
    qed
    then show ?thesis
      unfolding nonReleasedBurnsTo_def
      by auto
  qed

  show ?thesis
  proof (cases "amount > 0 \<and> getTokenWithdrawn (the (tokenDepositState contractsBD tokenDepositAddress)) (hash2 caller token) = False")
    case True
    define Proof where "Proof = generateBalanceProof contractsLastUpdate' ?mintedToken (sender (message caller 0)) amount"
    have "fst (callWithdrawWhileDead contractsR tokenDepositAddress (message caller 0) \<lparr>timestamp = 0\<rparr> token amount Proof) = Success"
      unfolding Proof_def
    proof (rule BD.withdrawPossibe)
      show "properToken contractsInit tokenDepositAddress bridgeAddress token"
        by fact
    next
      show "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"
        by fact
    next
      show "accountBalance contractsLastUpdate' (mintedTokenB contractsInit bridgeAddress token) (sender (message caller 0)) = amount"
        unfolding amount_def
        by simp
    next
      show "tokenDepositAddress \<noteq> sender (message caller 0)"
        using assms(3)
        by simp
    next
      show "getTokenWithdrawn (the (tokenDepositState contractsR tokenDepositAddress)) (hash2 (sender (message caller 0)) token) = False"
      proof-
        have "getTokenWithdrawn (the (tokenDepositState contractsC tokenDepositAddress)) (hash2 caller token) = False"
          using reachableFromGetTokenWithdrawnNoWithdrawNoChange[OF \<open>reachableFrom contractsBD contractsC CANCEL_WD_steps\<close>]
          using \<open>amount > 0 \<and> getTokenWithdrawn (the (tokenDepositState contractsBD tokenDepositAddress)) (hash2 caller token) = False\<close>
          unfolding CANCEL_WD_steps_def CANCEL_fun_def
          by auto
        then show ?thesis
          using reachableFromGetTokenWithdrawnNoWithdrawNoChange[OF \<open>reachableFrom contractsC contractsR RELEASE_steps\<close>]
          unfolding RELEASE_steps_def RELEASE_fun_def
          by auto
      qed
    qed
    then obtain contracts' where wwd: "callWithdrawWhileDead contractsR tokenDepositAddress (message caller 0) \<lparr>timestamp = 0\<rparr> token amount Proof = (Success, contracts')"
      by (metis prod.collapse)

    define WITHDRAW_WD_step where "WITHDRAW_WD_step = WITHDRAW_WD tokenDepositAddress caller token amount Proof"
    have wwd: "reachableFrom contractsR contracts' [WITHDRAW_WD_step]"
      using wwd 
      unfolding WITHDRAW_WD_step_def
      by (metis executeStep.simps(8) reachableFrom_base reachableFrom_step)

    have pbW: "paidBackAmountFrom tokenDepositAddress token caller [WITHDRAW_WD_step] = accountBalance contractsLastUpdate' ?mintedToken caller"
      unfolding paidBackAmountFrom_def WITHDRAW_WD_step_def releasedAmountFrom_def releasesFrom_def withdrawnAmountFrom_def withdrawalsFrom_def canceledAmountFrom_def cancelsFrom_def
      unfolding amount_def
      by simp

    have "reachableFrom contractsBD contracts' (WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps)"
        using \<open>reachableFrom contractsBD contractsC CANCEL_WD_steps\<close> \<open>reachableFrom contractsC contractsR RELEASE_steps\<close> wwd
        by (meson reachableFromSingleton reachableFromTrans reachableFrom_step)
    then interpret BD'': BridgeDead where contractsBD=contracts' and stepsBD = "WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps @ stepsBD"
      by (smt (verit) BridgeDead.intro BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms append.assoc append_Cons bridgeDead deathStep notBridgeDead' reachableFromContractsBD reachableFromTrans stateRootNonZero)
    interpret BD'': BridgeDeadInitFirstUpdate where contractsBD=contracts' and stepsBD = "WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps @ stepsBD"
    proof
      show "BD''.stepsAllBD \<noteq> [] \<and> last BD''.stepsAllBD = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
        using firstUpdate
        unfolding stepsAllBD_def BD''.stepsAllBD_def
        by auto
    next
    have "updatesNonZero (WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps)"
      unfolding WITHDRAW_WD_step_def CANCEL_WD_steps_def CANCEL_fun_def RELEASE_steps_def RELEASE_fun_def updatesNonZero_def
      by auto
    then show "updatesNonZero BD''.stepsAllBD"
      unfolding BD''.stepsAllBD_def
      using updatesNonZeroInit
      unfolding BD'.stepsAllBD_def stepsAllBD_def
      by (simp add: updatesNonZero_def)
    qed

    show ?thesis
    proof (rule_tac x="contracts'" in exI, rule_tac x="WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps" in exI, safe)
      show "reachableFrom contractsBD contracts' (WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps)"
        by fact
    next
      show "paidBackAmountFrom tokenDepositAddress token caller (WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps) + W + Z =
            X + Y"
      proof-
        have "paidBackAmountFrom tokenDepositAddress token caller (WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps) + W = 
              paidBackAmountFrom tokenDepositAddress token caller BD''.stepsAllBD"
          using W[symmetric]
          unfolding BD''.stepsAllBD_def stepsAllBD_def
          by (metis append.assoc append_Cons paidBackAmountFromAppend)
        moreover
        have "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsLastUpdate' contracts' = 0"
          using executeStepNonWithdrawnBalanceBeforeAfter[where msg="message caller 0"]
          by (metis WITHDRAW_WD_step_def executeStep.simps(8) reachableFromSingleton senderMessage wwd)
        moreover
        have "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit
             (WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps @ stepsAllBD) = []"
          using allCanceled unfolding WITHDRAW_WD_step_def
          by simp
        then have "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit  BD''.stepsAllBD = 0"
          unfolding BD''.stepsAllBD_def stepsAllBD_def
          by (simp add: nonClaimedBeforeNonCanceledDepositsAmountTo_def)
        moreover
        have "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
              (WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps @ stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) = []"
          using allReleased
          unfolding WITHDRAW_WD_step_def
          unfolding stepsAllBD_def
          by simp
        then have "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit BD''.stepsAllBD = 0"
          unfolding nonReleasedBurnedAmountTo_def BD''.stepsAllBD_def stepsAllBD_def
          by simp
        moreover
        have "accountBalance contractsInit (mintedTokenTD contractsInit tokenDepositAddress token) caller = 0"
          by (metis assms(1) assms(2) finiteBalances_def mintedTokenITDB properTokenFiniteBalancesMinted totalBalanceZero)
        moreover
        have "depositedAmountTo tokenDepositAddress token caller BD''.stepsAllBD =
              depositedAmountTo tokenDepositAddress token caller stepsAllBD"
        proof-
          have "depositedAmountTo tokenDepositAddress token caller [WITHDRAW_WD_step] = 0"
            unfolding WITHDRAW_WD_step_def
            by simp
          then show ?thesis
            using noDeposits
            by (auto simp add: BD''.stepsAllBD_def stepsAllBD_def depositedAmountTo_def depositsTo_def)
        qed
        ultimately
        show ?thesis
          using BD''.userTokensInvariant[OF assms(1), of caller] 
          using X Y Z W pbC pbR
          by (simp add: paidBackAmountFrom_def)
      qed
    next
      fix stateRoot
      show "UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) stateRoot \<in> set (WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps) \<Longrightarrow> False"
        unfolding WITHDRAW_WD_step_def RELEASE_steps_def RELEASE_fun_def CANCEL_WD_steps_def CANCEL_fun_def
        by auto
    qed
  next
    case False

    have r: "reachableFrom contractsBD contractsR (RELEASE_steps @ CANCEL_WD_steps)"
     using \<open>reachableFrom contractsBD contractsC CANCEL_WD_steps\<close> \<open>reachableFrom contractsC contractsR RELEASE_steps\<close>
     by (meson reachableFromTrans reachableFrom_step)

    show ?thesis
    proof (rule_tac x=contractsR in exI, rule_tac x=" RELEASE_steps @ CANCEL_WD_steps" in exI, safe)
      show "reachableFrom contractsBD contractsR (RELEASE_steps @ CANCEL_WD_steps)"
        by fact
    next
      show "paidBackAmountFrom tokenDepositAddress token caller (RELEASE_steps @ CANCEL_WD_steps) + W + Z = X + Y"
      proof-
        have "paidBackAmountFrom tokenDepositAddress token caller (RELEASE_steps @ CANCEL_WD_steps) + W = 
              paidBackAmountFrom tokenDepositAddress token caller BD'.stepsAllBD"
          using W[symmetric]
          unfolding BD'.stepsAllBD_def stepsAllBD_def
          by (metis append.assoc append_Cons paidBackAmountFromAppend)
        moreover
        have "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsLastUpdate' contractsR = 0"
          using False reachableFromGetTokenWithdrawn[OF r]
          unfolding amount_def nonWithdrawnBalanceBefore_def
          by auto
        moreover
        have "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit  BD'.stepsAllBD = 0"
          using allCanceled 
          unfolding BD'.stepsAllBD_def stepsAllBD_def
          by (simp add: nonClaimedBeforeNonCanceledDepositsAmountTo_def)
        moreover
        have "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit BD'.stepsAllBD = 0"
          using allReleased
          unfolding nonReleasedBurnedAmountTo_def BD'.stepsAllBD_def stepsAllBD_def
          by simp
        moreover
        have "accountBalance contractsInit (mintedTokenTD contractsInit tokenDepositAddress token) caller = 0"
          by (metis assms(1) assms(2) finiteBalances_def mintedTokenITDB properTokenFiniteBalancesMinted totalBalanceZero)
        ultimately
        show ?thesis
          using noDeposits
          using BD.userTokensInvariant[OF assms(1), of caller] 
          using X Y Z W pbC pbR
          unfolding BD'.stepsAllBD_def stepsAllBD_def
          by (simp add: paidBackAmountFrom_def depositedAmountTo_def)
      qed
    next
      fix stateRoot
      show "UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) stateRoot \<in> set (RELEASE_steps @ CANCEL_WD_steps) \<Longrightarrow> False"
        unfolding RELEASE_steps_def RELEASE_fun_def CANCEL_WD_steps_def CANCEL_fun_def
        by auto
    qed
  qed
qed

end

end