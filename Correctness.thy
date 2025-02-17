theory Correctness
imports BridgeProperties.TokenInvariants
begin

(**************************************************************************************************)
section \<open>Correctness theorems\<close>
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
  assumes "reachable contractsD contractsLastUpdate' steps"
  \<comment> \<open>the bridge is not dead in the reached state\<close>
  assumes "\<not> bridgeDead  contractsLastUpdate' tokenDepositAddress"

  \<comment> \<open>there was no previous claim\<close>
  assumes "getClaimB contractsLU bridgeAddress ID = False"

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
    show "getDepositTD contractsLastUpdate' tokenDepositAddress ID = hash3 (sender msg) token amount"
      using reachableGetDepositBridgeNotDead
      using \<open>reachable contractsD contractsLastUpdate' steps\<close> hash3_nonzero assms callDepositWritesHash
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
    by (smt (verit, ccfv_threshold) callClaimI callDepositProperToken option.collapse properSetupLU properSetup_def properTokenReachable properToken_def reachableLastUpdate'LU stateBridge_def)
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
  assumes "getWithdrawalB contracts bridgeAddress ID = 0"
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
  show "getWithdrawalB contracts bridgeAddress ID = 0"
    by fact
qed

end

context InitFirstUpdateLastUpdate
begin

text \<open>After a successful burn and a state update (while the bridge is alive), a release can be made\<close>
theorem releasePossibleAfterBurnAndUpdateBridgeNotDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"

  assumes "tokenNotMinted contractsInit token"
  assumes "mintedUnique contractsInit bridgeAddress token"
  assumes "noActionOfToken (mintedTokenB contractsInit bridgeAddress token) stepsInit"

  \<comment> \<open>A burn is successfully made\<close>
  assumes "BURN bridgeAddress caller ID token amount \<in> set stepsInit"
  \<comment> \<open>the bridge is not dead in the reached state\<close>
  assumes "\<not> bridgeDead  contractsLU tokenDepositAddress"
  \<comment> \<open>there was no previous release\<close>
  assumes "getReleaseTD contractsLU tokenDepositAddress ID = False"

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
    using InitFirstUpdate_LU.ERC20stateINonNone assms(1) by blast
next
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  have "?BURN_step \<in> set (nonReleasedBurns tokenDepositAddress bridgeAddress token stepsInit stepsAllLU)"
  proof-
    have "?BURN_step \<in> set (burns bridgeAddress token stepsInit)"
      unfolding nonReleasedBurns_def
      using assms(6)
      by (simp add: burns_def)
    moreover
    have "\<not> isReleasedID tokenDepositAddress token ID stepsAllLU"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain caller' amount' proof' where "RELEASE tokenDepositAddress caller' ID token amount' proof' \<in> set stepsAllLU"
        unfolding isReleasedID_def
        by auto
      then have "getReleaseTD contractsLU tokenDepositAddress ID = True"
        using reachableInitLU reachableReleaseSetsFlag by blast
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
    using tokenDepositBalanceBridgeNotDead[OF assms(1) assms(7) assms(2) assms(3-5)]
    by simp
next
  show "getReleaseTD contractsLU tokenDepositAddress ID = False"
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
    have "getWithdrawalB contractsLastUpdate' bridgeAddress ID =
          hash3 caller token amount"
      using reachableBurnSetsFlag[OF reachableInitI \<open>BURN bridgeAddress caller ID token amount \<in> set stepsInit\<close>]
      by blast
    then show "getWithdrawal (the (bridgeState contractsLastUpdate' (bridgeAddressTD contractsLU tokenDepositAddress))) ID =
          hash3 (sender msg') token amount"
      using \<open>sender msg' = caller\<close> bridgeAddressLU by blast
  next
    have "generateStateRoot contractsLastUpdate' = stateRoot"
      by simp
    moreover
    have "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
      by (metis assms(7) reachableDeadState reachableLastUpdate'LU)
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


context BridgeDeadInitFirstUpdate 
begin

text \<open>After a successful burn and a state update (while the bridge is alive), a release can be made even if the bridge is dead\<close>
theorem releasePossibleAfterBurnAndUpdateBridgeDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"

  assumes "tokenNotMinted contractsInit token"
          "mintedUnique contractsInit bridgeAddress token"
          "noActionOfToken (mintedTokenB contractsInit bridgeAddress token) stepsInit"

  \<comment> \<open>A burn is successfully made\<close>
  assumes "BURN bridgeAddress caller ID token amount \<in> set stepsInit"
  \<comment> \<open>there was no previous release\<close>
  assumes "getReleaseTD contractsBD tokenDepositAddress ID = False"

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
    using Init_BD.tokenDepositStateINotNone
    using Init_BD.stateOracleAddressTDI Init_BD.stateOracleStateINotNone
    using Init_BD.proofVerifierStateNotNone
    by presburger+
next
  show "ERC20state contractsBD token \<noteq> None"
    using Init_BD.ERC20stateINonNone assms(1) by blast
next
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  have "?BURN_step \<in> set (nonReleasedBurns tokenDepositAddress bridgeAddress token stepsInit stepsAllBD)"
  proof-
    have "?BURN_step \<in> set (burns bridgeAddress token stepsInit)"
      unfolding nonReleasedBurns_def
      using assms(6)
      by (simp add: burns_def)
    moreover
    have "\<not> isReleasedID tokenDepositAddress token ID stepsAllBD"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain caller' amount' proof' where "RELEASE tokenDepositAddress caller' ID token amount' proof' \<in> set stepsAllBD"
        unfolding isReleasedID_def
        by auto
      then have "getReleaseTD contractsBD tokenDepositAddress ID = True"
        using reachableReleaseSetsFlag Init_BD.reachableInitI 
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
    using assms le_add2
    by presburger
next
  show "getReleaseTD contractsBD tokenDepositAddress ID = False"
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
      using Init_BD.bridgeBridgeAddress bridgeStateINotNone by blast
    then show "bridgeState contractsLastUpdate' (bridgeAddressTD contractsBD tokenDepositAddress)  = 
               Some (the (bridgeState contractsLastUpdate' (bridgeAddressTD contractsBD tokenDepositAddress)))"
      by simp
  next
    have "getWithdrawalB contractsLastUpdate' bridgeAddress ID =
          hash3 caller token amount"
      using reachableBurnSetsFlag[OF reachableInitI \<open>BURN bridgeAddress caller ID token amount \<in> set stepsInit\<close>]
      by blast
    then show "getWithdrawal (the (bridgeState contractsLastUpdate' (bridgeAddressTD contractsBD tokenDepositAddress))) ID =
          hash3 (sender msg') token amount"
      using \<open>sender msg' = caller\<close> 
      using Init_BD.bridgeBridgeAddress by blast
  next
    show "generateStateRoot contractsLastUpdate' = snd (lastValidStateTD contractsBD tokenDepositAddress)"
      by (simp add: InitUpdateBridgeNotDeadLastValidState_BD.getLastValidStateLVS)
  qed
  then show "?P"
    by simp
qed


theorem cancelPossible:
  \<comment> \<open>Tokens are properly initialized\<close>
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  \<comment> \<open>Initially there are no minted tokens\<close>
  assumes "totalMinted contractsInit bridgeAddress token = 0"

  assumes "tokenNotMinted contractsInit token"
          "mintedUnique contractsInit bridgeAddress token"
          "noActionOfToken (mintedTokenB contractsInit bridgeAddress token) stepsInit"

  \<comment> \<open>User has made a deposit that he has not claimed before the bridge died\<close>
  assumes "DEPOSIT tokenDepositAddress caller ID token amount \<in> set stepsAllBD"
  assumes "\<not> isClaimedID bridgeAddress token ID stepsInit"
  \<comment> \<open>User has not canceled this deposit\<close>
  assumes "\<not> isCanceledID tokenDepositAddress token ID stepsAllBD"
  \<comment> \<open>Caller is not the bridge itself\<close>
  assumes "caller \<noteq> tokenDepositAddress"
  shows "\<exists> contractsCancel. reachable contractsBD contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount (generateClaimProof contractsLastUpdate' ID)]"
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
        by (metis Init_BD.properSetupI properSetup_def)
    next
      show "proofVerifierState contractsBD (TokenDepositState.proofVerifier (the (tokenDepositState contractsBD tokenDepositAddress))) \<noteq> None"
        by (metis Init_BD.properSetupI properSetup_def)
    next
      show "ERC20state contractsBD token \<noteq> None"
        using Init_BD.ERC20stateINonNone assms(1) by blast
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
      have "getClaimB contractsLastUpdate' bridgeAddress ID = False"
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
        have "getClaimB contractsInit bridgeAddress ID = False"
          using claimsEmpty by blast
        ultimately show ?thesis
          using reachableGetClaimNoClaim[OF reachableInitI]
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
      show "getDepositTD  contractsBD tokenDepositAddress ID =
            hash3 (sender (message caller 0)) token amount"
        using  nonCanceledDepositGetDeposit 
             \<open>DEPOSIT tokenDepositAddress caller ID token amount \<in> set stepsAllBD\<close>
             \<open>\<not> isCanceledID tokenDepositAddress token ID stepsAllBD\<close>
             Init_BD.reachableInitI
        unfolding isCanceledID_def
        by (metis senderMessage)
    qed
    then show thesis
      using that
      by simp
  qed
  then show ?thesis
    by (metis executeStep.simps(7) prod.collapse reachable_base reachable_step)
qed

text \<open>If the user had some amount of tokens in the state in which the bridge died, 
      he can withdraw that amount\<close>
theorem withdrawPossible:
  \<comment> \<open>Tokens are properly initialized\<close>
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  \<comment> \<open>Initially there are no minted tokens\<close>
  assumes "totalMinted contractsInit bridgeAddress token = 0"

  assumes "tokenNotMinted contractsInit token"
          "mintedUnique contractsInit bridgeAddress token"
          "noActionOfToken (mintedTokenB contractsInit bridgeAddress token) stepsInit"

  \<comment> \<open>Caller had sufficient balance before the bridge died\<close>
  assumes "accountBalance contractsLastUpdate' (mintedTokenB contractsInit bridgeAddress token) (sender msg) = amount"
  \<comment> \<open>Caller has not yet withdrawn his balance\<close>
  assumes notWithdrawn: 
    "getTokenWithdrawnTD contractsBD tokenDepositAddress (hash2 (sender msg) token) = False"
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
    show "getTokenWithdrawnTD contractsBD tokenDepositAddress (hash2 (sender msg) token) = False"
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
            show "reachable contractsInit contractsLastUpdate' stepsInit"
              by simp
          next
            let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
            show "accountBalance contractsLastUpdate' ?mintedToken (sender msg) = amount"
              using assms
              using callBalanceOf by blast
          next
            show "accountBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) (sender msg) = 0"
              by fact
          qed (simp_all add: assms)
          moreover 
          have "\<nexists> amount proof. WITHDRAW_WD tokenDepositAddress (sender msg) token amount proof \<in> set stepsAllBD"
            using \<open>getTokenWithdrawnTD contractsBD tokenDepositAddress (hash2 (sender msg) token) = False\<close>
            using Init_BD.reachableInitI reachableGetTokenWithdrawnNoWithdraw by blast
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
        by (simp add: InitUpdateBridgeNotDeadLastValidState_BD.getLastValidStateLVS)
    next
      show "ERC20state contractsLastUpdate' (mintedTokenTD contractsBD tokenDepositAddress token) =
            Some (the (ERC20state contractsLastUpdate' (mintedTokenTD contractsBD tokenDepositAddress token)))"
        using assms(1)
        by (metis ERC20StateMintedTokenINotNone Init_BD.mintedTokenTDI option.collapse)
    next
      show "accountBalance contractsLastUpdate' (mintedTokenTD contractsBD tokenDepositAddress token) (sender msg) = amount"
        by (metis Init_BD.mintedTokenTDI assms(6) mintedTokenITDB)
    next
      show "generateBalanceProof contractsLastUpdate' (mintedTokenTD contractsBD tokenDepositAddress token) (sender msg) amount = Proof"
        unfolding Proof_def
        using Init_BD.mintedTokenTDI mintedTokenITDB by presburger
    qed
    then show "verifyBalanceProof () ?mintedToken (sender msg) amount 
               (snd (lastValidStateTD contractsBD tokenDepositAddress)) Proof"
      by blast
  qed    
qed

end

(**************************************************************************************************)
section \<open>Central theorem\<close>
(**************************************************************************************************)


context HashProofVerifier
begin

definition allTokensPaidBackEq where
  "allTokensPaidBackEq tokenDepositAddress bridgeAddress token caller stepsAll stepsInit \<equiv>
   paidBackAmountFrom tokenDepositAddress token caller stepsAll + 
   transferredAmountFrom bridgeAddress token caller stepsInit = 
   depositedAmountTo tokenDepositAddress token caller stepsAll + 
   transferredAmountTo bridgeAddress token caller stepsInit"

definition allTokensPaidBack where
  "allTokensPaidBack tokenDepositAddress bridgeAddress token caller stepsAll stepsInit \<equiv>
   paidBackAmountFrom tokenDepositAddress token caller stepsAll + 
   transferredAmountFrom bridgeAddress token caller stepsInit \<ge> 
   depositedAmountTo tokenDepositAddress token caller stepsAll + 
   transferredAmountTo bridgeAddress token caller stepsInit"

end

context BridgeDeadInitFirstUpdate
begin

theorem paybackPossibleBridgeDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"

  assumes "tokenNotMinted contractsInit token"
  assumes "mintedUnique contractsInit bridgeAddress token"
  assumes "noActionOfToken (mintedTokenB contractsInit bridgeAddress token) stepsInit"

  assumes "caller \<noteq> tokenDepositAddress"
  shows "\<exists> steps. (\<forall> step \<in> set steps. isCaller caller step) \<and>
                  executableSteps caller contractsBD steps \<and>
                  (\<forall> contracts' stepListsOther.
                     reachableInterleaved caller contractsBD contracts' steps stepListsOther \<longrightarrow>  
                     allTokensPaidBackEq tokenDepositAddress bridgeAddress token caller
                                         (interleaveSteps steps stepListsOther @ stepsAllBD)
                                         stepsInit)"
proof-
  define NCDepositSteps where
    "NCDepositSteps = nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllBD"
  define CANCEL_fun where 
    "CANCEL_fun = (\<lambda> step. CANCEL_WD tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step)
                                    (generateClaimProof contractsLastUpdate' (DEPOSIT_id step)))"
  define CANCEL_WD_steps where 
    "CANCEL_WD_steps = map CANCEL_fun NCDepositSteps"

  have "\<forall> step \<in> set NCDepositSteps. 
           step = DEPOSIT tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step) \<and>
           step \<in> set (depositsTo tokenDepositAddress token caller stepsAllBD) \<and>
           \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
           \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsAllBD"
    unfolding NCDepositSteps_def nonClaimedBeforeNonCanceledDepositsTo_def depositsTo_def
    by auto

  moreover 
  have "distinct (map DEPOSIT_id NCDepositSteps)"
    by (metis (mono_tags, lifting) Init_BD.reachableInitI NCDepositSteps_def distinctDepositsToIDs distinct_map_filter nonClaimedBeforeNonCanceledDepositsTo_def)

  ultimately 

  have "executableSteps caller contractsBD CANCEL_WD_steps"
    unfolding CANCEL_WD_steps_def
  proof (induction NCDepositSteps)
    case Nil
    then show ?case
      by simp
  next
    case (Cons step NCDepositSteps)
    then have "executableSteps caller contractsBD (map CANCEL_fun NCDepositSteps)"
      by auto
    moreover
    {
      fix contracts' stepListsOther
      assume r': "reachableInterleaved caller contractsBD contracts' (map CANCEL_fun NCDepositSteps) stepListsOther"

      have length: "length stepListsOther = length (map CANCEL_fun NCDepositSteps)"
        using r'
        by (metis reachableInterleavedLength)

      have "executableStep caller contracts' (CANCEL_fun step)"
        unfolding executableStep_def
      proof safe
        fix contractsS' stepsOther block blockNum
        assume "reachableOtherCaller caller contracts' contractsS' stepsOther"

        have step: 
             "step = DEPOSIT tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step)"
             "step \<in> set stepsAllBD"
          using Cons.prems
          by (auto simp add: depositsTo_def)

        have "reachable contractsDead contractsS' (stepsOther @ interleaveSteps (map CANCEL_fun NCDepositSteps) stepListsOther @ stepsBD)"
          by (meson \<open>reachableInterleaved caller contractsBD contracts' (map CANCEL_fun NCDepositSteps) stepListsOther\<close> \<open>reachableOtherCaller caller contracts' contractsS' stepsOther\<close> reachableInterleavedReachable reachableContractsBD reachableOtherCaller_def reachableTrans)
        then interpret BD: BridgeDead where contractsBD=contractsS' and stepsBD="stepsOther @ concat (map2 (#) (map CANCEL_fun NCDepositSteps) stepListsOther) @ stepsBD"
          by (metis BridgeDead.deadStateContractsDead BridgeDead.intro BridgeDead_axioms BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms deathStep notBridgeDead' stateRootNonZero)
        interpret BDIFU: BridgeDeadInitFirstUpdate  where contractsBD=contractsS' and stepsBD="stepsOther @ concat (map2 (#) (map CANCEL_fun NCDepositSteps) stepListsOther) @ stepsBD"
        proof
          show "BD.stepsAllBD \<noteq> [] \<and> last BD.stepsAllBD = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
            using BD.stepsAllBD_def InitFirstUpdate_Dead'.firstUpdate stepsBeforeDeath_def by force
        next
          show "stateRootInit \<noteq> 0"
            by (simp add: stateRootInitNonZero)
        qed
        have "\<exists>contractsCancel.
              reachable contractsS' contractsCancel
               [CANCEL_WD tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step) (generateClaimProof contractsLastUpdate' (DEPOSIT_id step))]"
        proof (rule BDIFU.cancelPossible)
          show "DEPOSIT tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step) \<in> set BD.stepsAllBD"
            using step
            unfolding BD.stepsAllBD_def stepsAllBD_def
            by auto
        next
          show "\<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit"
            using Cons.prems
            by auto
        next
          show "\<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) BD.stepsAllBD"
          proof-
            have "\<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsAllBD"
              using Cons.prems
              by auto
            moreover
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
            moreover
            have "\<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) (concat (stepsOther # stepListsOther))"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain caller' amount' proof' where
                 *: "CANCEL_WD tokenDepositAddress caller' (DEPOSIT_id step) token amount' proof'
                     \<in> set (concat (stepsOther # stepListsOther))"
                unfolding isCanceledID_def
                by auto
              moreover
              have "set (concat (stepsOther # stepListsOther)) \<subseteq> set BD.stepsAllBD"
                using setInterleaveSteps[of "map CANCEL_fun NCDepositSteps" stepListsOther] length 
                unfolding BD.stepsAllBD_def
                by auto
              ultimately have **: "CANCEL_WD tokenDepositAddress caller' (DEPOSIT_id step) token amount' proof' \<in> set BD.stepsAllBD"
                unfolding BD.stepsAllBD_def
                by blast
              have "\<forall> step \<in> set (concat (stepsOther # stepListsOther)). \<not> isCaller caller step"
                using \<open>reachableInterleaved caller contractsBD contracts' (map CANCEL_fun NCDepositSteps) stepListsOther\<close> 
                      \<open>reachableOtherCaller caller contracts' contractsS' stepsOther\<close>
                by (metis UnE concat.simps(2) reachableInterleavedOtherCaller reachableOtherCaller_def set_append)
              then have "caller \<noteq> caller'"
                using *
                by fastforce
              moreover
              have "step \<in> set BD.stepsAllBD"
                using step(2)
                by (auto simp add: BD.stepsAllBD_def stepsAllBD_def)
              ultimately
              show False
                using step(1) ** onlyDepositorCanCancelSteps
                by (metis BD.Init_BD.reachableInitI)
            qed
            moreover
            have "set (stepsOther @ interleaveSteps (map CANCEL_fun NCDepositSteps) stepListsOther) =
                  set (map CANCEL_fun NCDepositSteps) \<union> set (concat (stepsOther # stepListsOther))"
              using setInterleaveSteps[of "map CANCEL_fun NCDepositSteps" stepListsOther] length 
              by fastforce
            ultimately
            show ?thesis
              using set_zip_leftD set_zip_rightD
              unfolding BD.stepsAllBD_def stepsAllBD_def isCanceledID_def
              by fastforce
          qed
        qed fact+
        then show "fst (executeStep contractsS' block blockNum (CANCEL_fun step)) = Success"
          sorry (* arbitrary block *)
      qed
    }
    ultimately
    show ?case
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

  have "\<forall> step \<in> set NRBurnSteps. 
           step = BURN bridgeAddress caller (BURN_id step) token (BURN_amount step) \<and>
           step \<in> set (burnsTo bridgeAddress token caller stepsInit) \<and>
           \<not> isReleasedID tokenDepositAddress token (BURN_id step) stepsAllBD"
    unfolding NRBurnSteps_def nonReleasedBurnsTo_def burnsTo_def
    by auto

  moreover 

  have "distinct (map BURN_id NRBurnSteps)"
    by (metis NRBurnSteps_def distinctBurnsToIDs distinct_map_filter nonReleasedBurnsTo_def reachableInitI)

  ultimately

  have "\<forall> contracts' stepListsOther. reachableInterleaved caller contractsBD contracts' CANCEL_WD_steps stepListsOther \<longrightarrow> 
        executableSteps caller contracts' RELEASE_steps"
    unfolding RELEASE_steps_def
  proof (induction NRBurnSteps)
    case Nil
    then show ?case
      by simp
  next
    case (Cons step NRBurnSteps)
    show ?case
    proof safe
      fix contracts' stepListsOther
      assume "reachableInterleaved caller contractsBD contracts' CANCEL_WD_steps stepListsOther"
      then have "executableSteps caller contracts' (map RELEASE_fun NRBurnSteps)"
        using Cons.IH Cons.prems(1) Cons.prems(2) 
        by auto
      moreover
      {
        fix contracts'' stepListsOther' block blockNum contracts''' stepsOther
        assume "reachableInterleaved caller contracts' contracts'' (map RELEASE_fun NRBurnSteps) stepListsOther'"
        assume "reachableOtherCaller caller contracts'' contracts''' stepsOther"

        have "reachable contractsDead contracts''' (stepsOther @ interleaveSteps (map RELEASE_fun NRBurnSteps) stepListsOther' @
                                                       interleaveSteps (map CANCEL_fun NCDepositSteps) stepListsOther @ 
                                                       stepsBD)"
          using \<open>reachableInterleaved caller contracts' contracts'' (map RELEASE_fun NRBurnSteps) stepListsOther'\<close> 
          using \<open>reachableInterleaved caller contractsBD contracts' CANCEL_WD_steps stepListsOther\<close>
          using \<open>reachableOtherCaller caller contracts'' contracts''' stepsOther\<close>
          by (metis CANCEL_WD_steps_def reachableInterleavedReachable reachableContractsBD reachableOtherCaller_def reachableTrans)
        then interpret BD: BridgeDead where contractsBD=contracts''' and stepsBD="stepsOther @ interleaveSteps (map RELEASE_fun NRBurnSteps) stepListsOther' @ interleaveSteps (map CANCEL_fun NCDepositSteps) stepListsOther @ stepsBD"
          by (metis BridgeDead.intro BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms bridgeDead deathStep notBridgeDead' stateRootNonZero)
        interpret BDIFU: BridgeDeadInitFirstUpdate  where contractsBD=contracts''' and stepsBD="stepsOther @ interleaveSteps (map RELEASE_fun NRBurnSteps) stepListsOther' @ interleaveSteps (map CANCEL_fun NCDepositSteps) stepListsOther @ stepsBD"
        proof
          show "BD.stepsAllBD \<noteq> [] \<and> last BD.stepsAllBD = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
            using BD.stepsAllBD_def InitFirstUpdate_Dead'.firstUpdate stepsBeforeDeath_def by auto
        next
          show "stateRootInit \<noteq> 0"
            by (simp add: stateRootInitNonZero)
        qed


        have "let proof = generateBurnProof contractsLastUpdate' (BURN_id step)
               in fst (callRelease contracts''' tokenDepositAddress (message caller 0) (BURN_id step) token (BURN_amount step) proof) = Success"
        proof (rule BDIFU.releasePossibleAfterBurnAndUpdateBridgeDead)
          show "BURN bridgeAddress caller (BURN_id step) token (BURN_amount step) \<in> set stepsInit"
            using Cons.prems(1)
            by (auto simp add: burnsTo_def)
        next
          show "getReleaseTD contracts''' tokenDepositAddress (BURN_id step) = False"
          proof (rule getReleaseNoReleaseFalse)
            show "reachable contractsInit contracts''' BD.stepsAllBD"
              using BD.Init_BD.reachableInitI by blast
          next
            show "getReleaseTD contractsInit tokenDepositAddress (BURN_id step) = False"
              using releasesEmpty by presburger
          next
            have "length (map RELEASE_fun NRBurnSteps) = length stepListsOther'"  "length (map CANCEL_fun NCDepositSteps) = length stepListsOther"
                using \<open>reachableInterleaved caller contracts' contracts'' (map RELEASE_fun NRBurnSteps) stepListsOther'\<close> 
                      \<open>reachableInterleaved caller contractsBD contracts' CANCEL_WD_steps stepListsOther\<close>
                using CANCEL_WD_steps_def  reachableInterleavedLength
                by blast+
              then have set: "set BD.stepsAllBD = set stepsAllBD \<union> 
                                             set (map RELEASE_fun NRBurnSteps) \<union> set (map CANCEL_fun NCDepositSteps) \<union>
                                             set (concat (stepsOther # stepListsOther @ stepListsOther'))"
              unfolding BD.stepsAllBD_def stepsAllBD_def
                using setInterleaveSteps[of "map RELEASE_fun NRBurnSteps" stepListsOther']
                using setInterleaveSteps[of "map CANCEL_fun NCDepositSteps" stepListsOther]
                by auto

            show "\<nexists>token caller amount proof. RELEASE tokenDepositAddress caller (BURN_id step) token amount proof \<in> set BD.stepsAllBD" (is "?P BD.stepsAllBD")
            proof-
              have "?P stepsAllBD"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                then obtain token' caller' amount' proof' where 
                  *: "RELEASE tokenDepositAddress caller' (BURN_id step) token' amount' proof' \<in> set stepsAllBD"
                  by auto
                then obtain steps1 steps2 where
                  "stepsAllBD = steps2 @ [RELEASE tokenDepositAddress caller' (BURN_id step) token' amount' proof'] @ steps1"
                  by (metis append_Cons append_self_conv2 in_set_conv_decomp)
                then have burn': "BURN bridgeAddress caller' (BURN_id step) token' amount' \<in> set stepsAllBD"
                  using burnBeforeReleaseSteps[of _ caller' "BURN_id step" token' amount' proof']
                  by simp
                have "\<not> isReleasedID tokenDepositAddress token (BURN_id step) stepsAllBD"
                  using Cons.prems(1)
                  by auto
                then have "token \<noteq> token'"
                  using *
                  unfolding isReleasedID_def
                  by auto
                moreover
                have "step = BURN bridgeAddress caller (BURN_id step) token (BURN_amount step) \<and>
                    step \<in> set stepsAllBD"
                  using Cons.prems(1)
                  by (auto simp add: burnsTo_def stepsAllBD_def)
                then have "token = token'"
                  using burn'
                  by (metis BURNNoDoubleCTA Init_BD.reachableInitI)
                ultimately 
                show False
                  by simp
              qed

              moreover

              have "?P CANCEL_WD_steps"
                unfolding CANCEL_WD_steps_def CANCEL_fun_def
                by auto

              moreover

              have "?P (map RELEASE_fun NRBurnSteps)"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                then obtain token' caller' amount' proof' where
                  "RELEASE tokenDepositAddress caller' (BURN_id step) token' amount' proof' \<in> 
                   set (map RELEASE_fun NRBurnSteps)"
                  by blast
                then have "BURN_id step \<in> set (map BURN_id NRBurnSteps)"
                  unfolding RELEASE_fun_def
                  by auto
                then show False
                  using Cons.prems(2)
                  by simp
              qed

              moreover

              have "?P (concat (stepsOther # stepListsOther @ stepListsOther'))"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                then obtain token' caller' amount' proof' where
                  *: "RELEASE tokenDepositAddress caller' (BURN_id step) token' amount' proof' \<in> set (concat (stepsOther # stepListsOther @ stepListsOther'))"
                  by blast
                then have **: "RELEASE tokenDepositAddress caller' (BURN_id step) token' amount' proof' \<in> set BD.stepsAllBD"
                  using set
                  by auto
                have "\<forall> step \<in> set (concat (stepsOther # stepListsOther @ stepListsOther')). \<not> isCaller caller step"       
                  using \<open>reachableInterleaved caller contractsBD contracts' CANCEL_WD_steps stepListsOther\<close>
                  using \<open>reachableInterleaved caller contracts' contracts'' (map RELEASE_fun NRBurnSteps) stepListsOther'\<close> 
                  using \<open>reachableOtherCaller caller contracts'' contracts''' stepsOther\<close>
                  unfolding CANCEL_WD_steps_def
                  using reachableInterleavedOtherCaller reachableOtherCaller_def 
                  by auto
                then have "caller' \<noteq> caller"
                  using *
                  using isCaller.simps(4) 
                  by blast
                moreover
                have "BURN bridgeAddress caller (BURN_id step) token (BURN_amount step) \<in> set BD.stepsAllBD"
                  using Cons.prems
                  unfolding burnsTo_def BD.stepsAllBD_def
                  by auto
                ultimately show False
                  using ** BDIFU.onlyBurnerCanReleaseSteps
                  by blast
              qed

              ultimately
              show ?thesis
                using set
                unfolding CANCEL_WD_steps_def
                by auto
            qed
          qed
        qed (auto simp add: assms)
        then have "fst (executeStep contracts''' block blockNum (RELEASE_fun step)) = Success"
          unfolding RELEASE_fun_def
          by auto
      }
      ultimately
      show "executableSteps caller contracts' (map RELEASE_fun (step # NRBurnSteps))"
        by (auto simp add: executableStep_def)
    qed
  qed

  have pbR: "paidBackAmountFrom tokenDepositAddress token caller RELEASE_steps =
             nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllBD"
    unfolding paidBackAmountFrom_def RELEASE_steps_def RELEASE_fun_def releasedAmountFrom_def releasesFrom_def withdrawnAmountFrom_def withdrawalsFrom_def canceledAmountFrom_def cancelsFrom_def nonReleasedBurnedAmountTo_def NRBurnSteps_def
    by (simp add: comp_def)

  let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
  define amount where "amount = accountBalance contractsLastUpdate' ?mintedToken caller"

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
    define WITHDRAW_WD_step where "WITHDRAW_WD_step = WITHDRAW_WD tokenDepositAddress caller token amount Proof"

    have "\<forall> contracts' stepListsOther. reachableInterleaved caller contractsBD contracts' (RELEASE_steps @ CANCEL_WD_steps) stepListsOther \<longrightarrow> 
          executableSteps caller contracts' [WITHDRAW_WD_step]"
    proof safe
      fix contracts' stepListsOther
      assume r': "reachableInterleaved caller contractsBD contracts' (RELEASE_steps @ CANCEL_WD_steps) stepListsOther"

      have "executableStep caller contracts' WITHDRAW_WD_step"
        unfolding executableStep_def
      proof safe
        fix contracts'' stepsOther and block :: Block and blockNum :: nat
        assume "reachableOtherCaller caller contracts' contracts'' stepsOther"
        have "reachable contractsDead contracts'' (stepsOther @ interleaveSteps (RELEASE_steps @ CANCEL_WD_steps) stepListsOther @ stepsBD)"
          using reachableContractsBD reachableInterleavedReachable[OF r'] \<open>reachableOtherCaller caller contracts' contracts'' stepsOther\<close>
          by (meson reachableOtherCaller_def reachableTrans)
        then interpret BD: BridgeDead where contractsBD=contracts'' and stepsBD="stepsOther @ interleaveSteps (RELEASE_steps @ CANCEL_WD_steps) stepListsOther @ stepsBD"
          by (metis BridgeDead.intro BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms bridgeDead deathStep notBridgeDead' stateRootNonZero)
        interpret BDIFU: BridgeDeadInitFirstUpdate where contractsBD=contracts'' and stepsBD="stepsOther @ interleaveSteps (RELEASE_steps @ CANCEL_WD_steps) stepListsOther @ stepsBD"
          by (smt (verit, best) BD.BridgeDead_axioms BD.Init_BD.Init_axioms BD.stepsAllBD_def BridgeDeadInitFirstUpdate.intro InitFirstUpdate_Dead'.firstUpdate InitFirstUpdate_LastUpdate.InitFirstUpdate_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def append_is_Nil_conv last_appendR stepsBeforeDeath_def)

        let ?msg = "message caller 0"
        have "fst (callWithdrawWhileDead contracts'' tokenDepositAddress ?msg block token amount
            (generateBalanceProof contractsLastUpdate' (mintedTokenB contractsInit bridgeAddress token)
              (sender (message caller 0)) amount)) = Success"
        proof (rule BDIFU.withdrawPossible)
          show "accountBalance contractsLastUpdate' ?mintedToken (sender (message caller 0)) = amount"
            unfolding amount_def
            by simp
        next
          have "getTokenWithdrawnTD contracts'' tokenDepositAddress (hash2 (sender ?msg) token) = 
                getTokenWithdrawnTD contractsBD tokenDepositAddress (hash2 (sender ?msg) token)"
          proof (rule reachableGetTokenWithdrawnNoWithdrawNoChange)
            show "reachable contractsBD contracts'' (stepsOther @ interleaveSteps (RELEASE_steps @ CANCEL_WD_steps) stepListsOther)"
              using r' reachableInterleavedReachable \<open>reachableOtherCaller caller contracts' contracts'' stepsOther\<close>
              by (meson reachableOtherCaller_def reachableTrans)
          next
            show "\<nexists>amount proof. WITHDRAW_WD tokenDepositAddress (sender ?msg) token amount proof \<in> set (stepsOther @ interleaveSteps (RELEASE_steps @ CANCEL_WD_steps) stepListsOther)" (is "?P (set (stepsOther @ interleaveSteps (RELEASE_steps @ CANCEL_WD_steps) stepListsOther))")
            proof-
              have "?P (set (RELEASE_steps @ CANCEL_WD_steps))"
                unfolding RELEASE_steps_def CANCEL_WD_steps_def RELEASE_fun_def CANCEL_fun_def
                by auto
              moreover
              have "?P (set (stepsOther @ (concat stepListsOther)))"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                then obtain amount' proof' where 
                  "WITHDRAW_WD tokenDepositAddress (sender (message caller 0)) token amount' proof' \<in> set (stepsOther @ concat stepListsOther)"
                  by auto
                moreover
                have "\<forall> step \<in> set (stepsOther @ (concat stepListsOther)). \<not> isCaller caller step"
                  using \<open>reachableOtherCaller caller contracts' contracts'' stepsOther\<close> r' 
                  by (metis UnE reachableInterleavedOtherCaller reachableOtherCaller_def set_append)
                ultimately
                show False
                  by fastforce
              qed
              moreover
              have l: "length (RELEASE_steps @ CANCEL_WD_steps) = length stepListsOther"
                using r' reachableInterleavedLength
                by blast
              ultimately
              show ?thesis
                using setInterleaveSteps[OF l]
                by auto
            qed
          qed
          then show "getTokenWithdrawnTD contracts'' tokenDepositAddress (hash2 (sender ?msg) token) = False"
            using True
            by simp
        next
          show "tokenDepositAddress \<noteq> sender ?msg"
            using assms senderMessage by presburger
        qed (auto simp add: assms)
        then show "fst (executeStep contracts'' blockNum block WITHDRAW_WD_step) = Success"
          unfolding WITHDRAW_WD_step_def Proof_def
          by simp
      qed
      then show "executableSteps caller contracts' [WITHDRAW_WD_step]"
        using executableSteps.simps(1) executableSteps.simps(2) reachableInterleaved.cases
        by blast
    qed

    have pbW: "paidBackAmountFrom tokenDepositAddress token caller [WITHDRAW_WD_step] = accountBalance contractsLastUpdate' ?mintedToken caller"
      unfolding paidBackAmountFrom_def WITHDRAW_WD_step_def releasedAmountFrom_def releasesFrom_def withdrawnAmountFrom_def withdrawalsFrom_def canceledAmountFrom_def cancelsFrom_def
      unfolding amount_def
      by simp

    let ?steps = "WITHDRAW_WD_step # RELEASE_steps @ CANCEL_WD_steps"
    show ?thesis
    proof (rule_tac x="?steps" in exI, safe)
      fix step
      assume "step \<in> set ?steps"
      then show "isCaller caller step"
        unfolding WITHDRAW_WD_step_def RELEASE_steps_def RELEASE_fun_def CANCEL_WD_steps_def CANCEL_fun_def
        by auto
    next
      show "executableSteps caller contractsBD ?steps"
        using \<open>executableSteps caller contractsBD CANCEL_WD_steps\<close>
        using \<open>\<forall>contracts' stepListsOther. reachableInterleaved caller contractsBD contracts' CANCEL_WD_steps stepListsOther \<longrightarrow> executableSteps caller contracts' RELEASE_steps\<close>
        using \<open>\<forall>contracts' stepListsOther. reachableInterleaved caller contractsBD contracts' (RELEASE_steps @ CANCEL_WD_steps) stepListsOther \<longrightarrow> executableSteps caller contracts' [WITHDRAW_WD_step]\<close> 
        by (metis append.left_neutral append_Cons executableStepsAppend)
    next
      fix contracts' stepListsOther
      assume r': "reachableInterleaved caller contractsBD contracts' ?steps stepListsOther"
      have "reachable contractsDead contracts' (interleaveSteps ?steps stepListsOther @ stepsBD)"
        using r' reachableInterleavedReachable reachableContractsBD reachableTrans by blast
      then interpret BD: BridgeDead where contractsBD=contracts' and stepsBD="interleaveSteps ?steps stepListsOther @ stepsBD"
        by (metis BridgeDead.intro BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms bridgeDead deathStep notBridgeDead' stateRootNonZero)
      interpret BDIFU: BridgeDeadInitFirstUpdate where contractsBD=contracts' and stepsBD="interleaveSteps ?steps stepListsOther @ stepsBD"
        by (smt (z3) BD.BridgeDead_axioms BD.InitUpdateBridgeNotDeadLastValidState_BD.Init_LVS.Init_axioms BD.InitUpdateBridgeNotDeadLastValidState_BD.stepsAllLVS_def BD.stepsAllBD_def BridgeDeadInitFirstUpdate.intro InitFirstUpdate.axioms(2) InitFirstUpdate.intro InitFirstUpdate_Dead'.firstUpdate InitFirstUpdate_axioms InitFirstUpdate_axioms_def Nil_is_append_conv append_eq_appendI last_append stepsBeforeDeath_def)

      have other: "\<forall> step \<in> set (concat stepListsOther). \<not> isCaller caller step" "length stepListsOther = length ?steps"
        using r' reachableInterleavedOtherCaller reachableInterleavedLength
        by metis+

      let ?stepsAll = "interleaveSteps ?steps stepListsOther @ stepsAllBD"
      show "allTokensPaidBackEq tokenDepositAddress bridgeAddress token caller
            ?stepsAll stepsInit"
      proof-
        have "?stepsAll = BD.stepsAllBD"
          by (simp add: BD.stepsAllBD_def stepsAllBD_def)
        moreover
        have "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsLastUpdate' contracts' = 0"
          using executeStepNonWithdrawnBalanceBeforeAfter[where msg="message caller 0"]
          by (smt (verit, best) WITHDRAW_WD_step_def executeStep.simps(8) list.inject list.simps(3) r' reachableInterleaved.simps senderMessage)
        moreover
        have "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit  BD.stepsAllBD = 0"
        proof-
          have "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit
               (?steps @ stepsAllBD) = []"
            using allCanceled unfolding WITHDRAW_WD_step_def
            by simp
          then have "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit
                     (interleaveSteps ?steps stepListsOther @ stepsAllBD) = []"
            using nonClaimedBeforeNonCanceledDepositsToInterleaveOther[where token=token and caller=caller and steps="?steps" and stepssOther=stepListsOther and stepsInit=stepsInit and stepsBefore="stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step]"] other BD.Init_BD.reachableInitI
            unfolding stepsAllBD_def BD.stepsAllBD_def
            by auto
          then show ?thesis
            unfolding BD.stepsAllBD_def stepsAllBD_def
            by (auto simp add: nonClaimedBeforeNonCanceledDepositsAmountTo_def)
        qed
        moreover
        have "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit BD.stepsAllBD = 0"
        proof-
          have "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
                (?steps @ stepsAllBD) = []"
            using allReleased
            unfolding WITHDRAW_WD_step_def stepsAllBD_def
            by simp
          moreover
          have "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
                  ?stepsAll = 
                nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
                  (?steps @ stepsAllBD)"
            using BDIFU.nonReleasedBurnsToInterleaveOther[of ?steps stepListsOther "stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit] other
            using BD.Init_BD.reachableInitI
            unfolding BD.stepsAllBD_def stepsAllBD_def
            by fastforce
          ultimately
          show ?thesis
            unfolding nonReleasedBurnedAmountTo_def BD.stepsAllBD_def stepsAllBD_def
            by simp
        qed
        moreover
        have "accountBalance contractsInit (mintedTokenTD contractsInit tokenDepositAddress token) caller = 0"
          by (metis assms(1) assms(2) finiteBalances_def mintedTokenITDB properTokenFiniteBalancesMinted totalBalanceZero)
        moreover
        have "depositedAmountTo tokenDepositAddress token caller BD.stepsAllBD =
              depositedAmountTo tokenDepositAddress token caller stepsAllBD"
        proof-
          have "depositedAmountTo tokenDepositAddress token caller [WITHDRAW_WD_step] = 0"
            unfolding WITHDRAW_WD_step_def
            by simp
          then show ?thesis
            using depositedAmountToInterleaveStepsOther[of stepListsOther caller ?steps tokenDepositAddress token] other
            using noDeposits
            by (metis BD.stepsAllBD_def depositedAmountTo_def append_Cons append_Nil append_assoc depositedAmountToAppend depositedAmountToNil stepsAllBD_def)
        qed
        ultimately
        show ?thesis
          using BDIFU.userTokensInvariant[OF assms(1), of caller] 
          using pbC pbR assms(4-5)
          unfolding allTokensPaidBackEq_def
          by (simp add: paidBackAmountFrom_def)
      qed
    qed
  next
    case False
    let ?steps = "RELEASE_steps @ CANCEL_WD_steps"
    show ?thesis
    proof (rule_tac x="?steps" in exI, safe)
      fix step
      assume "step \<in> set ?steps"
      then show "isCaller caller step"
        unfolding RELEASE_steps_def RELEASE_fun_def CANCEL_WD_steps_def CANCEL_fun_def
        by auto
    next
      show "executableSteps caller contractsBD ?steps"
        using \<open>\<forall>contracts' stepListsOther. reachableInterleaved caller contractsBD contracts' CANCEL_WD_steps stepListsOther \<longrightarrow> executableSteps caller contracts' RELEASE_steps\<close> \<open>executableSteps caller contractsBD CANCEL_WD_steps\<close> executableStepsAppend 
        by blast
    next
      fix contracts' stepListsOther
      assume r': "reachableInterleaved caller contractsBD contracts' ?steps stepListsOther"
      have "reachable contractsDead contracts' (interleaveSteps ?steps stepListsOther @ stepsBD)"
        using r' reachableInterleavedReachable reachableContractsBD reachableTrans by blast
      then interpret BD: BridgeDead where contractsBD=contracts' and stepsBD="interleaveSteps ?steps stepListsOther @ stepsBD"
        by (metis BridgeDead.intro BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms bridgeDead deathStep notBridgeDead' stateRootNonZero)
      interpret BDIFU: BridgeDeadInitFirstUpdate where contractsBD=contracts' and stepsBD="interleaveSteps ?steps stepListsOther @ stepsBD"
        by (smt (z3) BD.BridgeDead_axioms BD.InitUpdateBridgeNotDeadLastValidState_BD.Init_LVS.Init_axioms BD.InitUpdateBridgeNotDeadLastValidState_BD.stepsAllLVS_def BD.stepsAllBD_def BridgeDeadInitFirstUpdate.intro InitFirstUpdate.axioms(2) InitFirstUpdate.intro InitFirstUpdate_Dead'.firstUpdate InitFirstUpdate_axioms InitFirstUpdate_axioms_def Nil_is_append_conv append_eq_appendI last_append stepsBeforeDeath_def)

      have other: "\<forall> step \<in> set (concat stepListsOther). \<not> isCaller caller step" "length stepListsOther = length ?steps"
        using r' reachableInterleavedOtherCaller reachableInterleavedLength
        by metis+

      let ?stepsAll = "interleaveSteps ?steps stepListsOther @ stepsAllBD"
      show "allTokensPaidBackEq tokenDepositAddress bridgeAddress token caller
            ?stepsAll stepsInit"
      proof-
        have "?stepsAll = BD.stepsAllBD"
          by (simp add: BD.stepsAllBD_def stepsAllBD_def)
        moreover
        have "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsLastUpdate' contracts' = 0"
          using False reachableGetTokenWithdrawn reachableInterleavedReachable[OF r']
          unfolding amount_def nonWithdrawnBalanceBefore_def
          by (metis  bot_nat_0.not_eq_extremum mintedTokenBI)
        moreover
        have "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit BD.stepsAllBD = 0"
        proof-
          have "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit
               (?steps @ stepsAllBD) = []"
            using allCanceled
            by simp
          then have "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit
                     (interleaveSteps ?steps stepListsOther @ stepsAllBD) = []"
            using nonClaimedBeforeNonCanceledDepositsToInterleaveOther[where token=token and caller=caller and steps="?steps" and stepssOther=stepListsOther and stepsInit=stepsInit and stepsBefore="stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step]"] other BD.Init_BD.reachableInitI
            unfolding stepsAllBD_def BD.stepsAllBD_def
            by auto
          then show ?thesis
            unfolding BD.stepsAllBD_def stepsAllBD_def
            by (auto simp add: nonClaimedBeforeNonCanceledDepositsAmountTo_def)
        qed
        moreover
        have "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit BD.stepsAllBD = 0"
        proof-
          have "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
                (?steps @ stepsAllBD) = []"
            using allReleased
            unfolding stepsAllBD_def
            by simp
          moreover
          have "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
                (interleaveSteps ?steps stepListsOther @ stepsAllBD) = nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
                (?steps @ stepsAllBD)"
            using BDIFU.nonReleasedBurnsToInterleaveOther[of ?steps stepListsOther "stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit] other
            using BD.Init_BD.reachableInitI
            unfolding BD.stepsAllBD_def stepsAllBD_def
            by fastforce
          ultimately
          show ?thesis
            unfolding nonReleasedBurnedAmountTo_def BD.stepsAllBD_def stepsAllBD_def
            by simp
        qed
        moreover
        have "accountBalance contractsInit (mintedTokenTD contractsInit tokenDepositAddress token) caller = 0"
          by (metis assms(1) assms(2) finiteBalances_def mintedTokenITDB properTokenFiniteBalancesMinted totalBalanceZero)
        moreover
        have "depositedAmountTo tokenDepositAddress token caller BD.stepsAllBD =
              depositedAmountTo tokenDepositAddress token caller stepsAllBD"
          using depositedAmountToInterleaveStepsOther other noDeposits
          by (metis BD.stepsAllBD_def depositedAmountToAppend depositedAmountTo_def append_assoc stepsAllBD_def)
        ultimately
        show ?thesis
          using noDeposits
          using BDIFU.userTokensInvariant[OF assms(1), of caller] 
          using pbC pbR assms(4-5)
          unfolding allTokensPaidBackEq_def
          by (simp add: paidBackAmountFrom_def)
      qed
    qed
  qed
qed

end

end