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
        have "amount \<le> nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
            unfolding nonClaimedBeforeDeathNonCanceledTokenDepositsAmount_def
        proof (rule member_le_sum_list)
          have "DEPOSIT tokenDepositAddress caller ID token amount \<in> set (nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsInit stepsAllBD)"
            using assms
            by (simp add: nonClaimedBeforeDeathNonCanceledTokenDeposits_def tokenDeposits_def)
          then show "amount \<in> set (map DEPOSIT_amount (nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsInit stepsAllBD))"
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
      have "amount \<le> nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
      proof-
        let ?N = "nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
        have "balanceOf ?N (sender msg) = amount"
        proof-
          have "balanceOf (tokenClaimsTransfersBurnsBalances bridgeAddress token stepsInit) (sender msg) = amount"
          proof (subst tokenClaimsTransfersBurnsBalanceAccountBalance)
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
            using nonWithdrawnTokenClaimsTransfersBurnsBalanceNoWithdraw
            by blast
        qed
        moreover 
        have "finite (Mapping.keys (balances ?N))"
          by simp
        ultimately
        show ?thesis
          unfolding nonWithdrawnNonBurnedClaimedBeforeDeathAmount_def
          by (meson order_refl totalBalance_removeFromBalance(1))
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
end