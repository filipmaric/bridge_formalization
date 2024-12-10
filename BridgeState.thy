theory BridgeState
  imports Main Definition ERC20State TokenPairsState StateOracleState ProofVerifierState
begin

context HashProofVerifier
begin

section \<open>Bridge\<close>

subsection \<open>Claim\<close>

lemma claimFail:
  assumes "claim contracts msg state ID token amount proof = (Fail str, state', contracts')"
  shows "state' = state" and "contracts' = contracts"
  using assms
  unfolding claim_def
  by (auto simp add: Let_def split: if_split_asm prod.splits)

lemma callClaimFail:
  assumes "callClaim contracts address msg ID token amount proof = (Fail str, contracts')"
  shows "contracts' = contracts"
  using assms claimFail
  unfolding callClaim_def
  by (simp split: option.splits prod.splits if_split_asm)

lemma claimWritesClaim:
  assumes "claim contracts msg state ID token amount proof = (Success, state', contracts')" 
  shows "getClaim state' ID = True"
  using assms
  unfolding claim_def lookupBool_def
  by (auto simp add: Let_def Mapping.lookup_default_update split: prod.splits if_split_asm)

lemma callClaimWritesClaim:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "getClaim (the (bridgeState contracts' address)) ID = True"
  using assms claimWritesClaim
  unfolding callClaim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

text \<open>There can be no double claim\<close>
(* TODO: this is just an illustration - the lemma should be generalized to non-consecutive states *)
lemma callClaimNoDouble:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "fst (callClaim contracts' address msg' ID token' amount' proof') \<noteq> Success"
proof-
  have "getClaim (the (bridgeState contracts' address)) ID = True"
    using assms
    by (simp add: callClaimWritesClaim)
  then show ?thesis
    unfolding callClaim_def claim_def
    by (auto simp add: Let_def split: prod.splits option.splits)
qed

lemma claimBalanceOfMinted:
  assumes "claim contracts msg state ID token amount proof = (Success, state', contracts')"
  assumes "stateTokenPairs = the (tokenPairsState contracts (tokenPairs state))"
  assumes "mintedToken = getMinted stateTokenPairs token"
  shows "balanceOf (the (ERC20state (setBridgeState contracts' address state') mintedToken)) (sender msg) = 
         balanceOf (the (ERC20state contracts mintedToken)) (sender msg) + amount"
  using assms callMintBalanceOf callOriginalToMinted
  unfolding claim_def
  by (auto simp add: Let_def split: if_split_asm prod.splits option.splits)

lemma callClaimBalanceOfMinted:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "mintedToken = bridgeMintedToken contracts address token"
  shows "balanceOf (the (ERC20state contracts' mintedToken)) (sender msg) = 
         balanceOf (the (ERC20state contracts mintedToken)) (sender msg) + amount"
  using assms claimBalanceOfMinted
  unfolding callClaim_def bridgeMintedToken_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimOtherToken:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "mintedToken = bridgeMintedToken contracts address token"
  assumes "mintedToken \<noteq> token'"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
     (metis bridgeMintedToken_def callMintIBridge callMintOtherToken callOriginalToMinted option.sel)
 (* FIXME: avoid proof after auto *)

lemma callClaimTotalBalance:
  assumes "finite (Mapping.keys (balances ((the (ERC20state contracts mintedToken)))))"
  assumes "callClaim contracts bridgeAddress msg ID token amount proof' = (Success, contracts')"
  assumes "bridgeMintedToken contracts bridgeAddress token = mintedToken"
  shows "totalBalance (the (ERC20state contracts' mintedToken)) =
         totalBalance (the (ERC20state contracts mintedToken)) + amount"
proof-
  define stateBridge where "stateBridge = the (bridgeState contracts bridgeAddress)"

  have "callOriginalToMinted contracts (BridgeState.tokenPairs stateBridge) token = 
        (Success, getMinted (the (tokenPairsState contracts (BridgeState.tokenPairs stateBridge))) token)" 
    using assms callOriginalToMinted[of contracts "BridgeState.tokenPairs stateBridge" token]
    unfolding callClaim_def claim_def stateBridge_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
  then have "callOriginalToMinted contracts (BridgeState.tokenPairs stateBridge) token = 
             (Success, mintedToken)"
    using assms
    unfolding bridgeMintedToken_def Let_def stateBridge_def
    by simp
  then show ?thesis
    using assms
    unfolding callClaim_def claim_def stateBridge_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
qed


lemma callClaimCallLastState:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "let state = the (bridgeState contracts address);
             lastState = getLastStateB contracts address
          in callLastState contracts (BridgeState.stateOracle state) = (Success, lastState)"
  using assms callLastState
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def simp del: callLastState split: option.splits prod.splits if_split_asm)

lemma callClaimCallVerifyProof:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "let state = the (bridgeState contracts address);
             lastState = getLastStateB contracts address
          in callVerifyDepositProof contracts (BridgeState.proofVerifier state) (BridgeState.deposit state)
                             ID (hash3 (sender msg) token amount) lastState proof = Success"
  using assms callLastState
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def simp del: callLastState split: option.splits prod.splits if_split_asm)

lemma callClaimITokenPairs [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimITokenDeposit [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "ITokenDeposit contracts' = ITokenDeposit contracts"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimIProofVerifier [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimIStateOracle [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "IStateOracle contracts = IStateOracle contracts'"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimDeposit [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "BridgeState.deposit (the (bridgeState contracts' address)) =
         BridgeState.deposit (the (bridgeState contracts address))"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimTokenPairs [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "BridgeState.tokenPairs (the (bridgeState contracts' address)) =
         BridgeState.tokenPairs (the (bridgeState contracts address))"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimStateOracle [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "BridgeState.stateOracle (the (bridgeState contracts' address)) =
         BridgeState.stateOracle (the (bridgeState contracts address))"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimProofVerifier [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "BridgeState.proofVerifier (the (bridgeState contracts' address)) =
         BridgeState.proofVerifier (the (bridgeState contracts address))"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimDeadState [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 
         deadState (the (tokenDepositState contracts tokenDepositAddress))"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimBridgeState:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "bridgeState contracts address \<noteq> None" and "bridgeState contracts' address \<noteq> None"
  using assms
  unfolding callClaim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

text \<open>The flag that records that money has been claimed cannot be unset\<close>
lemma callClaimPreservesTrueClaim [simp]:
  assumes
    "callClaim contracts address msg ID token amount proof = (Success, contracts')"
    "getClaim (the (bridgeState contracts address)) ID' = True"
  shows
    "getClaim (the (bridgeState contracts' address)) ID' = True"
proof (cases "ID = ID'")
  case True
  then have False
    using assms
    unfolding callClaim_def claim_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
    using assms Mapping.lookup_default_update'[of False ID True]
    unfolding callClaim_def claim_def lookupBool_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
qed

lemma callClaimERC20state:
  assumes "callClaim contracts address msg ID token amount proof  = (Success, contracts')"
  assumes "ERC20state contracts token' \<noteq> None"
  shows "ERC20state contracts' token' \<noteq> None"
  using assms callMintERC20state callMintOtherToken
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def simp del: callMintOtherToken split: option.splits prod.splits if_split_asm) metis (* FIXME *)

lemma callClaimOtherAddress [simp]: 
  assumes "address' \<noteq> address"
          "callClaim contracts address msg ID token amount proof = (status, contracts')"
  shows "bridgeState contracts' address' = bridgeState contracts address'"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma callClaimGetLastValidStateTD [simp]:
  assumes "callClaim contracts bridgeAddress msg ID token amount proof = (Success, contracts')"
  shows "getLastValidStateTD contracts' tokenDepositAddress = 
         getLastValidStateTD contracts tokenDepositAddress"
  using assms
  using callClaimIStateOracle callClaimITokenDeposit callLastState_def lastValidState_def by presburger

lemma callClaimGetClaimOther:
  assumes "callClaim contracts address msg ID' token amount proof = (Success, contracts')"
  assumes "address \<noteq> bridgeAddress \<or> ID' \<noteq> ID"
  shows "getClaim (the (bridgeState contracts' bridgeAddress)) ID = 
         getClaim (the (bridgeState contracts bridgeAddress)) ID"
  using assms
  unfolding callClaim_def claim_def
  by (cases "address = bridgeAddress")
     (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
 
text \<open>Sufficient conditions for a claim\<close>
lemma callClaimI:
  assumes "bridgeState contracts address = Some stateBridge"
  assumes "tokenPairsState contracts (BridgeState.tokenPairs stateBridge) = Some stateTokenPairs"
  assumes "stateOracleState contracts (BridgeState.stateOracle stateBridge) = Some stateStateOracle"
  assumes "proofVerifierState contracts (BridgeState.proofVerifier stateBridge) \<noteq> None"
  assumes "ERC20state contracts (getMinted stateTokenPairs token) \<noteq> None" 
  assumes "getMinted stateTokenPairs token \<noteq> 0"
  \<comment> \<open>Proof must be verified\<close>
  assumes "verifyDepositProof () (BridgeState.deposit stateBridge) ID (hash3 (sender msg) token amount) (StateOracleState.lastState stateStateOracle) proof"
  \<comment> \<open>There must not be a prior claim\<close>
  assumes "getClaim stateBridge ID = False"
  shows "fst (callClaim contracts address msg ID token amount proof) = Success"
proof-
  have "callLastState contracts (BridgeState.stateOracle stateBridge) = (Success, StateOracleState.lastState stateStateOracle)"
    using assms callLastStateI callLastState
    by (simp add: callLastState_def)
  moreover
  have "fst (callMint contracts (getMinted stateTokenPairs token) (sender msg) amount) = Success"
    using assms callMintI 
    by blast
  moreover
  have "callVerifyDepositProof contracts (BridgeState.proofVerifier stateBridge)
         (BridgeState.deposit stateBridge) ID (hash3 (sender msg) token amount) (StateOracleState.lastState stateStateOracle) proof =
          Success"
    using assms callVerifyDepositProofI
    by auto
  moreover
  have "callOriginalToMinted contracts (BridgeState.tokenPairs stateBridge) token = (Success, getMinted stateTokenPairs token)"
    using assms callOriginalToMintedI callOriginalToMinted
    by (simp add: callOriginalToMinted_def)
      ultimately show ?thesis
    using assms 
    unfolding callClaim_def claim_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm) (*FIXME*)
qed

subsection \<open>callVerifyClaimProof\<close>

lemma callVerifyClaimProofI:
  assumes "proofVerifierState contracts proofVerifierAddress \<noteq> None"
  assumes "verifyClaimProof () bridgeAddress ID stateRoot proof"
  shows "callVerifyClaimProof contracts proofVerifierAddress bridgeAddress ID stateRoot proof = Success"
  using assms
  unfolding callVerifyClaimProof_def
  by (auto split: option.splits prod.splits)


end

end