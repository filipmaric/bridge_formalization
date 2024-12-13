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
  shows "accountBalance (setBridgeState contracts' address state') mintedToken (sender msg) =
         accountBalance contracts mintedToken (sender msg) + amount"
  using assms callMintBalanceOf callOriginalToMinted
  unfolding claim_def
  by (auto simp add: Let_def split: if_split_asm prod.splits option.splits)

lemma callClaimBalanceOfMinted:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "mintedToken = mintedTokenB contracts address token"
  shows "accountBalance contracts' mintedToken (sender msg) =
         accountBalance contracts mintedToken (sender msg) + amount"
  using assms claimBalanceOfMinted
  unfolding callClaim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimOtherToken:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "mintedToken = mintedTokenB contracts address token"
  assumes "mintedToken \<noteq> token'"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms 
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
     (metis callMintITokenPairs callMintOtherToken callOriginalToMinted)
 (* FIXME: avoid proof after auto *)

lemma callClaimTotalBalance:
  assumes "finiteBalances contracts mintedToken"
  assumes "callClaim contracts bridgeAddress msg ID token amount proof' = (Success, contracts')"
  assumes "mintedTokenB contracts bridgeAddress token = mintedToken"
  shows "totalTokenBalance contracts' mintedToken =
         totalTokenBalance contracts mintedToken + amount"
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
    unfolding  Let_def stateBridge_def
    by simp
  then show ?thesis
    using assms callMint_total_balance
    unfolding callClaim_def claim_def stateBridge_def finiteBalances_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
qed

lemma finiteBalancesSetBridgeState:
  assumes "finiteBalances contracts token'"
  shows "finiteBalances (setBridgeState contracts address state) token'"
  using assms
  by (simp add: finiteBalances_def)

lemma callClaimFiniteBalances [simp]:
  assumes "finiteBalances contracts token'"
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "finiteBalances contracts' token'"
  using assms
  unfolding callClaim_def claim_def
  apply (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
  using callMintFiniteBalances finiteBalancesSetBridgeState by blast
  (* FIXME: avoid methods after auto *)

lemma callClaimCallLastState:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "callLastState contracts (stateOracleAddressB contracts address) =
         (Success, lastStateB contracts address)"
  using assms callLastState
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def simp del: callLastState split: option.splits prod.splits if_split_asm)


lemma callClaimCallVerifyProof:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "callVerifyDepositProof contracts 
           (proofVerifierAddressB contracts address) 
           (depositAddressB contracts address)
           ID
           (hash3 (sender msg) token amount) 
           (lastStateB contracts address) 
           proof = Success"
  using assms callLastState
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def simp del: callLastState split: option.splits prod.splits if_split_asm)

lemma callClaimVerifyProof:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "verifyDepositProof () 
         (depositAddressB contracts address)
         ID
         (hash3 (sender msg) token amount)
         (lastStateB contracts address)
         proof"
  using callClaimCallVerifyProof[OF assms]
  unfolding callVerifyDepositProof_def
  by (simp split: option.splits prod.splits if_split_asm)

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
  shows "depositAddressB contracts' address =
         depositAddressB contracts address"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimTokenPairs [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "tokenPairsAddressB contracts' address = 
         tokenPairsAddressB contracts address"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimStateOracle [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "stateOracleAddressB contracts' address = 
         stateOracleAddressB contracts address"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimProofVerifier [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "proofVerifierAddressB contracts' address =
         proofVerifierAddressB contracts address"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimDeadState [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "deadStateTD contracts' tokenDepositAddress = 
         deadStateTD contracts tokenDepositAddress"
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
  shows "lastValidStateTD contracts' tokenDepositAddress = 
         lastValidStateTD contracts tokenDepositAddress"
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


subsection \<open>callTransfer\<close>
  
lemma callTransferSafeTransferFrom:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  shows "callSafeTransferFrom contracts (mintedTokenB contracts address token) caller receiver amount = (Success, contracts')"
    using assms callOriginalToMinted
    unfolding callTransfer_def transfer_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callTransferBalanceOfReceiver:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  assumes "mintedToken = mintedTokenB contracts address token"
  shows "accountBalance contracts' mintedToken receiver =
         accountBalance contracts mintedToken receiver + amount"
proof-
  have "callSafeTransferFrom contracts mintedToken caller receiver amount = (Success, contracts')"
    using assms(1) assms(2) callTransferSafeTransferFrom by blast
  then show ?thesis
    by (smt (verit, ccfv_threshold) callBalanceOf_def callSafeTransferFromBalanceOfTo callSafeTransferFromERC20state(1) callSafeTransferFromERC20state(2) option.case_eq_if)
qed

lemma callTransferBalanceOfCaller:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  assumes "mintedToken = mintedTokenB contracts address token"
  shows "amount \<le> accountBalance contracts mintedToken caller"
        "accountBalance contracts' mintedToken caller =
         accountBalance contracts mintedToken caller - amount"
proof-
  have "callSafeTransferFrom contracts mintedToken caller receiver amount = (Success, contracts')"
    using assms(1) assms(2) callTransferSafeTransferFrom by blast
  then show "amount \<le> accountBalance contracts mintedToken caller"
            "accountBalance contracts' mintedToken caller =
             accountBalance contracts mintedToken caller - amount"
    using safeTransferFromBalanceOfCaller[of _ _ caller receiver amount]
    unfolding callSafeTransferFrom_def
    by (auto  split: option.splits prod.splits if_split_asm)
qed

lemma callTransferBalanceOfOther:
  assumes "other \<noteq> caller" "other \<noteq> receiver"
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  assumes "mintedToken = mintedTokenB contracts address token"
  shows "accountBalance contracts' mintedToken other =
         accountBalance contracts mintedToken other"
proof-
  have "callSafeTransferFrom contracts mintedToken caller receiver amount = (Success, contracts')"
    using assms callTransferSafeTransferFrom by blast
  then show ?thesis
    using callSafeTransferFromBalanceOfOther[OF assms(1-2)]
    by simp
qed

lemma callTransferTotalBalance:
  assumes "finiteBalances contracts mintedToken"
  assumes "callTransfer contracts bridgeAddress caller receiver token amount = (Success, contracts')"
  assumes "mintedTokenB contracts bridgeAddress token = mintedToken"
  shows "totalTokenBalance contracts' token' =
         totalTokenBalance contracts token'"
proof-
  have *: "callSafeTransferFrom contracts mintedToken caller receiver amount = (Success, contracts')"
    using assms callTransferSafeTransferFrom by blast

  have "caller \<noteq> receiver"
    using assms
    unfolding callTransfer_def transfer_def
    by (simp split: option.splits prod.splits if_split_asm)

  have **: "amount \<le> balanceOf (the (ERC20state contracts mintedToken)) caller"
    using callTransferBalanceOfCaller(1) assms by blast

  show ?thesis
  proof (cases "token' = mintedTokenB contracts bridgeAddress token")
    case True
    then show ?thesis
      using assms(3) *
      using totalBalance_safeTransferFrom[OF \<open>caller \<noteq> receiver\<close> _ **] assms
      unfolding callSafeTransferFrom_def finiteBalances_def
      by (auto split: option.splits prod.splits if_split_asm)
  next
    case False
    then show ?thesis
      using * assms(3)
      unfolding callSafeTransferFrom_def
      by (auto split: option.splits prod.splits if_split_asm)
  qed
qed

lemma callTransferOtherToken:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  assumes "mintedToken = mintedTokenB contracts address token"
  assumes "mintedToken \<noteq> token'"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
proof-
  have "callSafeTransferFrom contracts mintedToken caller receiver amount = (Success, contracts')"
    using assms(1) assms(2) callTransferSafeTransferFrom by blast
  then show ?thesis
    by (metis assms(3) callSafeTransferFromOtherToken)
qed

lemma callTransferITokenPairs [simp]:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
  unfolding callTransfer_def transfer_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callTransferITokenDeposit [simp]:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  shows "ITokenDeposit contracts' = ITokenDeposit contracts"
  using assms
  unfolding callTransfer_def transfer_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callTransferIProofVerifier [simp]:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
  unfolding callTransfer_def transfer_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callTransferIStateOracle [simp]:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  shows "IStateOracle contracts' = IStateOracle contracts"
  using assms
  unfolding callTransfer_def transfer_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callTransferIBridge [simp]:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  shows "IBridge contracts' = IBridge contracts"
  using assms
  unfolding callTransfer_def transfer_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callTransferERC20state:
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  assumes "ERC20state contracts token' \<noteq> None"
  shows "ERC20state contracts' token' \<noteq> None"
proof-
  have *: "callSafeTransferFrom contracts (mintedTokenB contracts address token) caller receiver amount = (Success, contracts')"
    using assms(1) assms(2) callTransferSafeTransferFrom by blast
   show ?thesis
     using assms(2) callSafeTransferFromERC20state(2)[OF *] callSafeTransferFromOtherToken[OF _ *]
     by metis
 qed

lemma callTransferFiniteBalances:
  assumes "finiteBalances contracts token'"
  assumes "callTransfer contracts address caller receiver token amount = (Success, contracts')"
  shows "finiteBalances contracts' token'"
  using assms
  by (metis callSafeTransferFromFiniteBalances callSafeTransferFromOtherToken callTransferSafeTransferFrom finiteBalances_def)

end

end