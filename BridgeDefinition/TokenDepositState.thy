theory TokenDepositState
  imports Main Definition More_Mapping ERC20State TokenPairsState StateOracleState BridgeState
begin

section \<open>TokenDeposit\<close>

subsection \<open>lastValidState\<close>

lemma lastValidStateI:
  assumes "stateOracleState contracts (stateOracleAddressTD contracts address) \<noteq> None"
  shows "fst (lastValidStateTD contracts address) = Success"
  using assms callLastStateI
  unfolding lastValidState_def Let_def
  by auto

subsection \<open>getDeadStatus\<close>

lemma getDeadStatusDeposits [simp]:
  assumes "getDeadStatus contracts state block = (status, dead, state')"
  shows "TokenDepositState.deposits state' = TokenDepositState.deposits state"
  using assms
  unfolding getDeadStatus_def Let_def
  by (auto split: if_split_asm prod.splits)

lemma getDeadStatusTokenPairs [simp]:
  assumes "getDeadStatus contracts state block = (status, dead, state')"
  shows "TokenDepositState.tokenPairs state' = TokenDepositState.tokenPairs state"
  using assms
  unfolding getDeadStatus_def Let_def
  by (auto split: if_split_asm prod.splits)

lemma getDeadStatusStateOracle [simp]:
  assumes "getDeadStatus contracts state block = (status, dead, state')"
  shows "TokenDepositState.stateOracle state' = TokenDepositState.stateOracle state"
  using assms
  unfolding getDeadStatus_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma getDeadStatusBridge [simp]:
  assumes "getDeadStatus contracts state block = (status, ret, state')"
  shows "TokenDepositState.bridge state' = TokenDepositState.bridge state"
  using assms
  unfolding getDeadStatus_def
  by (auto split: if_split_asm prod.splits)

lemma getDeadStatusProofVerifier [simp]:
  assumes "getDeadStatus contracts state block = (status, ret, state')"
  shows "TokenDepositState.proofVerifier state' = TokenDepositState.proofVerifier state"
  using assms
  unfolding getDeadStatus_def
  by (auto split: if_split_asm prod.splits)

lemma getDeadStatusReleases [simp]:
  assumes "getDeadStatus contracts state block = (status, ret, state')"
  shows "TokenDepositState.releases state' = TokenDepositState.releases state"
  using assms
  unfolding getDeadStatus_def
  by (auto split: if_split_asm prod.splits)

lemma getDeadStatusTokenWithdrawn [simp]:
  assumes "getDeadStatus contracts state block = (status, dead, state')"
  shows "TokenDepositState.tokenWithdrawn state' = TokenDepositState.tokenWithdrawn state"
  using assms
  unfolding getDeadStatus_def
  by (auto split: if_split_asm prod.splits)

lemma getDeadStatusLastValidState [simp]:
  assumes "getDeadStatus contracts state block = (Success, ret, state')"
  shows "lastValidState contracts state' = lastValidState contracts state"
  using assms
  unfolding getDeadStatus_def lastValidState_def
  by (auto split: if_split_asm prod.splits)

lemma getDeadStatusFalse:
  assumes "getDeadStatus contracts state block = (Success, False, state')"
  shows "deadState state = 0"
  using assms
  unfolding getDeadStatus_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma getDeadStatusFalse':
  assumes "getDeadStatus contracts state block = (Success, False, state')"
  shows "deadState state' = 0"
  using assms
  unfolding getDeadStatus_def
  by (auto split: if_split_asm option.splits prod.splits)

lemma getDeadStatusSetsDeadState:
  assumes "getDeadStatus contracts state block = (Success, True, state')"
  assumes "deadState state = 0"
  shows "deadState state' = lastStateSO contracts (TokenDepositState.stateOracle state)"
  using assms
  unfolding getDeadStatus_def callLastState_def
  by (auto split: option.splits prod.splits if_split_asm)

lemma getDeadStatusTrueDeadState:
  assumes "getDeadStatus contracts state block = (Success, True, state')"
  shows "deadState state' \<noteq> 0"
  using assms
  unfolding getDeadStatus_def callLastState_def
  by (auto split: if_split_asm option.splits prod.splits)

lemma getDeadStatusInDeadState [simp]:
  assumes "getDeadStatus contracts state block = (status, result, state')"
  assumes "deadState state \<noteq> 0"
  shows "deadState state' = deadState state"
  using assms
  unfolding getDeadStatus_def callLastState_def
  by (auto split: if_split_asm option.splits prod.splits)

lemma getDeadStatusI:
  assumes "stateOracleState contracts (stateOracleAddressTD contracts address) \<noteq> None"
  shows "fst (getDeadStatus contracts (the (tokenDepositState contracts address)) block) = Success"
  using assms callLastStateI[OF assms(1)]  callLastUpdateTimeI[OF assms(1)]
  unfolding getDeadStatus_def 
  by (auto split: option.splits prod.splits if_split_asm)

subsection \<open>deposit\<close>

context Hash
begin

lemma depositFail:
  assumes "deposit state contracts this block msg ID token amount = 
             (Fail str, state', contracts')"
  shows "state' = state" and "contracts' = contracts"
  using assms
  unfolding deposit_def
  by (auto simp add: Let_def split: prod.splits if_split_asm)

lemma callDepositFail:
  assumes "callDeposit contracts address block msg ID token amount = 
             (Fail str, contracts')"
  shows "contracts' = contracts"
  using assms depositFail
  unfolding callDeposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma depositWritesHash:
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  shows "getDeposit state' ID = hash3 (sender msg) token amount"
  using assms callSafeTransferFromBalanceOfTo'
  unfolding deposit_def
  by (auto simp add: Let_def split: prod.splits if_split_asm)

lemma callDepositWritesHash:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "getDepositTD contracts' address ID = hash3 (sender msg) token amount"
  using assms depositWritesHash
  unfolding callDeposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

text \<open>other deposits enteries are not changed\<close>
lemma callDepositOtherID [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  assumes "ID' \<noteq> ID"
  shows "getDepositTD contracts' address ID' =
         getDepositTD contracts address ID'"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma depositBalanceOfContract:
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  shows "accountBalance contracts' token this = 
         accountBalance contracts token this + amount"
  using assms callSafeTransferFromBalanceOfTo callBalanceOf
  unfolding deposit_def
  by (auto simp add: Let_def split: prod.splits if_split_asm)
  
lemma callDepositBalanceOfContract:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "accountBalance contracts' token address = 
         accountBalance contracts token address + amount"
  using assms depositBalanceOfContract
  unfolding callDeposit_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)
 
lemma depositBalanceOfUser:
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  shows  "amount \<le> accountBalance contracts token (sender msg)"
         "accountBalance contracts' token (sender msg) =
          accountBalance contracts token (sender msg) - amount"
  using assms
  using safeTransferFromBalanceOfCaller
  unfolding deposit_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositBalanceOfUser:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "amount \<le> accountBalance contracts token (sender msg) " 
        "accountBalance contracts' token (sender msg) =
         accountBalance contracts token (sender msg) - amount "
  using assms depositBalanceOfUser
  unfolding callDeposit_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma depositBalanceOfOther:
  assumes "other \<noteq> this" "other \<noteq> sender msg"
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  shows "accountBalance contracts' token other =
         accountBalance contracts token other"
  using assms
  using safeTransferFromBalanceOfOther
  unfolding deposit_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositBalanceOfOther:
  assumes "other \<noteq> address" "other \<noteq> sender msg"
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "accountBalance contracts' token other =
         accountBalance contracts token other"
  using assms depositBalanceOfOther
  unfolding callDeposit_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)


lemma callDepositTokenWithdrawn [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "tokenWithdrawn (the (tokenDepositState contracts' address')) = 
         tokenWithdrawn (the (tokenDepositState contracts address'))"
  using assms
  unfolding callDeposit_def deposit_def
  by (cases "address = address'", auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositReleases [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "releases (the (tokenDepositState contracts' address')) = 
         releases (the (tokenDepositState contracts address'))"
  using assms
  unfolding callDeposit_def deposit_def
  by (cases "address = address'", auto simp add: Let_def split: option.splits prod.splits if_split_asm)

\<comment> \<open>Only existing tokens can give successful deposit \<close>
lemma depositTokenExists:
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  assumes "stateTokenPairs = the (tokenPairsState contracts (TokenDepositState.tokenPairs state))"
  shows "token \<in> Mapping.keys (originalToMinted stateTokenPairs)"
proof-
  have "lookupNat (originalToMinted stateTokenPairs) token > 0"
    using assms callOriginalToMinted[of contracts]
    unfolding deposit_def
    by (auto simp add: Let_def split: prod.splits if_split_asm)
  then show ?thesis
    unfolding lookupNat_def Mapping.lookup_default_def
    by (auto split: option.splits simp add: keys_is_none_rep)
qed

lemma callDepositTokenExists:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "token \<in> Mapping.keys (originalToMinted (tokenPairsStateTD contracts address))"
  using assms depositTokenExists
  unfolding callDeposit_def
  by (simp add: Let_def split: option.splits prod.splits if_split_asm)


text \<open>There can be no double deposit\<close>
lemma callDepositWrittenHash:
  assumes "getDepositTD contracts address ID \<noteq> 0"
  shows "fst (callDeposit contracts address block msg ID token amount) \<noteq> Success"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
end

context StrongHash
begin

text \<open>This lemma is later generalized to non-consecutive states\<close>
lemma depositNoDouble:
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  shows "fst (deposit state' (setTokenDepositState contracts' this state') this block' msg' ID token' amount') \<noteq> Success"
proof-
  have "getDeposit state' ID = hash3 (sender msg) token amount"
    using assms depositWritesHash by blast
  with hash3_nonzero
  show ?thesis
    unfolding deposit_def
    by (auto split: prod.splits simp add: Let_def)
qed

lemma callDepositNoDouble:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "fst (callDeposit contracts' address block' msg' ID token' amount') \<noteq> Success"
  using assms depositNoDouble
  unfolding callDeposit_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm) (metis fst_conv)
end

context Hash
begin

lemma callDepositITokenPairs [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (status, contracts')"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositIBridge [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (status, contracts')"
  shows "IBridge contracts' = IBridge contracts"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositIProofVerifier [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (status, contracts')"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositIStateOracle [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "IStateOracle contracts' = IStateOracle contracts"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositOtherAddress [simp]: 
  assumes "address' \<noteq> address"
          "callDeposit contracts address block msg ID token amount = (status, contracts')"
  shows "tokenDepositState contracts' address' = tokenDepositState contracts address'"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositStateOracle [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "stateOracleAddressTD contracts' address' = stateOracleAddressTD contracts address'"
  using assms
  unfolding callDeposit_def deposit_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositTokenPairs [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows  "tokenPairsAddressTD contracts' address' = tokenPairsAddressTD contracts address'"
  using assms
  unfolding callDeposit_def deposit_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma callDepositBridge [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "bridgeAddressTD contracts' address' = bridgeAddressTD contracts address'"
  using assms
  unfolding callDeposit_def deposit_def
  by (cases "address = address'") (auto split: option.splits prod.splits if_split_asm)

lemma callDepositProofVerifier [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "proofVerifierAddressTD contracts' address' = proofVerifierAddressTD contracts address'"
  using assms
  unfolding callDeposit_def deposit_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositERC20state:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "ERC20state contracts token \<noteq> None" and "ERC20state contracts' token \<noteq> None"
  using assms callBalanceOfERC20state
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callDepositOtherToken:
  assumes "token' \<noteq> token"
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms callSafeTransferFromOtherToken
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)
  

lemma callDepositFailsInDeadState:
  assumes "bridgeDead contracts tokenDepositAddress"
  shows "fst (callDeposit contracts tokenDepositAddress block msg ID token amount) \<noteq> Success"
  using assms getDeadStatusFalse
  unfolding callDeposit_def deposit_def
  by (auto split: option.splits prod.splits)

lemma callDepositInDeadState:
  assumes "bridgeDead contracts tokenDepositAddress"
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "deadStateTD contracts' tokenDepositAddress = deadStateTD contracts tokenDepositAddress"
  using assms
  by (cases "address = tokenDepositAddress", metis callDepositFailsInDeadState fstI, metis callDepositOtherAddress)

lemma callDepositDeadStateRemainsSet:
  assumes "bridgeDead contracts tokenDepositAddress"
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "bridgeDead contracts' tokenDepositAddress"
  using callDepositInDeadState[OF assms] assms
  by simp

lemma callDepositNotBridgeDead':
  assumes "callDeposit contracts tokenDepositAddress block msg ID token amount = (Success, contracts')"
  shows "\<not> bridgeDead contracts' tokenDepositAddress"
  using assms getDeadStatusFalse'
  unfolding callDeposit_def deposit_def
  by (auto split: option.splits prod.splits if_split_asm)

lemma callDepositLastValidStateTD [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "lastValidStateTD contracts' tokenDepositAdddress = 
         lastValidStateTD contracts tokenDepositAdddress"
  using assms
  by (smt (verit, ccfv_SIG) Hash.callDepositOtherAddress Hash.callDepositStateOracle callDepositDeadStateRemainsSet callDepositIStateOracle callDepositNotBridgeDead' callLastState_def lastValidState_def)

lemma finiteBalancesSetTokenDepositState:
  assumes "finiteBalances contracts token'"
  shows "finiteBalances (setTokenDepositState contracts address state) token'"
  using assms
  by (simp add: finiteBalances_def)

lemma callDepositFiniteBalances:
  assumes "finiteBalances contracts token'"
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "finiteBalances contracts' token'"
proof (cases "token = token'")
  case True
  then show ?thesis
    using assms callSafeTransferFromFiniteBalances[of contracts token "sender msg" address amount]
    by (auto simp add: finiteBalances_def callDeposit_def deposit_def split: option.splits prod.splits if_split_asm)
next
  case False
  then show ?thesis
    using assms
    unfolding finiteBalances_def
    by (metis callDepositOtherToken)
qed

text \<open>Sufficient conditions for a deposit to be made\<close>
lemma callDepositI:
  assumes "tokenDepositState contracts address = Some state"
  assumes "tokenPairsState contracts (TokenDepositState.tokenPairs state) = Some stateTokenPairs"
  assumes "ERC20state contracts token = Some stateToken"
  assumes "getMinted stateTokenPairs token \<noteq> 0"

  \<comment> \<open>bridge is not dead\<close>
  assumes "getDeadStatus contracts state block = (Success, False, state')"
  \<comment> \<open>sender is not the bridge itself\<close>
  assumes "sender msg \<noteq> address"
  \<comment> \<open>deposit with this ID has not already been made\<close>
  assumes "getDeposit state ID = 0"
  \<comment> \<open>sender has enough funds\<close>
  assumes "balanceOf stateToken (sender msg) \<ge> amount"
  \<comment> \<open>some funds must be deposited\<close>
  assumes "amount > 0"

  shows "fst (callDeposit contracts address block msg ID token amount) = Success"
proof-
  have "(Success, getMinted stateTokenPairs token) = callOriginalToMinted contracts (TokenDepositState.tokenPairs state') token"
    using assms callOriginalToMintedI
    by (simp add: callOriginalToMinted_def)
  moreover
  have "fst (callSafeTransferFrom contracts token (sender msg) address amount) = Success"
    using assms callSafeTransferFromI
    by auto
  then obtain contracts' where contracts': "callSafeTransferFrom contracts token (sender msg) address amount = (Success, contracts')"
    by (metis eq_fst_iff)
  moreover
  have "fst (callBalanceOf contracts token address) = Success"
    using assms callBalanceOfI
    by auto
  then obtain balanceBefore where 
     "callBalanceOf contracts token address = (Success, balanceBefore)"
    by (metis prod.exhaust_sel)
  moreover
  have "ERC20state contracts' token \<noteq> None"
    using contracts'
    unfolding callSafeTransferFrom_def
    by (auto split: option.splits prod.splits if_split_asm)
  then have "fst (callBalanceOf contracts' token address) = Success"
    using callBalanceOfI
    by auto
  then obtain balanceAfter where 
     "callBalanceOf contracts' token address = (Success, balanceAfter)"
    by (metis prod.exhaust_sel)
  moreover
  have "balanceBefore < balanceAfter"
  proof-
    have "balanceBefore = balanceOf stateToken address"
      using callBalanceOf[OF \<open>callBalanceOf contracts token address = (Success, balanceBefore)\<close>]
      using \<open>ERC20state contracts token = Some stateToken\<close> 
      by simp
    moreover
    have "balanceAfter = balanceBefore + amount"
      using callSafeTransferFromBalanceOfTo \<open>callBalanceOf contracts token address = (Success, balanceBefore)\<close> \<open>callBalanceOf contracts' token address = (Success, balanceAfter)\<close> contracts' 
      by blast
    ultimately
    show ?thesis
      using \<open>amount > 0\<close>
      by auto
  qed
  ultimately
  show ?thesis
    using assms
    unfolding callDeposit_def deposit_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
qed

(* TODO: add other conclusions *)
lemma callDepositE:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "tokenDepositState contracts' address \<noteq> None"
  using assms
  unfolding callDeposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

end


subsection \<open>CancelDepositWhileDead\<close>

context HashProofVerifier
begin

lemma callCancelDepositWhileDeadITokenPairs [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadIProofVerifier [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadIBridge [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "IBridge contracts' = IBridge contracts"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadIStateOracle [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "IStateOracle contracts' = IStateOracle contracts"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadOtherAddress [simp]: 
  assumes "address' \<noteq> address"
          "callCancelDepositWhileDead contracts address msg block ID token amount proof = (status, contracts')"
  shows "tokenDepositState contracts' address' = tokenDepositState contracts address'"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadStateOracle [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "stateOracleAddressTD contracts' address' = stateOracleAddressTD contracts address'"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadDeposits [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "deposits (the (tokenDepositState contracts' address)) =
         Mapping.delete ID (TokenDepositState.deposits (the (tokenDepositState contracts address)))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadBridge [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "bridgeAddressTD contracts' address' = bridgeAddressTD contracts address'"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadTokenPairs [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "tokenPairsAddressTD contracts' address' = tokenPairsAddressTD contracts address'"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadProofVerifier [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "proofVerifierAddressTD contracts' address' = proofVerifierAddressTD contracts address'"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

(* TODO: add other conclusions *)
lemma callCancelDepositWhileDeadE:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "tokenDepositState contracts' address \<noteq> None"
  using assms
  unfolding callCancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadERC20state:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "ERC20state contracts token \<noteq> None" and "ERC20state contracts' token \<noteq> None"
  using assms callSafeTransferFromERC20state
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadOtherToken:
  assumes "token' \<noteq> token"
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms callSafeTransferFromOtherToken
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadInDeadState:
  assumes "deadStateTD contracts tokenDepositAddress \<noteq> 0"
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "deadStateTD contracts' tokenDepositAddress = deadStateTD contracts tokenDepositAddress"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (cases "address = tokenDepositAddress")
     (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadDeadStateRemainsSet:
  assumes "deadStateTD contracts tokenDepositAddress \<noteq> 0"
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "deadStateTD contracts' tokenDepositAddress \<noteq> 0"
  using callCancelDepositWhileDeadInDeadState assms
  by metis

lemma callCancelDepositWhileDeadBridgeDead:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  shows "bridgeDead contracts' tokenDepositAddress"
proof (cases "bridgeDead contracts tokenDepositAddress")
  case False
  then show ?thesis
    using assms
    using callSafeTransferFromIStateOracle
    using getDeadStatusSetsDeadState[of "contracts" "the (tokenDepositState contracts tokenDepositAddress)" block]
    using getDeadStatusTrueDeadState[of "contracts" "the (tokenDepositState contracts tokenDepositAddress)" block]
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
next
  case True
  then show ?thesis
    using assms 
    using callCancelDepositWhileDeadDeadStateRemainsSet
    by blast
qed

lemma callCancelDepositWhileDeadSetsDeadState:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  assumes "\<not> bridgeDead contracts tokenDepositAddress"
  shows "deadStateTD contracts' tokenDepositAddress = 
         lastStateTD contracts tokenDepositAddress"
  using assms getDeadStatusSetsDeadState
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadSetsDeadState' [simp]:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof = (Success, contracts')"
  assumes "\<not> bridgeDead contracts tokenDepositAddress"
  shows "callLastState contracts (stateOracleAddressTD contracts tokenDepositAddress) = 
        (Success, deadStateTD contracts' tokenDepositAddress)"
proof-
  have "fst (callLastState contracts (stateOracleAddressTD contracts tokenDepositAddress)) = Success"
    using assms getDeadStatusLastValidState
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def lastValidState_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
  then show ?thesis
    using callCancelDepositWhileDeadSetsDeadState[OF assms]
    using callLastState
    by (metis split_pairs)
qed

lemma callCancelDepositWhileDeadBalanceOfSender:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  shows "accountBalance contracts' token (sender msg) =
         accountBalance contracts token (sender msg) + amount"
  using assms
  using safeTransferFromBalanceOfTo
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadBalanceOfContract:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  shows 
    "amount \<le> accountBalance contracts token tokenDepositAddress"
    "accountBalance contracts' token tokenDepositAddress =
     accountBalance contracts token tokenDepositAddress - amount"
  using assms
  using safeTransferFromBalanceOfCaller
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadBalanceOfOther:
  assumes "address' \<noteq> address" "address' \<noteq> sender msg"
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof =
           (Success, contracts')"
  shows "accountBalance contracts' token address' = accountBalance contracts token address'"
  using assms callSafeTransferFromBalanceOfOther
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)
  

lemma callCancelDepositWhileDeadFiniteBalances:
  assumes "finiteBalances contracts token'"
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof =
           (Success, contracts')"
  shows "finiteBalances contracts' token'"
proof (cases "token = token'")
  case True
  then show ?thesis
    using assms callSafeTransferFromFiniteBalances[of contracts token' address "sender msg" amount]
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def Let_def
    by (auto split: option.splits prod.splits if_split_asm simp add: finiteBalances_def)
next
  case False
  then show ?thesis
    using assms
    unfolding finiteBalances_def
    by (metis callCancelDepositWhileDeadOtherToken)
qed

lemma callCancelDepositWhileDeadTokenWithdrawn [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "tokenWithdrawn ((the (tokenDepositState contracts' address'))) = 
         tokenWithdrawn ((the (tokenDepositState contracts address')))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (cases "address = address'", auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadReleases [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "releases (the (tokenDepositState contracts' address')) = 
         releases (the (tokenDepositState contracts address'))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (cases "address = address'", auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadLastValidStateTD [simp]:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof = (Success, contracts')"
  shows "lastValidStateTD contracts' address' = 
         lastValidStateTD contracts address'"
  using assms
  by (smt (verit, best) callCancelDepositWhileDeadBridgeDead callCancelDepositWhileDeadIStateOracle callCancelDepositWhileDeadInDeadState callCancelDepositWhileDeadOtherAddress callCancelDepositWhileDeadSetsDeadState' callLastState_def lastValidState_def)
end


context StrongHashProofVerifier
begin

lemma callCancelDepositWhileDeadGetDepositNonzero:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "getDepositTD contracts address ID \<noteq> 0"
  using assms hash3_nonzero[of "sender msg" token amount]
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def Let_def
  by (auto split: option.splits prod.splits if_split_asm)

end

context HashProofVerifier
begin

lemma callCancelDepositWhileDeadCallVerifyClaimProof:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  shows "callVerifyClaimProof 
           contracts 
           (proofVerifierAddressTD contracts tokenDepositAddress) 
           (bridgeAddressTD contracts tokenDepositAddress) ID
           (snd (lastValidStateTD contracts tokenDepositAddress)) proof = Success"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadVerifyClaimProof:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  shows "verifyClaimProof 
            ()
            (bridgeAddressTD contracts tokenDepositAddress)
            ID 
            (snd (lastValidStateTD contracts tokenDepositAddress)) proof"
  using callCancelDepositWhileDeadCallVerifyClaimProof[OF assms]
  unfolding callVerifyClaimProof_def
  by (simp split: option.splits if_split_asm)

lemma callCancelDepositWhileDeadI:
  assumes "tokenDepositState contracts address \<noteq> None"
  assumes "stateOracleState contracts (stateOracleAddressTD contracts address) \<noteq> None"
  assumes "proofVerifierState contracts (TokenDepositState.proofVerifier (the (tokenDepositState contracts address))) \<noteq> None"
  assumes "ERC20state contracts token \<noteq> None"
  assumes "getDepositTD contracts address ID = hash3 (sender msg) token amount"
  assumes "fst (snd (getDeadStatus contracts (the (tokenDepositState contracts address)) block)) = True"
  assumes "bridgeDead contracts address \<longrightarrow> deadState (the (tokenDepositState contracts address)) = stateRoot"
  assumes "\<not> bridgeDead contracts address \<longrightarrow> lastState (the (stateOracleState contracts (stateOracleAddressTD contracts address))) = stateRoot"
  assumes "verifyClaimProof () (TokenDepositState.bridge (the (tokenDepositState contracts address))) ID stateRoot proof"
  assumes "amount \<le> balanceOf (the (ERC20state contracts token)) address"
  assumes "sender msg \<noteq> address"
  shows "fst (callCancelDepositWhileDead contracts address msg block ID token amount proof) = Success"
  using assms
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


subsection \<open>Withdraw while dead\<close>

lemma callWithdrawWhileDeadITokenPairs [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadIProofVerifier [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadIBridge [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "IBridge contracts' = IBridge contracts"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadIStateOracle [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "IStateOracle contracts' = IStateOracle contracts"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadOtherAddress [simp]: 
  assumes "address' \<noteq> address"
          "callWithdrawWhileDead contracts address msg block token amount proof = (status, contracts')"
  shows "tokenDepositState contracts' address' = tokenDepositState contracts address'"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadStateOracle [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "stateOracleAddressTD contracts' address' = stateOracleAddressTD contracts address'"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadBridge [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "bridgeAddressTD contracts' address' = bridgeAddressTD contracts address'"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadTokenPairs [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "tokenPairsAddressTD contracts' address' = tokenPairsAddressTD contracts address'"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadDeposits [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "TokenDepositState.deposits (the (tokenDepositState contracts' address')) =
         TokenDepositState.deposits (the (tokenDepositState contracts address'))"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadProofVerifier [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "proofVerifierAddressTD contracts' address' = proofVerifierAddressTD contracts address'"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadERC20state:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "ERC20state contracts token \<noteq> None" and "ERC20state contracts' token \<noteq> None"
  using assms callSafeTransferFromERC20state
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadOtherToken:
  assumes "token' \<noteq> token"
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms callSafeTransferFromOtherToken
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadTokenWithdrawn [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "getTokenWithdrawnTD contracts' address (hash2 (sender msg) token) = True"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def lookupBool_def lookup_default_update split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadNotTokenWithdrawn [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "getTokenWithdrawnTD contracts address (hash2 (sender msg) token) = False"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def lookupBool_def lookup_default_update split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadReleases [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "releases (the (tokenDepositState contracts' address')) = 
         releases (the (tokenDepositState contracts address'))"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = address'", auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadBalanceOfSender:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  shows "accountBalance contracts' token (sender msg) =
         accountBalance contracts token (sender msg) + amount"
  using assms
  using safeTransferFromBalanceOfTo
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadBalanceOfContract:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  shows 
    "amount \<le> accountBalance contracts token tokenDepositAddress"
    "accountBalance contracts' token tokenDepositAddress =
     accountBalance contracts token tokenDepositAddress - amount "
  using assms
  using safeTransferFromBalanceOfCaller
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadBalanceOfOther:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  assumes "address \<noteq> tokenDepositAddress" "address \<noteq> sender msg"
  shows "accountBalance contracts' token address = accountBalance contracts token address"
  using assms
  using safeTransferFromBalanceOfOther
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma callWithdrawWhileDeadFiniteBalances:
  assumes "finiteBalances contracts token'"
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "finiteBalances contracts' token'"
proof (cases "token = token'")
  case True
  then show ?thesis
    using assms callSafeTransferFromFiniteBalances[of contracts token' address "sender msg" amount]
    unfolding callWithdrawWhileDead_def withdrawWhileDead_def Let_def
    by (auto split: option.splits prod.splits if_split_asm simp add: finiteBalances_def)
next
  case False
  then show ?thesis
    using assms
    unfolding finiteBalances_def
    by (metis callWithdrawWhileDeadOtherToken)
qed

(* TODO: add other conclusions *)
lemma callWithdrawWhileDeadE:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "tokenDepositState contracts' address \<noteq> None"
  using assms
  unfolding callWithdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadInDeadState:
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"
  assumes "callWithdrawWhileDead contracts address msg block oken amount proof = (Success, contracts')"
  shows "deadStateTD contracts' tokenDepositAddress = deadStateTD contracts tokenDepositAddress"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = tokenDepositAddress")
     (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadSetsDeadState:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  assumes "\<not> bridgeDead contracts tokenDepositAddress"
  shows "deadStateTD contracts' tokenDepositAddress = lastStateTD contracts tokenDepositAddress"
  using assms getDeadStatusSetsDeadState
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadSetsDeadState':
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof = (Success, contracts')"
  assumes "\<not> bridgeDead contracts tokenDepositAddress"
  shows "callLastState contracts (stateOracleAddressTD contracts tokenDepositAddress) = 
        (Success, deadStateTD contracts' tokenDepositAddress)"
proof-
  have "fst (callLastState contracts (stateOracleAddressTD contracts tokenDepositAddress)) = Success"
    using assms getDeadStatusLastValidState getDeadStatusTrueDeadState
    unfolding callWithdrawWhileDead_def withdrawWhileDead_def lastValidState_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)
       (metis fst_conv less_not_refl3) (* FIXME: avoid calling methods after auto *)
  then show ?thesis
    using callWithdrawWhileDeadSetsDeadState[OF assms]
    using callLastState
    by (metis split_pairs)
qed

lemma callWithdrawWhileDeadBridgeDead:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  shows "bridgeDead contracts' tokenDepositAddress"
  using assms getDeadStatusTrueDeadState
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadTokenWithdrawn':
  assumes "getTokenWithdrawnTD contracts address' h = True"
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "getTokenWithdrawnTD contracts' address' h = True"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = address'", cases "hash2 (sender msg) token = h", auto simp add: Let_def lookupBool_def lookup_default_update' split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadCallVerifyBalanceProof:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof = (Success, contracts')"
  shows "callVerifyBalanceProof 
           contracts 
           (proofVerifierAddressTD contracts tokenDepositAddress) 
           (mintedTokenTD contracts tokenDepositAddress token) (sender msg) amount
           (snd (lastValidStateTD contracts tokenDepositAddress))
           proof = Success"
  using assms callOriginalToMinted[of contracts "tokenPairsAddressTD contracts tokenDepositAddress" token]
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def getDeadStatus_def lastValidState_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadVerifyBalanceProof:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof = (Success, contracts')"
  shows "verifyBalanceProof () (mintedTokenTD contracts tokenDepositAddress token) (sender msg) amount 
              (snd (lastValidStateTD contracts tokenDepositAddress)) proof"
  using callWithdrawWhileDeadCallVerifyBalanceProof[OF assms]
  unfolding callVerifyBalanceProof_def
  by (simp split: option.splits if_split_asm)

lemma callWithdrawWhileDeadLastValidStateTD [simp]:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof = (Success, contracts')"
  shows "lastValidStateTD contracts' address' = 
         lastValidStateTD contracts address'"
  using assms
  by (smt (verit, ccfv_threshold) HashProofVerifier.callWithdrawWhileDeadIStateOracle HashProofVerifier_axioms callLastState_def callWithdrawWhileDeadBridgeDead callWithdrawWhileDeadInDeadState callWithdrawWhileDeadOtherAddress callWithdrawWhileDeadSetsDeadState' lastValidState_def)

lemma callWithdrawWhileDeadI:
  assumes "tokenDepositState contracts tokenDepositAddress \<noteq> None"
  assumes "ERC20state contracts token \<noteq> None"
  assumes "tokenPairsState contracts (tokenPairsAddressTD contracts tokenDepositAddress) \<noteq> None"
  assumes "stateOracleState contracts (stateOracleAddressTD contracts tokenDepositAddress) \<noteq> None"
  assumes "proofVerifierState contracts (TokenDepositState.proofVerifier (the (tokenDepositState contracts tokenDepositAddress))) \<noteq> None"
  assumes "fst (snd (getDeadStatus contracts (the (tokenDepositState contracts tokenDepositAddress)) block)) = True"
  assumes "getTokenWithdrawnTD contracts tokenDepositAddress (hash2 (sender msg) token) = False"
  assumes "tokenDepositAddress \<noteq> sender msg"
  assumes "amount \<le> accountBalance contracts token tokenDepositAddress"
  assumes "mintedTokenTD contracts tokenDepositAddress token \<noteq> 0"
  assumes "verifyBalanceProof () (mintedTokenTD contracts tokenDepositAddress token) (sender msg) amount 
              (snd (lastValidStateTD contracts tokenDepositAddress)) proof"
  shows "fst (callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof) = Success"
proof-
  define stateTokenDeposit where [simp]: "stateTokenDeposit = the (tokenDepositState contracts tokenDepositAddress)"
  have "fst (getDeadStatus contracts stateTokenDeposit block) = Success"
    using getDeadStatusI[OF assms(4), of block]
    by simp
  moreover
  have "fst (callSafeTransferFrom contracts token tokenDepositAddress (sender msg) amount) =
      Success"
    using callSafeTransferFromI[of contracts token _ amount tokenDepositAddress "sender msg"]
    using assms(2) assms(8-9)
    by auto
  moreover
  have "callOriginalToMinted contracts (tokenPairsAddressTD contracts tokenDepositAddress) token =
        (Success, mintedTokenTD contracts tokenDepositAddress token)"
    using callOriginalToMintedI[OF assms(3), of token]
    using callOriginalToMinted[of contracts "tokenPairsAddressTD contracts tokenDepositAddress" token]
    by (metis split_pairs)
  moreover
  have "callVerifyBalanceProof 
           contracts 
           (proofVerifierAddressTD contracts tokenDepositAddress) 
           (mintedTokenTD contracts tokenDepositAddress token) (sender msg) amount
           (snd (lastValidStateTD contracts tokenDepositAddress))
           proof = Success"
    using assms(5) assms(11)
    unfolding callVerifyBalanceProof_def
    by (auto simp add: Let_def split: option.splits prod.splits)
  moreover
  have "deadState (snd (snd (getDeadStatus contracts stateTokenDeposit block))) = 
        snd (lastValidStateTD contracts tokenDepositAddress)"
    using \<open>fst (snd (getDeadStatus contracts (the (tokenDepositState contracts tokenDepositAddress)) block)) = True\<close>
    using assms(4) \<open>fst (getDeadStatus contracts stateTokenDeposit block) = Success\<close>
    unfolding stateTokenDeposit_def
    by (smt (z3) callLastState getDeadStatusInDeadState getDeadStatusSetsDeadState lastValidStateI lastValidState_def prod.collapse snd_conv stateTokenDeposit_def)
  ultimately
  show ?thesis
    using \<open>tokenDepositState contracts tokenDepositAddress \<noteq> None\<close>
    using \<open>mintedTokenTD contracts tokenDepositAddress token \<noteq> 0\<close>
    using \<open>getTokenWithdrawnTD contracts tokenDepositAddress (hash2 (sender msg) token) = False\<close>
    using \<open>fst (snd (getDeadStatus contracts (the (tokenDepositState contracts tokenDepositAddress)) block)) = True\<close>
    unfolding callWithdrawWhileDead_def withdrawWhileDead_def lastValidState_def
    by (auto simp add: Let_def split: option.splits prod.splits)
qed
end


context HashProofVerifier
begin

subsection \<open>Release\<close>

lemma callReleaseITokenPairs [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
  unfolding callRelease_def release_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseIProofVerifier [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
  unfolding callRelease_def release_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseIBridge [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "IBridge contracts' = IBridge contracts"
  using assms
  unfolding callRelease_def release_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseIStateOracle [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "IStateOracle contracts' = IStateOracle contracts"
  using assms
  unfolding callRelease_def release_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseOtherAddress [simp]: 
  assumes "address' \<noteq> address"
          "callRelease contracts address msg ID token amount proof = (status, contracts')"
  shows "tokenDepositState contracts' address' = tokenDepositState contracts address'"
  using assms
  unfolding callRelease_def release_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseStateOracleAddress [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "stateOracleAddressTD contracts' address' = 
         stateOracleAddressTD contracts address'"
  using assms
  unfolding callRelease_def release_def
  by (cases "address=address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma callReleaseBridgeAddress [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "bridgeAddressTD contracts' address' = bridgeAddressTD contracts address'"
  using assms
  unfolding callRelease_def release_def
  by (cases "address=address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseTokenPairs [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "tokenPairsAddressTD contracts' address' = tokenPairsAddressTD contracts address'"
  using assms
  unfolding callRelease_def release_def
  by (cases "address=address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseDeposits [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "TokenDepositState.deposits (the (tokenDepositState contracts' address')) =
         TokenDepositState.deposits (the (tokenDepositState contracts address'))"
  using assms
  unfolding callRelease_def release_def
  by (cases "address=address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseProofVerifier [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "proofVerifierAddressTD contracts' address' = proofVerifierAddressTD contracts address'"
  using assms
  unfolding callRelease_def release_def
  by (cases "address=address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma callReleaseTokenWithdrawn [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "tokenWithdrawn (the (tokenDepositState contracts' address')) =
         tokenWithdrawn (the (tokenDepositState contracts address'))"
  using assms
  unfolding callRelease_def release_def
  by (cases "address=address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma callReleaseDeadState [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "deadStateTD contracts' address' = deadStateTD contracts address'"
  using assms
  unfolding callRelease_def release_def
  by (cases "address=address'") (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseERC20state:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "ERC20state contracts token \<noteq> None" and "ERC20state contracts' token \<noteq> None"
  using assms callSafeTransferFromERC20state
  unfolding callRelease_def release_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callReleaseOtherToken:
  assumes "token' \<noteq> token"
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms callSafeTransferFromOtherToken
  unfolding callRelease_def release_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callReleaseOtherID:
  assumes "ID' \<noteq> ID"
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "getReleaseTD contracts' address ID' = getReleaseTD contracts address ID'"
  using assms
  unfolding callRelease_def release_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseRelase [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "getReleaseTD contracts' address ID = True"
  using assms
  unfolding callRelease_def release_def
  by (auto simp add: Let_def lookupBool_def lookup_default_update split: option.splits prod.splits if_split_asm)

lemma callReleaseNotReleased [simp]:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "getReleaseTD contracts address ID = False"
  using assms
  unfolding callRelease_def release_def
  by (auto simp add: Let_def lookupBool_def lookup_default_update split: option.splits prod.splits if_split_asm)

lemma callReleaseBalanceOfSender:
  assumes "callRelease contracts tokenDepositAddress msg ID token amount proof =
           (Success, contracts')"
  shows "accountBalance contracts' token (sender msg) =
         accountBalance contracts token (sender msg) + amount"
  using assms
  using safeTransferFromBalanceOfTo
  unfolding callRelease_def release_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseBalanceOfContract:
  assumes "callRelease contracts tokenDepositAddress msg ID token amount proof =
           (Success, contracts')"
  shows 
    "amount \<le> accountBalance contracts token tokenDepositAddress"
    "accountBalance contracts' token tokenDepositAddress =
     accountBalance contracts token tokenDepositAddress - amount "
  using assms
  using safeTransferFromBalanceOfCaller
  unfolding callRelease_def release_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseBalanceOfOther:
  assumes "callRelease contracts tokenDepositAddress msg ID token amount proof =
           (Success, contracts')"
  assumes "address \<noteq> tokenDepositAddress" "address \<noteq> sender msg"
  shows "accountBalance contracts' token address = accountBalance contracts token address"
  using assms
  using safeTransferFromBalanceOfOther
  unfolding callRelease_def release_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma callReleaseFiniteBalances:
  assumes "finiteBalances contracts token'"
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "finiteBalances contracts' token'"
proof (cases "token = token'")
  case True
  then show ?thesis
    using assms callSafeTransferFromFiniteBalances[of contracts token' address "sender msg" amount]
    unfolding callRelease_def release_def Let_def
    by (auto split: option.splits prod.splits if_split_asm simp add: finiteBalances_def)
next
  case False
  then show ?thesis
    using assms
    unfolding finiteBalances_def
    by (metis callReleaseOtherToken)
qed

(* TODO: add other conclusions *)
lemma callReleaseE:
  assumes "callRelease contracts address msg ID token amount proof = (Success, contracts')"
  shows "tokenDepositState contracts' address \<noteq> None"
  using assms
  unfolding callRelease_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma callReleaseCallVerifyBurnProof:
  assumes "callRelease contracts tokenDepositAddress msg ID token amount proof = (Success, contracts')"
  shows "callVerifyBurnProof 
           contracts 
           (proofVerifierAddressTD contracts tokenDepositAddress) 
           (bridgeAddressTD contracts tokenDepositAddress) 
           ID
           (hash3 (sender msg) token amount)
           (snd (lastValidStateTD contracts tokenDepositAddress))
           proof = Success"
  using assms 
  unfolding callRelease_def release_def lastValidState_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseVerifyBurnProof:
  assumes "callRelease contracts tokenDepositAddress msg ID token amount proof = (Success, contracts')"
  shows "verifyBurnProof () 
         (bridgeAddressTD contracts tokenDepositAddress)
         ID
         (hash3 (sender msg) token amount)
         (snd (lastValidStateTD contracts tokenDepositAddress))
         proof"
  using callReleaseCallVerifyBurnProof[OF assms]
  unfolding callVerifyBurnProof_def
  by (simp split: option.splits if_split_asm)

lemma callReleaseLastValidStateTD [simp]:
  assumes "callRelease contracts tokenDepositAddress msg ID token amount proof = (Success, contracts')"
  shows "lastValidStateTD contracts' tokenDepositAddress = 
         lastValidStateTD contracts tokenDepositAddress"
  using assms
  using assms
  unfolding callRelease_def release_def lastValidState_def callLastState_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callReleaseI:
  assumes "tokenDepositState contracts tokenDepositAddress \<noteq> None"
  assumes "ERC20state contracts token \<noteq> None"
  assumes "stateOracleState contracts (stateOracleAddressTD contracts tokenDepositAddress) \<noteq> None"
  assumes "proofVerifierState contracts (TokenDepositState.proofVerifier (the (tokenDepositState contracts tokenDepositAddress))) \<noteq> None"
  assumes "amount \<le> accountBalance contracts token tokenDepositAddress"
  assumes "getReleaseTD contracts tokenDepositAddress ID = False"
  assumes "tokenDepositAddress \<noteq> sender msg"
  assumes "verifyBurnProof () (bridgeAddressTD contracts tokenDepositAddress) ID (hash3 (sender msg) token amount) (snd (lastValidStateTD contracts tokenDepositAddress)) proof"
  shows "fst (callRelease contracts tokenDepositAddress msg ID token amount proof) = Success"
proof-
  define stateTokenDeposit where [simp]: "stateTokenDeposit = the (tokenDepositState contracts tokenDepositAddress)"
  have "fst (callSafeTransferFrom contracts token tokenDepositAddress (sender msg) amount) =
      Success"
    using callSafeTransferFromI[of contracts token _ amount tokenDepositAddress "sender msg"]
    using assms
    by auto
  moreover
  have "callVerifyBurnProof 
           contracts 
           (proofVerifierAddressTD contracts tokenDepositAddress) 
           (bridgeAddressTD contracts tokenDepositAddress) 
           ID
           (hash3 (sender msg) token amount)
           (snd (lastValidStateTD contracts tokenDepositAddress))
           proof = Success"
    using assms
    unfolding callVerifyBurnProof_def
    by (auto simp add: Let_def split: option.splits prod.splits)
  moreover
  have "fst (callLastState contracts (TokenDepositState.stateOracle stateTokenDeposit)) = Success"
    using callLastStateI
    using assms stateTokenDeposit_def by blast
  ultimately
  show ?thesis
    using \<open>tokenDepositState contracts tokenDepositAddress \<noteq> None\<close>
    using \<open>getReleaseTD contracts tokenDepositAddress ID = False\<close>
    unfolding callRelease_def release_def lastValidState_def
    by (auto simp add: Let_def split: option.splits prod.splits)
qed

end

end
