theory TokenDepositState
  imports Main Definition More_Mapping ERC20State TokenPairsState StateOracleState
begin

section \<open>TokenDeposit\<close>

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

lemma getDeadStatusLastValidState [simp]:
  assumes "getDeadStatus contracts state block = (Success, ret, state')"
  shows "lastValidState contracts state' = lastValidState contracts state"
  using assms
  unfolding getDeadStatus_def lastValidState_def
  by (auto split: if_split_asm prod.splits)

lemma getDeadStatusTokenWithdrawn [simp]:
  assumes "getDeadStatus contracts state block = (status, dead, state')"
  shows "TokenDepositState.tokenWithdrawn state' = TokenDepositState.tokenWithdrawn state"
  using assms
  unfolding getDeadStatus_def
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
  shows "deadState state' = lastState (the (stateOracleState contracts (TokenDepositState.stateOracle state)))"
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
  assumes "deposit state contracts this block msg ID token amount = 
             (Success, state', contracts')"
  shows "getDeposit state' ID = hash3 (sender msg) token amount"
  using assms callSafeTransferFromBalanceOfTo'
  unfolding deposit_def
  by (auto simp add: Let_def split: prod.splits if_split_asm)

lemma callDepositWritesHash:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "getDeposit (the (tokenDepositState contracts' address)) ID = 
         hash3 (sender msg) token amount"
  using assms depositWritesHash
  unfolding callDeposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

text \<open>other deposits enteries are not changed\<close>
lemma callDepositOtherID [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  assumes "ID' \<noteq> ID"
  shows "getDeposit (the (tokenDepositState contracts' address)) ID' =
         getDeposit (the (tokenDepositState contracts address)) ID'"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma depositBalanceOfContract:
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  shows "balanceOf (the (ERC20state contracts' token)) this =
         balanceOf (the (ERC20state contracts token)) this + amount"
  using assms callSafeTransferFromBalanceOfTo
  unfolding deposit_def
  by (auto simp add: Let_def split: prod.splits if_split_asm)

lemma callDepositBalanceOfContract:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "balanceOf (the (ERC20state contracts' token)) address =
         balanceOf (the (ERC20state contracts token)) address + amount"
  using assms depositBalanceOfContract
  unfolding callDeposit_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)
 
lemma depositBalanceOfUser:
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  shows "balanceOf (the (ERC20state contracts token)) (sender msg) \<ge> amount" 
        "balanceOf (the (ERC20state contracts' token)) (sender msg) = 
         balanceOf (the (ERC20state contracts token)) (sender msg) - amount"
  using assms
  using safeTransferFromBalanceOfCaller[of "the (ERC20state contracts' token)" "the (ERC20state contracts token)" "sender msg" this amount]
  unfolding deposit_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositBalanceOfUser:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "balanceOf (the (ERC20state contracts token)) (sender msg) \<ge> amount" 
        "balanceOf (the (ERC20state contracts' token)) (sender msg) = 
         balanceOf (the (ERC20state contracts token)) (sender msg) - amount"
  using assms depositBalanceOfUser
  unfolding callDeposit_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma depositBalanceOfOther:
  assumes "other \<noteq> this" "other \<noteq> sender msg"
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  shows "balanceOf (the (ERC20state contracts' token)) other = 
         balanceOf (the (ERC20state contracts token)) other"
  using assms
  using safeTransferFromBalanceOfOther[of other "sender msg" this "the (ERC20state contracts' token)" "the (ERC20state contracts token)" amount]
  unfolding deposit_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositBalanceOfOther:
  assumes "other \<noteq> address" "other \<noteq> sender msg"
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "balanceOf (the (ERC20state contracts' token)) other = 
         balanceOf (the (ERC20state contracts token)) other"
  using assms depositBalanceOfOther
  unfolding callDeposit_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)


lemma callDepositTokenWithdrawn [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "tokenWithdrawn ((the (tokenDepositState contracts' address'))) = 
         tokenWithdrawn ((the (tokenDepositState contracts address')))"
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
  assumes "state = the (tokenDepositState contracts address)"
  assumes "stateTokenPairs = the (tokenPairsState contracts (TokenDepositState.tokenPairs state))"
  shows "token \<in> Mapping.keys (originalToMinted stateTokenPairs)"
  using assms depositTokenExists
  unfolding callDeposit_def
  by (simp add: Let_def split: option.splits prod.splits if_split_asm)


text \<open>There can be no double deposit\<close>
lemma callDepositWrittenHash:
  assumes "getDeposit (the (tokenDepositState contracts address)) ID \<noteq> 0"
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
  shows "ITokenPairs contracts = ITokenPairs contracts'"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositIBridge [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (status, contracts')"
  shows "IBridge contracts = IBridge contracts'"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositIProofVerifier [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (status, contracts')"
  shows "IProofVerifier contracts = IProofVerifier contracts'"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositIStateOracle [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "IStateOracle contracts = IStateOracle contracts'"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositOtherAddress [simp]: 
  assumes "address \<noteq> address'"
          "callDeposit contracts address' block msg ID token amount = (status, contracts')"
  shows "tokenDepositState contracts' address = tokenDepositState contracts address"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositStateOracle [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "TokenDepositState.stateOracle (the (tokenDepositState contracts' address)) =
         TokenDepositState.stateOracle (the (tokenDepositState contracts address))"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositTokenPairs [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows  "TokenDepositState.tokenPairs (the (tokenDepositState contracts' address)) =
          TokenDepositState.tokenPairs (the (tokenDepositState contracts address))"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositBridge [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "TokenDepositState.bridge (the (tokenDepositState contracts address)) = 
         TokenDepositState.bridge (the (tokenDepositState contracts' address))"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto split: option.splits prod.splits if_split_asm)

lemma callDepositProofVerifier [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "TokenDepositState.proofVerifier (the (tokenDepositState contracts' address)) =
         TokenDepositState.proofVerifier (the (tokenDepositState contracts address))"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositERC20state:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "ERC20state contracts token \<noteq> None" and "ERC20state contracts' token \<noteq> None"
  using assms callBalanceOfERC20state
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callDepositOtherToken [simp]:
  assumes "token' \<noteq> token"
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callDepositFailsInDeadState:
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"
  shows "fst (callDeposit contracts tokenDepositAddress block msg ID token amount) \<noteq> Success"
  using assms getDeadStatusFalse
  unfolding callDeposit_def deposit_def
  by (auto split: option.splits prod.splits)

lemma callDepositInDeadState:
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 
         deadState (the (tokenDepositState contracts tokenDepositAddress))"
  using assms
  by (cases "address = tokenDepositAddress", metis callDepositFailsInDeadState fstI, metis callDepositOtherAddress)

lemma callDepositDeadStateRemainsSet:
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
  using callDepositInDeadState[OF assms] assms
  by simp

lemma callDepositLiveState:
  assumes "callDeposit contracts tokenDepositAddress block msg ID token amount = (Success, contracts')"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 0"
  using assms getDeadStatusFalse'
  unfolding callDeposit_def deposit_def
  by (auto split: option.splits prod.splits if_split_asm)

lemma callDepositSetsDeadState:
  assumes "getLastStateTD contracts tokenDepositAddress = stateRoot"
  assumes "callDeposit contracts tokenDepositAddress block msg ID token' amount = (Success, contracts')"
  assumes "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = stateRoot"
  using \<open>callDeposit contracts tokenDepositAddress block msg ID token' amount = (Success, contracts')\<close>
  using \<open>deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0\<close>
  using getDeadStatusFalse'
  unfolding callDeposit_def deposit_def
  by (auto split: option.splits prod.splits if_split_asm)

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
  assumes "address \<noteq> address'"
          "callCancelDepositWhileDead contracts address' msg block ID token amount proof = (status, contracts')"
  shows "tokenDepositState contracts' address = tokenDepositState contracts address"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadStateOracle [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "TokenDepositState.stateOracle (the (tokenDepositState contracts' address)) =
         TokenDepositState.stateOracle (the (tokenDepositState contracts address))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadDeposits [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "TokenDepositState.deposits (the (tokenDepositState contracts' address)) =
         Mapping.delete ID (TokenDepositState.deposits (the (tokenDepositState contracts address)))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadBridge [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "TokenDepositState.bridge (the (tokenDepositState contracts' address)) =
         TokenDepositState.bridge (the (tokenDepositState contracts address))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadTokenPairs [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "TokenDepositState.tokenPairs (the (tokenDepositState contracts' address)) =
         TokenDepositState.tokenPairs (the (tokenDepositState contracts address))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadProofVerifier [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "TokenDepositState.proofVerifier (the (tokenDepositState contracts' address)) =
         TokenDepositState.proofVerifier (the (tokenDepositState contracts address))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

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

lemma callCancelDepositOtherToken [simp]:
  assumes "token' \<noteq> token"
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadInDeadState:
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 
         deadState (the (tokenDepositState contracts tokenDepositAddress))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (cases "address = tokenDepositAddress")
     (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositDeadStateRemainsSet:
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
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
    using callCancelDepositDeadStateRemainsSet
    by blast
qed

lemma callCancelDepositWhileDeadSetsDeadState:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  assumes "\<not> bridgeDead contracts tokenDepositAddress"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 
         getLastStateTD contracts tokenDepositAddress"
  using assms getDeadStatusSetsDeadState
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDead_balanceOfSender:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  shows "balanceOf (the (ERC20state contracts' token)) (sender msg) =
         balanceOf (the (ERC20state contracts token)) (sender msg) + amount"
  using assms
  using safeTransferFromBalanceOfTo[of "the (ERC20state contracts' token)" "the (ERC20state contracts token)" tokenDepositAddress "sender msg" amount]
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDead_balanceOfContract:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  shows 
    "balanceOf (the (ERC20state contracts token)) tokenDepositAddress \<ge> amount"
    "balanceOf (the (ERC20state contracts' token)) tokenDepositAddress =
     balanceOf (the (ERC20state contracts token)) tokenDepositAddress - amount"
  using assms
  using safeTransferFromBalanceOfCaller[of "the (ERC20state contracts' token)" "the (ERC20state contracts token)" tokenDepositAddress "sender msg" amount]
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDead_balanceOfOther:
  assumes "address' \<noteq> address" "address' \<noteq> sender msg"
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof =
           (Success, contracts')"
  shows "balanceOf (the (ERC20state contracts' token)) address' =
         balanceOf (the (ERC20state contracts token)) address'"
  using assms 
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadTokenWithdrawn [simp]:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "tokenWithdrawn ((the (tokenDepositState contracts' address'))) = 
         tokenWithdrawn ((the (tokenDepositState contracts address')))"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (cases "address = address'", auto simp add: Let_def split: option.splits prod.splits if_split_asm)
end


context StrongHashProofVerifier
begin

lemma callCancelDepositWhileDeadGetDepositNonzero:
  assumes "callCancelDepositWhileDead contracts address msg block ID token amount proof = (Success, contracts')"
  shows "getDeposit (the (tokenDepositState contracts address)) ID \<noteq> 0"
  using assms hash3_nonzero[of "sender msg" token amount]
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def Let_def
  by (auto split: option.splits prod.splits if_split_asm)

end

context HashProofVerifier
begin

lemma callCancelDepositWhileDeadCallVerifyClaimProof:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  shows "let stateTokenDeposit = the (tokenDepositState contracts tokenDepositAddress);
             stateRoot = snd (lastValidState contracts stateTokenDeposit)
          in callVerifyClaimProof contracts (TokenDepositState.proofVerifier stateTokenDeposit) (bridge stateTokenDeposit) ID
             stateRoot proof = Success"
  using assms
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callCancelDepositWhileDeadVerifyClaimProof:
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof =
           (Success, contracts')"
  shows "let stateTokenDeposit = the (tokenDepositState contracts tokenDepositAddress);
             stateRoot = snd (lastValidState contracts stateTokenDeposit)
          in verifyClaimProof () (bridge stateTokenDeposit) ID stateRoot proof = True"
  by (smt (verit, best) Status.simps(3) assms callCancelDepositWhileDeadCallVerifyClaimProof callVerifyClaimProof_def old.unit.exhaust option.case_eq_if)

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
  assumes "address \<noteq> address'"
          "callWithdrawWhileDead contracts address' msg block token amount proof = (status, contracts')"
  shows "tokenDepositState contracts' address = tokenDepositState contracts address"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadStateOracle [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "TokenDepositState.stateOracle (the (tokenDepositState contracts' address)) =
         TokenDepositState.stateOracle (the (tokenDepositState contracts address))"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)


lemma callWithdrawWhileDeadBridge [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "TokenDepositState.bridge (the (tokenDepositState contracts' address)) =
         TokenDepositState.bridge (the (tokenDepositState contracts address))"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadTokenPairs [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "TokenDepositState.tokenPairs (the (tokenDepositState contracts' address)) =
         TokenDepositState.tokenPairs (the (tokenDepositState contracts address))"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadDeposits [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "TokenDepositState.deposits (the (tokenDepositState contracts' address)) =
         TokenDepositState.deposits (the (tokenDepositState contracts address))"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadProofVerifier [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "TokenDepositState.proofVerifier (the (tokenDepositState contracts' address)) =
         TokenDepositState.proofVerifier (the (tokenDepositState contracts address))"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadERC20state:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "ERC20state contracts token \<noteq> None" and "ERC20state contracts' token \<noteq> None"
  using assms callSafeTransferFromERC20state
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadOtherToken [simp]:
  assumes "token' \<noteq> token"
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadTokenWithdrawn [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "getTokenWithdrawn (the (tokenDepositState contracts' address)) (hash2 (sender msg) token) = True"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def lookupBool_def lookup_default_update split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadNotTokenWithdrawn [simp]:
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "getTokenWithdrawn (the (tokenDepositState contracts address)) (hash2 (sender msg) token) = False"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def lookupBool_def lookup_default_update split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDead_balanceOfSender:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  shows "balanceOf (the (ERC20state contracts' token)) (sender msg) =
         balanceOf (the (ERC20state contracts token)) (sender msg) + amount"
  using assms
  using safeTransferFromBalanceOfTo[of "the (ERC20state contracts' token)" "the (ERC20state contracts token)" tokenDepositAddress "sender msg" amount]
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDead_balanceOfContract:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  shows 
    "balanceOf (the (ERC20state contracts token)) tokenDepositAddress \<ge> amount"
    "balanceOf (the (ERC20state contracts' token)) tokenDepositAddress =
     balanceOf (the (ERC20state contracts token)) tokenDepositAddress - amount"
  using assms
  using safeTransferFromBalanceOfCaller[of "the (ERC20state contracts' token)" "the (ERC20state contracts token)" tokenDepositAddress "sender msg" amount]
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDead_balanceOfOther:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  assumes "address \<noteq> tokenDepositAddress" "address \<noteq> sender msg"
  shows "balanceOf (the (ERC20state contracts' token)) address =
         balanceOf (the (ERC20state contracts token)) address"
  using assms
  using safeTransferFromBalanceOfOther[of address tokenDepositAddress "sender msg" "the (ERC20state contracts' token)" "the (ERC20state contracts token)" amount, symmetric]
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

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
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 
         deadState (the (tokenDepositState contracts tokenDepositAddress))"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = tokenDepositAddress")
     (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadSetsDeadState:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  assumes "\<not> bridgeDead contracts tokenDepositAddress"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = getLastStateTD contracts tokenDepositAddress"
  using assms getDeadStatusSetsDeadState
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadBridgeDead:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof =
           (Success, contracts')"
  shows "bridgeDead contracts' tokenDepositAddress"
  using assms getDeadStatusTrueDeadState
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadTokenWithdrawn' [simp]:
  assumes "getTokenWithdrawn ((the (tokenDepositState contracts address'))) h = True"
  assumes "callWithdrawWhileDead contracts address msg block token amount proof = (Success, contracts')"
  shows "getTokenWithdrawn ((the (tokenDepositState contracts' address'))) h = True"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def
  by (cases "address = address'", cases "hash2 (sender msg) token = h", auto simp add: Let_def lookupBool_def lookup_default_update' split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadCallVerifyBalanceProof:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof = (Success, contracts')"
  shows "let stateTokenDeposit = the (tokenDepositState contracts tokenDepositAddress);
             stateRoot = snd (lastValidState contracts stateTokenDeposit)
          in callVerifyBalanceProof contracts (TokenDepositState.proofVerifier stateTokenDeposit) token (sender msg) amount
             stateRoot proof = Success"
  using assms
  unfolding callWithdrawWhileDead_def withdrawWhileDead_def getDeadStatus_def lastValidState_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadVerifyBalanceProof:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof = (Success, contracts')"
  shows "let stateTokenDeposit = the (tokenDepositState contracts tokenDepositAddress);
             stateRoot = snd (lastValidState contracts stateTokenDeposit)
          in verifyBalanceProof () token (sender msg) amount stateRoot proof"
  using assms
  by (smt (z3) Status.simps(3) callVerifyBalanceProof_def callWithdrawWhileDeadCallVerifyBalanceProof old.unit.exhaust option.case_eq_if)

end

end