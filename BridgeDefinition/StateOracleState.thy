theory StateOracleState
  imports Main Definition
begin

section \<open>StateOracle\<close>

subsection \<open>lastState\<close>

abbreviation lastStateSO where
   "lastStateSO contracts stateOracleAddress \<equiv> StateOracleState.lastState (the (stateOracleState contracts stateOracleAddress))"

lemma callLastState:
  assumes "callLastState contracts stateOracleAddress = (Success, state)"
  shows "state = lastStateSO contracts stateOracleAddress"
  using assms
  unfolding callLastState_def
  by (simp split: option.splits)

text \<open>Sufficient condtion for callLastState to succeed\<close>
lemma callLastStateI:
  assumes "stateOracleState contracts address \<noteq> None" \<comment> \<open>There is a state oracle on the give address\<close>
  shows "fst (callLastState contracts address) = Success"
  using assms
  unfolding callLastState_def
  by (auto split: option.splits)

text \<open>lastUpdateTime\<close>

lemma callLastUpdateTimeI:
  assumes "stateOracleState contracts (stateOracleAddressTD contracts address) \<noteq> None"
  shows "fst (callLastUpdateTime contracts (stateOracleAddressTD contracts address)) = Success"
  using assms
  unfolding callLastUpdateTime_def
  by (simp split: option.splits)


subsection \<open>update\<close>

lemma callUpdateLastState:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "lastStateSO contracts' address = stateRoot"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateStateOracleState:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "stateOracleState contracts address \<noteq> None" and
        "stateOracleState contracts' address \<noteq> None"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateIBridge [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "IBridge contracts' = IBridge contracts"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateITokenDeposit [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "ITokenDeposit contracts' = ITokenDeposit contracts"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateIERC20 [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "IERC20 contracts' =  IERC20 contracts"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateITokenPairs [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "ITokenPairs contracts' =  ITokenPairs contracts"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateIProofVerifier [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateDeadState [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "deadStateTD contracts' tokenDepositAddress = 
         deadStateTD contracts tokenDepositAddress"
  using assms
  unfolding callUpdate_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateOtherAddress:
  assumes "address' \<noteq> address"
  assumes "callUpdate contracts address' block blockNum stateRoot = (Success, contracts')"
  shows "stateOracleState contracts' address = stateOracleState contracts address"
  using assms
  unfolding callUpdate_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateLastValidStateTD [simp]:
  assumes "address' \<noteq> stateOracleAddressTD contracts tokenDepositAddress"
  assumes "callUpdate contracts address' block blockNum stateRoot = (Success, contracts')"
  shows "lastValidStateTD contracts' tokenDepositAddress = 
         lastValidStateTD contracts tokenDepositAddress"
  using assms
  using callLastState_def callUpdateITokenDeposit callUpdateOtherAddress lastValidState_def 
  by presburger

lemma callUpdateBridgeNotDeadLastValidState:
  assumes "callUpdate contracts (stateOracleAddressTD contracts address) block blockNum stateRoot = (Success, contracts')"
  assumes "\<not> bridgeDead contracts address"
  shows "snd (lastValidStateTD contracts' address) = stateRoot"
  using assms
  by (metis callLastState callLastStateI callUpdateITokenDeposit callUpdateLastState callUpdateStateOracleState(2) lastValidState_def surjective_pairing)

lemma callUpdateFiniteBalances:
  assumes "finiteBalances contracts token'"
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "finiteBalances contracts' token'"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def finiteBalances_def split: option.splits prod.splits if_split_asm)

lemma callUpdateStateRootNonZero:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "stateRoot \<noteq> 0"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

end
