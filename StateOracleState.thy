theory StateOracleState
  imports Main Definition
begin

section \<open>StateOracle\<close>

subsection \<open>lastState\<close>

lemma callLastState [simp]:
  assumes "callLastState contracts address = (Success, state)"
  shows "state = StateOracleState.lastState (the (stateOracleState contracts address))"
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

lemma callUpdateLastState [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "StateOracleState.lastState (the (stateOracleState contracts' address)) = stateRoot"
  using assms
  unfolding callUpdate_def update_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateStateOracleState [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "stateOracleState contracts address \<noteq> None" and "stateOracleState contracts' address \<noteq> None"
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
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 
         deadState (the (tokenDepositState contracts tokenDepositAddress))"
  using assms
  unfolding callUpdate_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callUpdateOtherAddress:
  assumes "address' \<noteq> address"
  assumes "callUpdate contracts address' block blockNum stateRoot = (Success, contracts')"
  shows "stateOracleState contracts address = stateOracleState contracts' address"
  using assms
  unfolding callUpdate_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callWithdrawWhileDeadGetLastValidStateTD [simp]:
  assumes "address' \<noteq> stateOracleAddressTD contracts tokenDepositAddress"
  assumes "callUpdate contracts address' block blockNum stateRoot = (Success, contracts')"
  shows "getLastValidStateTD contracts' tokenDepositAddress = 
         getLastValidStateTD contracts tokenDepositAddress"
  using assms
  using callLastState_def callUpdateITokenDeposit callUpdateOtherAddress lastValidState_def 
  by presburger

end