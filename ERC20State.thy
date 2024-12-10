theory ERC20State
  imports Definition More_Mapping
begin
section \<open>IERC20\<close>

subsection \<open>callBalanceOf\<close>

lemma callBalanceOf [simp]:
  assumes "callBalanceOf contracts token account = (Success, balance)"
  shows "accountBalance contracts token account = balance"
  using assms
  unfolding callBalanceOf_def
  by (simp add: Let_def split: option.splits)

lemma callBalanceOfERC20state:
  assumes "callBalanceOf contracts token account = (Success, balance)"
  shows "ERC20state contracts token \<noteq> None"
  using assms
  unfolding callBalanceOf_def
  by (auto simp add: Let_def split: option.splits)

lemma callBalanceOfI:
  assumes "ERC20state contracts token \<noteq> None"
  shows "fst (callBalanceOf contracts token account) = Success"
  unfolding callBalanceOf_def
  using assms
  by (auto split: option.splits)

subsection \<open>setBalance, addToBalance, removeFromBalance, transferBalance\<close>

lemma setBalanceBalanceOf [simp]:
  shows "balanceOf (setBalance state account amount) account = amount"
  unfolding balanceOf_def
  by (simp add: lookup_def lookup_default_update')

lemma setBalanceBalanceOfOther [simp]:
  assumes "other \<noteq> account"
  shows "balanceOf (setBalance state account amount) other = 
         balanceOf state other"
  using assms
  unfolding balanceOf_def
  by (simp add: lookup_def lookup_default_update')

lemma addToBalanceBalanceOf [simp]:
  shows "balanceOf (addToBalance state account amount) account = 
         balanceOf state account + amount"
  unfolding balanceOf_def addToBalance_def
  by (simp add: lookup_def lookup_default_update')

lemma addToBalanceBalanceOfOther [simp]:
  assumes "other \<noteq> account"
  shows "balanceOf (addToBalance state account amount) other = 
         balanceOf state other"
  using assms
  unfolding balanceOf_def addToBalance_def
  by (simp add: lookup_def lookup_default_update')

lemma removeFromBalanceBalanceOf [simp]:
  assumes "amount \<le> balanceOf state account"
  shows "balanceOf (removeFromBalance state account amount) account = 
         balanceOf state account - amount"
  using assms
  unfolding balanceOf_def removeFromBalance_def
  by (simp add: lookup_def lookup_default_update')

lemma removeFromBalanceBalanceOfOther [simp]:
  assumes "other \<noteq> account"
  shows "balanceOf (removeFromBalance state account amount) other = 
         balanceOf state other"
  using assms
  unfolding balanceOf_def removeFromBalance_def
  by (simp add: lookup_def lookup_default_update')

lemma transferBalanceBalanceOfTo [simp]:
  assumes "from \<noteq> to" "amount \<le> balanceOf state from"
  shows "balanceOf (transferBalance state from to amount) from = 
         balanceOf state from - amount"
  using assms
  unfolding transferBalance_def
  by simp

lemma transferBalanceBalanceOfFrom [simp]:
  assumes "from \<noteq> to" "amount \<le> balanceOf state from"
  shows "balanceOf (transferBalance state from to amount) to = 
         balanceOf state to + amount"
  using assms
  unfolding transferBalance_def
  by simp

lemma transferBalanceBalanceOfOther [simp]:
  assumes "from \<noteq> to" "other \<noteq> from" "other \<noteq> to" "amount \<le> balanceOf state from"
  shows "balanceOf (transferBalance state from to amount) other = 
         balanceOf state other"
  using assms
  unfolding transferBalance_def
  by simp

subsection \<open>safeTransferFrom\<close>

lemma safeTransferFromFail [simp]:
  assumes "safeTransferFrom state caller to amount = (Fail str, state')"
  shows "state' = state"
  using assms
  unfolding safeTransferFrom_def
  by (simp split: if_split_asm)

lemma callSafeTransferFromFail [simp]:
  assumes "callSafeTransferFrom contracts address caller to amount = (Fail str, contracts')"
  shows "contracts' = contracts"
  using assms
  unfolding callSafeTransferFrom_def
  by (simp split: option.splits prod.splits if_split_asm)

lemma safeTransferFromBalanceOfTo:
  assumes "(Success, state') = safeTransferFrom state caller to amount" 
  shows "balanceOf state' to =
         balanceOf state to + amount"
  using assms
  unfolding safeTransferFrom_def
  by (simp split: if_split_asm)

lemma safeTransferFromBalanceOfCaller:
  assumes "(Success, state') = safeTransferFrom state caller to amount" 
  shows "balanceOf state caller \<ge> amount" 
        "balanceOf state' caller =
         balanceOf state caller - amount"
  using assms
  unfolding safeTransferFrom_def
  by (auto split: if_split_asm)

lemma safeTransferFromBalanceOfOther:
  assumes "other \<noteq> caller" "other \<noteq> to" 
  assumes "(Success, state') = safeTransferFrom state caller to amount" 
  shows "balanceOf state' other =
         balanceOf state other"
  using assms
  unfolding safeTransferFrom_def
  by (simp split: if_split_asm)

lemma callSafeTransferFromBalanceOfTo:
  assumes "callBalanceOf contracts token to = (Success, balanceBefore)"
  assumes "callSafeTransferFrom contracts token caller to amount = (Success, contracts')"
  assumes "callBalanceOf contracts' token to = (Success, balanceAfter)"
  shows "balanceAfter = balanceBefore + amount"
  using assms
  using safeTransferFromBalanceOfTo[where caller="caller" and to="to" and amount="amount", symmetric]
  unfolding callBalanceOf_def callSafeTransferFrom_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)
  
lemma callSafeTransferFromBalanceOfTo':
  assumes "callBalanceOf contracts token to = (Success, balanceBefore)"
  assumes "callSafeTransferFrom contracts token caller to amount = (Success, contracts')"
  assumes "callBalanceOf contracts' token to = (Success, balanceAfter)"
  shows "balanceAfter - balanceBefore = amount"
  by (metis add_diff_cancel_left' assms callSafeTransferFromBalanceOfTo)

lemma callSafeTransferFromBalanceOfOther [simp]:
  assumes "address' \<noteq> caller" "address' \<noteq> to"
  assumes "callSafeTransferFrom contracts token caller to amount = (Success, contracts')"
  shows "accountBalance contracts' token address' = 
         accountBalance contracts token address'"
  using assms safeTransferFromBalanceOfOther[of address' caller to "the (ERC20state contracts' token)" "the (ERC20state contracts token)" amount]
  unfolding callSafeTransferFrom_def
  by (auto simp add: Let_def  split: option.splits prod.splits if_split_asm)

lemma callSafeTransferFromITokenPairs [simp]:
  assumes "callSafeTransferFrom contracts token caller to amount = (status, contracts')"
  shows "ITokenPairs contracts = ITokenPairs contracts'"
  using assms
  unfolding callSafeTransferFrom_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma callSafeTransferFromITokenDeposit [simp]:
  assumes "callSafeTransferFrom contracts token caller to amount = (status, contracts')"
  shows "ITokenDeposit contracts = ITokenDeposit contracts'"
  using assms
  unfolding callSafeTransferFrom_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma callSafeTransferFromIBridge [simp]:
  assumes "callSafeTransferFrom contracts token caller to amount = (status, contracts')"
  shows "IBridge contracts = IBridge contracts'"
  using assms
  unfolding callSafeTransferFrom_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma callSafeTransferFromIProofVerifier [simp]:
  assumes "callSafeTransferFrom contracts token caller to amount = (status, contracts')"
  shows "IProofVerifier contracts = IProofVerifier contracts'"
  using assms
  unfolding callSafeTransferFrom_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma callSafeTransferFromIStateOracle [simp]: 
  assumes "callSafeTransferFrom contracts token caller address amount = (Success, contracts')"
  shows "IStateOracle contracts = IStateOracle contracts'"
  using assms
  unfolding callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callSafeTransferFromERC20state:
  assumes "callSafeTransferFrom contracts token caller address account = (Success, contracts')"
  shows "ERC20state contracts token \<noteq> None" "ERC20state contracts' token \<noteq> None"
  using assms
  unfolding callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

text \<open>transferring does not affect other tokens\<close>
lemma callSafeTransferFromOtherToken [simp]: 
  assumes "token' \<noteq> token"
          "callSafeTransferFrom contracts token caller to amount = (status, contracts')"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms
  unfolding callSafeTransferFrom_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

text \<open>Sufficient condition for callTransferFrom to succeed\<close>
lemma callSafeTransferFromI:
  assumes "ERC20state contracts address = Some state"
  assumes "balanceOf state caller \<ge> amount"
  assumes "caller \<noteq> receiver" 
  shows "fst (callSafeTransferFrom contracts address caller receiver amount) = Success"
  using assms
  unfolding callSafeTransferFrom_def safeTransferFrom_def
  by (auto split: option.splits prod.splits)

subsection \<open>mint\<close>

lemma mintBalanceOf [simp]:
  assumes "mint state account amount = state'"
  shows "balanceOf state' account = balanceOf state account + amount"
  using assms
  unfolding mint_def
  by auto

lemma mintBalanceOfOther [simp]:
  assumes "other \<noteq> account" "mint state account amount = state'"
  shows "balanceOf state' other = balanceOf state other"
  using assms
  unfolding mint_def
  by auto

lemma callMintBalanceOf [simp]:
  assumes "callMint contracts mintedToken account amount = (Success, contracts')"
  shows "accountBalance contracts' mintedToken account =
         accountBalance contracts mintedToken account + amount"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: option.splits)

lemma callMintBalanceOfOther [simp]:
  assumes "other \<noteq> account"
  assumes "callMint contracts mintedToken account amount = (Success, contracts')"
  shows "accountBalance contracts' mintedToken other = 
         accountBalance contracts mintedToken other"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: option.splits)

lemma callMintITokenPairs [simp]:
  assumes "callMint contracts mintedToken account amount = (Success, contracts')"
  shows "ITokenPairs contracts = ITokenPairs contracts'"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma callMintITokenDeposit [simp]:
  assumes "callMint contracts mintedToken account amount = (Success, contracts')"
  shows "ITokenDeposit contracts = ITokenDeposit contracts'"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma callMintIBridge [simp]:
  assumes "callMint contracts mintedToken account amount = (Success, contracts')"
  shows "IBridge contracts = IBridge contracts'"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma callMintIProofVerifier [simp]:
  assumes "callMint contracts mintedToken account amount = (Success, contracts')"
  shows "IProofVerifier contracts = IProofVerifier contracts'"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm)

lemma callMintIStateOracle [simp]: 
  assumes "callMint contracts token (sender msg) amount = (Success, contracts')"
  shows "IStateOracle contracts = IStateOracle contracts'"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callMintERC20state:
  assumes "callMint contracts token caller amount = (Success, contracts')"
  shows "ERC20state contracts token \<noteq> None" and "ERC20state contracts' token \<noteq> None"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

text \<open>minting does not affect other tokens\<close>
lemma callMintOtherToken [simp]: 
  assumes "token' \<noteq> token"
          "callMint contracts token caller amount = (status, contracts')"
  shows "ERC20state contracts' token' = ERC20state contracts token'"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

text \<open>Sufficient condition for callMint to succeed\<close>
lemma callMintI: 
  assumes "ERC20state contracts mintedToken \<noteq> None" \<comment> \<open>minted token contract exists\<close>
  shows "fst (callMint contracts mintedToken (sender msg) amount) = Success"
  using assms
  unfolding callMint_def
  by (auto split: option.splits)

subsection \<open>Total balance of a state\<close>

definition totalBalance :: "ERC20State \<Rightarrow> nat" where
  "totalBalance state = mapping_value_sum (balances state)"

abbreviation totalTokenBalance :: "Contracts \<Rightarrow> address \<Rightarrow> nat" where
  "totalTokenBalance contracts token \<equiv>
   totalBalance (the (ERC20state contracts token))"

lemma totalBalance_addToBalance [simp]:
  assumes "finite (Mapping.keys (balances state))"
  shows "totalBalance (addToBalance state caller amount) = totalBalance state + amount"
  using assms
  unfolding totalBalance_def addToBalance_def
  by simp

lemma callMint_total_balance [simp]:
  assumes "finite (Mapping.keys (balances ((the (ERC20state contracts token)))))"
  assumes "callMint contracts token caller amount = (Success, contracts')"
  shows "totalTokenBalance contracts' token = 
         totalTokenBalance contracts token + amount"
  using assms
  unfolding callMint_def mint_def
  by (auto simp add: Let_def split: option.splits)

end