theory TokenPairsState
  imports Main Definition More_Mapping
begin

section \<open>TokenPairs\<close>

lemma callOriginalToMinted:
  assumes "callOriginalToMinted contracts address token = (Success, mintedToken)"
  shows "mintedToken = getMinted (the (tokenPairsState contracts address)) token"
  using assms
  unfolding callOriginalToMinted_def
  by (simp add: Let_def split: option.splits)

text \<open>Sufficient condition for callOriginalToMinted to succeed\<close>
lemma callOriginalToMintedI:
  assumes "tokenPairsState contracts address \<noteq> None" \<comment> \<open>There is a TokenPairs contract on the given address\<close>
  shows "fst (callOriginalToMinted contracts address token) = Success"
  using assms
  unfolding callOriginalToMinted_def Let_def
  by (auto split: option.splits)

end