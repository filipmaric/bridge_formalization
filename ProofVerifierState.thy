theory ProofVerifierState
   imports Main Definition
begin

context ProofVerifier
begin

section \<open>ProofVerifier\<close>

text \<open>Sufficient condition for a callVerifyProof to succeed\<close>
lemma callVerifyDepositProofI:
  assumes "proofVerifierState contracts address \<noteq> None"
  assumes "verifyDepositProof () contractAddress stateRoot proof ID hsh"
  shows "callVerifyDepositProof contracts address contractAddress stateRoot proof ID hsh = Success"
  using assms
  unfolding callVerifyDepositProof_def
  by (auto split: option.splits)

end

end