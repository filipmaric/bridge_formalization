


type_synonym address = nat

(*
locale Token =
  fixes totalSupply  :: "'state \<Rightarrow> nat"
  fixes balanceOf    :: "'state \<Rightarrow> address \<Rightarrow> nat"                             (* balanceOf(account) *)
  fixes transfer     :: "'state \<Rightarrow> address \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> bool \<times> 'state" (* transfer(caller, to, value) *)
  fixes allowance    :: "'state \<Rightarrow> address \<Rightarrow> address \<Rightarrow> nat"                  (* allowance(owner, spender) *)
  fixes approve      :: "'state \<Rightarrow> address \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> bool \<times> 'state" (* approve(caller, spender, value *)
  fixes transferFrom :: "'state \<Rightarrow> address \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> bool \<times> 'state" (* transferFrom(from, to, value) *)
  assumes transfer: 
          "(res, state') = transfer state caller to value \<Longrightarrow> 
           if res then 
             value \<ge> balanceOf state caller \<and>
             balanceOf state' caller = balanceOf state caller - value \<and>
             balanceOf state' to = balenceOf state to + value \<and>
             allowance state' = allowance state
           else
             state' = state"
*)

(* ERC20 tokens *)

(* core implementation *) 
record TokenState = 
  balances' :: "(address, nat) mapping"
  allowances' :: "(address, (address, nat) mapping) mapping"
  totalSupply' :: nat

definition totalSupply :: "TokenState \<Rightarrow> nat" where
  "totalSupply state = totalSupply' state"

definition balanceOf :: "TokenState \<Rightarrow> address \<Rightarrow> nat" where
  "balanceOf state account = (case Mapping.lookup (balances' state) account of 
                                None \<Rightarrow> 0 
                              | Some value \<Rightarrow> value)"


definition transfer_balance :: "address \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> (address, nat) mapping \<Rightarrow> (address, nat) mapping" where
 "transfer_balance from to value balance = Mapping.update from (Mapping.lookup_default 0 balance from - value)
                                          (Mapping.update to (Mapping.lookup_default 0 balance to + value) balance)"

definition transfer :: "TokenState \<Rightarrow> address \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> bool \<times> TokenState" where
 "transfer state caller to amount = 
    (if caller = to then
        (False, state)
     else if balanceOf state caller < amount then 
        (False, state) 
     else
        (True, state \<lparr> balances' := transfer_balance caller to amount (balances' state) \<rparr>))"

definition allowance :: "TokenState \<Rightarrow> address \<Rightarrow> address \<Rightarrow> nat" where
  "allowance state owner spender = 
    (case Mapping.lookup (allowances' state) owner of 
       None \<Rightarrow> 0
     | Some owner_allowances \<Rightarrow> (case Mapping.lookup owner_allowances spender of 
                                   None \<Rightarrow> 0
                                 | Some value \<Rightarrow> value))"

definition updateAllowance :: "address \<Rightarrow> address \<Rightarrow> nat \<Rightarrow>
                               (address, (address, nat) mapping) mapping \<Rightarrow> 
                               (address, (address, nat) mapping) mapping" where
 "updateAllowance owner spender value allowances = 
  (let owner_allowances = Mapping.lookup_default Mapping.empty allowances owner;
        spender_allowance = Mapping.lookup_default 0 owner_allowances spender
     in Mapping.update owner (Mapping.update spender (value + spender_allowance) owner_allowances) allowances)"

definition approve :: "TokenState \<Rightarrow> address \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> bool \<times> TokenState" where
  "approve state owner spender value = (True, state \<lparr> allowances' := updateAllowance owner spender value (allowances' state) \<rparr>)"

definition transferFrom :: "TokenState \<Rightarrow> address \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> bool \<times> TokenState" where
 "transferFrom state from to value =
   (if from = to then
      (False, state) 
    else if allowance state from to < value then 
      (False, state)
    else
      (True, state \<lparr> allowances' := updateAllowance from to (allowance state from to - value) (allowances' state),
                     balances' := Mapping.update from (balanceOf state from - value) 
                                  (Mapping.update to (balanceOf state to + value) (balances' state))\<rparr>)
   )"

(* auxiliary functions *)
definition total_balance :: "(address, nat) mapping \<Rightarrow> nat" where
  "total_balance balances = Sum ((\<lambda> account. the (Mapping.lookup balances account)) ` (Mapping.keys balances))"

(* correctness *)

lemma total_balance_Update:
  shows "total_balance (Mapping.update account value balances) = total_balance balances + value - Mapping.lookup_default 0 balances account"
  unfolding total_balance_def
  apply (auto simp add: Mapping.lookup_default_def)
  sorry

lemma transfer_balance:
  assumes "amount \<le> Mapping.lookup_default 0 balances from" "from \<noteq> to"
  shows "total_balance (transfer_balance from to amount balances) = total_balance balances"
  using assms
  unfolding transfer_balance_def
  by (auto simp add: total_balance_Update lookup_default_def)

lemma transfer:
  assumes "(True, state') = transfer state caller to amount"
  shows "total_balance (balances' state') = total_balance (balances' state)"
proof-
  have "balanceOf state caller \<ge> amount" 
    using assms not_le_imp_less transfer_def
    by (metis prod.inject)
  then have "Mapping.lookup_default 0 (balances' state) caller \<ge> amount"
    unfolding balanceOf_def
    by (simp add: lookup_default_def)
  then show ?thesis
    using transfer_balance[of amount "balances' state" caller to]
    using assms
    by (auto simp add: transfer_def split: if_split_asm)
qed

(* -------------------------------------------- *)

locale SourceBlockchain = 
  fixes addTransaction :: "'state \<Rightarrow> 'transaction \<Rightarrow> 'state"
  fixes containsTransaction :: "'state \<Rightarrow> 'transaction \<Rightarrow> bool"
  fixes getRoot :: "'state \<Rightarrow> 'root \<times> nat" (* root and block height *)
  fixes getTransactionProof :: "'state \<Rightarrow> 'transaction \<Rightarrow> 'proof"
  fixes verifyProof :: "'proof \<Rightarrow> 'root \<Rightarrow> nat \<Rightarrow> bool"
  assumes "let (root, height) = getRoot state
            in verifyProof (getTransactionProof state Tx) root height = True \<longleftrightarrow> 
               containsTransaction state Tx"













locale StateOracle = 
  fixes isDead :: "'state \<Rightarrow> bool" 
  fixes lastState :: "'state \<Rightarrow> nat"

locale ProofVerifier = 
  fixes isDead :: "'state \<Rightarrow> bool"
  fixes verifyProof :: "'state \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" (* verifyProof contractAddress slotIndex expectedValue proof *)

locale Deposit = 
  fixes deposits :: "nat \<Rightarrow> nat"
  fixes claims :: "nat \<Rightarrow> bool"
  fixes tokenWithdrawn :: "nat \<Rightarrow> bool"

  fixes bridge :: "address"
  fixes proofVerifier :: "address"

locale Bridge =
  fixes withdrawals :: "nat \<Rightarrow> nat"
  fixes claims :: "nat \<Rightarrow> bool"

