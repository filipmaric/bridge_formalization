theory Bridge
  imports Main "HOL-Library.Mapping"
begin

text \<open>Solidity mappings assign default values to unexisting keys\<close>
definition lookupNat :: "('a, nat) mapping \<Rightarrow> 'a \<Rightarrow> nat" where
  "lookupNat m x = Mapping.lookup_default 0 m x"
definition lookupBool :: "('a, bool) mapping \<Rightarrow> 'a \<Rightarrow> bool" where
  "lookupBool m x = Mapping.lookup_default False m x"

type_synonym address = nat
type_synonym uint256 = nat
type_synonym bytes32 = nat
type_synonym bytes = "nat list"

datatype Status = 
  Success | Fail string

record Block = 
  timestamp :: uint256

record Message =
  sender :: address
  val :: uint256

section \<open>ERC20\<close>

record ERC20State = 
  balances :: "(address, uint256) mapping"
(*  
  allowances :: "(address, (address, uint256) mapping) mapping"
  totalSupply :: nat 
*)

section \<open>State oracle\<close>

record Validator = 
   addr :: address
   weight :: uint256

record L1StateOracleState = 
   lastState :: bytes32
   lastBlockNum :: uint256
   lastUpdateTime :: uint256
   chainId :: uint256

record L2StateOracleState = 
   lastState :: bytes32
   lastBlockNum :: uint256
   lastUpdateTime :: uint256

section \<open>Token pairs\<close>

record TokenPairsState = 
   originalToMinted :: "(address, address) mapping"
   mintedToOriginal :: "(address, address) mapping"

section \<open>Token deposit\<close>

record TokenDepositState = 
   deposits :: "(uint256, bytes32) mapping"
   claims :: "(uint256, bool) mapping"
   tokenWithdrawn :: "(bytes32, bool) mapping"
   proofVerifier :: address
   bridge :: address
   tokenPairs :: address
   stateOracle :: address
   deadState :: bytes32

definition TIME_UNTIL_DEAD :: nat where
  "TIME_UNTIL_DEAD = 7 * 24 * 60 * 60" 

text \<open>Bridge\<close>

record BridgeState =
  withdrawals :: "(uint256, bytes32) mapping"
  claims :: "(uint256, bool) mapping"
  proofVerifier :: address
  deposit :: address
  tokenPairs :: address
  stateOracle :: address

text \<open>ProofVerifier\<close>
\<comment> \<open>it has no state\<close>
type_synonym ProofVerifierState = unit

text \<open>Blokchain maps adresses to contract states. We have to keep a separate mapping for each type \<close>
record Contracts = 
  IERC20 :: "(address, ERC20State) mapping"
  IStateOracle :: "(address, L1StateOracleState) mapping"
  ITokenPairs :: "(address, TokenPairsState) mapping"
  ITokenDeposit :: "(address, TokenDepositState) mapping"
  IBridge :: "(address, BridgeState) mapping"
  IProofVerifier :: "(address, ProofVerifierState) mapping" (* no state *)

abbreviation stateOracleState :: "Contracts \<Rightarrow> address \<Rightarrow> L1StateOracleState option" where
  "stateOracleState contracts address \<equiv> Mapping.lookup (IStateOracle contracts) address"

abbreviation setStateOracleState :: "Contracts \<Rightarrow> address \<Rightarrow> L1StateOracleState \<Rightarrow> Contracts" where
  "setStateOracleState contracts address state \<equiv> 
      contracts \<lparr> IStateOracle := Mapping.update address state (IStateOracle contracts) \<rparr>"

abbreviation ERC20state :: "Contracts \<Rightarrow> address \<Rightarrow> ERC20State option" where
  "ERC20state contracts address \<equiv> Mapping.lookup (IERC20 contracts) address"

abbreviation setERC20State :: "Contracts \<Rightarrow> address \<Rightarrow> ERC20State \<Rightarrow> Contracts" where
  "setERC20State contracts address state \<equiv> 
      contracts \<lparr> IERC20 := Mapping.update address state (IERC20 contracts) \<rparr>"

abbreviation tokenDepositState :: "Contracts \<Rightarrow> address \<Rightarrow> TokenDepositState option"  where
  "tokenDepositState contracts address \<equiv> Mapping.lookup (ITokenDeposit contracts) address"

abbreviation setTokenDepositState :: "Contracts \<Rightarrow> address \<Rightarrow> TokenDepositState \<Rightarrow> Contracts" where
  "setTokenDepositState contracts address state \<equiv> 
      contracts \<lparr> ITokenDeposit := Mapping.update address state (ITokenDeposit contracts) \<rparr>"

abbreviation bridgeState :: "Contracts \<Rightarrow> address \<Rightarrow> BridgeState option"  where
  "bridgeState contracts address \<equiv> Mapping.lookup (IBridge contracts) address"

abbreviation setBridgeState :: "Contracts \<Rightarrow> address \<Rightarrow> BridgeState \<Rightarrow> Contracts" where
  "setBridgeState contracts address state \<equiv> 
      contracts \<lparr> IBridge := Mapping.update address state (IBridge contracts) \<rparr>"

abbreviation tokenPairsState :: "Contracts \<Rightarrow> address \<Rightarrow> TokenPairsState option"  where
  "tokenPairsState contracts address \<equiv> Mapping.lookup (ITokenPairs contracts) address"

abbreviation setTokenPairsState :: "Contracts \<Rightarrow> address \<Rightarrow> TokenPairsState \<Rightarrow> Contracts" where
  "setTokenPairsState contracts address state \<equiv> 
      contracts \<lparr> ITokenPairs := Mapping.update address state (ITokenPairs contracts) \<rparr>"

abbreviation proofVerifierState :: "Contracts \<Rightarrow> address \<Rightarrow> ProofVerifierState option"  where
  "proofVerifierState contracts address \<equiv> Mapping.lookup (IProofVerifier contracts) address"

abbreviation setProofVerifierState :: "Contracts \<Rightarrow> address \<Rightarrow> ProofVerifierState \<Rightarrow> Contracts" where
  "setProofVerifierState contracts address state \<equiv> 
      contracts \<lparr> IProofVerifier := Mapping.update address state (IProofVerifier contracts) \<rparr>"

section \<open>IERC20\<close>
 
definition ERC20Constructor :: ERC20State where 
  "ERC20Constructor = \<lparr> balances = Mapping.empty \<rparr>"

(* read only *)
text \<open>read token balance of a given address\<close>
definition balanceOf :: "ERC20State \<Rightarrow> address \<Rightarrow> uint256" where
  "balanceOf state account = lookupNat (balances state) account"

text \<open>Call via contract address\<close>
definition callBalanceOf :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> Status \<times> uint256" where
  "callBalanceOf contracts address account = 
    (case ERC20state contracts address of 
           None \<Rightarrow>
             (Fail ''wrong address'', 0)
         | Some state \<Rightarrow> 
             (Success, balanceOf state account ))"

(* private helper functions *)
abbreviation setBalance :: "ERC20State \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> ERC20State" where
  "setBalance state account amount \<equiv>
      state \<lparr> balances := Mapping.update account amount (balances state) \<rparr>"

definition addToBalance :: "ERC20State \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> ERC20State" where
  "addToBalance state account amount = 
      setBalance state account (lookupNat (balances state) account + amount)"

definition removeFromBalance :: "ERC20State \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> ERC20State" where
  "removeFromBalance state account amount = 
      setBalance state account (lookupNat (balances state) account - amount)"

definition transferBalance :: "ERC20State \<Rightarrow> address \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> ERC20State" where
  "transferBalance state from to amount = 
    addToBalance (removeFromBalance state from amount) to amount"

text \<open>Transfer given amount of tokens from the caller to the receiver \<close>
definition safeTransferFrom :: "ERC20State \<Rightarrow> address \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> Status \<times> ERC20State" where
 "safeTransferFrom state caller receiver amount = 
    (if caller = receiver then
        (Fail ''Sender and reciever must not be equal'', state)
     else if balanceOf state caller < amount then 
        (Fail ''Insufficient balance'', state) 
     else
        (Success, transferBalance state caller receiver amount))"

text \<open>Call via contract address\<close>
definition callSafeTransferFrom :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> Status \<times> Contracts" where
  "callSafeTransferFrom contracts address caller receiver amount = 
    (case ERC20state contracts address of 
            None \<Rightarrow>
               (Fail ''wrong address'', contracts)
          | Some state \<Rightarrow> 
               let (status, state') = safeTransferFrom state caller receiver amount 
                in if status \<noteq> Success then 
                      (status, contracts)
                   else
                      (Success, setERC20State contracts address state')
    )"

text \<open>Mint the given amount of tokens and assign them to the caller \<close>
definition mint :: "ERC20State \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> ERC20State" where
  "mint state caller amount = addToBalance state caller amount"

text \<open>Call via contract address\<close>
definition callMint :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> Status \<times> Contracts" where
  "callMint contracts address caller amount = 
    (case ERC20state contracts address of
            None \<Rightarrow>
               (Fail ''wrong address'', contracts)
          | Some state \<Rightarrow> 
               (Success, setERC20State contracts address (mint state caller amount)))"

section \<open>TokenPairs\<close>

definition TokenPairsConstructor :: TokenPairsState where
  "TokenPairsConstructor =
      \<lparr> originalToMinted = Mapping.empty,
        mintedToOriginal = Mapping.empty \<rparr>"

definition addTokenPair :: "TokenPairsState \<Rightarrow> address \<Rightarrow> address \<Rightarrow> TokenPairsState" where
  "addTokenPair state original minted = 
     state \<lparr> originalToMinted := Mapping.update original minted (originalToMinted state), 
             mintedToOriginal := Mapping.update minted original (mintedToOriginal state)\<rparr>"

section \<open>State oracle\<close>

definition L1StateOracleConstructor :: "uint256 \<Rightarrow> Validator list \<Rightarrow> L1StateOracleState" where
  "L1StateOracleConstructor chainId' validators = 
      \<lparr> L1StateOracleState.lastState = 0, 
        L1StateOracleState.lastBlockNum = 0, 
        L1StateOracleState.lastUpdateTime = 0, 
        L1StateOracleState.chainId = chainId' \<rparr>"

text \<open>Read the last known state root\<close>
text \<open>Call via contract address\<close>
definition callLastState :: "Contracts \<Rightarrow> address \<Rightarrow> Status \<times> bytes32" where
  "callLastState contracts address = 
     (case stateOracleState contracts address of
           None \<Rightarrow> 
             (Fail ''wrong address'', 0)
         | Some state \<Rightarrow> 
             (Success, L1StateOracleState.lastState state))"

text \<open>Call via contract address\<close>
definition callLastUpdateTime :: "Contracts \<Rightarrow> address \<Rightarrow> Status \<times> bytes32" where
  "callLastUpdateTime contracts address = 
     (case stateOracleState contracts address of
          None \<Rightarrow> 
             (Fail ''wrong address'', 0)
        | Some state \<Rightarrow> 
             (Success, L1StateOracleState.lastUpdateTime state))"

text \<open>Update the state oracle by giving it the info about the last known block (its blockNum and stateRoot are known) \<close>
definition update :: "L1StateOracleState \<Rightarrow> Block \<Rightarrow> uint256 \<Rightarrow> bytes32 \<Rightarrow> Status \<times> L1StateOracleState" where
  "update state block blockNum stateRoot = 
   (if blockNum \<le> L1StateOracleState.lastBlockNum state then 
       (Fail ''Replay of old signed state'', state)
    else
       (Success, state \<lparr> L1StateOracleState.lastState := stateRoot, 
                         L1StateOracleState.lastUpdateTime := timestamp block,
                         L1StateOracleState.lastBlockNum := blockNum \<rparr>))"

text \<open>Call via contract address\<close>
definition callUpdate where
  "callUpdate contracts address block blockNum stateRoot = 
    (let state_opt = Mapping.lookup (IStateOracle contracts) address 
      in case state_opt of 
           None \<Rightarrow> (Fail ''wrong address'', contracts)
         | Some state \<Rightarrow> 
             let (status, state') = update state block blockNum stateRoot
              in if status \<noteq> Success then 
                     (status, contracts)
                 else
                     (Success, setStateOracleState contracts address state'))"

section \<open>Token deposit\<close>

definition TokenDepositConstructor :: "address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> TokenDepositState" where
  "TokenDepositConstructor proofVerifier' bridge' tokenPairs' stateOracle' = 
      \<lparr> deposits = Mapping.empty,
        claims = Mapping.empty,
        tokenWithdrawn = Mapping.empty,
        proofVerifier = proofVerifier',
        bridge = bridge',
        tokenPairs = tokenPairs',
        stateOracle = stateOracle',
        deadState = 0 \<rparr>"

(* always succeeds, but has a side effect *)
definition getIsDead :: "Contracts \<Rightarrow> TokenDepositState \<Rightarrow> Block \<Rightarrow> Status \<times> bool \<times> TokenDepositState" where
 "getIsDead contracts state block = 
      (if deadState state \<noteq> 0 then
          (Success, True, state)
       else
          let (status, lastUpdateTime) = callLastUpdateTime contracts (TokenDepositState.stateOracle state)
           in if status \<noteq> Success then 
                 (status, False, state) 
              else if lastUpdateTime \<noteq> 0 \<and> lastUpdateTime < (timestamp block) then 
                 let (status, lastState) = callLastState contracts (TokenDepositState.stateOracle state)
                  in if status \<noteq> Success then
                        (status, False, state)
                     else 
                        (Success, True, state \<lparr> deadState := lastState \<rparr>) 
              else
                  (Success, False, state)
      )"

definition callOriginalToMinted :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> Status \<times> address" where
  "callOriginalToMinted contracts address token = 
      (let state_opt = Mapping.lookup (ITokenPairs contracts) address
        in case state_opt of None \<Rightarrow> 
              (Fail ''wrong address'', 0)
           | Some state \<Rightarrow> (Success, lookupNat (originalToMinted state) token))"

locale Hash = 
  fixes hash :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

context Hash
begin

abbreviation getDeposit :: "TokenDepositState \<Rightarrow> uint256 \<Rightarrow> bytes32" where
  "getDeposit state ID \<equiv> lookupNat (deposits state) ID"

abbreviation setDeposit :: "TokenDepositState \<Rightarrow> uint256 \<Rightarrow> bytes32 \<Rightarrow> TokenDepositState" where
  "setDeposit state ID v \<equiv> state \<lparr> deposits := Mapping.update ID v (deposits state) \<rparr>"

definition deposit :: "TokenDepositState \<Rightarrow> Contracts  \<Rightarrow> address \<Rightarrow> Block \<Rightarrow> Message \<Rightarrow> uint256 \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> Status \<times> TokenDepositState \<times> Contracts" where
  "deposit state contracts this block msg ID token amount = 
     (let (status, dead, state') = getIsDead contracts state block
       in if status \<noteq> Success then 
             (status, state, contracts)
          else if dead then 
             (Fail ''Bridge is dead - deposits are not possible'', state, contracts)
          else if getDeposit state' ID \<noteq> 0 then
             (Fail ''Deposit id is already used'', state, contracts)
          else let (status, mintedToken) = callOriginalToMinted contracts (TokenDepositState.tokenPairs state') token
                in if status \<noteq> Success then 
                      (status, state, contracts)
                   else if mintedToken = 0 then
                      (Fail ''Not supported token'', state, contracts) 
          else let (status, balanceBefore) = callBalanceOf contracts token this
                in if status \<noteq> Success then
                      (status, state, contracts)
                   else let (status, contracts') = callSafeTransferFrom contracts token (sender msg) this amount
                 in if status \<noteq> Success then 
                        (status, state, contracts)
                    else let (status, balanceAfter) = callBalanceOf contracts' token this
                          in if status \<noteq> Success then
                             (status, state, contracts)
                             else let realAmount = balanceAfter - balanceBefore
                               in if realAmount = 0 then
                                   (Fail ''No tokens were transferred'', state, contracts) 
                               else let state'' = setDeposit state' ID (hash (sender msg) token realAmount) 
                                     in (Success, state'', contracts'))"

definition callDeposit where
  "callDeposit contracts address block msg ID token amount =
    (case tokenDepositState contracts address of
         None \<Rightarrow>
            (Fail ''wrong address'', contracts)
       | Some state \<Rightarrow> 
            let (status, state', contracts') = deposit state contracts address block msg ID token amount
             in if status \<noteq> Success then
                    (status, contracts)
                else
                    (Success, setTokenDepositState contracts' address state'))"

end

text \<open>Bridge\<close>

definition BridgeStateConstructor :: "address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> BridgeState" where
  "BridgeStateConstructor proofVerifier' tokenPairs' stateOracle' = 
        \<lparr> withdrawals = Mapping.empty,
          claims = Mapping.empty, 
          proofVerifier = proofVerifier',
          deposit = 0,
          tokenPairs = tokenPairs',
          stateOracle = stateOracle' \<rparr>"

definition setTokenDepositAddress :: "BridgeState \<Rightarrow> address \<Rightarrow> Status \<times> BridgeState" where
  "setTokenDepositAddress state deposit' = 
    (if deposit state \<noteq> 0 then 
        (Fail ''Address already set'', state)
     else 
        (Success, state \<lparr> deposit := deposit' \<rparr>))"

locale ProofVerifier = Hash +
  fixes verifyProof :: "unit \<Rightarrow> bytes32 \<Rightarrow> bytes \<Rightarrow> uint256 \<Rightarrow> bytes32 \<Rightarrow> bool"
  fixes generateStateRoot :: "TokenDepositState \<Rightarrow> bytes32"
  fixes generateProof :: "TokenDepositState \<Rightarrow> uint256 \<Rightarrow> bytes"
  assumes verifyDepositProof:
    "\<And> state ID state_root proof val. \<lbrakk> 
         generateProof state ID = proof; generateStateRoot state = state_root \<rbrakk> \<Longrightarrow>
         verifyProof () state_root proof ID val = True \<longleftrightarrow>
         getDeposit state ID = val" 

context ProofVerifier
begin

definition callVerifyProof where
  "callVerifyProof contracts address state_root proof ID v = 
      (case proofVerifierState contracts address of 
            None \<Rightarrow>
               Fail ''wrong address''
          | Some state \<Rightarrow> 
               if \<not> verifyProof state state_root proof ID v then
                  Fail ''proof verification failed''
               else
                  Success)"

abbreviation getClaim :: "BridgeState \<Rightarrow> uint256 \<Rightarrow> bool" where
  "getClaim state ID \<equiv> lookupBool (claims state) ID"
abbreviation setClaim where
  "setClaim state ID b \<equiv> state \<lparr> claims := Mapping.update ID b (claims state) \<rparr>"

definition claim :: "Contracts \<Rightarrow> Message \<Rightarrow> BridgeState \<Rightarrow> uint256 \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> bytes \<Rightarrow> Status \<times> BridgeState \<times> Contracts" where
  "claim contracts msg state ID token amount proof =
   (if getClaim state ID then 
      (Fail ''Already claimed'', state, contracts) 
    else 
       let depositHash = hash (sender msg) token amount;
           (status, lastState) = callLastState contracts (stateOracle state)
        in if status \<noteq> Success then
              (status, state, contracts)
           else 
              let status = callVerifyProof contracts (proofVerifier state) lastState proof ID depositHash
               in if status \<noteq> Success then
                     (status, state, contracts) 
                  else 
                     let (status, mintedToken) = callOriginalToMinted contracts (tokenPairs state) token
                      in if status \<noteq> Success then
                            (status, state, contracts)
                         else if mintedToken = 0 then 
                            (Fail ''No minted token for given token'', state, contracts) 
                         else 
                            let state' = setClaim state ID True;
                                (status, contracts') = callMint contracts mintedToken (sender msg) amount
                             in if status \<noteq> Success then 
                                   (status, state, contracts)
                                else 
                                   (Success, state', contracts'))"

definition callClaim where
  "callClaim contracts address msg ID token amount proof = 
     (case bridgeState contracts address of
           None \<Rightarrow> (Fail ''wrong address'', contracts)
         | Some state \<Rightarrow> 
             let (status, state', contracts') = claim contracts msg state ID token amount proof
              in if status \<noteq> Success then
                    (status, contracts)
                 else 
                    (Success, setBridgeState contracts' address state'))"

section \<open>Correctness proofs\<close>

lemma lookupNat_update [simp]: 
  shows "lookupNat (Mapping.update k v m) k = v"
  unfolding lookupNat_def
  by (simp add: lookup_default_update)

lemma lookupNat_update' [simp]:
  assumes "k' \<noteq> k"
  shows "lookupNat (Mapping.update k v m) k' = lookupNat m k'"
  using assms
  unfolding lookupNat_def
  by (auto simp add: lookup_default_update')

section \<open>IERC20\<close>

subsection \<open>callBalanceOf\<close>

lemma callBalanceOf [simp]:
  assumes "callBalanceOf contracts token account = (Success, balance)"
  shows "balanceOf (the (ERC20state contracts token)) account = balance"
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
  shows "balanceOf (the (ERC20state contracts' mintedToken)) account = 
         balanceOf (the (ERC20state contracts mintedToken)) account + amount"
  using assms
  unfolding callMint_def
  by (auto simp add: Let_def split: option.splits)

lemma callMintBalanceOfOther [simp]:
  assumes "other \<noteq> account"
  assumes "callMint contracts mintedToken account amount = (Success, contracts')"
  shows "balanceOf (the (ERC20state contracts' mintedToken)) other =
         balanceOf (the (ERC20state contracts mintedToken)) other"
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

section \<open>TokenPairs\<close>

abbreviation getMinted where
  "getMinted state token \<equiv> lookupNat (originalToMinted state) token"

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

text \<open>Sufficient condtion for callLastState to succeed\<close>
lemma callLastStateI:
  assumes "stateOracleState contracts address \<noteq> None" \<comment> \<open>There is a state oracle on the give address\<close>
  shows "fst (callLastState contracts address) = Success"
  using assms
  unfolding callLastState_def
  by (auto split: option.splits)

section \<open>TokenDeposit\<close>

subsection \<open>getIsDead\<close>
lemma getIsDeadDeposits [simp]:
  assumes "getIsDead contracts state block = (status, dead, state')"
  shows "deposits state' = deposits state"
  using assms
  unfolding getIsDead_def Let_def
  by (auto split: if_split_asm prod.splits)

lemma getIsDeadTokenPairs [simp]:
  assumes "getIsDead contracts state block = (status, dead, state')"
  shows "TokenDepositState.tokenPairs state' = TokenDepositState.tokenPairs state"
  using assms
  unfolding getIsDead_def Let_def
  by (auto split: if_split_asm prod.splits)

lemma getIsDeadStateOracle [simp]:
  assumes "getIsDead contracts state block = (status, dead, state')"
  shows "TokenDepositState.stateOracle state' = TokenDepositState.stateOracle state"
  using assms
  unfolding getIsDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

subsection \<open>deposit\<close>

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
  shows "getDeposit state' ID = hash (sender msg) token amount"
  using assms callSafeTransferFromBalanceOfTo'
  unfolding deposit_def
  by (auto simp add: Let_def split: prod.splits if_split_asm)

lemma callDepositWritesHash:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "getDeposit (the (tokenDepositState contracts' address)) ID = 
         hash (sender msg) token amount"
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

(* TODO: this is just an illustration - the lemma should be generalized to non-consecutive states *)
lemma depositNoDouble:
  assumes "hash (sender msg) token amount \<noteq> 0" \<comment> \<open>potential bug\<close>
  assumes "deposit state contracts this block msg ID token amount = (Success, state', contracts')"
  shows "fst (deposit state' (setTokenDepositState contracts' this state') this block' msg' ID token' amount') \<noteq> Success"
proof-
  have "getDeposit state' ID = hash (sender msg) token amount"
    using assms depositWritesHash by blast
  with \<open>hash (sender msg) token amount \<noteq> 0\<close>
  show ?thesis
    unfolding deposit_def
    by (auto split: prod.splits simp add: Let_def)
qed

lemma callDepositNoDouble:
  assumes "hash (sender msg) token amount \<noteq> 0" \<comment> \<open>potential bug\<close>
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "fst (callDeposit contracts' address block' msg' ID token' amount') \<noteq> Success"
  using assms depositNoDouble[OF assms(1)]
  unfolding callDeposit_def
  by (auto simp add: Let_def split: prod.splits option.splits if_split_asm) (metis fst_conv)

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

lemma callDepositOtherAddress [simp]: 
  assumes "address \<noteq> address'"
          "callDeposit contracts address' block msg ID token amount = (status, contracts')"
  shows "tokenDepositState contracts' address = tokenDepositState contracts address"
  using assms
  unfolding callDeposit_def deposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callDepositDepositStateOracle [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "TokenDepositState.stateOracle (the (tokenDepositState contracts' address)) =
         TokenDepositState.stateOracle (the (tokenDepositState contracts address))"
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

text \<open>Sufficient conditions for a deposit to be made\<close>
lemma callDepositI:
  assumes "tokenDepositState contracts address = Some state"
  assumes "tokenPairsState contracts (TokenDepositState.tokenPairs state) = Some stateTokenPairs"
  assumes "ERC20state contracts token = Some stateToken"
  assumes "getMinted stateTokenPairs token \<noteq> 0"

  \<comment> \<open>bridge is not dead\<close>
  assumes "getIsDead contracts state block = (Success, False, state')"
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

section \<open>StateOracle\<close>

subsection \<open>lastState\<close>

lemma callLastState [simp]:
  assumes "callLastState contracts address = (Success, state)"
  shows "state = L1StateOracleState.lastState (the (stateOracleState contracts address))"
  using assms
  unfolding callLastState_def
  by (simp split: option.splits)

subsection \<open>update\<close>

lemma callUpdateLastState [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  shows "L1StateOracleState.lastState (the (stateOracleState contracts' address)) = stateRoot"
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

section \<open>ProofVerifier\<close>

text \<open>Sufficient condition for a callVerifyProof to succeed\<close>
lemma callVerifyProofI:
  assumes "proofVerifierState contracts address \<noteq> None"
  assumes "verifyProof () state_root proof ID hsh"
  shows "callVerifyProof contracts address state_root proof ID hsh = Success"
  using assms
  unfolding callVerifyProof_def
  by (auto split: option.splits)

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
  unfolding claim_def
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

lemma claimBalanceOf:
  assumes "claim contracts msg state ID token amount proof = (Success, state', contracts')"
  assumes "stateTokenPairs = the (tokenPairsState contracts (tokenPairs state))"
  assumes "mintedToken = getMinted stateTokenPairs token"
  shows "balanceOf (the (ERC20state (setBridgeState contracts' address state') mintedToken)) (sender msg) = 
         balanceOf (the (ERC20state contracts mintedToken)) (sender msg) + amount"
  using assms callMintBalanceOf callOriginalToMinted
  unfolding claim_def
  by (auto simp add: Let_def split: if_split_asm prod.splits option.splits)

lemma callClaimBalanceOf:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "state = the (bridgeState contracts address)"
  assumes "stateTokenPairs = the (tokenPairsState contracts (tokenPairs state))"
  assumes "mintedToken = getMinted stateTokenPairs token"
  shows "balanceOf (the (ERC20state contracts' mintedToken)) (sender msg) = 
         balanceOf (the (ERC20state contracts mintedToken)) (sender msg) + amount"
  using assms claimBalanceOf
  unfolding callClaim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

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
    unfolding callClaim_def claim_def
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

text \<open>Sufficient conditions for a claim\<close>
lemma callClaimI:
  assumes "bridgeState contracts address = Some stateBridge"
  assumes "tokenPairsState contracts (BridgeState.tokenPairs stateBridge) = Some stateTokenPairs"
  assumes "stateOracleState contracts (BridgeState.stateOracle stateBridge) = Some stateStateOracle"
  assumes "proofVerifierState contracts (BridgeState.proofVerifier stateBridge) \<noteq> None"
  assumes "ERC20state contracts (getMinted stateTokenPairs token) \<noteq> None" 
  assumes "getMinted stateTokenPairs token \<noteq> 0"
  \<comment> \<open>Proof must be verified\<close>
  assumes "verifyProof () (L1StateOracleState.lastState stateStateOracle) proof ID (hash (sender msg) token amount)"
  \<comment> \<open>There must not be a prior claim\<close>
  assumes "getClaim stateBridge ID = False"
  shows "fst (callClaim contracts address msg ID token amount proof) = Success"
proof-
  have "callLastState contracts (BridgeState.stateOracle stateBridge) = (Success, L1StateOracleState.lastState stateStateOracle)"
    using assms callLastStateI callLastState
    by (simp add: callLastState_def)
  moreover
  have "fst (callMint contracts (getMinted stateTokenPairs token) (sender msg) amount) = Success"
    using assms callMintI 
    by blast
  moreover
  have "callVerifyProof contracts (BridgeState.proofVerifier stateBridge)
         (L1StateOracleState.lastState stateStateOracle) proof ID (hash (sender msg) token amount) =
          Success"
    using assms callVerifyProofI
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

text \<open>Steps\<close>

datatype Step = 
  DEPOSIT address uint256 address uint256 (* address ID token amount *)
| CLAIM address uint256 address uint256 bytes (* address ID token amount proof *) 

primrec executeStep :: "Contracts \<Rightarrow> nat \<Rightarrow> Block \<Rightarrow> Message \<Rightarrow> Step \<Rightarrow> Status \<times> Contracts" where
  "executeStep contracts blockNum block msg (DEPOSIT address ID token amount) = 
    callDeposit contracts address block msg ID token amount"
| "executeStep contracts blockNum block msg (CLAIM address ID token amount proof) = 
    callClaim contracts address msg ID token amount proof"

definition ContractsConstructor :: Contracts where
  "ContractsConstructor =
   \<lparr> 
     IERC20 = Mapping.empty,
     IStateOracle = Mapping.empty,
     ITokenPairs = Mapping.empty,
     ITokenDeposit = Mapping.empty,
     IBridge = Mapping.empty,
     IProofVerifier = Mapping.empty \<rparr>"

definition init :: "uint256 \<Rightarrow> Contracts" where
  "init L1ChainId = 
    (let original = 100;
         minted = 200;
         tokenPairs = 300;
         bridge = 400;
         proofVerifier = 500;
         stateOracle = 600;
         tokenDeposit = 700;

         originalState = ERC20Constructor;
         mintedState = ERC20Constructor;
         tokenPairsState = TokenPairsConstructor;
         tokenPairsState = addTokenPair tokenPairsState original minted;
         proofVerifierState = ();
         bridgeState = BridgeStateConstructor proofVerifier tokenPairs stateOracle;
         (status, bridgeState) = setTokenDepositAddress bridgeState tokenDeposit;
         L1StateOracleState = L1StateOracleConstructor L1ChainId [];
         tokenDepositState = TokenDepositConstructor proofVerifier bridge tokenPairs stateOracle;
         contracts = ContractsConstructor;
         contracts = setERC20State contracts original originalState;
         contracts = setERC20State contracts minted mintedState;
         contracts = setTokenPairsState contracts tokenPairs tokenPairsState;
         contracts = setProofVerifierState contracts proofVerifier proofVerifierState;
         contracts = setBridgeState contracts bridge bridgeState;
         contracts = setStateOracleState contracts stateOracle L1StateOracleState;
         contracts = setTokenDepositState contracts tokenDeposit tokenDepositState
      in contracts)"

inductive reachableFrom where
  reachableFrom_base: "\<And> contracts. reachableFrom contracts contracts"
| reachableFrom_step: "\<And> contracts contracts' blockNum block msg step. 
                       \<lbrakk>reachableFrom contracts contracts'; 
                        executeStep contracts' blockNum block msg step = (Success, contracts'')\<rbrakk> \<Longrightarrow> 
                        reachableFrom contracts contracts''" 

text \<open>Just a simple experiment - prove that some trivial property is preserved across reachable states.
      Original to minted token mapping is never changed.\<close>
lemma reachableFromOriginalToMinted:
  assumes "reachableFrom contracts contracts'" 
        "callOriginalToMinted contracts tokenPairsAddr original = (Success, minted)"
  shows "callOriginalToMinted contracts' tokenPairsAddr original = (Success, minted)"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  show ?case
  proof (cases step)
    case (DEPOSIT address ID token amount)
    then show ?thesis 
      using reachableFrom_step
      unfolding callOriginalToMinted_def
      by (simp add: Let_def split: option.splits prod.splits if_split_asm)
  next
    case (CLAIM address ID token amount "proof")
    then show ?thesis
      using reachableFrom_step
      unfolding callOriginalToMinted_def
      by (simp add: Let_def split: option.splits prod.splits if_split_asm)
  qed 
qed


text \<open>A more interesting property - there are no double claims\<close>
lemma callClaimNoDouble':
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
          "reachableFrom contracts' contracts''"
        shows "fst (callClaim contracts'' address msg' ID token' amount' proof') \<noteq> Success"
proof-
  define state' where "state' = the (bridgeState contracts' address)"
  have "getClaim state' ID = True"
    using assms
    by (simp add: callClaimWritesClaim state'_def)
  then have *: "getClaim (the (bridgeState contracts' address)) ID = True"
    using state'_def
    by simp
  from \<open>reachableFrom contracts' contracts''\<close>
  have "getClaim (the (bridgeState contracts'' address)) ID = True"
    using *
  proof (induction contracts' contracts'' rule: reachableFrom.induct)
    case (reachableFrom_base contracts')
    then show ?case 
      by simp
  next
    case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
    show ?case
    proof (cases step)
      case (DEPOSIT address' ID' token' amount')
      then show ?thesis
        using reachableFrom_step
        by simp
    next
      case (CLAIM address' ID' token' amount' proof')
      show ?thesis
      proof (cases "address = address'")
        case True
        then show ?thesis
          using reachableFrom_step CLAIM
          by simp
      next
        case False
        then show ?thesis
          using reachableFrom_step CLAIM
          by (simp add: Let_def split: option.splits prod.splits)
      qed
    qed
  qed
  then show ?thesis
    unfolding callClaim_def claim_def
    by (auto simp add: Let_def split: option.splits prod.splits)
qed

text \<open>Once written deposit entry cannot be unset\<close>
lemma reachableFromGetDeposit:
  assumes "reachableFrom contracts contracts'"
  assumes "h \<noteq> 0"
  assumes "getDeposit (the (tokenDepositState contracts address)) ID = h"
  shows "getDeposit (the (tokenDepositState contracts' address)) ID = h"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  show ?case
  proof (cases step)
    case (CLAIM address' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (DEPOSIT address' ID' token' amount')
    show ?thesis
    proof (cases "address' \<noteq> address")
      case True
      then show ?thesis
        using DEPOSIT reachableFrom_step callDepositOtherAddress[of address address']
        by auto
    next
      case False
      show ?thesis
      proof (cases "ID = ID'")
        case True
        then have False
          using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> address\<close> callDepositWrittenHash[of contracts' address ID' block msg token' amount']
          by auto
        then show ?thesis
          by simp
      next
        case False
        then show ?thesis
          using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> address\<close>
          by auto
      qed
    qed
  qed
qed

lemma reachableFromBridgeState:
  assumes "reachableFrom contracts contracts'"
  assumes "bridgeState contracts address \<noteq> None"
  shows "bridgeState contracts' address \<noteq> None"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  then show ?case
    using callClaimBridgeState[of contracts'] callClaimOtherAddress
    by (cases step, simp, metis executeStep.simps(2))
qed

lemma reachableFromERC20State:
  assumes "reachableFrom contracts contracts'"
  assumes "ERC20state contracts token \<noteq> None"
  shows "ERC20state contracts' token \<noteq> None"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  then show ?case
  proof(cases step)
    case (DEPOSIT address' ID' token' amount')
    then show ?thesis
      using reachableFrom_step callDepositERC20state(2)
      by (cases "token = token'") auto
  next
    case (CLAIM address' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (simp add: callClaimERC20state)      
  qed
qed

lemma reachableFromBridgeTokenPairs [simp]:
  assumes "reachableFrom contracts contracts'"
  shows "BridgeState.tokenPairs (the (bridgeState contracts' address)) = 
         BridgeState.tokenPairs (the (bridgeState contracts address))"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromBridgeStateOracle [simp]:
  assumes "reachableFrom contracts contracts'"
  shows "BridgeState.stateOracle (the (bridgeState contracts' address)) = 
         BridgeState.stateOracle (the (bridgeState contracts address))"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromBridgeProofVerifier [simp]:
  assumes "reachableFrom contracts contracts'"
  shows "BridgeState.proofVerifier (the (bridgeState contracts' address)) = 
         BridgeState.proofVerifier (the (bridgeState contracts address))"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromDepositStateOracle [simp]:
  assumes "reachableFrom contracts contracts'"
  shows "TokenDepositState.stateOracle (the (tokenDepositState contracts' address)) =
         TokenDepositState.stateOracle (the (tokenDepositState contracts address))"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (CLAIM address' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by auto
  qed
qed

lemma reachableFromITokenPairs [simp]:
  assumes "reachableFrom contracts contracts'"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableFromIProofVerifier [simp]:
  assumes "reachableFrom contracts contracts'"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
proof (induction contracts contracts' rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step contracts'' contracts contracts' blockNum block msg step)
  then show ?case
    by (cases step, auto)
qed

text \<open>After a successful deposit and a state update a claim can be made\<close>
lemma claimPossibleAfterDepositAndUpdate:
  assumes "callDeposit contracts tokenDepositAddress block msg ID token amount = (Success, contractsD)"
  assumes "reachableFrom contractsD contractsD'"
  assumes "stateRoot = generateStateRoot (the (tokenDepositState contractsD' tokenDepositAddress))"
  assumes "proof = generateProof (the (tokenDepositState contractsD' tokenDepositAddress)) ID"
  assumes "callUpdate contractsD' stateOracleAddress block blockNum stateRoot = (Success, contractsU)"

  assumes "hash (sender msg) token amount \<noteq> 0" (* ADDITIONAL PREMISE *)
  assumes "TokenDepositState.stateOracle (the (tokenDepositState contracts tokenDepositAddress)) =
          stateOracleAddress"
  assumes "BridgeState.stateOracle (the (bridgeState contracts bridgeAddress)) =
          stateOracleAddress"
  assumes "BridgeState.proofVerifier (the (bridgeState contracts bridgeAddress)) =
          proofVerifierAddress"
  assumes "tokenPairsState contracts (BridgeState.tokenPairs (the (bridgeState contracts bridgeAddress))) = Some stateTokenPairs"
  assumes "proofVerifierState contracts proofVerifierAddress \<noteq> None"
  assumes "bridgeState contracts bridgeAddress \<noteq> None"
  assumes "getMinted stateTokenPairs token \<noteq> 0"
  assumes "ERC20state contracts (getMinted stateTokenPairs token) \<noteq> None"
  assumes "getClaim (the (bridgeState contractsU bridgeAddress)) ID = False"
  assumes "sender msg' = sender msg"

  shows "\<exists> contractsC. callClaim contractsU bridgeAddress msg' ID token amount proof = (Success, contractsC)"
proof-
  have "verifyProof () stateRoot proof ID (hash (sender msg) token amount) = True"
    using assms callDepositWritesHash reachableFromGetDeposit verifyDepositProof
    by auto

  have "bridgeState contractsU bridgeAddress \<noteq> None"
    using reachableFromBridgeState assms by auto
  then obtain stateBridgeU where 
    "bridgeState contractsU bridgeAddress = Some stateBridgeU"
    by auto
  then have stateBridgeU: "stateBridgeU = the (bridgeState contractsU bridgeAddress)"
    using \<open>bridgeState contractsU bridgeAddress \<noteq> None\<close>
    by auto

  have "TokenDepositState.stateOracle (the (tokenDepositState contractsU tokenDepositAddress)) =
        stateOracleAddress"
    using assms
    by auto

  have "BridgeState.stateOracle stateBridgeU = stateOracleAddress"
       "BridgeState.proofVerifier stateBridgeU =  proofVerifierAddress"
       "tokenPairsState contractsU (BridgeState.tokenPairs stateBridgeU) = Some stateTokenPairs"
    using assms stateBridgeU \<open>bridgeState contractsU bridgeAddress \<noteq> None\<close>
    by auto

  have "L1StateOracleState.lastState (the (stateOracleState contractsU stateOracleAddress)) = stateRoot"
    using \<open>callUpdate contractsD' stateOracleAddress block blockNum stateRoot = (Success, contractsU)\<close>
    by simp

  have "fst (callClaim contractsU bridgeAddress msg' ID token amount proof) = Success"
  proof (rule callClaimI)
    show "bridgeState contractsU bridgeAddress = Some stateBridgeU"
      by fact
  next
    show "verifyProof () (L1StateOracleState.lastState (the (stateOracleState contractsU (BridgeState.stateOracle stateBridgeU)))) proof ID
     (hash (sender msg') token amount)"
      using \<open>bridgeState contractsU bridgeAddress = Some stateBridgeU\<close>
      using \<open>BridgeState.stateOracle stateBridgeU = stateOracleAddress\<close>
      using \<open>L1StateOracleState.lastState (the (stateOracleState contractsU stateOracleAddress)) = stateRoot\<close>
      using \<open>verifyProof () stateRoot proof ID (hash (sender msg) token amount) = True\<close>
      using \<open>sender msg' = sender msg\<close>
      by simp
  next
    show "tokenPairsState contractsU (BridgeState.tokenPairs stateBridgeU) = Some stateTokenPairs"
      using \<open>bridgeState contractsU bridgeAddress = Some stateBridgeU\<close>
            \<open>tokenPairsState contractsU (BridgeState.tokenPairs stateBridgeU) = Some stateTokenPairs\<close> 
      by auto
  next
    show "stateOracleState contractsU (BridgeState.stateOracle stateBridgeU) =
          Some (the (stateOracleState contractsU (BridgeState.stateOracle stateBridgeU)))"
    using \<open>BridgeState.stateOracle stateBridgeU = stateOracleAddress\<close>
    using callUpdateStateOracleState[OF \<open>callUpdate contractsD' stateOracleAddress block blockNum stateRoot = (Success, contractsU)\<close>]
    by auto
  next
    show "proofVerifierState contractsU (BridgeState.proofVerifier stateBridgeU) \<noteq> None"
      using \<open>BridgeState.proofVerifier stateBridgeU = proofVerifierAddress\<close> 
            \<open>bridgeState contractsU bridgeAddress = Some stateBridgeU\<close> 
      using assms
      by (metis callDepositIProofVerifier callUpdateIProofVerifier reachableFromIProofVerifier)
  next
    show "getMinted stateTokenPairs token \<noteq> 0"
      by fact
  next
    show "ERC20state contractsU (getMinted stateTokenPairs token) \<noteq> None"
      using assms
      by (metis callDepositERC20state(2) callDepositOtherToken callUpdateIERC20 reachableFromERC20State)
  next
    show "getClaim stateBridgeU ID = False"
      using \<open>bridgeState contractsU bridgeAddress = Some stateBridgeU\<close> assms 
      by auto
  qed
  then show ?thesis
    by (metis eq_fst_iff)
qed

end