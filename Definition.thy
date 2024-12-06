theory Definition
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

record StateOracleState = 
   lastState :: bytes32
   lastBlockNum :: uint256
   lastUpdateTime :: uint256
   chainId :: uint256

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

abbreviation getDeposit :: "TokenDepositState \<Rightarrow> uint256 \<Rightarrow> bytes32" where
  "getDeposit state ID \<equiv> lookupNat (deposits state) ID"
abbreviation setDeposit :: "TokenDepositState \<Rightarrow> uint256 \<Rightarrow> bytes32 \<Rightarrow> TokenDepositState" where
  "setDeposit state ID v \<equiv> state \<lparr> deposits := Mapping.update ID v (deposits state) \<rparr>"
abbreviation deleteDeposit :: "TokenDepositState \<Rightarrow> uint256 \<Rightarrow> TokenDepositState" where
  "deleteDeposit state ID \<equiv> state \<lparr> deposits := Mapping.delete ID (deposits state) \<rparr>"

abbreviation getTokenWithdrawn :: "TokenDepositState \<Rightarrow> uint256 \<Rightarrow> bool" where
  "getTokenWithdrawn state withdrawHash \<equiv> lookupBool (tokenWithdrawn state) withdrawHash"
abbreviation setTokenWithdrawn :: "TokenDepositState \<Rightarrow> uint256 \<Rightarrow> TokenDepositState" where
  "setTokenWithdrawn state withdrawHash \<equiv>  state \<lparr> tokenWithdrawn := Mapping.update withdrawHash True (tokenWithdrawn state)\<rparr>"

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

abbreviation getClaim :: "BridgeState \<Rightarrow> uint256 \<Rightarrow> bool" where
  "getClaim state ID \<equiv> lookupBool (claims state) ID"
abbreviation setClaim :: "BridgeState \<Rightarrow> uint256 \<Rightarrow> bool \<Rightarrow> BridgeState" where
  "setClaim state ID b \<equiv> state \<lparr> claims := Mapping.update ID b (claims state) \<rparr>"

text \<open>ProofVerifier\<close>
\<comment> \<open>it has no state\<close>
type_synonym ProofVerifierState = unit

text \<open>Blokchain maps adresses to contract states. We have to keep a separate mapping for each type \<close>
record Contracts = 
  IERC20 :: "(address, ERC20State) mapping"
  IStateOracle :: "(address, StateOracleState) mapping"
  ITokenPairs :: "(address, TokenPairsState) mapping"
  ITokenDeposit :: "(address, TokenDepositState) mapping"
  IBridge :: "(address, BridgeState) mapping"
  IProofVerifier :: "(address, ProofVerifierState) mapping" (* no state *)

abbreviation stateOracleState :: "Contracts \<Rightarrow> address \<Rightarrow> StateOracleState option" where
  "stateOracleState contracts address \<equiv> Mapping.lookup (IStateOracle contracts) address"

abbreviation setStateOracleState :: "Contracts \<Rightarrow> address \<Rightarrow> StateOracleState \<Rightarrow> Contracts" where
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
(* FIXME: each call also has a message, block, this addresss, ... *)
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

definition StateOracleConstructor :: "uint256 \<Rightarrow> Validator list \<Rightarrow> StateOracleState" where
  "StateOracleConstructor chainId' validators = 
      \<lparr> StateOracleState.lastState = 0, 
        StateOracleState.lastBlockNum = 0, 
        StateOracleState.lastUpdateTime = 0, 
        StateOracleState.chainId = chainId' \<rparr>"

text \<open>Read the last known state root\<close>
text \<open>Call via contract address\<close>
definition callLastState :: "Contracts \<Rightarrow> address \<Rightarrow> Status \<times> bytes32" where
  "callLastState contracts address = 
     (case stateOracleState contracts address of
           None \<Rightarrow> 
             (Fail ''wrong address'', 0)
         | Some state \<Rightarrow> 
             (Success, StateOracleState.lastState state))"

text \<open>Call via contract address\<close>
definition callLastUpdateTime :: "Contracts \<Rightarrow> address \<Rightarrow> Status \<times> bytes32" where
  "callLastUpdateTime contracts address = 
     (case stateOracleState contracts address of
          None \<Rightarrow> 
             (Fail ''wrong address'', 0)
        | Some state \<Rightarrow> 
             (Success, StateOracleState.lastUpdateTime state))"

text \<open>Update the state oracle by giving it the info about the last known block (its blockNum and stateRoot are known) \<close>
definition update :: "StateOracleState \<Rightarrow> Block \<Rightarrow> uint256 \<Rightarrow> bytes32 \<Rightarrow> Status \<times> StateOracleState" where
  "update state block blockNum stateRoot = 
   (if blockNum \<le> StateOracleState.lastBlockNum state then 
       (Fail ''Replay of old signed state'', state)
    else
       (Success, state \<lparr> StateOracleState.lastState := stateRoot, 
                         StateOracleState.lastUpdateTime := timestamp block,
                         StateOracleState.lastBlockNum := blockNum \<rparr>))"

text \<open>Call via contract address\<close>
definition callUpdate :: "Contracts \<Rightarrow> address \<Rightarrow> Block \<Rightarrow> uint256 \<Rightarrow> bytes32 \<Rightarrow> Status \<times> Contracts"  where
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
definition getDeadStatus :: "Contracts \<Rightarrow> TokenDepositState \<Rightarrow> Block \<Rightarrow> Status \<times> bool \<times> TokenDepositState" where
 "getDeadStatus contracts state block = 
      (if deadState state \<noteq> 0 then
          (Success, True, state)
       else
          let (status, lastUpdateTime) = callLastUpdateTime contracts (TokenDepositState.stateOracle state)
           in if status \<noteq> Success then 
                 (status, False, state) 
          else if lastUpdateTime \<noteq> 0 \<and> lastUpdateTime < (timestamp block) - TIME_UNTIL_DEAD then 
                 let (status, lastState) = callLastState contracts (TokenDepositState.stateOracle state)
                  in if status \<noteq> Success \<or> lastState = 0 then \<comment> \<open>or lastState = 0 is an additional check\<close>
                        (status, False, state)
                     else
                        (Success, True, state \<lparr> deadState := lastState \<rparr>) 
              else
                  (Success, False, state)
      )"

definition lastValidState :: "Contracts \<Rightarrow> TokenDepositState \<Rightarrow> Status \<times> bytes32" where
  "lastValidState contracts state =
    (if deadState state \<noteq> 0 then
        (Success, deadState state)
     else
         callLastState contracts (TokenDepositState.stateOracle state))"

definition callOriginalToMinted :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> Status \<times> address" where
  "callOriginalToMinted contracts address token = 
      (let state_opt = Mapping.lookup (ITokenPairs contracts) address
        in case state_opt of None \<Rightarrow> 
              (Fail ''wrong address'', 0)
           | Some state \<Rightarrow> (Success, lookupNat (originalToMinted state) token))"

locale Hash = 
  fixes hash2 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  fixes hash3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
begin

text \<open>hash function is injective\<close>
definition hash2_inj where
  "hash2_inj  \<longleftrightarrow> (\<forall> x1 x2 x1' x2'. 
                  hash2 x1 x2 = hash2 x1' x2'  \<longrightarrow> 
                  x1' = x1 \<and> x2' = x2)"

text \<open>hash function is injective\<close>
definition hash3_inj where
  "hash3_inj  \<longleftrightarrow> (\<forall> x1 x2 x3 x1' x2' x3'. 
                  hash3 x1 x2 x3 = hash3 x1' x2' x3' \<longrightarrow> 
                  x1' = x1 \<and> x2' = x2 \<and> x3' = x3)"

end

(* NOTE: additional assumptions on the hashing functions that guarantee correctness *)
locale StrongHash = Hash + 
  assumes hash2_nonzero:
    "\<And> x1 x2. hash2 x1 x2 \<noteq> 0"
  assumes hash3_nonzero:
    "\<And> x1 x2 x3. hash3 x1 x2 x3 \<noteq> 0"
  assumes hash2_inj [simp]:
    "hash2_inj"
  assumes hash3_inj [simp]:
    "hash3_inj"

context Hash
begin

definition deposit :: "TokenDepositState \<Rightarrow> Contracts  \<Rightarrow> address \<Rightarrow> Block \<Rightarrow> Message \<Rightarrow> uint256 \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> Status \<times> TokenDepositState \<times> Contracts" where
  "deposit state contracts this block msg ID token amount = 
     (let (status, dead, state') = getDeadStatus contracts state block
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
                               else let state'' = setDeposit state' ID (hash3 (sender msg) token realAmount) 
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


(* FIXME: For typing reasons we have separate deposit proofs and claim proofs.
   Once the low level storage layout is formalized this will be merged. *)
locale ProofVerifier = 
  fixes generateStateRoot :: "Contracts \<Rightarrow> bytes32"
  \<comment> \<open>verifyDepositProof proofVerifierState tokenDepositAddress ID val stateRoot proof\<close> 
  fixes verifyDepositProof :: "unit \<Rightarrow> address \<Rightarrow> uint256  \<Rightarrow> bytes32 \<Rightarrow> bytes32 \<Rightarrow> bytes \<Rightarrow> bool"
  fixes generateDepositProof :: "Contracts \<Rightarrow> uint256 \<Rightarrow> bytes"

  assumes verifyDepositProofI:
    "\<And> tokenDepositAddress contracts ID state stateRoot proof val. 
        \<lbrakk>generateDepositProof contracts ID = proof; 
         generateStateRoot contracts = stateRoot; 
         tokenDepositState contracts tokenDepositAddress = Some state;
         getDeposit state ID = val\<rbrakk> \<Longrightarrow>
            verifyDepositProof () tokenDepositAddress ID val stateRoot proof = True" 
  assumes verifyDepositProofE:
    "\<And> contracts tokenDepositAddress state ID stateRoot proof val. 
        \<lbrakk>generateStateRoot contracts = stateRoot; 
         verifyDepositProof () tokenDepositAddress ID val stateRoot proof = True;
         tokenDepositState contracts tokenDepositAddress = Some state\<rbrakk> \<Longrightarrow>
         getDeposit state ID = val"

  \<comment> \<open>verifyClaimProof proofVerifierState bridgeAddress ID stateRoot proof\<close>
  fixes verifyClaimProof :: "unit \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> bytes32 \<Rightarrow> bytes \<Rightarrow> bool"
  \<comment> \<open>verifyClaimProof proofVerifierState bridgeAddress ID stateRoot proof\<close>
  fixes generateClaimProof :: "Contracts \<Rightarrow> uint256 \<Rightarrow> bytes"

  assumes verifyClaimProofI:
    "\<And> bridgeAddress contracts ID state stateRoot proof. 
        \<lbrakk>generateClaimProof contracts ID = proof; 
         generateStateRoot contracts = stateRoot; 
         bridgeState contracts brdigeAddress = Some state;
         getClaim state ID = False\<rbrakk> \<Longrightarrow>
            verifyClaimProof () bridgeAddress ID stateRoot proof = True" 

  assumes verifyClaimProofE:
    "\<And> contracts bridgeAddress state ID stateRoot proof. 
        \<lbrakk>generateStateRoot contracts = stateRoot; 
         verifyClaimProof () bridgeAddress ID stateRoot proof = True;
         bridgeState contracts bridgeAddress = Some state\<rbrakk> \<Longrightarrow>
         getClaim state ID = False"


  \<comment> \<open>verifyBalanceProof proofVerifierState token caller amount stateRoot proof\<close> 
  fixes verifyBalanceProof :: "unit \<Rightarrow> address \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> bytes32 \<Rightarrow> bytes \<Rightarrow> bool"
  fixes generateBalanceProof :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> bytes"

  assumes verifyBalanceProofI:
    "\<And> contracts stateRoot proof token caller amount. 
        \<lbrakk>generateBalanceProof contracts token caller amount = proof; 
         generateStateRoot contracts = stateRoot; 
         ERC20state contracts token = Some state;
         balanceOf state caller = amount\<rbrakk> \<Longrightarrow>
            verifyBalanceProof () token caller amount stateRoot proof = True" 
  assumes verifyBalanceProofE:
    "\<And> contracts stateRoot proof token caller amount. 
        \<lbrakk>generateStateRoot contracts = stateRoot; 
         verifyBalanceProof () token caller amount stateRoot proof = True;
         ERC20state contracts token = Some state\<rbrakk> \<Longrightarrow>
         balanceOf state caller = amount"

  assumes updateSuccess:
        "\<And> contracts address block blockNum stateRoot contracts'.
         \<lbrakk>callUpdate contracts address block blockNum stateRoot = (Success, contracts')\<rbrakk> \<Longrightarrow> 
          stateRoot = generateStateRoot contracts"

context ProofVerifier
begin

definition callVerifyDepositProof where
  "callVerifyDepositProof contracts proofVerifierAddress tokenDepositAddress ID v stateRoot proof = 
      (case proofVerifierState contracts proofVerifierAddress of 
            None \<Rightarrow>
               Fail ''wrong address''
          | Some state \<Rightarrow> 
               if \<not> verifyDepositProof state tokenDepositAddress ID v stateRoot proof then
                  Fail ''proof verification failed''
               else
                  Success)"

definition callVerifyClaimProof where
  "callVerifyClaimProof contracts proofVerifierAddress bridgeAddress ID stateRoot proof = 
      (case proofVerifierState contracts proofVerifierAddress of 
            None \<Rightarrow>
               Fail ''wrong address''
          | Some state \<Rightarrow> 
               if \<not> verifyClaimProof state bridgeAddress ID stateRoot proof then
                  Fail ''proof verification failed''
               else
                  Success)"

definition callVerifyBalanceProof where
  "callVerifyBalanceProof contracts proofVerifierAddress token caller amount stateRoot proof = 
      (case proofVerifierState contracts proofVerifierAddress of 
            None \<Rightarrow>
               Fail ''wrong address''
          | Some state \<Rightarrow> 
               if \<not> verifyBalanceProof state token caller amount stateRoot proof then
                  Fail ''proof verification failed''
               else
                  Success)"
end

locale HashProofVerifier = Hash + ProofVerifier
begin

definition claim :: "Contracts \<Rightarrow> Message \<Rightarrow> BridgeState \<Rightarrow> uint256 \<Rightarrow> address \<Rightarrow> uint256 \<Rightarrow> bytes \<Rightarrow> Status \<times> BridgeState \<times> Contracts" where
  "claim contracts msg state ID token amount proof =
   (if getClaim state ID then 
      (Fail ''Already claimed'', state, contracts) 
    else 
       let depositHash = hash3 (sender msg) token amount;
           (status, lastState) = callLastState contracts (stateOracle state)
        in if status \<noteq> Success then
              (status, state, contracts)
           else 
              let status = callVerifyDepositProof contracts (proofVerifier state) (BridgeState.deposit state) ID depositHash lastState proof
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


text \<open>TokenDeposit\<close>

definition cancelDepositWhileDead where
  "cancelDepositWhileDead state contracts this msg block ID token amount proof = 
     (if getDeposit state ID \<noteq> hash3 (sender msg) token amount then
         (Fail ''No deposit to cancel'', state, contracts)
      else 
         let (status, dead, state') = getDeadStatus contracts state block
          in if status \<noteq> Success then 
                (status, state, contracts)
             else if \<not> dead then 
                (Fail ''Bridge is not dead'', state', contracts)
             else
               let (status, stateRoot) = lastValidState contracts state'
                in if status \<noteq> Success then
                      (status, state, contracts)
                   else 
                     let status = callVerifyClaimProof contracts (TokenDepositState.proofVerifier state') (TokenDepositState.bridge state') ID stateRoot proof
                      in if status \<noteq> Success then
                            (status, state, contracts)
                         else 
                            let state'' = deleteDeposit state' ID;
                                \<comment> \<open>FIXME: the original uses safeTransfer\<close>
                                (status, contracts') = callSafeTransferFrom contracts token this (sender msg) amount 
                             in if status \<noteq> Success then
                                (status, state, contracts)
                             else
                                (Success, state'', contracts'))"

definition callCancelDepositWhileDead where
   "callCancelDepositWhileDead contracts address msg block ID token amount proof = 
     (case tokenDepositState contracts address of
           None \<Rightarrow> (Fail ''wrong address'', contracts)
         | Some state \<Rightarrow> 
             let (status, state', contracts') = cancelDepositWhileDead state contracts address msg block ID token amount proof
              in if status \<noteq> Success then
                    (status, contracts)
                 else 
                    (Success, setTokenDepositState contracts' address state'))"

(* FIXME: add exitAdministrator *)
definition withdrawWhileDead where
  "withdrawWhileDead state contracts this block msg token amount proof = 
    (let (status, dead, state') = getDeadStatus contracts state block
      in if status \<noteq> Success then 
            (status, state', contracts)
         else if \<not> dead then 
            (Fail ''Bridge must be dead'', state', contracts)
         else let status = callVerifyBalanceProof contracts (TokenDepositState.proofVerifier state') token (sender msg) amount (deadState state') proof
               in if status \<noteq> Success then
                 (status, state', contracts)
               else let withdrawHash = hash2 (sender msg) token
                     in if getTokenWithdrawn state withdrawHash then
                           (Fail ''Already withdrawn'', state', contracts) 
                        else let (status, contracts') = callSafeTransferFrom contracts token this (sender msg) amount
                              in if status \<noteq> Success then
                                    (status, state', contracts)
                                 else
                                    (Success, setTokenWithdrawn state' withdrawHash, contracts'))"

definition callWithdrawWhileDead where
   "callWithdrawWhileDead contracts address msg block token amount proof = 
     (case tokenDepositState contracts address of
           None \<Rightarrow> (Fail ''wrong address'', contracts)
         | Some state \<Rightarrow> 
             let (status, state', contracts') = withdrawWhileDead state contracts address block msg token amount proof
              in if status \<noteq> Success then
                    (status, contracts)
                 else 
                    (Success, setTokenDepositState contracts' address state'))"

end

locale StrongHashProofVerifier = StrongHash + ProofVerifier

sublocale StrongHashProofVerifier \<subseteq> HashProofVerifier
  by unfold_locales

\<comment> \<open>stateOracle address written in a token deposit\<close>
abbreviation stateOracleAddressTD :: "Contracts \<Rightarrow> address \<Rightarrow> address" where
  "stateOracleAddressTD contracts tokenDepositAddress \<equiv> TokenDepositState.stateOracle (the (tokenDepositState contracts tokenDepositAddress))"
\<comment> \<open>last state of the state oracle whose address is writ
ten in a token deposit\<close>
abbreviation getLastStateTD :: "Contracts \<Rightarrow> address \<Rightarrow> uint256" where
  "getLastStateTD contracts tokenDepositAddress \<equiv> StateOracleState.lastState (the (stateOracleState contracts (stateOracleAddressTD contracts tokenDepositAddress)))"
\<comment> \<open>stateOracle address written in a bridge\<close>
abbreviation stateOracleAddressB :: "Contracts \<Rightarrow> address \<Rightarrow> address" where
  "stateOracleAddressB contracts bridgeAddress \<equiv> BridgeState.stateOracle (the (bridgeState contracts bridgeAddress))"
\<comment> \<open>last state of the state oracle whose address is written in a token deposit\<close>
abbreviation getLastStateB :: "Contracts \<Rightarrow> address \<Rightarrow> uint256" where
  "getLastStateB contracts bridgeAddress \<equiv> StateOracleState.lastState (the (stateOracleState contracts (stateOracleAddressB contracts bridgeAddress)))"

abbreviation getMinted where
  "getMinted state token \<equiv> lookupNat (originalToMinted state) token"

abbreviation bridgeDead where
  "bridgeDead contracts tokenDepositAddress \<equiv>
   deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"

text \<open>read minted token for a given token using the given bridge address\<close>
definition bridgeMintedToken :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address" where
  "bridgeMintedToken contracts bridgeAddress token = 
    (let state = the (bridgeState contracts bridgeAddress);
         stateTokenPairs = the (tokenPairsState contracts (BridgeState.tokenPairs state))
      in getMinted stateTokenPairs token)"

end