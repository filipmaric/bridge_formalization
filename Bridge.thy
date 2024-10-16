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

abbreviation getLastStateTD :: "Contracts \<Rightarrow> address \<Rightarrow> uint256" where
  "getLastStateTD contracts tokenDepositAddress \<equiv> StateOracleState.lastState (the (stateOracleState contracts (TokenDepositState.stateOracle (the (tokenDepositState contracts tokenDepositAddress)))))"

abbreviation getLastStateB :: "Contracts \<Rightarrow> address \<Rightarrow> uint256" where
  "getLastStateB contracts bridgeAddress \<equiv> StateOracleState.lastState (the (stateOracleState contracts (BridgeState.stateOracle (the (bridgeState contracts bridgeAddress)))))"

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
                  in if status \<noteq> Success then
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
  fixes hash :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

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


(* FIXME: For typing reasons we have separate deposit proofs and claim proofs.
   Once the low level storage layout is formalized this will be merged. *)
locale ProofVerifier = Hash +
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
     (if getDeposit state ID \<noteq> hash (sender msg) token amount then
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

lemma callSafeTransferFromIStateOracle [simp]: 
  assumes "callSafeTransferFrom contracts token (sender msg) address amount = (Success, contracts')"
  shows "IStateOracle contracts = IStateOracle contracts'"
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

lemma deadStatusTrueDeadState [simp]:
  assumes "getDeadStatus contracts state block = (Success, True, state')"
  assumes "lastState (the (stateOracleState contracts (TokenDepositState.stateOracle state))) \<noteq> 0"
  shows "deadState state' \<noteq> 0"
  using assms
  unfolding getDeadStatus_def callLastState_def
  by (auto split: if_split_asm option.splits prod.splits)

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

(* FIXME: add other conclusions *)
lemma callDepositE:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  shows "tokenDepositState contracts' address \<noteq> None"
  using assms
  unfolding callDeposit_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

section \<open>StateOracle\<close>

subsection \<open>lastState\<close>

lemma callLastState [simp]:
  assumes "callLastState contracts address = (Success, state)"
  shows "state = StateOracleState.lastState (the (stateOracleState contracts address))"
  using assms
  unfolding callLastState_def
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



section \<open>ProofVerifier\<close>

text \<open>Sufficient condition for a callVerifyProof to succeed\<close>
lemma callVerifyDepositProofI:
  assumes "proofVerifierState contracts address \<noteq> None"
  assumes "verifyDepositProof () contractAddress stateRoot proof ID hsh"
  shows "callVerifyDepositProof contracts address contractAddress stateRoot proof ID hsh = Success"
  using assms
  unfolding callVerifyDepositProof_def
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
  unfolding claim_def lookupBool_def
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

lemma callClaimCallLastState:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "let state = the (bridgeState contracts address);
             lastState = StateOracleState.lastState (the (stateOracleState contracts (BridgeState.stateOracle state)))
          in callLastState contracts (BridgeState.stateOracle state) = (Success, lastState)"
  using assms callLastState
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def simp del: callLastState split: option.splits prod.splits if_split_asm)

lemma callClaimCallVerifyProof:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "let state = the (bridgeState contracts address);
             lastState = StateOracleState.lastState (the (stateOracleState contracts (BridgeState.stateOracle state)))
          in callVerifyDepositProof contracts (BridgeState.proofVerifier state) (BridgeState.deposit state)
                             ID (hash (sender msg) token amount) lastState proof = Success"
  using assms callLastState
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def simp del: callLastState split: option.splits prod.splits if_split_asm)

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

lemma callClaimIStateOracle [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "IStateOracle contracts = IStateOracle contracts'"
  using assms
  unfolding callClaim_def claim_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma callClaimDeposit [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "BridgeState.deposit (the (bridgeState contracts' address)) =
         BridgeState.deposit (the (bridgeState contracts address))"
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

lemma callClaimDeadState [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 
         deadState (the (tokenDepositState contracts tokenDepositAddress))"
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
    unfolding callClaim_def claim_def lookupBool_def
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
  assumes "verifyDepositProof () (BridgeState.deposit stateBridge) ID (hash (sender msg) token amount) (StateOracleState.lastState stateStateOracle) proof"
  \<comment> \<open>There must not be a prior claim\<close>
  assumes "getClaim stateBridge ID = False"
  shows "fst (callClaim contracts address msg ID token amount proof) = Success"
proof-
  have "callLastState contracts (BridgeState.stateOracle stateBridge) = (Success, StateOracleState.lastState stateStateOracle)"
    using assms callLastStateI callLastState
    by (simp add: callLastState_def)
  moreover
  have "fst (callMint contracts (getMinted stateTokenPairs token) (sender msg) amount) = Success"
    using assms callMintI 
    by blast
  moreover
  have "callVerifyDepositProof contracts (BridgeState.proofVerifier stateBridge)
         (BridgeState.deposit stateBridge) ID (hash (sender msg) token amount) (StateOracleState.lastState stateStateOracle) proof =
          Success"
    using assms callVerifyDepositProofI
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
  DEPOSIT address address uint256 address uint256 (* address caller ID token amount *)
| CLAIM address address uint256 address uint256 bytes (* address caller ID token amount proof *) 
| UPDATE address bytes32 (* address stateRoot *)

definition message where 
  "message sender' val' = \<lparr> sender = sender', val = val' \<rparr>"

primrec executeStep :: "Contracts \<Rightarrow> nat \<Rightarrow> Block \<Rightarrow> Step \<Rightarrow> Status \<times> Contracts" where
  "executeStep contracts blockNum block (DEPOSIT address caller ID token amount) = 
    callDeposit contracts address block (message caller amount) ID token amount"
| "executeStep contracts blockNum block (CLAIM address caller ID token amount proof) = 
    callClaim contracts address (message caller amount) ID token amount proof"
| "executeStep contracts blockNum block (UPDATE address stateRoot) = 
    callUpdate contracts address block blockNum stateRoot"

definition ContractsConstructor :: Contracts where
  "ContractsConstructor =
   \<lparr> IERC20 = Mapping.empty,
     IStateOracle = Mapping.empty,
     ITokenPairs = Mapping.empty,
     ITokenDeposit = Mapping.empty,
     IBridge = Mapping.empty,
     IProofVerifier = Mapping.empty \<rparr>"

definition TOKEN_DEPOSIT_ADDRESS where [simp]: "TOKEN_DEPOSIT_ADDRESS = 100"
definition BRIDGE_ADDRESS where [simp]: "BRIDGE_ADDRESS = 200"
definition TOKEN_ADDRESS where [simp]: "TOKEN_ADDRESS = 300"
definition MINTED_ADDRESS where [simp]: "MINTED_ADDRESS = 400"
definition TOKEN_PAIRS_ADDRESS where [simp]: "TOKEN_PAIRS_ADDRESS = 500"
definition STATE_ORACLE_ADDRESS where [simp]: "STATE_ORACLE_ADDRESS = 600"
definition PROOF_VERIFIER_ADDRESS where [simp]: "PROOF_VERIFIER_ADDRESS = 700"

definition init :: "uint256 \<Rightarrow> Contracts" where
  "init L1ChainId = 
    (let originalState = ERC20Constructor;
         mintedState = ERC20Constructor;
         tokenPairsState = TokenPairsConstructor;
         tokenPairsState = addTokenPair tokenPairsState TOKEN_ADDRESS MINTED_ADDRESS;
         proofVerifierState = ();
         bridgeState = BridgeStateConstructor PROOF_VERIFIER_ADDRESS TOKEN_PAIRS_ADDRESS STATE_ORACLE_ADDRESS;
         (status, bridgeState) = setTokenDepositAddress bridgeState TOKEN_DEPOSIT_ADDRESS;
         StateOracleState = StateOracleConstructor L1ChainId [];
         tokenDepositState = TokenDepositConstructor PROOF_VERIFIER_ADDRESS BRIDGE_ADDRESS TOKEN_PAIRS_ADDRESS STATE_ORACLE_ADDRESS;
         contracts = ContractsConstructor;
         contracts = setERC20State contracts TOKEN_ADDRESS originalState;
         contracts = setERC20State contracts MINTED_ADDRESS mintedState;
         contracts = setTokenPairsState contracts TOKEN_PAIRS_ADDRESS tokenPairsState;
         contracts = setProofVerifierState contracts PROOF_VERIFIER_ADDRESS proofVerifierState;
         contracts = setBridgeState contracts BRIDGE_ADDRESS bridgeState;
         contracts = setStateOracleState contracts STATE_ORACLE_ADDRESS StateOracleState;
         contracts = setTokenDepositState contracts TOKEN_DEPOSIT_ADDRESS tokenDepositState
      in contracts)"


inductive reachableFrom :: "Contracts \<Rightarrow> Contracts \<Rightarrow> Step list \<Rightarrow> bool" where
  reachableFrom_base: "\<And> contracts. reachableFrom contracts contracts []"
| reachableFrom_step: "\<And> contracts contracts' blockNum block step. 
                       \<lbrakk>reachableFrom contracts contracts' steps; 
                        executeStep contracts' blockNum block step = (Success, contracts'')\<rbrakk> \<Longrightarrow> 
                        reachableFrom contracts contracts'' (step # steps)" 

lemma reachableFromITokenPairs [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "ITokenPairs contracts' = ITokenPairs contracts"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

lemma reachableFromIProofVerifier [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "IProofVerifier contracts' = IProofVerifier contracts"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed


lemma reachableFromBridgeDeposit [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "BridgeState.deposit (the (bridgeState contracts' address)) = 
         BridgeState.deposit (the (bridgeState contracts address))"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed


lemma reachableFromBridgeTokenPairs [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "BridgeState.tokenPairs (the (bridgeState contracts' address)) = 
         BridgeState.tokenPairs (the (bridgeState contracts address))"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromBridgeStateOracle [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "BridgeState.stateOracle (the (bridgeState contracts' address)) = 
         BridgeState.stateOracle (the (bridgeState contracts address))"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next   
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromBridgeProofVerifier [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "BridgeState.proofVerifier (the (bridgeState contracts' address)) = 
         BridgeState.proofVerifier (the (bridgeState contracts address))"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  qed
qed

lemma reachableFromDepositStateOracle [simp]:
  assumes "reachableFrom contracts contracts' steps"
  shows "TokenDepositState.stateOracle (the (tokenDepositState contracts' address)) =
         TokenDepositState.stateOracle (the (tokenDepositState contracts address))"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by (cases "address \<noteq> address'") auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by auto
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by auto
  qed
qed

lemma reachableFromBridgeState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "bridgeState contracts address \<noteq> None"
  shows "bridgeState contracts' address \<noteq> None"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    using callClaimBridgeState[of contracts'] callClaimOtherAddress
    by (cases step, simp, metis executeStep.simps(2), simp)
qed

lemma reachableFromTokenDepositState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "tokenDepositState contracts address \<noteq> None"
  shows "tokenDepositState contracts' address \<noteq> None"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, metis callDepositOtherAddress callDepositE executeStep.simps(1), auto)
qed

lemma reachableFromERC20State:
  assumes "reachableFrom contracts contracts' steps"
  assumes "ERC20state contracts token \<noteq> None"
  shows "ERC20state contracts' token \<noteq> None"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof(cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step callDepositERC20state(2)
      by (cases "token = token'") auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by (simp add: callClaimERC20state)
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  qed
qed






text \<open>Just a simple experiment - prove that some trivial property is preserved across reachable states.
      Original to minted token mapping is never changed.\<close>
lemma reachableFromOriginalToMinted:
  assumes "reachableFrom contracts contracts' steps" 
        "callOriginalToMinted contracts tokenPairsAddr original = (Success, minted)"
  shows "callOriginalToMinted contracts' tokenPairsAddr original = (Success, minted)"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address caller ID token amount)
    then show ?thesis 
      using reachableFrom_step
      unfolding callOriginalToMinted_def
      by (simp add: Let_def split: option.splits prod.splits if_split_asm)
  next
    case (CLAIM address caller ID token amount "proof")
    then show ?thesis
      using reachableFrom_step
      unfolding callOriginalToMinted_def
      by (simp add: Let_def split: option.splits prod.splits if_split_asm)
  next 
    case (UPDATE address stateRoot)
    then show ?thesis
      using reachableFrom_step
      unfolding callOriginalToMinted_def
      by simp
  qed 
qed


text \<open>A more interesting property - there are no double claims\<close>
lemma callClaimNoDouble':
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
          "reachableFrom contracts' contracts'' steps"
        shows "fst (callClaim contracts'' address msg' ID token' amount' proof') \<noteq> Success"
proof-
  define state' where "state' = the (bridgeState contracts' address)"
  have "getClaim state' ID = True"
    using assms
    by (simp add: callClaimWritesClaim state'_def)
  then have *: "getClaim (the (bridgeState contracts' address)) ID = True"
    using state'_def
    by simp
  from \<open>reachableFrom contracts' contracts'' steps\<close>
  have "getClaim (the (bridgeState contracts'' address)) ID = True"
    using *
  proof (induction contracts' contracts'' steps rule: reachableFrom.induct)
    case (reachableFrom_base contracts')
    then show ?case 
      by simp
  next
    case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
    show ?case
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      then show ?thesis
        using reachableFrom_step
        by simp
    next 
      case (UPDATE address' stateRoot')
      then show ?thesis
        using reachableFrom_step
        by simp
    next
      case (CLAIM address' caller' ID' token' amount' proof')
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
  assumes "reachableFrom contracts contracts' steps"
  assumes "h \<noteq> 0"
  assumes "getDeposit (the (tokenDepositState contracts address)) ID = h"
  shows "getDeposit (the (tokenDepositState contracts' address)) ID = h"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (DEPOSIT address' caller' ID' token' amount')
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
          using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> address\<close> callDepositWrittenHash
          by (metis executeStep.simps(1) fst_conv)
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

text \<open>Once written claim entry cannot be unset\<close>
lemma reachableFromGetClaim:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getClaim (the (bridgeState contracts address)) ID = True"
  shows "getClaim (the (bridgeState contracts' address)) ID = True"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step callClaimPreservesTrueClaim callClaimOtherAddress
      by (metis executeStep.simps(2))
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step
      by simp
  next
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step
      by simp
  qed
qed


text \<open>Conditions that are necessary for bridge functioning (address memorized in contracts should be
      synchronized and all constructors must have been called)\<close>
definition properSetup :: "Contracts \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> bool" where
  "properSetup contracts tokenDepositAddress bridgeAddress token = 
    (let stateTokenDeposit = tokenDepositState contracts tokenDepositAddress;
         stateBridge = bridgeState contracts bridgeAddress;
         stateTokenPairs = tokenPairsState contracts (BridgeState.tokenPairs (the stateBridge))
      in stateTokenDeposit \<noteq> None \<and>
         stateBridge \<noteq> None \<and>
         BridgeState.deposit (the stateBridge) = tokenDepositAddress \<and>
         TokenDepositState.bridge (the stateTokenDeposit) = bridgeAddress \<and>
         TokenDepositState.stateOracle (the stateTokenDeposit) =
         BridgeState.stateOracle (the stateBridge) \<and>
         TokenDepositState.tokenPairs (the stateTokenDeposit) =
         BridgeState.tokenPairs (the stateBridge) \<and>
         stateOracleState contracts (BridgeState.stateOracle (the stateBridge)) \<noteq> None \<and>
         proofVerifierState contracts (BridgeState.proofVerifier (the stateBridge)) \<noteq> None \<and>
         tokenPairsState contracts (BridgeState.tokenPairs (the stateBridge)) \<noteq> None \<and>
         ERC20state contracts token \<noteq> None \<and>
         getMinted (the stateTokenPairs) token \<noteq> 0 \<and>
         ERC20state contracts (getMinted (the stateTokenPairs) token) \<noteq> None)"


lemma properSetup_stateOracleAddress:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
  shows "TokenDepositState.stateOracle (the (tokenDepositState contracts tokenDepositAddress)) = 
         BridgeState.stateOracle (the (bridgeState contracts bridgeAddress))"
  using assms
  unfolding properSetup_def
  by (simp add: Let_def)

lemma properSetup_getLastState:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
  shows "getLastStateB contracts bridgeAddress = getLastStateTD contracts tokenDepositAddress"
  using assms
  by (simp add: properSetup_stateOracleAddress)

lemma properSetupInit:
  shows "properSetup (init L1ChainId) TOKEN_DEPOSIT_ADDRESS BRIDGE_ADDRESS TOKEN_ADDRESS"
  unfolding properSetup_def init_def Let_def lookupNat_def
  by (auto simp add: lookup_default_update setTokenDepositAddress_def BridgeStateConstructor_def TokenDepositConstructor_def TokenPairsConstructor_def addTokenPair_def split: prod.splits)

lemma callDepositProperSetup [simp]:
  assumes "callDeposit contracts address block msg ID token amount = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  by (smt (verit, best) callDepositBridge callDepositStateOracle callDepositE callDepositERC20state(2) callDepositIBridge callDepositIProofVerifier callDepositIStateOracle callDepositITokenPairs callDepositOtherAddress callDepositOtherToken callDepositTokenPairs properSetup_def)

lemma callClaimProperSetup [simp]:
  assumes "callClaim contracts address msg ID token amount proof = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
  by (smt (verit, best) ProofVerifier.callClaimOtherAddress ProofVerifier.callClaimTokenPairs ProofVerifier_axioms callClaimBridgeState(2) callClaimDeposit callClaimERC20state callClaimIProofVerifier callClaimIStateOracle callClaimITokenDeposit callClaimITokenPairs callClaimProofVerifier callClaimStateOracle properSetup_def)

lemma callUpdateProperSetup [simp]:
  assumes "callUpdate contracts address block blockNum stateRoot = (Success, contracts')"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows  "properSetup contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms unfolding callUpdate_def update_def properSetup_def
  by (auto simp add: Let_def lookup_update' split: option.splits prod.splits if_split_asm)

lemma properSetupReachable:
  assumes "reachableFrom contracts contracts' steps"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress tokenAddress"
  shows "properSetup contracts' tokenDepositAddress bridgeAddress tokenAddress"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (cases step, auto)
qed

text \<open>State root is never zero in an update\<close>
definition updatesNonZero where
  "updatesNonZero steps \<longleftrightarrow> 
     (\<forall> address stateRoot. UPDATE address stateRoot \<in> set steps \<longrightarrow> stateRoot \<noteq> 0)"

lemma updatesNonZero:
  assumes "updatesNonZero (step # steps)"
  shows "updatesNonZero steps" "\<forall> address stateRoot. step = UPDATE address stateRoot \<longrightarrow> stateRoot \<noteq> 0"
  using assms
  unfolding updatesNonZero_def
  by auto

lemma reachableFromStateRootNonZero:
  assumes "reachableFrom contracts contracts' steps" "updatesNonZero steps"
  assumes "lastState (the (stateOracleState contracts address)) \<noteq> 0"
  shows "lastState (the (stateOracleState contracts' address)) \<noteq> 0"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step updatesNonZero
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachableFrom_step updatesNonZero
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step updatesNonZero[of step steps]
      by (metis callUpdateLastState callUpdateOtherAddress executeStep.simps(3))
  qed
qed


text \<open>After a successful deposit and a state update a claim can be made\<close>
lemma claimPossibleAfterDepositAndUpdate:
  assumes "callDeposit contracts tokenDepositAddress block msg ID token amount = (Success, contractsD)"
  assumes "reachableFrom contractsD contractsD' steps"
  assumes "stateRoot = generateStateRoot contractsD'"
  assumes "proof = generateDepositProof contractsD' ID"
  assumes "callUpdate contractsD' (TokenDepositState.stateOracle (the (tokenDepositState contractsD' tokenDepositAddress))) block blockNum stateRoot = (Success, contractsU)"

  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"

  assumes "getClaim (the (bridgeState contractsU bridgeAddress)) ID = False"
  assumes "sender msg' = sender msg"

  assumes "hash (sender msg) token amount \<noteq> 0" (* ADDITIONAL PREMISE *)

  shows "\<exists> contractsC. callClaim contractsU bridgeAddress msg' ID token amount proof = (Success, contractsC)"
proof-
  define stateOracleAddress where 
       "stateOracleAddress = BridgeState.stateOracle (the (bridgeState contracts bridgeAddress))"
  define proofVerifierAddress where 
       "proofVerifierAddress = BridgeState.proofVerifier (the (bridgeState contracts bridgeAddress))"
  define tokenPairsAddress where 
       "tokenPairsAddress = BridgeState.tokenPairs (the (bridgeState contracts bridgeAddress))"

  have "verifyDepositProof () tokenDepositAddress ID (hash (sender msg) token amount) stateRoot proof = True"
  proof (rule verifyDepositProofI)
    show "generateDepositProof contractsD' ID = proof"
      using assms
      by simp
  next
    show "generateStateRoot contractsD' = stateRoot"
      using assms
      by simp
  next
    have "tokenDepositState contractsD tokenDepositAddress \<noteq> None"
      using assms(1)
      by (auto simp add: callDeposit_def Let_def split: option.splits prod.splits if_split_asm)
    then have "tokenDepositState contractsD' tokenDepositAddress \<noteq> None"
      using \<open>reachableFrom contractsD contractsD' steps\<close>
      using reachableFromTokenDepositState by blast
    then show "tokenDepositState contractsD' tokenDepositAddress = Some (the (tokenDepositState contractsD' tokenDepositAddress))"
      by simp
  next
    show "getDeposit (the (tokenDepositState contractsD' tokenDepositAddress)) ID = hash (sender msg) token amount"
      using callDepositWritesHash assms \<open>reachableFrom contractsD contractsD' steps\<close> \<open>hash (sender msg) token amount \<noteq> 0\<close>
      using reachableFromGetDeposit
      by blast
  qed

  have "bridgeState contractsU bridgeAddress \<noteq> None"
    using reachableFromBridgeState assms
    unfolding properSetup_def
    by (auto simp add: Let_def)
  then obtain stateBridgeU where 
    "bridgeState contractsU bridgeAddress = Some stateBridgeU"
    by auto
  then have stateBridgeU: "stateBridgeU = the (bridgeState contractsU bridgeAddress)"
    using \<open>bridgeState contractsU bridgeAddress \<noteq> None\<close>
    by auto

  have "TokenDepositState.stateOracle (the (tokenDepositState contractsU tokenDepositAddress)) =
        stateOracleAddress"
    using assms stateOracleAddress_def properSetup_def
    by (auto simp add: Let_def)

  have "BridgeState.stateOracle stateBridgeU = stateOracleAddress"
       "BridgeState.proofVerifier stateBridgeU = proofVerifierAddress"
       "BridgeState.deposit stateBridgeU = tokenDepositAddress"
       "tokenPairsState contractsU (BridgeState.tokenPairs stateBridgeU) \<noteq> None"
    using assms stateBridgeU \<open>bridgeState contractsU bridgeAddress \<noteq> None\<close> properSetup_def stateOracleAddress_def proofVerifierAddress_def
    by (auto simp add: Let_def)

  then obtain stateTokenPairs where
    stateTokenPairs: "tokenPairsState contractsU (BridgeState.tokenPairs stateBridgeU) = Some stateTokenPairs"
    by auto

  have "StateOracleState.lastState (the (stateOracleState contractsU stateOracleAddress)) = stateRoot"
    using assms \<open>TokenDepositState.stateOracle (the (tokenDepositState contractsU tokenDepositAddress)) =
        stateOracleAddress\<close>
    by simp

  have "fst (callClaim contractsU bridgeAddress msg' ID token amount proof) = Success"
  proof (rule callClaimI)
    show "bridgeState contractsU bridgeAddress = Some stateBridgeU"
      by fact
  next
    show "verifyDepositProof () (BridgeState.deposit stateBridgeU) ID (hash (sender msg') token amount)  
          (StateOracleState.lastState (the (stateOracleState contractsU (BridgeState.stateOracle stateBridgeU)))) proof"
      using \<open>BridgeState.deposit stateBridgeU = tokenDepositAddress\<close>
      using \<open>bridgeState contractsU bridgeAddress = Some stateBridgeU\<close>
      using \<open>BridgeState.stateOracle stateBridgeU = stateOracleAddress\<close>
      using \<open>StateOracleState.lastState (the (stateOracleState contractsU stateOracleAddress)) = stateRoot\<close>
      using \<open>verifyDepositProof () tokenDepositAddress ID (hash (sender msg) token amount) stateRoot proof = True\<close>
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
    using callUpdateStateOracleState assms
    using \<open>TokenDepositState.stateOracle (the (tokenDepositState contractsU tokenDepositAddress)) =
        stateOracleAddress\<close>
    by auto
  next
    show "proofVerifierState contractsU (BridgeState.proofVerifier stateBridgeU) \<noteq> None"
      using \<open>BridgeState.proofVerifier stateBridgeU = proofVerifierAddress\<close> 
            stateBridgeU 
      using assms
      using callDepositIProofVerifier callUpdateIProofVerifier reachableFromIProofVerifier
      unfolding proofVerifierAddress_def properSetup_def
      by metis
    show "getMinted stateTokenPairs token \<noteq> 0"
      using stateTokenPairs assms stateBridgeU
      unfolding properSetup_def
      by (auto simp add: Let_def)
  next
    show "ERC20state contractsU (getMinted stateTokenPairs token) \<noteq> None"
      using assms
      unfolding properSetup_def
      by (smt (verit, best) callDepositERC20state(2) callDepositIBridge callDepositITokenPairs callDepositOtherToken callUpdateIBridge callUpdateIERC20 callUpdateITokenPairs option.sel reachableFromBridgeTokenPairs reachableFromERC20State reachableFromITokenPairs stateBridgeU stateTokenPairs)
  next
    show "getClaim stateBridgeU ID = False"
      using \<open>bridgeState contractsU bridgeAddress = Some stateBridgeU\<close> assms 
      by auto
  qed
  then show ?thesis
    by (metis eq_fst_iff)
qed


lemma hashWrittenOnlyByDeposit:
  assumes "reachableFrom contracts contracts' steps"
  assumes "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = 0"
  assumes "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = hash caller token amount"
  assumes "hash caller token amount \<noteq> 0"
  (* EXPLOIT? *)
  assumes hash_inj: "\<And> caller caller' amount amount' token token'. 
                      hash caller token amount = hash caller' token' amount' \<Longrightarrow> 
                      token = token' \<and> caller = caller' \<and> amount = amount'"
  shows "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  show False
    using assms(1-4) *
  proof (induction contracts contracts' steps rule: reachableFrom.induct)
    case (reachableFrom_base contracts)
    then show ?case
      by simp
  next
    case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
    show ?case
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' \<noteq> tokenDepositAddress")
        case True
        then show ?thesis
          using DEPOSIT reachableFrom_step callDepositOtherAddress[OF True[symmetric]]
          by simp
      next
        case False
        show ?thesis
        proof (cases "ID \<noteq> ID'")
          case True
          then show ?thesis
            using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close> callDepositOtherID
            by simp
        next
          case False
          then have "getDeposit (the (tokenDepositState contracts'' tokenDepositAddress)) ID =
                     hash caller' token' amount'"
            using DEPOSIT reachableFrom_step \<open>\<not> address' \<noteq> tokenDepositAddress\<close> callDepositWritesHash
            by (auto simp add: message_def)
          then have "hash caller token amount = hash caller' token' amount'"
            using reachableFrom_step
            by auto
          then have "caller = caller'" "token = token'" "amount = amount'"
            using hash_inj
            by blast+
          then show False
            using DEPOSIT reachableFrom_step \<open>\<not> ID \<noteq> ID'\<close>
            by auto
        qed
      qed
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        by auto
    next
      case (UPDATE address' stateRoot')
      then show ?thesis
        using reachableFrom_step
        by auto
    qed
  qed
qed

lemma updateHappened:
  assumes "reachableFrom contracts contracts' steps"
  assumes "StateOracleState.lastState (the (stateOracleState contracts address)) \<noteq> 
           StateOracleState.lastState (the (stateOracleState contracts' address))"
  shows "\<exists> contractsU contractsU' block blockNum steps1 steps2 stateRoot. 
                       reachableFrom contracts contractsU steps1 \<and> 
                       stateRoot = generateStateRoot contractsU \<and>
                       callUpdate contractsU address block blockNum stateRoot = (Success, contractsU') \<and>
                       reachableFrom contractsU' contracts' steps2 \<and>
                       (\<nexists> stateRoot'. UPDATE address stateRoot' \<in> set steps2)"
using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
  next
    case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
    show ?case
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      then show ?thesis
        using reachableFrom_step
        by (metis callDepositIStateOracle Step.simps(6) executeStep.simps(1) reachableFrom.reachableFrom_step set_ConsD)
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        by (metis callClaimIStateOracle Step.simps(8) executeStep.simps(2) reachableFrom.reachableFrom_step set_ConsD)
    next
      case (UPDATE address' stateRoot')
      then have *: "stateRoot' = generateStateRoot contracts'"
        using reachableFrom_step updateSuccess
        by simp
      show ?thesis
      proof (cases "address = address'")
        case True
        then show ?thesis
            using reachableFrom_step.hyps UPDATE *
            using reachableFrom_base 
            by (rule_tac x="contracts'" in exI, rule_tac x="contracts''" in exI, force)
        next
          case False
          then show ?thesis
            using reachableFrom_step UPDATE callUpdateOtherAddress
            by (smt (verit, best) Step.simps(3) executeStep.simps(3) reachableFrom.reachableFrom_step set_ConsD)
        qed
    qed
qed

lemma noUpdateLastState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<nexists> stateRoot. UPDATE address stateRoot \<in> set steps"
  shows "StateOracleState.lastState (the (stateOracleState contracts address)) =  
         StateOracleState.lastState (the (stateOracleState contracts' address))"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
  next
    case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
    show ?case
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      then show ?thesis
        using reachableFrom_step
        by simp
    next
      case (CLAIM address' calller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        by simp
    next
      case (UPDATE address' stateRoot')
      then have "address \<noteq> address'"
        using reachableFrom_step.prems by auto
      then show ?thesis
        by (metis UPDATE callUpdateOtherAddress executeStep.simps(3) list.set_intros(2) reachableFrom_step.IH reachableFrom_step.hyps(2) reachableFrom_step.prems)
    qed
qed

lemma callClaimGetDeposit:
  assumes "reachableFrom initContracts contracts steps"
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token"
  assumes "getLastStateB initContracts bridgeAddress = 0"
  assumes "getLastStateB contracts bridgeAddress \<noteq> 0"
  assumes claim: "callClaim contracts bridgeAddress msg ID token amount proof = (Success, contracts')"
  assumes "hash (sender msg) token amount \<noteq> 0"
  shows "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = hash (sender msg) token amount"
proof-
  define stateBridge where "stateBridge = the (bridgeState contracts bridgeAddress)"
  define stateStateOracle where "stateStateOracle = the (stateOracleState contracts (BridgeState.stateOracle stateBridge))"

  obtain stateRoot where stateLast: "callLastState contracts (BridgeState.stateOracle stateBridge) = (Success, stateRoot)"
    using claim
    by (metis callClaimCallLastState stateBridge_def)
  then have 1: "StateOracleState.lastState stateStateOracle = stateRoot"
    unfolding stateStateOracle_def
    using callLastState 
    by blast

  have "BridgeState.deposit stateBridge = tokenDepositAddress"
    using assms
    unfolding stateBridge_def properSetup_def Let_def
    by auto

  have *: "BridgeState.stateOracle stateBridge = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))"
    using assms(1)
    unfolding stateBridge_def
    by simp

  have "stateRoot \<noteq> 0"
    using 1 assms stateBridge_def stateStateOracle_def by blast
  then have 2: "StateOracleState.lastState (the (stateOracleState initContracts (BridgeState.stateOracle stateBridge))) \<noteq> stateRoot"
    using * assms
    by simp

  obtain contractsU contractsU' block blockNum steps1 steps2 stateRoot' where
      "reachableFrom initContracts contractsU steps1"
      "stateRoot' = generateStateRoot contractsU"
      "callUpdate contractsU (BridgeState.stateOracle stateBridge) block blockNum stateRoot' =
       (Success, contractsU')"
      "reachableFrom contractsU' contracts steps2"
      "\<nexists> stateRoot''. UPDATE (BridgeState.stateOracle stateBridge) stateRoot'' \<in> set steps2"
    using updateHappened assms(1) stateLast 1 2
    unfolding stateStateOracle_def
    by meson

  have 3: "StateOracleState.lastState (the (stateOracleState contractsU' (BridgeState.stateOracle stateBridge))) =
           StateOracleState.lastState (the (stateOracleState contracts (BridgeState.stateOracle stateBridge)))"
    using \<open>reachableFrom contractsU' contracts steps2\<close>
          \<open>\<nexists> stateRoot''. UPDATE (BridgeState.stateOracle stateBridge) stateRoot'' \<in> set steps2\<close>
    using noUpdateLastState
    by simp

  have "stateRoot = stateRoot'"
    by (metis "1" "3" \<open>callUpdate contractsU (BridgeState.stateOracle stateBridge) block blockNum stateRoot' = (Success, contractsU')\<close> callUpdateLastState stateStateOracle_def)

  have "callVerifyDepositProof contracts (BridgeState.proofVerifier stateBridge) (BridgeState.deposit stateBridge) ID (hash (sender msg) token amount) 
         stateRoot proof = Success"
    using callClaimCallVerifyProof[OF claim] 1
    unfolding stateBridge_def Let_def stateStateOracle_def
    by blast
  then have *: "verifyDepositProof () (BridgeState.deposit stateBridge) ID (hash (sender msg) token amount) stateRoot proof = True"
    unfolding callVerifyDepositProof_def
    by (simp split: option.splits if_split_asm)
  have "getDeposit (the (tokenDepositState contractsU tokenDepositAddress)) ID =
        hash (sender msg) token amount"
  proof (rule verifyDepositProofE[OF _  *])
    show "generateStateRoot contractsU = stateRoot"
      using \<open>stateRoot' = generateStateRoot contractsU\<close> \<open>stateRoot = stateRoot'\<close>
      by simp
  next
    have "tokenDepositState contractsU (BridgeState.deposit stateBridge) \<noteq> None"
      using \<open>properSetup initContracts tokenDepositAddress bridgeAddress token\<close>
      using \<open>BridgeState.deposit stateBridge = tokenDepositAddress\<close>
      using \<open>reachableFrom initContracts contractsU steps1\<close> 
      using reachableFromTokenDepositState
      by (metis properSetup_def)
    then show "tokenDepositState contractsU (BridgeState.deposit stateBridge) =
          Some (the (tokenDepositState contractsU tokenDepositAddress))"
      using \<open>BridgeState.deposit stateBridge = tokenDepositAddress\<close>
      by simp
  qed
  then have "getDeposit (the (tokenDepositState contractsU' tokenDepositAddress)) ID =
        hash (sender msg) token amount"
    using \<open>callUpdate contractsU (BridgeState.stateOracle stateBridge) block blockNum stateRoot' =
       (Success, contractsU')\<close>
    by simp
  then show ?thesis
    using \<open>hash (sender msg) token amount \<noteq> 0\<close> \<open>reachableFrom contractsU' contracts steps2\<close>
    using reachableFromGetDeposit 
    by blast
qed

text \<open>There was at least one update and no updates set zero state\<close>
lemma lastStateNonZero:
  assumes "reachableFrom initContracts contracts steps"
  assumes "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress)) 
            in UPDATE stateOracleAddress stateRoot \<in> set steps"
  assumes "updatesNonZero steps"
  shows "getLastStateB contracts bridgeAddress \<noteq> 0"
  using assms
proof (induction initContracts contracts steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "step = (let stateOracleAddress = BridgeState.stateOracle (the (bridgeState contracts bridgeAddress)) 
            in UPDATE stateOracleAddress stateRoot)")
    case True
    then show ?thesis
      using reachableFrom_step updatesNonZero_def 
      by (auto simp add: Let_def)
  next
    case False
    then have *: "getLastStateB contracts' bridgeAddress \<noteq> 0"
      using reachableFrom_step updatesNonZero
       by auto
    show "getLastStateB contracts'' bridgeAddress \<noteq> 0"
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      then show ?thesis
        using reachableFrom_step *
        by simp
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      then show ?thesis
        using * reachableFrom_step
        by (cases "bridgeAddress = address'", auto)
    next
      case (UPDATE address' stateRoot')
      then have "stateRoot' \<noteq> 0"
        using reachableFrom_step.prems updatesNonZero
        by blast
      then show ?thesis
        using * reachableFrom_step UPDATE
        by (metis (mono_tags, lifting) callUpdateIBridge callUpdateLastState callUpdateOtherAddress executeStep.simps(3))
    qed
  qed
qed

lemma depositBeforeClaim:
  assumes "reachableFrom initContracts contracts steps"
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token"
  assumes "getDeposit (the (tokenDepositState initContracts tokenDepositAddress)) ID = 0"
  assumes "getLastStateB initContracts bridgeAddress = 0"
  assumes "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in UPDATE stateOracleAddress stateRoot \<in> set steps"
  assumes "updatesNonZero steps"
  assumes "callClaim contracts bridgeAddress msg ID token amount proof = (Success, contracts')"
  (* EXPLOIT? *)
  assumes "hash (sender msg) token amount \<noteq> 0"
  assumes hash_inj: "\<And> caller caller' amount amount' token token'. 
                      hash caller token amount = hash caller' token' amount' \<Longrightarrow> 
                      token = token' \<and> caller = caller' \<and> amount = amount'"
  shows "DEPOSIT tokenDepositAddress (sender msg) ID token amount \<in> set steps"
proof-
  have "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = hash (sender msg) token amount"
    using assms callClaimGetDeposit lastStateNonZero
    by metis
  then show ?thesis
    using hashWrittenOnlyByDeposit
    using assms
    by blast
qed


lemma onlyDepositorCanClaim:
  assumes "reachableFrom initContracts contracts steps"
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token'"
  assumes "getLastStateB initContracts bridgeAddress = 0"

  assumes "val msg = amount"
  assumes "hash (sender msg') token' amount' \<noteq> 0"
  assumes hash_inj: "\<And> caller caller' amount amount' token token'. 
                      hash caller token amount = hash caller' token' amount' \<Longrightarrow> 
                      token = token' \<and> caller = caller' \<and> amount = amount'"

  assumes "getLastStateB contracts' bridgeAddress \<noteq> 0"

  assumes deposit: "callDeposit contracts tokenDepositAddress block msg ID token amount = (Success, contracts')"
  assumes claim: "callClaim contracts' bridgeAddress msg' ID token' amount' proof = (Success, contracts'')"

  shows "sender msg = sender msg'" "token = token'" "amount = amount'"
proof-
  have "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = hash (sender msg) token amount"
    using callDepositWritesHash deposit
    by simp
  moreover
  obtain blockNum where "executeStep contracts blockNum block (DEPOSIT tokenDepositAddress (sender msg) ID token amount) = (Success, contracts')"
    using \<open>val msg = amount\<close> deposit
    by (cases msg, auto simp add: message_def)
  then have *: "reachableFrom initContracts contracts' (DEPOSIT tokenDepositAddress (sender msg) ID token amount # steps)"
    using reachableFrom_step[OF assms(1)]
    by auto
  then have "getDeposit (the (tokenDepositState contracts' tokenDepositAddress)) ID = hash (sender msg') token' amount'"
    using callClaimGetDeposit assms
    by blast
  ultimately
  have "hash (sender msg) token amount = hash (sender msg') token' amount'"
    by simp
  then show "sender msg = sender msg'" "token = token'" "amount = amount'"
    using hash_inj
    by blast+    
qed

(* ----------------------------------------------------------------------------- *)

lemma getDeadStatusDeadState:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
  assumes "getLastStateB contracts bridgeAddress \<noteq> 0"
  assumes "getDeadStatus contracts (the (tokenDepositState contracts tokenDepositAddress))  block = 
           (Success, True, state)"
  shows "deadState state > 0"
proof-
  have "TokenDepositState.stateOracle (the (tokenDepositState contracts tokenDepositAddress)) = 
        BridgeState.stateOracle (the (bridgeState contracts bridgeAddress))"
    using \<open>properSetup contracts tokenDepositAddress bridgeAddress token\<close>
    unfolding properSetup_def
    by (simp add: Let_def)
  then show ?thesis
    using \<open>getDeadStatus contracts (the (tokenDepositState contracts tokenDepositAddress))  block = (Success, True, state)\<close>
    using \<open>getLastStateB contracts bridgeAddress \<noteq> 0\<close>
    by (metis assms(2) assms(3) deadStatusTrueDeadState neq0_conv)
qed

lemma getDeadStatusDeadStateOneUpdate:
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token"
  assumes "reachableFrom initContracts contracts steps"
  \<comment> \<open>at least one update happend\<close>
  assumes "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in UPDATE stateOracleAddress stateRoot \<in> set steps"
  \<comment> \<open>updates never set zero state\<close>
  assumes "updatesNonZero steps"
  \<comment> \<open>the bridge became dead\<close>
  assumes "getDeadStatus contracts (the (tokenDepositState contracts tokenDepositAddress)) block = 
           (Success, True, state)"
  \<comment> \<open>deadState is set\<close>
  shows "deadState state > 0"
  using assms
  using getDeadStatusDeadState lastStateNonZero properSetupReachable
  by blast

lemma deadStateGetDeadStatus:
  assumes "deadState state > 0"
  shows "getDeadStatus contracts state block = (Success, True, state)"
  using assms
  unfolding getDeadStatus_def
  by simp

text \<open>Dead state is never unset\<close>
lemma deadStateRemains:
  assumes "reachableFrom contracts contracts' steps"
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then have *: "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
    using updatesNonZero
    by simp
  then show ?case
    using reachableFrom_step.hyps(2)
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using reachableFrom_step *
      by (metis callDepositInDeadState executeStep.simps(1))
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using * reachableFrom_step
      by simp
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachableFrom_step *
      by simp
  qed
qed

text \<open>No deposit after the bridge dies\<close>
lemma  noDepositBridgeDead:
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) \<noteq> 0"
  assumes "reachableFrom contracts contracts' steps"
  shows "fst (callDeposit contracts' tokenDepositAddress block msg ID token amount) \<noteq> Success"
  using assms deadStateRemains callDepositFailsInDeadState
  by blast

text \<open>Cancel only when the bridge is dead\<close>
lemma cancelDepositBridgeIsDead:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
  assumes "getLastStateB contracts bridgeAddress \<noteq> 0"
  assumes "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof = (Success, contracts')"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
  using assms getDeadStatusDeadState[OF assms(1-2)]
  unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
  by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

lemma cancelDepositOnlyAfterDeposit:
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token"
  assumes "getDeposit (the (tokenDepositState initContracts tokenDepositAddress)) ID = 0"
  assumes "reachableFrom initContracts contracts steps"
  assumes cancel: "callCancelDepositWhileDead contracts tokenDepositAddress msg block ID token amount proof = (Success, contracts')"
  (* EXPLOIT? *)
  assumes "hash (sender msg) token amount \<noteq> 0"
  assumes hash_inj: "\<And> caller caller' amount amount' token token'. 
                      hash caller token amount = hash caller' token' amount' \<Longrightarrow> 
                      token = token' \<and> caller = caller' \<and> amount = amount'"
  shows "DEPOSIT tokenDepositAddress (sender msg) ID token amount \<in> set steps"
proof-
  have "getDeposit (the (tokenDepositState contracts tokenDepositAddress)) ID = hash (sender msg) token amount"
    using cancel
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def
    by (simp add: Let_def split: option.splits prod.splits if_split_asm)
  then show ?thesis
    using assms hashWrittenOnlyByDeposit
    by blast
qed


(* ----------------------------------------------------------------- *)

lemma callDepositSetsDeadState:
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
  assumes "callLastState contracts (BridgeState.stateOracle (the (bridgeState contracts bridgeAddress))) =
          (Success, stateRoot)"
  assumes "callDeposit contracts tokenDepositAddress block msg ID token' amount = (Success, contracts')"
  assumes "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = stateRoot"
proof-
  have "getLastStateTD contracts tokenDepositAddress = stateRoot"
    using assms
    by (metis callLastState properSetup_stateOracleAddress)
  then show ?thesis
    using \<open>callDeposit contracts tokenDepositAddress block msg ID token' amount = (Success, contracts')\<close>
    using \<open>deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0\<close>
    using getDeadStatusFalse'
    unfolding callDeposit_def deposit_def
    by (auto split: option.splits prod.splits if_split_asm)
qed

lemma deadStateLastState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "properSetup contracts tokenDepositAddress bridgeAddress token"
  assumes noUpdate: "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState contracts bridgeAddress))
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps"
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) = 0"
  assumes "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0"
  assumes "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState contracts bridgeAddress))
            in callLastState contracts stateOracleAddress = (Success, stateRoot)"
  shows "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = stateRoot"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by blast
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
  proof (cases "deadState (the (tokenDepositState contracts' tokenDepositAddress)) \<noteq> 0")
    case True
    then show ?thesis
      using reachableFrom_step
      apply (cases step)
        apply (metis callDepositInDeadState executeStep.simps(1) list.set_intros(2))
       apply simp
      apply (metis callUpdateDeadState executeStep.simps(3) list.set_intros(2))
      done
  next
    case False
    show ?thesis
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' = tokenDepositAddress")
        case False
        then show ?thesis
          using reachableFrom_step
          by (metis DEPOSIT callDepositOtherAddress executeStep.simps(1) list.set_intros(2))
      next
        case True
        show ?thesis
        proof (rule callDepositSetsDeadState)
          show "properSetup contracts' tokenDepositAddress bridgeAddress token"
            using reachableFrom_step.prems reachableFrom_step.hyps
            using properSetupReachable by blast
        next
          show "callLastState contracts' (BridgeState.stateOracle (the (bridgeState contracts' bridgeAddress))) =
               (Success, stateRoot)"
            using reachableFrom_step.prems reachableFrom_step.hyps
            by (smt (verit, ccfv_threshold) noUpdateLastState callLastState callLastStateI list.set_intros(2) prod.exhaust_sel properSetupReachable properSetup_def reachableFromBridgeStateOracle)
        next
          show "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) \<noteq> 0"
            by fact
        next
          show "callDeposit contracts' tokenDepositAddress block (message caller' amount') ID' token' amount' =
                (Success, contracts'')"
            using reachableFrom_step DEPOSIT \<open>address' = tokenDepositAddress\<close>
            by simp
        qed
      qed
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      then show ?thesis
        using reachableFrom_step
        by simp
    next
      case (UPDATE address' stateRoot')
      then show ?thesis
        using reachableFrom_step
        by (metis False callUpdateDeadState executeStep.simps(3))
    qed
  qed
qed

text \<open>If cancel deposit succeeds, then the bridge is dead and there was no claim previous to the state
in which the bridge died\<close>
lemma cancelDepositNoClaim:
  assumes "properSetup initContracts tokenDepositAddress bridgeAddress token"
  assumes "reachableFrom initContracts contracts steps"
  \<comment> \<open>The last update that happened when the bridge was still alive\<close>
  assumes update:
          "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in callUpdate contracts stateOracleAddress block blockNum stateRoot = (Success, contracts')"
  assumes "stateRoot \<noteq> 0" (* Additional ssumption *)
  assumes "deadState (the (tokenDepositState contracts tokenDepositAddress)) = 0"

  \<comment> \<open>There were no updates since then\<close>
  assumes "reachableFrom contracts' contracts'' steps'"
  assumes noUpdate: "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))
            in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"

  \<comment> \<open>Cancel deposit succeded\<close>
  assumes cancel:
          "callCancelDepositWhileDead contracts'' tokenDepositAddress msg block' ID token amount proof = (Success, contracts''')"

  \<comment> \<open>Claim did not happen before that last update\<close>
  shows "\<nexists> proof. CLAIM bridgeAddress (sender msg) ID token amount proof \<in> set steps"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain p where *: "CLAIM bridgeAddress (sender msg) ID token amount p \<in> set steps"
    by auto
  have "getClaim (the (bridgeState contracts bridgeAddress)) ID = True"
    using \<open>reachableFrom initContracts contracts steps\<close> *
  proof (induction initContracts contracts steps rule: reachableFrom.induct)
    case (reachableFrom_base contracts)
    then show ?case
      by simp
  next
    case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
    show ?case
    proof (cases "step = CLAIM bridgeAddress (sender msg) ID token amount p")
      case True
      then show ?thesis
        using reachableFrom_step.hyps callClaimWritesClaim
        by simp
    next
      case False
      then show ?thesis
        using reachableFrom_step
        by (cases step,
            simp,
            metis callClaimOtherAddress callClaimPreservesTrueClaim executeStep.simps(2) set_ConsD,
            simp)
    qed
  qed

  moreover

  define stateBridge where "stateBridge = the (bridgeState contracts'' bridgeAddress)"
  define stateStateOracle where "stateStateOracle = the (stateOracleState contracts'' (BridgeState.stateOracle stateBridge))"
  define stateTokenDeposit where "stateTokenDeposit = the (tokenDepositState contracts'' tokenDepositAddress)"
  define stateTokenDeposit' where "stateTokenDeposit' = snd (snd (getDeadStatus contracts'' stateTokenDeposit block'))"

  have dB: "BridgeState.deposit stateBridge = tokenDepositAddress"
    using assms
    unfolding stateBridge_def properSetup_def Let_def
    by auto

  have bD: "TokenDepositState.bridge stateTokenDeposit = bridgeAddress"
    using assms
    unfolding stateTokenDeposit_def
    by (meson callUpdateProperSetup properSetupReachable properSetup_def)

  have sOB: "BridgeState.stateOracle stateBridge = BridgeState.stateOracle (the (bridgeState initContracts bridgeAddress))"
    using assms
    unfolding stateBridge_def
    by simp

  have "properSetup contracts' tokenDepositAddress bridgeAddress token"
    using assms
    by (meson callUpdateProperSetup properSetupReachable)

  from cancel
  obtain stateRoot' where
    lVS: "lastValidState contracts'' stateTokenDeposit' = (Success, stateRoot')" and
    vCP: "callVerifyClaimProof contracts'' (TokenDepositState.proofVerifier stateTokenDeposit') (bridge stateTokenDeposit') ID
          stateRoot' proof = Success" and
         "getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')"
    unfolding callCancelDepositWhileDead_def cancelDepositWhileDead_def stateTokenDeposit_def stateTokenDeposit'_def
    by (auto simp add: Let_def split: option.splits prod.splits if_split_asm)

  have "lastState stateStateOracle = stateRoot"
    using assms
    by (metis (no_types, lifting) callUpdateLastState noUpdateLastState sOB stateStateOracle_def)
  then have "getLastStateB contracts'' bridgeAddress = stateRoot"
    using stateBridge_def stateStateOracle_def
    by argo
  then have "getLastStateTD contracts'' tokenDepositAddress = stateRoot"
    using assms properSetup_stateOracleAddress update
    by auto

  have "stateRoot' = stateRoot"
  proof (cases "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) \<noteq> 0")
    case True
    have "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) = stateRoot"
    proof (rule deadStateLastState)
      show "reachableFrom contracts' contracts'' steps'"
        by fact
    next
      show "properSetup contracts' tokenDepositAddress bridgeAddress token" 
        by fact 
    next
      show "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState contracts' bridgeAddress))
             in \<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set steps'"
        using \<open>reachableFrom contracts' contracts'' steps'\<close>
        by (metis noUpdate reachableFromBridgeStateOracle sOB stateBridge_def)
    next
      show "deadState (the (tokenDepositState contracts' tokenDepositAddress)) = 0"
        using \<open>deadState (the (tokenDepositState contracts tokenDepositAddress)) = 0\<close> update
        using callUpdateDeadState
        by presburger
    next
      show "deadState (the (tokenDepositState contracts'' tokenDepositAddress)) \<noteq> 0"
        by fact
    next
      show "let stateOracleAddress = BridgeState.stateOracle (the (bridgeState contracts' bridgeAddress))
             in callLastState contracts' stateOracleAddress = (Success, stateRoot)"
        using \<open>properSetup contracts' tokenDepositAddress bridgeAddress token\<close> assms(6) 
        by (smt (verit, best) callLastState_def callUpdateLastState option.case_eq_if properSetup_def reachableFromBridgeStateOracle sOB stateBridge_def update)
    qed
    then show ?thesis
      using \<open>getLastStateB contracts'' bridgeAddress = stateRoot\<close> lVS True
      unfolding lastValidState_def
      by (metis \<open>getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')\<close> bot_nat_0.not_eq_extremum deadStateGetDeadStatus snd_conv stateTokenDeposit_def)
  next
    case False
    then show ?thesis
      using \<open>getLastStateB contracts'' bridgeAddress = stateRoot\<close> lVS
      unfolding lastValidState_def
      by (metis \<open>getDeadStatus contracts'' stateTokenDeposit block' = (Success, True, stateTokenDeposit')\<close> \<open>getLastStateTD contracts'' tokenDepositAddress = stateRoot\<close> assms(4) getDeadStatusSetsDeadState snd_conv stateTokenDeposit_def)
  qed

  from update have "generateStateRoot contracts = stateRoot"
    using updateSuccess
    by simp

  have "getClaim (the (bridgeState contracts bridgeAddress)) ID = False"
  proof (rule verifyClaimProofE)
    show "generateStateRoot contracts = stateRoot"
      by fact
  next
    show "verifyClaimProof () bridgeAddress ID stateRoot proof = True"
      using vCP bD \<open>stateRoot' = stateRoot\<close>
      unfolding callVerifyClaimProof_def
      unfolding stateTokenDeposit'_def stateTokenDeposit_def
      by (simp add: snd_def split: option.splits prod.splits if_split_asm)
  next
    have "bridgeState contracts bridgeAddress \<noteq> None"
      using assms
      by (meson \<open>reachableFrom initContracts contracts steps\<close> properSetup_def reachableFromBridgeState)
    then show "bridgeState contracts bridgeAddress = Some (the (bridgeState contracts bridgeAddress))"
      by simp
  qed

   ultimately
   show False
     by simp
qed

end

end