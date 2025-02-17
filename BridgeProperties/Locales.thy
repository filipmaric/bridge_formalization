theory Locales
  imports Reachability UpdateProperties
begin

(* ------------------------------------------------------------------------------------ *)

(*
                     update                                
   contractsUpdate'    \<rightarrow>   contractsUpdate
   properSetup
*)
locale Update = StrongHashProofVerifier +
  fixes tokenDepositAddress :: address
  fixes bridgeAddress :: address
  fixes contractsUpdate' :: Contracts
  fixes contractsUpdate :: Contracts
  fixes blockUpdate :: Block
  fixes blockNumUpdate :: uint256
  fixes stateRoot :: bytes32
  \<comment> \<open>starting from a properly configured state\<close>
  assumes properSetupUpdate':
   "properSetup contractsUpdate' tokenDepositAddress bridgeAddress"
  \<comment> \<open>the last update that happened\<close>
  assumes update:
    "let stateOracleAddress = stateOracleAddressB contractsUpdate' bridgeAddress
      in callUpdate contractsUpdate' stateOracleAddress blockUpdate blockNumUpdate stateRoot = (Success, contractsUpdate)"
begin
definition UPDATE_step where
  "UPDATE_step = UPDATE (stateOracleAddressB contractsUpdate' bridgeAddress) stateRoot"

lemma reachableUpdate'Update [simp]:
  shows "reachable contractsUpdate' contractsUpdate [UPDATE_step]"
proof-
  have "executeStep contractsUpdate' blockNumUpdate blockUpdate (UPDATE_step) = (Success, contractsUpdate)"
    using update
    unfolding UPDATE_step_def
    by simp
  then show ?thesis
    using reachable_base reachable_step by blast
qed

lemma tokenDepositStateUpdate'NotNone [simp]:
  shows "tokenDepositState contractsUpdate' tokenDepositAddress \<noteq> None"
  by (meson properSetupUpdate' properSetup_def)

lemma properSetupUpdate [simp]:
  shows "properSetup contractsUpdate tokenDepositAddress bridgeAddress"
  using callUpdateProperSetup update properSetupUpdate' 
  by presburger

lemma depositUpdate' [simp]: 
  shows "BridgeState.deposit (the (bridgeState contractsUpdate' bridgeAddress)) = tokenDepositAddress"
  by (meson properSetupUpdate' properSetup_def)

lemma generateStateRootUpdate' [simp]:
  shows "generateStateRoot contractsUpdate' = stateRoot"
  using update updateSuccess 
  by force

end


(* ------------------------------------------------------------------------------------ *)

(*
                         update                    [stepsNoUpdate]             
   contractsLastUpdate'    \<rightarrow>   contractsLastUpdate      \<rightarrow>*    contractsLU
   properSetup                                        noUpdates                  
*)
locale LastUpdate = 
  Update where
    contractsUpdate=contractsLastUpdate and 
    contractsUpdate'=contractsLastUpdate' and
    blockUpdate=blockLastUpdate and
    blockNumUpdate=blockNumLastUpdate
    for contractsLastUpdate and  contractsLastUpdate' and blockLastUpdate and blockNumLastUpdate + 
  fixes contractsLU :: Contracts
  fixes stepsNoUpdate :: "Step list"
  \<comment> \<open>there were no updates since the last update\<close>
  assumes reachableLastUpdateLU [simp]: 
    "reachable contractsLastUpdate contractsLU stepsNoUpdate"
  assumes noUpdate:
    "let stateOracleAddress = stateOracleAddressB contractsLastUpdate bridgeAddress
      in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set stepsNoUpdate"
begin

lemma reachableLastUpdate'LU [simp]:
  shows "reachable contractsLastUpdate' contractsLU (stepsNoUpdate @ [UPDATE_step])"
  using reachableLastUpdateLU reachableTrans reachableUpdate'Update by blast

lemma properSetupLU [simp]:
  shows "properSetup contractsLU tokenDepositAddress bridgeAddress"
  using properSetupReachable properSetupUpdate' reachableLastUpdate'LU by blast

lemma stateOracleAddressBLU [simp]:
  shows "stateOracleAddressB contractsLU bridgeAddress =
         stateOracleAddressB contractsLastUpdate' bridgeAddress"
  using reachableBridgeStateOracle reachableLastUpdate'LU 
  by blast

lemma depositLU [simp]:
  "depositAddressB contractsLU bridgeAddress = tokenDepositAddress"
  by (meson properSetupLU properSetup_def)

lemma bridgeAddressLU [simp]:
  "bridgeAddressTD contractsLU tokenDepositAddress = bridgeAddress"
  by (meson properSetupLU properSetup_def)

lemma callLastStateLU [simp]:
  shows "callLastState contractsLU (stateOracleAddressB contractsLU bridgeAddress) = 
         (Success, stateRoot)"
  using noUpdate noUpdateLastState callUpdateLastState update
  using reachableBridgeStateOracle reachableLastUpdate'LU reachableLastUpdateLU
  by (smt (verit, ccfv_threshold) callLastState_def  option.case_eq_if properSetupLU properSetup_def )

lemma lastStateBLU [simp]:
  shows "lastStateB contractsLU bridgeAddress = stateRoot"
  using callLastState callLastStateLU
  by blast

lemma  lastStateTDLU [simp]:
  shows "lastStateTD contractsLU tokenDepositAddress = stateRoot"
  by (metis lastStateBLU properSetupLU properSetup_getLastState)

lemma notBridgeDeadLastValidState [simp]:
  assumes "\<not> bridgeDead contractsLU tokenDepositAddress"
  shows "snd (lastValidStateTD contractsLU tokenDepositAddress) = stateRoot"
  using assms
  by (metis callLastStateLU lastValidState_def properSetupLU properSetup_stateOracleAddress snd_conv)

end

(* ------------------------------------------------------------------------------------ *)

locale Addresses = HashProofVerifier + 
  fixes isSmartContract :: "address \<Rightarrow> bool"
  \<comment> \<open>smart contracts do not call for transactions\<close>
  assumes smartContractsNoCalls: 
    "\<And> address step contracts blockNum block. \<lbrakk> isSmartContract address; isCaller address step \<rbrakk> \<Longrightarrow> 
         fst (executeStep contracts blockNum block step) \<noteq> Success"

(*
   contractsInit
   properSetup
   <empty>
*)

locale Init' = StrongHashProofVerifier + Addresses + 
  fixes tokenDepositAddress :: address
  fixes bridgeAddress :: address
  fixes contractsInit :: Contracts
  \<comment> \<open>tokenDeposit and bridge are smart contracts\<close>
  assumes isSmartContractTD: 
    "isSmartContract tokenDepositAddress"
  assumes isSmartContractB:
    "isSmartContract bridgeAddress"
  \<comment> \<open>The operation starts from an initial state that is properly setup\<close>
  assumes properSetupInit [simp]:
    "properSetup contractsInit tokenDepositAddress bridgeAddress"
  \<comment> \<open>All relevant data is still empty\<close>
  assumes depositsEmpty [simp]: 
    "\<And> ID. getDepositTD contractsInit tokenDepositAddress ID = 0"
  assumes tokenWithdrawnEmpty [simp]: 
    "\<And> H. getTokenWithdrawnTD contractsInit tokenDepositAddress H = False"
  assumes releasesEmpty [simp]: 
    "\<And> ID. getReleaseTD contractsInit tokenDepositAddress ID = False"
  assumes claimsEmpty [simp]:
    "\<And> ID. getClaimB contractsInit bridgeAddress ID = False"
  assumes withdrawalsEmpty [simp]: 
    "\<And> ID. getWithdrawalB contractsInit bridgeAddress ID = 0"
  assumes lastStateBZero [simp]:
    "lastStateB contractsInit bridgeAddress = 0"
  assumes notDead [simp]: 
   "\<not> bridgeDead contractsInit tokenDepositAddress"
  \<comment> \<open>There are no funds on the contract\<close>
  assumes noFunds [simp]:
    "\<And> token. ERC20state contractsInit token \<noteq> None \<Longrightarrow> 
               accountBalance contractsInit token tokenDepositAddress = 0"
  assumes finiteBalances [simp]:
    "\<And> token. ERC20state contractsInit token \<noteq> None \<Longrightarrow> 
              finiteBalances contractsInit token"
begin

lemma lastStateTDZeroInit [simp]:
  shows "lastStateTD contractsInit tokenDepositAddress = 0"
  by (metis lastStateBZero properSetupInit properSetup_getLastState)

lemma mintedTokenITDB:
  shows "mintedTokenB contractsInit bridgeAddress token = mintedTokenTD contractsInit tokenDepositAddress token"
  by (metis properSetupInit properSetup_def)

lemma mintedTokenTDInitNonNone [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "mintedTokenTD contractsInit tokenDepositAddress token \<noteq> 0"
  using assms
  unfolding properToken_def Let_def
  by (simp add: mintedTokenITDB)

lemma properTokenNoFunds [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "accountBalance contractsInit token tokenDepositAddress = 0"
  by (meson assms noFunds properToken_def)

lemma properTokenFiniteBalances [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "finiteBalances contractsInit token"
  using assms
  by (meson finiteBalances properToken_def)

lemma properTokenFiniteBalancesMinted [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "finiteBalances contractsInit (mintedTokenB contractsInit bridgeAddress token)"
  using assms
  by (meson finiteBalances properToken_def)

lemma mintedTokenBInitNonNone [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "mintedTokenB contractsInit bridgeAddress token \<noteq> 0"
  using assms
  by (simp add: Let_def properToken_def)

lemma notCallerTD:
  assumes "reachable contractsInit contracts steps"
  shows "\<forall> step \<in> set steps. \<not> isCaller tokenDepositAddress step"
  using assms
proof (induction contractsInit contracts steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
    by (metis Addresses.smartContractsNoCalls Addresses_axioms fst_conv isSmartContractTD set_ConsD)
qed

end

(* ------------------------------------------------------------------------------------ *)

(*
                  [stepsI]
   contractsInit      \<rightarrow>*       contractsI
   properSetup
   <empty>
*)
locale Init = Init' + 
  fixes contractsI :: Contracts
  fixes stepsInit :: "Step list"
  assumes reachableInitI [simp]:
    "reachable contractsInit contractsI stepsInit"
begin

lemma properSetupI [simp]: 
  shows "properSetup contractsI tokenDepositAddress bridgeAddress"
  using properSetupInit properSetupReachable reachableInitI
  by blast

lemma stateOracleAddressBI [simp]:
  shows "stateOracleAddressB contractsI bridgeAddress =
         stateOracleAddressB contractsInit bridgeAddress"
  using reachableBridgeStateOracle reachableInitI by blast

lemma stateOracleAddressTDI [simp]:
  shows "stateOracleAddressTD contractsI tokenDepositAddress =
         stateOracleAddressTD contractsInit tokenDepositAddress"
  using reachableDepositStateOracle reachableInitI
  by blast

lemma tokenDepositStateINotNone [simp]:
  shows "tokenDepositState contractsI tokenDepositAddress \<noteq> None"
  by (meson properSetupI properSetup_def)

lemma bridgeStateINotNone [simp]:
  shows "bridgeState contractsI bridgeAddress \<noteq> None"
  by (meson properSetupI properSetup_def)

lemma bridgeBridgeAddress [simp]:
  shows "TokenDepositState.bridge (the (tokenDepositState contractsI tokenDepositAddress)) = bridgeAddress"
  by (meson properSetupI properSetup_def)

lemma tokenDepositTokenDepositAddress [simp]:
  shows "BridgeState.deposit (the (bridgeState contractsI bridgeAddress)) = tokenDepositAddress"
  by (meson properSetupI properSetup_def)

lemma tokenPairsStateINotNone [simp]:
  shows "tokenPairsState contractsI (tokenPairsAddressTD contractsI tokenDepositAddress) \<noteq> None"
  by (metis properSetupI properSetup_def)

lemma stateOracleStateINotNone [simp]:
  shows "stateOracleState contractsI (stateOracleAddressTD contractsInit tokenDepositAddress) \<noteq> None"
  by (metis properSetupI properSetup_def stateOracleAddressTDI)

lemma stateOracleStateInitNotNone [simp]:
  shows "stateOracleState contractsInit (stateOracleAddressTD contractsInit tokenDepositAddress) \<noteq> None"
  by (metis properSetupInit properSetup_def)

lemma proofVerifierStateNotNone [simp]:
  shows "proofVerifierState contractsI (proofVerifierAddressTD contractsI tokenDepositAddress) \<noteq> None"
  by (metis properSetupI properSetup_def)

lemma ERC20stateINonNone [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "ERC20state contractsI token \<noteq> None"
  using assms
  by (meson reachableERC20State properToken_def reachableInitI)

lemma mintedTokenBI [simp]:
  shows "mintedTokenB contractsI bridgeAddress token = 
         mintedTokenB contractsInit bridgeAddress token"
  using reachableBridgeMintedToken reachableInitI by blast

lemma mintedTokenTDI [simp]:
  shows "mintedTokenTD contractsI tokenDepositAddress token = 
         mintedTokenTD contractsInit tokenDepositAddress token"
  by (smt (verit, best) properSetup_def reachableBridgeTokenPairs reachableITokenPairs properSetupI properSetupInit reachableInitI)

lemma ERC20StateMintedTokenINotNone [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "ERC20state contractsI (mintedTokenTD contractsInit tokenDepositAddress token) \<noteq> None"
  using assms
  by (metis mintedTokenTDI properTokenReachable properSetupI properSetup_def properToken_def reachableInitI)

end

locale InitUpdate = Init where contractsI=contractsUpdate' + Update
begin
lemma reachableInitLastUpdate [simp]:
  shows "reachable contractsInit contractsUpdate (UPDATE_step # stepsInit)"
    using reachableInitI reachableUpdate'Update
    by (meson reachableSingleton reachable_step)
end

sublocale InitUpdate \<subseteq> Init_Update: Init where contractsI=contractsUpdate and stepsInit="UPDATE_step # stepsInit"
  by (unfold_locales, simp)


(* ------------------------------------------------------------------------------------ *)
(*
               stepsInit                     update                    [stepsNoUpdate]             
contractsInit    \<rightarrow>*   contractsLastUpdate'    \<rightarrow>   contractsLastUpdate      \<rightarrow>*    contractsLU
properSetup             properSetup                                     noUpdates                  
*)
locale InitLastUpdate = Init where contractsI=contractsLastUpdate' + LastUpdate

sublocale InitLastUpdate \<subseteq> Init_LastUpdate: Init where contractsI=contractsLastUpdate and stepsInit="UPDATE_step # stepsInit"
  using reachableInitI update
  using executeStep.simps(6) reachable_step
  unfolding UPDATE_step_def
  using Init'_axioms Init_axioms_def Init_def by presburger

sublocale InitLastUpdate \<subseteq> Init_LU: Init where contractsI=contractsLU and stepsInit="stepsNoUpdate @ [UPDATE_step] @ stepsInit"
  by (smt (verit) Cons_eq_append_conv Init'_axioms Init.intro Init_LastUpdate.reachableInitI Init_axioms.intro reachable.cases reachableInitI reachableLastUpdateLU reachableTrans)

(* ------------------------------------------------------------------------------------ *)

(*
                  [stepsI]
   contractsInit      \<rightarrow>*       contractsI
   properSetup    _ @ [UPDATE]
   <empty>
*)
locale InitFirstUpdate = Init + 
  fixes stateRootInit :: "bytes32"
  assumes firstUpdate:
    "stepsInit \<noteq> [] \<and> last stepsInit = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
  assumes stateRootInitNonZero: 
    "stateRootInit \<noteq> 0"
begin

definition UPDATE1_step where 
  "UPDATE1_step = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"

lemma obtainContractsU:
  obtains blockU blockNumU contractsU where
  "callUpdate contractsInit (stateOracleAddressB contractsInit bridgeAddress) blockU blockNumU stateRootInit = (Success, contractsU)" and
  "reachable contractsU contractsI (butlast stepsInit)"
proof-
  obtain steps where "stepsInit = steps @ [UPDATE1_step]"
    using firstUpdate
    unfolding UPDATE1_step_def
    by (metis append_butlast_last_id)
  then show ?thesis
    using reachableInitI that
    unfolding UPDATE1_step_def
    by (smt (verit, best) \<open>\<And>thesis. (\<And>steps. stepsInit = steps @ [UPDATE1_step] \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>stepsInit = steps @ [UPDATE1_step]\<close> append.right_neutral butlast.simps(2) butlast_append executeStep.simps(6) list.distinct(1) reachable.cases reachableAppend reachableCons')
qed

lemma getLastStateBContractsU:
  assumes "callUpdate contractsInit (stateOracleAddressB contractsInit bridgeAddress) blockU blockNumU stateRootInit = (Success, contractsU)"
  shows "lastStateB contractsU bridgeAddress = stateRootInit"
  using assms
  using callUpdateIBridge callUpdateLastState 
  by presburger

lemma generateStateRootInit:
  shows "generateStateRoot contractsInit = stateRootInit"
proof-
  obtain blockU blockNumU contractsU
    where "callUpdate contractsInit (stateOracleAddressB contractsInit bridgeAddress) blockU blockNumU stateRootInit = (Success, contractsU)"
    by (meson obtainContractsU)
  then show ?thesis
    using updateSuccess 
    by blast
qed

lemma getLastStateBContractsUNonZero:
  shows "lastStateB contractsI bridgeAddress \<noteq> 0"
  by (metis lastStateNonZero reachableBridgeStateOracle firstUpdate last_in_set reachableInitI)

end

(* ------------------------------------------------------------------------------------ *)

(*
               stepsInit                     update                    [stepsNoUpdate]             
contractsInit    \<rightarrow>*   contractsLastUpdate'    \<rightarrow>   contractsLastUpdate      \<rightarrow>*    contractsLU
properSetup           properSetup                                        noUpdates                  
*)


locale InitFirstUpdateLastUpdate = InitFirstUpdate where contractsI=contractsLastUpdate' + LastUpdate
begin

definition stepsAllLU where
  "stepsAllLU = stepsNoUpdate @ [UPDATE_step] @ stepsInit"

lemma reachableInitLU [simp]:
  shows "reachable contractsInit contractsLU stepsAllLU"
  using reachableInitI reachableLastUpdate'LU reachableTrans stepsAllLU_def by fastforce

end

sublocale InitFirstUpdateLastUpdate \<subseteq> InitFirstUpdate_LastUpdate: InitFirstUpdate where contractsI=contractsLastUpdate and stepsInit="UPDATE_step # stepsInit"
  by (metis (full_types) Init'_axioms Init.intro InitFirstUpdate.intro InitFirstUpdate_axioms.intro Init_axioms.intro append_Cons append_Nil firstUpdate last_ConsR list.distinct(1) reachableInitI reachableTrans reachableUpdate'Update stateRootInitNonZero)

sublocale InitFirstUpdateLastUpdate \<subseteq> InitFirstUpdate_LU: InitFirstUpdate where contractsI=contractsLU and stepsInit=stepsAllLU
  by (metis Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def Nil_is_append_conv firstUpdate last_appendR reachableInitLU stateRootInitNonZero stepsAllLU_def)


(* ------------------------------------------------------------------------------------ *)

context HashProofVerifier
begin

lemma InitInduction [simp]:
  assumes "Init hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof generateClaimProof
           verifyBalanceProof generateBalanceProof verifyBurnProof generateBurnProof isSmartContract tokenDepositAddress bridgeAddress contractsInit contractsI
           (step # steps)"
  assumes "reachable contractsInit contractsI' steps"
  assumes "executeStep contractsI' blockNum block step = (Success, contractsI)"
  shows "Init hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof generateClaimProof
         verifyBalanceProof generateBalanceProof verifyBurnProof generateBurnProof isSmartContract tokenDepositAddress bridgeAddress contractsInit contractsI' steps"
  using assms
  by (simp add: Init_def Init_axioms_def)

lemma InitFirstUpdateAxiomsInduction [simp]:
  assumes "InitFirstUpdate hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof
     generateClaimProof verifyBalanceProof generateBalanceProof verifyBurnProof generateBurnProof isSmartContract tokenDepositAddress bridgeAddress contractsInit
     contractsI (step # steps) stateRootInit"
  assumes "reachable contractsInit contractsI' steps"
  assumes "executeStep contractsI' blockNum block step = (Success, contractsI)"
  assumes "steps \<noteq> []"
  shows "InitFirstUpdate hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof
      generateClaimProof verifyBalanceProof generateBalanceProof verifyBurnProof generateBurnProof isSmartContract tokenDepositAddress bridgeAddress contractsInit
      contractsI' steps stateRootInit"
  using assms
  unfolding InitFirstUpdate_def InitFirstUpdate_axioms_def
  by (metis InitInduction last_ConsR)
end


(*
                         update                    [stepsNoUpdate]             
   contractsLastUpdate'    \<rightarrow>   contractsLastUpdate      \<rightarrow>*    contractsLU
   properSetup                      noUpdates
   bridgeNotDead                 
*)
locale LastUpdateBridgeNotDead = LastUpdate + 
  assumes bridgeNotDeadLastUpdate' [simp]:
    "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
begin

lemma lastValidStateLU [simp]:
  shows "snd (lastValidStateTD contractsLU tokenDepositAddress) = stateRoot"
  unfolding Let_def
  using reachableLastUpdateLU LastUpdateBridgeNotDead_axioms
proof (induction contractsLastUpdate contractsLU stepsNoUpdate rule: reachable.induct)
  case (reachable_base contractsLastUpdate)
  then interpret LU': LastUpdateBridgeNotDead where contractsLastUpdate=contractsLastUpdate and contractsLU=contractsLastUpdate and stepsNoUpdate="[]"
    by simp    
  show ?case
    by (metis LU'.callLastStateLU LU'.update LU'.properSetupUpdate bridgeNotDeadLastUpdate' callUpdateITokenDeposit lastValidState_def properSetup_stateOracleAddress snd_eqD)
next
  case (reachable_step steps contractsLU contractsLastUpdate contractsLU' blockNum block step)
  then interpret LU': LastUpdateBridgeNotDead where contractsLastUpdate=contractsLastUpdate and contractsLU=contractsLU' and stepsNoUpdate=steps
    unfolding LastUpdateBridgeNotDead_def LastUpdate_def LastUpdate_axioms_def Let_def
    by simp
  have "snd (lastValidStateTD contractsLU' tokenDepositAddress) = stateRoot"
    using reachable_step.IH
    using LU'.LastUpdateBridgeNotDead_axioms by auto
  moreover
  have "\<nexists>stateRoot'. step = UPDATE (stateOracleAddressB contractsLU' bridgeAddress) stateRoot'"
    by (metis reachableBridgeStateOracle LU'.reachableLastUpdateLU LastUpdate.noUpdate LastUpdateBridgeNotDead.axioms(1) list.set_intros(1) reachable_step.prems)
  ultimately
  show ?case
    using noUpdateGetLastValidStateTD
    using LU'.properSetupLU properSetup_stateOracleAddress reachable_step.hyps(2) 
    by presburger
qed

end


(*
               [stepsInit]               update                 [stepsLVS]    
  contractsInit  \<rightarrow>*   contractsUpdate'    \<rightarrow>   contractsUpdate    \<rightarrow>*      contractsLVS
  properSetup            properSetup   stateRoot                            getLastValidState=stateRoot
                         bridgeNotDead                 
*)

locale InitUpdateBridgeNotDeadLastValidState = InitUpdate + 
  fixes contractsLVS :: Contracts
  fixes stepsLVS :: "Step list"
  assumes bridgeNotDead [simp]: 
    "\<not> bridgeDead contractsUpdate' tokenDepositAddress"
  assumes reachableUpdate'LVS [simp]: 
    "reachable contractsUpdate contractsLVS stepsLVS"
  assumes getLastValidStateLVS: 
    "lastValidStateTD contractsLVS tokenDepositAddress = (Success, stateRoot)"
begin
definition stepsAllLVS where
  "stepsAllLVS = stepsLVS @ [UPDATE_step] @ stepsInit"

lemma reachableInitLVS [simp]: 
  shows "reachable contractsInit contractsLVS stepsAllLVS"
  unfolding stepsAllLVS_def
  using reachableTrans reachableUpdate'LVS  reachableInitI reachableUpdate'Update
  by blast

end

sublocale InitUpdateBridgeNotDeadLastValidState \<subseteq> Init_LVS: Init where contractsI=contractsLVS and stepsInit="stepsAllLVS"
  using reachableInitLVS 
  by unfold_locales auto

(*
               [stepsInit]                  update                  [stepsNoUpdate]               stepDeath               stepsBD
   contractsInit  \<rightarrow>*   contractsLastUpdate'  \<rightarrow>  contractsLastUpdate       \<rightarrow>*     contractsDead'     \<rightarrow>    contractsDead   \<rightarrow>*  contractsBD
   properSetup
*)
locale BridgeDead =
  InitUpdate where contractsUpdate=contractsLastUpdate and contractsUpdate'=contractsLastUpdate' and blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate +
  LastUpdate where contractsLU=contractsDead' for contractsDead'::Contracts +
  fixes contractsBD::Contracts
  fixes stepDeath :: Step
  fixes contractsDead :: Contracts
  fixes stepsBD :: "Step list"
  \<comment> \<open>Bridge died\<close>
  assumes notBridgeDead' [simp]:
    "\<not> bridgeDead contractsDead' tokenDepositAddress"
  assumes deathStep [simp]: 
    "reachable contractsDead' contractsDead [stepDeath]"
  assumes bridgeDead [simp]:
    "bridgeDead contractsDead tokenDepositAddress"
  \<comment> \<open>Current contracts are reached\<close>
  assumes reachableContractsBD [simp]:
    "reachable contractsDead contractsBD stepsBD"
  \<comment> \<open>state root hash is not zero\<close>
  assumes stateRootNonZero:
    "stateRoot \<noteq> 0"
begin
definition stepsAllBD where
  "stepsAllBD = stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step] @ stepsInit"

definition stepsBeforeDeath where
  "stepsBeforeDeath = stepsNoUpdate @ [UPDATE_step] @ stepsInit"

lemma reachableLastUpdateDead [simp]:
  shows "reachable contractsLastUpdate contractsDead (stepDeath # stepsNoUpdate)"
  by (meson deathStep reachableLastUpdateLU reachableSingleton reachable_step)

lemma notBridgeDeadContractsLastUpdate' [simp]:
  shows "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
  using notBridgeDead' reachableBridgeDead reachableLastUpdate'LU 
  by blast

lemma bridgeDeadContractsBD [simp]:
  shows "bridgeDead contractsBD tokenDepositAddress"
  using reachableBridgeDead bridgeDead reachableContractsBD
  by blast

lemma stepDeathNoUpdate [simp]:
  shows "\<nexists> address stateRoot. stepDeath = UPDATE address stateRoot"
  by (metis bridgeDead callUpdateITokenDeposit deathStep executeStep.simps(6) notBridgeDead' reachableSingleton)
 
lemma getLastStateBLastUpdate [simp]:
  shows "lastStateB contractsLastUpdate bridgeAddress = stateRoot"
  using callUpdateLastState update 
  by (metis Init_Update.stateOracleAddressBI stateOracleAddressBI)

lemma deadStateContractsDead [simp]: 
  shows "deadStateTD contractsDead tokenDepositAddress = stateRoot"
  by (metis BridgeDiesDeadState bridgeDead deathStep lastStateTDLU notBridgeDead' reachableSingleton)

lemma deadStateContractsBD [simp]: 
  shows "deadStateTD contractsBD tokenDepositAddress = stateRoot"
  using stateRootNonZero reachableContractsBD deadStateContractsDead reachableDeadState
  by blast

end

sublocale BridgeDead \<subseteq> Init_Dead': Init where contractsI=contractsDead' and stepsInit=stepsBeforeDeath
proof
  show "reachable contractsInit contractsDead' stepsBeforeDeath"
    using reachableInitI reachableLastUpdateLU reachableTrans reachableUpdate'Update stepsBeforeDeath_def
    by presburger
qed

sublocale BridgeDead \<subseteq> Init_Dead: Init where contractsI=contractsDead and stepsInit="[stepDeath] @ stepsBeforeDeath"
proof
  show "reachable contractsInit contractsDead  ([stepDeath] @ stepsBeforeDeath)"
    using Init_Dead'.reachableInitI deathStep reachableTrans 
    by blast
qed

sublocale BridgeDead \<subseteq> Init_BD: Init where contractsI=contractsBD and stepsInit=stepsAllBD
proof
  show "reachable contractsInit contractsBD stepsAllBD"
    unfolding stepsAllBD_def
    by (metis Init_Dead.reachableInitI reachableContractsBD reachableTrans stepsBeforeDeath_def)
qed

sublocale BridgeDead \<subseteq> LastUpdateBridgeNotDead where contractsLU=contractsDead'
proof
  show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using notBridgeDeadContractsLastUpdate' by blast
qed

sublocale BridgeDead \<subseteq> InitUpdateBridgeNotDeadLastValidState_Dead': InitUpdateBridgeNotDeadLastValidState where
  contractsUpdate=contractsLastUpdate and 
  contractsUpdate'=contractsLastUpdate' and 
  blockUpdate=blockLastUpdate and 
  blockNumUpdate=blockNumLastUpdate and 
  contractsLVS=contractsDead' and 
  stepsLVS=stepsNoUpdate
proof
  show "lastValidStateTD contractsDead' tokenDepositAddress = (Success, stateRoot)"
    using callLastStateLU lastValidState_def notBridgeDead' properSetupLU properSetup_stateOracleAddress 
    by presburger
next
  show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using notBridgeDeadContractsLastUpdate'
    by simp
qed simp_all

sublocale BridgeDead \<subseteq> InitUpdateBridgeNotDeadLastValidState_Dead: InitUpdateBridgeNotDeadLastValidState where
  contractsUpdate=contractsLastUpdate and 
  contractsUpdate'=contractsLastUpdate' and 
  blockUpdate=blockLastUpdate and 
  blockNumUpdate=blockNumLastUpdate and 
  contractsLVS=contractsDead and 
  stepsLVS="stepDeath # stepsNoUpdate"
proof
  show "lastValidStateTD contractsDead tokenDepositAddress = (Success, stateRoot)"
    using bridgeDead deadStateContractsDead lastValidState_def by presburger
next
  show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using notBridgeDeadContractsLastUpdate'
    by simp
qed simp_all

sublocale BridgeDead \<subseteq> InitUpdateBridgeNotDeadLastValidState_BD: InitUpdateBridgeNotDeadLastValidState where 
  contractsUpdate=contractsLastUpdate and 
  contractsUpdate'=contractsLastUpdate' and 
  blockUpdate=blockLastUpdate and 
  blockNumUpdate=blockNumLastUpdate and 
  contractsLVS=contractsBD and 
  stepsLVS="stepsBD @ [stepDeath] @ stepsNoUpdate"
proof
  show "reachable contractsLastUpdate contractsBD (stepsBD @ [stepDeath] @ stepsNoUpdate)"
    using deathStep reachableContractsBD reachableTrans reachableLastUpdateLU
    by blast
next
  show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using notBridgeDeadContractsLastUpdate'
    by blast
next
  show "lastValidStateTD contractsBD tokenDepositAddress = (Success, stateRoot)"
    using bridgeDeadContractsBD deadStateContractsBD lastValidState_def by presburger
qed

(* ------------------------------------------------------------------------------------ *)

locale BridgeDeadInitFirstUpdate = BridgeDead + InitFirstUpdate where contractsI=contractsBD and stepsInit=stepsAllBD

sublocale BridgeDeadInitFirstUpdate \<subseteq> InitFirstUpdate_LastUpdate: InitFirstUpdate where contractsI=contractsLastUpdate and stepsInit="UPDATE_step # stepsInit"
  by (metis InitFirstUpdate.intro InitFirstUpdate_axioms.intro Init_Update.Init_axioms append_Cons firstUpdate last_append list.simps(3) self_append_conv2 stateRootInitNonZero stepsAllBD_def)

sublocale BridgeDeadInitFirstUpdate \<subseteq> InitFirstUpdate_Dead': InitFirstUpdate where contractsI=contractsDead' and stepsInit="stepsBeforeDeath"
  using InitFirstUpdate_LastUpdate.firstUpdate InitFirstUpdate_axioms_def InitFirstUpdate_def Init_Dead'.Init_axioms Nil_is_append_conv append_Cons last_append self_append_conv2 stateRootInitNonZero stepsBeforeDeath_def
  by auto

sublocale BridgeDeadInitFirstUpdate \<subseteq> InitFirstUpdate_Dead: InitFirstUpdate where contractsI=contractsDead and stepsInit="stepDeath # stepsBeforeDeath"
  by (metis InitFirstUpdate.intro InitFirstUpdate_Dead'.firstUpdate InitFirstUpdate_axioms_def InitUpdateBridgeNotDeadLastValidState_Dead.Init_LVS.Init_axioms InitUpdateBridgeNotDeadLastValidState_Dead.stepsAllLVS_def append_Cons last_ConsR list.distinct(1) stateRootInitNonZero stepsBeforeDeath_def)

(* ------------------------------------------------------------------------------------ *)

end