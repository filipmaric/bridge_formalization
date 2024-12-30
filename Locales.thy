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

lemma reachableFromUpdate'Update [simp]:
  shows "reachableFrom contractsUpdate' contractsUpdate [UPDATE_step]"
proof-
  have "executeStep contractsUpdate' blockNumUpdate blockUpdate (UPDATE_step) = (Success, contractsUpdate)"
    using update
    unfolding UPDATE_step_def
    by simp
  then show ?thesis
    using reachableFrom_base reachableFrom_step by blast
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
  assumes reachableFromLastUpdateLU [simp]: 
    "reachableFrom contractsLastUpdate contractsLU stepsNoUpdate"
  assumes noUpdate:
    "let stateOracleAddress = stateOracleAddressB contractsLastUpdate bridgeAddress
      in \<nexists> stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set stepsNoUpdate"
begin

lemma reachableFromLastUpdate'LU [simp]:
  shows "reachableFrom contractsLastUpdate' contractsLU (stepsNoUpdate @ [UPDATE_step])"
  using reachableFromLastUpdateLU reachableFromTrans reachableFromUpdate'Update by blast

lemma properSetupLU [simp]:
  shows "properSetup contractsLU tokenDepositAddress bridgeAddress"
  using properSetupReachable properSetupUpdate' reachableFromLastUpdate'LU by blast

lemma stateOracleAddressBLU [simp]:
  shows "stateOracleAddressB contractsLU bridgeAddress =
         stateOracleAddressB contractsLastUpdate' bridgeAddress"
  using reachableFromBridgeStateOracle reachableFromLastUpdate'LU 
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
  using reachableFromBridgeStateOracle reachableFromLastUpdate'LU reachableFromLastUpdateLU
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

(*
   contractsInit
   properSetup
   getDeposit=0
   lastStateB=0
*)

locale Init' = StrongHashProofVerifier + 
  fixes tokenDepositAddress :: address
  fixes bridgeAddress :: address
  fixes contractsInit :: Contracts
  \<comment> \<open>The operation starts from an initial state that is properly setup\<close>
  assumes properSetupInit [simp]:
    "properSetup contractsInit tokenDepositAddress bridgeAddress"
  \<comment> \<open>All relevant data is still empty\<close>
  assumes depositsEmpty [simp]: 
    "\<And> ID. getDeposit (the (tokenDepositState contractsInit tokenDepositAddress)) ID = 0"
  assumes tokenWithdrawnEmpty [simp]: 
    "\<And> H. getTokenWithdrawn (the (tokenDepositState contractsInit tokenDepositAddress)) H = False"
  assumes claimsEmpty [simp]:
    "\<And> ID. getClaim (the (bridgeState contractsInit bridgeAddress)) ID = False"
  assumes withdrawalsEmpty [simp]: 
    "\<And> ID. getWithdrawal (the (bridgeState contractsInit bridgeAddress)) ID = 0"
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

end

(* ------------------------------------------------------------------------------------ *)

(*
                  [stepsI]
   contractsInit      \<rightarrow>*       contractsI
   properSetup
   getDeposit=0
   lastStateB=0
*)
locale Init = Init' + 
  fixes contractsI :: Contracts
  fixes stepsInit :: "Step list"
  assumes reachableFromInitI [simp]:
    "reachableFrom contractsInit contractsI stepsInit"
begin

lemma properSetupI [simp]: 
  shows "properSetup contractsI tokenDepositAddress bridgeAddress"
  using properSetupInit properSetupReachable reachableFromInitI
  by blast

lemma stateOracleAddressBI [simp]:
  shows "stateOracleAddressB contractsI bridgeAddress =
         stateOracleAddressB contractsInit bridgeAddress"
  using reachableFromBridgeStateOracle reachableFromInitI by blast

lemma stateOracleAddressTDI [simp]:
  shows "stateOracleAddressTD contractsI tokenDepositAddress =
         stateOracleAddressTD contractsInit tokenDepositAddress"
  using reachableFromDepositStateOracle reachableFromInitI
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
  by (meson reachableFromERC20State properToken_def reachableFromInitI)

lemma mintedTokenBI [simp]:
  shows "mintedTokenB contractsI bridgeAddress token = 
         mintedTokenB contractsInit bridgeAddress token"
  using reachableFromBridgeMintedToken reachableFromInitI by blast

lemma mintedTokenTDI [simp]:
  shows "mintedTokenTD contractsI tokenDepositAddress token = 
         mintedTokenTD contractsInit tokenDepositAddress token"
  by (smt (verit, best) properSetup_def reachableFromBridgeTokenPairs reachableFromITokenPairs properSetupI properSetupInit reachableFromInitI)

lemma ERC20StateMintedTokenINotNone [simp]:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "ERC20state contractsI (mintedTokenTD contractsInit tokenDepositAddress token) \<noteq> None"
  using assms
  by (metis mintedTokenTDI properTokenReachable properSetupI properSetup_def properToken_def reachableFromInitI)

end

locale InitUpdate = Init where contractsI=contractsUpdate' + Update
begin
lemma reachableFromInitLastUpdate [simp]:
  shows "reachableFrom contractsInit contractsUpdate (UPDATE_step # stepsInit)"
    using reachableFromInitI reachableFromUpdate'Update
    by (meson reachableFromSingleton reachableFrom_step)
end

sublocale InitUpdate \<subseteq> InitUpdate: Init where contractsI=contractsUpdate and stepsInit="UPDATE_step # stepsInit"
  by (unfold_locales, simp)


(* ------------------------------------------------------------------------------------ *)
locale InitLastUpdate = Init where contractsI=contractsLastUpdate' + LastUpdate

(* ------------------------------------------------------------------------------------ *)

(*
                  [stepsI]
   contractsInit      \<rightarrow>*       contractsI
   properSetup    _ @ [UPDATE]
   getDeposit=0
   lastStateB=0
*)
locale InitFirstUpdate = Init + 
  fixes stateRootInit :: "bytes32"
  assumes firstUpdate:
    "stepsInit \<noteq> [] \<and> last stepsInit = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
  assumes updatesNonZeroInit [simp]:
    "updatesNonZero stepsInit"
begin

lemma stateRootInitNonZero:
  "stateRootInit \<noteq> 0"
  using firstUpdate updatesNonZeroInit
  unfolding updatesNonZero_def
  by (metis last_in_set)

definition UPDATE1_step where 
  "UPDATE1_step = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"

lemma obtainContractsU:
  obtains blockU blockNumU contractsU where
  "callUpdate contractsInit (stateOracleAddressB contractsInit bridgeAddress) blockU blockNumU stateRootInit = (Success, contractsU)" and
  "reachableFrom contractsU contractsI (butlast stepsInit)"
proof-
  obtain steps where "stepsInit = steps @ [UPDATE1_step]"
    using firstUpdate
    unfolding UPDATE1_step_def
    by (metis append_butlast_last_id)
  then show ?thesis
    using reachableFromInitI that
    unfolding UPDATE1_step_def
    by (smt (verit, best) \<open>\<And>thesis. (\<And>steps. stepsInit = steps @ [UPDATE1_step] \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>stepsInit = steps @ [UPDATE1_step]\<close> append.right_neutral butlast.simps(2) butlast_append executeStep.simps(6) list.distinct(1) reachableFrom.cases reachableFromAppend reachableFromCons')
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
  by (metis lastStateNonZero reachableFromBridgeStateOracle firstUpdate last_in_set reachableFromInitI updatesNonZeroInit)

end

(* ------------------------------------------------------------------------------------ *)
locale InitFirstUpdateLastUpdate = InitFirstUpdate where contractsI=contractsLastUpdate' + LastUpdate +
  assumes updatesNonZeroLU: "updatesNonZero (stepsNoUpdate @ [UPDATE_step] @ stepsInit)"
begin

definition stepsAllLU where
  "stepsAllLU = stepsNoUpdate @ [UPDATE_step] @ stepsInit"

lemma reachableFromInitLU [simp]:
  shows "reachableFrom contractsInit contractsLU stepsAllLU"
  using reachableFromInitI reachableFromLastUpdate'LU reachableFromTrans stepsAllLU_def by fastforce

end

sublocale InitFirstUpdateLastUpdate \<subseteq> IFLU: InitFirstUpdate where contractsI=contractsLU and stepsInit=stepsAllLU
  by (metis Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def Nil_is_append_conv firstUpdate last_appendR reachableFromInitLU stepsAllLU_def updatesNonZeroLU)

sublocale InitFirstUpdateLastUpdate \<subseteq> IFLastUpdate: InitFirstUpdate where contractsI=contractsLastUpdate and stepsInit="UPDATE_step # stepsInit"
  by (smt (verit) Cons_eq_append_conv Init'_axioms Init.intro InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro firstUpdate last_ConsR list.distinct(1) reachableFrom.cases reachableFromInitI reachableFromTrans reachableFromUpdate'Update updatesNonZeroAppend(2) updatesNonZeroLU)

(* ------------------------------------------------------------------------------------ *)

context HashProofVerifier
begin

lemma InitInduction [simp]:
  assumes "Init hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof generateClaimProof
           verifyBalanceProof generateBalanceProof verifyBurnProof generateBurnProof tokenDepositAddress bridgeAddress contractsInit contractsI
           (step # steps)"
  assumes "reachableFrom contractsInit contractsI' steps"
  assumes "executeStep contractsI' blockNum block step = (Success, contractsI)"
  shows "Init hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof generateClaimProof
         verifyBalanceProof generateBalanceProof verifyBurnProof generateBurnProof tokenDepositAddress bridgeAddress contractsInit contractsI' steps"
  using assms
  by (simp add: Init_def Init_axioms_def)

lemma InitFirstUpdateAxiomsInduction [simp]:
  assumes "InitFirstUpdate hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof
     generateClaimProof verifyBalanceProof generateBalanceProof verifyBurnProof generateBurnProof tokenDepositAddress bridgeAddress contractsInit
     contractsI (step # steps) stateRootInit"
  assumes "reachableFrom contractsInit contractsI' steps"
  assumes "executeStep contractsI' blockNum block step = (Success, contractsI)"
  assumes "steps \<noteq> []"
  shows "InitFirstUpdate hash2 hash3 generateStateRoot verifyDepositProof generateDepositProof verifyClaimProof
      generateClaimProof verifyBalanceProof generateBalanceProof verifyBurnProof generateBurnProof tokenDepositAddress bridgeAddress contractsInit
      contractsI' steps stateRootInit"
  using assms
  unfolding InitFirstUpdate_def InitFirstUpdate_axioms_def
  by (metis InitInduction last_ConsR updatesNonZeroCons(1))
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
  using reachableFromLastUpdateLU LastUpdateBridgeNotDead_axioms
proof (induction contractsLastUpdate contractsLU stepsNoUpdate rule: reachableFrom.induct)
  case (reachableFrom_base contractsLastUpdate)
  then interpret LU': LastUpdateBridgeNotDead where contractsLastUpdate=contractsLastUpdate and contractsLU=contractsLastUpdate and stepsNoUpdate="[]"
    by simp    
  show ?case
    by (metis LU'.callLastStateLU LU'.update LU'.properSetupUpdate bridgeNotDeadLastUpdate' callUpdateITokenDeposit lastValidState_def properSetup_stateOracleAddress snd_eqD)
next
  case (reachableFrom_step steps contractsLU contractsLastUpdate contractsLU' blockNum block step)
  then interpret LU': LastUpdateBridgeNotDead where contractsLastUpdate=contractsLastUpdate and contractsLU=contractsLU' and stepsNoUpdate=steps
    unfolding LastUpdateBridgeNotDead_def LastUpdate_def LastUpdate_axioms_def Let_def
    by simp
  have "snd (lastValidStateTD contractsLU' tokenDepositAddress) = stateRoot"
    using reachableFrom_step.IH
    using LU'.LastUpdateBridgeNotDead_axioms by auto
  moreover
  have "\<nexists>stateRoot'. step = UPDATE (stateOracleAddressB contractsLU' bridgeAddress) stateRoot'"
    by (metis reachableFromBridgeStateOracle LU'.reachableFromLastUpdateLU LastUpdate.noUpdate LastUpdateBridgeNotDead.axioms(1) list.set_intros(1) reachableFrom_step.prems)
  ultimately
  show ?case
    using noUpdateGetLastValidStateTD
    using LU'.properSetupLU properSetup_stateOracleAddress reachableFrom_step.hyps(2) 
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
  assumes reachableFromUpdate'LVS [simp]: 
    "reachableFrom contractsUpdate contractsLVS stepsLVS"
  assumes getLastValidStateLVS: 
    "lastValidStateTD contractsLVS tokenDepositAddress = (Success, stateRoot)"
begin
definition stepsAllLVS where
  "stepsAllLVS = stepsLVS @ [UPDATE_step] @ stepsInit"

lemma reachableFromInitLVS [simp]: 
  shows "reachableFrom contractsInit contractsLVS stepsAllLVS"
  unfolding stepsAllLVS_def
  using reachableFromTrans reachableFromUpdate'LVS  reachableFromInitI reachableFromUpdate'Update
  by blast

end

sublocale InitUpdateBridgeNotDeadLastValidState \<subseteq> InitLVS: Init where contractsI=contractsLVS and stepsInit="stepsAllLVS"
  using reachableFromInitLVS 
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
    "reachableFrom contractsDead' contractsDead [stepDeath]"
  assumes bridgeDead [simp]:
    "bridgeDead contractsDead tokenDepositAddress"
  \<comment> \<open>Current contracts are reached\<close>
  assumes reachableFromContractsBD [simp]:
    "reachableFrom contractsDead contractsBD stepsBD"
 (* NOTE: additional assumptions *)
  \<comment> \<open>state root hash is not zero\<close>
  assumes stateRootNonZero:
    "stateRoot \<noteq> 0"
begin
definition stepsAllBD where
  "stepsAllBD = stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step] @ stepsInit"

definition stepsBeforeDeath where
  "stepsBeforeDeath = stepsNoUpdate @ [UPDATE_step] @ stepsInit"

lemma reachableFromLastUpdateDead [simp]:
  shows "reachableFrom contractsLastUpdate contractsDead (stepDeath # stepsNoUpdate)"
  by (meson deathStep reachableFromLastUpdateLU reachableFromSingleton reachableFrom_step)

lemma notBridgeDeadContractsLastUpdate' [simp]:
  shows "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
  using notBridgeDead' reachableFromBridgeDead reachableFromLastUpdate'LU 
  by blast

lemma bridgeDeadContractsBD [simp]:
  shows "bridgeDead contractsBD tokenDepositAddress"
  using reachableFromBridgeDead bridgeDead reachableFromContractsBD
  by blast

lemma stepDeathNoUpdate [simp]:
  shows "\<nexists> address stateRoot. stepDeath = UPDATE address stateRoot"
  by (metis bridgeDead callUpdateITokenDeposit deathStep executeStep.simps(6) notBridgeDead' reachableFromSingleton)
 
lemma getLastStateBLastUpdate [simp]:
  shows "lastStateB contractsLastUpdate bridgeAddress = stateRoot"
  using callUpdateLastState update 
  by (metis InitUpdate.stateOracleAddressBI stateOracleAddressBI)

lemma deadStateContractsDead [simp]: 
  shows "deadStateTD contractsDead tokenDepositAddress = stateRoot"
  by (metis BridgeDiesDeadState bridgeDead deathStep lastStateTDLU notBridgeDead' reachableFromSingleton)

lemma deadStateContractsBD [simp]: 
  shows "deadStateTD contractsBD tokenDepositAddress = stateRoot"
  using stateRootNonZero reachableFromContractsBD deadStateContractsDead reachableFromDeadState
  by blast

end

sublocale BridgeDead \<subseteq> InitDead': Init where contractsI=contractsDead' and stepsInit=stepsBeforeDeath
proof
  show "reachableFrom contractsInit contractsDead' stepsBeforeDeath"
    using reachableFromInitI reachableFromLastUpdateLU reachableFromTrans reachableFromUpdate'Update stepsBeforeDeath_def
    by presburger
qed

sublocale BridgeDead \<subseteq> InitDead: Init where contractsI=contractsDead and stepsInit="[stepDeath] @ stepsBeforeDeath"
proof
  show "reachableFrom contractsInit contractsDead  ([stepDeath] @ stepsBeforeDeath)"
    using InitDead'.reachableFromInitI deathStep reachableFromTrans 
    by blast
qed

sublocale BridgeDead \<subseteq> InitBD: Init where contractsI=contractsBD and stepsInit=stepsAllBD
proof
  show "reachableFrom contractsInit contractsBD stepsAllBD"
    unfolding stepsAllBD_def
    by (metis InitDead.reachableFromInitI reachableFromContractsBD reachableFromTrans stepsBeforeDeath_def)
qed

sublocale BridgeDead \<subseteq> LastUpdateBridgeNotDead where contractsLU=contractsDead'
proof
  show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using notBridgeDeadContractsLastUpdate' by blast
qed

sublocale BridgeDead \<subseteq> LVSDead': InitUpdateBridgeNotDeadLastValidState where
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

sublocale BridgeDead \<subseteq> LVSDead: InitUpdateBridgeNotDeadLastValidState where
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

sublocale BridgeDead \<subseteq> LVSBD: InitUpdateBridgeNotDeadLastValidState where 
  contractsUpdate=contractsLastUpdate and 
  contractsUpdate'=contractsLastUpdate' and 
  blockUpdate=blockLastUpdate and 
  blockNumUpdate=blockNumLastUpdate and 
  contractsLVS=contractsBD and 
  stepsLVS="stepsBD @ [stepDeath] @ stepsNoUpdate"
proof
  show "reachableFrom contractsLastUpdate contractsBD (stepsBD @ [stepDeath] @ stepsNoUpdate)"
    using deathStep reachableFromContractsBD reachableFromTrans reachableFromLastUpdateLU
    by blast
next
  show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using notBridgeDeadContractsLastUpdate'
    by blast
next
  show "lastValidStateTD contractsBD tokenDepositAddress = (Success, stateRoot)"
    using bridgeDeadContractsBD deadStateContractsBD lastValidState_def by presburger
qed

locale BridgeDeadInitFirstUpdate = BridgeDead + InitFirstUpdate where contractsI=contractsBD and stepsInit=stepsAllBD

end