theory TokenInvariants
  imports Reachability UpdateProperties DepositClaimProperties BurnReleaseProperties CancelWithdrawProperties
begin

(* ------------------------------------------------------------------------------------ *)

context HashProofVerifier
begin

primrec DEPOSIT_amount where
  "DEPOSIT_amount (DEPOSIT address caller ID token amount) = amount"

primrec CLAIM_amount where
  "CLAIM_amount (CLAIM address caller ID token amount proof) = amount"

primrec WITHDRAW_WD_amount where
  "WITHDRAW_WD_amount (WITHDRAW_WD address caller token amount proof) = amount"

primrec CANCEL_amount where
  "CANCEL_amount (CANCEL_WD address caller ID token amount proof) = amount"

primrec BURN_amount where
  "BURN_amount (BURN address caller ID token amount) = amount"

primrec RELEASE_amount where
  "RELEASE_amount (RELEASE address caller ID token amount proof) = amount"
end

(* ------------------------------------------------------------------------------------ *)
section \<open>Deposited token amount\<close>

context HashProofVerifier
begin

fun isTokenDeposit :: "address \<Rightarrow> address \<Rightarrow> Step \<Rightarrow> bool" where
  "isTokenDeposit address token (DEPOSIT address' caller ID token' amount) \<longleftrightarrow> address' = address \<and> token' = token"
| "isTokenDeposit address token _ = False"

\<comment> \<open>All deposits of the given token on the given address\<close>
definition tokenDeposits where
  "tokenDeposits address token steps = filter (isTokenDeposit address token) steps"

\<comment> \<open>Total amount of the given token deposited on the given address\<close>
definition depositedTokenAmount where
  "depositedTokenAmount tokenDepositAddress token steps = 
        sum_list (map DEPOSIT_amount (tokenDeposits tokenDepositAddress token steps))"

lemma tokenDepositsNil [simp]:
  shows "tokenDeposits tokenDepositAddress token [] = []"
  by (simp add: tokenDeposits_def)

lemma tokenDepositsAppend[simp]:
  shows "tokenDeposits tokenDepositAddress token (steps1 @ steps2) = 
         tokenDeposits tokenDepositAddress token steps1 @ tokenDeposits tokenDepositAddress token steps2"
  by (simp add: tokenDeposits_def)

lemma tokenDepositsSubsetSteps:
  shows "set (tokenDeposits tokenDepositAddress token steps) \<subseteq> set steps"
  by (simp add: tokenDeposits_def)

lemma tokenDepositsConsDeposit [simp]:
  shows "tokenDeposits tokenDepositAddress token (DEPOSIT tokenDepositAddress caller ID token amount # steps) =
         DEPOSIT tokenDepositAddress caller ID token amount # tokenDeposits tokenDepositAddress token steps"
  unfolding tokenDeposits_def
  by simp

lemma tokenDepositsConsDepositOther [simp]:
  assumes "tokenDepositAddress \<noteq> tokenDepositAddress' \<or> token \<noteq> token'"
  shows "tokenDeposits tokenDepositAddress token (DEPOSIT tokenDepositAddress' caller ID token' amount # steps) =
         tokenDeposits tokenDepositAddress token steps"
  using assms
  unfolding tokenDeposits_def
  by auto

lemma tokenDepositsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "tokenDeposits tokenDepositAddress token (step # steps) = tokenDeposits tokenDepositAddress token steps"
  using assms
  by (cases step, auto simp add: tokenDeposits_def)

lemma depositedTokenAmountNil [simp]:
  shows "depositedTokenAmount address token [] = 0"
  by (simp add: depositedTokenAmount_def)

lemma depositedTokenAmountConsDeposit [simp]:
  shows "depositedTokenAmount address token (DEPOSIT address caller ID token amount # steps) = 
         amount + depositedTokenAmount address token steps"
  by (simp add: depositedTokenAmount_def)

lemma depositedTokenAmountConsDepositOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "depositedTokenAmount address token (DEPOSIT address' caller ID token' amount # steps) = 
         depositedTokenAmount address token steps"
  using assms
  by (auto simp add: depositedTokenAmount_def)

lemma depositedTokenAmoutConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount'. step = DEPOSIT address' caller' ID' token' amount'"
  shows "depositedTokenAmount address token (step # steps) = depositedTokenAmount address token steps"
  using assms 
  unfolding depositedTokenAmount_def
  by (cases step, auto)

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Claimed token amount\<close>

context HashProofVerifier
begin


fun isTokenClaim where
  "isTokenClaim address token (CLAIM address' caller ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isTokenClaim address token _ = False"

\<comment> \<open>All claims of a given token on the given bridge\<close>
definition tokenClaims where 
  "tokenClaims address token steps = 
   filter (isTokenClaim address token) steps"

lemma tokenClaimsNil [simp]:
  shows "tokenClaims bridgeAddress token [] = []"
  by (simp add: tokenClaims_def)

\<comment> \<open>Total amount of a given token claimed on the given bridge\<close>
definition claimedTokenAmount where
  "claimedTokenAmount bridgeAddress token steps = 
   sum_list (map CLAIM_amount (tokenClaims bridgeAddress token steps))"

lemma claimedTokenAmountNil [simp]:
  shows "claimedTokenAmount bridgeAddress token [] = 0"
  by (simp add: claimedTokenAmount_def)

lemma claimedTokenAmoutConsClaim [simp]:
  shows "claimedTokenAmount address token (CLAIM address caller ID token amount proof # steps) = claimedTokenAmount address token steps + amount"
  unfolding claimedTokenAmount_def tokenClaims_def
  by auto

lemma claimedTokenAmoutConsClaimOther [simp]:
  assumes "address' \<noteq> address \<or> token' \<noteq> token"
  shows "claimedTokenAmount address token (CLAIM address' caller ID token' amount proof # steps) = claimedTokenAmount address token steps"
  using assms
  unfolding claimedTokenAmount_def tokenClaims_def
  by auto

lemma claimedTokenAmoutConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CLAIM address' caller' ID' token' amount' proof'"
  shows "claimedTokenAmount address token (step # steps) = claimedTokenAmount address token steps"
  using assms 
  unfolding claimedTokenAmount_def tokenClaims_def
  by (cases step, auto)

end


(* ------------------------------------------------------------------------------------ *)
section \<open>Burned token amount\<close>

context HashProofVerifier
begin

fun isTokenBurn where
  "isTokenBurn address token (BURN address' caller ID token' amount) \<longleftrightarrow> address' = address \<and> token' = token"
| "isTokenBurn address token _ = False"

\<comment> \<open>All burns of a given token on the given bridge\<close>
definition tokenBurns where 
  "tokenBurns address token steps = 
   filter (isTokenBurn address token) steps"

lemma tokenBurnsNil [simp]:
  shows "tokenBurns bridgeAddress token [] = []"
  by (simp add: tokenBurns_def)

lemma tokenBurnsConsOther [simp]:
  assumes "\<nexists> caller ID amount. step = BURN bridgeAddress caller ID token amount"
  shows "tokenBurns bridgeAddress token (step # steps) = tokenBurns bridgeAddress token steps"
  using assms
  by (simp add: tokenBurns_def, cases step, auto)

lemma tokenBurnsConsBurn [simp]:
  shows "tokenBurns bridgeAddress token (BURN bridgeAddress caller ID token amount # steps) = 
         BURN bridgeAddress caller ID token amount # tokenBurns bridgeAddress token steps"
  by (simp add: tokenBurns_def)

\<comment> \<open>Total amount of a given token claimed on the given bridge\<close>
definition burnedTokenAmount where
  "burnedTokenAmount bridgeAddress token steps = 
   sum_list (map BURN_amount (tokenBurns bridgeAddress token steps))"

lemma burnedTokenAmountNil [simp]:
  shows "burnedTokenAmount bridgeAddress token [] = 0"
  by (simp add: burnedTokenAmount_def)

lemma burnedTokenAmoutConsBurn [simp]:
  shows "burnedTokenAmount address token (BURN address caller ID token amount  # steps) = burnedTokenAmount address token steps + amount"
  unfolding burnedTokenAmount_def tokenBurns_def
  by auto

lemma burnedTokenAmoutConsBurnOther [simp]:
  assumes "address' \<noteq> address \<or> token' \<noteq> token"
  shows "burnedTokenAmount address token (BURN address' caller ID token' amount # steps) = burnedTokenAmount address token steps"
  using assms
  unfolding burnedTokenAmount_def tokenBurns_def
  by auto

lemma burnedTokenAmountConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = BURN address' caller' ID' token' amount'"
  shows "burnedTokenAmount address token (step # steps) = burnedTokenAmount address token steps"
  using assms 
  unfolding burnedTokenAmount_def tokenBurns_def
  by (cases step, auto)

end

(* ------------------------------------------------------------------------------------ *)

section \<open>Canceled token amount\<close>
context HashProofVerifier
begin

fun isTokenCancel where
  "isTokenCancel address token (CANCEL_WD address' caller ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isTokenCancel address token _ = False"

definition tokenCancels where
  "tokenCancels tokenDepositAddress token steps = 
   filter (isTokenCancel tokenDepositAddress token) steps"

definition canceledTokenAmount where
  "canceledTokenAmount tokenDepositAddress token steps = 
   sum_list (map CANCEL_amount (tokenCancels tokenDepositAddress token steps))"

lemma tokenCancelsNil [simp]:
  shows "tokenCancels tokenDepositAddress token [] = []"
  by (simp add: tokenCancels_def)

lemma canceledTokenAmountNil [simp]:
  shows "canceledTokenAmount tokenDepositAddress token [] = 0"
  by (simp add: canceledTokenAmount_def)

lemma canceledTokenAmountCancel [simp]:
  shows "canceledTokenAmount address token (CANCEL_WD address caller ID token amount proof # steps) = 
         amount + canceledTokenAmount address token steps"
  unfolding canceledTokenAmount_def tokenCancels_def
  by auto

lemma canceledTokenAmountConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CANCEL_WD address' caller' ID' token' amount' proof'"
  shows "canceledTokenAmount address token (step # steps) = canceledTokenAmount address token steps"
  using assms 
  unfolding canceledTokenAmount_def tokenCancels_def
  by (cases step, auto)

lemma canceledTokenAmountConsCancelOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "canceledTokenAmount address token (CANCEL_WD address' caller' ID' token' amount' proof' # steps) = 
         canceledTokenAmount address token steps"
  using assms
  unfolding canceledTokenAmount_def tokenCancels_def
  by auto

end

(* ------------------------------------------------------------------------------------ *)
text \<open>Withdrawn while dead token amount\<close>
context HashProofVerifier
begin

fun isTokenWithdrawal where
  "isTokenWithdrawal address token (WITHDRAW_WD address' caller token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isTokenWithdrawal address token _ = False"

definition tokenWithdrawals where
  "tokenWithdrawals tokenDepositAddress token steps = filter (isTokenWithdrawal tokenDepositAddress token) steps"

definition withdrawnTokenAmount where
  "withdrawnTokenAmount tokenDepositAddress token steps = 
   sum_list (map WITHDRAW_WD_amount (tokenWithdrawals tokenDepositAddress token steps))"

lemma tokenWithdrawalsNil [simp]:
  shows "tokenWithdrawals tokenDepositAddress token [] = []"
  unfolding tokenWithdrawals_def
  by simp

lemma withdrawnTokenAmountNil [simp]:
  shows "withdrawnTokenAmount tokenDepositAddress token [] = 0"
  by (simp add: withdrawnTokenAmount_def)

lemma withdrawnTokenAmoutConsOther [simp]:
  assumes "\<nexists> caller' amount' proof'. step = WITHDRAW_WD address caller' token amount' proof'"
  shows "withdrawnTokenAmount address token (step # steps) = withdrawnTokenAmount address token steps"
  using assms 
  unfolding withdrawnTokenAmount_def tokenWithdrawals_def
  by (cases step, auto)

lemma withdrawnTokenAmoutConsWithdraw [simp]:
  shows "withdrawnTokenAmount address token (WITHDRAW_WD address caller token amount proof # steps) = 
         withdrawnTokenAmount address token steps + amount"
  unfolding withdrawnTokenAmount_def tokenWithdrawals_def
  by auto

lemma withdrawnTokenAmountBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
    shows "withdrawnTokenAmount tokenDepositAddress token steps = 0"
  using assms
  using assms noWithdrawBeforeBridgeDead[OF assms]
  unfolding withdrawnTokenAmount_def tokenWithdrawals_def
  by (metis filter_False isTokenWithdrawal.elims(2) list.simps(8) sum_list.Nil)

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Claimed deposits amount\<close>

context HashProofVerifier
begin

fun isTokenRelease where
  "isTokenRelease address token (RELEASE address' caller ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isTokenRelease address token _ = False"

definition tokenReleases where
  "tokenReleases tokenDepositAddress token steps = 
   filter (isTokenRelease tokenDepositAddress token) steps"

definition releasedTokenAmount where
  "releasedTokenAmount tokenDepositAddress token steps = 
   sum_list (map RELEASE_amount (tokenReleases tokenDepositAddress token steps))"

lemma tokenReleasesNil [simp]:
  shows "tokenReleases tokenDepositAddress token [] = []"
  by (simp add: tokenReleases_def)

lemma releasedTokenAmountNil [simp]:
  shows "releasedTokenAmount tokenDepositAddress token [] = 0"
  by (simp add: releasedTokenAmount_def)

lemma releasedTokenAmountRelease [simp]:
  shows "releasedTokenAmount address token (RELEASE address caller ID token amount proof # steps) = 
         amount + releasedTokenAmount address token steps"
  unfolding releasedTokenAmount_def tokenReleases_def
  by auto

lemma releasedTokenAmountConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = RELEASE address' caller' ID' token' amount' proof'"
  shows "releasedTokenAmount address token (step # steps) = releasedTokenAmount address token steps"
  using assms 
  unfolding releasedTokenAmount_def tokenReleases_def
  by (cases step, auto)

lemma realesedTokenAmountConsReleaseOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "releasedTokenAmount address token (RELEASE address' caller' ID' token' amount' proof' # steps) = 
         releasedTokenAmount address token steps"
  using assms
  unfolding releasedTokenAmount_def tokenReleases_def
  by auto

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Claimed deposits amount\<close>

context HashProofVerifier
begin

primrec DEPOSIT_id where
  "DEPOSIT_id (DEPOSIT address caller ID token amount) = ID"

(* NOTE: only for the given token *)
definition isClaimedID where
 "isClaimedID bridgeAddress token ID steps \<longleftrightarrow> 
  (\<exists> caller' amount' proof'. CLAIM bridgeAddress caller' ID token amount' proof' \<in> set steps)"

text \<open>All deposits of the given token on the given address that have been claimed\<close>
definition claimedTokenDeposits where
  "claimedTokenDeposits tokenDepositAddress bridgeAddress token steps = 
     filter 
      (\<lambda> step. isClaimedID bridgeAddress token (DEPOSIT_id step) steps) 
      (tokenDeposits tokenDepositAddress token steps)"

text \<open>Total amount of tokens that have been deposited on the given address and then claimed\<close>
definition claimedTokenDepositsAmount where
  "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps = 
   sum_list (map DEPOSIT_amount (claimedTokenDeposits tokenDepositAddress bridgeAddress token steps))"

lemma claimedTokenDepositsNil [simp]: 
  shows "claimedTokenDeposits tokenDepositAddress bridgeAddress token [] = []"
  unfolding claimedTokenDeposits_def
  by simp

lemma claimedTokenDepositsConsOther [simp]:
  assumes "\<nexists> caller ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"
  shows "claimedTokenDeposits tokenDepositAddress bridgeAddress token (step # steps) = 
         claimedTokenDeposits tokenDepositAddress bridgeAddress token steps"
    using assms
    unfolding claimedTokenDeposits_def isClaimedID_def
    by (smt (verit, del_insts) filter_cong list.set_intros(2) set_ConsD tokenDepositsOther)

lemma claimedTokenDepositsAmountNil [simp]: 
  shows "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token [] = 0"
  unfolding claimedTokenDepositsAmount_def
  by simp

lemma claimedTokenDepositsAmountConsOther [simp]: 
  assumes "\<nexists> caller ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"
  shows "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token (step # steps) =
         claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps"
  using assms
  unfolding claimedTokenDepositsAmount_def
  by simp

end

context InitFirstUpdate
begin


(*
                   stepsInit                CLAIM
contractsInit        \<rightarrow>*         contractsI   \<rightarrow>   contractsClaim
properSetup        UPDATE
getDeposit=0
lastState=0
*)
lemma claimedTokenDepositsAmountConsClaim [simp]:
  assumes "reachableFrom contractsI contractsClaim [CLAIM bridgeAddress caller ID token amount proof]"
  shows   "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token
             (CLAIM bridgeAddress caller ID token amount proof # stepsInit) = 
           claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit + amount"
proof-
  define CLAIM_step where 
  "CLAIM_step = CLAIM bridgeAddress caller ID token amount proof"
  define DEPOSIT_step where
  "DEPOSIT_step = DEPOSIT tokenDepositAddress caller ID token amount"
  define claimed where
  "claimed = claimedTokenDeposits tokenDepositAddress bridgeAddress token (CLAIM_step # stepsInit)"

  have deposits: "tokenDeposits tokenDepositAddress token (CLAIM_step # stepsInit) = 
                  tokenDeposits tokenDepositAddress token stepsInit"
    unfolding CLAIM_step_def
    by simp

  have "callClaim contractsI bridgeAddress (message caller amount) ID token amount proof = (Success, contractsClaim)"
    using assms
    by (metis executeStep.simps(2) reachableFromSingleton)
  then have "DEPOSIT_step \<in> set stepsInit"
    using depositBeforeClaim[where msg="message caller amount"]
    unfolding DEPOSIT_step_def
    by simp
  then have "DEPOSIT_step \<in> set claimed"
    unfolding DEPOSIT_step_def CLAIM_step_def claimed_def
    unfolding claimedTokenDeposits_def tokenDeposits_def isClaimedID_def
    by auto

  obtain steps1 steps2 where steps: "stepsInit = steps1 @ [DEPOSIT_step] @ steps2"
    using \<open>DEPOSIT_step \<in> set stepsInit\<close>
    by (metis Cons_eq_append_conv in_set_conv_decomp self_append_conv2)

  have *: "\<forall> step \<in> set (steps1 @ steps2). (\<forall> caller' amount' ID'. step = DEPOSIT tokenDepositAddress caller' ID' token amount' \<longrightarrow> ID' \<noteq> ID)"
    using DEPOSITNoDouble'[OF reachableFromInitI] steps
    unfolding DEPOSIT_step_def
    by auto
  then have "DEPOSIT_step \<notin> set (steps1 @ steps2)"
    unfolding DEPOSIT_step_def
    by auto

  define P where "P = (\<lambda> step. isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit)"
  define P' where "P' = (\<lambda> step. isClaimedID bridgeAddress token (DEPOSIT_id step) (CLAIM_step # stepsInit))"
  define Q where "Q = (\<lambda> step. isTokenDeposit tokenDepositAddress token step)"

  define depositsInit where "depositsInit = tokenDeposits tokenDepositAddress token stepsInit"

  have "depositsInit = (filter Q steps1) @ [DEPOSIT_step] @ (filter Q steps2)"
    using \<open>stepsInit = steps1 @ [DEPOSIT_step] @ steps2\<close>
    unfolding depositsInit_def tokenDeposits_def Q_def DEPOSIT_step_def
    by auto
  then have claimed:
    "claimed = filter P' (filter Q steps1) @ filter P' [DEPOSIT_step] @ filter P' (filter Q steps2)"
    using deposits
    unfolding depositsInit_def claimed_def claimedTokenDeposits_def P'_def
    by auto

  define c1 where "c1 = filter P' (filter Q steps1)" 
  define c2 where "c2 = filter P' (filter Q steps2)" 

  have "DEPOSIT_step \<notin> set (c1 @ c2)"
    using \<open>DEPOSIT_step \<notin> set (steps1 @ steps2)\<close>
    unfolding c1_def c2_def
    by auto
  then have claimed: "claimed = c1 @ [DEPOSIT_step] @ c2"
    using claimed \<open>DEPOSIT_step \<in> set claimed\<close> 
    unfolding c1_def c2_def
    by (metis append.assoc append.right_neutral filter.simps(1) filter.simps(2))
  
  moreover

  have "set (c1 @ c2) \<subseteq> set (steps1 @ steps2)"
    unfolding c1_def c2_def
    by auto

  have "filter P depositsInit = c1 @ c2"
  proof (rule filter')
    show "DEPOSIT_step \<notin> set (c1 @ c2)"
      by fact
  next
    show "filter P' depositsInit = c1 @ [DEPOSIT_step] @ c2"
      using \<open>claimed = c1 @ [DEPOSIT_step] @ c2\<close> deposits
      unfolding depositsInit_def claimed_def claimedTokenDeposits_def P'_def
      by simp
  next
    show "\<forall> step \<in> set depositsInit. (P' step \<and> step \<noteq> DEPOSIT_step) \<longleftrightarrow> P step"
    proof safe
      fix step
      assume "step \<in> set depositsInit" "P' step" "step \<noteq> DEPOSIT_step"
      have "DEPOSIT_id step \<noteq> ID"
      proof-
        have "step \<in> set (filter Q steps1 @ filter Q steps2)"
          using \<open>step \<in> set depositsInit\<close> \<open>step \<noteq> DEPOSIT_step\<close>
          using \<open>depositsInit = (filter Q steps1) @ [DEPOSIT_step] @ (filter Q steps2)\<close>
          by auto
        then have "step \<in> set (steps1 @ steps2)" "Q step"
          by auto
        then obtain ID' caller' amount' where "step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
          unfolding Q_def
          by (metis isTokenDeposit.elims(2))
        then show ?thesis
          using * \<open>step \<in> set (steps1 @ steps2)\<close>
          by simp
      qed
      then show "P step"
        using \<open>P' step\<close>
        unfolding P_def P'_def CLAIM_step_def isClaimedID_def
        by auto
    next
      fix step
      assume "step \<in> set depositsInit" "P step"
      then show "P' step"
        unfolding P_def P'_def isClaimedID_def
        by auto
    next
      assume "P DEPOSIT_step"
      have "reachableFrom contractsInit contractsClaim (CLAIM bridgeAddress caller ID token amount proof # stepsInit)"
        by (meson assms(1) reachableFromInitI reachableFromSingleton reachableFrom_step)
      then show False
        using CLAIMNoDoubleCons \<open>P DEPOSIT_step\<close>
        unfolding P_def DEPOSIT_step_def isClaimedID_def depositsInit_def
        by auto
    qed
  qed
  then have "claimedTokenDeposits tokenDepositAddress bridgeAddress token stepsInit = c1 @ c2"
    unfolding claimed_def P_def claimedTokenDeposits_def depositsInit_def
    by auto
  ultimately
  show ?thesis
    unfolding claimed_def claimedTokenDepositsAmount_def
    unfolding CLAIM_step_def DEPOSIT_step_def depositsInit_def
    by simp
qed


(*
                steps               DEPOSIT
contractsInit    \<rightarrow>*     contractsI    \<rightarrow>   contractsDeposit
properSetup
getDeposit=0
lastState=0
*)
lemma claimedTokenDepositsAmountConsDeposit [simp]:
  assumes "reachableFrom contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
  shows "claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token
            (DEPOSIT tokenDepositAddress caller ID token amount # stepsInit) =
         claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit"
proof-
  define DEPOSIT_step where "DEPOSIT_step = DEPOSIT tokenDepositAddress caller ID token amount"
  have "claimedTokenDeposits tokenDepositAddress bridgeAddress token (DEPOSIT_step # stepsInit) = 
        claimedTokenDeposits tokenDepositAddress bridgeAddress token stepsInit"
  proof-
    have "\<nexists> caller' token' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
      using assms noClaimBeforeDeposit
      unfolding DEPOSIT_step_def
      by blast
    then show ?thesis
      unfolding claimedTokenDeposits_def
      using DEPOSIT_step_def isClaimedID_def
      by auto
  qed
  then show ?thesis
    unfolding claimedTokenDepositsAmount_def DEPOSIT_step_def
    by simp
qed

text \<open>Total claimed amount equals total amount of deposits that have been claimed\<close>
lemma tokenClaimsClaimedTokenDeposits:
  shows "claimedTokenAmount bridgeAddress token stepsInit = 
         claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit"
  using reachableFromInitI InitFirstUpdate_axioms
proof (induction contractsInit contractsI stepsInit)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contractsI contractsInit contractsI' blockNum block step)
  show ?case
  proof (cases "steps = []")
    case True
    then obtain stateRoot where "step = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRoot"
      by (metis InitFirstUpdate.firstUpdate last.simps reachableFrom_step.prems)
    then show ?thesis
      using True claimedTokenDepositsAmountConsOther
      by (simp add: claimedTokenAmount_def tokenClaims_def claimedTokenDepositsAmount_def claimedTokenDeposits_def tokenDeposits_def)
  next
    case False
    interpret I: Init where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
      by (meson InitFirstUpdate_def Init_axioms.intro Init_def reachableFrom_step.hyps(1) reachableFrom_step.prems)
    interpret IFU: InitFirstUpdate where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
      using False
      by (metis I.Init_axioms InitFirstUpdate.axioms(2) InitFirstUpdate.intro InitFirstUpdate_axioms_def last_ConsR reachableFrom_step.prems updatesNonZeroCons(1))

    have *: "claimedTokenAmount bridgeAddress token steps =
             claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token steps"
      using IFU.InitFirstUpdate_axioms reachableFrom_step.IH by blast

    show ?thesis
      using * claimedTokenDepositsAmountConsOther
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token")
        case True
        show ?thesis
          using DEPOSIT True IFU.claimedTokenDepositsAmountConsDeposit
          by (metis IFU.InitFirstUpdate_axioms Step.simps(9) claimedTokenAmoutConsOther reachableFrom.reachableFrom_step reachableFrom_base reachableFrom_step.IH reachableFrom_step.hyps(2))
      next
        case False
        then show ?thesis
          using DEPOSIT *
          using claimedTokenDepositsAmountConsOther
          by auto
      qed
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token' = token")
        case False
        then show ?thesis
          using * CLAIM
          using claimedTokenDepositsAmountConsOther
          by auto
      next
        case True
        then show ?thesis
          using * CLAIM True claimedTokenAmoutConsClaim  IFU.claimedTokenDepositsAmountConsClaim
          by (metis reachableFrom.reachableFrom_step reachableFrom_base reachableFrom_step.hyps(2))
      qed
    qed auto
  qed
qed

end


(* ------------------------------------------------------------------------------------ *)

context InitFirstUpdate
begin

text \<open>The total amount of minted tokens is the difference between claimed tokens and burned tokens\<close>
(*               [steps]
   contractsInit   \<rightarrow>*    contracts 
                           \<not> dead
*)
theorem totalMintedBridgeNotDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "totalMinted contractsI bridgeAddress token + 
         burnedTokenAmount bridgeAddress token stepsInit = 
         totalMinted contractsInit bridgeAddress token + 
         claimedTokenAmount bridgeAddress token stepsInit"
  using reachableFromInitI assms InitFirstUpdate_axioms
proof (induction contractsInit contractsI stepsInit rule: reachableFrom.induct)
  case (reachableFrom_base contractsInit)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contractsI contractsInit contractsI' blockNum block step)

  show ?case
  proof (cases "steps = []")
    case True
    then have "reachableFrom contractsInit contractsI' []"
      using reachableFrom_step.hyps
      by simp
    then have "contractsInit = contractsI'"
      using reachableFrom.cases
      by blast
    then have "totalMinted contractsI' bridgeAddress token = totalMinted contractsInit bridgeAddress token"
      by blast
    moreover
    have "claimedTokenAmount bridgeAddress token
          [UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit] = 0"
      by simp
    moreover
    have "burnedTokenAmount bridgeAddress token
          [UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit] = 0"
      by simp
    moreover
    have "step = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
      by (metis InitFirstUpdate.firstUpdate True last.simps reachableFrom_step.prems(2))
    ultimately
    show ?thesis
      using reachableFrom_step.prems reachableFrom_step.hyps firstUpdate True
      by (metis reachableFromITokenPairs HashProofVerifier.reachableFrom_step HashProofVerifier_axioms Nat.add_0_right callUpdateIBridge callUpdateIERC20 executeStep.simps(6))
  next
    case False

    interpret InitFirstUpdate': InitFirstUpdate  where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
      using False InitFirstUpdateAxiomsInduction reachableFrom_step.hyps(1) reachableFrom_step.hyps(2) reachableFrom_step.prems(2)
      by blast

    have *: "reachableFrom contractsInit contractsI (step # steps)"
      using reachableFrom.reachableFrom_step reachableFrom_step
      by blast

    have *: "totalMinted contractsI' bridgeAddress token + burnedTokenAmount bridgeAddress token steps  = 
             totalMinted contractsInit bridgeAddress token +
             claimedTokenAmount bridgeAddress token steps"
      using reachableFrom_step.IH reachableFrom_step.prems
      using InitFirstUpdate'.InitFirstUpdate_axioms notDead 
      by fastforce

    let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
    have **: "mintedTokenB contractsI bridgeAddress token = ?mintedToken"
       using InitFirstUpdate'.reachableFromInitI reachableFrom.reachableFrom_step reachableFromBridgeMintedToken reachableFrom_step.hyps(2) 
       by blast

    show ?thesis
    proof (cases step)
      case (DEPOSIT address' caller ID token' amount)
      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token")
        case False
        have "token' \<noteq> mintedTokenB contractsInit bridgeAddress token"
          sorry (* no direct deposit on minted token *)
        then have "ERC20state contractsI (mintedTokenB contractsInit bridgeAddress token) = ERC20state contractsI' (mintedTokenB contractsInit bridgeAddress token)"
          using DEPOSIT reachableFrom_step.prems reachableFrom_step.hyps callDepositOtherToken
          by (metis executeStep.simps(1))
        moreover 
        have "claimedTokenAmount bridgeAddress token steps =
              claimedTokenAmount bridgeAddress token (DEPOSIT address' caller ID token' amount # steps)"
          using False
          by auto
        moreover
        have "burnedTokenAmount bridgeAddress token steps = 
              burnedTokenAmount bridgeAddress token (DEPOSIT address' caller ID token' amount # steps)"
          using False
          by auto
        ultimately
        show ?thesis
          using * ** reachableFrom_step.prems reachableFrom_step.hyps DEPOSIT
          by (metis InitFirstUpdate'.mintedTokenBI)
      next
        case True
        have "claimedTokenAmount bridgeAddress token (step # steps) = 
              claimedTokenAmount bridgeAddress token steps"
          using DEPOSIT True
          by simp
        moreover
        have "burnedTokenAmount bridgeAddress token (step # steps) = 
              burnedTokenAmount bridgeAddress token steps"
          using DEPOSIT
          by simp
        ultimately
        show ?thesis
          using * **
          using DEPOSIT True callDepositOtherToken
          using  reachableFrom_step.prems(1)
          unfolding properToken_def
          by (smt (verit, ccfv_SIG) executeStep.simps(1) reachableFromBridgeTokenPairs reachableFromITokenPairs InitFirstUpdate'.reachableFromInitI reachableFrom_step.hyps(2))
      qed
    next
      case (CLAIM address' caller ID token' amount proof')
      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token' = token")
        case True

        have ***: "mintedTokenB contractsI' bridgeAddress token' = ?mintedToken"
            using ** True
            using InitFirstUpdate'.reachableFromInitI reachableFromBridgeMintedToken
            by blast

        have "totalTokenBalance contractsI ?mintedToken =
              totalTokenBalance contractsI' ?mintedToken + amount"
        proof (rule callClaimTotalBalance)
          show "finiteBalances contractsI' ?mintedToken"
            using InitFirstUpdate'.properTokenFiniteBalancesMinted InitFirstUpdate'.reachableFromInitI reachableFromFiniteBalances reachableFrom_step.prems(1)
            by blast
        next
          show "callClaim contractsI' bridgeAddress (message caller amount) ID token' amount proof' = (Success, contractsI)"
            using True CLAIM reachableFrom_step.hyps
            by simp
        next
          show "mintedTokenB contractsI' bridgeAddress token' = ?mintedToken"
            by fact
        qed
        moreover
        have "claimedTokenAmount bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof' # steps) =
              claimedTokenAmount bridgeAddress token steps + amount"
          using True
          by simp
        moreover 
        have "burnedTokenAmount bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof' # steps) =
              burnedTokenAmount bridgeAddress token steps"
          by simp
        ultimately
        show ?thesis
          using *** ** * CLAIM True
          by (smt (verit, del_insts) ab_semigroup_add_class.add_ac(1) add.commute)
      next
        case False
        have "?mintedToken \<noteq> mintedTokenB contractsInit address' token'" (* no cancel of minted tokens *)
          sorry
        then have "ERC20state contractsI ?mintedToken = ERC20state contractsI' ?mintedToken"
          using CLAIM callClaimOtherToken[where msg="message caller amount"]
          by (metis executeStep.simps(2) reachableFromBridgeMintedToken InitFirstUpdate'.reachableFromInitI reachableFrom_step.hyps(2))
        then have "totalTokenBalance contractsI (mintedTokenB contractsI bridgeAddress token) =
                   totalTokenBalance contractsI' (mintedTokenB contractsInit bridgeAddress token)"
          using **
          by presburger
        moreover
        have "burnedTokenAmount bridgeAddress token (step # steps) = burnedTokenAmount bridgeAddress token steps"
          using CLAIM
          by simp
        moreover
        have "claimedTokenAmount bridgeAddress token (step # steps) = 
              claimedTokenAmount bridgeAddress token steps"
          using CLAIM False
          by simp
        ultimately
        show ?thesis
          using *
          by (metis InitFirstUpdate'.mintedTokenBI)
      qed
    next
      case (UPDATE address' stateRoot')
      have "totalTokenBalance contractsI (mintedTokenB contractsI bridgeAddress token) =
            totalTokenBalance contractsI' (mintedTokenB contractsInit bridgeAddress token)"
        using **
        using UPDATE callUpdateIERC20 executeStep.simps(6) reachableFrom_step.hyps(2)
        by presburger
      moreover
      have "burnedTokenAmount bridgeAddress token (step # steps) = burnedTokenAmount bridgeAddress token steps"
        using UPDATE
        by simp
      moreover
      have "claimedTokenAmount bridgeAddress token (step # steps) = 
            claimedTokenAmount bridgeAddress token steps"
        using UPDATE False
        by simp
      ultimately
      show ?thesis
        using *
        by (metis InitFirstUpdate'.mintedTokenBI)
    next
      case (CANCEL_WD address' caller' ID' token' amount' proof')
      have "?mintedToken \<noteq> token'" (* no cancel of minted tokens *)
        sorry
      then have "ERC20state contractsI ?mintedToken = ERC20state contractsI' ?mintedToken"
        using CANCEL_WD reachableFrom_step.hyps(2)
        using callCancelDepositWhileDeadOtherToken
        by (metis executeStep.simps(7))
      then have "totalTokenBalance contractsI (mintedTokenB contractsI bridgeAddress token) =
                 totalTokenBalance contractsI' (mintedTokenB contractsInit bridgeAddress token)"
        using **
        by presburger
      moreover
      have "burnedTokenAmount bridgeAddress token (step # steps) = burnedTokenAmount bridgeAddress token steps"
        using CANCEL_WD
        by simp
      moreover
      have "claimedTokenAmount bridgeAddress token (step # steps) = 
            claimedTokenAmount bridgeAddress token steps"
        using CANCEL_WD False
        by simp
      ultimately
      show ?thesis
        using *
        by (metis InitFirstUpdate'.mintedTokenBI)
    next
      case (WITHDRAW_WD address' caller token' amount proof')
      have "?mintedToken \<noteq> token'" (* no withdrawal of minted tokens *)
        sorry
      then have "ERC20state contractsI ?mintedToken = ERC20state contractsI' ?mintedToken"
        using WITHDRAW_WD reachableFrom_step.hyps(2)
        using callWithdrawWhileDeadOtherToken
        by (metis executeStep.simps(8))
      then have "totalTokenBalance contractsI (mintedTokenB contractsI bridgeAddress token) =
                 totalTokenBalance contractsI' (mintedTokenB contractsInit bridgeAddress token)"
        using **
        by presburger
      moreover
      have "burnedTokenAmount bridgeAddress token (step # steps) = burnedTokenAmount bridgeAddress token steps"
        using WITHDRAW_WD
        by simp
      moreover
      have "claimedTokenAmount bridgeAddress token (step # steps) = 
            claimedTokenAmount bridgeAddress token steps"
        using WITHDRAW_WD False
        by simp
      ultimately
      show ?thesis
        using *
        by (metis InitFirstUpdate'.mintedTokenBI)
    next
      case (TRANSFER address' caller' receiver' token' amount')

      have "callTransfer contractsI' address' caller' receiver' token' amount' = (Success, contractsI)"
         using reachableFrom_step.hyps TRANSFER
         by auto

      moreover

      have claimed: 
        "claimedTokenAmount bridgeAddress token (step # steps) = 
         claimedTokenAmount bridgeAddress token steps"
        using claimedTokenDepositsAmountConsOther TRANSFER
        by simp

      moreover

      have burned: 
        "burnedTokenAmount bridgeAddress token (step # steps) = 
         burnedTokenAmount bridgeAddress token steps"
        using TRANSFER
        by simp

      moreover

      have "totalTokenBalance contractsI ?mintedToken = totalTokenBalance contractsI' ?mintedToken"
      proof (cases "mintedTokenB contractsI' address' token' = ?mintedToken")
        case True
        show ?thesis
        proof (rule callTransferTotalBalance)
          show "callTransfer contractsI' address' caller' receiver' token' amount' = (Success, contractsI)"
            by fact
        next
          show "mintedTokenB contractsI' address' token' = ?mintedToken"
            by fact
        next
          show "finiteBalances contractsI' ?mintedToken"
            using reachableFromFiniteBalances InitFirstUpdate'.properTokenFiniteBalancesMinted InitFirstUpdate'.reachableFromInitI reachableFrom_step.prems(1)
            by blast
        qed
      next
        case False
        then show ?thesis
          using calculation(1) callTransferOtherToken by presburger
      qed

      ultimately 

      show ?thesis
        using * **
        by (metis callTransferIBridge callTransferITokenPairs)
    next
      case (BURN address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token' = token")
        case True

        have "totalTokenBalance contractsI ?mintedToken = totalTokenBalance contractsI' ?mintedToken - amount' \<and>
              amount' \<le> totalTokenBalance contractsI' ?mintedToken"
        proof (rule callWithdrawTotalBalance)
          show "finiteBalances contractsI' ?mintedToken"
            using reachableFromFiniteBalances InitFirstUpdate'.properTokenFiniteBalancesMinted InitFirstUpdate'.reachableFromInitI reachableFrom_step.prems(1) 
            by blast
        next
          show "callWithdraw contractsI' address' (message caller' 0) ID' token' amount' = (Success, contractsI)"
            using reachableFrom_step.hyps BURN
            by auto
        next
          show "mintedTokenB contractsI' address' token' = ?mintedToken"
            using True **
            by simp
        qed

        moreover

        have "burnedTokenAmount bridgeAddress token (step # steps) = burnedTokenAmount bridgeAddress token steps + amount'"
          using BURN True
          by simp

        moreover

        have "claimedTokenAmount bridgeAddress token (step # steps) = 
              claimedTokenAmount bridgeAddress token steps"
          using claimedTokenDepositsAmountConsOther BURN
          by simp

        ultimately

        show ?thesis
          using * **
          by (smt (verit) InitFirstUpdate'.mintedTokenBI add.commute add.left_commute diff_add)
      next
      case False
        have "?mintedToken \<noteq> mintedTokenB contractsI' address' token'"
          sorry
        then have "ERC20state contractsI ?mintedToken = ERC20state contractsI' ?mintedToken"
          using BURN reachableFrom_step.hyps(2)
          using callWithdrawOtherToken
          by (metis executeStep.simps(3))
        then have "totalTokenBalance contractsI ?mintedToken = totalTokenBalance contractsI' ?mintedToken"
          by argo
        moreover 
         
        have "burnedTokenAmount bridgeAddress token (step # steps) = burnedTokenAmount bridgeAddress token steps"
          using BURN False
          by simp

        moreover

        have "claimedTokenAmount bridgeAddress token (step # steps) = 
              claimedTokenAmount bridgeAddress token steps"
          using claimedTokenDepositsAmountConsOther BURN
          by simp

        ultimately 
        
        show ?thesis
          using * **
          by (metis InitFirstUpdate'.mintedTokenBI)
      qed
    next
      case (RELEASE address' caller' ID' token' amount')
      have "?mintedToken \<noteq> token'" (* no withdrawal of minted tokens *)
        sorry
      then have "ERC20state contractsI ?mintedToken = ERC20state contractsI' ?mintedToken"
        using RELEASE reachableFrom_step.hyps(2)
        using callReleaseOtherToken
        by (metis executeStep.simps(4))
      then have "totalTokenBalance contractsI (mintedTokenB contractsI bridgeAddress token) =
                 totalTokenBalance contractsI' (mintedTokenB contractsInit bridgeAddress token)"
        using **
        by presburger
      moreover
      have "burnedTokenAmount bridgeAddress token (step # steps) = burnedTokenAmount bridgeAddress token steps"
        using RELEASE
        by simp
      moreover
      have "claimedTokenAmount bridgeAddress token (step # steps) = 
            claimedTokenAmount bridgeAddress token steps"
        using RELEASE False
        by simp
      ultimately
      show ?thesis
        using *
        by (metis InitFirstUpdate'.mintedTokenBI)
    qed
  qed
qed

end

(* ------------------------------------------------------------------------------------ *)

context HashProofVerifier
begin

lemma canceledTokenAmountBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
    shows "canceledTokenAmount tokenDepositAddress token steps = 0"
  using assms noCancelBeforeBridgeDead[OF assms]
  unfolding canceledTokenAmount_def tokenCancels_def
  by (metis filter_False isTokenCancel.elims(2) list.simps(8) sum_list.Nil)
end


text \<open>Current amount of tokens on the TokenDeposit balance (on the sender chain)\<close>
context HashProofVerifier
begin

abbreviation tokenDepositBalance where
 "tokenDepositBalance contracts token tokenDepositAddress \<equiv> 
  accountBalance contracts token tokenDepositAddress"

end

context Init
begin

text \<open>Current TokenDeposit balance equals the sum of all deposits minus
       the sum of all released, canceled and withdrawn tokens \<close>
theorem tokenDepositBalanceInvariant:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "tokenDepositBalance contractsI token tokenDepositAddress + 
         canceledTokenAmount tokenDepositAddress token stepsInit + 
         withdrawnTokenAmount tokenDepositAddress token stepsInit + 
         releasedTokenAmount tokenDepositAddress token stepsInit = 
         depositedTokenAmount tokenDepositAddress token stepsInit"
  using reachableFromInitI Init_axioms assms
proof (induction contractsInit contractsI stepsInit rule: reachableFrom.induct)
  case (reachableFrom_base contractsInit)
  then interpret I: Init where contractsInit=contractsInit and contractsI=contractsInit and stepsInit="[]"
    by simp
  show ?case
    using reachableFrom_base.prems
    by simp
next
  case (reachableFrom_step steps contractsI contractsInit contractsI' blockNum block step)
  then interpret I: Init where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
    using InitInduction by blast
  have *: "accountBalance contractsI' token tokenDepositAddress +
           canceledTokenAmount tokenDepositAddress token steps +
           withdrawnTokenAmount tokenDepositAddress token steps +
           releasedTokenAmount tokenDepositAddress token steps =
           depositedTokenAmount tokenDepositAddress token steps"
    using reachableFrom_step
    by simp
  show ?case
  proof (cases step)
    case (UPDATE address' stateRoot')
    then show ?thesis
      using * reachableFrom_step.hyps
      by simp
  next
    case (TRANSFER address' caller' receiver' token' amount')
    have "mintedTokenB contractsI' address' token' \<noteq> token"
      sorry
    then have "accountBalance contractsI token tokenDepositAddress = 
               accountBalance contractsI' token tokenDepositAddress"
      using TRANSFER reachableFrom_step.hyps
      using callTransferOtherToken[of contractsI' address' caller' receiver' token' amount' contractsI "mintedTokenB contractsI' address' token'" token]
      by (metis executeStep.simps(5))
    then show ?thesis
      using * TRANSFER reachableFrom_step.hyps
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    have "mintedTokenB contractsI' address' token' \<noteq> token"
      sorry
    then have "accountBalance contractsI token tokenDepositAddress = 
              accountBalance contractsI' token tokenDepositAddress"
      using callClaimOtherToken[of contractsI' address' "message caller' amount'" ID']
      using CLAIM reachableFrom_step.hyps
      by simp
    then show ?thesis
      using * CLAIM
      by simp
  next
    case (DEPOSIT address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case True
      then show ?thesis
        using * DEPOSIT reachableFrom_step.hyps callDepositBalanceOfContract
        by simp
    next
      case False
      have "caller' \<noteq> tokenDepositAddress"
        sorry
      then show ?thesis
        using False * DEPOSIT reachableFrom_step.hyps
        using callDepositOtherToken[of token token']
        using callDepositBalanceOfOther[of tokenDepositAddress address' "message caller' amount'" contractsI' block ID' token' amount' contractsI]
        by (smt (verit, ccfv_threshold) Step.simps(13) Step.simps(19) Step.simps(21) canceledTokenAmountConsOther depositedTokenAmountConsDepositOther executeStep.simps(1) releasedTokenAmountConsOther senderMessage withdrawnTokenAmoutConsOther)
    qed
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case True
      then show ?thesis
        using CANCEL_WD * reachableFrom_step.hyps 
        using callCancelDepositWhileDeadBalanceOfContract[of contractsI' address' "message caller' 0" block ID' token' amount' proof' contractsI]
        by auto
    next
      case False
      have "caller' \<noteq> tokenDepositAddress"
        sorry
      then show ?thesis
        using False CANCEL_WD * reachableFrom_step.hyps 
        using callCancelDepositWhileDeadBalanceOfOther callCancelDepositWhileDeadOtherToken
        using canceledTokenAmountConsCancelOther depositedTokenAmoutConsOther withdrawnTokenAmoutConsOther releasedTokenAmountConsOther
        using senderMessage
        by (metis (no_types, lifting) Step.simps(19) Step.simps(49) Step.simps(63) executeStep.simps(7))
    qed
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case True
      then show ?thesis
        using WITHDRAW_WD * reachableFrom_step.hyps 
        using callWithdrawWhileDeadBalanceOfContract[of contractsI' address' "message caller' 0" block token' amount' proof' contractsI]
        by auto
    next
      case False
      have "caller' \<noteq> tokenDepositAddress"
        sorry
      then show ?thesis
        using False WITHDRAW_WD * reachableFrom_step.hyps 
        using callWithdrawWhileDeadBalanceOfOther[of contractsI' address' "message caller' 0" block token' amount' proof' contractsI tokenDepositAddress] 
        using callWithdrawWhileDeadOtherToken[of token token' contractsI' address' "message caller' 0" block amount' proof' contractsI]
        by (smt (verit, del_insts) Step.simps(21) Step.simps(51) Step.simps(63) Step.simps(8) canceledTokenAmountConsOther depositedTokenAmoutConsOther executeStep.simps(8) releasedTokenAmountConsOther senderMessage withdrawnTokenAmoutConsOther)
    qed
  next
    case (BURN address' caller' ID' token' amount')
    have "mintedTokenB contractsI' address' token' \<noteq> token"
      sorry
    then have "accountBalance contractsI token tokenDepositAddress = 
               accountBalance contractsI' token tokenDepositAddress"
      using callWithdrawOtherToken[of contractsI' address' "message caller' 0" ID']
      using BURN reachableFrom_step.hyps
      by simp
    then show ?thesis
      using * BURN
      by simp
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case True
      then show ?thesis
        using RELEASE * reachableFrom_step.hyps 
        using callReleaseBalanceOfContract[of contractsI' address' "message caller' 0" ID' token' amount' proof' contractsI]
        by auto
    next
      case False
      have "caller' \<noteq> tokenDepositAddress"
        sorry
      then show ?thesis
        using False RELEASE * reachableFrom_step.hyps 
        using callReleaseBalanceOfOther[of contractsI' address' "message caller' 0" ID' token' amount' proof' contractsI tokenDepositAddress] 
        using callReleaseOtherToken[of token token' contractsI' address' "message caller' 0" ID' amount' proof' contractsI]
        by (metis Step.simps(13) Step.simps(49) Step.simps(51) canceledTokenAmountConsOther depositedTokenAmoutConsOther executeStep.simps(4) realesedTokenAmountConsReleaseOther senderMessage withdrawnTokenAmoutConsOther)
    qed
  qed
qed

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Claimed and non-claimed before death\<close>

context HashProofVerifier
begin

definition claimedBeforeDeathTokenDeposits where
  "claimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore) 
            (tokenDeposits tokenDepositAddress token steps)"

lemma claimedBeforeDeathTokenDepositsConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "claimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         claimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding claimedBeforeDeathTokenDeposits_def
  by (cases step, auto)

end

context InitFirstUpdate
begin

lemma claimedBeforeDeathTokenDepositsClaimedTokenDeposits:
  assumes "stepsInit = steps @ stepsBefore"
  shows
    "claimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore) =
     claimedTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore"
proof-
  have "filter (\<lambda>step. isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore)
               (tokenDeposits tokenDepositAddress token steps) = []"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain step where *: "step \<in> set (tokenDeposits tokenDepositAddress token steps)"
                           "isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore"
      by (meson filter_False)
    obtain caller ID amount where 
       deposit: "step = DEPOSIT tokenDepositAddress caller ID token amount"
      using *(1)
      unfolding tokenDeposits_def
      by (metis filter.simps(2) filter_set member_filter not_Cons_self tokenDepositsOther tokenDeposits_def)

    then obtain caller' amount' proof' where
      "CLAIM bridgeAddress caller' ID token amount' proof' \<in> set stepsBefore"
      using *(2)
      by (auto simp add: isClaimedID_def)

    moreover
    have "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
      using *(1) tokenDepositsSubsetSteps deposit
      by blast
   
    ultimately show False
      using assms noClaimBeforeDepositSteps'
      by blast
  qed
  then show ?thesis
    unfolding claimedBeforeDeathTokenDeposits_def claimedTokenDeposits_def
    by simp
qed

lemma claimedBeforeDeathTokenDepositsCons [simp]:
  assumes "stepsInit = (step # steps) @ stepsBefore"
  shows "claimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps @ stepsBefore) =
         claimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
proof (cases "stepsBefore=[]")
  case True
  then show ?thesis
    using assms
    by (simp add: claimedBeforeDeathTokenDeposits_def isClaimedID_def)
next
  case False
  obtain contracts where "reachableFrom contractsInit contracts (steps @ stepsBefore)" "reachableFrom contracts contractsI [step]"
    using assms
    by (metis append_Cons append_self_conv2 reachableFromAppend reachableFromInitI)

  interpret IFU: InitFirstUpdate where contractsI=contracts and stepsInit="steps @ stepsBefore"
    by (metis (no_types, lifting) False Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def \<open>reachableFrom contractsInit contracts (steps @ stepsBefore)\<close> append_Cons append_is_Nil_conv assms firstUpdate last_appendR updatesNonZeroCons(1) updatesNonZeroInit)

  show ?thesis
    using claimedBeforeDeathTokenDepositsClaimedTokenDeposits[OF assms, of token]
    using IFU.claimedBeforeDeathTokenDepositsClaimedTokenDeposits[of steps stepsBefore token]
    by simp
qed

end

context HashProofVerifier
begin

definition claimedBeforeDeathTokenDepositsAmount where
  "claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (claimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma claimedBeforeDeathTokenDepositsAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms claimedBeforeDeathTokenDepositsAmount_def)

end

context InitFirstUpdate
begin

lemma claimedBeforeDeathTokenDepositsAmountClaimedTokenDepositsAmount:
  assumes "stepsInit = steps @ stepsBefore"
  shows "claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore) =
         claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore"
  using assms claimedTokenDepositsAmount_def claimedBeforeDeathTokenDepositsAmount_def claimedBeforeDeathTokenDepositsClaimedTokenDeposits
  by auto


lemma claimedBeforeDeathTokenDepositsAmountCons [simp]:
  assumes "stepsInit = (step # steps) @ stepsBefore"
  shows "claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps @ stepsBefore) =
         claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
  by (simp add: assms claimedBeforeDeathTokenDepositsAmount_def)

end

context HashProofVerifier
begin

definition nonClaimedBeforeDeathTokenDeposits where
  "nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore) 
            (tokenDeposits tokenDepositAddress token steps)"

lemma nonClaimedTokenDepositsBeforeDeathConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeDeathTokenDeposits_def
  by (cases step, auto)

definition nonClaimedBeforeDeathTokenDepositsAmount where
  "nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (nonClaimedBeforeDeathTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma nonClaimedBeforeDeathTokenDepositsAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms nonClaimedBeforeDeathTokenDepositsAmount_def)

end


context HashProofVerifier
begin

text \<open>All deposits are either claimed before death or not claimed before death\<close>
theorem depositTokenAmountEqualsClaimedPlusNonClaimed:
  shows "depositedTokenAmount tokenDepositAddress token steps = 
         claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps + 
         nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  unfolding depositedTokenAmount_def claimedBeforeDeathTokenDepositsAmount_def nonClaimedBeforeDeathTokenDepositsAmount_def
  by (simp add: claimedBeforeDeathTokenDeposits_def nonClaimedBeforeDeathTokenDeposits_def sum_list_filter_P_notP)

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Non claimed before death and not canceled token deposits\<close>

context HashProofVerifier
begin

(* NOTE: only on the given token *)
definition isCanceledID where
  "isCanceledID tokenDepositAddress token ID steps \<longleftrightarrow> 
   (\<exists> caller amount proof. CANCEL_WD tokenDepositAddress caller ID token amount proof \<in> set steps)"

definition nonClaimedBeforeDeathNonCanceledTokenDeposits where
  "nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore \<and>
                     \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) steps)
            (tokenDeposits tokenDepositAddress token steps)"

lemma nonClaimedBeforeDeathNonCanceledTokenDepositsConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  assumes "\<nexists> caller' ID' amount' proof'. step = CANCEL_WD tokenDepositAddress caller' ID' token amount' proof'"
  shows "nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeDeathNonCanceledTokenDeposits_def tokenDeposits_def
  by (smt (verit, ccfv_SIG) filter.simps(2) filter_cong isCanceledID_def isTokenDeposit.elims(2) list.set_intros(2) set_ConsD)

definition nonClaimedBeforeDeathNonCanceledTokenDepositsAmount where
  "nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma nonClaimedBeforeDeathNonCanceledTokenDepositsAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  assumes "\<nexists> caller' ID' amount' proof'. step = CANCEL_WD tokenDepositAddress caller' ID' token amount' proof'"
  shows "nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms nonClaimedBeforeDeathNonCanceledTokenDepositsAmount_def)

end

context InitUpdateBridgeNotDeadLastValidState
begin

lemma nonClaimedBeforeDeathNonCanceledTokenDepositsConsCancel:
  assumes "reachableFrom contractsLVS contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
  shows "\<exists> steps1 steps2.
           nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS = 
           steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2 \<and>
           nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsInit (CANCEL_WD tokenDepositAddress caller ID token amount proof # stepsAllLVS) = 
           steps1 @ steps2"
proof-
  define CANCEL_step where "CANCEL_step = CANCEL_WD tokenDepositAddress caller ID token amount proof"
  define DEPOSIT_step where "DEPOSIT_step = DEPOSIT tokenDepositAddress (sender (message caller 0)) ID token amount"
  define P where "P = (\<lambda>step.
         \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
         \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsAllLVS)"
  define P' where "P' = (\<lambda>step.
         \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
         \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) (CANCEL_step # stepsAllLVS))"
  define Q where "Q = (\<lambda> step. isTokenDeposit tokenDepositAddress token step)"
  define depositsAll where "depositsAll = tokenDeposits tokenDepositAddress token stepsAllLVS"
  define non where "non = nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS"
  define nonCancel where "nonCancel = nonClaimedBeforeDeathNonCanceledTokenDeposits tokenDepositAddress bridgeAddress token stepsInit (CANCEL_step # stepsAllLVS)"

  obtain block "proof" where 
    cancel: "callCancelDepositWhileDead contractsLVS tokenDepositAddress (message caller 0) block ID token amount proof =
    (Success, contractsCancel)"
    using assms
    by (metis executeStep.simps(7) reachableFromSingleton)

  then have "DEPOSIT_step \<in> set stepsAllLVS"
    unfolding DEPOSIT_step_def
    by  (rule InitLVS.cancelDepositOnlyAfterDeposit)
  then obtain steps1 steps2 where steps: "stepsAllLVS = steps1 @ [DEPOSIT_step] @ steps2"
    by (metis append_Cons append_self_conv2 split_list)
  then have "DEPOSIT_step \<in> set (tokenDeposits tokenDepositAddress token stepsAllLVS)"
    unfolding tokenDeposits_def DEPOSIT_step_def
    by auto

  moreover

  have "\<nexists> caller' token' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
    using cancel
    by (simp add: cancelDepositWhileDeadNoClaim)

  moreover

  have noCancel: "\<nexists> caller' token' amount' proof'. 
          CANCEL_WD tokenDepositAddress caller' ID token' amount' proof' \<in> set stepsAllLVS"
    using CANCELNoDoubleCons assms reachableFromSingleton reachableFrom_step reachableFromInitLVS
    by meson

  ultimately

  have "DEPOSIT_step \<in> set non"
    unfolding non_def
    unfolding nonClaimedBeforeDeathNonCanceledTokenDeposits_def DEPOSIT_step_def isClaimedID_def isCanceledID_def
    by auto
  have *: "\<forall> step \<in> set (steps1 @ steps2). (\<forall> caller' amount' ID'. step = DEPOSIT tokenDepositAddress caller' ID' token amount' \<longrightarrow> ID' \<noteq> ID)"
    using steps DEPOSITNoDouble' InitLVS.reachableFromInitI 
    unfolding DEPOSIT_step_def
    by blast
  then have "DEPOSIT_step \<notin> set (steps1 @ steps2)"
    unfolding DEPOSIT_step_def
    by auto

  have depositsAll: "depositsAll = (filter Q steps1) @ [DEPOSIT_step] @ (filter Q steps2)"
    using steps
    unfolding depositsAll_def tokenDeposits_def Q_def DEPOSIT_step_def
    by auto

  define c1 where "c1 = filter P' (filter Q steps1)" 
  define c2 where "c2 = filter P' (filter Q steps2)" 

  have "\<not> P' DEPOSIT_step"
    unfolding P'_def DEPOSIT_step_def CANCEL_step_def
    by (auto simp add: isCanceledID_def)
  then have nonCancel:
    "nonCancel = c1 @ c2"
    using depositsAll \<open>\<not> P' DEPOSIT_step\<close>
    unfolding nonCancel_def c1_def c2_def depositsAll_def nonClaimedBeforeDeathNonCanceledTokenDeposits_def P'_def
    by (simp add: CANCEL_step_def)

  have "DEPOSIT_step \<notin> set (c1 @ c2)"
    using \<open>DEPOSIT_step \<notin> set (steps1 @ steps2)\<close>
    unfolding c1_def c2_def
    by auto

  have "\<And> steps. set steps \<subseteq> set steps1 \<union> set steps2 \<Longrightarrow> filter P (filter Q steps) = filter P' (filter Q steps)"
  proof (rule filter_cong)
    fix steps step
    assume "set steps \<subseteq> set steps1 \<union> set steps2" "step \<in> set (filter Q steps)"
    then obtain caller' ID' amount' where "step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
      unfolding Q_def
      by (smt (verit, best) isTokenDeposit.elims(2) mem_Collect_eq set_filter)
    then show "P step \<longleftrightarrow> P' step"
      using * \<open>set steps \<subseteq> set steps1 \<union> set steps2\<close> \<open>step \<in> set (filter Q steps)\<close>
      unfolding P_def P'_def CANCEL_step_def
      by (auto simp add: isCanceledID_def)
  qed simp
  then have "non = c1 @ filter P [DEPOSIT_step] @ c2"
    unfolding non_def nonClaimedBeforeDeathNonCanceledTokenDeposits_def P_def c1_def c2_def
    using depositsAll depositsAll_def
    by auto
  then have non: "non = c1 @ [DEPOSIT_step] @ c2"
    using \<open>DEPOSIT_step \<in> set non\<close> \<open>DEPOSIT_step \<notin> set (c1 @ c2)\<close>
    by (metis append.assoc append.right_neutral filter.simps(1) filter.simps(2))

  show ?thesis
    using nonCancel non
    using CANCEL_step_def DEPOSIT_step_def nonCancel_def non_def 
    by auto
qed

lemma nonClaimedBeforeDeathNonCanceledTokenDepositsAmountCancel:
  assumes "reachableFrom contractsLVS contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
  shows "nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit (CANCEL_WD tokenDepositAddress caller ID token amount proof # stepsAllLVS) =
         nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS - amount"
        "amount \<le> nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS"
  using nonClaimedBeforeDeathNonCanceledTokenDepositsConsCancel[OF assms]
  unfolding nonClaimedBeforeDeathNonCanceledTokenDepositsAmount_def
  by auto

end

text \<open>Before the bridge dies all non-claimed token deposits are not canceled\<close>
context StrongHashProofVerifier
begin

lemma nonCanceledNonClaimedBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
    shows "nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
           nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms noCancelBeforeBridgeDead[OF assms]
  unfolding nonClaimedBeforeDeathNonCanceledTokenDepositsAmount_def nonClaimedBeforeDeathTokenDepositsAmount_def
  unfolding nonClaimedBeforeDeathNonCanceledTokenDeposits_def nonClaimedBeforeDeathTokenDeposits_def isCanceledID_def
  by metis

end


context BridgeDead
begin

lemma canceledAmountInvariant':
  shows
  "nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit  ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) + 
   canceledTokenAmount tokenDepositAddress token ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) = 
   nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit)" (is "?NCC (stepsBD @ [stepDeath]) + ?C (stepsBD @ [stepDeath]) = ?NC (stepsBD @ [stepDeath])")
  using reachableFromContractsBD BridgeDead_axioms
proof (induction contractsDead contractsBD stepsBD rule: reachableFrom.induct)
  case (reachableFrom_base contractsBD)
  then interpret BD: BridgeDead where contractsBD=contractsBD and stepsBD="[]" and contractsDead=contractsBD
    .
  have *: "?NCC [] + ?C [] = ?NC []"
    using LVSDead'.reachableFromInitLVS canceledTokenAmountBridgeNotDead nonCanceledNonClaimedBridgeNotDead notBridgeDead'
    unfolding LVSDead'.stepsAllLVS_def
    by auto

  show ?case
    using *
  proof (cases stepDeath)
    case (DEPOSIT address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case True
      have "bridgeDead contractsBD tokenDepositAddress"
        using  BD.bridgeDead DEPOSIT
        by auto
      then show ?thesis
        using DEPOSIT True callDepositNotBridgeDead'
        using reachableFromSingleton[OF BD.deathStep] 
        by (metis executeStep.simps(1))
    next
      case False
      then show ?thesis
        using * DEPOSIT 
        by force
    qed
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case False
      then show ?thesis
        using * CANCEL_WD
        by (cases "address' = tokenDepositAddress") auto
    next
      case True
      have "?NC [stepDeath] = ?NC []"
        using CANCEL_WD
        by auto
      moreover
      have "?NCC [stepDeath] = ?NCC [] - amount' \<and> amount' \<le> ?NCC []"
        using LVSDead'.nonClaimedBeforeDeathNonCanceledTokenDepositsAmountCancel
        using BD.deathStep CANCEL_WD LVSDead'.stepsAllLVS_def True by auto
      moreover
      have "?C [stepDeath] = ?C [] + amount'"
        by (simp add: CANCEL_WD True)
      ultimately
      show ?thesis
        using *
        by simp
    qed
  qed auto
next
  case (reachableFrom_step steps contractsBD contractsDead contractsBD' blockNum block step)

  interpret BD': BridgeDead where contractsBD=contractsBD and stepsBD="step#steps" and contractsDead=contractsDead
    using reachableFrom_step.prems by fastforce

  interpret BD: BridgeDead where contractsBD=contractsBD' and stepsBD=steps and contractsDead=contractsDead
  proof
    show "\<not> bridgeDead contractsDead' tokenDepositAddress"
      using notBridgeDead' by blast
  next
    show "reachableFrom contractsDead contractsBD' steps"
      using reachableFrom_step.hyps
      by simp
  next
    show "reachableFrom contractsDead' contractsDead [stepDeath]"
      by (meson BridgeDead.deathStep reachableFrom_step.prems)
  next
    show "bridgeDead contractsDead tokenDepositAddress"
      by (meson BridgeDead.bridgeDead reachableFrom_step.prems)
  next
    show "stateRoot \<noteq> 0"
      using stateRootNonZero
      by simp
  qed

  have *: "?NCC (steps @ [stepDeath]) + ?C (steps @ [stepDeath]) = ?NC (steps @ [stepDeath])"
    using reachableFrom_step.IH[OF BD.BridgeDead_axioms]
    by simp

  show ?case
    using *
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case True
      have "bridgeDead contractsBD' tokenDepositAddress"
        using reachableFrom_step.hyps BD.bridgeDead DEPOSIT
        by auto
      then show ?thesis
        using DEPOSIT reachableFrom_step.hyps True
        by (metis callDepositFailsInDeadState executeStep.simps(1) fst_conv)
    next
      case False
      then show ?thesis
        using * DEPOSIT 
        by force
    qed
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case False
      then show ?thesis
        using * CANCEL_WD
        by auto
    next
      case True
      have "?NC (step # (steps @ [stepDeath])) = ?NC (steps @ [stepDeath])"
        using CANCEL_WD
        by auto
      moreover
      have "?NCC (step # steps @ [stepDeath]) = ?NCC (steps @ [stepDeath]) - amount' \<and> amount' \<le> ?NCC (steps @ [stepDeath])"
        by (metis BD.LVSBD.nonClaimedBeforeDeathNonCanceledTokenDepositsAmountCancel(1) BD.LVSBD.nonClaimedBeforeDeathNonCanceledTokenDepositsAmountCancel(2) BD.LVSBD.stepsAllLVS_def CANCEL_WD Cons_eq_append_conv True append_eq_appendI reachableFrom.reachableFrom_step reachableFrom_base reachableFrom_step.hyps(2))
      moreover
      have "?C (step # steps @ [stepDeath]) = ?C (steps @ [stepDeath]) + amount'"
        by (simp add: CANCEL_WD True)
      ultimately
      show ?thesis
        using *
        by simp
    qed
  qed auto
qed

theorem canceledAmountInvariant:
  shows
  "nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD + 
   canceledTokenAmount tokenDepositAddress token stepsAllBD = 
   nonClaimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
  unfolding stepsAllBD_def
  using canceledAmountInvariant'[of token]
  by auto  
end



(* ------------------------------------------------------------------------------------ *)
section \<open>Minted token balance of all users (affected by claims, transfers and burns) \<close>

context HashProofVerifier
begin

fun isTokenTransfer where
  "isTokenTransfer bridgeAddress token (TRANSFER address' caller receiver token' amount) \<longleftrightarrow> address' = bridgeAddress \<and> token' = token"
| "isTokenTransfer bridgeAddress token _ = False"


definition tokenClaimsTransfersBurns where
  "tokenClaimsTransfersBurns bridgeAddress token steps = 
      filter (\<lambda> step. isTokenClaim bridgeAddress token step \<or> 
                      isTokenTransfer bridgeAddress token step \<or>
                      isTokenBurn bridgeAddress token step) steps"


lemma tokenClaimsTransfersBurnsNil [simp]:
  shows "tokenClaimsTransfersBurns bridgeAddress token [] = []"
  by (simp add: tokenClaimsTransfersBurns_def)

lemma tokenClaimsTransfersBurnsConsOther [simp]: 
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"  
  assumes "\<nexists> caller' receiver' amount' proof'. step = TRANSFER bridgeAddress caller' receiver' token amount'"
  assumes "\<nexists> caller' ID' amount'. step = BURN bridgeAddress caller' ID' token amount'"
  shows "tokenClaimsTransfersBurns bridgeAddress token (step # steps) = 
         tokenClaimsTransfersBurns bridgeAddress token steps"
  using assms
  by (cases step) (auto simp add: tokenClaimsTransfersBurns_def)

lemma tokenClaimsTransfersBurnsConsClaim [simp]: 
  shows "tokenClaimsTransfersBurns bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof # steps) = 
         CLAIM bridgeAddress caller ID token amount proof # tokenClaimsTransfersBurns bridgeAddress token steps"
  by (simp add: tokenClaimsTransfersBurns_def)

lemma tokenClaimsTransfersBurnsConsTransfer [simp]: 
  shows "tokenClaimsTransfersBurns bridgeAddress token (TRANSFER bridgeAddress caller receiver token amount # steps) = 
         TRANSFER bridgeAddress caller receiver token amount # tokenClaimsTransfersBurns bridgeAddress token steps"
  by (simp add: tokenClaimsTransfersBurns_def)

lemma tokenClaimsTransfersBurnsConsBurn [simp]: 
  shows "tokenClaimsTransfersBurns bridgeAddress token (BURN bridgeAddress caller ID token amount # steps) = 
         BURN bridgeAddress caller ID token amount # tokenClaimsTransfersBurns bridgeAddress token steps"
  by (simp add: tokenClaimsTransfersBurns_def)

definition tokenClaimsTransfersBurnsBalances_fun where
  "tokenClaimsTransfersBurnsBalances_fun step state = 
       (case step of CLAIM address caller ID token amount proof \<Rightarrow> addToBalance state caller amount 
                   | TRANSFER address caller receiver token amount \<Rightarrow> transferBalance state caller receiver amount
                   | BURN address caller ID token amount \<Rightarrow> removeFromBalance state caller amount
                   | _ \<Rightarrow> state)"

lemma tokenClaimsTransfersBurnsBalances_funFiniteKeys [simp]:
  assumes "finite (Mapping.keys (balances state))"
  shows "finite (Mapping.keys (balances (tokenClaimsTransfersBurnsBalances_fun step state)))"
  using assms
  by (cases step) (auto simp add: tokenClaimsTransfersBurnsBalances_fun_def addToBalance_def transferBalance_def removeFromBalance_def)

definition tokenClaimsTransfersBurnsBalances' :: "address \<Rightarrow> address \<Rightarrow> Step list \<Rightarrow> ERC20State" where
  "tokenClaimsTransfersBurnsBalances' address token steps = 
    foldr tokenClaimsTransfersBurnsBalances_fun steps ERC20Constructor"

definition tokenClaimsTransfersBurnsBalances :: "address \<Rightarrow> address \<Rightarrow> Step list \<Rightarrow> ERC20State" where
 "tokenClaimsTransfersBurnsBalances bridgeAddress token steps = 
  tokenClaimsTransfersBurnsBalances' bridgeAddress token (tokenClaimsTransfersBurns bridgeAddress token steps)"

lemma tokenClaimsTransfersBurnsBalances'Nil [simp]:
  shows "tokenClaimsTransfersBurnsBalances' bridgeAddress token [] = ERC20Constructor"
  by (simp add: tokenClaimsTransfersBurnsBalances'_def)

lemma tokenClaimsTransfersBurnsBalancesCons:
 "tokenClaimsTransfersBurnsBalances' bridgeAddress token (step # steps) = 
  tokenClaimsTransfersBurnsBalances_fun step (tokenClaimsTransfersBurnsBalances' bridgeAddress token steps)"
  unfolding tokenClaimsTransfersBurnsBalances'_def
  by simp

lemma tokenClaimsTransfersBurnsBalance'_finiteKeys [simp]:
  shows "finite (Mapping.keys (balances (tokenClaimsTransfersBurnsBalances' bridgeAddress token steps)))"
  by (induction steps) (auto simp add: tokenClaimsTransfersBurnsBalancesCons)

lemma tokenClaimsTransfersBurnsBalancesNil [simp]:
  shows "tokenClaimsTransfersBurnsBalances bridgeAddress token [] = ERC20Constructor"
  by (simp add: tokenClaimsTransfersBurnsBalances_def)

lemma tokenClaimsTransfersBurnsBalancesConsOther [simp]:
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"  
  assumes "\<nexists> caller' receiver' amount' proof'. step = TRANSFER bridgeAddress caller' receiver' token amount'"  
  assumes "\<nexists> caller' ID' amount'. step = BURN bridgeAddress caller' ID' token amount'"  
  shows "tokenClaimsTransfersBurnsBalances bridgeAddress token (step # steps) = 
         tokenClaimsTransfersBurnsBalances bridgeAddress token steps"
  using assms
  unfolding tokenClaimsTransfersBurnsBalances_def
  by simp

lemma tokenClaimsTransfersBurnsBalances'ConsClaim [simp]:
  shows "tokenClaimsTransfersBurnsBalances' bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof # steps) = 
         addToBalance (tokenClaimsTransfersBurnsBalances' bridgeAddress token steps) caller amount"
  unfolding tokenClaimsTransfersBurnsBalances'_def
  by (simp add: tokenClaimsTransfersBurnsBalances_fun_def)

lemma tokenClaimsTransfersBurnsBalancesConsClaim [simp]:
  shows "tokenClaimsTransfersBurnsBalances bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof # steps) = 
         addToBalance (tokenClaimsTransfersBurnsBalances bridgeAddress token steps) caller amount"
  unfolding tokenClaimsTransfersBurnsBalances_def
  by simp

lemma tokenClaimsTransfersBurnsBalance'ConsTransfer [simp]:
  shows "tokenClaimsTransfersBurnsBalances' bridgeAddress token (TRANSFER bridgeAddress caller receiver token amount # steps) = 
         transferBalance (tokenClaimsTransfersBurnsBalances' bridgeAddress token steps) caller receiver amount"
  unfolding tokenClaimsTransfersBurnsBalances'_def
  by (simp add: tokenClaimsTransfersBurnsBalances_fun_def)

lemma tokenClaimsTransfersBurnsBalanceConsTransfer [simp]:
  shows "tokenClaimsTransfersBurnsBalances bridgeAddress token (TRANSFER bridgeAddress caller receiver token amount # steps) = 
         transferBalance (tokenClaimsTransfersBurnsBalances bridgeAddress token steps) caller receiver amount"
  unfolding tokenClaimsTransfersBurnsBalances_def
  by simp

lemma tokenClaimsTransfersBurnsBalance'ConsBurn [simp]:
  shows "tokenClaimsTransfersBurnsBalances' bridgeAddress token (BURN bridgeAddress caller ID token amount # steps) = 
         removeFromBalance (tokenClaimsTransfersBurnsBalances' bridgeAddress token steps) caller amount"
  unfolding tokenClaimsTransfersBurnsBalances'_def
  by (simp add: tokenClaimsTransfersBurnsBalances_fun_def)

lemma tokenClaimsTransfersBurnsBalanceConsBurn [simp]:
  shows "tokenClaimsTransfersBurnsBalances bridgeAddress token (BURN bridgeAddress caller ID token amount # steps) = 
         removeFromBalance (tokenClaimsTransfersBurnsBalances bridgeAddress token steps) caller amount"
  unfolding tokenClaimsTransfersBurnsBalances_def
  by simp


lemma tokenClaimsTransfersBurnsBalances_finiteKeys [simp]:
  shows "finite (Mapping.keys (balances (tokenClaimsTransfersBurnsBalances bridgeAddress token steps)))"
  unfolding tokenClaimsTransfersBurnsBalances_def
  by simp


text \<open>Claims, burns and transfers faithfully represent balances of minted tokens on the bridge\<close>
theorem tokenClaimsTransfersBurnsBalanceAccountBalance:
  assumes "reachableFrom contracts contracts' steps"
  assumes "accountBalance contracts (mintedTokenB contracts bridgeAddress token) account = 0"
  shows "balanceOf (tokenClaimsTransfersBurnsBalances bridgeAddress token steps) account = 
         accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then have *: 
    "balanceOf (tokenClaimsTransfersBurnsBalances bridgeAddress token steps) account =
    accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account"
    using reachableFrom_step
    by blast
    
  show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = bridgeAddress \<and> token' = token \<and> caller' = account")
      case True
      then show ?thesis
        using CLAIM * reachableFrom_step.hyps 
        using callClaimBalanceOfMinted[of contracts' bridgeAddress "message caller' amount'" ID' token amount' proof' contracts'']
        by simp
    next
      case False
      have "mintedTokenB contracts bridgeAddress token \<noteq> mintedTokenB contracts address' token'"
        sorry
      then show ?thesis
        using False CLAIM * reachableFrom_step.hyps 
        using  callClaimOtherToken[of contracts' address'  "message caller' amount'"]
        by (cases "address' = bridgeAddress \<and> token' = token") auto
    qed
  next
    case (TRANSFER address' caller' receiver' token' amount')
    have transfer:
      "callTransfer contracts' address' caller' receiver' token' amount' = (Success, contracts'')"
        using TRANSFER reachableFrom_step.hyps
        by auto
    show ?thesis
    proof (cases "address' = bridgeAddress \<and> token' = token \<and> caller' = account")
      case True
      have "account \<noteq> receiver'"
        sorry
      show ?thesis
        using True TRANSFER * reachableFrom_step.hyps
        using callTransferBalanceOfCaller[OF transfer]
        using transferBalanceBalanceOfTo[OF \<open>account \<noteq> receiver'\<close>]
        by (metis reachableFromBridgeTokenPairs reachableFromITokenPairs tokenClaimsTransfersBurnsBalanceConsTransfer)
    next
      case False
      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token' = token")
        case True
        then have "account \<noteq> caller'"
          using False
          by auto
        have "caller' \<noteq> receiver'" "account \<noteq> receiver'"
          sorry
        have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
              accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
          using callTransferBalanceOfOther[OF _ _ transfer] True  \<open>account \<noteq> caller'\<close> \<open>account \<noteq> receiver'\<close>
          by (metis (no_types, opaque_lifting) reachableFromBridgeTokenPairs reachableFromITokenPairs reachableFrom_step.hyps(1))
        then show ?thesis
          using transferBalanceBalanceOfOther *
          using TRANSFER True \<open>account \<noteq> caller'\<close> \<open>account \<noteq> receiver'\<close> addToBalanceBalanceOfOther removeFromBalanceBalanceOfOther tokenClaimsTransfersBurnsBalanceConsTransfer transferBalance_def 
          by presburger
      next
        case False
        have m: "mintedTokenB contracts' address' token' \<noteq>
                 mintedTokenB contracts bridgeAddress token"
          sorry
        have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
              accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
          using * callTransferOtherToken[OF transfer _ m]
          by auto
        then show ?thesis
          using * False transfer TRANSFER
          using tokenClaimsTransfersBurnsBalancesConsOther
          by (metis Step.simps(27) Step.simps(37) Step.simps(5))
      qed
    qed
  next
    case (UPDATE address' stateRoot)
    then show ?thesis
      using * reachableFrom_step.hyps
      by simp
  next
    case (DEPOSIT address' caller' ID' token' amount')
    have "mintedTokenB contracts bridgeAddress token \<noteq> token'"
      sorry
    then have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
               accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
      using callDepositOtherToken
      using DEPOSIT reachableFrom_step.hyps
      by simp
    then show ?thesis
      using DEPOSIT * reachableFrom_step.hyps
      by simp
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    have "mintedTokenB contracts bridgeAddress token \<noteq> token'"
      sorry
    then have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
               accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
      using CANCEL_WD reachableFrom_step.hyps
      using callCancelDepositWhileDeadOtherToken 
      by (metis executeStep.simps(7))
    then show ?thesis
      using CANCEL_WD * reachableFrom_step.hyps
      by simp
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    have "mintedTokenB contracts bridgeAddress token \<noteq> token'"
      sorry
    then have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
               accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
      using WITHDRAW_WD reachableFrom_step.hyps
      using callWithdrawWhileDeadOtherToken 
      by (metis executeStep.simps(8))
    then show ?thesis
      using WITHDRAW_WD * reachableFrom_step.hyps
      by simp
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    have "mintedTokenB contracts bridgeAddress token \<noteq> token'"
      sorry
    then have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
               accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
      using callReleaseOtherToken
      using RELEASE reachableFrom_step.hyps
      by (metis executeStep.simps(4))
    then show ?thesis
      using RELEASE * reachableFrom_step.hyps
      by simp
  next
    case (BURN address' caller' ID' token' amount') 
    show ?thesis
    proof (cases "address' = bridgeAddress \<and> token' = token \<and> caller' = account")
      case True
      then show ?thesis
        using BURN * reachableFrom_step.hyps 
        using callWithdrawBalanceOfSender[of contracts' bridgeAddress "message caller' 0"]
        by simp
    next
      case False
      have "mintedTokenB contracts bridgeAddress token \<noteq> mintedTokenB contracts address' token'"
        sorry
      then show ?thesis
        using False BURN * reachableFrom_step.hyps 
        using  callWithdrawOtherToken[of contracts' address'  "message caller' 0"]
        by (cases "address' = bridgeAddress \<and> token' = token") auto
    qed
  qed
qed

theorem tokenClaimsTransfersBurnsBalanceAccountTotalBalance:
  assumes "reachableFrom contracts contracts' steps"
  assumes "totalMinted contracts bridgeAddress token = 0"
  assumes "finiteBalances contracts (mintedTokenB contracts bridgeAddress token)"
  shows "totalBalance (tokenClaimsTransfersBurnsBalances bridgeAddress token steps) =
         totalMinted contracts' bridgeAddress token"
proof (rule totalBalanceEq, safe)
  show "finite (Mapping.keys (balances (tokenClaimsTransfersBurnsBalances bridgeAddress token steps)))"
    by simp
next
  show "finite (Mapping.keys (balances (the (ERC20state contracts' (mintedTokenB contracts' bridgeAddress token)))))"
    by (metis assms(1) assms(3) finiteBalances_def reachableFromBridgeTokenPairs reachableFromFiniteBalances reachableFromITokenPairs)
next
  fix user
  have "finite (Mapping.keys (balances (the (ERC20state contracts (mintedTokenB contracts bridgeAddress token))))) "
    using assms(3) finiteBalances_def by blast
  then show "balanceOf (tokenClaimsTransfersBurnsBalances bridgeAddress token steps) user = 
        accountBalance contracts' (mintedTokenB contracts' bridgeAddress token) user"
    using tokenClaimsTransfersBurnsBalanceAccountBalance assms totalBalanceZero reachableFromBridgeMintedToken
    by metis
qed

end

context InitFirstUpdate
begin

lemma tokenClaimsTransfersBurnsBalanceClaimedBurnedTokenAmount:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  assumes "finiteBalances contractsInit (mintedTokenB contractsInit bridgeAddress token)"
  shows "totalBalance (tokenClaimsTransfersBurnsBalances bridgeAddress token stepsInit) + 
         burnedTokenAmount bridgeAddress token stepsInit =
         claimedTokenAmount bridgeAddress token stepsInit"
  using tokenClaimsTransfersBurnsBalanceAccountTotalBalance[OF reachableFromInitI]
        totalMintedBridgeNotDead
  using assms
  by (metis add_cancel_right_left)

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Minted token balance of users that have not withdrawn their funds when the bridge died) \<close>

context HashProofVerifier
begin

definition nonWithdrawnTokenClaimsTransfersBurnsBalances_fun where
  "nonWithdrawnTokenClaimsTransfersBurnsBalances_fun tokenDepositAddress token step state = 
    (case step of WITHDRAW_WD address' caller' token' amount' proof' \<Rightarrow> 
                    if address' = tokenDepositAddress \<and> token' = token then 
                       removeFromBalance state caller' amount'
                    else
                       state
                   | _ \<Rightarrow> state)"

lemma nonWithdrawnTokenClaimsTransfersBurnsBalances_funOther [simp]:
  assumes "\<nexists> caller amount proof. step = WITHDRAW_WD tokenDepositAddress caller token amount proof"
  shows "nonWithdrawnTokenClaimsTransfersBurnsBalances_fun tokenDepositAddress token step state = state"
  using assms
  by (cases step, auto simp add: nonWithdrawnTokenClaimsTransfersBurnsBalances_fun_def)

lemma nonWithdrawnTokenClaimsTransfersBurnsBalances_funWithdraw [simp]:
  shows "nonWithdrawnTokenClaimsTransfersBurnsBalances_fun tokenDepositAddress token (WITHDRAW_WD tokenDepositAddress caller token amount proof) state = 
        removeFromBalance state caller amount"
  by (simp add: nonWithdrawnTokenClaimsTransfersBurnsBalances_fun_def)

definition nonWithdrawnTokenClaimsTransfersBurnsBalances where
  "nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore steps = 
    foldr (nonWithdrawnTokenClaimsTransfersBurnsBalances_fun tokenDepositAddress token) steps (tokenClaimsTransfersBurnsBalances bridgeAddress token stepsBefore)"

lemma nonWithdrawnTokenClaimsTransfersBurnsBalances_funFiniteKeys [simp]:
  assumes "finite (Mapping.keys (balances state))"
  shows "finite (Mapping.keys (balances (nonWithdrawnTokenClaimsTransfersBurnsBalances_fun address token step state)))"
  using assms
  by (cases step, auto simp add: nonWithdrawnTokenClaimsTransfersBurnsBalances_fun_def removeFromBalance_def)

lemma nonWithdrawnTokenClaimsTransfersBurnsBalancesNil [simp]:
  shows "nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore [] = 
         tokenClaimsTransfersBurnsBalances bridgeAddress token stepsBefore"
  by (simp add: nonWithdrawnTokenClaimsTransfersBurnsBalances_def)

lemma nonWithdrawnTokenClaimsTransfersBurnsBalancesCons:
  shows "nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore (step # steps) = 
         nonWithdrawnTokenClaimsTransfersBurnsBalances_fun tokenDepositAddress token step (nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore steps)"
  unfolding nonWithdrawnTokenClaimsTransfersBurnsBalances_def
  by simp

lemma nonWithdrawnTokenClaimsTransfersBurnsBalances_finiteKeys [simp]:
  shows "finite (Mapping.keys (balances (nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore steps)))"
  by (induction steps) (auto simp add: nonWithdrawnTokenClaimsTransfersBurnsBalancesCons)

lemma nonWithdrawnTokenClaimsTransfersBurnsBalancesConsOther:
  assumes "\<nexists> caller' ID' amount' proof'. step = WITHDRAW_WD tokenDepositAddress caller' token amount' proof'"  
  shows "nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore
           (step # steps) =
         nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore
           steps"
  using assms
  unfolding nonWithdrawnTokenClaimsTransfersBurnsBalances_def
  by (simp add: nonWithdrawnTokenClaimsTransfersBurnsBalancesCons)

lemma nonWithdrawnTokenClaimsTransfersBurnsBalancesWithdraw [simp]:
  shows "nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsInit
           (WITHDRAW_WD tokenDepositAddress caller token amount proof # steps @ stepsInit) = 
         removeFromBalance (nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsInit
           (steps @ stepsInit)) caller amount"
  unfolding nonWithdrawnTokenClaimsTransfersBurnsBalances_def
  by (simp add: nonWithdrawnTokenClaimsTransfersBurnsBalancesCons)

lemma nonWithdrawnTokenClaimsTransfersBurnsBalanceNoWithdraw:
  assumes "\<nexists>amount proof. WITHDRAW_WD tokenDepositAddress caller token amount proof \<in> set steps"
  shows "balanceOf (nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore steps) caller = 
         balanceOf (tokenClaimsTransfersBurnsBalances bridgeAddress token stepsBefore) caller"
  using assms
proof (induction steps)
  case Nil
  then show ?case
    by simp
next
  case (Cons step steps)
  then show ?case
    by (cases step, auto simp add: nonWithdrawnTokenClaimsTransfersBurnsBalancesCons nonWithdrawnTokenClaimsTransfersBurnsBalances_fun_def)
qed


lemma nonWithdrawnTokenClaimsTransfersBurnsBalanceBridgeDead:
  assumes "reachableFrom contractsInit contractsI stepsInit"
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore stepsInit = 
         tokenClaimsTransfersBurnsBalances bridgeAddress token stepsBefore"
  using assms
proof-
  have *: "\<nexists> caller amount proof. WITHDRAW_WD tokenDepositAddress caller token amount proof \<in> set stepsInit"
    using noWithdrawBeforeBridgeDead[OF assms]
    by auto
  show ?thesis
    using assms *
  proof (induction contractsInit contractsI stepsInit rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
  next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then have "\<nexists> caller amount proof. step = WITHDRAW_WD tokenDepositAddress caller token amount proof"
    by auto
  moreover have "deadStateTD contracts' tokenDepositAddress = 0"
    using reachableFrom.reachableFrom_step reachableFromBridgeDead reachableFrom_base reachableFrom_step.hyps(2) reachableFrom_step.prems(1) by blast
  ultimately show ?case
      using reachableFrom_step
      by (auto simp add: nonWithdrawnTokenClaimsTransfersBurnsBalancesCons)
  qed 
qed


definition nonWithdrawnNonBurnedClaimedBeforeDeathAmount where
  "nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore steps = 
   totalBalance (nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsBefore steps)"

lemma nonWithdrawnClaimedBeforeDeathAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount' proof'. step = WITHDRAW_WD tokenDepositAddress caller' token amount' proof'"  
  shows "nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore
          (step # steps) =
         nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore
          steps"
  unfolding nonWithdrawnNonBurnedClaimedBeforeDeathAmount_def
  using assms nonWithdrawnTokenClaimsTransfersBurnsBalancesCons nonWithdrawnTokenClaimsTransfersBurnsBalances_funOther 
  by presburger

lemma nonWithdrawnClaimedBeforeDeathAmountConsWithdraw[simp]: 
  assumes "amount \<le> balanceOf (nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsInit (steps @ stepsInit)) caller"
  shows
   "nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsInit
      (WITHDRAW_WD tokenDepositAddress caller token amount proof # steps @ stepsInit) = 
    nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsInit
      (steps @ stepsInit) - amount" 
   "amount \<le> nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsInit
      (steps @ stepsInit)"
  using assms totalBalance_removeFromBalance
  unfolding nonWithdrawnNonBurnedClaimedBeforeDeathAmount_def
  by auto

lemma nonWithdrawnClaimedBeforeDeathAmountBridgeNotDead:
  assumes "reachableFrom contractsInit contractsI (steps @ stepsBefore)"
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore) =
         totalBalance (tokenClaimsTransfersBurnsBalances bridgeAddress token stepsBefore)"
  unfolding nonWithdrawnNonBurnedClaimedBeforeDeathAmount_def
  using nonWithdrawnTokenClaimsTransfersBurnsBalanceBridgeDead[OF assms]
  by simp

end

context InitFirstUpdate
begin

theorem nonWithdrawnNotBurnedClaimedBeforeDeathAmountNotDead:
  assumes "stepsInit = steps @ stepsBefore"
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  assumes "finiteBalances contractsInit (mintedTokenB contractsInit bridgeAddress token)"
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore) +
         burnedTokenAmount bridgeAddress token stepsBefore =
         claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
proof-
  have "totalBalance (tokenClaimsTransfersBurnsBalances bridgeAddress token stepsBefore) + 
        burnedTokenAmount bridgeAddress token stepsBefore =
        claimedTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore"
  proof (cases "stepsBefore = []")
    case True
    then show ?thesis
      by simp
  next
    case False
    obtain contracts where "reachableFrom contractsInit contracts stepsBefore" "reachableFrom contracts contractsI steps"
      using reachableFromInitI assms(1)
      using reachableFromAppend by blast

    interpret IFU: InitFirstUpdate where contractsI=contracts and stepsInit=stepsBefore
      by (metis False Init'_axioms Init.intro InitFirstUpdate.intro InitFirstUpdate_axioms_def Init_axioms_def \<open>reachableFrom contractsInit contracts stepsBefore\<close> assms(1) firstUpdate last_appendR updatesNonZeroAppend(2) updatesNonZeroInit)
    show ?thesis
      using IFU.tokenClaimsTransfersBurnsBalanceClaimedBurnedTokenAmount IFU.tokenClaimsClaimedTokenDeposits
      using assms 
      by presburger
  qed
  then show ?thesis
    using claimedBeforeDeathTokenDepositsAmountClaimedTokenDepositsAmount[OF assms(1)]
    using nonWithdrawnClaimedBeforeDeathAmountBridgeNotDead
    using assms reachableFromInitI
    by presburger
qed

end

context BridgeDeadInitFirstUpdate
begin

theorem withdrawnAmountInvariant':
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  shows
  "withdrawnTokenAmount tokenDepositAddress token  ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) + 
   nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsInit ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) +
   burnedTokenAmount bridgeAddress token stepsInit = 
   claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit)" (is "?W (stepsBD @ [stepDeath]) + ?N (stepsBD @ [stepDeath]) + ?B = ?C (stepsBD @ [stepDeath])")
  using reachableFromContractsBD assms BridgeDeadInitFirstUpdate_axioms
proof (induction contractsDead contractsBD stepsBD rule: reachableFrom.induct)
  case (reachableFrom_base contractsBD)
  then interpret BD: BridgeDeadInitFirstUpdate where contractsBD=contractsBD and stepsBD="[]" and contractsDead=contractsBD
    by blast

  interpret IFUDead': InitFirstUpdate where contractsI=contractsDead' and stepsInit=stepsBeforeDeath
    by (metis InitDead'.Init_axioms InitFirstUpdate.intro InitFirstUpdate_axioms_def append_is_Nil_conv firstUpdate last_appendR list.distinct(1) stepsAllBD_def stepsBeforeDeath_def updatesNonZeroAppend(2) updatesNonZeroInit)

  interpret IFUDead: InitFirstUpdate where contractsI=contractsDead and stepsInit="stepDeath#stepsBeforeDeath"
    by (metis IFUDead'.firstUpdate InitDead.Init_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def append.left_neutral append_Cons last_ConsR list.distinct(1) stepsAllBD_def stepsBeforeDeath_def updatesNonZeroAppend(2) updatesNonZeroInit)

  have *: "?W [] + ?N [] + ?B = ?C []"
    using withdrawnTokenAmountBridgeNotDead[OF InitDead'.reachableFromInitI BD.notBridgeDead', of token]
    using IFUDead'.nonWithdrawnNotBurnedClaimedBeforeDeathAmountNotDead[where steps="stepsNoUpdate @ [UPDATE_step]" and stepsBefore=stepsInit and token=token]
    using notBridgeDead'
    using reachableFrom_base.prems
    unfolding BD.stepsBeforeDeath_def
    by simp

  show ?case
  proof (cases stepDeath)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (CANCEL_WD address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case False
      then show ?thesis
        using * WITHDRAW_WD
        by auto
    next
      case True
      obtain block where withdraw: "callWithdrawWhileDead contractsDead' tokenDepositAddress (message caller' 0) block token amount' proof' = (Success, contractsDead)"
        using WITHDRAW_WD
        by (metis True deathStep executeStep.simps(8) reachableFromSingleton)
      let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
      have "verifyBalanceProof () ?mintedToken caller' amount' stateRoot proof'"
        using callWithdrawWhileDeadVerifyBalanceProof[OF withdraw]
        by (metis LVSDead'.InitLVS.mintedTokenTDI LVSDead'.getLastValidStateLVS mintedTokenITDB senderMessage snd_conv)
      then have "accountBalance contractsLastUpdate' ?mintedToken caller' = amount'"
        by (metis (no_types, lifting) ERC20StateMintedTokenINotNone generateStateRootUpdate' mintedTokenITDB option.collapse reachableFrom_base.prems(1) verifyBalanceProofE)
      then have "balanceOf (tokenClaimsTransfersBurnsBalances bridgeAddress token stepsInit) caller' = amount'" 
        using tokenClaimsTransfersBurnsBalanceAccountBalance[OF reachableFromInitI totalBalanceZero, of bridgeAddress token caller']
        using reachableFrom_base.prems(2)
        using properTokenFiniteBalancesMinted reachableFrom_base.prems
        unfolding finiteBalances_def
        by blast
      then have **: "amount' \<le> balanceOf (nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsInit
          ((stepsNoUpdate @ [UPDATE_step]) @ stepsInit)) caller'"
        using nonWithdrawnTokenClaimsTransfersBurnsBalanceBridgeDead
        by (metis InitDead'.reachableFromInitI append.assoc le_refl notBridgeDead' stepsBeforeDeath_def)
      show ?thesis
        using nonWithdrawnClaimedBeforeDeathAmountConsWithdraw[OF **]
        using True * WITHDRAW_WD
        using IFUDead.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
        unfolding BD.stepsBeforeDeath_def
        by auto
    qed
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (RELEASE address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  qed
next
  case (reachableFrom_step stepsBD contractsBD'' contractsDead contractsBD' blockNum block step)
  interpret BD: BridgeDead where contractsDead=contractsDead and contractsBD=contractsBD' and stepsBD=stepsBD
    by (metis BridgeDead.bridgeDead BridgeDead.deathStep BridgeDead.intro BridgeDeadInitFirstUpdate.axioms(1) BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms notBridgeDead' reachableFrom_step.hyps(1) reachableFrom_step.prems(3) stateRootNonZero)
  interpret BDIFU: BridgeDeadInitFirstUpdate where contractsDead=contractsDead and contractsBD=contractsBD' and stepsBD=stepsBD
    by (metis (no_types, opaque_lifting) BD.BridgeDead_axioms BD.InitBD.reachableFromInitI BridgeDead.stepsAllBD_def BridgeDeadInitFirstUpdate_def HashProofVerifier.InitFirstUpdateAxiomsInduction HashProofVerifier_axioms append_Cons append_is_Nil_conv list.distinct(1) reachableFrom_step.hyps(2) reachableFrom_step.prems(3))
  interpret IFU: InitFirstUpdate where contractsI=contractsBD'' and stepsInit="step # BD.stepsAllBD"
    by (metis BD.stepsAllBD_def BridgeDead.stepsAllBD_def BridgeDeadInitFirstUpdate_def append_Cons reachableFrom_step.prems(3))
    
  have *: "?W (stepsBD @ [stepDeath]) + ?N (stepsBD @ [stepDeath]) + ?B = ?C (stepsBD @ [stepDeath])"
    using reachableFrom_step.IH
    using BDIFU.BridgeDeadInitFirstUpdate_axioms reachableFrom_step.prems by blast
  show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFU.claimedBeforeDeathTokenDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (CANCEL_WD address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFU.claimedBeforeDeathTokenDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using *
      using IFU.claimedBeforeDeathTokenDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress") auto
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using *
      using IFU.claimedBeforeDeathTokenDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using *
      using IFU.claimedBeforeDeathTokenDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case False
      then show ?thesis
        using * WITHDRAW_WD
        by auto
    next
      case True
      then have withdraw: "callWithdrawWhileDead contractsBD' tokenDepositAddress (message caller' 0) block token amount' proof' = (Success, contractsBD'')"
        using WITHDRAW_WD reachableFrom_step.hyps
        by auto
      let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
      have "verifyBalanceProof () ?mintedToken caller' amount' stateRoot proof'"
        using callWithdrawWhileDeadVerifyBalanceProof[OF withdraw]
        by (metis BD.LVSBD.InitLVS.mintedTokenTDI BD.LVSBD.getLastValidStateLVS mintedTokenITDB senderMessage snd_conv)
      then have "accountBalance contractsLastUpdate' ?mintedToken caller' = amount'"
        by (metis (no_types, opaque_lifting) ERC20StateMintedTokenINotNone generateStateRootUpdate' mintedTokenITDB option.collapse reachableFrom_step.prems(1) verifyBalanceProofE)
      then have "balanceOf (tokenClaimsTransfersBurnsBalances bridgeAddress token stepsInit) caller' = amount'" 
        using tokenClaimsTransfersBurnsBalanceAccountBalance
        using notBridgeDeadContractsLastUpdate' reachableFromInitI reachableFrom_step.prems(2) totalBalanceZero
        using properTokenFiniteBalancesMinted reachableFrom_step.prems
        unfolding finiteBalances_def
        by blast
      moreover

      have "getTokenWithdrawn (the (tokenDepositState contractsBD' tokenDepositAddress)) (hash2 caller' token) = False"
        using callWithdrawWhileDeadNotTokenWithdrawn[OF withdraw]
        by simp
      then have "\<nexists>amount proof. WITHDRAW_WD tokenDepositAddress caller' token amount proof \<in> set BD.stepsAllBD"
        using reachableFromGetTokenWithdrawnNoWithdraw
        using BD.InitBD.reachableFromInitI by blast
      then have "balanceOf (tokenClaimsTransfersBurnsBalances bridgeAddress token stepsInit) caller' = 
                 balanceOf (nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsInit BD.stepsAllBD) caller'"
        using nonWithdrawnTokenClaimsTransfersBurnsBalanceNoWithdraw
        by simp

      ultimately

      have **: "amount' \<le> balanceOf (nonWithdrawnTokenClaimsTransfersBurnsBalances tokenDepositAddress bridgeAddress token stepsInit BD.stepsAllBD) caller'"
        by simp

      then show ?thesis
        using True * WITHDRAW_WD
        using nonWithdrawnClaimedBeforeDeathAmountConsWithdraw[of amount' tokenDepositAddress bridgeAddress token stepsInit "stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step]"]
        using BDIFU.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
        unfolding BD.stepsAllBD_def
        by simp
    qed
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFU.claimedBeforeDeathTokenDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (RELEASE address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFU.claimedBeforeDeathTokenDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  qed
qed

lemma withdrawnAmountInvariant:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  shows "withdrawnTokenAmount tokenDepositAddress token stepsAllBD + 
         nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD +
         burnedTokenAmount bridgeAddress token stepsInit = 
         claimedBeforeDeathTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
  unfolding stepsAllBD_def
  using withdrawnAmountInvariant'[OF assms]
  by simp
  
end


(* ------------------------------------------------------------------------------------ *)
section \<open>Burned tokens that are not yet released\<close>

context HashProofVerifier
begin

definition isReleasedID where
  "isReleasedID tokenDepositAddress token ID steps \<longleftrightarrow>
    (\<exists>caller' amount' proof'. RELEASE tokenDepositAddress caller' ID token amount' proof' \<in> set steps)"

fun BURN_id where
  "BURN_id (BURN address caller ID token amount) = ID"

definition nonReleasedTokenBurns where
  "nonReleasedTokenBurns tokenDepositAddress bridgeAddress token stepsBefore steps = 
   filter (\<lambda> step. \<not> isReleasedID tokenDepositAddress token (BURN_id step) steps) (tokenBurns bridgeAddress token stepsBefore)"

lemma nonReleasedTokenBurnsDeposits_Nil [simp]: 
  "nonReleasedTokenBurns tokenDepositAddress bridgeAddress token [] steps = []" 
  unfolding nonReleasedTokenBurns_def
  by simp

definition nonReleasedTokenBurnsAmount where
  "nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsBefore steps = 
    sum_list (map BURN_amount (nonReleasedTokenBurns tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma nonReleasedTokenBurnsAmount_Nil [simp]: 
  "nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token [] steps = 0" 
  unfolding nonReleasedTokenBurnsAmount_def
  by simp

lemma  nonReleasedTokenBurnsConsNotBurn [simp]:
  assumes "\<nexists> caller ID amount. step = BURN bridgeAddress caller ID token amount"
  shows "nonReleasedTokenBurns tokenDepositAddress bridgeAddress token (step # stepsBefore) steps =  
         nonReleasedTokenBurns tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonReleasedTokenBurns_def
  by simp

lemma nonReleasedTokenBurnsConsNotRelease [simp]:
  assumes "\<nexists> caller ID amount proof. step = RELEASE tokenDepositAddress caller ID token amount proof"
  shows "nonReleasedTokenBurns tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =  
         nonReleasedTokenBurns tokenDepositAddress bridgeAddress token stepsBefore steps"
  unfolding nonReleasedTokenBurns_def
proof (rule filter_cong)
  fix step'
  assume "step' \<in> set (tokenBurns bridgeAddress token stepsBefore)"
  then show "(\<not> isReleasedID tokenDepositAddress token (BURN_id step') (step # steps)) =
             (\<not> isReleasedID tokenDepositAddress token (BURN_id step') steps)"
    using assms
    by (auto simp add: isReleasedID_def)
qed simp

lemma nonReleasedTokenBurnsAmountConsNotRelease [simp]:
  assumes "\<nexists> caller ID amount proof. step = RELEASE tokenDepositAddress caller ID token amount proof"
  shows "nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =  
        nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonReleasedTokenBurnsAmount_def
  by simp

lemma nonReleasedTokenBurnsAmountConsNotBurn [simp]:
  assumes "\<nexists> caller ID amount. step = BURN bridgeAddress caller ID token amount"
  shows "nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token (step # stepsBefore) steps =  
         nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonReleasedTokenBurnsAmount_def
  by simp

end

context InitFirstUpdate
begin

lemma nonReleasedTokenBurnsConsBurn [simp]:
  assumes "stepsInit = BURN bridgeAddress caller ID token amount # steps"
  shows "nonReleasedTokenBurns tokenDepositAddress bridgeAddress token
           (BURN bridgeAddress caller ID token amount # steps) steps =
         BURN bridgeAddress caller ID token amount # 
         nonReleasedTokenBurns tokenDepositAddress bridgeAddress token
            steps steps"
proof-
  have "\<not> isReleasedID tokenDepositAddress token ID steps"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain caller' amount' proof' where 
      "RELEASE tokenDepositAddress caller' ID token amount' proof' \<in> set steps"
      unfolding isReleasedID_def
      by auto
    then show False
      using  assms noReleaseBeforBurnSteps' 
      by force
  qed
  then show ?thesis
    unfolding nonReleasedTokenBurns_def
    by simp
qed

lemma nonReleasedTokenBurnsAmountConsBurn:
  assumes "stepsInit = BURN bridgeAddress caller ID token amount # steps"
  shows "nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token
          (BURN bridgeAddress caller ID token amount # steps) steps = 
        nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token
          steps steps + amount"
  using assms
  unfolding nonReleasedTokenBurnsAmount_def
  by simp
end

context InitUpdateBridgeNotDeadLastValidState
begin

lemma nonReleasedTokenBurnsAmountConsRelease:
  assumes "reachableFrom contractsLVS contractsRelease [RELEASE tokenDepositAddress caller ID token amount proof]"
  shows "nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit
           (RELEASE tokenDepositAddress caller ID token amount proof # stepsAllLVS) + amount =
         nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit
           stepsAllLVS"
proof-
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller ID token amount proof"

  define nonReleased where
  "nonReleased = nonReleasedTokenBurns tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS"

  have "?BURN_step \<in> set stepsInit"
    using burnBeforeRelease
    by (metis assms executeStep.simps(4) reachableFromSingleton senderMessage)
  then obtain steps1 steps2 where steps: "stepsInit = steps1 @ [?BURN_step] @ steps2"
    by (metis append_Cons append_Nil split_list_first)

  have *: "\<forall> step \<in> set (steps1 @ steps2). (\<forall> caller' amount' ID'. step = BURN bridgeAddress caller' ID' token amount' \<longrightarrow> ID' \<noteq> ID)"
    using BURNNoDouble' steps assms reachableFromInitI
    by metis
  then have "?BURN_step \<notin> set (steps1 @ steps2)"
    by auto

  define P where "P = (\<lambda> step. \<not> isReleasedID tokenDepositAddress token (BURN_id step) stepsAllLVS)"
  define P' where "P' = (\<lambda> step. \<not> isReleasedID tokenDepositAddress token (BURN_id step) (?RELEASE_step # stepsAllLVS))"
  define Q where "Q = (\<lambda> step. isTokenBurn bridgeAddress token step)"

  define burnsInit where "burnsInit = tokenBurns bridgeAddress token stepsInit"

  have "burnsInit = (filter Q steps1) @ [?BURN_step] @ (filter Q steps2)"
    using steps
    unfolding burnsInit_def tokenBurns_def Q_def
    by auto
  moreover
  have "nonReleased = filter P burnsInit"
    unfolding burnsInit_def nonReleased_def nonReleasedTokenBurns_def P_def
    by simp
  ultimately have nonReleased:
    "nonReleased = filter P (filter Q steps1) @ filter P [?BURN_step] @ filter P (filter Q steps2)"
    by simp

  have "filter P [?BURN_step] = [?BURN_step]"
  proof-
    have "\<not> isReleasedID tokenDepositAddress token ID stepsAllLVS"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain caller' amount' proof'  where "RELEASE tokenDepositAddress caller' ID token amount' proof' \<in> set stepsAllLVS"
        unfolding isReleasedID_def
        by auto
      then show False
        using RELEASENoDoubleCons assms reachableFromInitLVS reachableFromTrans
        by (metis (mono_tags, lifting) append_Cons append_Nil)
    qed
    then show ?thesis
      unfolding P_def
      by simp
  qed

  define c1 where "c1 = filter P (filter Q steps1)" 
  define c2 where "c2 = filter P (filter Q steps2)" 

  have "?BURN_step \<notin> set (c1 @ c2)"
    using \<open>?BURN_step \<notin> set (steps1 @ steps2)\<close>
    unfolding c1_def c2_def
    by auto
  then have nonReleased: "nonReleased = c1 @ [?BURN_step] @ c2"
    using nonReleased \<open>filter P [?BURN_step] = [?BURN_step]\<close>
    unfolding c1_def c2_def
    by metis
  
  moreover

  have "set (c1 @ c2) \<subseteq> set (steps1 @ steps2)"
    unfolding c1_def c2_def
    by auto

  have "filter P' burnsInit = c1 @ c2"
  proof (rule filter')
    show "?BURN_step \<notin> set (c1 @ c2)"
      by fact
  next
    show "filter P burnsInit = c1 @ [?BURN_step] @ c2"
      using \<open>nonReleased = c1 @ [?BURN_step] @ c2\<close> \<open>nonReleased = filter P burnsInit\<close>
      by simp
  next
    show "\<forall> step \<in> set burnsInit. (P step \<and> step \<noteq> ?BURN_step) \<longleftrightarrow> P' step"
    proof safe
      fix step
      assume "step \<in> set burnsInit" "P step" "step \<noteq> ?BURN_step"
      have "BURN_id step \<noteq> ID"
      proof-
        have "step \<in> set (filter Q steps1 @ filter Q steps2)"
          using \<open>step \<in> set burnsInit\<close> \<open>step \<noteq> ?BURN_step\<close>
          using \<open>burnsInit = (filter Q steps1) @ [?BURN_step] @ (filter Q steps2)\<close>
          by auto
        then have "step \<in> set (steps1 @ steps2)" "Q step"
          by auto
        then obtain ID' caller' amount' where "step = BURN bridgeAddress caller' ID' token amount'"
          unfolding Q_def
          by (metis isTokenBurn.elims(2))
        then show ?thesis
          using * \<open>step \<in> set (steps1 @ steps2)\<close>
          by simp
      qed
      then show "P' step"
        using \<open>P step\<close>
        unfolding P_def P'_def isReleasedID_def
        by auto
    next
      fix step
      assume "step \<in> set burnsInit" "P' step"
      then show "P step"
        unfolding P_def P'_def isReleasedID_def
        by auto
    next
      assume "P' ?BURN_step" "?BURN_step \<in> set burnsInit"
      then show False
        unfolding P'_def
        using isReleasedID_def by auto
    qed
  qed
  then have "nonReleasedTokenBurns tokenDepositAddress bridgeAddress token stepsInit
             (RELEASE tokenDepositAddress caller ID token amount proof # stepsAllLVS) = c1 @ c2"
    unfolding burnsInit_def P'_def nonReleasedTokenBurns_def
    by auto
  ultimately
  show ?thesis
    unfolding nonReleased_def nonReleasedTokenBurnsAmount_def
    by simp
qed

end

context InitFirstUpdate
begin

(* FIXME: try to derive this from the previous lemma (strong version proved in the LVS locale) *)
lemma nonReleasedTokenBurnsAmountConsReleaseWeak:
  assumes "stepsInit = RELEASE tokenDepositAddress caller ID token amount proof # steps"
  shows "nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token steps
             (RELEASE tokenDepositAddress caller ID token amount proof # steps) + amount = 
         nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token steps steps"
proof-
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller ID token amount proof"

  define nonReleased where
  "nonReleased = nonReleasedTokenBurns tokenDepositAddress bridgeAddress token steps steps"

  have "?BURN_step \<in> set steps"
    using burnBeforeReleaseSteps assms
    by simp
  then obtain steps1 steps2 where steps: "steps = steps1 @ [?BURN_step] @ steps2"
    by (metis append_Cons append_Nil split_list_first)

  have *: "\<forall> step \<in> set (steps1 @ steps2). (\<forall> caller' amount' ID'. step = BURN bridgeAddress caller' ID' token amount' \<longrightarrow> ID' \<noteq> ID)"
    using BURNNoDouble' steps assms reachableFromInitI
    by (metis reachableFromCons')
  then have "?BURN_step \<notin> set (steps1 @ steps2)"
    by auto

  define P where "P = (\<lambda> step. \<not> isReleasedID tokenDepositAddress token (BURN_id step) steps)"
  define P' where "P' = (\<lambda> step. \<not> isReleasedID tokenDepositAddress token (BURN_id step) (?RELEASE_step # steps))"
  define Q where "Q = (\<lambda> step. isTokenBurn bridgeAddress token step)"

  define burnsInit where "burnsInit = tokenBurns bridgeAddress token steps"

  have "burnsInit = (filter Q steps1) @ [?BURN_step] @ (filter Q steps2)"
    using steps
    unfolding burnsInit_def tokenBurns_def Q_def
    by auto
  moreover
  have "nonReleased = filter P burnsInit"
    unfolding burnsInit_def nonReleased_def nonReleasedTokenBurns_def P_def
    by simp
  ultimately have nonReleased:
    "nonReleased = filter P (filter Q steps1) @ filter P [?BURN_step] @ filter P (filter Q steps2)"
    by simp

  have "filter P [?BURN_step] = [?BURN_step]"
  proof-
    have "\<not> isReleasedID tokenDepositAddress token ID steps"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain caller' amount' proof'  where "RELEASE tokenDepositAddress caller' ID token amount' proof' \<in> set steps"
        unfolding isReleasedID_def
        by auto
      then show False
        using RELEASENoDoubleCons assms reachableFromInitI
        by force
    qed
    then show ?thesis
      unfolding P_def
      by simp
  qed

  define c1 where "c1 = filter P (filter Q steps1)" 
  define c2 where "c2 = filter P (filter Q steps2)" 

  have "?BURN_step \<notin> set (c1 @ c2)"
    using \<open>?BURN_step \<notin> set (steps1 @ steps2)\<close>
    unfolding c1_def c2_def
    by auto
  then have nonReleased: "nonReleased = c1 @ [?BURN_step] @ c2"
    using nonReleased \<open>filter P [?BURN_step] = [?BURN_step]\<close>
    unfolding c1_def c2_def
    by metis
  
  moreover

  have "set (c1 @ c2) \<subseteq> set (steps1 @ steps2)"
    unfolding c1_def c2_def
    by auto

  have "filter P' burnsInit = c1 @ c2"
  proof (rule filter')
    show "?BURN_step \<notin> set (c1 @ c2)"
      by fact
  next
    show "filter P burnsInit = c1 @ [?BURN_step] @ c2"
      using \<open>nonReleased = c1 @ [?BURN_step] @ c2\<close> \<open>nonReleased = filter P burnsInit\<close>
      by simp
  next
    show "\<forall> step \<in> set burnsInit. (P step \<and> step \<noteq> ?BURN_step) \<longleftrightarrow> P' step"
    proof safe
      fix step
      assume "step \<in> set burnsInit" "P step" "step \<noteq> ?BURN_step"
      have "BURN_id step \<noteq> ID"
      proof-
        have "step \<in> set (filter Q steps1 @ filter Q steps2)"
          using \<open>step \<in> set burnsInit\<close> \<open>step \<noteq> ?BURN_step\<close>
          using \<open>burnsInit = (filter Q steps1) @ [?BURN_step] @ (filter Q steps2)\<close>
          by auto
        then have "step \<in> set (steps1 @ steps2)" "Q step"
          by auto
        then obtain ID' caller' amount' where "step = BURN bridgeAddress caller' ID' token amount'"
          unfolding Q_def
          by (metis isTokenBurn.elims(2))
        then show ?thesis
          using * \<open>step \<in> set (steps1 @ steps2)\<close>
          by simp
      qed
      then show "P' step"
        using \<open>P step\<close>
        unfolding P_def P'_def isReleasedID_def
        by auto
    next
      fix step
      assume "step \<in> set burnsInit" "P' step"
      then show "P step"
        unfolding P_def P'_def isReleasedID_def
        by auto
    next
      assume "P' ?BURN_step" "?BURN_step \<in> set burnsInit"
      then show False
        unfolding P'_def
        using isReleasedID_def by auto
    qed
  qed
  then have "nonReleasedTokenBurns tokenDepositAddress bridgeAddress token steps
             (RELEASE tokenDepositAddress caller ID token amount proof # steps) = c1 @ c2"
    unfolding burnsInit_def P'_def nonReleasedTokenBurns_def
    by auto
  ultimately
  show ?thesis
    unfolding nonReleased_def nonReleasedTokenBurnsAmount_def
    by simp
qed

end


context InitFirstUpdate
begin

theorem releasedInvariantBase:
  shows "releasedTokenAmount tokenDepositAddress token stepsInit +
         nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsInit =
         burnedTokenAmount bridgeAddress token stepsInit"
  using reachableFromInitI InitFirstUpdate_axioms
proof (induction contractsInit contractsI stepsInit rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  interpret IFU: InitFirstUpdate where contractsInit=contracts and contractsI=contracts'' and stepsInit="step # steps"
    by (simp add: reachableFrom_step.prems)

  show ?case
  proof (cases "steps = []")
    case True
    then show ?thesis
      using IFU.firstUpdate
      by simp
  next
    case False
    then interpret IFU': InitFirstUpdate where contractsInit=contracts and contractsI=contracts' and stepsInit=steps
      using InitFirstUpdateAxiomsInduction reachableFrom_step.hyps reachableFrom_step.prems by blast

    have *: "releasedTokenAmount tokenDepositAddress token steps +
             nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token steps steps =
             burnedTokenAmount bridgeAddress token steps"
      using IFU'.InitFirstUpdate_axioms reachableFrom_step.IH by blast

    then show ?thesis
    proof (cases step)
      case (BURN address' caller' ID' token' amount')
      then show ?thesis
        using * IFU.nonReleasedTokenBurnsAmountConsBurn
        by (cases "address' = bridgeAddress \<and> token' = token") auto
    next
      case (RELEASE address' caller' ID' token' amount' proof')
      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token")
        case True

        show ?thesis
          using True * RELEASE
          using IFU.nonReleasedTokenBurnsAmountConsReleaseWeak
          by simp
      next
        case False
        then show ?thesis
          using * RELEASE
          by auto
      qed
    qed auto
  qed
qed

end


context InitUpdateBridgeNotDeadLastValidState
begin

lemma releasedTokenAmountInvariantStep:
  assumes "executeStep contractsLVS blockNum block step = (Success, contracts')" 
  assumes "releasedTokenAmount tokenDepositAddress token stepsAllLVS  + 
           nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS  = 
           burnedTokenAmount bridgeAddress token stepsInit"
  shows "releasedTokenAmount tokenDepositAddress token (step # stepsAllLVS)  + 
         nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit (step # stepsAllLVS)  = 
         burnedTokenAmount bridgeAddress token stepsInit"
  using assms
proof (cases step)
  case (RELEASE address' caller' ID' token' amount' proof')
  show ?thesis
  proof (cases "address' = tokenDepositAddress \<and> token' = token")
    case False
    then show ?thesis
      using assms RELEASE
      by auto
  next
    case True
    have *: "reachableFrom contractsLVS contracts' [RELEASE tokenDepositAddress caller' ID' token amount' proof']"
      using assms(1) RELEASE True
      using reachableFrom_base reachableFrom_step by blast
    show ?thesis
      using True assms RELEASE nonReleasedTokenBurnsAmountConsRelease[OF *]
      by simp
  qed
qed auto

end

context InitFirstUpdateLastUpdate
begin

lemma releasedTokenAmountInvariantBeforeDeath:
  assumes "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
  shows "releasedTokenAmount tokenDepositAddress token (stepsNoUpdate @ [UPDATE_step] @ stepsInit)  + 
         nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit (stepsNoUpdate @ [UPDATE_step] @ stepsInit)  = 
         burnedTokenAmount bridgeAddress token stepsInit"
  using reachableFromLastUpdateLU assms InitFirstUpdateLastUpdate_axioms 
proof (induction contractsLastUpdate contractsLU stepsNoUpdate rule: reachableFrom.induct)
  case (reachableFrom_base contractsLU)
  show ?case
    using releasedInvariantBase
    by (simp add: UPDATE_step_def)
next
  case (reachableFrom_step stepsNoUpdate contracts'' contracts contracts' blockNum block step)
  then interpret I: InitFirstUpdateLastUpdate where stepsNoUpdate="step # stepsNoUpdate" and contractsLU=contracts'' and contractsLastUpdate=contracts
    by simp

  have *: "releasedTokenAmount tokenDepositAddress token (I.UPDATE_step # stepsInit) +
           nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit (I.UPDATE_step # stepsInit) =
           burnedTokenAmount bridgeAddress token stepsInit"
    by (simp add: UPDATE_step_def releasedInvariantBase)

  show ?case
  proof (cases "stepsNoUpdate = []")
    case True
    interpret LVS: InitUpdateBridgeNotDeadLastValidState where contractsUpdate'=contractsLastUpdate' and contractsUpdate=contractsLastUpdate and blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and contractsLVS=contractsLastUpdate and stepsLVS="[]"
    proof
      show "lastValidStateTD contractsLastUpdate tokenDepositAddress = (Success, stateRoot)"
        by (smt (verit, best) HashProofVerifier.properSetup_stateOracleAddress HashProofVerifier_axioms assms callUpdateBridgeNotDeadLastValidState callUpdateIBridge callUpdateITokenDeposit callUpdateStateOracleState(2) lastValidStateI properSetupUpdate split_pairs update)
    next
      show "reachableFrom contractsLastUpdate contractsLastUpdate []"
        by (simp add: reachableFrom_base)
    next
      show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
        by fact
    qed

    show ?thesis
      using True LVS.releasedTokenAmountInvariantStep *
      unfolding LVS.stepsAllLVS_def
      by (metis I.reachableFromLastUpdateLU I.update append_Cons append_Nil prod.inject reachableFromSingleton update)
  next
    case False
    interpret I': InitFirstUpdateLastUpdate where stepsNoUpdate="stepsNoUpdate" and contractsLU=contracts' and contractsLastUpdate=contracts
    proof
      show "reachableFrom contracts contracts' stepsNoUpdate"
        by fact
    next
      show "let stateOracleAddress = stateOracleAddressB contracts bridgeAddress
            in \<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set stepsNoUpdate"
        using I.noUpdate
        unfolding Let_def
        by auto
    qed

    have *: "releasedTokenAmount tokenDepositAddress token (stepsNoUpdate @ [I.UPDATE_step] @ stepsInit) +
             nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit (stepsNoUpdate @ [I.UPDATE_step] @ stepsInit) =
             burnedTokenAmount bridgeAddress token stepsInit"
      using reachableFrom_step.IH I'.InitFirstUpdateLastUpdate_axioms reachableFrom_step.prems 
      by blast

    interpret LVS: InitUpdateBridgeNotDeadLastValidState where contractsUpdate'=contractsLastUpdate' and contractsUpdate=contractsLastUpdate and blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and contractsLVS=contracts' and stepsLVS=stepsNoUpdate
    proof
      show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
        by fact
    next
      show "reachableFrom contractsLastUpdate contracts' stepsNoUpdate"
        by (metis I'.reachableFromLastUpdateLU I.Update_axioms Update.update prod.inject update)
    next
      show "lastValidStateTD contracts' tokenDepositAddress = (Success, stateRoot)"
        by (smt (verit) I'.LastUpdate_axioms I'.properSetupLU LastUpdateBridgeNotDead.intro LastUpdateBridgeNotDead.lastValidStateLU LastUpdateBridgeNotDead_axioms.intro assms lastValidStateI properSetup_def split_pairs)
    qed
    show ?thesis
      using * LVS.releasedTokenAmountInvariantStep reachableFrom_step.hyps
      unfolding LVS.stepsAllLVS_def
      by simp
  qed
qed

end

context HashProofVerifier
begin

lemma reachableFromNoUpdateLastValidState:
  assumes "reachableFrom contracts contracts' steps"
  assumes "\<nexists> stateRoot. UPDATE (stateOracleAddressTD contracts tokenDepositAddress) stateRoot \<in> set steps"
  shows "lastValidStateTD contracts' tokenDepositAddress = lastValidStateTD contracts tokenDepositAddress"
  using assms
proof (induction contracts contracts' steps rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  show ?case
    using noUpdateGetLastValidStateTD reachableFrom_step reachableFromDepositStateOracle
    by (metis list.set_intros(1) list.set_intros(2))
qed

end

context InitUpdateBridgeNotDeadLastValidState
begin

lemma stepsInitEmptyNoReleases:
  assumes "stepsInit = []"
  assumes "\<nexists> stateRoot. UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) stateRoot \<in> set stepsLVS"
  shows "releasedTokenAmount tokenDepositAddress token (stepsLVS @ [UPDATE_step]) = 0"
    using reachableFromUpdate'LVS assms InitUpdateBridgeNotDeadLastValidState_axioms
proof (induction contractsUpdate contractsLVS stepsLVS)
  case (reachableFrom_base contracts)
  then show ?case
    by (simp add: UPDATE_step_def)
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then interpret I: InitUpdateBridgeNotDeadLastValidState where contractsLVS=contracts'' and contractsUpdate=contracts and stepsLVS="step # steps"
    by simp
  interpret I': InitUpdateBridgeNotDeadLastValidState where contractsLVS=contracts' and contractsUpdate=contracts and stepsLVS="steps"
  proof
    show "lastValidStateTD contracts' tokenDepositAddress = (Success, stateRoot)"
      using I.getLastValidStateLVS reachableFromNoUpdateLastValidState I.InitUpdate.stateOracleAddressTDI reachableFromDepositStateOracle  noUpdateGetLastValidStateTD reachableFrom_step.hyps reachableFrom_step.prems(2)
      by (metis (no_types, lifting) list.set_intros(1))
  next
    show "\<not> bridgeDead contractsUpdate' tokenDepositAddress"
      using bridgeNotDead by blast
  next
    show "reachableFrom contracts contracts' steps"
      by fact
  qed

  have *: "releasedTokenAmount tokenDepositAddress token (steps @ [I.UPDATE_step]) = 0"
    using reachableFrom_step.IH[OF reachableFrom_step.prems(1) _] reachableFrom_step.prems(2) I'.InitUpdateBridgeNotDeadLastValidState_axioms
    by (meson list.set_intros(2))

  then show ?case
  proof (cases step)
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using * I'.burnBeforeRelease reachableFrom_step.prems(1) reachableFrom_step.hyps
      by (cases "address' = tokenDepositAddress \<and> token' = token") force+
  qed auto
qed

end


context BridgeDeadInitFirstUpdate
begin

lemma releasedTokenAmountInvariant:
  shows "releasedTokenAmount tokenDepositAddress token stepsAllBD  + 
         nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD  = 
         burnedTokenAmount bridgeAddress token stepsInit"
  using reachableFromContractsBD BridgeDeadInitFirstUpdate_axioms
  unfolding stepsAllBD_def
proof (induction contractsDead contractsBD stepsBD rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  show ?case
  proof (cases "stepsInit=[]")
    case True
    then show ?thesis
      using LVSDead.stepsInitEmptyNoReleases
      by (smt (verit, ccfv_threshold) properSetup_stateOracleAddress InitUpdate.stateOracleAddressTDI LVSDead.stepsAllLVS_def Nat.add_0_right append.assoc append_Cons append_Nil burnedTokenAmountNil noUpdate nonReleasedTokenBurnsAmount_Nil properSetupUpdate set_ConsD stepDeathNoUpdate)
  next
    case False
    interpret I: InitFirstUpdateLastUpdate where contractsLU=contractsDead and stepsNoUpdate="stepDeath # stepsNoUpdate"
    proof
      show "stepsInit \<noteq> [] \<and> last stepsInit = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit"
        using False firstUpdate stepsAllBD_def by fastforce
    next
      show "updatesNonZero stepsInit"
        by (metis updatesNonZeroAppend(2) stepsAllBD_def updatesNonZeroInit)
    next
      show "reachableFrom contractsLastUpdate contractsDead (stepDeath # stepsNoUpdate)"
        by (metis Cons_eq_appendI deathStep eq_Nil_appendI reachableFromLastUpdateLU reachableFromTrans)
    next
      show "let stateOracleAddress = stateOracleAddressB contractsLastUpdate bridgeAddress
             in \<nexists>stateRoot'. UPDATE stateOracleAddress stateRoot' \<in> set (stepDeath # stepsNoUpdate)"
        by (metis noUpdate set_ConsD stepDeathNoUpdate)
    qed

    show ?thesis
      using I.releasedTokenAmountInvariantBeforeDeath notBridgeDeadContractsLastUpdate' 
      by auto
  qed
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then interpret BD: BridgeDeadInitFirstUpdate where contractsBD=contracts'' and contractsDead=contracts and stepsBD="step # steps"
    by simp
  interpret BD': BridgeDead where contractsBD=contracts' and contractsDead=contracts and stepsBD=steps
    by (metis BD.BridgeDead_axioms BridgeDead_axioms_def BridgeDead_def reachableFrom_step.hyps(1))

  interpret BD'': BridgeDeadInitFirstUpdate where contractsBD=contracts' and contractsDead=contracts and stepsBD=steps
    by (metis (no_types, lifting) BD'.BridgeDead_axioms BD'.InitBD.reachableFromInitI BD'.stepsAllBD_def BD.InitFirstUpdate_axioms BD.stepsAllBD_def BridgeDeadInitFirstUpdate.intro HashProofVerifier.InitFirstUpdateAxiomsInduction HashProofVerifier_axioms Nil_is_append_conv append_Cons list.distinct(1) reachableFrom_step.hyps(2))

  note * = reachableFrom_step.IH[OF BD''.BridgeDeadInitFirstUpdate_axioms]

  show ?case
    using * BD'.LVSBD.releasedTokenAmountInvariantStep reachableFrom_step.hyps
    unfolding BD'.LVSBD.stepsAllLVS_def
    by simp
qed

end

context BridgeDeadInitFirstUpdate
begin

theorem tokenDepositBalance:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  shows "tokenDepositBalance contractsBD token tokenDepositAddress = 
         nonClaimedBeforeDeathNonCanceledTokenDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD + 
         nonWithdrawnNonBurnedClaimedBeforeDeathAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD +
         nonReleasedTokenBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
  using InitBD.tokenDepositBalanceInvariant[of token]
  using withdrawnAmountInvariant[of token]
  using canceledAmountInvariant[of token]
  using depositTokenAmountEqualsClaimedPlusNonClaimed[of tokenDepositAddress token stepsAllBD bridgeAddress stepsInit]
  using releasedTokenAmountInvariant[of token]
  using assms
  by simp

end

end