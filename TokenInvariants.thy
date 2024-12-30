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

fun TRANSFER_amount where
  "TRANSFER_amount (TRANSFER address caller receiver token amount) = amount" 

end


(* ------------------------------------------------------------------------------------ *)
section \<open>Deposited token amount\<close>

context HashProofVerifier
begin

primrec DEPOSIT_id where
  "DEPOSIT_id (DEPOSIT address caller ID token amount) = ID"

fun isDeposit :: "address \<Rightarrow> address \<Rightarrow> Step \<Rightarrow> bool" where
  "isDeposit address token (DEPOSIT address' caller ID token' amount) \<longleftrightarrow> address' = address \<and> token' = token"
| "isDeposit address token _ = False"

\<comment> \<open>All deposits of the given token on the given address\<close>
definition deposits where
  "deposits address token steps = filter (isDeposit address token) steps"

\<comment> \<open>Total amount of the given token deposited on the given address\<close>
definition depositedAmount where
  "depositedAmount tokenDepositAddress token steps = 
        sum_list (map DEPOSIT_amount (deposits tokenDepositAddress token steps))"

lemma depositsNil [simp]:
  shows "deposits tokenDepositAddress token [] = []"
  by (simp add: deposits_def)

lemma depositsAppend[simp]:
  shows "deposits tokenDepositAddress token (steps1 @ steps2) = 
         deposits tokenDepositAddress token steps1 @ deposits tokenDepositAddress token steps2"
  by (simp add: deposits_def)

lemma depositsSubsetSteps:
  shows "set (deposits tokenDepositAddress token steps) \<subseteq> set steps"
  by (simp add: deposits_def)

lemma depositsConsDeposit [simp]:
  shows "deposits tokenDepositAddress token (DEPOSIT tokenDepositAddress caller ID token amount # steps) =
         DEPOSIT tokenDepositAddress caller ID token amount # deposits tokenDepositAddress token steps"
  unfolding deposits_def
  by simp

lemma depositsConsDepositOther [simp]:
  assumes "tokenDepositAddress \<noteq> tokenDepositAddress' \<or> token \<noteq> token'"
  shows "deposits tokenDepositAddress token (DEPOSIT tokenDepositAddress' caller ID token' amount # steps) =
         deposits tokenDepositAddress token steps"
  using assms
  unfolding deposits_def
  by auto

lemma depositsConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "deposits tokenDepositAddress token (step # steps) = deposits tokenDepositAddress token steps"
  using assms
  by (cases step, auto simp add: deposits_def)

lemma depositedAmountNil [simp]:
  shows "depositedAmount address token [] = 0"
  by (simp add: depositedAmount_def)

lemma depositedAmountConsDeposit [simp]:
  shows "depositedAmount address token (DEPOSIT address caller ID token amount # steps) = 
         amount + depositedAmount address token steps"
  by (simp add: depositedAmount_def)

lemma depositedAmountConsDepositOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "depositedAmount address token (DEPOSIT address' caller ID token' amount # steps) = 
         depositedAmount address token steps"
  using assms
  by (auto simp add: depositedAmount_def)

lemma depositedAmountConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount'. step = DEPOSIT address' caller' ID' token' amount'"
  shows "depositedAmount address token (step # steps) = depositedAmount address token steps"
  using assms 
  unfolding depositedAmount_def
  by (cases step, auto)

lemma depositsDEPOSIT: 
  assumes "step \<in> set (deposits tokenDepositAddress token stepsInit)"
  obtains caller ID amount where "step = DEPOSIT tokenDepositAddress caller ID token amount"
  using assms
  unfolding deposits_def
  by (metis filter_set isDeposit.elims(2) member_filter)

end

context StrongHashProofVerifier
begin

lemma distinctDeposits:
  assumes "reachableFrom contracts contracts' steps"
  shows "distinct (deposits tokenDepositAddress token steps)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain ID caller amount steps1 steps2 steps3 where 
    "deposits tokenDepositAddress token steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps3"
    by (metis append_Cons depositsDEPOSIT not_distinct_decomp in_set_conv_decomp)
  then obtain steps1' steps2' steps3' where "steps = steps1' @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2' @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps3'"
    unfolding deposits_def
    by (meson twiceInFilter)
  then show False
    using DEPOSITNoDouble[OF assms]
    by blast
qed

lemma distinctDepositIDs:
  assumes "reachableFrom contracts contracts' steps"
  shows "distinct (map DEPOSIT_id (deposits tokenDepositAddress token steps))"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  then obtain ID caller amount caller' amount' where
    "DEPOSIT tokenDepositAddress caller ID token amount \<in> set (deposits tokenDepositAddress token steps)"
    "DEPOSIT tokenDepositAddress caller' ID token amount' \<in> set (deposits tokenDepositAddress token steps)"
    "DEPOSIT tokenDepositAddress caller ID token amount \<noteq> DEPOSIT tokenDepositAddress caller' ID token amount'"
    using distinctDeposits[OF assms]
    by (subst (asm) distinct_map, smt (verit) DEPOSIT_id.simps depositsDEPOSIT inj_on_def)
  then show False
    by (metis DEPOSITNoDoubleCTA depositsSubsetSteps in_mono assms)
qed

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Claimed token amount\<close>

context HashProofVerifier
begin

fun isClaim where
  "isClaim address token (CLAIM address' caller ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isClaim address token _ = False"

\<comment> \<open>All claims of a given token on the given bridge\<close>
definition claims where 
  "claims address token steps = 
   filter (isClaim address token) steps"

lemma claimsNil [simp]:
  shows "claims bridgeAddress token [] = []"
  by (simp add: claims_def)

lemma claimsConsClaim [simp]:
  shows "claims bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof # steps) = 
         CLAIM bridgeAddress caller ID token amount proof # claims bridgeAddress token steps"
  unfolding claims_def
  by simp

lemma claimsConsClaimOther [simp]:
  assumes "address' \<noteq> bridgeAddress \<or> token' \<noteq> token"
  shows "claims bridgeAddress token (CLAIM address' caller ID token' amount proof # steps) = 
         claims bridgeAddress token steps"
  using assms
  unfolding claims_def
  by auto

lemma claimsConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CLAIM address' caller' ID' token' amount' proof'"
  shows "claims bridgeAddress token (step # steps) = 
         claims bridgeAddress token steps"
  using assms
  unfolding claims_def
  by (cases step, auto)

\<comment> \<open>Total amount of a given token claimed on the given bridge\<close>
definition claimedAmount where
  "claimedAmount bridgeAddress token steps = 
   sum_list (map CLAIM_amount (claims bridgeAddress token steps))"

lemma claimedAmountNil [simp]:
  shows "claimedAmount bridgeAddress token [] = 0"
  by (simp add: claimedAmount_def)

lemma claimedAmountConsClaim [simp]:
  shows "claimedAmount address token (CLAIM address caller ID token amount proof # steps) =
         claimedAmount address token steps + amount"
  unfolding claimedAmount_def
  by auto

lemma claimedAmountConsClaimOther [simp]:
  assumes "address' \<noteq> address \<or> token' \<noteq> token"
  shows "claimedAmount address token (CLAIM address' caller ID token' amount proof # steps) =
         claimedAmount address token steps"
  using assms
  unfolding claimedAmount_def
  by auto

lemma claimedAmountConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CLAIM address' caller' ID' token' amount' proof'"
  shows "claimedAmount address token (step # steps) = claimedAmount address token steps"
  using assms 
  unfolding claimedAmount_def
  by simp

end


(* ------------------------------------------------------------------------------------ *)
section \<open>Burned token amount\<close>

context HashProofVerifier
begin

fun isBurn where
  "isBurn address token (BURN address' caller ID token' amount) \<longleftrightarrow> address' = address \<and> token' = token"
| "isBurn address token _ = False"

\<comment> \<open>All burns of a given token on the given bridge\<close>
definition burns where 
  "burns address token steps = 
   filter (isBurn address token) steps"

lemma burnsNil [simp]:
  shows "burns bridgeAddress token [] = []"
  by (simp add: burns_def)

lemma burnsConsOther [simp]:
  assumes "\<nexists> caller ID amount. step = BURN bridgeAddress caller ID token amount"
  shows "burns bridgeAddress token (step # steps) = burns bridgeAddress token steps"
  using assms
  unfolding burns_def
  by (cases step, auto)

lemma burnsConsBurn [simp]:
  shows "burns bridgeAddress token (BURN bridgeAddress caller ID token amount # steps) = 
         BURN bridgeAddress caller ID token amount # burns bridgeAddress token steps"
  by (simp add: burns_def)

lemma burnsConsBurnOther [simp]:
  assumes "address' \<noteq> address \<or> token' \<noteq> token"
  shows "burns address token (BURN address' caller ID token' amount # steps) = 
         burns address token steps"
  using assms
  by (auto simp add: burns_def)

\<comment> \<open>Total amount of a given token claimed on the given bridge\<close>
definition burnedAmount where
  "burnedAmount bridgeAddress token steps = 
   sum_list (map BURN_amount (burns bridgeAddress token steps))"

lemma burnedAmountNil [simp]:
  shows "burnedAmount bridgeAddress token [] = 0"
  by (simp add: burnedAmount_def)

lemma burnedAmountConsBurn [simp]:
  shows "burnedAmount address token (BURN address caller ID token amount # steps) = 
         burnedAmount address token steps + amount"
  unfolding burnedAmount_def
  by auto

lemma burnedAmountConsBurnOther [simp]:
  assumes "address' \<noteq> address \<or> token' \<noteq> token"
  shows "burnedAmount address token (BURN address' caller ID token' amount # steps) = 
         burnedAmount address token steps"
  using assms
  unfolding burnedAmount_def
  by auto

lemma burnedAmountConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = BURN address' caller' ID' token' amount'"
  shows "burnedAmount address token (step # steps) = burnedAmount address token steps"
  using assms 
  unfolding burnedAmount_def
  by simp

lemma burnsBURN:
  assumes "step \<in> set (burns bridgeAddress token steps)"
  obtains ID caller amount where "step = BURN bridgeAddress caller ID token amount"
  using assms
  unfolding burns_def
  using assms
  unfolding deposits_def
  by (metis filter_set isBurn.elims(2) member_filter)

fun BURN_id where
  "BURN_id (BURN address caller ID token amount) = ID"

end

context StrongHashProofVerifier
begin

lemma distinctBurns:
  assumes "reachableFrom contracts contracts' steps"
  shows "distinct (burns bridgeAddress token steps)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain ID caller amount steps1 steps2 steps3 where 
    "burns bridgeAddress token steps = steps1 @ [BURN bridgeAddress caller ID token amount] @ steps2 @ [BURN bridgeAddress caller ID token amount] @ steps3"
    by (metis append_Cons burnsBURN not_distinct_decomp in_set_conv_decomp)
  then obtain steps1' steps2' steps3' where "steps = steps1' @ [BURN bridgeAddress caller ID token amount] @ steps2' @ [BURN bridgeAddress caller ID token amount] @ steps3'"
    unfolding burns_def
    by (meson twiceInFilter)
  then show False
    using BURNNoDouble[OF assms]
    by blast
qed

lemma distinctBurnIDs:
  assumes "reachableFrom contracts contracts' steps"
  shows "distinct (map BURN_id (burns bridgeAddress token steps))"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  then obtain ID caller amount caller' amount' where
    "BURN bridgeAddress caller ID token amount \<in> set (burns bridgeAddress token steps)"
    "BURN bridgeAddress caller' ID token amount' \<in> set (burns bridgeAddress token steps)"
    "BURN bridgeAddress caller ID token amount \<noteq> BURN bridgeAddress caller' ID token amount'"
    using distinctBurns[OF assms]
    by (subst (asm) distinct_map, smt (verit, best) BURN_id.simps burnsBURN inj_onI)
  then show False
    using BURNNoDoubleCTA[OF assms]
    by (simp add: burns_def)
qed

end


(* ------------------------------------------------------------------------------------ *)

section \<open>Canceled token amount\<close>
context HashProofVerifier
begin

fun isCancel where
  "isCancel address token (CANCEL_WD address' caller ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isCancel address token _ = False"

definition cancels where
  "cancels tokenDepositAddress token steps = 
   filter (isCancel tokenDepositAddress token) steps"

lemma cancelsNil [simp]:
  shows "cancels tokenDepositAddress token [] = []"
  by (simp add: cancels_def)

lemma cancelsConsCancel [simp]:
  shows "cancels address token (CANCEL_WD address caller ID token amount proof # steps) = 
         CANCEL_WD address caller ID token amount proof # cancels address token steps"
  unfolding cancels_def
  by simp

lemma cancelsConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CANCEL_WD address' caller' ID' token' amount' proof'"
  shows "cancels address token (step # steps) = cancels address token steps"
  using assms
  unfolding cancels_def
  by (cases step, auto)

lemma cancelsConsCancelOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "cancels address token (CANCEL_WD address' caller' ID' token' amount' proof' # steps) = 
         cancels address token steps"
  using assms
  unfolding cancels_def
  by auto

lemma cancelsBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
    shows "cancels tokenDepositAddress token steps = []"
  using noCancelBeforeBridgeDead[OF assms]
  unfolding cancels_def
  by (smt (verit, best) filter_empty_conv isCancel.elims(2))

definition canceledAmount where
  "canceledAmount tokenDepositAddress token steps = 
   sum_list (map CANCEL_amount (cancels tokenDepositAddress token steps))"

lemma canceledAmountNil [simp]:
  shows "canceledAmount tokenDepositAddress token [] = 0"
  by (simp add: canceledAmount_def)

lemma canceledAmountConsCancel [simp]:
  shows "canceledAmount address token (CANCEL_WD address caller ID token amount proof # steps) = 
         amount + canceledAmount address token steps"
  unfolding canceledAmount_def
  by auto

lemma canceledAmountConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = CANCEL_WD address' caller' ID' token' amount' proof'"
  shows "canceledAmount address token (step # steps) = canceledAmount address token steps"
  using assms 
  unfolding canceledAmount_def
  by simp

lemma canceledAmountConsCancelOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "canceledAmount address token (CANCEL_WD address' caller' ID' token' amount' proof' # steps) = 
         canceledAmount address token steps"
  using assms
  unfolding canceledAmount_def
  by simp

lemma canceledAmountBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
    shows "canceledAmount tokenDepositAddress token steps = 0"
  using cancelsBridgeNotDead[OF assms]
  by (simp add: canceledAmount_def)

end

(* ------------------------------------------------------------------------------------ *)
text \<open>Withdrawn while dead token amount\<close>
context HashProofVerifier
begin

fun isWithdraw where
  "isWithdraw address token (WITHDRAW_WD address' caller token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isWithdraw address token _ = False"

definition withdraws where
  "withdraws tokenDepositAddress token steps = filter (isWithdraw tokenDepositAddress token) steps"

lemma withdrawsNil [simp]:
  shows "withdraws tokenDepositAddress token [] = []"
  unfolding withdraws_def
  by simp

lemma withdrawsConsOther [simp]:
  assumes "\<nexists> caller' amount' proof'. step = WITHDRAW_WD address caller' token amount' proof'"
  shows "withdraws address token (step # steps) = withdraws address token steps"
  using assms 
  unfolding withdraws_def
  by (cases step, auto)

lemma withdrawsConsWithdraw [simp]:
  shows "withdraws address token (WITHDRAW_WD address caller token amount proof # steps) = 
         WITHDRAW_WD address caller token amount proof # withdraws address token steps"
  unfolding withdraws_def
  by auto

lemma withdrawsBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
    shows "withdraws tokenDepositAddress token steps = []"
  using assms noWithdrawBeforeBridgeDead[OF assms]
  by (metis filter_False isWithdraw.elims(2) withdraws_def)

definition withdrawnAmount where
  "withdrawnAmount tokenDepositAddress token steps = 
   sum_list (map WITHDRAW_WD_amount (withdraws tokenDepositAddress token steps))"


lemma withdrawnAmountNil [simp]:
  shows "withdrawnAmount tokenDepositAddress token [] = 0"
  by (simp add: withdrawnAmount_def)

lemma withdrawnAmountConsOther [simp]:
  assumes "\<nexists> caller' amount' proof'. step = WITHDRAW_WD address caller' token amount' proof'"
  shows "withdrawnAmount address token (step # steps) = withdrawnAmount address token steps"
  using assms 
  unfolding withdrawnAmount_def
  by simp

lemma withdrawnAmountConsWithdraw [simp]:
  shows "withdrawnAmount address token (WITHDRAW_WD address caller token amount proof # steps) = 
         withdrawnAmount address token steps + amount"
  unfolding withdrawnAmount_def 
  by simp

lemma withdrawnAmountBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
        shows "withdrawnAmount tokenDepositAddress token steps = 0"
  using withdrawsBridgeNotDead[OF assms]
  unfolding withdrawnAmount_def
  by simp

end


(* ------------------------------------------------------------------------------------ *)
section \<open>Released deposits amount\<close>

context HashProofVerifier
begin

fun isRelease where
  "isRelease address token (RELEASE address' caller ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token"
| "isRelease address token _ = False"

definition releases where
  "releases tokenDepositAddress token steps = 
   filter (isRelease tokenDepositAddress token) steps"

lemma releasesNil [simp]:
  shows "releases tokenDepositAddress token [] = []"
  by (simp add: releases_def)

lemma releasesConsRelease [simp]:
  shows "releases address token (RELEASE address caller ID token amount proof # steps) = 
         RELEASE address caller ID token amount proof # releases address token steps"
  unfolding releases_def
  by auto

lemma releasesConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = RELEASE address' caller' ID' token' amount' proof'"
  shows "releases address token (step # steps) = releases address token steps"
  using assms 
  unfolding releases_def
  by (cases step, auto)

lemma realesesConsReleaseOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "releases address token (RELEASE address' caller' ID' token' amount' proof' # steps) = 
         releases address token steps"
  using assms
  unfolding releases_def
  by auto

definition releasedAmount where
  "releasedAmount tokenDepositAddress token steps = 
   sum_list (map RELEASE_amount (releases tokenDepositAddress token steps))"

lemma releasedAmountNil [simp]:
  shows "releasedAmount tokenDepositAddress token [] = 0"
  by (simp add: releasedAmount_def)

lemma releasedAmountRelease [simp]:
  shows "releasedAmount address token (RELEASE address caller ID token amount proof # steps) = 
         amount + releasedAmount address token steps"
  unfolding releasedAmount_def
  by simp

lemma releasedAmountConsOther [simp]:
  assumes "\<nexists> address' caller' ID' token' amount' proof'. step = RELEASE address' caller' ID' token' amount' proof'"
  shows "releasedAmount address token (step # steps) = releasedAmount address token steps"
  using assms 
  unfolding releasedAmount_def
  by simp

lemma realesedAmountConsReleaseOther [simp]:
  assumes "address \<noteq> address' \<or> token \<noteq> token'"
  shows "releasedAmount address token (RELEASE address' caller' ID' token' amount' proof' # steps) = 
         releasedAmount address token steps"
  using assms
  unfolding releasedAmount_def
  by simp

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Claimed deposits amount\<close>

context HashProofVerifier
begin

(* NOTE: only for the given token *)
definition isClaimedID where
 "isClaimedID bridgeAddress token ID steps \<longleftrightarrow> 
  (\<exists> caller' amount' proof'. CLAIM bridgeAddress caller' ID token amount' proof' \<in> set steps)"

text \<open>All deposits of the given token on the given address that have been claimed\<close>
definition claimedDeposits where
  "claimedDeposits tokenDepositAddress bridgeAddress token steps = 
     filter 
      (\<lambda> step. isClaimedID bridgeAddress token (DEPOSIT_id step) steps) 
      (deposits tokenDepositAddress token steps)"

lemma claimedDepositsNil [simp]: 
  shows "claimedDeposits tokenDepositAddress bridgeAddress token [] = []"
  unfolding claimedDeposits_def
  by simp

lemma claimedDepositsConsOther [simp]:
  assumes "\<nexists> caller ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"
  shows "claimedDeposits tokenDepositAddress bridgeAddress token (step # steps) = 
         claimedDeposits tokenDepositAddress bridgeAddress token steps"
    using assms
    unfolding claimedDeposits_def isClaimedID_def
    by (smt (verit, del_insts) filter_cong list.set_intros(2) set_ConsD depositsConsOther)

text \<open>Total amount of tokens that have been deposited on the given address and then claimed\<close>
definition claimedDepositsAmount where
  "claimedDepositsAmount tokenDepositAddress bridgeAddress token steps = 
   sum_list (map DEPOSIT_amount (claimedDeposits tokenDepositAddress bridgeAddress token steps))"

lemma claimedDepositsAmountNil [simp]: 
  shows "claimedDepositsAmount tokenDepositAddress bridgeAddress token [] = 0"
  unfolding claimedDepositsAmount_def
  by simp

lemma claimedDepositsAmountConsOther [simp]: 
  assumes "\<nexists> caller ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"
  shows "claimedDepositsAmount tokenDepositAddress bridgeAddress token (step # steps) =
         claimedDepositsAmount tokenDepositAddress bridgeAddress token steps"
  using assms
  unfolding claimedDepositsAmount_def
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
lemma claimedDepositsAmountConsClaim [simp]:
  assumes "reachableFrom contractsI contractsClaim [CLAIM bridgeAddress caller ID token amount proof]"
  shows   "claimedDepositsAmount tokenDepositAddress bridgeAddress token
             (CLAIM bridgeAddress caller ID token amount proof # stepsInit) = 
           claimedDepositsAmount tokenDepositAddress bridgeAddress token stepsInit + amount"
proof-
  let ?CLAIM_step = "CLAIM bridgeAddress caller ID token amount proof"
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"

  have *: "deposits tokenDepositAddress token (?CLAIM_step # stepsInit) =
           deposits tokenDepositAddress token stepsInit"
    by simp

  have "reachableFrom contractsInit contractsClaim (?CLAIM_step # stepsInit)"
    using reachableFromTrans[OF assms(1) reachableFromInitI]
    by simp
 
  have "callClaim contractsI bridgeAddress (message caller amount) ID token amount proof = (Success, contractsClaim)"
    using assms
    by (metis executeStep.simps(2) reachableFromSingleton)
  then have "?DEPOSIT_step \<in> set (deposits tokenDepositAddress token stepsInit)"
    using depositBeforeClaim[where msg="message caller amount"]
    by (simp add: deposits_def)

  have "\<exists> steps1 steps2. 
          claimedDeposits tokenDepositAddress bridgeAddress token stepsInit = steps1 @ steps2 \<and> 
          claimedDeposits tokenDepositAddress bridgeAddress token (?CLAIM_step # stepsInit) = steps1 @ [?DEPOSIT_step] @ steps2"
    unfolding claimedDeposits_def
  proof (subst *, rule filter'')
    let ?P = "\<lambda> step steps. isClaimedID bridgeAddress token (DEPOSIT_id step) steps" 
    show "\<forall>step\<in>set (deposits tokenDepositAddress token stepsInit).
             (?P step (?CLAIM_step # stepsInit) \<and> step \<noteq> ?DEPOSIT_step) =
              ?P step stepsInit"
    proof safe
      fix step
      assume "step \<in> set (deposits tokenDepositAddress token stepsInit)"
      assume "step \<noteq> ?DEPOSIT_step"
      then have "DEPOSIT_id step \<noteq> ID"
        using distinctDepositIDs[OF reachableFromInitI]
        using \<open>step \<in> set (deposits tokenDepositAddress token stepsInit)\<close> \<open>?DEPOSIT_step \<in> set (deposits tokenDepositAddress token stepsInit)\<close>
        by (metis DEPOSIT_id.simps distinct_map inj_on_def)
      assume "isClaimedID bridgeAddress token (DEPOSIT_id step) (?CLAIM_step # stepsInit)"
      then show "isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit"
        using \<open>DEPOSIT_id step \<noteq> ID\<close>
        unfolding isClaimedID_def
        by auto
    next
      assume "?DEPOSIT_step \<in> set (deposits tokenDepositAddress token stepsInit)"
             "isClaimedID bridgeAddress token (DEPOSIT_id ?DEPOSIT_step) stepsInit"
      then show False
        using CLAIMNoDoubleCons \<open>reachableFrom contractsInit contractsClaim (?CLAIM_step # stepsInit)\<close>
        unfolding isClaimedID_def
        by auto
    qed (auto simp add: isClaimedID_def)
  next
    show "?DEPOSIT_step \<in> set (deposits tokenDepositAddress token stepsInit)"
      by fact
  next
    show "isClaimedID bridgeAddress token (DEPOSIT_id ?DEPOSIT_step) (?CLAIM_step # stepsInit)"
      by (auto simp add: isClaimedID_def)
  next
    show "distinct (deposits tokenDepositAddress token stepsInit)"
      using distinctDeposits[OF reachableFromInitI]
      by auto
  qed
  then show ?thesis
    unfolding claimedDepositsAmount_def 
    by auto
qed


(*
                steps               DEPOSIT
contractsInit    \<rightarrow>*     contractsI    \<rightarrow>   contractsDeposit
properSetup
getDeposit=0
lastState=0
*)
lemma claimedDepositsAmountConsDeposit [simp]:
  assumes "reachableFrom contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
  shows "claimedDepositsAmount tokenDepositAddress bridgeAddress token
            (DEPOSIT tokenDepositAddress caller ID token amount # stepsInit) =
         claimedDepositsAmount tokenDepositAddress bridgeAddress token stepsInit"
proof-
  define DEPOSIT_step where "DEPOSIT_step = DEPOSIT tokenDepositAddress caller ID token amount"
  have "claimedDeposits tokenDepositAddress bridgeAddress token (DEPOSIT_step # stepsInit) = 
        claimedDeposits tokenDepositAddress bridgeAddress token stepsInit"
  proof-
    have "\<nexists> caller' token' amount' proof'. CLAIM bridgeAddress caller' ID token' amount' proof' \<in> set stepsInit"
      using assms noClaimBeforeDeposit
      unfolding DEPOSIT_step_def
      by blast
    then show ?thesis
      unfolding claimedDeposits_def
      using DEPOSIT_step_def isClaimedID_def
      by auto
  qed
  then show ?thesis
    unfolding claimedDepositsAmount_def DEPOSIT_step_def
    by simp
qed

text \<open>Total claimed amount equals total amount of deposits that have been claimed\<close>
lemma claimedEqualsClaimedDeposits:
  shows "claimedAmount bridgeAddress token stepsInit = 
         claimedDepositsAmount tokenDepositAddress bridgeAddress token stepsInit"
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
      using True claimedDepositsAmountConsOther
      by (simp add: claimedAmount_def claims_def claimedDepositsAmount_def claimedDeposits_def deposits_def)
  next
    case False
    interpret I: Init where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
      by (meson InitFirstUpdate_def Init_axioms.intro Init_def reachableFrom_step.hyps(1) reachableFrom_step.prems)
    interpret IFU: InitFirstUpdate where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
      using False
      by (metis I.Init_axioms InitFirstUpdate.axioms(2) InitFirstUpdate.intro InitFirstUpdate_axioms_def last_ConsR reachableFrom_step.prems updatesNonZeroCons(1))

    have *: "claimedAmount bridgeAddress token steps =
             claimedDepositsAmount tokenDepositAddress bridgeAddress token steps"
      using IFU.InitFirstUpdate_axioms reachableFrom_step.IH by blast

    show ?thesis
      using * claimedDepositsAmountConsOther
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token")
        case True
        show ?thesis
          using DEPOSIT True IFU.claimedDepositsAmountConsDeposit claimedAmountConsOther
          by (metis IFU.InitFirstUpdate_axioms Step.simps(9) reachableFrom.reachableFrom_step reachableFrom_base reachableFrom_step.IH reachableFrom_step.hyps(2))
      next
        case False
        then show ?thesis
          using DEPOSIT *
          using claimedDepositsAmountConsOther
          by auto
      qed
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token' = token")
        case False
        then show ?thesis
          using * CLAIM
          using claimedDepositsAmountConsOther
          by auto
      next
        case True
        then show ?thesis
          using * CLAIM True claimedAmountConsClaim  IFU.claimedDepositsAmountConsClaim
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
theorem totalMintedBridgeNotDead':
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  shows "totalMinted contractsI bridgeAddress token + 
         burnedAmount bridgeAddress token stepsInit = 
         totalMinted contractsInit bridgeAddress token + 
         claimedAmount bridgeAddress token stepsInit"
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
    have "claimedAmount bridgeAddress token
          [UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRootInit] = 0"
      by simp
    moreover
    have "burnedAmount bridgeAddress token
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

    have *: "totalMinted contractsI' bridgeAddress token + burnedAmount bridgeAddress token steps = 
             totalMinted contractsInit bridgeAddress token +
             claimedAmount bridgeAddress token steps"
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
        have "claimedAmount bridgeAddress token steps =
              claimedAmount bridgeAddress token (DEPOSIT address' caller ID token' amount # steps)"
          using False
          by auto
        moreover
        have "burnedAmount bridgeAddress token steps = 
              burnedAmount bridgeAddress token (DEPOSIT address' caller ID token' amount # steps)"
          using False
          by auto
        ultimately
        show ?thesis
          using * ** reachableFrom_step.prems reachableFrom_step.hyps DEPOSIT
          by (metis InitFirstUpdate'.mintedTokenBI)
      next
        case True
        have "claimedAmount bridgeAddress token (step # steps) = 
              claimedAmount bridgeAddress token steps"
          using DEPOSIT True
          by simp
        moreover
        have "burnedAmount bridgeAddress token (step # steps) = 
              burnedAmount bridgeAddress token steps"
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
        have "claimedAmount bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof' # steps) =
              claimedAmount bridgeAddress token steps + amount"
          using True
          by simp
        moreover 
        have "burnedAmount bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof' # steps) =
              burnedAmount bridgeAddress token steps"
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
        have "burnedAmount bridgeAddress token (step # steps) =
              burnedAmount bridgeAddress token steps"
          using CLAIM
          by simp
        moreover
        have "claimedAmount bridgeAddress token (step # steps) = 
              claimedAmount bridgeAddress token steps"
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
      have "burnedAmount bridgeAddress token (step # steps) =
            burnedAmount bridgeAddress token steps"
        using UPDATE
        by simp
      moreover
      have "claimedAmount bridgeAddress token (step # steps) = 
            claimedAmount bridgeAddress token steps"
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
      have "burnedAmount bridgeAddress token (step # steps) =
            burnedAmount bridgeAddress token steps"
        using CANCEL_WD
        by simp
      moreover
      have "claimedAmount bridgeAddress token (step # steps) = 
            claimedAmount bridgeAddress token steps"
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
      have "burnedAmount bridgeAddress token (step # steps) =
            burnedAmount bridgeAddress token steps"
        using WITHDRAW_WD
        by simp
      moreover
      have "claimedAmount bridgeAddress token (step # steps) = 
            claimedAmount bridgeAddress token steps"
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
        "claimedAmount bridgeAddress token (step # steps) = 
         claimedAmount bridgeAddress token steps"
        using TRANSFER
        by simp

      moreover

      have burned: 
        "burnedAmount bridgeAddress token (step # steps) = 
         burnedAmount bridgeAddress token steps"
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

        have "burnedAmount bridgeAddress token (step # steps) =
              burnedAmount bridgeAddress token steps + amount'"
          using BURN True
          by simp

        moreover

        have "claimedAmount bridgeAddress token (step # steps) = 
              claimedAmount bridgeAddress token steps"
          using BURN
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
         
        have "burnedAmount bridgeAddress token (step # steps) =
              burnedAmount bridgeAddress token steps"
          using BURN False
          by simp

        moreover

        have "claimedAmount bridgeAddress token (step # steps) = 
              claimedAmount bridgeAddress token steps"
          using BURN
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
      have "burnedAmount bridgeAddress token (step # steps) = 
            burnedAmount bridgeAddress token steps"
        using RELEASE
        by simp
      moreover
      have "claimedAmount bridgeAddress token (step # steps) = 
            claimedAmount bridgeAddress token steps"
        using RELEASE False
        by simp
      ultimately
      show ?thesis
        using *
        by (metis InitFirstUpdate'.mintedTokenBI)
    qed
  qed
qed

theorem totalMintedBridgeNotDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  shows "totalMinted contractsI bridgeAddress token + 
         burnedAmount bridgeAddress token stepsInit =
         claimedAmount bridgeAddress token stepsInit"
  using assms totalMintedBridgeNotDead' 
  by presburger

end

(* ------------------------------------------------------------------------------------ *)


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
         canceledAmount tokenDepositAddress token stepsInit + 
         withdrawnAmount tokenDepositAddress token stepsInit + 
         releasedAmount tokenDepositAddress token stepsInit = 
         depositedAmount tokenDepositAddress token stepsInit"
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
           canceledAmount tokenDepositAddress token steps +
           withdrawnAmount tokenDepositAddress token steps +
           releasedAmount tokenDepositAddress token steps =
           depositedAmount tokenDepositAddress token steps"
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
        by (smt (verit, ccfv_threshold) Step.simps(13) Step.simps(19) Step.simps(21) canceledAmountConsOther depositedAmountConsDepositOther executeStep.simps(1) releasedAmountConsOther senderMessage withdrawnAmountConsOther)
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
        using canceledAmountConsCancelOther depositedAmountConsOther withdrawnAmountConsOther releasedAmountConsOther
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
        using canceledAmountConsOther depositedAmountConsOther withdrawnAmountConsOther releasedAmountConsOther
        by (smt (verit, del_insts) Step.simps(21) Step.simps(51) Step.simps(63) Step.simps(8) executeStep.simps(8) senderMessage)
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
        using  canceledAmountConsOther depositedAmountConsOther  realesedAmountConsReleaseOther withdrawnAmountConsOther 
        by (metis Step.simps(13) Step.simps(49) Step.simps(51) executeStep.simps(4) senderMessage)
    qed
  qed
qed

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Deposits that have been claimed before some significant event (e.g., last update before bridge death)\<close>

context HashProofVerifier
begin

definition claimedBeforeDeposits where
  "claimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore) 
            (deposits tokenDepositAddress token steps)"

lemma claimedBeforeDepositsNil [simp]:
  shows "claimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore [] = []"
  unfolding claimedBeforeDeposits_def
  by simp

lemma claimedBeforeDepositsConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "claimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         claimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding claimedBeforeDeposits_def
  by (cases step, auto)

lemma claimedBeforeDepositsClaimedDepositsTrivial:
  shows "claimedBeforeDeposits tokenDepositAddress bridgeAddress token steps steps = 
         claimedDeposits tokenDepositAddress bridgeAddress token steps"
  unfolding claimedBeforeDeposits_def claimedDeposits_def
  by simp

end

context InitFirstUpdate
begin

lemma claimedBeforeDepositsClaimedDeposits:
  assumes "stepsInit = steps @ stepsBefore"
  shows
    "claimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore) =
     claimedDeposits tokenDepositAddress bridgeAddress token stepsBefore"
proof-
  have "filter (\<lambda>step. isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore)
               (deposits tokenDepositAddress token steps) = []"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain step where *: "step \<in> set (deposits tokenDepositAddress token steps)"
                           "isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore"
      by (meson filter_False)
    obtain caller ID amount where 
       deposit: "step = DEPOSIT tokenDepositAddress caller ID token amount"
      using *(1) depositsConsOther
      by (metis filter.simps(2) filter_set member_filter not_Cons_self deposits_def)

    then obtain caller' amount' proof' where
      "CLAIM bridgeAddress caller' ID token amount' proof' \<in> set stepsBefore"
      using *(2)
      by (auto simp add: isClaimedID_def)

    moreover
    have "DEPOSIT tokenDepositAddress caller ID token amount \<in> set steps"
      using *(1) depositsSubsetSteps deposit
      by blast
   
    ultimately show False
      using assms noClaimBeforeDepositSteps'
      by blast
  qed
  then show ?thesis
    unfolding claimedBeforeDeposits_def claimedDeposits_def
    by simp
qed

lemma claimedBeforeDepositsCons [simp]:
  assumes "stepsInit = (step # steps) @ stepsBefore"
  shows "claimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps @ stepsBefore) =
         claimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
proof (cases "stepsBefore=[]")
  case True
  then show ?thesis
    using assms
    by (simp add: claimedBeforeDeposits_def isClaimedID_def)
next
  case False
  obtain contracts where "reachableFrom contractsInit contracts (steps @ stepsBefore)" "reachableFrom contracts contractsI [step]"
    using assms
    by (metis append_Cons append_self_conv2 reachableFromAppend reachableFromInitI)

  interpret IFU: InitFirstUpdate where contractsI=contracts and stepsInit="steps @ stepsBefore"
    by (metis (no_types, lifting) False Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def \<open>reachableFrom contractsInit contracts (steps @ stepsBefore)\<close> append_Cons append_is_Nil_conv assms firstUpdate last_appendR updatesNonZeroCons(1) updatesNonZeroInit)

  show ?thesis
    using claimedBeforeDepositsClaimedDeposits[OF assms, of token]
    using IFU.claimedBeforeDepositsClaimedDeposits[of steps stepsBefore token]
    by simp
qed

end

context HashProofVerifier
begin

definition claimedBeforeDepositsAmount where
  "claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (claimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma claimedBeforeDepositsAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms claimedBeforeDepositsAmount_def)

end

context InitFirstUpdate
begin

lemma claimedBeforeDepositsAmountClaimedDepositsAmount:
  assumes "stepsInit = steps @ stepsBefore"
  shows "claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore) =
         claimedDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore"
  using assms claimedDepositsAmount_def claimedBeforeDepositsAmount_def claimedBeforeDepositsClaimedDeposits
  by auto


lemma claimedBeforeDepositsAmountCons [simp]:
  assumes "stepsInit = (step # steps) @ stepsBefore"
  shows "claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps @ stepsBefore) =
         claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
  by (simp add: assms claimedBeforeDepositsAmount_def)

end

context HashProofVerifier
begin

definition nonClaimedBeforeDeposits where
  "nonClaimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore) 
            (deposits tokenDepositAddress token steps)"

lemma nonClaimedBeforeDepositsNil [simp]:
  shows "nonClaimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore [] = []"
  unfolding nonClaimedBeforeDeposits_def
  by simp

lemma nonClaimedBeforeDepositsConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "nonClaimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeDeposits_def
  by (cases step, auto)

definition nonClaimedBeforeDepositsAmount where
  "nonClaimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (nonClaimedBeforeDeposits tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma nonClaimedBeforeDepositsAmountNil [simp]:
  shows "nonClaimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore [] = 0"
  by (simp add: nonClaimedBeforeDepositsAmount_def)

lemma nonClaimedBeforeDepositsAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  shows "nonClaimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms nonClaimedBeforeDepositsAmount_def)

end


context HashProofVerifier
begin

text \<open>All deposits are either claimed before death or not claimed before death\<close>
theorem depositedAmountEqualsClaimedPlusNonClaimed:
  shows "depositedAmount tokenDepositAddress token steps = 
         claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps + 
         nonClaimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  unfolding depositedAmount_def claimedBeforeDepositsAmount_def nonClaimedBeforeDepositsAmount_def
  unfolding claimedBeforeDeposits_def nonClaimedBeforeDeposits_def
  by (simp add: sum_list_filter_P_notP)

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Non claimed before some event and not canceled token deposits\<close>

context HashProofVerifier
begin

(* NOTE: only on the given token *)
definition isCanceledID where
  "isCanceledID tokenDepositAddress token ID steps \<longleftrightarrow> 
   (\<exists> caller amount proof. CANCEL_WD tokenDepositAddress caller ID token amount proof \<in> set steps)"

definition nonClaimedBeforeNonCanceledDeposits where
  "nonClaimedBeforeNonCanceledDeposits tokenDepositAddress bridgeAddress token stepsBefore steps =
     filter (\<lambda> step. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore \<and>
                     \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) steps)
            (deposits tokenDepositAddress token steps)"

lemma nonClaimedBeforeNonCanceledDepositsConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  assumes "\<nexists> caller' ID' amount' proof'. step = CANCEL_WD tokenDepositAddress caller' ID' token amount' proof'"
  shows "nonClaimedBeforeNonCanceledDeposits tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeNonCanceledDeposits tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeNonCanceledDeposits_def deposits_def
  by (smt (verit, ccfv_SIG) filter.simps(2) filter_cong isCanceledID_def isDeposit.elims(2) list.set_intros(2) set_ConsD)

definition nonClaimedBeforeNonCanceledDepositsAmount where
  "nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
    sum_list (map DEPOSIT_amount (nonClaimedBeforeNonCanceledDeposits tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma nonClaimedBeforeNonCanceledDepositsAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount'. step = DEPOSIT tokenDepositAddress caller' ID' token amount'"
  assumes "\<nexists> caller' ID' amount' proof'. step = CANCEL_WD tokenDepositAddress caller' ID' token amount' proof'"
  shows "nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =
         nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  by (simp add: assms nonClaimedBeforeNonCanceledDepositsAmount_def)

end

context InitUpdateBridgeNotDeadLastValidState
begin

lemma nonClaimedBeforeNonCanceledDepositsConsCancel:
  assumes "reachableFrom contractsLVS contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
  shows "\<exists> steps1 steps2.
           nonClaimedBeforeNonCanceledDeposits tokenDepositAddress bridgeAddress token stepsInit (CANCEL_WD tokenDepositAddress caller ID token amount proof # stepsAllLVS) = 
           steps1 @ steps2 \<and>
           nonClaimedBeforeNonCanceledDeposits tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS = 
           steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2"
proof-
  let ?CANCEL_step = "CANCEL_WD tokenDepositAddress caller ID token amount proof"
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"
  let ?deposits = "deposits tokenDepositAddress token stepsAllLVS"

  obtain block "proof" where 
    cancel: "callCancelDepositWhileDead contractsLVS tokenDepositAddress (message caller 0) block ID token amount proof =
    (Success, contractsCancel)"
    using assms
    by (metis executeStep.simps(7) reachableFromSingleton)

  have "?DEPOSIT_step \<in> set stepsAllLVS"
    using InitLVS.cancelDepositOnlyAfterDeposit[OF cancel]
    by simp
  then have "?DEPOSIT_step \<in> set ?deposits"
    by (simp add: deposits_def)
  
  have *: "deposits tokenDepositAddress token (?CANCEL_step # stepsAllLVS) = ?deposits" 
    by simp


  let ?P = "\<lambda> step steps.
              \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
              \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) steps"
  show ?thesis
    unfolding nonClaimedBeforeNonCanceledDeposits_def
  proof (subst *, rule filter'')
    show "distinct ?deposits"
      using distinctDeposits[OF reachableFromInitLVS]
      by simp
  next
    show "?DEPOSIT_step \<in> set ?deposits"
      by fact
  next
    show "?P ?DEPOSIT_step stepsAllLVS"
      using assms cancel cancelDepositWhileDeadNoClaim CANCELNoDoubleCons 
      by (metis DEPOSIT_id.simps isCanceledID_def isClaimedID_def reachableFromSingleton reachableFromInitLVS reachableFrom_step)
  next
    show "\<forall> step \<in> set ?deposits. ?P step stepsAllLVS \<and> step \<noteq> ?DEPOSIT_step \<longleftrightarrow> ?P step (?CANCEL_step # stepsAllLVS)"
    proof safe
      fix step
      assume "step \<noteq> ?DEPOSIT_step" "step \<in> set ?deposits"
      then have "DEPOSIT_id step \<noteq> ID"
        using \<open>?DEPOSIT_step \<in> set ?deposits\<close>
        by (metis DEPOSIT_id.simps distinctDepositIDs distinct_map inj_on_def reachableFromInitLVS)
      assume "\<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsAllLVS"
             "isCanceledID tokenDepositAddress token (DEPOSIT_id step) (?CANCEL_step # stepsAllLVS)"
      then show False
        using \<open>DEPOSIT_id step \<noteq> ID\<close>
        by (simp add: isCanceledID_def)
    qed (auto simp add: isCanceledID_def)
  qed
qed

lemma nonClaimedBeforeNonCanceledDepositsAmountConsCancel:
  assumes "reachableFrom contractsLVS contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
  shows "nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsInit (CANCEL_WD tokenDepositAddress caller ID token amount proof # stepsAllLVS) =
         nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS - amount"
        "amount \<le> nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS"
  using nonClaimedBeforeNonCanceledDepositsConsCancel[OF assms]
  unfolding nonClaimedBeforeNonCanceledDepositsAmount_def
  by auto

end

text \<open>Before the bridge dies all non-claimed token deposits are not canceled\<close>
context StrongHashProofVerifier
begin

lemma nonCanceledNonClaimedBridgeNotDead:
  assumes "reachableFrom contractsInit contracts steps"
          "\<not> bridgeDead contracts tokenDepositAddress"
    shows "nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps =
           nonClaimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms noCancelBeforeBridgeDead[OF assms]
  unfolding nonClaimedBeforeNonCanceledDepositsAmount_def nonClaimedBeforeDepositsAmount_def
  unfolding nonClaimedBeforeNonCanceledDeposits_def nonClaimedBeforeDeposits_def isCanceledID_def
  by metis

end


context BridgeDead
begin

lemma canceledAmountInvariant':
  shows
  "nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsInit  ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) + 
   canceledAmount tokenDepositAddress token ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) = 
   nonClaimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsInit ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit)" (is "?NCC (stepsBD @ [stepDeath]) + ?C (stepsBD @ [stepDeath]) = ?NC (stepsBD @ [stepDeath])")
  using reachableFromContractsBD BridgeDead_axioms
proof (induction contractsDead contractsBD stepsBD rule: reachableFrom.induct)
  case (reachableFrom_base contractsBD)
  then interpret BD: BridgeDead where contractsBD=contractsBD and stepsBD="[]" and contractsDead=contractsBD
    .
  have *: "?NCC [] + ?C [] = ?NC []"
    using LVSDead'.reachableFromInitLVS canceledAmountBridgeNotDead nonCanceledNonClaimedBridgeNotDead notBridgeDead'
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
        using LVSDead'.nonClaimedBeforeNonCanceledDepositsAmountConsCancel
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
        by (metis BD.LVSBD.nonClaimedBeforeNonCanceledDepositsAmountConsCancel(1) BD.LVSBD.nonClaimedBeforeNonCanceledDepositsAmountConsCancel(2) BD.LVSBD.stepsAllLVS_def CANCEL_WD Cons_eq_append_conv True append_eq_appendI reachableFrom.reachableFrom_step reachableFrom_base reachableFrom_step.hyps(2))
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
  "nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD + 
   canceledAmount tokenDepositAddress token stepsAllBD = 
   nonClaimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
  unfolding stepsAllBD_def
  using canceledAmountInvariant'[of token]
  by auto  
end



(* ------------------------------------------------------------------------------------ *)
section \<open>Minted token balance of all users (affected by claims, transfers and burns) \<close>

context HashProofVerifier
begin

fun isTransfer where
  "isTransfer bridgeAddress token (TRANSFER address' caller receiver token' amount) \<longleftrightarrow> address' = bridgeAddress \<and> token' = token"
| "isTransfer bridgeAddress token _ = False"


definition claimsTransfersBurns where
  "claimsTransfersBurns bridgeAddress token steps = 
      filter (\<lambda> step. isClaim bridgeAddress token step \<or> 
                      isTransfer bridgeAddress token step \<or>
                      isBurn bridgeAddress token step) steps"


lemma claimsTransfersBurnsNil [simp]:
  shows "claimsTransfersBurns bridgeAddress token [] = []"
  by (simp add: claimsTransfersBurns_def)

lemma claimsTransfersBurnsConsOther [simp]: 
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"  
  assumes "\<nexists> caller' receiver' amount' proof'. step = TRANSFER bridgeAddress caller' receiver' token amount'"
  assumes "\<nexists> caller' ID' amount'. step = BURN bridgeAddress caller' ID' token amount'"
  shows "claimsTransfersBurns bridgeAddress token (step # steps) = 
         claimsTransfersBurns bridgeAddress token steps"
  using assms
  by (cases step) (auto simp add: claimsTransfersBurns_def)

lemma claimsTransfersBurnsConsClaim [simp]: 
  shows "claimsTransfersBurns bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof # steps) = 
         CLAIM bridgeAddress caller ID token amount proof # claimsTransfersBurns bridgeAddress token steps"
  by (simp add: claimsTransfersBurns_def)

lemma claimsTransfersBurnsConsTransfer [simp]: 
  shows "claimsTransfersBurns bridgeAddress token (TRANSFER bridgeAddress caller receiver token amount # steps) = 
         TRANSFER bridgeAddress caller receiver token amount # claimsTransfersBurns bridgeAddress token steps"
  by (simp add: claimsTransfersBurns_def)

lemma claimsTransfersBurnsConsBurn [simp]: 
  shows "claimsTransfersBurns bridgeAddress token (BURN bridgeAddress caller ID token amount # steps) = 
         BURN bridgeAddress caller ID token amount # claimsTransfersBurns bridgeAddress token steps"
  by (simp add: claimsTransfersBurns_def)

definition mintedUserBalances_fun where
  "mintedUserBalances_fun step state = 
       (case step of CLAIM address caller ID token amount proof \<Rightarrow> addToBalance state caller amount 
                   | TRANSFER address caller receiver token amount \<Rightarrow> transferBalance state caller receiver amount
                   | BURN address caller ID token amount \<Rightarrow> removeFromBalance state caller amount
                   | _ \<Rightarrow> state)"

lemma mintedUserBalances_funFiniteKeys [simp]:
  assumes "finite (Mapping.keys (balances state))"
  shows "finite (Mapping.keys (balances (mintedUserBalances_fun step state)))"
  using assms
  by (cases step) (auto simp add: mintedUserBalances_fun_def addToBalance_def transferBalance_def removeFromBalance_def)

definition mintedUserBalances' :: "address \<Rightarrow> address \<Rightarrow> Step list \<Rightarrow> ERC20State" where
  "mintedUserBalances' address token steps = 
    foldr mintedUserBalances_fun steps ERC20Constructor"

definition mintedUserBalances :: "address \<Rightarrow> address \<Rightarrow> Step list \<Rightarrow> ERC20State" where
 "mintedUserBalances bridgeAddress token steps = 
  mintedUserBalances' bridgeAddress token (claimsTransfersBurns bridgeAddress token steps)"

lemma mintedUserBalances'Nil [simp]:
  shows "mintedUserBalances' bridgeAddress token [] = ERC20Constructor"
  by (simp add: mintedUserBalances'_def)

lemma mintedUserBalancesCons:
 "mintedUserBalances' bridgeAddress token (step # steps) = 
  mintedUserBalances_fun step (mintedUserBalances' bridgeAddress token steps)"
  unfolding mintedUserBalances'_def
  by simp

lemma claimsTransfersBurnsBalance'_finiteKeys [simp]:
  shows "finite (Mapping.keys (balances (mintedUserBalances' bridgeAddress token steps)))"
  by (induction steps) (auto simp add: mintedUserBalancesCons)

lemma mintedUserBalancesNil [simp]:
  shows "mintedUserBalances bridgeAddress token [] = ERC20Constructor"
  by (simp add: mintedUserBalances_def)

lemma mintedUserBalancesConsOther [simp]:
  assumes "\<nexists> caller' ID' amount' proof'. step = CLAIM bridgeAddress caller' ID' token amount' proof'"  
  assumes "\<nexists> caller' receiver' amount' proof'. step = TRANSFER bridgeAddress caller' receiver' token amount'"  
  assumes "\<nexists> caller' ID' amount'. step = BURN bridgeAddress caller' ID' token amount'"  
  shows "mintedUserBalances bridgeAddress token (step # steps) = 
         mintedUserBalances bridgeAddress token steps"
  using assms
  unfolding mintedUserBalances_def
  by simp

lemma mintedUserBalances'ConsClaim [simp]:
  shows "mintedUserBalances' bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof # steps) = 
         addToBalance (mintedUserBalances' bridgeAddress token steps) caller amount"
  unfolding mintedUserBalances'_def
  by (simp add: mintedUserBalances_fun_def)

lemma mintedUserBalancesConsClaim [simp]:
  shows "mintedUserBalances bridgeAddress token (CLAIM bridgeAddress caller ID token amount proof # steps) = 
         addToBalance (mintedUserBalances bridgeAddress token steps) caller amount"
  unfolding mintedUserBalances_def
  by simp

lemma mintedUserBalances'ConsTransfer [simp]:
  shows "mintedUserBalances' bridgeAddress token (TRANSFER bridgeAddress caller receiver token amount # steps) = 
         transferBalance (mintedUserBalances' bridgeAddress token steps) caller receiver amount"
  unfolding mintedUserBalances'_def
  by (simp add: mintedUserBalances_fun_def)

lemma mintedUserBalancesConsTransfer [simp]:
  shows "mintedUserBalances bridgeAddress token (TRANSFER bridgeAddress caller receiver token amount # steps) = 
         transferBalance (mintedUserBalances bridgeAddress token steps) caller receiver amount"
  unfolding mintedUserBalances_def
  by simp

lemma mintedUserBalances'ConsBurn [simp]:
  shows "mintedUserBalances' bridgeAddress token (BURN bridgeAddress caller ID token amount # steps) = 
         removeFromBalance (mintedUserBalances' bridgeAddress token steps) caller amount"
  unfolding mintedUserBalances'_def
  by (simp add: mintedUserBalances_fun_def)

lemma mintedUserBalancesConsBurn [simp]:
  shows "mintedUserBalances bridgeAddress token (BURN bridgeAddress caller ID token amount # steps) = 
         removeFromBalance (mintedUserBalances bridgeAddress token steps) caller amount"
  unfolding mintedUserBalances_def
  by simp

lemma mintedUserBalances_finiteKeys [simp]:
  shows "finite (Mapping.keys (balances (mintedUserBalances bridgeAddress token steps)))"
  unfolding mintedUserBalances_def
  by simp


text \<open>Claims, burns and transfers faithfully represent balances of minted tokens on the bridge\<close>
theorem mintedUserBalancesAccountBalance:
  assumes "reachableFrom contracts contracts' steps"
  assumes "accountBalance contracts (mintedTokenB contracts bridgeAddress token) account = 0"
  shows "balanceOf (mintedUserBalances bridgeAddress token steps) account = 
         accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account"
  using assms
proof (induction contracts contracts' steps)
  case (reachableFrom_base contracts)
  then show ?case
    by simp
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  then have *: 
    "balanceOf (mintedUserBalances bridgeAddress token steps) account =
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
        by (metis reachableFromBridgeTokenPairs reachableFromITokenPairs mintedUserBalancesConsTransfer)
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
          using TRANSFER True \<open>account \<noteq> caller'\<close> \<open>account \<noteq> receiver'\<close> addToBalanceBalanceOfOther removeFromBalanceBalanceOfOther mintedUserBalancesConsTransfer transferBalance_def 
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
          using mintedUserBalancesConsOther
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

theorem totalMintedUserBalances:
  assumes "reachableFrom contracts contracts' steps"
  assumes "totalMinted contracts bridgeAddress token = 0"
  assumes "finiteBalances contracts (mintedTokenB contracts bridgeAddress token)"
  shows "totalBalance (mintedUserBalances bridgeAddress token steps) =
         totalMinted contracts' bridgeAddress token"
proof (rule totalBalanceEq, safe)
  show "finite (Mapping.keys (balances (mintedUserBalances bridgeAddress token steps)))"
    by simp
next
  show "finite (Mapping.keys (balances (the (ERC20state contracts' (mintedTokenB contracts' bridgeAddress token)))))"
    by (metis assms(1) assms(3) finiteBalances_def reachableFromBridgeTokenPairs reachableFromFiniteBalances reachableFromITokenPairs)
next
  fix user
  have "finite (Mapping.keys (balances (the (ERC20state contracts (mintedTokenB contracts bridgeAddress token))))) "
    using assms(3) finiteBalances_def by blast
  then show "balanceOf (mintedUserBalances bridgeAddress token steps) user = 
        accountBalance contracts' (mintedTokenB contracts' bridgeAddress token) user"
    using mintedUserBalancesAccountBalance assms totalBalanceZero reachableFromBridgeMintedToken
    by metis
qed

end

context InitFirstUpdate
begin

lemma totalMintedUserBalancesClaimedBurnedAmount:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  assumes "finiteBalances contractsInit (mintedTokenB contractsInit bridgeAddress token)"
  shows "totalBalance (mintedUserBalances bridgeAddress token stepsInit) + 
         burnedAmount bridgeAddress token stepsInit =
         claimedAmount bridgeAddress token stepsInit"
  using totalMintedUserBalances[OF reachableFromInitI] totalMintedBridgeNotDead
  using assms
  by metis

end

(* ------------------------------------------------------------------------------------ *)
section \<open>Minted token balance of users that have not withdrawn their funds when the bridge died) \<close>

context HashProofVerifier
begin

definition nonWithdrawnMintedUserBalances_fun where
  "nonWithdrawnMintedUserBalances_fun tokenDepositAddress token step state = 
    (case step of WITHDRAW_WD address' caller' token' amount' proof' \<Rightarrow> 
                    if address' = tokenDepositAddress \<and> token' = token then 
                       removeFromBalance state caller' amount'
                    else
                       state
                   | _ \<Rightarrow> state)"

lemma nonWithdrawnMintedUserBalances_funOther [simp]:
  assumes "\<nexists> caller amount proof. step = WITHDRAW_WD tokenDepositAddress caller token amount proof"
  shows "nonWithdrawnMintedUserBalances_fun tokenDepositAddress token step state = state"
  using assms
  by (cases step, auto simp add: nonWithdrawnMintedUserBalances_fun_def)

lemma nonWithdrawnMintedUserBalances_funWithdraw [simp]:
  shows "nonWithdrawnMintedUserBalances_fun tokenDepositAddress token (WITHDRAW_WD tokenDepositAddress caller token amount proof) state = 
        removeFromBalance state caller amount"
  by (simp add: nonWithdrawnMintedUserBalances_fun_def)

definition nonWithdrawnMintedUserBalances where
  "nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore steps = 
    foldr (nonWithdrawnMintedUserBalances_fun tokenDepositAddress token) steps (mintedUserBalances bridgeAddress token stepsBefore)"

lemma nonWithdrawnMintedUserBalances_funFiniteKeys [simp]:
  assumes "finite (Mapping.keys (balances state))"
  shows "finite (Mapping.keys (balances (nonWithdrawnMintedUserBalances_fun address token step state)))"
  using assms
  by (cases step, auto simp add: nonWithdrawnMintedUserBalances_fun_def removeFromBalance_def)

lemma nonWithdrawnMintedUserBalancesNil [simp]:
  shows "nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore [] = 
         mintedUserBalances bridgeAddress token stepsBefore"
  by (simp add: nonWithdrawnMintedUserBalances_def)

lemma nonWithdrawnMintedUserBalancesCons:
  shows "nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore (step # steps) = 
         nonWithdrawnMintedUserBalances_fun tokenDepositAddress token step (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore steps)"
  unfolding nonWithdrawnMintedUserBalances_def
  by simp

lemma nonWithdrawnMintedUserBalances_finiteKeys [simp]:
  shows "finite (Mapping.keys (balances (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore steps)))"
  by (induction steps) (auto simp add: nonWithdrawnMintedUserBalancesCons)

lemma nonWithdrawnMintedUserBalancesConsOther:
  assumes "\<nexists> caller' ID' amount' proof'. step = WITHDRAW_WD tokenDepositAddress caller' token amount' proof'"  
  shows "nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore
           (step # steps) =
         nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore
           steps"
  using assms
  unfolding nonWithdrawnMintedUserBalances_def
  by (simp add: nonWithdrawnMintedUserBalancesCons)

lemma nonWithdrawnMintedUserBalancesWithdraw [simp]:
  shows "nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsInit
           (WITHDRAW_WD tokenDepositAddress caller token amount proof # steps @ stepsInit) = 
         removeFromBalance (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsInit
           (steps @ stepsInit)) caller amount"
  unfolding nonWithdrawnMintedUserBalances_def
  by (simp add: nonWithdrawnMintedUserBalancesCons)

lemma nonWithdrawnMintedUserBalancesNoWithdraw:
  assumes "\<nexists>amount proof. WITHDRAW_WD tokenDepositAddress caller token amount proof \<in> set steps"
  shows "balanceOf (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore steps) caller = 
         balanceOf (mintedUserBalances bridgeAddress token stepsBefore) caller"
  using assms
proof (induction steps)
  case Nil
  then show ?case
    by simp
next
  case (Cons step steps)
  then show ?case
    by (cases step, auto simp add: nonWithdrawnMintedUserBalancesCons nonWithdrawnMintedUserBalances_fun_def)
qed


lemma nonWithdrawnMintedUserBalancesBridgeNotDead:
  assumes "reachableFrom contractsInit contractsI stepsInit"
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore stepsInit = 
         mintedUserBalances bridgeAddress token stepsBefore"
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
      by (auto simp add: nonWithdrawnMintedUserBalancesCons)
  qed 
qed


definition nonWithdrawnNonBurnedClaimedBeforeAmount where
  "nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsBefore steps = 
   totalBalance (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsBefore steps)"

lemma nonWithdrawnClaimedBeforeDeathAmountConsOther [simp]:
  assumes "\<nexists> caller' ID' amount' proof'. step = WITHDRAW_WD tokenDepositAddress caller' token amount' proof'"  
  shows "nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsBefore
          (step # steps) =
         nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsBefore
          steps"
  unfolding nonWithdrawnNonBurnedClaimedBeforeAmount_def
  using assms nonWithdrawnMintedUserBalancesCons nonWithdrawnMintedUserBalances_funOther 
  by presburger

lemma nonWithdrawnClaimedBeforeDeathAmountConsWithdraw[simp]: 
  assumes "amount \<le> balanceOf (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsInit (steps @ stepsInit)) caller"
  shows
   "nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsInit
      (WITHDRAW_WD tokenDepositAddress caller token amount proof # steps @ stepsInit) = 
    nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsInit
      (steps @ stepsInit) - amount" 
   "amount \<le> nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsInit
      (steps @ stepsInit)"
  using assms totalBalance_removeFromBalance
  unfolding nonWithdrawnNonBurnedClaimedBeforeAmount_def
  by auto

definition nonBurnedClaimedBeforeAmount where
  "nonBurnedClaimedBeforeAmount bridgeAddress token steps = totalBalance (mintedUserBalances bridgeAddress token steps)"

lemma nonWithdrawnClaimedBeforeAmountBridgeNotDead:
  assumes "reachableFrom contractsInit contractsI (steps @ stepsBefore)"
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore) =
         nonBurnedClaimedBeforeAmount bridgeAddress token stepsBefore"
  unfolding nonWithdrawnNonBurnedClaimedBeforeAmount_def nonBurnedClaimedBeforeAmount_def
  using nonWithdrawnMintedUserBalancesBridgeNotDead[OF assms]
  by simp

end

context InitFirstUpdate
begin

theorem claimedBeforeDepositsAmountBridgeNotDead:
  assumes "stepsInit = steps @ stepsBefore"
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  assumes "finiteBalances contractsInit (mintedTokenB contractsInit bridgeAddress token)"
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "nonBurnedClaimedBeforeAmount bridgeAddress token stepsBefore +
         burnedAmount bridgeAddress token stepsBefore =
         claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore (steps @ stepsBefore)"
proof-
  have "totalBalance (mintedUserBalances bridgeAddress token stepsBefore) + 
        burnedAmount bridgeAddress token stepsBefore =
        claimedDepositsAmount tokenDepositAddress bridgeAddress token stepsBefore"
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
      using IFU.totalMintedUserBalancesClaimedBurnedAmount IFU.claimedEqualsClaimedDeposits
      using assms 
      by presburger
  qed
  then show ?thesis
    using claimedBeforeDepositsAmountClaimedDepositsAmount[OF assms(1)]
    using nonWithdrawnClaimedBeforeAmountBridgeNotDead
    using assms reachableFromInitI
    using nonBurnedClaimedBeforeAmount_def
    by presburger
qed

end

context BridgeDeadInitFirstUpdate
begin

theorem withdrawnAmountInvariant':
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  shows
  "withdrawnAmount tokenDepositAddress token ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) + 
   nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsInit ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit) +
   burnedAmount bridgeAddress token stepsInit = 
   claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsInit ((stepsBD @ [stepDeath]) @ stepsNoUpdate @ [UPDATE_step] @ stepsInit)" (is "?W (stepsBD @ [stepDeath]) + ?N (stepsBD @ [stepDeath]) + ?B = ?C (stepsBD @ [stepDeath])")
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
    using withdrawnAmountBridgeNotDead[OF InitDead'.reachableFromInitI BD.notBridgeDead', of token]
    using IFUDead'.claimedBeforeDepositsAmountBridgeNotDead[where steps="stepsNoUpdate @ [UPDATE_step]" and stepsBefore=stepsInit and token=token]
    using notBridgeDead'
    using reachableFrom_base.prems LVSDead'.reachableFromInitLVS nonWithdrawnClaimedBeforeAmountBridgeNotDead properTokenFiniteBalancesMinted
    unfolding BD.stepsBeforeDeath_def
    by (metis  LVSDead'.stepsAllLVS_def add_cancel_right_left append.assoc append_Nil)

  show ?case
  proof (cases stepDeath)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (CANCEL_WD address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
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
      then have "balanceOf (mintedUserBalances bridgeAddress token stepsInit) caller' = amount'" 
        using mintedUserBalancesAccountBalance[OF reachableFromInitI totalBalanceZero, of bridgeAddress token caller']
        using reachableFrom_base.prems(2)
        using properTokenFiniteBalancesMinted reachableFrom_base.prems
        unfolding finiteBalances_def
        by blast
      then have **: "amount' \<le> balanceOf (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsInit
          ((stepsNoUpdate @ [UPDATE_step]) @ stepsInit)) caller'"
        using nonWithdrawnMintedUserBalancesBridgeNotDead
        by (metis InitDead'.reachableFromInitI append.assoc le_refl notBridgeDead' stepsBeforeDeath_def)
      show ?thesis
        using nonWithdrawnClaimedBeforeDeathAmountConsWithdraw[OF **]
        using True * WITHDRAW_WD
        using IFUDead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
        unfolding BD.stepsBeforeDeath_def
        by auto
    qed
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (RELEASE address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFUDead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
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
      using IFU.claimedBeforeDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (CANCEL_WD address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFU.claimedBeforeDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using *
      using IFU.claimedBeforeDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress") auto
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using *
      using IFU.claimedBeforeDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using *
      using IFU.claimedBeforeDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
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
      then have "balanceOf (mintedUserBalances bridgeAddress token stepsInit) caller' = amount'" 
        using mintedUserBalancesAccountBalance
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
      then have "balanceOf (mintedUserBalances bridgeAddress token stepsInit) caller' = 
                 balanceOf (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsInit BD.stepsAllBD) caller'"
        using nonWithdrawnMintedUserBalancesNoWithdraw
        by simp

      ultimately

      have **: "amount' \<le> balanceOf (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsInit BD.stepsAllBD) caller'"
        by simp

      then show ?thesis
        using True * WITHDRAW_WD
        using nonWithdrawnClaimedBeforeDeathAmountConsWithdraw[of amount' tokenDepositAddress bridgeAddress token stepsInit "stepsBD @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step]"]
        using BDIFU.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
        unfolding BD.stepsAllBD_def
        by simp
    qed
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFU.claimedBeforeDepositsAmountCons[of step "stepsBD @[stepDeath] @ stepsNoUpdate @ [UPDATE_step]" stepsInit]
      unfolding BD.stepsAllBD_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (RELEASE address' caller' ID' token' amount')
    then show ?thesis
      using *
      using IFU.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  qed
qed

lemma withdrawnAmountInvariant:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "totalMinted contractsInit bridgeAddress token = 0"
  shows "withdrawnAmount tokenDepositAddress token stepsAllBD + 
         nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD +
         burnedAmount bridgeAddress token stepsInit = 
         claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
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

definition nonReleasedBurns where
  "nonReleasedBurns tokenDepositAddress bridgeAddress token stepsBefore steps = 
   filter (\<lambda> step. \<not> isReleasedID tokenDepositAddress token (BURN_id step) steps) (burns bridgeAddress token stepsBefore)"

lemma nonReleasedBurnsDeposits_Nil [simp]: 
  "nonReleasedBurns tokenDepositAddress bridgeAddress token [] steps = []" 
  unfolding nonReleasedBurns_def
  by simp

definition nonReleasedBurnsAmount where
  "nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsBefore steps = 
    sum_list (map BURN_amount (nonReleasedBurns tokenDepositAddress bridgeAddress token stepsBefore steps))"

lemma nonReleasedBurnsAmount_Nil [simp]: 
  "nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token [] steps = 0" 
  unfolding nonReleasedBurnsAmount_def
  by simp

lemma  nonReleasedBurnsConsNotBurn [simp]:
  assumes "\<nexists> caller ID amount. step = BURN bridgeAddress caller ID token amount"
  shows "nonReleasedBurns tokenDepositAddress bridgeAddress token (step # stepsBefore) steps =  
         nonReleasedBurns tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonReleasedBurns_def
  by simp

lemma nonReleasedBurnsConsNotRelease [simp]:
  assumes "\<nexists> caller ID amount proof. step = RELEASE tokenDepositAddress caller ID token amount proof"
  shows "nonReleasedBurns tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =  
         nonReleasedBurns tokenDepositAddress bridgeAddress token stepsBefore steps"
  unfolding nonReleasedBurns_def
proof (rule filter_cong)
  fix step'
  assume "step' \<in> set (burns bridgeAddress token stepsBefore)"
  then show "(\<not> isReleasedID tokenDepositAddress token (BURN_id step') (step # steps)) =
             (\<not> isReleasedID tokenDepositAddress token (BURN_id step') steps)"
    using assms
    by (auto simp add: isReleasedID_def)
qed simp

lemma nonReleasedBurnsAmountConsNotRelease [simp]:
  assumes "\<nexists> caller ID amount proof. step = RELEASE tokenDepositAddress caller ID token amount proof"
  shows "nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsBefore (step # steps) =  
        nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonReleasedBurnsAmount_def
  by simp

lemma nonReleasedBurnsAmountConsNotBurn [simp]:
  assumes "\<nexists> caller ID amount. step = BURN bridgeAddress caller ID token amount"
  shows "nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token (step # stepsBefore) steps =  
         nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsBefore steps"
  using assms
  unfolding nonReleasedBurnsAmount_def
  by simp

end

context InitFirstUpdate
begin

lemma nonReleasedBurnsConsBurn [simp]:
  assumes "stepsInit = BURN bridgeAddress caller ID token amount # steps"
  shows "nonReleasedBurns tokenDepositAddress bridgeAddress token
           (BURN bridgeAddress caller ID token amount # steps) steps =
         BURN bridgeAddress caller ID token amount # 
         nonReleasedBurns tokenDepositAddress bridgeAddress token
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
    unfolding nonReleasedBurns_def
    by simp
qed

lemma nonReleasedBurnsAmountConsBurn:
  assumes "stepsInit = BURN bridgeAddress caller ID token amount # steps"
  shows "nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token
          (BURN bridgeAddress caller ID token amount # steps) steps = 
        nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token
          steps steps + amount"
  using assms
  unfolding nonReleasedBurnsAmount_def
  by simp
end

context InitUpdateBridgeNotDeadLastValidState
begin

lemma nonReleasedBurnsAmountConsRelease:
  assumes "reachableFrom contractsLVS contractsRelease [RELEASE tokenDepositAddress caller ID token amount proof]"
  shows "nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit
           (RELEASE tokenDepositAddress caller ID token amount proof # stepsAllLVS) + amount =
         nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit
           stepsAllLVS"
proof-
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller ID token amount proof"
  let ?burns = "burns bridgeAddress token stepsInit"

  have "?BURN_step \<in> set stepsInit"
    using burnBeforeRelease
    by (metis assms executeStep.simps(4) reachableFromSingleton senderMessage)
  then have "?BURN_step \<in> set ?burns"
    unfolding burns_def
    by simp

  let ?P = "\<lambda> step steps. \<not> isReleasedID tokenDepositAddress token (BURN_id step) steps"

  have "\<exists> steps1 steps2. 
          nonReleasedBurns tokenDepositAddress bridgeAddress token stepsInit (?RELEASE_step # stepsAllLVS) = steps1 @ steps2 \<and>
          nonReleasedBurns tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS = steps1 @ [?BURN_step] @ steps2"
    unfolding nonReleasedBurns_def
  proof (rule filter'')
    show "?BURN_step \<in> set ?burns"
      by fact
  next
    show "distinct (burns bridgeAddress token stepsInit)"
      using distinctBurns reachableFromInitI by blast
  next
    show "\<not> isReleasedID tokenDepositAddress token (BURN_id ?BURN_step) stepsAllLVS"
      using RELEASENoDoubleCons[of contractsInit contractsRelease] reachableFromTrans[OF assms(1) reachableFromInitLVS]
      by (simp add: isReleasedID_def)
  next
    show "\<forall> step \<in> set ?burns. (?P step stepsAllLVS \<and> step \<noteq> ?BURN_step \<longleftrightarrow> ?P step (?RELEASE_step # stepsAllLVS))"
    proof safe
      fix step
      assume "step \<in> set ?burns" "step \<noteq> ?BURN_step"
      then have "BURN_id step \<noteq> ID"
        using \<open>?BURN_step \<in> set ?burns\<close>
        by (metis BURN_id.simps distinctBurnIDs distinct_map inj_on_def reachableFromInitI)
      assume "\<not> isReleasedID tokenDepositAddress token (BURN_id step) stepsAllLVS"
             "isReleasedID tokenDepositAddress token (BURN_id step) (?RELEASE_step # stepsAllLVS)"
      then show False
        using \<open>BURN_id step \<noteq> ID\<close>
        by (simp add: isReleasedID_def)
    qed (auto simp add: isReleasedID_def)
  qed

  then show ?thesis
    unfolding nonReleasedBurnsAmount_def
    by auto
qed

end

context InitFirstUpdate
begin

(* FIXME: try to derive this from the previous lemma (strong version proved in the LVS locale) *)
lemma nonReleasedBurnsAmountConsReleaseWeak:
  assumes "stepsInit = RELEASE tokenDepositAddress caller ID token amount proof # steps"
  shows "nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token steps
             (RELEASE tokenDepositAddress caller ID token amount proof # steps) + amount = 
         nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token steps steps"
proof-
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller ID token amount proof"
  let ?burns = "burns bridgeAddress token steps"

  have "?BURN_step \<in> set steps"
    using assms burnBeforeReleaseSteps by auto
  then have "?BURN_step \<in> set ?burns"
    unfolding burns_def
    by simp

  let ?P = "\<lambda> step steps. \<not> isReleasedID tokenDepositAddress token (BURN_id step) steps"

  have "\<exists> steps1 steps2. 
          nonReleasedBurns tokenDepositAddress bridgeAddress token steps (?RELEASE_step # steps) = steps1 @ steps2 \<and>
          nonReleasedBurns tokenDepositAddress bridgeAddress token steps steps = steps1 @ [?BURN_step] @ steps2"
    unfolding nonReleasedBurns_def
  proof (rule filter'')
    show "?BURN_step \<in> set ?burns"
      by fact
  next
    show "distinct ?burns"
      using assms distinctBurns reachableFromInitI by fastforce
  next
    show "\<not> isReleasedID tokenDepositAddress token (BURN_id ?BURN_step) steps"
      using RELEASENoDoubleCons[of contractsInit _] 
      using assms isReleasedID_def reachableFromInitI 
      by auto
  next
    show "\<forall> step \<in> set ?burns. (?P step steps \<and> step \<noteq> ?BURN_step \<longleftrightarrow> ?P step (?RELEASE_step # steps))"
    proof safe
      fix step
      assume "step \<in> set ?burns" "step \<noteq> ?BURN_step"
      then have "BURN_id step \<noteq> ID"
        using \<open>?BURN_step \<in> set ?burns\<close>
        by (metis BURN_id.simps Step.simps(35) assms burnsConsOther distinctBurnIDs distinct_map inj_on_def reachableFromInitI)
      assume "\<not> isReleasedID tokenDepositAddress token (BURN_id step) steps"
             "isReleasedID tokenDepositAddress token (BURN_id step) (?RELEASE_step # steps)"
      then show False
        using \<open>BURN_id step \<noteq> ID\<close>
        by (simp add: isReleasedID_def)
    qed (auto simp add: isReleasedID_def)
  qed

  then show ?thesis
    unfolding nonReleasedBurnsAmount_def
    by auto
qed

end


context InitFirstUpdate
begin

theorem releasedInvariantBase:
  shows "releasedAmount tokenDepositAddress token stepsInit +
         nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsInit =
         burnedAmount bridgeAddress token stepsInit"
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

    have *: "releasedAmount tokenDepositAddress token steps +
             nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token steps steps =
             burnedAmount bridgeAddress token steps"
      using IFU'.InitFirstUpdate_axioms reachableFrom_step.IH by blast

    then show ?thesis
    proof (cases step)
      case (BURN address' caller' ID' token' amount')
      then show ?thesis
        using * IFU.nonReleasedBurnsAmountConsBurn
        by (cases "address' = bridgeAddress \<and> token' = token") auto
    next
      case (RELEASE address' caller' ID' token' amount' proof')
      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token")
        case True

        show ?thesis
          using True * RELEASE
          using IFU.nonReleasedBurnsAmountConsReleaseWeak
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

lemma releasedAmountInvariantStep:
  assumes "executeStep contractsLVS blockNum block step = (Success, contracts')" 
  assumes "releasedAmount tokenDepositAddress token stepsAllLVS  + 
           nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLVS  = 
           burnedAmount bridgeAddress token stepsInit"
  shows "releasedAmount tokenDepositAddress token (step # stepsAllLVS)  + 
         nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit (step # stepsAllLVS)  = 
         burnedAmount bridgeAddress token stepsInit"
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
      using True assms RELEASE nonReleasedBurnsAmountConsRelease[OF *]
      by simp
  qed
qed auto

end

context InitFirstUpdateLastUpdate
begin

lemma releasedAmountInvariantBeforeDeath:
  assumes "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
  shows "releasedAmount tokenDepositAddress token stepsAllLU  + 
         nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLU  = 
         burnedAmount bridgeAddress token stepsInit"
  unfolding stepsAllLU_def
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

  have *: "releasedAmount tokenDepositAddress token (I.UPDATE_step # stepsInit) +
           nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit (I.UPDATE_step # stepsInit) =
           burnedAmount bridgeAddress token stepsInit"
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
      using True LVS.releasedAmountInvariantStep *
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
    next
      show "updatesNonZero (stepsNoUpdate @ [I.UPDATE_step] @ stepsInit) "
        by (metis I.updatesNonZeroLU append_Cons updatesNonZeroCons(1))
    qed

    have *: "releasedAmount tokenDepositAddress token (stepsNoUpdate @ [I.UPDATE_step] @ stepsInit) +
             nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit (stepsNoUpdate @ [I.UPDATE_step] @ stepsInit) =
             burnedAmount bridgeAddress token stepsInit"
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
      using * LVS.releasedAmountInvariantStep reachableFrom_step.hyps
      unfolding LVS.stepsAllLVS_def
      by simp
  qed
qed

theorem tokenDepositBalanceBridgeNotDead:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "\<not> bridgeDead contractsLU tokenDepositAddress"
  assumes "totalTokenBalance contractsInit (mintedTokenB contractsInit bridgeAddress token) = 0"
  shows "tokenDepositBalance contractsLU token tokenDepositAddress =
         nonClaimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLU +
         nonBurnedClaimedBeforeAmount bridgeAddress token stepsInit + 
         nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLU"
proof-
  have *: "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
    using assms(2) reachableFromBridgeDead reachableFromLastUpdate'LU by blast

  have "tokenDepositBalance contractsLU token tokenDepositAddress + 
        releasedAmount tokenDepositAddress token stepsAllLU = 
        depositedAmount tokenDepositAddress token stepsAllLU"
    using IFLU.tokenDepositBalanceInvariant[OF assms(1)]
    using canceledAmountBridgeNotDead[OF reachableFromInitLU assms(2), of token]
    using withdrawnAmountBridgeNotDead[OF reachableFromInitLU assms(2), of token]
    by simp
  moreover
  have "nonBurnedClaimedBeforeAmount bridgeAddress token stepsInit + burnedAmount bridgeAddress token stepsInit =
        claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLU"
    using IFLU.claimedBeforeDepositsAmountBridgeNotDead[of "stepsNoUpdate @ [UPDATE_step]" stepsInit token]
    using assms
    unfolding stepsAllLU_def
    by auto
  ultimately
  show ?thesis
    using releasedAmountInvariantBeforeDeath[OF *, of token]
    using depositedAmountEqualsClaimedPlusNonClaimed[of tokenDepositAddress token stepsAllLU bridgeAddress stepsInit]
    by simp
qed


end

context InitUpdateBridgeNotDeadLastValidState
begin

lemma stepsInitEmptyNoReleases:
  assumes "stepsInit = []"
  assumes "\<nexists> stateRoot. UPDATE (stateOracleAddressTD contractsInit tokenDepositAddress) stateRoot \<in> set stepsLVS"
  shows "releasedAmount tokenDepositAddress token (stepsLVS @ [UPDATE_step]) = 0"
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

  have *: "releasedAmount tokenDepositAddress token (steps @ [I.UPDATE_step]) = 0"
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

lemma releasedAmountInvariant:
  shows "releasedAmount tokenDepositAddress token stepsAllBD  + 
         nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD  = 
         burnedAmount bridgeAddress token stepsInit"
  using reachableFromContractsBD BridgeDeadInitFirstUpdate_axioms
  unfolding stepsAllBD_def
proof (induction contractsDead contractsBD stepsBD rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  show ?case
  proof (cases "stepsInit=[]")
    case True
    then show ?thesis
      using LVSDead.stepsInitEmptyNoReleases
      by (smt (verit, ccfv_threshold) properSetup_stateOracleAddress InitUpdate.stateOracleAddressTDI LVSDead.stepsAllLVS_def Nat.add_0_right append.assoc append_Cons append_Nil burnedAmountNil noUpdate nonReleasedBurnsAmount_Nil properSetupUpdate set_ConsD stepDeathNoUpdate)
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
    next
      show "updatesNonZero ((stepDeath # stepsNoUpdate) @ [UPDATE_step] @ stepsInit)"
        by (metis append.left_neutral append_Cons stepsAllBD_def updatesNonZeroAppend(2) updatesNonZeroInit)
    qed

    show ?thesis
      using I.releasedAmountInvariantBeforeDeath notBridgeDeadContractsLastUpdate' 
      unfolding I.stepsAllLU_def
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
    using * BD'.LVSBD.releasedAmountInvariantStep reachableFrom_step.hyps
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
         nonClaimedBeforeNonCanceledDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD + 
         nonWithdrawnNonBurnedClaimedBeforeAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD +
         nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllBD"
  using InitBD.tokenDepositBalanceInvariant[of token]
  using withdrawnAmountInvariant[of token]
  using canceledAmountInvariant[of token]
  using depositedAmountEqualsClaimedPlusNonClaimed[of tokenDepositAddress token stepsAllBD bridgeAddress stepsInit]
  using releasedAmountInvariant[of token]
  using assms
  by simp

end



(* ------------------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------------------ *)
section \<open>Per user transactions\<close>
(* ------------------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------------------ *)

context HashProofVerifier
begin

\<comment> \<open>Steps labeled by "From" remove tokens from the user account on the bridge.
    Steps labled by "To" add tokens to the user account on the bridge\<close>

fun isTransferFrom where
   "isTransferFrom bridgeAddress token caller (TRANSFER address' caller' receiver' token' amount') \<longleftrightarrow>
      address' = bridgeAddress \<and> caller' = caller \<and> token' = token"
|  "isTransferFrom bridgeAddress token caller _ = False"

fun isTransferTo where
   "isTransferTo bridgeAddress token receiver (TRANSFER address' caller' receiver' token' amount') \<longleftrightarrow>
      address' = bridgeAddress \<and> receiver' = receiver \<and> token' = token"
|  "isTransferTo bridgeAddress token receiver _ = False"

definition transferredAmountFrom where
  "transferredAmountFrom bridgeAddress token caller steps = 
      sum_list (map TRANSFER_amount (filter (isTransferFrom bridgeAddress token caller) steps))" 

definition transferredAmountTo where
  "transferredAmountTo bridgeAddress token receiver steps = 
      sum_list (map TRANSFER_amount (filter (isTransferTo bridgeAddress token receiver) steps))" 

lemma transferAmountFromNil [simp]:
  shows "transferredAmountFrom bridgeAddress token caller [] = 0"
  by (simp add: transferredAmountFrom_def)

lemma transferAmountToNil [simp]:
  shows "transferredAmountTo bridgeAddress token caller [] = 0"
  by (simp add: transferredAmountTo_def)

lemma transferAmountFromConsOther [simp]:
  assumes "\<nexists> receiver amount. step = TRANSFER bridgeAddress caller receiver token amount"
  shows "transferredAmountFrom bridgeAddress token caller (step # steps) = 
         transferredAmountFrom bridgeAddress token caller steps"
  using assms
  by (cases step, auto simp add: transferredAmountFrom_def)

lemma transferAmountToConsOther [simp]:
  assumes "\<nexists> from amount. step = TRANSFER bridgeAddress from caller token amount"
  shows "transferredAmountTo bridgeAddress token caller (step # steps) = 
         transferredAmountTo bridgeAddress token caller steps"
  using assms
  by (cases step, auto simp add: transferredAmountTo_def)

lemma transferredAmountFromConsTransferOther [simp]:
  assumes "address' \<noteq> bridgeAddress \<or> caller' \<noteq> caller \<or> token' \<noteq> token"
  shows "transferredAmountFrom bridgeAddress token caller
            (TRANSFER address' caller' receiver' token' amount' # steps) =
         transferredAmountFrom bridgeAddress token caller steps"
  using assms
  by (auto simp add: transferredAmountFrom_def)

lemma transferredAmountToConsTransferOther [simp]:
  assumes "address' \<noteq> bridgeAddress \<or> receiver' \<noteq> receiver \<or> token' \<noteq> token"
  shows "transferredAmountTo bridgeAddress token receiver
            (TRANSFER address' caller' receiver' token' amount' # steps) =
         transferredAmountTo bridgeAddress token receiver steps"
  using assms
  by (auto simp add: transferredAmountTo_def)

lemma transferredAmountFromConsTransfer [simp]:
  shows "transferredAmountFrom bridgeAddress token caller
            (TRANSFER bridgeAddress caller receiver token amount # steps) =
         amount + transferredAmountFrom bridgeAddress token caller steps"
  by (auto simp add: transferredAmountFrom_def)

lemma transferredAmountToConsTransfer [simp]:
  shows "transferredAmountTo bridgeAddress token receiver
            (TRANSFER bridgeAddress caller receiver token amount # steps) =
         amount + transferredAmountTo bridgeAddress token receiver steps"
  by (auto simp add: transferredAmountTo_def)

(* ------------------------------------------------------------------------------------ *)

fun isDepositTo :: "address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> Step \<Rightarrow> bool" where
  "isDepositTo address token caller  (DEPOSIT address' caller' ID token' amount) \<longleftrightarrow> address' = address \<and> caller' = caller \<and> token' = token"
| "isDepositTo address token caller  _ = False"

lemma isDepositToDEPOSIT [simp]:
  assumes "isDepositTo tokenDepositAddress token caller step"
  shows "step = DEPOSIT tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step)"
  using assms
  by (cases step, auto)

\<comment> \<open>All deposits of the given token on the given address\<close>
definition depositsTo where
  "depositsTo address token caller steps = filter (isDepositTo address token caller) steps"

lemma depositsToDEPOSIT: 
  assumes "step \<in> set (depositsTo tokenDepositAddress token caller stepsInit)"
  obtains ID amount where "step = DEPOSIT tokenDepositAddress caller ID token amount"
  using assms
  unfolding depositsTo_def
  by (metis filter_set isDepositToDEPOSIT member_filter)

lemma depositsToNil [simp]:
  shows "depositsTo address token caller [] = []"
  unfolding depositsTo_def
  by simp

lemma depositsToConsOther [simp]:
  assumes "\<nexists> ID amount. step = DEPOSIT address caller ID token amount"
  shows "depositsTo address token caller (step # steps) = depositsTo address token caller steps"
  using assms
  unfolding depositsTo_def
  by (cases step, auto)

lemma depositsToConsDeposit [simp]:
  shows "depositsTo tokenDepositAddress token caller
           (DEPOSIT tokenDepositAddress caller ID token amount # steps) = 
         DEPOSIT tokenDepositAddress caller ID token amount # depositsTo tokenDepositAddress token caller steps"
  by (simp add: depositsTo_def)

lemma depositsToSubsetDeposits:
  shows "set (depositsTo tokenDepositAddress token caller steps) \<subseteq> 
         set (deposits tokenDepositAddress token steps)"
  unfolding deposits_def depositsTo_def
  by (metis filter_set isDeposit.simps(1) isDepositToDEPOSIT member_filter subsetI)

end

context StrongHashProofVerifier
begin

lemma distinctDepositsTo:
  assumes "reachableFrom contracts contracts' steps"
  shows "distinct (depositsTo tokenDepositAddress token caller steps)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain ID amount steps1 steps2 steps3 where 
    "depositsTo tokenDepositAddress token caller steps = steps1 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2 @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps3"
    by (metis append_Cons depositsToDEPOSIT not_distinct_decomp in_set_conv_decomp)
  then obtain steps1' steps2' steps3' where "steps = steps1' @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps2' @ [DEPOSIT tokenDepositAddress caller ID token amount] @ steps3'"
    unfolding depositsTo_def
    by (meson twiceInFilter)
  then show False
    using DEPOSITNoDouble[OF assms]
    by blast
qed

lemma distinctDepositsToIDs:
  assumes "reachableFrom contracts contracts' steps"
  shows "distinct (map DEPOSIT_id (depositsTo tokenDepositAddress token caller steps))"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  then obtain ID amount amount' where
    "DEPOSIT tokenDepositAddress caller ID token amount \<in> set (depositsTo tokenDepositAddress token caller steps)"
    "DEPOSIT tokenDepositAddress caller ID token amount' \<in> set (depositsTo tokenDepositAddress token caller steps)"
    "DEPOSIT tokenDepositAddress caller ID token amount \<noteq> DEPOSIT tokenDepositAddress caller ID token amount'"
    using distinctDeposits[OF assms]
    by (subst (asm) distinct_map, meson assms depositsToSubsetDeposits distinctDepositIDs distinctDepositsTo distinct_map inj_on_subset)
  then show False
    by (metis DEPOSITNoDoubleCTA depositsToSubsetDeposits depositsSubsetSteps in_mono assms)
qed

end

context HashProofVerifier
begin

\<comment> \<open>Total amount of the given token deposited on the given address\<close>
definition depositedAmountTo where
  "depositedAmountTo tokenDepositAddress token caller steps = 
        sum_list (map DEPOSIT_amount (depositsTo tokenDepositAddress token caller steps))"

lemma depositedAmountToNil [simp]:
  "depositedAmountTo address token caller [] = 0"
  unfolding depositedAmountTo_def
  by simp

lemma depositedAmountToConsOther [simp]:
  assumes "\<nexists> ID amount. step = DEPOSIT address caller ID token amount"
  shows "depositedAmountTo address token caller (step # steps) = depositedAmountTo address token caller steps"
  using assms
  unfolding depositedAmountTo_def
  by simp

lemma depositedAmountToConsDeposit [simp]:
  shows "depositedAmountTo tokenDepositAddress token caller
           (DEPOSIT tokenDepositAddress caller ID token amount # steps) = 
         depositedAmountTo tokenDepositAddress token caller steps + amount"
  unfolding depositedAmountTo_def depositsTo_def
  by simp

(* ------------------------------------------------------------------------------------ *)

fun isReleaseFrom where
  "isReleaseFrom address token caller (RELEASE address' caller' ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token \<and> caller' = caller"
| "isReleaseFrom address token caller _ = False"

definition releasesFrom where
  "releasesFrom tokenDepositAddress token caller steps = 
   filter (isReleaseFrom tokenDepositAddress token caller) steps"

lemma releasesFromNil [simp]:
  shows "releasesFrom tokenDepositAddress token caller [] = []"
  unfolding releasesFrom_def
  by simp

lemma releasesFromConsOther [simp]:
  assumes "\<nexists> ID amount proof. step = RELEASE tokenDepositAddress caller ID token amount proof"
  shows "releasesFrom tokenDepositAddress token caller (step # steps) = releasesFrom tokenDepositAddress token caller steps"
  using assms
  unfolding releasesFrom_def
  by (cases step, auto)

definition releasedAmountFrom where
  "releasedAmountFrom tokenDepositAddress token caller steps = 
   sum_list (map RELEASE_amount (releasesFrom tokenDepositAddress token caller steps))"

lemma releasedAmountFromNil [simp]:
  shows "releasedAmountFrom tokenDepositAddress token caller [] = 0"
  unfolding releasedAmountFrom_def
  by simp

lemma releasedAmountFromConsOther [simp]:
  assumes "\<nexists> ID amount proof. step = RELEASE tokenDepositAddress caller ID token amount proof"
  shows "releasedAmountFrom tokenDepositAddress token caller (step # steps) = releasedAmountFrom tokenDepositAddress token caller steps"
  using assms
  unfolding releasedAmountFrom_def
  by simp

lemma releasedAmountFromConsReleaseOther [simp]:
  assumes "address' \<noteq> tokenDepositAddress \<or> caller' \<noteq> caller \<or> token' \<noteq> token"
  shows "releasedAmountFrom tokenDepositAddress token caller (RELEASE address' caller' ID' token' amount' proof' # steps) = 
         releasedAmountFrom tokenDepositAddress token caller steps"
  using assms
  unfolding releasedAmountFrom_def
  by simp

lemma releasedAmountFromConsRelease [simp]:
  shows "releasedAmountFrom tokenDepositAddress token caller (RELEASE tokenDepositAddress caller ID token amount proof # steps) = 
         releasedAmountFrom tokenDepositAddress token caller steps + amount"
  unfolding releasedAmountFrom_def releasesFrom_def
  by simp

(* ------------------------------------------------------------------------------------ *)

fun isCancelFrom where
  "isCancelFrom address token caller (CANCEL_WD address' caller' ID token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token \<and> caller' = caller"
| "isCancelFrom address token caller _ = False"

definition cancelsFrom where
  "cancelsFrom tokenDepositAddress token caller steps = 
   filter (isCancelFrom tokenDepositAddress token caller) steps"

lemma cancelsFromNil [simp]:
  shows "cancelsFrom tokenDepositAddress token caller [] = []"
  unfolding cancelsFrom_def
  by simp

lemma cancelsFromConsOther [simp]:
  assumes "\<nexists> ID amount proof. step = CANCEL_WD tokenDepositAddress caller ID token amount proof"
  shows "cancelsFrom tokenDepositAddress token caller (step # steps) = cancelsFrom tokenDepositAddress token caller steps"
  using assms
  unfolding cancelsFrom_def
  by (cases step, auto)

definition canceledAmountFrom where
  "canceledAmountFrom tokenDepositAddress token caller steps = 
   sum_list (map CANCEL_amount (cancelsFrom tokenDepositAddress token caller steps))"

lemma canceledAmountFromNil [simp]:
  shows "canceledAmountFrom tokenDepositAddress token caller [] = 0"
  unfolding canceledAmountFrom_def
  by simp

lemma canceledAmountFromConsOther [simp]:
  assumes "\<nexists> ID amount proof. step = CANCEL_WD tokenDepositAddress caller ID token amount proof"
  shows "canceledAmountFrom tokenDepositAddress token caller (step # steps) = canceledAmountFrom tokenDepositAddress token caller steps"
  using assms
  unfolding canceledAmountFrom_def
  by simp

lemma canceledAmountFromConsCancel [simp]:
  shows "canceledAmountFrom tokenDepositAddress token caller (CANCEL_WD tokenDepositAddress caller ID token amount proof # steps) = canceledAmountFrom tokenDepositAddress token caller steps + amount"
  unfolding canceledAmountFrom_def cancelsFrom_def
  by simp

lemma canceledAmountFromConsCancelOther [simp]:
  assumes "address' \<noteq> tokenDepositAddress \<or> token' \<noteq> token \<or> caller' \<noteq> caller"
  shows "canceledAmountFrom tokenDepositAddress token caller (CANCEL_WD address' caller' ID' token' amount' proof' # steps) = canceledAmountFrom tokenDepositAddress token caller steps"
  using assms
  unfolding canceledAmountFrom_def cancelsFrom_def
  by auto

(* ------------------------------------------------------------------------------------ *)

fun isWithdrawFrom where
  "isWithdrawFrom address token caller (WITHDRAW_WD address' caller' token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token \<and> caller' = caller"
| "isWithdrawFrom address token caller _ = False"

definition withdrawalsFrom where
  "withdrawalsFrom tokenDepositAddress token caller steps = filter (isWithdrawFrom tokenDepositAddress token caller) steps"

lemma withdrawalsFromNil [simp]:
  shows "withdrawalsFrom tokenDepositAddress token caller [] = []"
  unfolding withdrawalsFrom_def
  by simp

lemma withdrawalsFromConsOther [simp]:
  assumes "\<nexists> amount' proof'. step = WITHDRAW_WD tokenDepositAddress caller token amount' proof'"
  shows "withdrawalsFrom tokenDepositAddress token caller (step # steps) = 
         withdrawalsFrom tokenDepositAddress token caller steps"
  using assms
  unfolding withdrawalsFrom_def
  by (cases step, auto)

definition withdrawnAmountFrom where
  "withdrawnAmountFrom tokenDepositAddress token caller steps = 
   sum_list (map WITHDRAW_WD_amount (withdrawalsFrom tokenDepositAddress token caller steps))"

lemma withdrawnAmountFromNil [simp]:
  shows "withdrawnAmountFrom tokenDepositAddress token caller [] = 0"
  unfolding withdrawnAmountFrom_def
  by simp

lemma withdrawnAmountFromConsOther [simp]:
  assumes "\<nexists> amount' proof'. step = WITHDRAW_WD tokenDepositAddress caller token amount' proof'"
  shows "withdrawnAmountFrom tokenDepositAddress token caller (step # steps) = 
         withdrawnAmountFrom tokenDepositAddress token caller steps"
  using assms
  unfolding withdrawnAmountFrom_def
  by simp

lemma withdrawnAmountFromConsWithdraw [simp]:
  shows "withdrawnAmountFrom tokenDepositAddress token caller (WITHDRAW_WD tokenDepositAddress caller token amount' proof' # steps) = 
         withdrawnAmountFrom tokenDepositAddress token caller steps + amount'"
  by (auto simp add: withdrawnAmountFrom_def withdrawalsFrom_def)

(* ------------------------------------------------------------------------------------ *)

definition paidBackAmountFrom where
  "paidBackAmountFrom tokenDepositAddress token caller steps = 
      releasedAmountFrom tokenDepositAddress token caller steps + 
      canceledAmountFrom tokenDepositAddress token caller steps +
      withdrawnAmountFrom tokenDepositAddress token caller steps" 

(* ------------------------------------------------------------------------------------ *)

definition nonClaimedBeforeNonCanceledDepositsTo where
  "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore steps = 
    filter (\<lambda>step. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore \<and>
                   \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) steps)
           (depositsTo tokenDepositAddress token caller steps)"

lemma nonClaimedBeforeNonCanceledDepositsToNil [simp]:
  shows "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore [] = []"
  unfolding nonClaimedBeforeNonCanceledDepositsTo_def
  by simp

lemma nonClaimedBeforeNonCanceledDepositsToConsOther [simp]:
  assumes "\<nexists> ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> ID amount proof. step = CLAIM bridgeAddress caller ID token amount proof"
  assumes "\<nexists> ID caller amount proof. step = CANCEL_WD tokenDepositAddress caller ID token amount proof"
  shows "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore (step # steps) =
         nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeNonCanceledDepositsTo_def
  by (cases step, auto simp add: isCanceledID_def)
  
definition nonClaimedBeforeNonCanceledDepositsAmountTo where
  "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore steps = 
   sum_list (map DEPOSIT_amount (nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore steps))" 

lemma nonClaimedBeforeNonCanceledDepositsAmountToNil [simp]:
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore [] = 0"
  unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def
  by simp

lemma nonClaimedBeforeNonCanceledDepositsAmountToConsOther [simp]:
  assumes "\<nexists> ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> ID amount proof. step = CLAIM bridgeAddress caller ID token amount proof"
  assumes "\<nexists> ID caller amount proof. step = CANCEL_WD tokenDepositAddress caller ID token amount proof"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore (step # steps) =
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def
  by simp

lemma nonClaimedBeforeNonCanceledDepositsToConsOtherDeposit [simp]:
  assumes "\<nexists> ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> ID caller amount proof. step = CANCEL_WD tokenDepositAddress caller ID token amount proof"
  shows "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore (step # steps) =
         nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def nonClaimedBeforeNonCanceledDepositsTo_def depositsTo_def isCanceledID_def
  by (cases step, auto)

lemma nonClaimedBeforeNonCanceledDepositsAmountToConsOtherDeposit [simp]:
  assumes "\<nexists> ID amount. step = DEPOSIT tokenDepositAddress caller ID token amount"
  assumes "\<nexists> ID caller amount proof. step = CANCEL_WD tokenDepositAddress caller ID token amount proof"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore (step # steps) =
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def
  by simp

lemma nonClaimedBeforeNonCanceledDepositsToBeforeConsClaim [simp]:
  assumes "\<nexists> ID amount proof caller. step = CLAIM bridgeAddress caller ID token amount proof"
  shows "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller (step # stepsBefore) steps =
         nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeNonCanceledDepositsTo_def
  by (cases step, auto simp add: isClaimedID_def)

lemma nonClaimedBeforeNonCanceledDepositsAmountToBeforeConsOther [simp]:
  assumes "\<nexists> ID amount proof caller. step = CLAIM bridgeAddress caller ID token amount proof"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller (step # stepsBefore) steps =
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore steps"
  using assms
  unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def
  by auto

end

context InitFirstUpdate
begin

lemma nonClaimedBeforeNonCanceledDepositsAmountToConsDeposit [simp]:
  assumes "stepsInit = steps @ stepsBefore"
  assumes "reachableFrom contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore
           (DEPOSIT tokenDepositAddress caller ID token amount # stepsInit) = 
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore stepsInit + amount"
proof-
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"
  have "\<not>  isClaimedID bridgeAddress token ID stepsBefore"
    using noClaimBeforeDeposit[OF _ assms(2)] assms(1)
    by (auto simp add: isClaimedID_def)
  moreover
  have " \<not> isCanceledID tokenDepositAddress token ID
         (DEPOSIT tokenDepositAddress caller ID token amount # stepsInit)"
    using noCancelBeforeDeposit
    by (metis Step.simps(19) assms(2) isCanceledID_def reachableFromInitI set_ConsD)
  ultimately
  have "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore
           (?DEPOSIT_step # stepsInit) = 
        ?DEPOSIT_step # nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore
           stepsInit"
    unfolding nonClaimedBeforeNonCanceledDepositsTo_def
    by (auto simp add: isCanceledID_def)
  then show ?thesis
    unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def
    by simp
qed

lemma nonClaimedBeforeNonCanceledDepositsAmountToConsDeposit' [simp]:
  assumes "reachableFrom contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit
           (DEPOSIT tokenDepositAddress caller ID token amount # stepsInit) = 
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsInit + amount"
  using assms 
  by force

end

context InitUpdateBridgeNotDeadLastValidState
begin
lemma nonClaimedBeforeNonCanceledDepositsAmountToConsCancel [simp]:
  assumes "reachableFrom contractsLVS contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller
           stepsInit (CANCEL_WD tokenDepositAddress caller ID token amount proof # stepsAllLVS) + amount = 
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller
           stepsInit stepsAllLVS"
proof-
  let ?CANCEL_step = "CANCEL_WD tokenDepositAddress caller ID token amount proof"
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"
  let ?deposits = "depositsTo tokenDepositAddress token caller stepsAllLVS"
  have deposits: "depositsTo tokenDepositAddress token caller (?CANCEL_step # stepsAllLVS) = ?deposits"
    by simp

  have "?DEPOSIT_step \<in> set stepsAllLVS"
    using InitLVS.cancelDepositOnlyAfterDeposit reachableFromSingleton[OF assms]
    by (metis executeStep.simps(7) senderMessage)
  then have "?DEPOSIT_step \<in> set ?deposits"
    by (auto simp add: depositsTo_def)

  have reach: "reachableFrom contractsInit contractsCancel (?CANCEL_step # stepsAllLVS)"
    using assms reachableFromInitLVS reachableFromTrans
    by fastforce

  let ?P = "\<lambda> step steps.
               \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
               \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) steps"

  have "\<exists> steps1 steps2. nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit 
                           (?CANCEL_step # stepsAllLVS) = steps1 @ steps2 \<and> 
                         nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit 
                           stepsAllLVS = steps1 @ [?DEPOSIT_step] @ steps2"
    unfolding nonClaimedBeforeNonCanceledDepositsTo_def
  proof (subst deposits, rule filter'')
    show "distinct (depositsTo tokenDepositAddress token caller stepsAllLVS)"
      using distinctDepositsTo[OF reachableFromInitLVS] assms 
      by auto
  next
    show "?DEPOSIT_step \<in> set ?deposits"
      by fact
  next
    show "?P ?DEPOSIT_step stepsAllLVS"
      using CANCELNoDoubleCons[OF reach] assms(1)
      using cancelDepositWhileDeadNoClaim
      using reachableFromSingleton[OF assms]
      unfolding isCanceledID_def isClaimedID_def
      by (metis DEPOSIT_id.simps executeStep.simps(7))
  next
    show "\<forall> step \<in> set ?deposits. ?P step stepsAllLVS \<and> step \<noteq> ?DEPOSIT_step \<longleftrightarrow> ?P step (?CANCEL_step # stepsAllLVS)"
    proof safe
      fix step
      assume "step \<in> set ?deposits" "step \<noteq> DEPOSIT tokenDepositAddress caller ID token amount"
      then have "DEPOSIT_id step \<noteq> ID"
        using \<open>?DEPOSIT_step \<in> set ?deposits\<close> distinctDepositsToIDs[OF reachableFromInitLVS]
        by (metis DEPOSIT_id.simps distinct_map inj_on_def)
      assume "\<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsAllLVS"
             "isCanceledID tokenDepositAddress token (DEPOSIT_id step) (?CANCEL_step # stepsAllLVS)"
      then show False
        using \<open>DEPOSIT_id step \<noteq> ID\<close>
        unfolding isCanceledID_def
        by auto
    qed (auto simp add: isCanceledID_def)
  qed

  then show ?thesis
    unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def
    by auto
qed

end

context Init
begin

lemma nonClaimedBeforeNonCanceledDepositsAmountToConsCancelOther [simp]:
  assumes "reachableFrom contractsI contractsCancel [CANCEL_WD address' caller' ID' token' amount' proof']"
  assumes "stepsInit = steps @ stepsBefore"
  assumes "address' \<noteq> tokenDepositAddress \<or> token' \<noteq> token \<or> caller' \<noteq> caller"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller
         stepsBefore (CANCEL_WD address' caller' ID' token' amount' proof' # stepsInit) = 
        nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller
         stepsBefore stepsInit"
proof-
  let ?CANCEL_step = "CANCEL_WD address' caller' ID' token' amount' proof'"
  let ?deposits = "depositsTo tokenDepositAddress token caller stepsInit"

  have *: "depositsTo tokenDepositAddress token caller (?CANCEL_step # stepsInit) = ?deposits"
    by simp

  let ?P = "\<lambda> step steps. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsBefore \<and>
                          \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) steps"
  have "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore
         (?CANCEL_step # stepsInit) = 
       nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsBefore
         stepsInit"
    unfolding nonClaimedBeforeNonCanceledDepositsTo_def
  proof (subst *, rule filter_cong)
    fix step
    assume "step \<in> set ?deposits"
    show "?P step (?CANCEL_step # stepsInit) \<longleftrightarrow> ?P step stepsInit"
    proof safe
      assume "isCanceledID tokenDepositAddress token (DEPOSIT_id step) (?CANCEL_step # stepsInit)"
             "\<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsInit"
      then show False
        using assms \<open>step \<in> set ?deposits\<close> 
        by (smt (verit) "*" Cons_eq_append_conv DEPOSIT_id.simps Step.simps(7) depositsSubsetSteps depositsToDEPOSIT depositsToSubsetDeposits in_mono isCanceledID_def onlyDepositorCanCancelSteps(1) reachableFrom.simps reachableFromInitI reachableFromTrans set_ConsD)
    qed (auto simp add: isCanceledID_def)
  qed auto
  then show ?thesis
    unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def
    by simp
qed

end

context InitFirstUpdate
begin

lemma nonClaimedBeforeNonCanceledDepositsAmountToBeforeConsClaimOther [simp]:
  assumes "address' \<noteq> bridgeAddress \<or> token' \<noteq> token \<or> caller' \<noteq> caller"
  assumes "reachableFrom contractsI contractsClaim [CLAIM address' caller' ID token' amount proof]"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller
         (CLAIM address' caller' ID token' amount proof # stepsInit) stepsInit = 
        nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller
         stepsInit stepsInit"
proof-
  let ?CLAIM_step = "CLAIM address' caller' ID token' amount proof"
  let ?deposits = "depositsTo tokenDepositAddress token caller stepsInit"

  let ?P = "\<lambda> step steps'. \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) steps' \<and>
                          \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsInit"
  have "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller
         (?CLAIM_step # stepsInit) stepsInit = 
       nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit
         stepsInit"
    unfolding nonClaimedBeforeNonCanceledDepositsTo_def
  proof (rule filter_cong)
    fix step
    assume "step \<in> set ?deposits"
    then obtain amount' ID' where step: "step = DEPOSIT tokenDepositAddress caller ID' token amount'"
      using depositsToDEPOSIT by blast

    interpret I: InitFirstUpdate where contractsI=contractsClaim and stepsInit="?CLAIM_step # stepsInit"
    proof
      show "reachableFrom contractsInit contractsClaim (CLAIM address' caller' ID token' amount proof # stepsInit)"
        using reachableFromInitI assms
        by (meson reachableFrom_step reachableFromSingleton)
    next
      show "updatesNonZero (CLAIM address' caller' ID token' amount proof # stepsInit)"
        by (metis Step.simps(29) set_ConsD updatesNonZeroInit updatesNonZero_def)
    qed (auto simp add: firstUpdate)

    show "?P step (?CLAIM_step # stepsInit) \<longleftrightarrow> ?P step stepsInit"
    proof safe
      assume *: "isClaimedID bridgeAddress token (DEPOSIT_id step) (?CLAIM_step # stepsInit)"
                 "\<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit"
      show False
      proof (cases "address' \<noteq> bridgeAddress \<or> token' \<noteq> token")
        case True
        then show ?thesis
          using *
          by (simp add: isClaimedID_def)
      next
        case False
        then have "caller' \<noteq> caller"
          using assms
          by simp

        moreover

        have "ID' = ID"
          using *
          by (simp add: isClaimedID_def step)

        then have "caller' = caller"
          using I.onlyDepositorCanClaimSteps(1)[of caller' ID token' amount "proof" caller token amount'] step False \<open>step \<in> set ?deposits\<close>
          by (auto simp add: depositsTo_def)

        ultimately 
        show False
          by simp
      qed
    qed (simp add: isClaimedID_def)
  qed auto
  then show ?thesis
    unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def
    by auto
qed

end

context InitFirstUpdate
begin

lemma nonClaimedBeforeNonCanceledDepositsAmountToBeforeConsClaim [simp]:
  assumes "reachableFrom contractsI contractsClaim [CLAIM bridgeAddress caller ID token amount proof]"
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller
         (CLAIM bridgeAddress caller ID token amount proof # stepsInit) stepsInit + amount = 
        nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller
         stepsInit stepsInit" 
proof-
  let ?CLAIM_step = "CLAIM bridgeAddress caller ID token amount proof"
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"
  let ?deposits = "depositsTo tokenDepositAddress token caller stepsInit"

  have "callClaim contractsI bridgeAddress (message caller amount) ID token amount proof = (Success, contractsClaim)"
    using reachableFromSingleton[OF assms(1)]
    unfolding executeStep.simps
    by auto
  then have "?DEPOSIT_step \<in> set stepsInit"
    using depositBeforeClaim
    by fastforce
  then have "?DEPOSIT_step \<in> set ?deposits"
    by (auto simp add: depositsTo_def)


  let ?P = "\<lambda> step steps. 
              \<not> isClaimedID bridgeAddress token (DEPOSIT_id step) steps \<and>
              \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsInit"

  have "\<exists> steps1 steps2. 
          nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller
            (?CLAIM_step # stepsInit) stepsInit = steps1 @ steps2 \<and>
          nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller
             stepsInit stepsInit = steps1 @ [?DEPOSIT_step] @ steps2"
    unfolding nonClaimedBeforeNonCanceledDepositsTo_def
  proof (rule filter'')
    show "distinct (depositsTo tokenDepositAddress token caller stepsInit)"
      using distinctDepositsTo reachableFromInitI by blast
  next
    show "?DEPOSIT_step \<in> set ?deposits"
      by fact
  next
    show "?P ?DEPOSIT_step stepsInit"
    proof-
      have "\<not> isClaimedID bridgeAddress token ID stepsInit"
        using assms(1)
        by (metis (full_types) CLAIMNoDoubleCons Cons_eq_append_conv eq_Nil_appendI isClaimedID_def reachableFromInitI reachableFromTrans)
      moreover
      have "\<not> isCanceledID tokenDepositAddress token ID stepsInit"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain caller' amount' proof' where "CANCEL_WD tokenDepositAddress caller' ID token amount' proof' \<in> set stepsInit"
          unfolding isCanceledID_def
          by auto
        then have "bridgeDead contractsI tokenDepositAddress"
          using reachableFromInitI reachableFromNotBridgeDeadNoCancel 
          by blast
        then show False
          using assms(2)
          by simp
      qed
      ultimately
      show ?thesis
        by simp
    qed
  next
    show "\<forall> step \<in> set ?deposits. (?P step stepsInit) \<and> step \<noteq> ?DEPOSIT_step \<longleftrightarrow> ?P step (?CLAIM_step # stepsInit)"
    proof safe
      fix step
      assume "step \<in> set ?deposits" "step \<noteq> ?DEPOSIT_step"
      then have "DEPOSIT_id step \<noteq> ID"
        using \<open>?DEPOSIT_step \<in> set ?deposits\<close> 
        by (metis DEPOSIT_id.simps distinctDepositsToIDs distinct_map inj_on_def reachableFromInitI)
      assume "\<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit"
             "isClaimedID bridgeAddress token (DEPOSIT_id step) (?CLAIM_step # stepsInit)"
      then show False
        using \<open>DEPOSIT_id step \<noteq> ID\<close>
        by (auto simp add: isClaimedID_def)
    qed (auto simp add: isClaimedID_def)
  qed
  then show ?thesis
    unfolding nonClaimedBeforeNonCanceledDepositsAmountTo_def
    by auto
qed

end


(* ------------------------------------------------------------------------------------ *)

context HashProofVerifier
begin

fun isBurnTo where
  "isBurnTo address token caller (BURN address' caller' ID token' amount) \<longleftrightarrow> address' = address \<and> token' = token \<and> caller' = caller"
| "isBurnTo address token caller _ = False"

\<comment> \<open>All burns of a given token on the given bridge\<close>
definition burnsTo where 
  "burnsTo address token caller steps = 
   filter (isBurnTo address token caller) steps"

lemma isBurnToStep [simp]:
  assumes "isBurnTo bridgeAddress token caller step"
  shows "step = BURN bridgeAddress caller (BURN_id step) token (BURN_amount step)"
  using assms
  by (cases step, auto)

lemma burnsToBURN:
  assumes "step \<in> set (burnsTo address token caller steps)"
  obtains ID amount where "step = BURN address caller ID token amount"
  by (smt (verit, best) assms burnsTo_def isBurnTo.elims(2) mem_Collect_eq set_filter)

lemma burnsToNil [simp]:
  shows "burnsTo bridgeAddress token caller [] = []"
  unfolding burnsTo_def
  by simp

lemma burnsToConsOther [simp]:
  assumes "\<nexists> ID amount proof. step = BURN bridgeAddress caller ID token amount"
  shows "burnsTo bridgeAddress token caller (step # steps) = burnsTo bridgeAddress token caller steps"
  using assms
  unfolding burnsTo_def
  by (cases step, auto)

end

context StrongHashProofVerifier
begin

lemma distinctBurnsTo:
  assumes "reachableFrom contracts contracts' steps"
  shows "distinct (burnsTo bridgeAddress token caller steps)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain ID amount steps1 steps2 steps3 where 
    "burnsTo bridgeAddress token caller steps = steps1 @ [BURN bridgeAddress caller ID token amount] @ steps2 @ [BURN bridgeAddress caller ID token amount] @ steps3"
    by (metis append_Cons burnsToBURN not_distinct_decomp in_set_conv_decomp)
  then obtain steps1' steps2' steps3' where "steps = steps1' @ [BURN bridgeAddress caller ID token amount] @ steps2' @ [BURN bridgeAddress caller ID token amount] @ steps3'"
    unfolding burnsTo_def
    by (meson twiceInFilter)
  then show False
    using BURNNoDouble assms
    by blast
qed

lemma distinctBurnsToIDs:
  assumes "reachableFrom contracts contracts' steps"
  shows "distinct (map BURN_id (burnsTo bridgeAddress token caller steps))"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  then obtain ID amount amount' where
    "BURN bridgeAddress caller ID token amount \<in> set (burnsTo bridgeAddress token caller steps)"
    "BURN bridgeAddress caller ID token amount' \<in> set (burnsTo bridgeAddress token caller steps)"
    "BURN bridgeAddress caller ID token amount \<noteq> BURN bridgeAddress caller ID token amount'"
    using distinctBurns[OF assms] distinctBurnsTo[OF assms]
    by (subst (asm) distinct_map, smt (verit, best) BURN_id.simps burnsToBURN inj_onI)
  then show False
    using BURNNoDoubleCTA[OF assms]
    by (auto simp add: burnsTo_def)
qed

end


context HashProofVerifier
begin

definition nonReleasedBurnsTo where
 "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsBefore steps =
   filter (\<lambda>step. \<not> isReleasedID tokenDepositAddress token (BURN_id step) steps)
    (burnsTo bridgeAddress token caller stepsBefore)"

lemma nonReleasedBurnsToNil [simp]:
  shows "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller [] steps = []"
  unfolding nonReleasedBurnsTo_def
  by simp

lemma nonReleasedBurnsToConsNoBurn [simp]:
  assumes "\<nexists> ID amount. step = BURN bridgeAddress caller ID token amount"
  shows "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller (step # steps) steps'= 
         nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller steps steps'"
  using assms
  unfolding nonReleasedBurnsTo_def
  by (cases step, auto)

lemma nonReleasedBurnsToConsNoRelease [simp]:
  assumes "\<nexists> ID caller amount proof. step = RELEASE tokenDepositAddress caller ID token amount proof"
  shows "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsBefore (step # steps)= 
         nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsBefore steps"
proof (cases step)
  case (RELEASE address' caller' ID' token' amount' proof')
  then show ?thesis
    using assms
    by (auto simp add: nonReleasedBurnsTo_def isReleasedID_def)
qed (auto simp add: assms isReleasedID_def nonReleasedBurnsTo_def)
  

definition nonReleasedBurnedAmountTo where
 "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore steps =
  sum_list (map BURN_amount (nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsBefore steps))"

lemma nonReleasedBurnedAmountToNil [simp]:
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller [] steps = 0"
  unfolding nonReleasedBurnedAmountTo_def
  by simp

lemma nonReleasedBurnedAmountToConsNoBurn [simp]:
  assumes "\<nexists> ID amount. step = BURN bridgeAddress caller ID token amount"
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller (step # steps) = 
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller steps"
  using assms
  unfolding nonReleasedBurnedAmountTo_def
  by simp

lemma nonReleasedBurnedAmountToConsNoRelease [simp]:
  assumes "\<nexists> ID amount caller proof. step = RELEASE tokenDepositAddress caller ID token amount proof"
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore (step # steps) = 
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore steps"
  using assms
  unfolding nonReleasedBurnedAmountTo_def
  by simp

end

context InitUpdateBridgeNotDeadLastValidState
begin

lemma nonReleasedBurnedAmountToConsRelease [simp]:
  assumes "reachableFrom contractsLVS contractsRelease [RELEASE tokenDepositAddress caller ID token amount proof]"
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit
           (RELEASE tokenDepositAddress caller ID token amount proof # stepsAllLVS) + amount =
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit
           stepsAllLVS"
proof-
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller ID token amount proof"
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  let ?burns = "burnsTo bridgeAddress token caller stepsInit"

  have "?BURN_step \<in> set stepsInit"
    using burnBeforeRelease[where msg="message caller 0"] reachableFromSingleton[OF assms]
    by (metis executeStep.simps(4) senderMessage)
  then have "?BURN_step \<in> set ?burns"
    unfolding burnsTo_def
    by simp

  let ?P = "\<lambda> step steps. \<not> isReleasedID tokenDepositAddress token (BURN_id step) steps"
  have "\<exists> steps1 steps2. nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
           (?RELEASE_step # stepsAllLVS) = steps1 @ steps2 \<and>
         nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
           stepsAllLVS = steps1 @ [?BURN_step] @ steps2"
    unfolding nonReleasedBurnsTo_def 
  proof (rule filter'')
    show "distinct ?burns"
      using distinctBurnsTo reachableFromInitI by blast
  next
    show "?BURN_step \<in> set ?burns"
      by fact
  next
    show "?P ?BURN_step stepsAllLVS"
      using RELEASENoDoubleCons[of contractsInit contractsRelease] reachableFromInitLVS assms(1) reachableFromTrans
      unfolding isReleasedID_def
      by (smt (verit) BURN_id.simps reachableFromSingleton reachableFrom_step)
  next
    show "\<forall> step \<in> set ?burns. ?P step stepsAllLVS \<and> step \<noteq> ?BURN_step \<longleftrightarrow> ?P step (?RELEASE_step # stepsAllLVS)"
    proof safe
      fix step
      assume "step \<in> set ?burns" "step \<noteq> ?BURN_step"
      then have "BURN_id step \<noteq> ID"
        using \<open>?BURN_step \<in> set ?burns\<close>
        by (metis BURN_id.simps distinctBurnsToIDs distinct_map inj_on_def reachableFromInitI)
      assume "\<not> isReleasedID tokenDepositAddress token (BURN_id step) stepsAllLVS"
             "isReleasedID tokenDepositAddress token (BURN_id step) (?RELEASE_step  # stepsAllLVS)"
      then show False
        using  \<open>BURN_id step \<noteq> ID\<close>
        unfolding isReleasedID_def
        by auto
    qed (auto simp add: isReleasedID_def)
  qed
  then show ?thesis
    unfolding nonReleasedBurnedAmountTo_def
    by auto
qed

end

context InitFirstUpdate
begin

lemma nonReleasedBurnedAmountToConsReleaseOther [simp]:
  assumes "caller' \<noteq> caller"
  assumes "stepsInit = steps @ stepsBefore"
  assumes "reachableFrom contractsI contractsRelease [RELEASE tokenDepositAddress caller' ID' token amount' proof']"
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore
           (RELEASE tokenDepositAddress caller' ID' token amount' proof' # stepsInit) =
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore stepsInit"
proof-
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller' ID' token amount' proof'"
  let ?BURN_step = "BURN bridgeAddress caller' ID' token amount'"
  let ?burns = "burnsTo bridgeAddress token caller stepsBefore"

  have "?BURN_step \<in> set stepsInit"
    using assms(3)
    by (metis reachableFromSingleton burnBeforeRelease executeStep.simps(4) senderMessage)

  have "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsBefore
           (?RELEASE_step # stepsInit) =
        nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsBefore
            stepsInit"
    unfolding nonReleasedBurnsTo_def
  proof (rule filter_cong)
    fix step 
    assume "step \<in> set ?burns"
    show "(\<not> isReleasedID tokenDepositAddress token (BURN_id step) (?RELEASE_step # stepsInit)) \<longleftrightarrow>
          (\<not> isReleasedID tokenDepositAddress token (BURN_id step) stepsInit)"
    proof safe
      assume "\<not> isReleasedID tokenDepositAddress token (BURN_id step) stepsInit"
             "isReleasedID tokenDepositAddress token (BURN_id step) (?RELEASE_step # stepsInit)"
      then have "BURN_id step = ID'"
        by (simp add: isReleasedID_def)
      then have "caller = caller'"
        using BURNNoDoubleCTA[OF reachableFromInitI] \<open>step \<in> set ?burns\<close> assms(2) \<open>?BURN_step \<in> set stepsInit\<close>
        by (metis BURN_id.simps UnCI burnsToBURN burnsTo_def filter_is_subset in_mono set_append)
      then show False
        using \<open>caller' \<noteq> caller\<close>
        by simp
    qed (simp add: isReleasedID_def)
  qed auto
  then show ?thesis
    unfolding nonReleasedBurnedAmountTo_def
    by simp
qed

end

(* ------------------------------------------------------------------------------------ *)
context HashProofVerifier
begin

definition nonWithdrawnBalanceBefore where
  "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsBefore contracts = 
       (let withdrawHash = hash2 caller token 
         in if \<not> getTokenWithdrawn (the (tokenDepositState contracts tokenDepositAddress)) withdrawHash then
               accountBalance contractsBefore (mintedTokenB contractsBefore bridgeAddress token) caller
            else 0)"

end

context Init
begin

lemma nonWithdrawnBalanceBeforeBridgeNotDead [simp]:
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsBefore contractsI = 
         accountBalance contractsBefore (mintedTokenB contractsBefore bridgeAddress token) caller"
  using getTokenWithdrawnNotBridgeDead[OF assms]
  unfolding nonWithdrawnBalanceBefore_def Let_def
  by simp

end

context StrongHashProofVerifier
begin

lemma executeStepNonWithdrawnBalanceBefore:
  assumes "executeStep contracts blockNum block step = (Success, contracts')"
  assumes "\<nexists> amount proof. step = WITHDRAW_WD tokenDepositAddress caller token amount proof"
  shows "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsLastUpdate' contracts' =
         nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsLastUpdate' contracts"
  using assms
proof (cases step)
  case (WITHDRAW_WD address' caller' token' amount' proof')
  then show ?thesis
    using assms
    by (smt (verit, ccfv_SIG) callWithdrawWhileDeadGetTokenWithdrawnOtherHash callWithdrawWhileDeadOtherAddress executeStep.simps(8) hash2_inj hash2_inj_def nonWithdrawnBalanceBefore_def senderMessage)
qed (auto simp add: nonWithdrawnBalanceBefore_def)

end

context HashProofVerifier
begin
lemma executeStepNonWithdrawnBalanceBeforeAfter [simp]:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof = (Success, contracts')"
  shows "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress (sender msg) token contractsLastUpdate' contracts' = 0"
  using assms
  unfolding nonWithdrawnBalanceBefore_def Let_def
  by (meson callWithdrawWhileDeadTokenWithdrawn)

lemma executeStepNonWithdrawnBalanceBeforeBefore [simp]:
  assumes "callWithdrawWhileDead contracts tokenDepositAddress msg block token amount proof = (Success, contracts')"
  shows "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress (sender msg) token contractsLastUpdate' contracts =
         accountBalance contractsLastUpdate' (mintedTokenB contractsLastUpdate' bridgeAddress token) (sender msg)"
  using assms
  unfolding nonWithdrawnBalanceBefore_def Let_def
  by (meson callWithdrawWhileDeadNotTokenWithdrawn)
end

(* ------------------------------------------------------------------------------------ *)

context HashProofVerifier
begin
thm callClaimBalanceOfMinted
(* FIXME: move *)
lemma callClaimBalanceOfOther:
  assumes "callClaim contracts bridgeAddress msg ID token amount proof = (Success, contracts')"
  assumes "user \<noteq> sender msg"
  shows "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) user = 
         accountBalance contracts (mintedTokenB contracts bridgeAddress token) user"
  using assms
  using callOriginalToMinted
  using callMintBalanceOfOther[of user "sender msg" contracts "mintedTokenB contracts bridgeAddress token"]
  unfolding callClaim_def claim_def
  by (auto simp add:Let_def split: option.splits prod.splits if_split_asm)

end

(* ------------------------------------------------------------------------------------ *)

context InitFirstUpdate
begin

lemma userTokensInvariantBase:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "accountBalance contractsInit (mintedTokenTD contractsInit tokenDepositAddress token) caller = 0"
  assumes "\<not> bridgeDead contractsI tokenDepositAddress"
  shows "accountBalance contractsI (mintedTokenTD contractsInit tokenDepositAddress token) caller + 
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsInit + 
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsInit + 
         transferredAmountFrom bridgeAddress token caller stepsInit +
         releasedAmountFrom tokenDepositAddress token caller stepsInit + 
         withdrawnAmountFrom tokenDepositAddress token caller stepsInit + 
         canceledAmountFrom tokenDepositAddress token caller stepsInit =
         depositedAmountTo tokenDepositAddress token caller stepsInit + 
         transferredAmountTo bridgeAddress token caller stepsInit"
  using reachableFromInitI assms InitFirstUpdate_axioms
proof (induction contractsInit contractsI stepsInit rule: reachableFrom.induct)
  case (reachableFrom_base contracts)
  then show ?case
    by (simp add: InitFirstUpdate_axioms_def InitFirstUpdate_def)
next
  case (reachableFrom_step steps contracts'' contracts contracts' blockNum block step)
  interpret IFU: InitFirstUpdate where contractsInit=contracts and contractsI=contracts'' and stepsInit="step # steps"
    using reachableFrom_step.prems
    by simp
  show ?case
  proof (cases "steps = []")
    case True
    then have step: "step = UPDATE (stateOracleAddressB contracts bridgeAddress) stateRootInit"
      using IFU.firstUpdate
      by simp

    have "accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller = 0"
      using \<open>steps = []\<close> reachableFrom_step.hyps reachableFrom.cases reachableFrom_step.prems(2) 
      by blast
    then show ?thesis
      using reachableFrom_step step \<open>steps = []\<close>
      by simp
  next
    case False
    then interpret IFU': InitFirstUpdate where contractsInit=contracts and contractsI=contracts' and stepsInit="steps"
      using InitFirstUpdateAxiomsInduction reachableFrom_step.hyps(1) reachableFrom_step.hyps(2) reachableFrom_step.prems 
      by blast

    have notDead: "\<not> bridgeDead contracts' tokenDepositAddress"
      by (meson reachableFrom.intros reachableFromBridgeDead reachableFrom_step.hyps(2) reachableFrom_step.prems(3))


    note * = reachableFrom_step.IH[OF reachableFrom_step.prems(1-2) notDead IFU'.InitFirstUpdate_axioms]
 
    show ?thesis
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')

      have "token' \<noteq> mintedTokenTD contracts tokenDepositAddress token"
        sorry
      then have AB:
        "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
         accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
        using callDepositOtherToken reachableFrom_step.hyps DEPOSIT
        by (metis executeStep.simps(1))

      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token \<and> caller' = caller")
        case True
        then have "reachableFrom contracts' contracts'' [DEPOSIT tokenDepositAddress caller ID' token amount']"
          by (metis DEPOSIT reachableFrom.simps reachableFrom_step.hyps(2))
        then have "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller steps
                      (DEPOSIT tokenDepositAddress caller ID' token amount' # steps) =
                   nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller steps steps + amount'"
          using IFU'.nonClaimedBeforeNonCanceledDepositsAmountToConsDeposit'
          by auto
        then show ?thesis
          using True AB DEPOSIT *
          by simp
      next
        case False
        then show ?thesis
          using AB DEPOSIT *
          by auto
      qed
    next
      case (UPDATE address' stateRoot')
      then show ?thesis
        using * reachableFrom_step.hyps
        by simp
    next
      case (TRANSFER address' caller' receiver' token' amount')

      have "caller' \<noteq> receiver'"
        sorry

      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token' = token")
        case False
        then have "mintedTokenB contracts' address' token' \<noteq> mintedTokenTD contracts tokenDepositAddress token"
          sorry
        then have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller =
                   accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
          using TRANSFER reachableFrom_step.hyps callTransferOtherToken[of contracts' address' caller' receiver' token' amount' contracts'' "mintedTokenB contracts' address' token'" "mintedTokenTD contracts tokenDepositAddress token"]
          by (metis executeStep.simps(5))
        then show ?thesis
          using False * TRANSFER
          by simp
      next
        case True
        show ?thesis
        proof (cases "caller' = caller")
          case True
 
          have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller + amount' =
                accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
            using callTransferBalanceOfCaller \<open>address' = bridgeAddress \<and> token' = token\<close> \<open>caller' = caller\<close>
            using TRANSFER reachableFrom_step.hyps
            by (metis IFU'.mintedTokenBI IFU.mintedTokenITDB executeStep.simps(5) le_add_diff_inverse2)

          then show ?thesis
            using * \<open>caller' = caller\<close> \<open>caller' \<noteq> receiver'\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> TRANSFER
            by simp
        next
          case False
          show ?thesis
          proof (cases "caller = receiver'")
            case True

            have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller =
                  accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller + amount'"
              using callTransferBalanceOfReceiver \<open>address' = bridgeAddress \<and> token' = token\<close> \<open>caller = receiver'\<close>
              using TRANSFER reachableFrom_step.hyps
              by (metis IFU'.mintedTokenBI IFU.mintedTokenITDB executeStep.simps(5))

            then show ?thesis
              using * \<open>caller = receiver'\<close> \<open>caller' \<noteq> receiver'\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> TRANSFER
              by simp
          next
            case False
            have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller =
                  accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
              using \<open>caller' \<noteq> caller\<close> \<open>caller \<noteq> receiver'\<close> 
              using IFU'.reachableFromInitI IFU.mintedTokenITDB TRANSFER True callTransferBalanceOfOther 
              by (smt (verit, ccfv_threshold) reachableFromBridgeTokenPairs reachableFromITokenPairs executeStep.simps(5) reachableFrom_step.hyps(2))
            then show ?thesis
              using * \<open>caller \<noteq> receiver'\<close> \<open>caller' \<noteq> caller\<close> \<open>caller' \<noteq> receiver'\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> TRANSFER
              by simp
          qed
        qed
      qed
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      
      have reachClaim: 
        "reachableFrom contracts' contracts'' [CLAIM address' caller' ID' token' amount' proof']"
        using CLAIM reachableFrom.reachableFrom_step reachableFrom_base reachableFrom_step.hyps(2)
        by blast

      show ?thesis
      proof (cases "address' = bridgeAddress \<and> caller' = caller \<and> token' = token")
        case False
        have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
              accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
        proof (cases "address' = bridgeAddress \<and> token' = token")
          case True
          then have "caller' \<noteq> caller"
            using False
            by simp
          then show ?thesis
            using True CLAIM callClaimBalanceOfOther[of contracts' address' "message caller' amount'"] reachableFrom_step.hyps
            using IFU'.mintedTokenBI IFU.mintedTokenITDB
            by auto
        next
          case False
          then have "mintedTokenTD contracts tokenDepositAddress token \<noteq> mintedTokenB contracts address' token'"
            sorry
          then show ?thesis
            using callClaimOtherToken[of contracts' address' "message caller' amount'"] reachableFrom_step.hyps CLAIM
            by auto
        qed
        then show ?thesis
          using False * CLAIM 
          using IFU'.nonClaimedBeforeNonCanceledDepositsAmountToBeforeConsClaimOther reachClaim
          by auto
      next
        case True
        have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
              accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller + amount'"
          using True callClaimBalanceOfMinted[of contracts' address' "message caller' amount'" ID' token' amount' proof' contracts''] reachableFrom_step.hyps CLAIM
          using IFU'.mintedTokenBI IFU.mintedTokenITDB
          by auto
        moreover
        have "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller
               (CLAIM bridgeAddress caller ID' token amount' proof' # steps) steps + amount' =
              nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller steps steps"
          using True IFU'.nonClaimedBeforeNonCanceledDepositsAmountToBeforeConsClaim[of contracts'' caller ID' token amount' proof'] reachClaim \<open>\<not> bridgeDead contracts' tokenDepositAddress\<close>
          by simp
        ultimately show ?thesis
          using True * CLAIM 
          by simp
      qed
    next
      case (BURN address' caller' ID' token' amount')
      then show ?thesis
        apply simp
        sorry
    next
      case (RELEASE address' caller' ID' token' amount' proof')
      then show ?thesis
        apply simp
        sorry
    next
      case (CANCEL_WD address' caller' ID' token' amount' proof')
      show ?thesis
      proof (cases "address' = tokenDepositAddress")
        case True
        then have False
          using reachableFrom_step.hyps callCancelDepositWhileDeadBridgeDead[of contracts' tokenDepositAddress "message caller' 0"] reachableFrom_step.prems
          by (metis CANCEL_WD executeStep.simps(7))
        then show ?thesis
          by simp
      next
        case False
        have "mintedTokenTD contracts tokenDepositAddress token \<noteq> tokenDepositAddress"
          sorry
        then have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
                   accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
          sorry
        then show ?thesis
          using False CANCEL_WD *
          by simp
      qed
    next
      case (WITHDRAW_WD address' caller' token' amount' proof')
      show ?thesis
      proof (cases "address' = tokenDepositAddress")
        case True
        then have False
          by (metis noWithdrawBeforeBridgeDead IFU'.reachableFromInitI WITHDRAW_WD list.set_intros(1) reachableFrom.reachableFrom_step reachableFrom_step.hyps(2) reachableFrom_step.prems(3))
        then show ?thesis
          by simp
      next
        case False
        then have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
                   accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
          sorry
        then show ?thesis
          using False WITHDRAW_WD *
          by simp
      qed
    qed
  qed
qed

end

locale InitFirstUpdateBridgeNotDeadLastValidState = InitUpdateBridgeNotDeadLastValidState + InitFirstUpdate where contractsI=contractsUpdate' + 
  assumes updatesNonZeroLVS: "updatesNonZero stepsAllLVS"

sublocale InitFirstUpdateBridgeNotDeadLastValidState \<subseteq> IFULVSLVS: InitFirstUpdate where contractsI=contractsLVS and stepsInit=stepsAllLVS
  by (metis InitFirstUpdate.axioms(2) InitFirstUpdate.intro InitFirstUpdate_axioms InitFirstUpdate_axioms_def InitLVS.Init_axioms Nil_is_append_conv last_appendR stepsAllLVS_def updatesNonZeroLVS)


context InitFirstUpdateBridgeNotDeadLastValidState
begin

lemma accountBalanceInvariantStep:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "executeStep contractsLVS blockNum block step = (Success, contracts)"
  assumes "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS + 
           nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllLVS + 
           nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllLVS + 
           transferredAmountFrom bridgeAddress token caller stepsInit +
           releasedAmountFrom tokenDepositAddress token caller stepsAllLVS + 
           withdrawnAmountFrom tokenDepositAddress token caller stepsAllLVS + 
           canceledAmountFrom tokenDepositAddress token caller stepsAllLVS =
           depositedAmountTo tokenDepositAddress token caller stepsAllLVS + 
           transferredAmountTo bridgeAddress token caller stepsInit"
  shows "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts + 
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit (step # stepsAllLVS) + 
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit (step # stepsAllLVS) + 
         transferredAmountFrom bridgeAddress token caller stepsInit +
         releasedAmountFrom tokenDepositAddress token caller (step # stepsAllLVS) + 
         withdrawnAmountFrom tokenDepositAddress token caller (step # stepsAllLVS) + 
         canceledAmountFrom tokenDepositAddress token caller (step # stepsAllLVS) =
         depositedAmountTo tokenDepositAddress token caller (step # stepsAllLVS) + 
         transferredAmountTo bridgeAddress token caller stepsInit"
proof (cases step)
  case (DEPOSIT address' caller' ID' token' amount')
  have *: "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts = 
           nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS"
    using assms DEPOSIT executeStepNonWithdrawnBalanceBefore
    by (simp del: executeStep.simps)

  show ?thesis
  proof (cases "address' = tokenDepositAddress \<and> token' = token \<and> caller' = caller")
    case True
    have r: "reachableFrom contractsLVS contracts [DEPOSIT tokenDepositAddress caller ID' token amount']"
      using assms True
      by (metis DEPOSIT HashProofVerifier.reachableFrom_base HashProofVerifier.reachableFrom_step HashProofVerifier_axioms)
    show ?thesis
      using True DEPOSIT * assms IFULVSLVS.nonClaimedBeforeNonCanceledDepositsAmountToConsDeposit[of "stepsLVS @ [UPDATE_step]" stepsInit, OF _ r]
      unfolding stepsAllLVS_def
      by simp
  next
    case False
    then show ?thesis
      using DEPOSIT assms *
      by auto
  qed
next
  case (CLAIM address' caller' ID' token' amount' proof')
  have *: "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts = 
           nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS"
    using assms CLAIM executeStepNonWithdrawnBalanceBefore
    by (simp del: executeStep.simps)
  then show ?thesis
    using CLAIM assms
    by auto
next
  case (BURN address' caller' ID' token' amount')
  have *: "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS = 
           nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts"
    using assms BURN executeStepNonWithdrawnBalanceBefore
    by (simp del: executeStep.simps)
  then show ?thesis
    using assms * BURN
    by auto
next
  case (TRANSFER address' caller' receiver' token' amount')
  have *: "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS = 
           nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts"
    using assms executeStepNonWithdrawnBalanceBefore TRANSFER
    by (simp del: executeStep.simps)
  then show ?thesis
    using assms TRANSFER
    by auto
next
  case (UPDATE address' stateRoot')
  have *: "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts = 
           nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS"
    using assms UPDATE executeStepNonWithdrawnBalanceBefore
    by (simp del: executeStep.simps)
  then show ?thesis
    using assms * UPDATE
    by auto
next
  case (RELEASE address' caller' ID' token' amount' proof')
  have *: "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS = 
           nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts"
    using assms RELEASE executeStepNonWithdrawnBalanceBefore
    by (simp del: executeStep.simps)
  show ?thesis
  proof (cases "address' = tokenDepositAddress \<and> token' = token")
   case True
   have r: "reachableFrom contractsLVS contracts [RELEASE tokenDepositAddress caller' ID' token amount' proof']"
      using RELEASE
      using True assms reachableFrom_base reachableFrom_step 
      by blast
    show ?thesis
    proof (cases "caller' = caller")
      case True
      then show ?thesis
        using \<open>address' = tokenDepositAddress \<and> token' = token\<close> * assms RELEASE nonReleasedBurnedAmountToConsRelease[OF r]
        by (simp del: nonReleasedBurnedAmountToConsRelease)
    next
      case False
      then show ?thesis
        using \<open>address' = tokenDepositAddress \<and> token' = token\<close> * RELEASE assms IFULVSLVS.nonReleasedBurnedAmountToConsReleaseOther[OF False _ r, of "stepsLVS @ [UPDATE_step]" stepsInit]
        unfolding stepsAllLVS_def
        by auto
    qed
  next
    case False
    then show ?thesis
      using * RELEASE assms
      by simp
  qed
next
  case (CANCEL_WD address' caller' ID' token' amount' proof')
  have *: "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts = 
           nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS"
    using assms CANCEL_WD  executeStepNonWithdrawnBalanceBefore
    by (simp del: executeStep.simps)

  have r: "reachableFrom contractsLVS contracts [CANCEL_WD address' caller' ID' token' amount' proof']"
    using assms
    using CANCEL_WD reachableFrom_base reachableFrom_step 
    by blast

  show ?thesis
  proof (cases "address' = tokenDepositAddress \<and> token' = token \<and> caller' = caller")
    case True
    then have r: "reachableFrom contractsLVS contracts [CANCEL_WD tokenDepositAddress caller ID' token amount' proof']"
      using r by simp
    show ?thesis
      using True * CANCEL_WD nonClaimedBeforeNonCanceledDepositsAmountToConsCancel[OF r] assms
      by simp
  next
    case False
    then show ?thesis
      using * assms CANCEL_WD InitLVS.nonClaimedBeforeNonCanceledDepositsAmountToConsCancelOther[OF r, of "stepsLVS @ [UPDATE_step]" stepsInit]
      unfolding stepsAllLVS_def
      by auto
  qed
next
  case (WITHDRAW_WD address' caller' token' amount' proof')
  show ?thesis
  proof (cases "address' = tokenDepositAddress \<and> token' = token \<and> caller' = caller")
    case True
    then have callWD: "callWithdrawWhileDead contractsLVS tokenDepositAddress (message caller 0) block token amount' proof' = (Success, contracts)"
      using WITHDRAW_WD assms
      by simp
    then have "verifyBalanceProof () (mintedTokenTD contractsInit tokenDepositAddress token) caller amount'
               (snd (lastValidStateTD contractsLVS tokenDepositAddress)) proof'"
      by (metis InitLVS.mintedTokenTDI callWithdrawWhileDeadVerifyBalanceProof senderMessage)
    then have vbp: "verifyBalanceProof () (mintedTokenTD contractsInit tokenDepositAddress token) caller amount'
               stateRoot proof' = True"
      by (metis getLastValidStateLVS snd_conv)
    have "accountBalance contractsUpdate' (mintedTokenTD contractsInit tokenDepositAddress token) caller = amount'"
      using verifyBalanceProofE[OF generateStateRootUpdate' vbp] assms
      by (metis ERC20StateMintedTokenINotNone option.collapse)
    then have "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS = amount'"
      by (metis callWD executeStepNonWithdrawnBalanceBeforeBefore mintedTokenBI mintedTokenITDB senderMessage)
    moreover have "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts = 0"
      by (metis callWD executeStepNonWithdrawnBalanceBeforeAfter senderMessage)
    ultimately show ?thesis
      using True assms WITHDRAW_WD callWithdrawWhileDeadBridgeDead[OF callWD]
      by simp
  next
    case False
    have *: "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contracts = 
             nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS"
      using False assms WITHDRAW_WD executeStepNonWithdrawnBalanceBefore
      by (auto simp del: executeStep.simps)
    then show ?thesis
      using False * assms WITHDRAW_WD
      by auto
  qed
qed

end

context BridgeDeadInitFirstUpdate
begin

lemma accountBalanceInvariant:
  assumes "properToken contractsInit tokenDepositAddress bridgeAddress token"
  assumes "accountBalance contractsInit (mintedTokenTD contractsInit tokenDepositAddress token) caller = 0"
  shows "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsLastUpdate' contractsBD + 
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllBD + 
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsAllBD + 
         transferredAmountFrom bridgeAddress token caller stepsInit +
         releasedAmountFrom tokenDepositAddress token caller stepsAllBD + 
         withdrawnAmountFrom tokenDepositAddress token caller stepsAllBD + 
         canceledAmountFrom tokenDepositAddress token caller stepsAllBD =
         depositedAmountTo tokenDepositAddress token caller stepsAllBD + 
         transferredAmountTo bridgeAddress token caller stepsInit"
  sorry

end

end