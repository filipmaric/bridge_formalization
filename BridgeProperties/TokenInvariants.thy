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
  assumes "reachable contracts contracts' steps"
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
  assumes "reachable contracts contracts' steps"
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
  assumes "reachable contracts contracts' steps"
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
  assumes "reachable contracts contracts' steps"
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
  assumes "reachable contractsInit contracts steps"
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
  assumes "reachable contractsInit contracts steps"
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
  assumes "reachable contractsInit contracts steps"
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
  assumes "reachable contractsInit contracts steps"
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
  assumes "reachable contractsI contractsClaim [CLAIM bridgeAddress caller ID token amount proof]"
  shows   "claimedDepositsAmount tokenDepositAddress bridgeAddress token
             (CLAIM bridgeAddress caller ID token amount proof # stepsInit) = 
           claimedDepositsAmount tokenDepositAddress bridgeAddress token stepsInit + amount"
proof-
  let ?CLAIM_step = "CLAIM bridgeAddress caller ID token amount proof"
  let ?DEPOSIT_step = "DEPOSIT tokenDepositAddress caller ID token amount"

  have *: "deposits tokenDepositAddress token (?CLAIM_step # stepsInit) =
           deposits tokenDepositAddress token stepsInit"
    by simp

  have "reachable contractsInit contractsClaim (?CLAIM_step # stepsInit)"
    using reachableTrans[OF assms(1) reachableInitI]
    by simp
 
  have "callClaim contractsI bridgeAddress (message caller amount) ID token amount proof = (Success, contractsClaim)"
    using assms
    by (metis executeStep.simps(2) reachableSingleton)
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
        using distinctDepositIDs[OF reachableInitI]
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
        using CLAIMNoDoubleCons \<open>reachable contractsInit contractsClaim (?CLAIM_step # stepsInit)\<close>
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
      using distinctDeposits[OF reachableInitI]
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
  assumes "reachable contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
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
  using reachableInitI InitFirstUpdate_axioms
proof (induction contractsInit contractsI stepsInit)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contractsI contractsInit contractsI' blockNum block step)
  show ?case
  proof (cases "steps = []")
    case True
    then obtain stateRoot where "step = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRoot"
      by (metis InitFirstUpdate.firstUpdate last.simps reachable_step.prems)
    then show ?thesis
      using True claimedDepositsAmountConsOther
      by (simp add: claimedAmount_def claims_def claimedDepositsAmount_def claimedDeposits_def deposits_def)
  next
    case False
    interpret I: Init where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
      by (meson InitFirstUpdate_def Init_axioms.intro Init_def reachable_step.hyps(1) reachable_step.prems)
    interpret IFU: InitFirstUpdate where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
      using False
      by (metis I.Init_axioms InitFirstUpdate.axioms(2) InitFirstUpdate.intro InitFirstUpdate_axioms_def last_ConsR reachable_step.prems stateRootInitNonZero)

    have *: "claimedAmount bridgeAddress token steps =
             claimedDepositsAmount tokenDepositAddress bridgeAddress token steps"
      using IFU.InitFirstUpdate_axioms reachable_step.IH by blast

    show ?thesis
      using * claimedDepositsAmountConsOther
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')
      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token")
        case True
        show ?thesis
          using DEPOSIT True IFU.claimedDepositsAmountConsDeposit claimedAmountConsOther
          by (metis IFU.InitFirstUpdate_axioms Step.simps(9) reachable.reachable_step reachable_base reachable_step.IH reachable_step.hyps(2))
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
          by (metis reachable.reachable_step reachable_base reachable_step.hyps(2))
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
  using reachableInitI assms InitFirstUpdate_axioms
proof (induction contractsInit contractsI stepsInit rule: reachable.induct)
  case (reachable_base contractsInit)
  then show ?case
    by simp
next
  case (reachable_step steps contractsI contractsInit contractsI' blockNum block step)

  show ?case
  proof (cases "steps = []")
    case True
    then have "reachable contractsInit contractsI' []"
      using reachable_step.hyps
      by simp
    then have "contractsInit = contractsI'"
      using reachable.cases
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
      by (metis InitFirstUpdate.firstUpdate True last.simps reachable_step.prems(2))
    ultimately
    show ?thesis
      using reachable_step.prems reachable_step.hyps firstUpdate True
      by (metis reachableITokenPairs HashProofVerifier.reachable_step HashProofVerifier_axioms Nat.add_0_right callUpdateIBridge callUpdateIERC20 executeStep.simps(6))
  next
    case False

    interpret IFU: InitFirstUpdate where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
      using False InitFirstUpdateAxiomsInduction reachable_step.hyps(1) reachable_step.hyps(2) reachable_step.prems(2)
      by blast

    have *: "reachable contractsInit contractsI (step # steps)"
      using reachable.reachable_step reachable_step
      by blast

    have *: "totalMinted contractsI' bridgeAddress token + burnedAmount bridgeAddress token steps = 
             totalMinted contractsInit bridgeAddress token +
             claimedAmount bridgeAddress token steps"
      using reachable_step.IH reachable_step.prems
      using IFU.InitFirstUpdate_axioms notDead 
      by fastforce

    let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
    have **: "mintedTokenB contractsI bridgeAddress token = ?mintedToken"
       using IFU.reachableInitI reachable.reachable_step reachableBridgeMintedToken reachable_step.hyps(2) 
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
          using DEPOSIT reachable_step.prems reachable_step.hyps callDepositOtherToken
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
          using * ** reachable_step.prems reachable_step.hyps DEPOSIT
          by (metis IFU.mintedTokenBI)
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
          using  reachable_step.prems(1)
          unfolding properToken_def
          by (smt (verit, ccfv_SIG) executeStep.simps(1) reachableBridgeTokenPairs reachableITokenPairs IFU.reachableInitI reachable_step.hyps(2))
      qed
    next
      case (CLAIM address' caller ID token' amount proof')
      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token' = token")
        case True

        have ***: "mintedTokenB contractsI' bridgeAddress token' = ?mintedToken"
            using ** True
            using IFU.reachableInitI reachableBridgeMintedToken
            by blast

        have "totalTokenBalance contractsI ?mintedToken =
              totalTokenBalance contractsI' ?mintedToken + amount"
        proof (rule callClaimTotalBalance)
          show "finiteBalances contractsI' ?mintedToken"
            using IFU.properTokenFiniteBalancesMinted IFU.reachableInitI reachableFiniteBalances reachable_step.prems(1)
            by blast
        next
          show "callClaim contractsI' bridgeAddress (message caller amount) ID token' amount proof' = (Success, contractsI)"
            using True CLAIM reachable_step.hyps
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
          by (metis executeStep.simps(2) reachableBridgeMintedToken IFU.reachableInitI reachable_step.hyps(2))
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
          by (metis IFU.mintedTokenBI)
      qed
    next
      case (UPDATE address' stateRoot')
      have "totalTokenBalance contractsI (mintedTokenB contractsI bridgeAddress token) =
            totalTokenBalance contractsI' (mintedTokenB contractsInit bridgeAddress token)"
        using **
        using UPDATE callUpdateIERC20 executeStep.simps(6) reachable_step.hyps(2)
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
        by (metis IFU.mintedTokenBI)
    next
      case (CANCEL_WD address' caller' ID' token' amount' proof')
      have "?mintedToken \<noteq> token'" (* no cancel of minted tokens *)
        sorry
      then have "ERC20state contractsI ?mintedToken = ERC20state contractsI' ?mintedToken"
        using CANCEL_WD reachable_step.hyps(2)
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
        by (metis IFU.mintedTokenBI)
    next
      case (WITHDRAW_WD address' caller token' amount proof')
      have "?mintedToken \<noteq> token'" (* no withdrawal of minted tokens *)
        sorry
      then have "ERC20state contractsI ?mintedToken = ERC20state contractsI' ?mintedToken"
        using WITHDRAW_WD reachable_step.hyps(2)
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
        by (metis IFU.mintedTokenBI)
    next
      case (TRANSFER address' caller' receiver' token' amount')

      have "callTransfer contractsI' address' caller' receiver' token' amount' = (Success, contractsI)"
         using reachable_step.hyps TRANSFER
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
            using reachableFiniteBalances IFU.properTokenFiniteBalancesMinted IFU.reachableInitI reachable_step.prems(1)
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
            using reachableFiniteBalances IFU.properTokenFiniteBalancesMinted IFU.reachableInitI reachable_step.prems(1) 
            by blast
        next
          show "callWithdraw contractsI' address' (message caller' 0) ID' token' amount' = (Success, contractsI)"
            using reachable_step.hyps BURN
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
          by (smt (verit) IFU.mintedTokenBI add.commute add.left_commute diff_add)
      next
      case False
        have "?mintedToken \<noteq> mintedTokenB contractsI' address' token'"
          sorry
        then have "ERC20state contractsI ?mintedToken = ERC20state contractsI' ?mintedToken"
          using BURN reachable_step.hyps(2)
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
          by (metis IFU.mintedTokenBI)
      qed
    next
      case (RELEASE address' caller' ID' token' amount')
      have "?mintedToken \<noteq> token'" (* no withdrawal of minted tokens *)
        sorry
      then have "ERC20state contractsI ?mintedToken = ERC20state contractsI' ?mintedToken"
        using RELEASE reachable_step.hyps(2)
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
        by (metis IFU.mintedTokenBI)
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
  using reachableInitI Init_axioms assms
proof (induction contractsInit contractsI stepsInit rule: reachable.induct)
  case (reachable_base contractsInit)
  then interpret I: Init where contractsInit=contractsInit and contractsI=contractsInit and stepsInit="[]"
    by simp
  show ?case
    using reachable_base.prems
    by simp
next
  case (reachable_step steps contractsI contractsInit contractsI' blockNum block step)
  then interpret I: Init where contractsInit=contractsInit and contractsI=contractsI' and stepsInit=steps
    using InitInduction by blast
  have *: "accountBalance contractsI' token tokenDepositAddress +
           canceledAmount tokenDepositAddress token steps +
           withdrawnAmount tokenDepositAddress token steps +
           releasedAmount tokenDepositAddress token steps =
           depositedAmount tokenDepositAddress token steps"
    using reachable_step
    by simp
  show ?case
  proof (cases step)
    case (UPDATE address' stateRoot')
    then show ?thesis
      using * reachable_step.hyps
      by simp
  next
    case (TRANSFER address' caller' receiver' token' amount')
    have "mintedTokenB contractsI' address' token' \<noteq> token"
      sorry
    then have "accountBalance contractsI token tokenDepositAddress = 
               accountBalance contractsI' token tokenDepositAddress"
      using TRANSFER reachable_step.hyps
      using callTransferOtherToken[of contractsI' address' caller' receiver' token' amount' contractsI "mintedTokenB contractsI' address' token'" token]
      by (metis executeStep.simps(5))
    then show ?thesis
      using * TRANSFER reachable_step.hyps
      by simp
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    have "mintedTokenB contractsI' address' token' \<noteq> token"
      sorry
    then have "accountBalance contractsI token tokenDepositAddress = 
              accountBalance contractsI' token tokenDepositAddress"
      using callClaimOtherToken[of contractsI' address' "message caller' amount'" ID']
      using CLAIM reachable_step.hyps
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
        using * DEPOSIT reachable_step.hyps callDepositBalanceOfContract
        by simp
    next
      case False
      have "caller' \<noteq> tokenDepositAddress"
        sorry
      then show ?thesis
        using False * DEPOSIT reachable_step.hyps
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
        using CANCEL_WD * reachable_step.hyps 
        using callCancelDepositWhileDeadBalanceOfContract[of contractsI' address' "message caller' 0" block ID' token' amount' proof' contractsI]
        by auto
    next
      case False
      have "caller' \<noteq> tokenDepositAddress"
        sorry
      then show ?thesis
        using False CANCEL_WD * reachable_step.hyps 
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
        using WITHDRAW_WD * reachable_step.hyps 
        using callWithdrawWhileDeadBalanceOfContract[of contractsI' address' "message caller' 0" block token' amount' proof' contractsI]
        by auto
    next
      case False
      have "caller' \<noteq> tokenDepositAddress"
        sorry
      then show ?thesis
        using False WITHDRAW_WD * reachable_step.hyps 
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
      using BURN reachable_step.hyps
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
        using RELEASE * reachable_step.hyps 
        using callReleaseBalanceOfContract[of contractsI' address' "message caller' 0" ID' token' amount' proof' contractsI]
        by auto
    next
      case False
      have "caller' \<noteq> tokenDepositAddress"
        sorry
      then show ?thesis
        using False RELEASE * reachable_step.hyps 
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
  obtain contracts where "reachable contractsInit contracts (steps @ stepsBefore)" "reachable contracts contractsI [step]"
    using assms
    by (metis append_Cons append_self_conv2 reachableAppend reachableInitI)

  interpret IFU: InitFirstUpdate where contractsI=contracts and stepsInit="steps @ stepsBefore"
    by (metis (no_types, lifting) False Init'_axioms InitFirstUpdate_axioms_def InitFirstUpdate_def Init_axioms.intro Init_def \<open>reachable contractsInit contracts (steps @ stepsBefore)\<close> append_Cons append_is_Nil_conv assms firstUpdate last_appendR stateRootInitNonZero)

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
  assumes "reachable contractsLVS contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
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
    by (metis executeStep.simps(7) reachableSingleton)

  have "?DEPOSIT_step \<in> set stepsAllLVS"
    using Init_LVS.cancelDepositOnlyAfterDeposit[OF cancel]
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
      using distinctDeposits[OF reachableInitLVS]
      by simp
  next
    show "?DEPOSIT_step \<in> set ?deposits"
      by fact
  next
    show "?P ?DEPOSIT_step stepsAllLVS"
      using assms cancel cancelDepositWhileDeadNoClaim CANCELNoDoubleCons 
      by (metis DEPOSIT_id.simps isCanceledID_def isClaimedID_def reachableSingleton reachableInitLVS reachable_step)
  next
    show "\<forall> step \<in> set ?deposits. ?P step stepsAllLVS \<and> step \<noteq> ?DEPOSIT_step \<longleftrightarrow> ?P step (?CANCEL_step # stepsAllLVS)"
    proof safe
      fix step
      assume "step \<noteq> ?DEPOSIT_step" "step \<in> set ?deposits"
      then have "DEPOSIT_id step \<noteq> ID"
        using \<open>?DEPOSIT_step \<in> set ?deposits\<close>
        by (metis DEPOSIT_id.simps distinctDepositIDs distinct_map inj_on_def reachableInitLVS)
      assume "\<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) stepsAllLVS"
             "isCanceledID tokenDepositAddress token (DEPOSIT_id step) (?CANCEL_step # stepsAllLVS)"
      then show False
        using \<open>DEPOSIT_id step \<noteq> ID\<close>
        by (simp add: isCanceledID_def)
    qed (auto simp add: isCanceledID_def)
  qed
qed

lemma nonClaimedBeforeNonCanceledDepositsAmountConsCancel:
  assumes "reachable contractsLVS contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
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
  assumes "reachable contractsInit contracts steps"
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
  using reachableContractsBD BridgeDead_axioms
proof (induction contractsDead contractsBD stepsBD rule: reachable.induct)
  case (reachable_base contractsBD)
  then interpret BD: BridgeDead where contractsBD=contractsBD and stepsBD="[]" and contractsDead=contractsBD
    .
  have *: "?NCC [] + ?C [] = ?NC []"
    find_theorems name: reachableInitLVS
    using InitUpdateBridgeNotDeadLastValidState_Dead'.reachableInitLVS canceledAmountBridgeNotDead nonCanceledNonClaimedBridgeNotDead notBridgeDead'
    unfolding InitUpdateBridgeNotDeadLastValidState_Dead'.stepsAllLVS_def
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
        using reachableSingleton[OF BD.deathStep] 
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
        using InitUpdateBridgeNotDeadLastValidState_Dead'.nonClaimedBeforeNonCanceledDepositsAmountConsCancel
        using BD.deathStep CANCEL_WD InitUpdateBridgeNotDeadLastValidState_Dead'.stepsAllLVS_def True by auto
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
  case (reachable_step steps contractsBD contractsDead contractsBD' blockNum block step)

  interpret BD': BridgeDead where contractsBD=contractsBD and stepsBD="step#steps" and contractsDead=contractsDead
    using reachable_step.prems by fastforce

  interpret BD: BridgeDead where contractsBD=contractsBD' and stepsBD=steps and contractsDead=contractsDead
    by (metis BD'.BridgeDead_axioms BD'.deathStep BridgeDead.bridgeDead BridgeDead.intro BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms notBridgeDead' reachable_step.hyps(1) stateRootNonZero)

  have *: "?NCC (steps @ [stepDeath]) + ?C (steps @ [stepDeath]) = ?NC (steps @ [stepDeath])"
    using reachable_step.IH[OF BD.BridgeDead_axioms]
    by simp

  show ?case
    using *
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    show ?thesis
    proof (cases "address' = tokenDepositAddress \<and> token' = token")
      case True
      have "bridgeDead contractsBD' tokenDepositAddress"
        using reachable_step.hyps BD.bridgeDead DEPOSIT
        by auto
      then show ?thesis
        using DEPOSIT reachable_step.hyps True
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
        using BD.InitUpdateBridgeNotDeadLastValidState_BD.nonClaimedBeforeNonCanceledDepositsAmountConsCancel
              BD.InitUpdateBridgeNotDeadLastValidState_BD.stepsAllLVS_def 
        by (metis CANCEL_WD Cons_eq_append_conv True append_eq_appendI reachable.reachable_step reachable_base reachable_step.hyps(2))
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
  assumes "reachable contracts contracts' steps"
  assumes "accountBalance contracts (mintedTokenB contracts bridgeAddress token) account = 0"
  shows "balanceOf (mintedUserBalances bridgeAddress token steps) account = 
         accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account"
  using assms
proof (induction contracts contracts' steps)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then have *: 
    "balanceOf (mintedUserBalances bridgeAddress token steps) account =
    accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account"
    using reachable_step
    by blast
    
  show ?case
  proof (cases step)
    case (CLAIM address' caller' ID' token' amount' proof')
    show ?thesis
    proof (cases "address' = bridgeAddress \<and> token' = token \<and> caller' = account")
      case True
      then show ?thesis
        using CLAIM * reachable_step.hyps 
        using callClaimBalanceOfMinted[of contracts' bridgeAddress "message caller' amount'" ID' token amount' proof' contracts'']
        by simp
    next
      case False
      have "mintedTokenB contracts bridgeAddress token \<noteq> mintedTokenB contracts address' token'"
        sorry
      then show ?thesis
        using False CLAIM * reachable_step.hyps 
        using  callClaimOtherToken[of contracts' address'  "message caller' amount'"]
        by (cases "address' = bridgeAddress \<and> token' = token") auto
    qed
  next
    case (TRANSFER address' caller' receiver' token' amount')
    have transfer:
      "callTransfer contracts' address' caller' receiver' token' amount' = (Success, contracts'')"
        using TRANSFER reachable_step.hyps
        by auto
    show ?thesis
    proof (cases "address' = bridgeAddress \<and> token' = token \<and> caller' = account")
      case True
      have "account \<noteq> receiver'"
        sorry
      show ?thesis
        using True TRANSFER * reachable_step.hyps
        using callTransferBalanceOfCaller[OF transfer]
        using transferBalanceBalanceOfTo[OF \<open>account \<noteq> receiver'\<close>]
        by (metis reachableBridgeTokenPairs reachableITokenPairs mintedUserBalancesConsTransfer)
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
          by (metis (no_types, opaque_lifting) reachableBridgeTokenPairs reachableITokenPairs reachable_step.hyps(1))
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
      using * reachable_step.hyps
      by simp
  next
    case (DEPOSIT address' caller' ID' token' amount')
    have "mintedTokenB contracts bridgeAddress token \<noteq> token'"
      sorry
    then have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
               accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
      using callDepositOtherToken
      using DEPOSIT reachable_step.hyps
      by simp
    then show ?thesis
      using DEPOSIT * reachable_step.hyps
      by simp
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    have "mintedTokenB contracts bridgeAddress token \<noteq> token'"
      sorry
    then have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
               accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
      using CANCEL_WD reachable_step.hyps
      using callCancelDepositWhileDeadOtherToken 
      by (metis executeStep.simps(7))
    then show ?thesis
      using CANCEL_WD * reachable_step.hyps
      by simp
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    have "mintedTokenB contracts bridgeAddress token \<noteq> token'"
      sorry
    then have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
               accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
      using WITHDRAW_WD reachable_step.hyps
      using callWithdrawWhileDeadOtherToken 
      by (metis executeStep.simps(8))
    then show ?thesis
      using WITHDRAW_WD * reachable_step.hyps
      by simp
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    have "mintedTokenB contracts bridgeAddress token \<noteq> token'"
      sorry
    then have "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) account =
               accountBalance contracts'' (mintedTokenB contracts bridgeAddress token) account"
      using callReleaseOtherToken
      using RELEASE reachable_step.hyps
      by (metis executeStep.simps(4))
    then show ?thesis
      using RELEASE * reachable_step.hyps
      by simp
  next
    case (BURN address' caller' ID' token' amount') 
    show ?thesis
    proof (cases "address' = bridgeAddress \<and> token' = token \<and> caller' = account")
      case True
      then show ?thesis
        using BURN * reachable_step.hyps 
        using callWithdrawBalanceOfSender[of contracts' bridgeAddress "message caller' 0"]
        by simp
    next
      case False
      have "mintedTokenB contracts bridgeAddress token \<noteq> mintedTokenB contracts address' token'"
        sorry
      then show ?thesis
        using False BURN * reachable_step.hyps 
        using  callWithdrawOtherToken[of contracts' address'  "message caller' 0"]
        by (cases "address' = bridgeAddress \<and> token' = token") auto
    qed
  qed
qed

theorem totalMintedUserBalances:
  assumes "reachable contracts contracts' steps"
  assumes "totalMinted contracts bridgeAddress token = 0"
  assumes "finiteBalances contracts (mintedTokenB contracts bridgeAddress token)"
  shows "totalBalance (mintedUserBalances bridgeAddress token steps) =
         totalMinted contracts' bridgeAddress token"
proof (rule totalBalanceEq, safe)
  show "finite (Mapping.keys (balances (mintedUserBalances bridgeAddress token steps)))"
    by simp
next
  show "finite (Mapping.keys (balances (the (ERC20state contracts' (mintedTokenB contracts' bridgeAddress token)))))"
    by (metis assms(1) assms(3) finiteBalances_def reachableBridgeTokenPairs reachableFiniteBalances reachableITokenPairs)
next
  fix user
  have "finite (Mapping.keys (balances (the (ERC20state contracts (mintedTokenB contracts bridgeAddress token))))) "
    using assms(3) finiteBalances_def by blast
  then show "balanceOf (mintedUserBalances bridgeAddress token steps) user = 
        accountBalance contracts' (mintedTokenB contracts' bridgeAddress token) user"
    using mintedUserBalancesAccountBalance assms totalBalanceZero reachableBridgeMintedToken
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
  using totalMintedUserBalances[OF reachableInitI] totalMintedBridgeNotDead
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
  assumes "reachable contractsInit contractsI stepsInit"
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
  proof (induction contractsInit contractsI stepsInit rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
  next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then have "\<nexists> caller amount proof. step = WITHDRAW_WD tokenDepositAddress caller token amount proof"
    by auto
  moreover have "deadStateTD contracts' tokenDepositAddress = 0"
    using reachable.reachable_step reachableBridgeDead reachable_base reachable_step.hyps(2) reachable_step.prems(1) by blast
  ultimately show ?case
      using reachable_step
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
  assumes "reachable contractsInit contractsI (steps @ stepsBefore)"
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
    obtain contracts where "reachable contractsInit contracts stepsBefore" "reachable contracts contractsI steps"
      using reachableInitI assms(1)
      using reachableAppend by blast

    interpret IFU: InitFirstUpdate where contractsI=contracts and stepsInit=stepsBefore
      by (metis False Init'_axioms Init.intro InitFirstUpdate.intro InitFirstUpdate_axioms_def Init_axioms_def \<open>reachable contractsInit contracts stepsBefore\<close> assms(1) firstUpdate last_appendR stateRootInitNonZero)
    show ?thesis
      using IFU.totalMintedUserBalancesClaimedBurnedAmount IFU.claimedEqualsClaimedDeposits
      using assms 
      by presburger
  qed
  then show ?thesis
    using claimedBeforeDepositsAmountClaimedDepositsAmount[OF assms(1)]
    using nonWithdrawnClaimedBeforeAmountBridgeNotDead
    using assms reachableInitI
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
  using reachableContractsBD assms BridgeDeadInitFirstUpdate_axioms
proof (induction contractsDead contractsBD stepsBD rule: reachable.induct)
  case (reachable_base contractsBD)
  then interpret BD: BridgeDeadInitFirstUpdate where contractsBD=contractsBD and stepsBD="[]" and contractsDead=contractsBD
    by blast

  find_theorems name: claimedBeforeDepositsAmountBridgeNotDead
  have *: "?W [] + ?N [] + ?B = ?C []"
    using withdrawnAmountBridgeNotDead[OF Init_Dead'.reachableInitI BD.notBridgeDead', of token]
    using InitFirstUpdate_Dead'.claimedBeforeDepositsAmountBridgeNotDead[where steps="stepsNoUpdate @ [UPDATE_step]" and stepsBefore=stepsInit and token=token]
    using notBridgeDead'
    using reachable_base.prems Init_Dead'.reachableInitI nonWithdrawnClaimedBeforeAmountBridgeNotDead properTokenFiniteBalancesMinted
    unfolding BD.stepsBeforeDeath_def
    by (metis add_cancel_right_left append.assoc append_Nil)

  show ?case
  proof (cases stepDeath)
    case (DEPOSIT address' caller' ID' token' amount')
    then show ?thesis
      using *
      using InitFirstUpdate_Dead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (CANCEL_WD address' caller' ID' token' amount')
    then show ?thesis
      using *
      using InitFirstUpdate_Dead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using *
      using InitFirstUpdate_Dead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (TRANSFER address' caller' receiver' token' amount')
    then show ?thesis
      using *
      using InitFirstUpdate_Dead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using *
      using InitFirstUpdate_Dead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
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
        by (metis True deathStep executeStep.simps(8) reachableSingleton)
      let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
      have "verifyBalanceProof () ?mintedToken caller' amount' stateRoot proof'"
        using callWithdrawWhileDeadVerifyBalanceProof[OF withdraw]
        by (metis InitUpdateBridgeNotDeadLastValidState_Dead'.getLastValidStateLVS Init_Dead'.mintedTokenTDI mintedTokenITDB senderMessage snd_conv)
      then have "accountBalance contractsLastUpdate' ?mintedToken caller' = amount'"
        by (metis (no_types, lifting) ERC20StateMintedTokenINotNone generateStateRootUpdate' mintedTokenITDB option.collapse reachable_base.prems(1) verifyBalanceProofE)
      then have "balanceOf (mintedUserBalances bridgeAddress token stepsInit) caller' = amount'" 
        using mintedUserBalancesAccountBalance[OF reachableInitI totalBalanceZero, of bridgeAddress token caller']
        using reachable_base.prems(2)
        using properTokenFiniteBalancesMinted reachable_base.prems
        unfolding finiteBalances_def
        by blast
      then have **: "amount' \<le> balanceOf (nonWithdrawnMintedUserBalances tokenDepositAddress bridgeAddress token stepsInit
          ((stepsNoUpdate @ [UPDATE_step]) @ stepsInit)) caller'"
        using nonWithdrawnMintedUserBalancesBridgeNotDead
        by (metis InitUpdateBridgeNotDeadLastValidState_Dead'.reachableInitLVS InitUpdateBridgeNotDeadLastValidState_Dead'.stepsAllLVS_def append.assoc le_refl notBridgeDead')
      show ?thesis
        using nonWithdrawnClaimedBeforeDeathAmountConsWithdraw[OF **]
        using True * WITHDRAW_WD
        using InitFirstUpdate_Dead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
        unfolding BD.stepsBeforeDeath_def
        by auto
    qed
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using *
      using InitFirstUpdate_Dead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by auto
  next
    case (RELEASE address' caller' ID' token' amount')
    then show ?thesis
      using *
      using InitFirstUpdate_Dead.claimedBeforeDepositsAmountCons[where stepsBefore=stepsInit]
      unfolding BD.stepsBeforeDeath_def
      by (cases "address' = tokenDepositAddress \<and> token' = token") auto
  qed
next
  case (reachable_step stepsBD contractsBD'' contractsDead contractsBD' blockNum block step)
  interpret BD: BridgeDead where contractsDead=contractsDead and contractsBD=contractsBD' and stepsBD=stepsBD
    by (metis BridgeDead.bridgeDead BridgeDead.deathStep BridgeDead.intro BridgeDeadInitFirstUpdate.axioms(1) BridgeDead_axioms_def InitUpdate_axioms LastUpdate_axioms notBridgeDead' reachable_step.hyps(1) reachable_step.prems(3) stateRootNonZero)
  interpret BDIFU: BridgeDeadInitFirstUpdate where contractsDead=contractsDead and contractsBD=contractsBD' and stepsBD=stepsBD
    by (metis BD.BridgeDead_axioms BD.Init_BD.reachableInitI BridgeDead.stepsAllBD_def BridgeDeadInitFirstUpdate_def HashProofVerifier.InitFirstUpdateAxiomsInduction HashProofVerifier_axioms append_Cons append_is_Nil_conv list.distinct(1) reachable_step.hyps(2) reachable_step.prems(3))
  interpret IFU: InitFirstUpdate where contractsI=contractsBD'' and stepsInit="step # BD.stepsAllBD"
    by (metis BD.stepsAllBD_def BridgeDead.stepsAllBD_def BridgeDeadInitFirstUpdate_def append_Cons reachable_step.prems(3))

  have *: "?W (stepsBD @ [stepDeath]) + ?N (stepsBD @ [stepDeath]) + ?B = ?C (stepsBD @ [stepDeath])"
    using reachable_step.IH
    using BDIFU.BridgeDeadInitFirstUpdate_axioms reachable_step.prems by blast
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
        using WITHDRAW_WD reachable_step.hyps
        by auto
      let ?mintedToken = "mintedTokenB contractsInit bridgeAddress token"
      have "verifyBalanceProof () ?mintedToken caller' amount' stateRoot proof'"
        using callWithdrawWhileDeadVerifyBalanceProof[OF withdraw]
        by (metis BD.InitUpdateBridgeNotDeadLastValidState_BD.getLastValidStateLVS BD.Init_BD.mintedTokenTDI mintedTokenITDB senderMessage snd_conv)
      then have "accountBalance contractsLastUpdate' ?mintedToken caller' = amount'"
        by (metis (no_types, opaque_lifting) ERC20StateMintedTokenINotNone generateStateRootUpdate' mintedTokenITDB option.collapse reachable_step.prems(1) verifyBalanceProofE)
      then have "balanceOf (mintedUserBalances bridgeAddress token stepsInit) caller' = amount'" 
        using mintedUserBalancesAccountBalance
        using notBridgeDeadContractsLastUpdate' reachableInitI reachable_step.prems(2) totalBalanceZero
        using properTokenFiniteBalancesMinted reachable_step.prems
        unfolding finiteBalances_def
        by blast
      moreover

      have "getTokenWithdrawn (the (tokenDepositState contractsBD' tokenDepositAddress)) (hash2 caller' token) = False"
        using callWithdrawWhileDeadNotTokenWithdrawn[OF withdraw]
        by simp
      then have "\<nexists>amount proof. WITHDRAW_WD tokenDepositAddress caller' token amount proof \<in> set BD.stepsAllBD"
        using reachableGetTokenWithdrawnNoWithdraw
        using BD.Init_BD.reachableInitI by blast
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
  assumes "reachable contractsLVS contractsRelease [RELEASE tokenDepositAddress caller ID token amount proof]"
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
    by (metis assms executeStep.simps(4) reachableSingleton senderMessage)
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
      using distinctBurns reachableInitI by blast
  next
    show "\<not> isReleasedID tokenDepositAddress token (BURN_id ?BURN_step) stepsAllLVS"
      using RELEASENoDoubleCons[of contractsInit contractsRelease] reachableTrans[OF assms(1) reachableInitLVS]
      by (simp add: isReleasedID_def)
  next
    show "\<forall> step \<in> set ?burns. (?P step stepsAllLVS \<and> step \<noteq> ?BURN_step \<longleftrightarrow> ?P step (?RELEASE_step # stepsAllLVS))"
    proof safe
      fix step
      assume "step \<in> set ?burns" "step \<noteq> ?BURN_step"
      then have "BURN_id step \<noteq> ID"
        using \<open>?BURN_step \<in> set ?burns\<close>
        by (metis BURN_id.simps distinctBurnIDs distinct_map inj_on_def reachableInitI)
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
      using assms distinctBurns reachableInitI by fastforce
  next
    show "\<not> isReleasedID tokenDepositAddress token (BURN_id ?BURN_step) steps"
      using RELEASENoDoubleCons[of contractsInit _] 
      using assms isReleasedID_def reachableInitI 
      by auto
  next
    show "\<forall> step \<in> set ?burns. (?P step steps \<and> step \<noteq> ?BURN_step \<longleftrightarrow> ?P step (?RELEASE_step # steps))"
    proof safe
      fix step
      assume "step \<in> set ?burns" "step \<noteq> ?BURN_step"
      then have "BURN_id step \<noteq> ID"
        using \<open>?BURN_step \<in> set ?burns\<close>
        by (metis BURN_id.simps Step.simps(35) assms burnsConsOther distinctBurnIDs distinct_map inj_on_def reachableInitI)
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
  using reachableInitI InitFirstUpdate_axioms
proof (induction contractsInit contractsI stepsInit rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  interpret IFU: InitFirstUpdate where contractsInit=contracts and contractsI=contracts'' and stepsInit="step # steps"
    by (simp add: reachable_step.prems)

  show ?case
  proof (cases "steps = []")
    case True
    then show ?thesis
      using IFU.firstUpdate
      by simp
  next
    case False
    then interpret IFU': InitFirstUpdate where contractsInit=contracts and contractsI=contracts' and stepsInit=steps
      using InitFirstUpdateAxiomsInduction reachable_step.hyps reachable_step.prems by blast

    have *: "releasedAmount tokenDepositAddress token steps +
             nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token steps steps =
             burnedAmount bridgeAddress token steps"
      using IFU'.InitFirstUpdate_axioms reachable_step.IH by blast

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
    have *: "reachable contractsLVS contracts' [RELEASE tokenDepositAddress caller' ID' token amount' proof']"
      using assms(1) RELEASE True
      using reachable_base reachable_step by blast
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
  using reachableLastUpdateLU assms InitFirstUpdateLastUpdate_axioms 
proof (induction contractsLastUpdate contractsLU stepsNoUpdate rule: reachable.induct)
  case (reachable_base contractsLU)
  show ?case
    using releasedInvariantBase
    by (simp add: UPDATE_step_def)
next
  case (reachable_step stepsNoUpdate contracts'' contracts contracts' blockNum block step)
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
      show "reachable contractsLastUpdate contractsLastUpdate []"
        by (simp add: reachable_base)
    next
      show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
        by fact
    qed

    show ?thesis
      using True LVS.releasedAmountInvariantStep *
      unfolding LVS.stepsAllLVS_def
      by (metis I.reachableLastUpdateLU I.update append_Cons append_Nil prod.inject reachableSingleton update)
  next
    case False
    interpret I': InitFirstUpdateLastUpdate where stepsNoUpdate="stepsNoUpdate" and contractsLU=contracts' and contractsLastUpdate=contracts
      by (meson I.Update_axioms I.noUpdate InitFirstUpdateLastUpdate.intro InitFirstUpdate_axioms LastUpdate.intro LastUpdate_axioms.intro list.set_intros(2) reachable_step.hyps(1))

    have *: "releasedAmount tokenDepositAddress token (stepsNoUpdate @ [I.UPDATE_step] @ stepsInit) +
             nonReleasedBurnsAmount tokenDepositAddress bridgeAddress token stepsInit (stepsNoUpdate @ [I.UPDATE_step] @ stepsInit) =
             burnedAmount bridgeAddress token stepsInit"
      using reachable_step.IH I'.InitFirstUpdateLastUpdate_axioms reachable_step.prems 
      by blast

    interpret LVS: InitUpdateBridgeNotDeadLastValidState where contractsUpdate'=contractsLastUpdate' and contractsUpdate=contractsLastUpdate and blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and contractsLVS=contracts' and stepsLVS=stepsNoUpdate
    proof
      show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
        by fact
    next
      show "reachable contractsLastUpdate contracts' stepsNoUpdate"
        by (metis I'.reachableLastUpdateLU I.Update_axioms Update.update prod.inject update)
    next
      show "lastValidStateTD contracts' tokenDepositAddress = (Success, stateRoot)"
        by (smt (verit) I'.LastUpdate_axioms I'.properSetupLU LastUpdateBridgeNotDead.intro LastUpdateBridgeNotDead.lastValidStateLU LastUpdateBridgeNotDead_axioms.intro assms lastValidStateI properSetup_def split_pairs)
    qed
    show ?thesis
      using * LVS.releasedAmountInvariantStep reachable_step.hyps
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
    using assms(2) reachableBridgeDead reachableLastUpdate'LU by blast

  have "tokenDepositBalance contractsLU token tokenDepositAddress + 
        releasedAmount tokenDepositAddress token stepsAllLU = 
        depositedAmount tokenDepositAddress token stepsAllLU"
    using InitFirstUpdate_LU.tokenDepositBalanceInvariant[OF assms(1)]
    using canceledAmountBridgeNotDead[OF reachableInitLU assms(2), of token]
    using withdrawnAmountBridgeNotDead[OF reachableInitLU assms(2), of token]
    by simp
  moreover
  have "nonBurnedClaimedBeforeAmount bridgeAddress token stepsInit + burnedAmount bridgeAddress token stepsInit =
        claimedBeforeDepositsAmount tokenDepositAddress bridgeAddress token stepsInit stepsAllLU"
    using InitFirstUpdate_LU.claimedBeforeDepositsAmountBridgeNotDead[of "stepsNoUpdate @ [UPDATE_step]" stepsInit token]
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
    using reachableUpdate'LVS assms InitUpdateBridgeNotDeadLastValidState_axioms
proof (induction contractsUpdate contractsLVS stepsLVS)
  case (reachable_base contracts)
  then show ?case
    by (simp add: UPDATE_step_def)
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then interpret I: InitUpdateBridgeNotDeadLastValidState where contractsLVS=contracts'' and contractsUpdate=contracts and stepsLVS="step # steps"
    by simp
  interpret I': InitUpdateBridgeNotDeadLastValidState where contractsLVS=contracts' and contractsUpdate=contracts and stepsLVS="steps"
    by (metis (no_types, lifting) HashProofVerifier.noUpdateGetLastValidStateTD HashProofVerifier.reachableDepositStateOracle HashProofVerifier_axioms I.InitUpdate_axioms I.Init_Update.stateOracleAddressTDI I.getLastValidStateLVS InitUpdateBridgeNotDeadLastValidState.intro InitUpdateBridgeNotDeadLastValidState_axioms.intro bridgeNotDead list.set_intros(1) reachable_step.hyps(1) reachable_step.hyps(2) reachable_step.prems(2))

  have *: "releasedAmount tokenDepositAddress token (steps @ [I.UPDATE_step]) = 0"
    using reachable_step.IH[OF reachable_step.prems(1) _] reachable_step.prems(2) I'.InitUpdateBridgeNotDeadLastValidState_axioms
    by (meson list.set_intros(2))

  then show ?case
  proof (cases step)
    case (RELEASE address' caller' ID' token' amount' proof')
    then show ?thesis
      using * I'.burnBeforeRelease reachable_step.prems(1) reachable_step.hyps
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
  using reachableContractsBD BridgeDeadInitFirstUpdate_axioms
  unfolding stepsAllBD_def
proof (induction contractsDead contractsBD stepsBD rule: reachable.induct)
  case (reachable_base contracts)
  show ?case
  proof (cases "stepsInit=[]")
    case True
    then show ?thesis
      using InitUpdateBridgeNotDeadLastValidState_Dead.stepsInitEmptyNoReleases
      by (smt (verit, ccfv_threshold) properSetup_stateOracleAddress Init_Update.stateOracleAddressTDI InitUpdateBridgeNotDeadLastValidState_Dead.stepsAllLVS_def Nat.add_0_right append.assoc append_Cons append_Nil burnedAmountNil noUpdate nonReleasedBurnsAmount_Nil properSetupUpdate set_ConsD stepDeathNoUpdate)
  next
    case False
    interpret I: InitFirstUpdateLastUpdate where contractsLU=contractsDead and stepsNoUpdate="stepDeath # stepsNoUpdate"
      by (metis False HashProofVerifier.InitFirstUpdateAxiomsInduction HashProofVerifier_axioms InitFirstUpdateLastUpdate.intro InitFirstUpdate_LastUpdate.InitFirstUpdate_axioms LastUpdate.intro LastUpdate_axioms.intro Update_axioms insert_iff list.set(2) noUpdate reachableInitI reachableLastUpdateDead reachableSingleton reachableUpdate'Update stepDeathNoUpdate)

    show ?thesis
      using I.releasedAmountInvariantBeforeDeath notBridgeDeadContractsLastUpdate' 
      unfolding I.stepsAllLU_def
      by auto
  qed
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then interpret BD: BridgeDeadInitFirstUpdate where contractsBD=contracts'' and contractsDead=contracts and stepsBD="step # steps"
    by simp
  interpret BD': BridgeDead where contractsBD=contracts' and contractsDead=contracts and stepsBD=steps
    by (metis BD.BridgeDead_axioms BridgeDead_axioms_def BridgeDead_def reachable_step.hyps(1))

  interpret BD'': BridgeDeadInitFirstUpdate where contractsBD=contracts' and contractsDead=contracts and stepsBD=steps
    by (metis (no_types, lifting) BD'.BridgeDead_axioms BD'.Init_BD.reachableInitI BD'.stepsAllBD_def BD.InitFirstUpdate_axioms BD.stepsAllBD_def BridgeDeadInitFirstUpdate.intro HashProofVerifier.InitFirstUpdateAxiomsInduction HashProofVerifier_axioms Nil_is_append_conv append_Cons list.distinct(1) reachable_step.hyps(2))

  note * = reachable_step.IH[OF BD''.BridgeDeadInitFirstUpdate_axioms]

  show ?case
    using * BD'.InitUpdateBridgeNotDeadLastValidState_BD.releasedAmountInvariantStep reachable_step.hyps
    unfolding BD'.InitUpdateBridgeNotDeadLastValidState_BD.stepsAllLVS_def
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
  using Init_BD.tokenDepositBalanceInvariant[of token]
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


lemma accountBalanceStepsOther:
  assumes "reachable contracts contracts' steps" 
          "\<forall> step \<in> set steps. \<not> isCaller caller step"
  shows "accountBalance contracts' (mintedTokenB contracts bridgeAddress token) caller = 
         accountBalance contracts (mintedTokenB contracts bridgeAddress token) caller + 
         transferredAmountTo bridgeAddress token caller steps"
  using assms
proof (induction contracts contracts' steps rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by simp
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  then show ?case
  proof (cases step)
    case (DEPOSIT address' caller' ID' token' amount')
    have "caller \<noteq> address'"
      sorry
    then show ?thesis
      using DEPOSIT reachable_step
      using callDepositBalanceOfOther callDepositOtherToken
      by (smt (z3) Step.simps(15) executeStep.simps(1) isCaller.simps(1) list.set_intros(1) list.set_intros(2) senderMessage transferAmountToConsOther)
  next
    case (CLAIM address' caller' ID' token' amount' proof')
    then show ?thesis
      using reachable_step
      using callClaimBalanceOfOther callClaimOtherToken
      by (smt (verit) Step.simps(27) executeStep.simps(2) isCaller.simps(2) list.set_intros(1) list.set_intros(2) senderMessage transferAmountToConsOther)
  next
    case (BURN address' caller' ID' token' amount')
    then show ?thesis
      using reachable_step
      using callWithdrawBalanceOfOther callWithdrawOtherToken
      by (smt (verit, best) executeStep.simps(3) Step.simps(38) isCaller.simps(3) list.set_intros(1) list.set_intros(2) local.reachable_step(2) senderMessage transferAmountToConsOther)
  next
    case (RELEASE address' caller' ID' token' amount' proof')
    have "caller \<noteq> address'"
      sorry
    then show ?thesis
      using RELEASE reachable_step
      using callReleaseBalanceOfOther callReleaseOtherToken
      by (smt (verit, best) Step.simps(45) executeStep.simps(4) isCaller.simps(4) list.set_intros(1) list.set_intros(2) senderMessage transferAmountToConsOther)
  next
    case (UPDATE address' stateRoot')
    then show ?thesis
      using reachable_step
      by simp
  next
    case (CANCEL_WD address' caller' ID' token' amount' proof')
    have "caller \<noteq> address'"
      sorry
    then show ?thesis
      using CANCEL_WD reachable_step
      using callCancelDepositWhileDeadBalanceOfOther callCancelDepositWhileDeadOtherToken 
      by (smt (verit, best) Step.simps(55) executeStep.simps(7) isCaller.simps(7) list.set_intros(1) list.set_intros(2) senderMessage transferAmountToConsOther)
  next
    case (WITHDRAW_WD address' caller' token' amount' proof')
    have "caller \<noteq> address'"
      sorry
    then show ?thesis
      using WITHDRAW_WD reachable_step
      using callWithdrawWhileDeadBalanceOfOther callWithdrawWhileDeadOtherToken 
      by (smt (verit, ccfv_SIG) Step.simps(57) executeStep.simps(8) isCaller.simps(8) list.set_intros(1) list.set_intros(2) senderMessage transferAmountToConsOther)
  next
    case (TRANSFER address' caller' receiver' token' amount')
    show ?thesis
    proof (cases "caller = receiver'")
      case True
      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token = token'")
        case True
        then show ?thesis
          using \<open>caller = receiver'\<close>
          using TRANSFER reachable_step
          using callTransferBalanceOfReceiver[of contracts' bridgeAddress caller' receiver' token' amount' contracts'' "mintedTokenB contracts' bridgeAddress token'"]
          by (smt (verit, best) HashProofVerifier.executeStep.simps(5) HashProofVerifier.reachableBridgeTokenPairs HashProofVerifier.reachableITokenPairs HashProofVerifier.transferredAmountToConsTransfer HashProofVerifier_axioms ab_semigroup_add_class.add_ac(1) add.commute list.set_intros(2))
      next
        case False
        then have "mintedTokenB contracts bridgeAddress token \<noteq> mintedTokenB contracts address' token'"
          sorry
        then show ?thesis
          using TRANSFER reachable_step
          using  callTransferOtherToken
          by (smt (verit, best) executeStep.simps(5) list.set_intros(2) reachableBridgeMintedToken transferredAmountToConsTransferOther)
      qed
    next
      case False
      then show ?thesis
        using TRANSFER reachable_step
        using callTransferOtherToken callTransferBalanceOfOther
        by (smt (verit, best) callTransferOtherToken executeStep.simps(5) isCaller.simps(5) list.set_intros(1) list.set_intros(2) transferredAmountToConsTransferOther)
    qed
  qed
qed

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
  assumes "reachable contracts contracts' steps"
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
  assumes "reachable contracts contracts' steps"
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

lemma canceledAmountFromBridgeDead:
  assumes "reachable contracts contracts' steps"  "\<not> bridgeDead contracts' tokenDepositAddress"
  shows "canceledAmountFrom tokenDepositAddress token caller steps = 0"
proof-
  have "cancelsFrom tokenDepositAddress token caller steps = []"
    using noCancelBeforeBridgeDead[OF assms]
    by (smt (verit, best) cancelsFrom_def filter_False isCancelFrom.elims(2))
  then show ?thesis
    unfolding canceledAmountFrom_def
    by simp
qed

(* ------------------------------------------------------------------------------------ *)

fun isWithdrawFrom where
  "isWithdrawFrom address token caller (WITHDRAW_WD address' caller' token' amount proof) \<longleftrightarrow> address' = address \<and> token' = token \<and> caller' = caller"
| "isWithdrawFrom address token caller _ = False"

definition withdrawalsFrom where
  "withdrawalsFrom tokenDepositAddress token caller steps = filter (isWithdrawFrom tokenDepositAddress token caller) steps"

lemma isWithdrawalWITHDRAWAL:
  assumes "isWithdrawFrom tokenDepositAddress token caller step"
  shows "\<exists> amount proof. step = WITHDRAW_WD tokenDepositAddress caller token amount proof"
  using assms
  by (cases step) auto

lemma withdrawalsFromWITHDRAWAL:
  assumes "step \<in> set (withdrawalsFrom tokenDepositAddress token caller steps)" 
  shows "\<exists> amount proof. step = WITHDRAW_WD tokenDepositAddress caller token amount proof"
  using assms isWithdrawalWITHDRAWAL
  unfolding withdrawalsFrom_def
  by auto

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

lemma withdrawnAmountFromBridgeDead:
  assumes "reachable contracts contracts' steps"  "\<not> bridgeDead contracts' tokenDepositAddress"
  shows "withdrawnAmountFrom tokenDepositAddress token caller steps = 0"
proof-
  have "withdrawalsFrom tokenDepositAddress token caller steps = []"
    using noWithdrawBeforeBridgeDead[OF assms]
    by (metis filter_False isWithdrawalWITHDRAWAL withdrawalsFrom_def)
  then show ?thesis
    unfolding withdrawnAmountFrom_def
    by simp
qed

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
  assumes "reachable contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
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
    by (metis Step.simps(19) assms(2) isCanceledID_def reachableInitI set_ConsD)
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
  assumes "reachable contractsI contractsDeposit [DEPOSIT tokenDepositAddress caller ID token amount]"
  shows "nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit
           (DEPOSIT tokenDepositAddress caller ID token amount # stepsInit) = 
         nonClaimedBeforeNonCanceledDepositsAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsInit + amount"
  using assms 
  by force

end

context InitUpdateBridgeNotDeadLastValidState
begin
lemma nonClaimedBeforeNonCanceledDepositsAmountToConsCancel [simp]:
  assumes "reachable contractsLVS contractsCancel [CANCEL_WD tokenDepositAddress caller ID token amount proof]"
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
    using Init_LVS.cancelDepositOnlyAfterDeposit reachableSingleton[OF assms]
    by (metis executeStep.simps(7) senderMessage)
  then have "?DEPOSIT_step \<in> set ?deposits"
    by (auto simp add: depositsTo_def)

  have reach: "reachable contractsInit contractsCancel (?CANCEL_step # stepsAllLVS)"
    using assms reachableInitLVS reachableTrans
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
      using distinctDepositsTo[OF reachableInitLVS] assms 
      by auto
  next
    show "?DEPOSIT_step \<in> set ?deposits"
      by fact
  next
    show "?P ?DEPOSIT_step stepsAllLVS"
      using CANCELNoDoubleCons[OF reach] assms(1)
      using cancelDepositWhileDeadNoClaim
      using reachableSingleton[OF assms]
      unfolding isCanceledID_def isClaimedID_def
      by (metis DEPOSIT_id.simps executeStep.simps(7))
  next
    show "\<forall> step \<in> set ?deposits. ?P step stepsAllLVS \<and> step \<noteq> ?DEPOSIT_step \<longleftrightarrow> ?P step (?CANCEL_step # stepsAllLVS)"
    proof safe
      fix step
      assume "step \<in> set ?deposits" "step \<noteq> DEPOSIT tokenDepositAddress caller ID token amount"
      then have "DEPOSIT_id step \<noteq> ID"
        using \<open>?DEPOSIT_step \<in> set ?deposits\<close> distinctDepositsToIDs[OF reachableInitLVS]
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
  assumes "reachable contractsI contractsCancel [CANCEL_WD address' caller' ID' token' amount' proof']"
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
        by (smt (verit) "*" Cons_eq_append_conv DEPOSIT_id.simps Step.simps(7) depositsSubsetSteps depositsToDEPOSIT depositsToSubsetDeposits in_mono isCanceledID_def onlyDepositorCanCancelSteps(1) reachable.simps reachableInitI reachableTrans set_ConsD)
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
  assumes "reachable contractsI contractsClaim [CLAIM address' caller' ID token' amount proof]"
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
      by (metis HashProofVerifier.reachableSingleton HashProofVerifier.reachable_step HashProofVerifier_axioms Init'_axioms Init.intro InitFirstUpdate_axioms.intro InitFirstUpdate_def Init_axioms.intro assms(2) firstUpdate last_ConsR list.discI reachableInitI stateRootInitNonZero)

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
  assumes "reachable contractsI contractsClaim [CLAIM bridgeAddress caller ID token amount proof]"
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
    using reachableSingleton[OF assms(1)]
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
      using distinctDepositsTo reachableInitI by blast
  next
    show "?DEPOSIT_step \<in> set ?deposits"
      by fact
  next
    show "?P ?DEPOSIT_step stepsInit"
    proof-
      have "\<not> isClaimedID bridgeAddress token ID stepsInit"
        using assms(1)
        by (metis (full_types) CLAIMNoDoubleCons Cons_eq_append_conv eq_Nil_appendI isClaimedID_def reachableInitI reachableTrans)
      moreover
      have "\<not> isCanceledID tokenDepositAddress token ID stepsInit"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain caller' amount' proof' where "CANCEL_WD tokenDepositAddress caller' ID token amount' proof' \<in> set stepsInit"
          unfolding isCanceledID_def
          by auto
        then have "bridgeDead contractsI tokenDepositAddress"
          using reachableInitI reachableNotBridgeDeadNoCancel 
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
        by (metis DEPOSIT_id.simps distinctDepositsToIDs distinct_map inj_on_def reachableInitI)
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

lemma burnsToConsBurn [simp]:
  shows "burnsTo bridgeAddress token caller (BURN bridgeAddress caller ID token amount # steps) = 
         BURN bridgeAddress caller ID token amount # burnsTo bridgeAddress token caller steps"
  by (simp add: burnsTo_def)

end

context StrongHashProofVerifier
begin

lemma distinctBurnsTo:
  assumes "reachable contracts contracts' steps"
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
  assumes "reachable contracts contracts' steps"
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


context InitFirstUpdate
begin

lemma nonReleasedBurnedAmountToConsBurnBefore [simp]:
  assumes "reachable contractsI contractsBurn [BURN bridgeAddress caller ID token amount]"
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller
         (BURN bridgeAddress caller ID token amount # stepsInit) stepsInit = 
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsInit + amount"
  using noReleaseBeforeBurn[OF _ assms]
  unfolding nonReleasedBurnedAmountTo_def nonReleasedBurnsTo_def
  by (auto simp add: isReleasedID_def)

end

context InitUpdateBridgeNotDeadLastValidState
begin

lemma nonReleasedBurnedAmountToConsRelease [simp]:
  assumes "reachable contractsLVS contractsRelease [RELEASE tokenDepositAddress caller ID token amount proof]"
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit
           (RELEASE tokenDepositAddress caller ID token amount proof # stepsAllLVS) + amount =
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit
           stepsAllLVS"
proof-
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller ID token amount proof"
  let ?BURN_step = "BURN bridgeAddress caller ID token amount"
  let ?burns = "burnsTo bridgeAddress token caller stepsInit"

  have "?BURN_step \<in> set stepsInit"
    using burnBeforeRelease[where msg="message caller 0"] reachableSingleton[OF assms]
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
      using distinctBurnsTo reachableInitI by blast
  next
    show "?BURN_step \<in> set ?burns"
      by fact
  next
    show "?P ?BURN_step stepsAllLVS"
      using RELEASENoDoubleCons[of contractsInit contractsRelease] reachableInitLVS assms(1) reachableTrans
      unfolding isReleasedID_def
      by (smt (verit) BURN_id.simps reachableSingleton reachable_step)
  next
    show "\<forall> step \<in> set ?burns. ?P step stepsAllLVS \<and> step \<noteq> ?BURN_step \<longleftrightarrow> ?P step (?RELEASE_step # stepsAllLVS)"
    proof safe
      fix step
      assume "step \<in> set ?burns" "step \<noteq> ?BURN_step"
      then have "BURN_id step \<noteq> ID"
        using \<open>?BURN_step \<in> set ?burns\<close>
        by (metis BURN_id.simps distinctBurnsToIDs distinct_map inj_on_def reachableInitI)
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
  assumes "reachable contractsI contractsRelease [RELEASE tokenDepositAddress caller' ID' token amount' proof']"
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore
           (RELEASE tokenDepositAddress caller' ID' token amount' proof' # stepsInit) =
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsBefore stepsInit"
proof-
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller' ID' token amount' proof'"
  let ?BURN_step = "BURN bridgeAddress caller' ID' token amount'"
  let ?burns = "burnsTo bridgeAddress token caller stepsBefore"

  have "?BURN_step \<in> set stepsInit"
    using assms(3)
    by (metis reachableSingleton burnBeforeRelease executeStep.simps(4) senderMessage)

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
        using BURNNoDoubleCTA[OF reachableInitI] \<open>step \<in> set ?burns\<close> assms(2) \<open>?BURN_step \<in> set stepsInit\<close>
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

lemma nonReleasedBurnedAmountToConsReleaseBefore:
  assumes "reachable contractsI contractsRelease [RELEASE tokenDepositAddress caller ID' token amount' proof']"
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit
            (RELEASE tokenDepositAddress caller ID' token amount' proof' # stepsInit) + amount' = 
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit stepsInit"
proof-
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller ID' token amount' proof'"
  let ?BURN_step = "BURN bridgeAddress caller ID' token amount'"
  let ?burns = "burnsTo bridgeAddress token caller stepsInit"

  have "?BURN_step \<in> set stepsInit"
    using burnBeforeRelease assms
    by (metis reachableSingleton  executeStep.simps(4) senderMessage)
  then have "?BURN_step \<in> set ?burns"
    unfolding burnsTo_def
    by simp

  let ?P = "\<lambda> step steps. \<not> isReleasedID tokenDepositAddress token (BURN_id step) steps"

  have "\<exists> steps1 steps2. 
        nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit 
           (?RELEASE_step # stepsInit) = steps1 @ steps2 \<and>
        nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
           stepsInit = steps1 @ [?BURN_step] @ steps2"
    unfolding nonReleasedBurnsTo_def
  proof (rule filter'')
    show "distinct ?burns"
      using distinctBurnsTo reachableInitI by blast
  next
    show "?BURN_step \<in> set ?burns"
      by fact
  next
    show "?P ?BURN_step stepsInit"
      using RELEASENoDoubleCons assms reachableInitI 
      unfolding isReleasedID_def
      by (metis BURN_id.simps reachableSingleton reachable_step)
  next
    show "\<forall> step \<in> set ?burns. ?P step stepsInit \<and> step \<noteq> ?BURN_step \<longleftrightarrow> ?P step (?RELEASE_step # stepsInit)"
    proof safe
      fix step
      assume "step \<in> set ?burns" "step \<noteq> ?BURN_step"
      then have "BURN_id step \<noteq> ID'"
        using \<open>?BURN_step \<in> set ?burns\<close>
        by (metis BURN_id.simps distinctBurnsToIDs distinct_map inj_on_def reachableInitI)
      assume "\<not> isReleasedID tokenDepositAddress token (BURN_id step) stepsInit"
             "isReleasedID tokenDepositAddress token (BURN_id step) (?RELEASE_step # stepsInit)"
      then show False
        using \<open>BURN_id step \<noteq> ID'\<close>
        by (auto simp add: isReleasedID_def)
    qed (auto simp add: isReleasedID_def)
  qed
  then show ?thesis
    unfolding nonReleasedBurnedAmountTo_def
    by auto
qed

lemma nonReleasedBurnedAmountToConsReleaseBeforeOtherCaller:
  assumes "caller \<noteq> caller'" 
  assumes "reachable contractsI contractsRelease [RELEASE tokenDepositAddress caller' ID' token amount' proof']"
  shows "nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit
            (RELEASE tokenDepositAddress caller' ID' token amount' proof' # stepsInit) =
         nonReleasedBurnedAmountTo tokenDepositAddress bridgeAddress token caller stepsInit
            stepsInit"
proof-
  let ?RELEASE_step = "RELEASE tokenDepositAddress caller' ID' token amount' proof'"
  let ?burns = "burnsTo bridgeAddress token caller stepsInit"
  let ?P = "\<lambda> step steps. \<not> isReleasedID tokenDepositAddress token (BURN_id step) steps"
  have "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
            (?RELEASE_step # stepsInit) =
        nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit
            stepsInit"
    unfolding nonReleasedBurnsTo_def
  proof (rule filter_cong)
    fix step
    assume "step \<in> set ?burns"
    show "?P step (?RELEASE_step # stepsInit) \<longleftrightarrow> ?P step stepsInit"
    proof-
    {
      assume *: "\<not> ?P step (?RELEASE_step # stepsInit)" "?P step stepsInit"
      then have "BURN_id step = ID'" 
       by (auto simp add: isReleasedID_def)
     moreover
     have "BURN bridgeAddress caller' ID' token amount' \<in> set stepsInit"
       by (metis assms(2) burnBeforeRelease executeStep.simps(4) reachableSingleton senderMessage)
     moreover
     obtain amount where "step = BURN bridgeAddress caller ID' token amount"
       using \<open>step \<in> set ?burns\<close> \<open>BURN_id step = ID'\<close>
       by (metis BURN_id.simps burnsToBURN)
     ultimately
     have "caller = caller'"
       using reachableInitI BURNNoDoubleCTA \<open>step \<in> set (burnsTo bridgeAddress token caller stepsInit)\<close>
       by (metis burnsTo_def filter_is_subset in_mono)
     then have False
       using \<open>caller \<noteq> caller'\<close>
       by simp
    } then show ?thesis
      by (auto simp add: isReleasedID_def)
    qed 
  qed auto
  then show ?thesis
    by (simp add: nonReleasedBurnedAmountTo_def)
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
  using reachableInitI assms InitFirstUpdate_axioms
proof (induction contractsInit contractsI stepsInit rule: reachable.induct)
  case (reachable_base contracts)
  then show ?case
    by (simp add: InitFirstUpdate_axioms_def InitFirstUpdate_def)
next
  case (reachable_step steps contracts'' contracts contracts' blockNum block step)
  interpret IFU: InitFirstUpdate where contractsInit=contracts and contractsI=contracts'' and stepsInit="step # steps"
    using reachable_step.prems
    by simp
  show ?case
  proof (cases "steps = []")
    case True
    then have step: "step = UPDATE (stateOracleAddressB contracts bridgeAddress) stateRootInit"
      using IFU.firstUpdate
      by simp

    have "accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller = 0"
      using \<open>steps = []\<close> reachable_step.hyps reachable.cases reachable_step.prems(2) 
      by blast
    then show ?thesis
      using reachable_step step \<open>steps = []\<close>
      by simp
  next
    case False
    then interpret IFU': InitFirstUpdate where contractsInit=contracts and contractsI=contracts' and stepsInit="steps"
      using InitFirstUpdateAxiomsInduction reachable_step.hyps(1) reachable_step.hyps(2) reachable_step.prems 
      by blast

    have notDead: "\<not> bridgeDead contracts' tokenDepositAddress"
      by (meson reachable.intros reachableBridgeDead reachable_step.hyps(2) reachable_step.prems(3))


    note * = reachable_step.IH[OF reachable_step.prems(1-2) notDead IFU'.InitFirstUpdate_axioms]
 
    show ?thesis
    proof (cases step)
      case (DEPOSIT address' caller' ID' token' amount')

      have "token' \<noteq> mintedTokenTD contracts tokenDepositAddress token"
        sorry
      then have AB:
        "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
         accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
        using callDepositOtherToken reachable_step.hyps DEPOSIT
        by (metis executeStep.simps(1))

      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token \<and> caller' = caller")
        case True
        then have "reachable contracts' contracts'' [DEPOSIT tokenDepositAddress caller ID' token amount']"
          by (metis DEPOSIT reachable.simps reachable_step.hyps(2))
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
        using * reachable_step.hyps
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
          using TRANSFER reachable_step.hyps callTransferOtherToken[of contracts' address' caller' receiver' token' amount' contracts'' "mintedTokenB contracts' address' token'" "mintedTokenTD contracts tokenDepositAddress token"]
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
            using TRANSFER reachable_step.hyps
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
              using TRANSFER reachable_step.hyps
              by (metis IFU'.mintedTokenBI IFU.mintedTokenITDB executeStep.simps(5))

            then show ?thesis
              using * \<open>caller = receiver'\<close> \<open>caller' \<noteq> receiver'\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> TRANSFER
              by simp
          next
            case False
            have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller =
                  accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
              using \<open>caller' \<noteq> caller\<close> \<open>caller \<noteq> receiver'\<close> 
              using IFU'.reachableInitI IFU.mintedTokenITDB TRANSFER True callTransferBalanceOfOther 
              by (smt (verit, ccfv_threshold) reachableBridgeTokenPairs reachableITokenPairs executeStep.simps(5) reachable_step.hyps(2))
            then show ?thesis
              using * \<open>caller \<noteq> receiver'\<close> \<open>caller' \<noteq> caller\<close> \<open>caller' \<noteq> receiver'\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> TRANSFER
              by simp
          qed
        qed
      qed
    next
      case (CLAIM address' caller' ID' token' amount' proof')
      
      have reachClaim: 
        "reachable contracts' contracts'' [CLAIM address' caller' ID' token' amount' proof']"
        using CLAIM reachable.reachable_step reachable_base reachable_step.hyps(2)
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
            using True CLAIM callClaimBalanceOfOther[of contracts' address' "message caller' amount'"] reachable_step.hyps
            using IFU'.mintedTokenBI IFU.mintedTokenITDB
            by auto
        next
          case False
          then have "mintedTokenTD contracts tokenDepositAddress token \<noteq> mintedTokenB contracts address' token'"
            sorry
          then show ?thesis
            using callClaimOtherToken[of contracts' address' "message caller' amount'"] reachable_step.hyps CLAIM
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
          using True callClaimBalanceOfMinted[of contracts' address' "message caller' amount'" ID' token' amount' proof' contracts''] reachable_step.hyps CLAIM
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
      show ?thesis
      proof (cases "address' = bridgeAddress \<and> token' = token")
        case True
        show ?thesis
        proof (cases "caller = caller'")
          case True
          then have r: "reachable contracts' contracts'' [BURN bridgeAddress caller ID' token amount']"
            using reachable_step.hyps \<open>address' = bridgeAddress \<and> token' = token\<close> 
            using BURN reachable.reachable_step reachable_base 
            by blast
          have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller' + amount' = 
                accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller'"
            using callWithdrawBalanceOfSender[of contracts' address' "message caller' 0" ID' token' amount' contracts'']
            using BURN reachable_step.hyps \<open>address' = bridgeAddress \<and> token' = token\<close> \<open>caller = caller'\<close> 
            by (metis (no_types, lifting) IFU.mintedTokenITDB executeStep.simps(3) le_add_diff_inverse2 reachableBridgeTokenPairs reachableITokenPairs senderMessage)
          then show ?thesis
            using * \<open>caller = caller'\<close> \<open>address' = bridgeAddress \<and> token' = token\<close> BURN
            using IFU'.nonReleasedBurnedAmountToConsBurnBefore[OF r]
            by auto
        next
          case False
          have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller =
                accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
            using \<open>caller \<noteq> caller'\<close> \<open>address' = bridgeAddress \<and> token' = token\<close>
            using callWithdrawBalanceOfOther[of contracts' bridgeAddress "message caller' 0" ID' token' amount' contracts'' caller] BURN reachable_step.hyps
            by (metis IFU'.mintedTokenBI IFU.mintedTokenITDB executeStep.simps(3) senderMessage)
          then show ?thesis
            using \<open>caller \<noteq> caller'\<close> \<open>address' = bridgeAddress \<and> token' = token\<close>
            using * BURN
            by simp
        qed
      next
        case False
        have "mintedTokenTD contracts tokenDepositAddress token \<noteq>  mintedTokenB contracts address' token'"
          sorry
        then have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
                   accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
          using callWithdrawOtherToken[where token' = "mintedTokenTD contracts tokenDepositAddress token"] reachable_step.hyps BURN
          by (metis executeStep.simps(3) reachableBridgeMintedToken)
        then show ?thesis
          using False BURN *
          by auto
      qed
    next
      case (RELEASE address' caller' ID' token' amount' proof')
      show ?thesis
      proof (cases "address' = tokenDepositAddress \<and> token' = token")
        case False
        have minted: "mintedTokenTD contracts tokenDepositAddress token \<noteq> token'"
          sorry
        have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
              accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
          using callReleaseOtherToken[OF minted]
          by (metis RELEASE executeStep.simps(4) reachable_step.hyps(2))
        then show ?thesis
          using False RELEASE *
          by auto
      next
        case True
        show ?thesis
        proof (cases "caller' = caller")
          case False
          have r: "reachable contracts' contracts'' [RELEASE tokenDepositAddress caller' ID' token amount' proof']"
            using RELEASE reachable_step.hyps
            using True \<open>address' = tokenDepositAddress \<and> token' = token\<close>
            using reachable.reachable_step reachable_base 
            by blast

          have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
                accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
            using \<open>address' = tokenDepositAddress \<and> token' = token\<close> RELEASE reachable_step.hyps
            by (metis (no_types, lifting) HashProofVerifier.callReleaseOtherToken HashProofVerifier.properToken_def HashProofVerifier_axioms IFU.mintedTokenITDB executeStep.simps(4) reachable_step.prems(1))
          then show ?thesis
            using True \<open>caller' \<noteq> caller\<close> RELEASE * \<open>caller' \<noteq> caller\<close>
            using IFU'.nonReleasedBurnedAmountToConsReleaseBeforeOtherCaller[OF _ r] 
            by auto
        next
          case True
          have r: "reachable contracts' contracts'' [RELEASE tokenDepositAddress caller ID' token amount' proof']"
            using RELEASE reachable_step.hyps
            using True \<open>address' = tokenDepositAddress \<and> token' = token\<close> \<open>caller' = caller\<close>
            using reachable.reachable_step reachable_base by blast
          have "mintedTokenTD contracts tokenDepositAddress token \<noteq> token"
            sorry
          then have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
                accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
            using RELEASE reachable_step.hyps  callReleaseOtherToken
            by (metis IFU.mintedTokenITDB executeStep.simps(4) r reachableSingleton)
          then show ?thesis
            using True \<open>address' = tokenDepositAddress \<and> token' = token\<close> \<open>caller' = caller\<close> RELEASE *
            using IFU'.nonReleasedBurnedAmountToConsReleaseBefore[OF r]
            by auto
        qed
      qed
    next
      case (CANCEL_WD address' caller' ID' token' amount' proof')
      show ?thesis
      proof (cases "address' = tokenDepositAddress")
        case True
        then have False
          using reachable_step.hyps callCancelDepositWhileDeadBridgeDead[of contracts' tokenDepositAddress "message caller' 0"] reachable_step.prems
          by (metis CANCEL_WD executeStep.simps(7))
        then show ?thesis
          by simp
      next
        case False
        have "mintedTokenTD contracts tokenDepositAddress token \<noteq> token'"
          sorry
        then have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
                   accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
          using callCancelDepositWhileDeadOtherToken[where token'="mintedTokenTD contracts tokenDepositAddress token" and token=token']
          using reachable_step.hyps CANCEL_WD
          by (metis executeStep.simps(7))
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
          by (metis noWithdrawBeforeBridgeDead IFU'.reachableInitI WITHDRAW_WD list.set_intros(1) reachable.reachable_step reachable_step.hyps(2) reachable_step.prems(3))
        then show ?thesis
          by simp
      next
        case False
        have "mintedTokenTD contracts tokenDepositAddress token \<noteq> token'"
          sorry
        then have "accountBalance contracts'' (mintedTokenTD contracts tokenDepositAddress token) caller = 
              accountBalance contracts' (mintedTokenTD contracts tokenDepositAddress token) caller"
          using callWithdrawWhileDeadOtherToken[where token'="mintedTokenTD contracts tokenDepositAddress token" and token=token']
          using reachable_step.hyps WITHDRAW_WD
          by (metis executeStep.simps(8))
        then show ?thesis
          using False WITHDRAW_WD *
          by simp
      qed
    qed
  qed
qed

end

locale InitFirstUpdateBridgeNotDeadLastValidState = 
  InitUpdateBridgeNotDeadLastValidState + 
  InitFirstUpdate where contractsI=contractsUpdate and stepsInit="UPDATE_step # stepsInit"

sublocale InitFirstUpdateBridgeNotDeadLastValidState \<subseteq> InitFirstUpdate_LVS: InitFirstUpdate where contractsI=contractsLVS and stepsInit=stepsAllLVS
  by (metis InitFirstUpdate_axioms.intro InitFirstUpdate_def Init_LVS.Init_axioms append_Cons append_eq_append_conv2 append_is_Nil_conv firstUpdate last_appendR stateRootInitNonZero stepsAllLVS_def)

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
    have r: "reachable contractsLVS contracts [DEPOSIT tokenDepositAddress caller ID' token amount']"
      using assms True
      by (metis DEPOSIT HashProofVerifier.reachable_base HashProofVerifier.reachable_step HashProofVerifier_axioms)
    show ?thesis
      using True DEPOSIT * assms InitFirstUpdate_LVS.nonClaimedBeforeNonCanceledDepositsAmountToConsDeposit[of "stepsLVS @ [UPDATE_step]" stepsInit, OF _ r]
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
   have r: "reachable contractsLVS contracts [RELEASE tokenDepositAddress caller' ID' token amount' proof']"
      using RELEASE
      using True assms reachable_base reachable_step 
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
        using \<open>address' = tokenDepositAddress \<and> token' = token\<close> * RELEASE assms InitFirstUpdate_LVS.nonReleasedBurnedAmountToConsReleaseOther[OF False _ r, of "stepsLVS @ [UPDATE_step]" stepsInit]
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

  have r: "reachable contractsLVS contracts [CANCEL_WD address' caller' ID' token' amount' proof']"
    using assms
    using CANCEL_WD reachable_base reachable_step 
    by blast

  show ?thesis
  proof (cases "address' = tokenDepositAddress \<and> token' = token \<and> caller' = caller")
    case True
    then have r: "reachable contractsLVS contracts [CANCEL_WD tokenDepositAddress caller ID' token amount' proof']"
      using r by simp
    show ?thesis
      using True * CANCEL_WD nonClaimedBeforeNonCanceledDepositsAmountToConsCancel[OF r] assms
      by simp
  next
    case False
    then show ?thesis
      using * assms CANCEL_WD Init_LVS.nonClaimedBeforeNonCanceledDepositsAmountToConsCancelOther[OF r, of "stepsLVS @ [UPDATE_step]" stepsInit]
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
      by (metis Init_LVS.mintedTokenTDI callWithdrawWhileDeadVerifyBalanceProof senderMessage)
    then have vbp: "verifyBalanceProof () (mintedTokenTD contractsInit tokenDepositAddress token) caller amount'
               stateRoot proof' = True"
      by (metis getLastValidStateLVS snd_conv)
    have "accountBalance contractsUpdate' (mintedTokenTD contractsInit tokenDepositAddress token) caller = amount'"
      using verifyBalanceProofE[OF generateStateRootUpdate' vbp] assms
      by (metis ERC20StateMintedTokenINotNone callUpdateIERC20 option.collapse update)
    then have "nonWithdrawnBalanceBefore tokenDepositAddress bridgeAddress caller token contractsUpdate' contractsLVS = amount'"
      by (metis callUpdateIBridge callUpdateITokenPairs callWD callWithdrawWhileDeadNotTokenWithdrawn mintedTokenITDB nonWithdrawnBalanceBefore_def reachableBridgeTokenPairs reachableITokenPairs reachableInitLastUpdate senderMessage update)
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

lemma userTokensInvariant:
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
         transferredAmountTo bridgeAddress token caller stepsInit" (is "?inv contractsBD stepsAllBD")
proof-
  have notBridgeDeadLastUpdate: "\<not> bridgeDead contractsLastUpdate tokenDepositAddress"
    using callUpdateDeadState notBridgeDeadContractsLastUpdate' update by presburger

  have "accountBalance contractsLastUpdate (mintedTokenTD contractsInit tokenDepositAddress token) caller = 
        accountBalance contractsLastUpdate' (mintedTokenTD contractsInit tokenDepositAddress token) caller"
    using callUpdateIERC20 update by presburger
  then have invLastUpdate: "?inv contractsLastUpdate ([UPDATE_step] @ stepsInit)"
    using InitFirstUpdate_LastUpdate.userTokensInvariantBase[OF assms notBridgeDeadLastUpdate]
    using Init_Update.nonWithdrawnBalanceBeforeBridgeNotDead[OF notBridgeDeadLastUpdate] mintedTokenITDB
    by (simp add: UPDATE_step_def)

  interpret IFULVSDead': InitFirstUpdateBridgeNotDeadLastValidState where
    contractsUpdate'=contractsLastUpdate' and contractsUpdate=contractsLastUpdate and
    blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and
    contractsLVS=contractsDead' and stepsLVS="stepsNoUpdate"
    by unfold_locales

  have invDead': "?inv contractsDead' (stepsNoUpdate @ [UPDATE_step] @ stepsInit)"
    using reachableLastUpdateLU IFULVSDead'.InitFirstUpdateBridgeNotDeadLastValidState_axioms invLastUpdate noUpdate
  proof (induction contractsLastUpdate contractsDead' stepsNoUpdate)
    case (reachable_base contractsLastUpdate)
    then show ?case
      using reachable_base.prems
      by simp
  next
    case (reachable_step steps contracts'' contracts contracts' blockNum block step)
    then interpret I: InitFirstUpdateBridgeNotDeadLastValidState where 
      contractsUpdate'=contractsLastUpdate' and contractsUpdate=contracts and 
      blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and contractsLVS=contracts'' and stepsLVS="step # steps"
      by simp
    interpret II: InitUpdateBridgeNotDeadLastValidState where 
      contractsUpdate'=contractsLastUpdate' and contractsUpdate=contracts and 
      blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and contractsLVS=contracts' and stepsLVS="steps"
    proof
      show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
        using notBridgeDeadContractsLastUpdate' by blast
    next
      show "reachable contracts contracts' steps"        
        by (simp add: reachable_step.hyps(1))
    next
      have "lastValidStateTD contracts'' tokenDepositAddress = (Success, stateRoot)"
        using I.getLastValidStateLVS by fastforce
      moreover
      have "\<nexists> stateRoot'. step = UPDATE (stateOracleAddressB contractsInit bridgeAddress) stateRoot'"
        using reachable_step.prems
        by auto
      ultimately show "lastValidStateTD contracts' tokenDepositAddress = (Success, stateRoot)"
        using reachable_step.hyps(2) 
        by (metis (no_types, lifting) HashProofVerifier.properSetup_stateOracleAddress HashProofVerifier.reachableDepositStateOracle HashProofVerifier_axioms I.Init_LVS.properSetupI I.Init_LVS.stateOracleAddressBI I.Init_LVS.stateOracleAddressTDI I.Init_Update.stateOracleAddressTDI noUpdateGetLastValidStateTD reachable_step.hyps(1))
    qed
    interpret I': InitFirstUpdateBridgeNotDeadLastValidState where 
      contractsUpdate'=contractsLastUpdate' and contractsUpdate=contracts and 
      blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and contractsLVS=contracts' and stepsLVS="steps"
      by (simp add: I.InitFirstUpdate_axioms II.InitUpdateBridgeNotDeadLastValidState_axioms InitFirstUpdateBridgeNotDeadLastValidState_def)

    have "?inv contracts' (steps @ [I.UPDATE_step] @ stepsInit)"
      using reachable_step.IH
      by (meson I'.InitFirstUpdateBridgeNotDeadLastValidState_axioms list.set_intros(2) reachable_step.prems(2) reachable_step.prems(3))
    then show ?case
      using I'.accountBalanceInvariantStep
      using II.stepsAllLVS_def assms(1) reachable_step.hyps(2) 
      by force
  qed

  have invDead: "?inv contractsDead (stepDeath # stepsNoUpdate @ [UPDATE_step] @ stepsInit)"
    using invDead' 
    by (metis IFULVSDead'.accountBalanceInvariantStep InitUpdateBridgeNotDeadLastValidState_Dead'.stepsAllLVS_def assms(1) deathStep reachableSingleton)

  interpret IFULVSBD: InitFirstUpdateBridgeNotDeadLastValidState where
    contractsUpdate'=contractsLastUpdate' and contractsUpdate=contractsLastUpdate and
    blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and
    contractsLVS=contractsBD and stepsLVS="stepsBD @ [stepDeath] @ stepsNoUpdate"
    by unfold_locales

  have "reachable contractsLastUpdate contractsDead (stepDeath # stepsNoUpdate)"
    by simp
  show ?thesis
    using reachableContractsBD invDead IFULVSBD.InitFirstUpdateBridgeNotDeadLastValidState_axioms bridgeDead \<open>reachable contractsLastUpdate contractsDead (stepDeath # stepsNoUpdate)\<close>
    unfolding stepsAllBD_def
  proof (induction contractsDead contractsBD stepsBD rule: reachable.induct)
    case (reachable_base contracts)
    then show ?case
      by simp
  next
    case (reachable_step steps contracts'' contracts contracts' blockNum block step)
    interpret I: InitFirstUpdateBridgeNotDeadLastValidState where 
      contractsUpdate'=contractsLastUpdate' and contractsUpdate=contractsLastUpdate and 
      blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and contractsLVS=contracts'' and stepsLVS="step # steps @ [stepDeath] @ stepsNoUpdate"
      using reachable_step.prems(2)
      by simp
    interpret II: InitUpdateBridgeNotDeadLastValidState where 
      contractsUpdate'=contractsLastUpdate' and contractsUpdate=contractsLastUpdate and 
      blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and contractsLVS=contracts' and stepsLVS="steps @ [stepDeath] @ stepsNoUpdate"
    proof
      show "\<not> bridgeDead contractsLastUpdate' tokenDepositAddress"
        using notBridgeDeadContractsLastUpdate' by blast
    next
      show "reachable contractsLastUpdate contracts' (steps @ [stepDeath] @ stepsNoUpdate)"
        using reachableTrans reachable_step.hyps(1) reachable_step.prems(4) by force
    next
      show "lastValidStateTD contracts' tokenDepositAddress = (Success, stateRoot)"
        by (smt (verit, ccfv_SIG) HashProofVerifier.reachableDeadState HashProofVerifier.reachable_step HashProofVerifier_axioms I.getLastValidStateLVS lastValidState_def reachable_step.hyps(1) reachable_step.hyps(2) reachable_step.prems(3))
    qed

    interpret I': InitFirstUpdateBridgeNotDeadLastValidState where 
      contractsUpdate'=contractsLastUpdate' and contractsUpdate=contractsLastUpdate and 
      blockUpdate=blockLastUpdate and blockNumUpdate=blockNumLastUpdate and contractsLVS=contracts' and stepsLVS="steps @ [stepDeath] @ stepsNoUpdate"
      by (meson II.InitUpdateBridgeNotDeadLastValidState_axioms InitFirstUpdateBridgeNotDeadLastValidState.intro InitFirstUpdate_LastUpdate.InitFirstUpdate_axioms)
    have "?inv contracts' (steps @ [stepDeath] @ stepsNoUpdate @ [UPDATE_step] @ stepsInit)"
      using reachable_step.IH
      using I'.InitFirstUpdateBridgeNotDeadLastValidState_axioms reachable_step.prems(1) reachable_step.prems(3) reachable_step.prems(4) by blast
    then show ?case
      using I'.accountBalanceInvariantStep
      using II.stepsAllLVS_def assms(1) reachable_step.hyps(2) 
      by force
  qed
qed

end


context HashProofVerifier
begin

lemma depositsToAppend [simp]:
  shows "depositsTo tokenDepositAddres token caller (steps1 @ steps2) = 
         depositsTo tokenDepositAddres token caller steps1 @ 
         depositsTo tokenDepositAddres token caller steps2"
  by (auto simp add: depositedAmountTo_def depositsTo_def)

lemma depositedAmountToAppend [simp]:
  shows "depositedAmountTo tokenDepositAddres token caller (steps1 @ steps2) = 
         depositedAmountTo tokenDepositAddres token caller steps1 + 
         depositedAmountTo tokenDepositAddres token caller steps2"
  by (auto simp add: depositedAmountTo_def depositsTo_def)

lemma burnsToAppend [simp]:
  shows "burnsTo tokenDepositAddres token caller (steps1 @ steps2) = 
         burnsTo tokenDepositAddres token caller steps1 @ 
         burnsTo tokenDepositAddres token caller steps2"
  by (auto simp add: burnsTo_def)

lemma transferredAmountFromAppend [simp]:
  shows "transferredAmountFrom bridgeAddress token caller (steps1 @ steps2) = 
         transferredAmountFrom bridgeAddress token caller steps1 + 
         transferredAmountFrom bridgeAddress token caller steps2"
  by (auto simp add: transferredAmountFrom_def)

lemma transferredAmountToAppend [simp]:
  shows "transferredAmountTo bridgeAddress token caller (steps1 @ steps2) = 
         transferredAmountTo bridgeAddress token caller steps1 + 
         transferredAmountTo bridgeAddress token caller steps2"
  by (auto simp add: transferredAmountTo_def)

lemma releasedAmountFromAppend [simp]:
  shows "releasedAmountFrom tokenDepositAddres token caller (steps1 @ steps2) = 
         releasedAmountFrom tokenDepositAddres token caller steps1 + 
         releasedAmountFrom tokenDepositAddres token caller steps2"
  by (auto simp add: releasedAmountFrom_def releasesFrom_def)

lemma withdrawnAmountFromAppend [simp]:
  shows "withdrawnAmountFrom tokenDepositAddres token caller (steps1 @ steps2) = 
         withdrawnAmountFrom tokenDepositAddres token caller steps1 + 
         withdrawnAmountFrom tokenDepositAddres token caller steps2"
  by (auto simp add: withdrawnAmountFrom_def withdrawalsFrom_def)

lemma canceledAmountFromAppend [simp]:
  shows "canceledAmountFrom tokenDepositAddres token caller (steps1 @ steps2) = 
         canceledAmountFrom tokenDepositAddres token caller steps1 + 
         canceledAmountFrom tokenDepositAddres token caller steps2"
  by (auto simp add: canceledAmountFrom_def cancelsFrom_def)

lemma paidBackAmountFromAppend [simp]:
  shows "paidBackAmountFrom tokenDepositAddres token caller (steps1 @ steps2) = 
         paidBackAmountFrom tokenDepositAddres token caller steps1 + 
         paidBackAmountFrom tokenDepositAddres token caller steps2"
  by (simp add: paidBackAmountFrom_def)

lemma paidBackAmountFromCons:
  shows "paidBackAmountFrom tokenDepositAddres token caller (step # steps) = 
         paidBackAmountFrom tokenDepositAddres token caller [step] + 
         paidBackAmountFrom tokenDepositAddres token caller steps"
  by (metis append.left_neutral append_Cons paidBackAmountFromAppend)
end


context HashProofVerifier
begin

lemma noIsStepCallerDepositsTo:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "depositsTo tokenDepositAddress token caller steps = []"
  using assms
  by (metis depositsTo_def filter_False isDepositToDEPOSIT isCaller.simps(1))

lemma noIsStepCallerDepositedAmountTo:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "depositedAmountTo tokenDepositAddress token caller steps = 0"
  using noIsStepCallerDepositsTo[OF assms]
  by (simp add: depositedAmountTo_def)

lemma noIsStepCallerBurnsTo:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "burnsTo bridgeAddress token caller steps = []"
  using assms
  by (metis burnsTo_def filter_False isBurnToStep isCaller.simps(3))

lemma noIsStepCallerTransferredAmountFrom:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "transferredAmountFrom brudgeAddress token caller steps = 0"
  using assms
  unfolding transferredAmountFrom_def
  by (metis filter_False isCaller.simps(5) isTransferFrom.elims(2) list.simps(8) sum_list.Nil)

lemma noIsStepCallerReleasesFrom:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "releasesFrom tokenDepositAddress token caller steps = []"
  using assms
  unfolding releasesFrom_def
  by (smt (verit, ccfv_SIG) filter_False isReleaseFrom.elims(2) isCaller.simps(4))

lemma noIsStepCallerReleasedAmountFrom:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "releasedAmountFrom tokenDepositAddress token caller steps = 0"
  using assms
  by (simp add: noIsStepCallerReleasesFrom releasedAmountFrom_def)

lemma noIsStepCallerWithdrawalsFrom:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "withdrawalsFrom tokenDepositAddress token caller steps = []"
  using assms
  unfolding withdrawalsFrom_def
  by (metis filter_False isCaller.simps(8) isWithdrawFrom.elims(2))

lemma noIsStepCallerWithdrawnAmountFrom:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "withdrawnAmountFrom tokenDepositAddress token caller steps = 0"
  using assms
  by (simp add: noIsStepCallerWithdrawalsFrom withdrawnAmountFrom_def)

lemma noIsStepCallerCancelsFrom:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "cancelsFrom tokenDepositAddress token caller steps = []"
  using assms
  unfolding cancelsFrom_def
  by (smt (verit) filter_False isCancelFrom.elims(2) isCaller.simps(7))

lemma noIsStepCallerCanceledAmountFrom:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "canceledAmountFrom tokenDepositAddress token caller steps = 0"
  using assms
  by (simp add: noIsStepCallerCancelsFrom canceledAmountFrom_def)

lemma noIsStepCallerPaidBackAmountFrom:
  assumes "\<nexists> step. step \<in> set steps \<and> isCaller caller step"
  shows "paidBackAmountFrom tokenDepositAddress token caller steps = 0"
  using assms
  unfolding paidBackAmountFrom_def
  by (simp add: noIsStepCallerCanceledAmountFrom noIsStepCallerReleasedAmountFrom noIsStepCallerWithdrawnAmountFrom)  

lemma depositedAmountToInterleaveSteps:
  assumes "length steps = length stepssOther"
  shows "depositedAmountTo tokenDepositAddress token caller (interleaveSteps steps stepssOther) = 
         depositedAmountTo tokenDepositAddress token caller steps +
         depositedAmountTo tokenDepositAddress token caller (concat stepssOther)"
  using assms
proof (induction steps arbitrary: stepssOther)
  case Nil
  then show ?case
    by simp
next
  let ?D = "\<lambda> steps. depositedAmountTo tokenDepositAddress token caller steps"
  case (Cons step steps)
  then obtain stepsOther stepssOther' where *: "stepssOther = stepsOther # stepssOther'"
    by (meson in_set_impl_in_set_zip1 list.set_cases list.set_intros(1) set_zip_rightD)
  then have "?D(interleaveSteps (step # steps) stepssOther) = 
             ?D (interleaveSteps (step # steps) (stepsOther # stepssOther'))"
    by simp
  also have "\<dots> = ?D (step # stepsOther @ interleaveSteps steps stepssOther')"
    by auto
  also have "\<dots> = ?D (step # stepsOther) + ?D (interleaveSteps steps stepssOther')"
    by (metis append_Cons depositedAmountToAppend)
  also have "\<dots> = ?D (step # stepsOther) + ?D steps + ?D (concat stepssOther')"
    using Cons.IH[of stepssOther'] Cons.prems *
    by simp
  also have "\<dots> = ?D (step # steps) + ?D stepsOther + ?D (concat stepssOther')"
    by (smt (verit, best) add.commute add.left_commute depositedAmountToConsDeposit depositedAmountToConsOther)
  finally show ?case
    using * depositedAmountTo_def depositsTo_def 
    by auto
qed

lemma depositedAmountToInterleaveStepsOther:
  assumes "\<nexists> step. step \<in> set (concat stepssOther) \<and> isCaller caller step"
  assumes "length steps = length stepssOther"
  shows "depositedAmountTo tokenDepositAddress token caller (interleaveSteps steps stepssOther) = 
         depositedAmountTo tokenDepositAddress token caller steps"
  using depositedAmountToInterleaveSteps[OF assms(2)] assms(1) noIsStepCallerDepositedAmountTo
  by presburger

lemma depositsToInterleaveStepsOther:
  assumes "\<nexists> step. step \<in> set (concat stepssOther) \<and> isCaller caller step"
  assumes "length steps = length stepssOther"
  shows "depositsTo tokenDepositAddress token caller (interleaveSteps steps stepssOther) = 
         depositsTo tokenDepositAddress token caller steps"
  using assms
proof (induction steps arbitrary: stepssOther)
  case Nil
  then show ?case
    by simp
next
  let ?D = "\<lambda> steps. depositsTo tokenDepositAddress token caller steps"
  case (Cons step steps)
  then obtain stepsOther stepssOther' where *: "stepssOther = stepsOther # stepssOther'"
    by (meson in_set_impl_in_set_zip1 list.set_cases list.set_intros(1) set_zip_rightD)
  then have "?D(interleaveSteps (step # steps) stepssOther) = 
             ?D (interleaveSteps (step # steps) (stepsOther # stepssOther'))"
    by simp
  also have "\<dots> = ?D (step # stepsOther @ interleaveSteps steps stepssOther')"
    by auto
  also have "\<dots> = ?D (step # stepsOther) @ ?D (interleaveSteps steps stepssOther')"
    by (metis append_Cons depositsToAppend)
  also have "\<dots> = ?D (step # stepsOther) @ ?D steps "
    using Cons.IH[of stepssOther'] Cons.prems *
    by auto
  also have "\<dots> = ?D [step] @ ?D stepsOther @ ?D steps"
    by (metis append_eq_Cons_conv depositsToAppend eq_Nil_appendI)
  also have "\<dots> = ?D [step] @ ?D steps"
    using Cons.prems(1) * noIsStepCallerDepositsTo
    by fastforce
  finally show ?case
    using * depositedAmountTo_def depositsTo_def 
    by auto
qed

lemma burnsToInterleaveStepsOther:
  assumes "\<nexists> step. step \<in> set (concat stepssOther) \<and> isCaller caller step"
  assumes "length steps = length stepssOther"
  shows "burnsTo bridgeAddress token caller (interleaveSteps steps stepssOther) = 
         burnsTo bridgeAddress token caller steps"
  using assms
proof (induction steps arbitrary: stepssOther)
  case Nil
  then show ?case
    by simp
next
  let ?B = "\<lambda> steps. burnsTo bridgeAddress token caller steps"
  case (Cons step steps)
  then obtain stepsOther stepssOther' where *: "stepssOther = stepsOther # stepssOther'"
    by (meson in_set_impl_in_set_zip1 list.set_cases list.set_intros(1) set_zip_rightD)
  then have "?B(interleaveSteps (step # steps) stepssOther) = 
             ?B (interleaveSteps (step # steps) (stepsOther # stepssOther'))"
    by simp
  also have "\<dots> = ?B (step # stepsOther @ interleaveSteps steps stepssOther')"
    by auto
  also have "\<dots> = ?B (step # stepsOther) @ ?B (interleaveSteps steps stepssOther')"
    by (metis append_Cons burnsToAppend)
  also have "\<dots> = ?B (step # stepsOther) @ ?B steps "
    using Cons.IH[of stepssOther'] Cons.prems *
    by auto
  also have "\<dots> = ?B [step] @ ?B stepsOther @ ?B steps"
    by (metis append_eq_Cons_conv burnsToAppend eq_Nil_appendI)
  also have "\<dots> = ?B [step] @ ?B steps"
    using Cons.prems(1) * noIsStepCallerBurnsTo
    by fastforce
  finally show ?case
    using * burnsTo_def 
    by auto
qed

lemma paidBackAmountFromInterleaveSteps:
  assumes "length steps = length stepssOther"
  shows "paidBackAmountFrom tokenDepositAddress token caller (interleaveSteps steps stepssOther) = 
         paidBackAmountFrom tokenDepositAddress token caller steps +
         paidBackAmountFrom tokenDepositAddress token caller (concat stepssOther)"
  using assms
proof (induction steps arbitrary: stepssOther)
  case Nil
  then show ?case
    by (simp add: paidBackAmountFrom_def)
next
  let ?P = "\<lambda> steps. paidBackAmountFrom tokenDepositAddress token caller steps"
  case (Cons step steps)
  then obtain stepsOther stepssOther' where *: "stepssOther = stepsOther # stepssOther'"
    by (meson in_set_impl_in_set_zip1 list.set_cases list.set_intros(1) set_zip_rightD)
  then have "?P (interleaveSteps (step # steps) stepssOther) = 
             ?P (interleaveSteps (step # steps) (stepsOther # stepssOther'))"
    by simp
  also have "\<dots> = ?P (step # stepsOther @ interleaveSteps steps stepssOther')"
    by auto
  also have "\<dots> = ?P (step # stepsOther) + ?P (interleaveSteps steps stepssOther')"
    by (metis append_Cons paidBackAmountFromAppend)
  also have "\<dots> = ?P (step # stepsOther) + ?P steps + ?P (concat stepssOther')"
    using Cons.IH[of stepssOther'] Cons.prems *
    by simp
  also have "\<dots> = ?P (step # steps) + ?P stepsOther + ?P (concat stepssOther')"
    by (smt (verit) ab_semigroup_add_class.add_ac(1) add.commute paidBackAmountFromCons)
  finally show ?case
    using * depositedAmountTo_def depositsTo_def 
    by auto
qed

lemma paidBackAmountFromInterleaveStepsOther:
  assumes "length steps = length stepssOther"
  assumes "\<nexists> step. step \<in> set (concat stepssOther) \<and> isCaller caller step"
  shows "paidBackAmountFrom tokenDepositAddress token caller (interleaveSteps steps stepssOther) = 
         paidBackAmountFrom tokenDepositAddress token caller steps"
  using assms
  using noIsStepCallerPaidBackAmountFrom paidBackAmountFromInterleaveSteps 
  by presburger

lemma transferredAmountFromInterleaveSteps:
  assumes "length steps = length stepssOther"
  shows "transferredAmountFrom tokenDepositAddress token caller (interleaveSteps steps stepssOther) = 
         transferredAmountFrom tokenDepositAddress token caller steps +
         transferredAmountFrom tokenDepositAddress token caller (concat stepssOther)"
  using assms
proof (induction steps arbitrary: stepssOther)
  case Nil
  then show ?case
    by simp
next
  let ?T = "\<lambda> steps. transferredAmountFrom tokenDepositAddress token caller steps"
  case (Cons step steps)
  then obtain stepsOther stepssOther' where *: "stepssOther = stepsOther # stepssOther'"
    by (meson in_set_impl_in_set_zip1 list.set_cases list.set_intros(1) set_zip_rightD)
  then have "?T (interleaveSteps (step # steps) stepssOther) = 
             ?T (interleaveSteps (step # steps) (stepsOther # stepssOther'))"
    by simp
  also have "\<dots> = ?T (step # stepsOther @ interleaveSteps steps stepssOther')"
    by auto
  also have "\<dots> = ?T (step # stepsOther) + ?T (interleaveSteps steps stepssOther')"
    by (metis append_Cons transferredAmountFromAppend)
  also have "\<dots> = ?T (step # stepsOther) + ?T steps + ?T (concat stepssOther')"
    using Cons.IH[of stepssOther'] Cons.prems *
    by simp
  also have "\<dots> = ?T (step # steps) + ?T stepsOther + ?T (concat stepssOther')"
    by (smt (verit, del_insts) ab_semigroup_add_class.add_ac(1) add.commute transferAmountFromConsOther transferredAmountFromConsTransfer)
  finally show ?case
    using *
    by auto
qed

lemma transferredAmountFromInterleaveStepsOther:
  assumes "length steps = length stepssOther"
  assumes "\<nexists> step. step \<in> set (concat stepssOther) \<and> isCaller caller step"
  shows "transferredAmountFrom tokenDepositAddress token caller (interleaveSteps steps stepssOther) = 
         transferredAmountFrom tokenDepositAddress token caller steps"
  using assms(1) assms(2) noIsStepCallerTransferredAmountFrom transferredAmountFromInterleaveSteps
  by presburger

end


context Init'
begin

lemma nonClaimedBeforeNonCanceledDepositsToInterleaveOther:
  assumes "reachable contractsInit contracts (interleaveSteps steps stepssOther @ stepsBefore @ stepsInit)"
  assumes "length stepssOther = length steps" "\<nexists> step. step \<in> set (concat stepssOther) \<and> isCaller caller step"
  shows 
   "nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit
      (interleaveSteps steps stepssOther @ stepsBefore @ stepsInit) = 
    nonClaimedBeforeNonCanceledDepositsTo tokenDepositAddress bridgeAddress token caller stepsInit
      (steps @ stepsBefore @ stepsInit)"
 unfolding nonClaimedBeforeNonCanceledDepositsTo_def
proof (rule filter_cong)
  show "depositsTo tokenDepositAddress token caller (interleaveSteps steps stepssOther @ stepsBefore @ stepsInit) =
        depositsTo tokenDepositAddress token caller (steps @ stepsBefore @ stepsInit)"
    using assms depositsToInterleaveStepsOther 
    by auto
next
  fix step
  assume step: "step \<in> set (depositsTo tokenDepositAddress token caller (steps @ stepsBefore @ stepsInit))"
  show "(\<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
         \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step)
              (interleaveSteps steps stepssOther @ stepsBefore @ stepsInit)) \<longleftrightarrow>
         (\<not> isClaimedID bridgeAddress token (DEPOSIT_id step) stepsInit \<and>
          \<not> isCanceledID tokenDepositAddress token (DEPOSIT_id step) 
              (steps @ stepsBefore @ stepsInit))" (is "\<not> ?P \<and> \<not> ?Q \<longleftrightarrow> \<not> ?P' \<and> \<not> ?Q'")
  proof safe
    assume "\<not> ?Q" "?Q'"
    then show False
      using setInterleaveSteps[of steps stepssOther] assms
      unfolding isCanceledID_def
      by (metis Un_iff set_append)
  next
    let ?S = "set (interleaveSteps steps stepssOther @ stepsBefore @ stepsInit)"
    assume "?Q" "\<not> ?Q'"
    then obtain caller' amount' proof' where
      *: "CANCEL_WD tokenDepositAddress caller' (DEPOSIT_id step) token amount' proof' \<in> set (concat stepssOther)"
      using setInterleaveSteps[of steps stepssOther] assms
      unfolding isCanceledID_def
      by force
    then have **: "CANCEL_WD tokenDepositAddress caller' (DEPOSIT_id step) token amount' proof' \<in> ?S"
      using setInterleaveSteps[of steps stepssOther] assms
      by simp
    have "caller \<noteq> caller'"
      using * assms
      by fastforce
    moreover
    have "DEPOSIT tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step) \<in> ?S"
    proof-
      have "step = DEPOSIT tokenDepositAddress caller (DEPOSIT_id step) token (DEPOSIT_amount step)"
        using depositsToDEPOSIT[OF step]
        by (metis DEPOSIT_amount.simps DEPOSIT_id.simps)
    moreover
      have "step \<in> ?S"
        using step setInterleaveSteps[of steps stepssOther] assms
        unfolding depositsTo_def
        using set_append set_filter
        by force
    ultimately
    show ?thesis
       by simp
  qed
  ultimately show False
    using onlyDepositorCanCancelSteps[OF assms(1) _ **]
    by auto
  qed
qed

end

context InitFirstUpdate
begin

lemma nonReleasedBurnsToInterleaveOther:
  assumes "stepsInit = interleaveSteps steps stepssOther @ stepsBefore @ stepsInit'"
  assumes "reachable contractsInit contracts (interleaveSteps steps stepssOther @ stepsBefore @ stepsInit')"
  assumes "length stepssOther = length steps" "\<nexists> step. step \<in> set (concat stepssOther) \<and> isCaller caller step"
  shows "nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit'
           (interleaveSteps steps stepssOther @ stepsBefore @ stepsInit') = 
         nonReleasedBurnsTo tokenDepositAddress bridgeAddress token caller stepsInit'
           (steps @ stepsBefore @ stepsInit')"
  unfolding nonReleasedBurnsTo_def
proof (rule filter_cong)
  fix step
  assume step: "step \<in> set (burnsTo bridgeAddress token caller stepsInit')"
  show "(\<not> isReleasedID tokenDepositAddress token (BURN_id step)
              (interleaveSteps steps stepssOther @ stepsBefore @ stepsInit')) =
         (\<not> isReleasedID tokenDepositAddress token (BURN_id step) 
              (steps @ stepsBefore @ stepsInit'))" (is "\<not> ?P \<longleftrightarrow> \<not> ?P'")
  proof safe
    assume "\<not> ?P" "?P'"
    then show False
      using setInterleaveSteps[of steps stepssOther] assms
      unfolding isReleasedID_def
      by (metis Un_iff set_append)
  next
    let ?S = "set stepsInit"
    assume "?P" "\<not> ?P'"
    then obtain caller' amount' proof' where
      *: "RELEASE tokenDepositAddress caller' (BURN_id step) token amount' proof' \<in> set (concat stepssOther)"
      using setInterleaveSteps[of steps stepssOther] assms
      unfolding isReleasedID_def
      by force
    then have **: "RELEASE tokenDepositAddress caller' (BURN_id step) token amount' proof' \<in> ?S"
      using setInterleaveSteps[of steps stepssOther] assms
      by simp
    have "caller \<noteq> caller'"
      using * assms
      by fastforce
    moreover
    have "BURN bridgeAddress caller (BURN_id step) token (BURN_amount step) \<in> ?S"
    proof-
      have "step = BURN bridgeAddress caller (BURN_id step) token (BURN_amount step)"
        using burnsToBURN[OF step]
        by (metis BURN_amount.simps BURN_id.simps)
    moreover
      have "step \<in> ?S"
        using step setInterleaveSteps[of steps stepssOther] assms
        unfolding burnsTo_def
        using set_append set_filter
        by force
    ultimately
    show ?thesis
       by simp
  qed
  ultimately show False
    using onlyBurnerCanReleaseSteps(1)[OF **] assms
    by auto
  qed
qed simp

end

end