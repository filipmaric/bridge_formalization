theory More_Mapping
  imports Definition
begin

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

lemma lookupNat_delete [simp]:
  shows "lookupNat (Mapping.delete k m) k = 0"
  unfolding lookupNat_def
  by (simp add: lookup_default_def)

lemma lookupNat_delete' [simp]:
  assumes "k \<noteq> k'"
  shows "lookupNat (Mapping.delete k m) k' = lookupNat m k'"
  using assms
  unfolding lookupNat_def
  by (simp add: lookup_default_def)

lemma lookupNat_empty [simp]:
  shows "lookupNat Mapping.empty x = 0"
  by (simp add: lookupNat_def lookup_default_empty)

lemma lookupBool_update [simp]: 
  shows "lookupBool (Mapping.update k v m) k = v"
  unfolding lookupBool_def
  by (simp add: lookup_default_update)

lemma lookupBool_update' [simp]:
  assumes "k' \<noteq> k"
  shows "lookupBool (Mapping.update k v m) k' = lookupBool m k'"
  using assms
  unfolding lookupBool_def
  by (auto simp add: lookup_default_update')

definition mapping_value_sum where
 "mapping_value_sum m = sum_list (map snd (Mapping.ordered_entries m))"

lemma mapping_value_sum_empty [simp]:
  shows "mapping_value_sum Mapping.empty = 0"
  unfolding mapping_value_sum_def
  by simp


lemma sum_list_insort_insert_key:
  fixes m :: "('a::linorder \<times> nat) list"
  assumes "k \<notin> set (map fst m)"
  shows "sum_list (map snd (insort_insert_key fst (k, v) m)) = sum_list (map snd m) + v" 
  using assms
  by (induction m) (auto simp add: insort_insert_key_def)

lemma sum_list_AList_delete_nonmember:
  assumes "k \<notin> set (map fst m)"
  shows "sum_list (map snd (AList.delete k m)) = sum_list (map snd m)"
  using assms 
  by auto

lemma sum_list_AList_delete_member:
  fixes m :: "('a::linorder \<times> nat) list"
  assumes "k \<in> set (map fst m)"
  assumes "distinct (map fst m)"
  shows "sum_list (map snd (AList.delete k m)) = sum_list (map snd m) - the (map_of m k) \<and>
        the (map_of m k) \<le> sum_list (map snd m)"
  using assms
proof (induction m)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "k \<in> set (map fst xs)")
    case True
    then obtain b where "(k, b) \<in> set xs"
      by auto
    have "k \<noteq> fst x"
      using True Cons.prems
      by force
    then have "AList.delete k (x # xs) = x # AList.delete k xs"
      by simp
    moreover have "sum_list (map snd xs) \<ge> b"
      using \<open>(k, b) \<in> set xs\<close>
      by (simp add: sum_list_map_remove1)
    ultimately show ?thesis
      using \<open>k \<noteq> fst x\<close>Cons.IH[OF True] Cons.prems \<open>(k, b) \<in> set xs\<close>
      by auto
  next
    case False
    then show ?thesis
      using Cons.prems(1) by fastforce
  qed
qed

lemma map_of_ordered_entries [simp]:
  assumes "finite (Mapping.keys m)" "k \<in> Mapping.keys m"
  shows "the (map_of (Mapping.ordered_entries m) k) = lookupNat m k"
  by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD assms(1) assms(2) default_def distinct_ordered_entries in_entriesI lookupNat_def lookup_default option.sel prod.sel(1) prod.sel(2) set_map_of_compr set_ordered_entries)

lemma mapping_value_sum_update_plus [simp]:
  assumes "finite (Mapping.keys m)"
  shows "mapping_value_sum (Mapping.update k (lookupNat m k + v) m) = mapping_value_sum m + v" (is "mapping_value_sum ?lhs = mapping_value_sum ?rhs + v")
proof-
  have "mapping_value_sum ?lhs = sum_list (map snd (Mapping.ordered_entries (Mapping.update k (lookupNat m k + v) m)))"
    unfolding mapping_value_sum_def
    by simp
  also have "\<dots> = sum_list (map snd (insort_insert_key fst (k, lookupNat m k + v) (AList.delete k (Mapping.ordered_entries m))))"
    using ordered_entries_update[OF assms]
    by simp
  also have "\<dots> = sum_list (map snd (AList.delete k (Mapping.ordered_entries m))) + (lookupNat m k + v)"
    by (subst sum_list_insort_insert_key, auto simp add: delete_notin_dom)
  also have "\<dots> = sum_list (map snd (Mapping.ordered_entries m)) + v"
  proof (cases "k \<in> Mapping.keys m")
    case True
    then have "sum_list (map snd (AList.delete k (Mapping.ordered_entries m))) + (lookupNat m k + v) = sum_list (map snd (Mapping.ordered_entries m)) - (lookupNat m k) + (lookupNat m k + v) \<and>
             lookupNat m k \<le> sum_list (map snd (Mapping.ordered_entries m))"
      using sum_list_AList_delete_member[of k "Mapping.ordered_entries m", OF _ distinct_ordered_entries]
      by (simp add: assms)
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using sum_list_AList_delete_nonmember[of k "Mapping.ordered_entries m"]
      by (metis Mapping_delete_if_notin_keys add_0 lookupNat_delete ordered_entries_delete)
  qed
  finally show ?thesis
    unfolding mapping_value_sum_def
    by simp
qed

lemma mapping_value_sum_update_minus [simp]:
  assumes "finite (Mapping.keys m)"
  assumes "v \<le> lookupNat m k"
  shows
     "v \<le> mapping_value_sum m"
     "mapping_value_sum (Mapping.update k (lookupNat m k - v) m) = mapping_value_sum m - v" (is "?lhs = ?rhs")
proof-
  have "mapping_value_sum (Mapping.update k (lookupNat m k - v) m) = sum_list (map snd (Mapping.ordered_entries (Mapping.update k (lookupNat m k - v) m)))"
    unfolding mapping_value_sum_def
    by simp
  also have "\<dots> = sum_list (map snd (insort_insert_key fst (k, lookupNat m k - v) (AList.delete k (Mapping.ordered_entries m))))"
    using ordered_entries_update[OF assms(1)]
    by simp
  also have "\<dots> = sum_list (map snd (AList.delete k (Mapping.ordered_entries m))) + (lookupNat m k - v)"
    by (subst sum_list_insort_insert_key, auto simp add: delete_notin_dom)
  also have "\<dots> = sum_list (map snd (Mapping.ordered_entries m)) - v \<and> v \<le> sum_list (map snd (Mapping.ordered_entries m))"
  proof (cases "k \<in> Mapping.keys m")
    case True
    then have "sum_list (map snd (AList.delete k (Mapping.ordered_entries m))) + (lookupNat m k - v) = 
               sum_list (map snd (Mapping.ordered_entries m)) - (lookupNat m k) + (lookupNat m k - v) \<and>
             lookupNat m k \<le> sum_list (map snd (Mapping.ordered_entries m))"
      by (metis assms(1) distinct_ordered_entries map_fst_ordered_entries map_of_ordered_entries set_ordered_keys sum_list_AList_delete_member)
    then show ?thesis
      using assms(2) by auto
  next
    case False
    then show ?thesis
      by (metis Mapping_delete_if_notin_keys add.right_neutral assms(1) assms(2) calculation diff_zero le_antisym lookupNat_delete mapping_value_sum_def mapping_value_sum_update_plus zero_le)
  qed
  finally show "v \<le> mapping_value_sum m" "?lhs = ?rhs"
    unfolding mapping_value_sum_def
    by auto
qed

lemma mapping_value_sum_geq_entry:
  assumes "finite (Mapping.keys M)" "x \<in> Mapping.keys M"
  shows "lookupNat M x \<le> mapping_value_sum M"
proof-
  have "finite (Mapping.entries M)"
    using assms
    by simp
  moreover
  have "(x, lookupNat M x) \<in> Mapping.entries M"
    using assms unfolding lookupNat_def
    by (metis default_def in_entriesI lookup_default)
  ultimately
  have "(x, lookupNat M x) \<in> set (Mapping.ordered_entries M)"
    using assms
    unfolding Mapping.ordered_entries_def
    by (metis (full_types) ordered_entries_def set_ordered_entries)
  then show ?thesis
    unfolding mapping_value_sum_def
    by (metis member_le_sum_list set_zip_rightD zip_map_fst_snd)
qed

lemma ordered_entries_empty:
  assumes "Mapping.ordered_entries m = []" "finite (Mapping.keys m)"
  shows "\<forall>x. lookupNat m x = 0"
  using assms
  unfolding lookupNat_def
  by (metis empty_iff finite.emptyI keys_empty lookup_default_empty map_fst_ordered_entries mapping_eqI' ordered_entries_empty ordered_keys_def sorted_list_of_set.set_sorted_key_list_of_set)

lemma lookupNat_all0:
  assumes "\<forall>x. lookupNat m x = 0"
  shows "\<forall> n \<in> Mapping.entries m. snd n = 0"
proof safe
  fix a b
  assume "(a, b) \<in> Mapping.entries m"
  then have "b = 0"
    using assms
    unfolding lookupNat_def
    by (metis in_entriesD lookup_default_def lookup_default_update lookup_update)
  then show "snd (a, b) = 0"
    by simp
qed

lemma mapping_value_sum_eq:
  assumes "finite (Mapping.keys m1)" "finite (Mapping.keys m2)"
  assumes "\<forall>x. lookupNat m1 x = lookupNat m2 x"
  shows "mapping_value_sum m1 = mapping_value_sum m2"
proof-
  have "Mapping.ordered_entries m1 = Mapping.ordered_entries m2" (is "?m1 = ?m2")
  proof-
    have *: "map fst ?m1 = map fst ?m2"
      sorry
    moreover
    have "map snd ?m1 = map snd ?m2"
      by (metis assms(1) assms(2) assms(3) * lookupNat_def map_fst_ordered_entries mapping_eqI' set_ordered_keys)
    ultimately
    show ?thesis
      by (metis zip_map_fst_snd)
  qed
  then show ?thesis
    unfolding mapping_value_sum_def
    by simp
qed

end