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

lemma mapping_value_sum_update_plus [simp]:
  assumes "finite (Mapping.keys m)"
  shows "mapping_value_sum (Mapping.update k (lookupNat m k + v) m) = mapping_value_sum m + v"
  using assms
  sorry

lemma mapping_value_sum_update_minus [simp]:
  assumes "finite (Mapping.keys m)"
  assumes "v \<le> lookupNat m k"
  shows
     "v \<le> mapping_value_sum m"
     "mapping_value_sum (Mapping.update k (lookupNat m k - v) m) = mapping_value_sum m - v"
  using assms
  sorry

lemma mapping_value_sum_geq_entry:
  assumes "finite (Mapping.keys M)" "user \<in> Mapping.keys M"
  shows "lookupNat M user \<le> mapping_value_sum M"
proof-
  have "finite (Mapping.entries M)"
    using assms
    by simp
  moreover
  have "(user, lookupNat M user) \<in> Mapping.entries M"
    using assms unfolding lookupNat_def
    by (metis default_def in_entriesI lookup_default)
  ultimately
  have "(user, lookupNat M user) \<in> set (Mapping.ordered_entries M)"
    using assms
    unfolding Mapping.ordered_entries_def
    by (metis (full_types) ordered_entries_def set_ordered_entries)
  then show ?thesis
    unfolding mapping_value_sum_def
    by (metis member_le_sum_list set_zip_rightD zip_map_fst_snd)
qed

end