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

end