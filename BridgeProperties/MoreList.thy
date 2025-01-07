theory MoreList
imports Main
begin

lemma filter':
  assumes "filter P xs = ys1 @ [y] @ ys2" "y \<notin> set (ys1 @ ys2)"
  assumes "\<forall> x \<in> set xs. P x \<and> x \<noteq> y \<longleftrightarrow> P' x"
  shows "filter P' xs = ys1 @ ys2"
  using assms
proof-
  have "filter (\<lambda>x. x \<noteq> y) ys1 = ys1"
    using assms(2)
    by (induction ys1, auto)
  moreover
  have "filter (\<lambda>x. x \<noteq> y) ys2 = ys2"
    using assms(2)
    by (induction ys2, auto)
  moreover
  have "filter P' xs = filter (\<lambda>x. P x \<and> x \<noteq> y) xs"
  proof (rule filter_cong)
    fix x
    assume "x \<in> set xs" then 
    show "P' x \<longleftrightarrow> P x \<and> x \<noteq> y"
      using assms
      by simp
  qed simp
  then have "filter P' xs = filter (\<lambda> x. x \<noteq> y) (filter P xs)"
    by simp
  ultimately show ?thesis
    using assms \<open>y \<notin> set (ys1 @ ys2)\<close>
    by auto
qed

lemma filter'':
  assumes "distinct xs" "x \<in> set xs" "P x"  "\<forall> x' \<in> set xs. (P x' \<and> x' \<noteq> x) \<longleftrightarrow> P' x'"
  shows "\<exists> Pxs1 Pxs2. filter P' xs = Pxs1 @ Pxs2 \<and> filter P xs = Pxs1 @ [x] @ Pxs2"
proof-
  obtain xs1 xs2 where "xs = xs1 @ [x] @ xs2" using \<open>x \<in> set xs\<close>
    by (metis append_eq_Cons_conv self_append_conv2 split_list)
  let ?Pxs1 = "filter P xs1" and ?Pxs2 = "filter P xs2"
  have "filter P' xs = ?Pxs1 @ ?Pxs2"
  proof (rule filter')
    show "filter P xs = ?Pxs1 @ [x] @ ?Pxs2"
      using \<open>xs = xs1 @ [x] @ xs2\<close> \<open>P x\<close>
      by auto
  next
    show "x \<notin> set (?Pxs1 @ ?Pxs2)"
    using \<open>xs = xs1 @ [x] @ xs2\<close> \<open>distinct xs\<close>
    by auto
  next
    show "\<forall> x' \<in> set xs. (P x' \<and> x' \<noteq> x) \<longleftrightarrow> P' x'"
      by fact
  qed
  then show ?thesis
    using \<open>xs = xs1 @ [x] @ xs2\<close> \<open>P x\<close>
    by auto
qed


lemma append_subset: 
  assumes "xs @ ys = xs' @ ys'"
  assumes "length ys' \<ge> length ys"
  shows "set xs' \<subseteq> set xs"
proof
  fix x
  assume "x \<in> set xs'"
  then obtain n where "x = xs' ! n" "n < length xs'"
    by (metis in_set_conv_nth)
  moreover
  have "length xs + length ys = length xs' + length ys'"
    using assms(1)
    by (metis length_append)
  then have "length xs \<ge> length xs'"
    using assms(2)
    by auto
  ultimately
  have "x = xs ! n" "n < length xs"
    using assms(1)[symmetric] 
    using nth_append[of xs' ys' n]
    using nth_append[of xs ys n]
    by auto
  then show "x \<in> set xs"
    by auto
qed

lemma sum_list_filter_P_notP:
  fixes f :: "'a \<Rightarrow> nat"
  shows "sum_list (map f xs) = 
         sum_list (map f (filter (\<lambda> x. P x) xs)) + sum_list (map f (filter (\<lambda> x. \<not> P x) xs))"
  by (induction xs) auto

lemma twiceInFilter:
  assumes "filter P xs = y1 @ [x] @ y2 @ [x] @ y3"
  shows "\<exists> z1 z2 z3. xs = z1 @ [x] @ z2 @ [x] @ z3"
  using assms
proof-
  let ?P = "filter P xs"
  have "x \<in> set xs \<and> P x"
    using assms
    by (metis append_Cons filter_set in_set_conv_decomp member_filter)
  then obtain xs1 xs2 where "xs = xs1 @ [x] @ xs2"
    by (metis append_eq_Cons_conv eq_Nil_appendI remove1_split)
  have "x \<in> set xs1 \<union> set xs2"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "?P = (filter P xs1) @ [x] @ (filter P xs2)" "x \<notin> set (filter P xs1)" "x \<notin> set (filter P xs2)"
      using \<open>xs = xs1 @ [x] @ xs2\<close>  \<open>x \<in> set xs \<and> P x\<close>
      by auto
    then show False
      using assms
      by (metis append_Cons append_Cons_eq_iff append_Nil in_set_conv_decomp)
  qed
  then show ?thesis
  proof
    assume "x \<in> set xs1"
    then obtain xs1' xs1'' where "xs1 = xs1' @ [x] @ xs1''"
      by (metis append_Cons append_Nil in_set_conv_decomp)
    then show ?thesis
      using \<open>xs = xs1 @ [x] @ xs2\<close>
      by auto
  next
    assume "x \<in> set xs2"
    then obtain xs2' xs2'' where "xs2 = xs2' @ [x] @ xs2''"
      by (metis append_Cons append_Nil in_set_conv_decomp)
    then show ?thesis
      using \<open>xs = xs1 @ [x] @ xs2\<close>
      by auto
  qed
qed

end