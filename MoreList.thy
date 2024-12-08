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

end