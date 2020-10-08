theory Future_Library
  imports Main
begin

text "Lemmas that will be present in the next release of Isabelle"

lemma ex_max_if_finite:
  "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>m\<in>S. \<not>(\<exists>x\<in>S. x > (m::'a::order))"
by(induction rule: finite.induct) (auto intro: order.strict_trans)

lemma ex_is_arg_max_if_finite: fixes f :: "'a \<Rightarrow> 'b :: order"
shows "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>x. is_arg_max f (\<lambda>x. x \<in> S) x"
unfolding is_arg_max_def
using ex_max_if_finite[of "f ` S"]
by auto

lemma arg_max_SOME_Max:
  "finite S \<Longrightarrow> arg_max_on f S = (SOME y. y \<in> S \<and> f y = Max(f ` S))"
unfolding arg_max_on_def arg_max_def is_arg_max_linorder
apply(rule arg_cong[where f = Eps])
apply (auto simp: fun_eq_iff intro: Max_eqI[symmetric])
done

lemma arg_max_if_finite: fixes f :: "'a \<Rightarrow> 'b :: order"
assumes "finite S" "S \<noteq> {}"
shows  "arg_max_on f S \<in> S" and "\<not>(\<exists>x\<in>S. f x > f (arg_max_on f S))"
using ex_is_arg_max_if_finite[OF assms, of f]
unfolding arg_max_on_def arg_max_def is_arg_max_def
by(auto dest!: someI_ex)

lemma arg_max_greatest: fixes f :: "'a \<Rightarrow> 'b :: linorder"
shows "\<lbrakk> finite S;  S \<noteq> {};  y \<in> S \<rbrakk> \<Longrightarrow> f(arg_max_on f S) \<ge> f y"
by(simp add: arg_max_SOME_Max inv_into_def2[symmetric] f_inv_into_f)

lemma arg_max_inj_eq: fixes f :: "'a \<Rightarrow> 'b :: order"
shows "\<lbrakk> inj_on f {x. P x}; P a; \<forall>y. P y \<longrightarrow> f a \<ge> f y \<rbrakk> \<Longrightarrow> arg_max f P = a"
apply(simp add: arg_max_def is_arg_max_def)
apply(rule someI2[of _ a])
 apply (simp add: less_le_not_le)
  by (metis inj_on_eq_iff less_le mem_Collect_eq)

end