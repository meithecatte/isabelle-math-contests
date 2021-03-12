theory Future_Library
  imports Main
    "HOL-Computational_Algebra.Factorial_Ring"
begin

section "Lemmas that might be present in some future release of Isabelle"

subsection "Minima and maxima"
(* https://lists.cam.ac.uk/mailman/htdig/cl-isabelle-users/2020-October/msg00021.html *)

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

subsection "Multiplicities"
(* https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2021-January/msg00088.html *)

context factorial_semiring
begin

lemma infinite_unit_divisor_powers:
  assumes "y \<noteq> 0"
  assumes "is_unit x"
  shows "infinite {n. x^n dvd y}"
proof -
  from `is_unit x` have "is_unit (x^n)" for n
    using is_unit_power_iff by auto
  hence "x^n dvd y" for n
    by auto
  hence "{n. x^n dvd y} = UNIV"
    by auto
  thus ?thesis
    by auto
qed

corollary is_unit_iff_infinite_divisor_powers:
  assumes "y \<noteq> 0"
  shows "is_unit x \<longleftrightarrow> infinite {n. x^n dvd y}"
  using infinite_unit_divisor_powers finite_divisor_powers assms by auto

lemma multiplicity_dvd_iff_dvd:
  assumes "x \<noteq> 0"
  shows "p^k dvd x \<longleftrightarrow> p^k dvd p^multiplicity p x"
proof (cases "is_unit p")
  case True
  then have "is_unit (p^k)"
    using is_unit_power_iff by simp
  hence "p^k dvd x"
    by auto
  moreover from `is_unit p` have "p^k dvd p^multiplicity p x"
    using multiplicity_unit_left is_unit_power_iff by simp
  ultimately show ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "p = 0")
    case True
    then have "p^multiplicity p x = 1"
      by simp
    moreover have "p^k dvd x \<Longrightarrow> k = 0"
    proof (rule ccontr)
      assume "p^k dvd x" and "k \<noteq> 0"
      with `p = 0` have "p^k = 0" by auto
      with `p^k dvd x` have "0 dvd x" by auto
      hence "x = 0" by auto
      with `x \<noteq> 0` show False by auto
    qed
    ultimately show ?thesis
      by (auto simp add: is_unit_power_iff `\<not> is_unit p`)
  next
    case False
    with `x \<noteq> 0` `\<not> is_unit p` show ?thesis
      by (simp add: power_dvd_iff_le_multiplicity dvd_power_iff multiplicity_same_power)
  qed
qed

lemma multiplicity_decomposeI:
  assumes "x = p^k * x'" and "\<not> p dvd x'" and "p \<noteq> 0"
  shows "multiplicity p x = k"
proof (rule multiplicity_eqI)
  from assms show "p^k dvd x" by auto
  from assms have "x = x' * p^k" by (simp add: ac_simps)
  with `\<not> p dvd x'` and `p \<noteq> 0` show "\<not> p^Suc k dvd x"
    by simp
qed

lemma multiplicity_sum_lt:
  assumes "multiplicity p a < multiplicity p b" "a \<noteq> 0" "b \<noteq> 0"
  shows "multiplicity p (a + b) = multiplicity p a"
proof -
  let ?vp = "multiplicity p"
  have unit: "\<not> is_unit p"
  proof
    assume "is_unit p"
    then have "?vp a = 0" and "?vp b = 0" using multiplicity_unit_left by auto
    with assms show False by auto
  qed

  from multiplicity_decompose' obtain a' where a': "a = p^?vp a * a'" "\<not> p dvd a'"
    using unit assms by metis
  from multiplicity_decompose' obtain b' where b': "b = p^?vp b * b'"
    using unit assms by metis

  show "?vp (a + b) = ?vp a"
    \<comment> \<open>Use the rule here, after we obtained @{term a'} and @{term b'}, to avoid the
          "Result contains obtained parameters" error\<close>
  proof (rule multiplicity_decomposeI)
    let ?k = "?vp b - ?vp a"
    from assms have k: "?k > 0" by simp
    with b' have "b = p^?vp a * p^?k * b'"
      by (simp flip: power_add)
    with a' show *: "a + b = p^?vp a * (a' + p^?k * b')"
      by (simp add: ac_simps distrib_left)

    moreover show "\<not> p dvd a' + p^?k * b'"
      using a' k dvd_add_left_iff by auto

    show "p \<noteq> 0" using assms by auto
  qed
qed

corollary multiplicity_sum_min:
  assumes "multiplicity p a \<noteq> multiplicity p b" "a \<noteq> 0" "b \<noteq> 0"
  shows "multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b)"
proof -
  let ?vp = "multiplicity p"
  from assms have "?vp a < ?vp b \<or> ?vp a > ?vp b"
    by auto
  then show ?thesis
    by (metis assms multiplicity_sum_lt min.commute add_commute min.strict_order_iff)    
qed

end

subsection "Summations"
(* https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2021-January/msg00103.html *)
lemma max_ge_card: "finite S \<Longrightarrow> Suc (Max S) \<ge> card S"
proof (rule classical)
  assume "finite S" and "\<not> Suc (Max S) \<ge> card S"
  then have "Suc (Max S) < card S"
    by simp
  with `finite S` have "S \<subseteq> {0..Max S}"
    by auto
  hence "card S \<le> card {0..Max S}"
    by (intro card_mono; auto)
  thus "card S \<le> Suc (Max S)"
    by simp
qed

lemma sum_min:
  shows "\<Sum> {0..<card S} \<le> \<Sum> S"
proof (cases "finite S")
  case True
  then show ?thesis
  proof (induction "card S" arbitrary: S)
    case (Suc x)
    then have "Max S \<ge> x" using max_ge_card by fastforce
    let ?S' = "S - {Max S}"
    from Suc have "Max S \<in> S" by (auto intro: Max_in)
    hence cards: "card S = Suc (card ?S')"
      using `finite S` by (intro card.remove; auto)
    hence "\<Sum> {0..<card ?S'} \<le> \<Sum> ?S'"
      using Suc by (intro Suc; auto)

    hence "\<Sum> {0..<card ?S'} + x \<le> \<Sum> ?S' + Max S"
      using `Max S \<ge> x` by simp
    also have "... = \<Sum> S"
      using sum.remove[OF `finite S` `Max S \<in> S`, where g="\<lambda>x. x"]
      by simp
    finally show ?case
      using cards Suc by auto
  qed simp
qed simp

lemma sum_count:
  assumes "finite S" "finite R" "g ` S \<subseteq> R"
  shows "(\<Sum>x \<in> S. f (g x)) = (\<Sum>y \<in> R. of_nat (card {x \<in> S. g x = y}) * f y)"
proof -
  let ?r = "relation_of (\<lambda>p q. g p = g q) S"
  have eqv: "equiv S ?r"
    unfolding relation_of_def by (auto intro: comp_equivI)
  have finite: "C \<in> S//?r \<Longrightarrow> finite C" for C
    by (fact finite_equiv_class[OF `finite S` equiv_type[OF `equiv S ?r`]])
  have disjoint: "A \<in> S//?r \<Longrightarrow> B \<in> S//?r \<Longrightarrow> A \<noteq> B \<Longrightarrow> A \<inter> B = {}" for A B
    using eqv quotient_disj by blast

  let ?cls = "\<lambda>y. {x \<in> S. y = g x}"
  have quot_as_img: "S//?r = ?cls ` g ` S"
    by (auto simp add: relation_of_def quotient_def)
  have cls_inj: "inj_on ?cls (g ` S)"
    by (auto intro: inj_onI)

  have rest_0: "(\<Sum>y \<in> R - g ` S. of_nat (card (?cls y)) * f y) = 0"
    (is "?rest = 0")
  proof -
    {
      fix y
      assume "y \<in> R - g ` S"
      then have *: "?cls y = {}"
        by auto
      have "of_nat (card (?cls y)) * f y = 0"
        unfolding * by simp
    }
    thus ?thesis by simp
  qed

  have "(\<Sum>x \<in> S. f (g x)) = (\<Sum>C \<in> S//?r. \<Sum>x \<in> C. f (g x))"
    using eqv finite disjoint
    by (simp flip: sum.Union_disjoint[simplified] add: Union_quotient)
  also have "... = (\<Sum>y \<in> g ` S. \<Sum>x \<in> ?cls y. f (g x))"
    unfolding quot_as_img by (simp add: sum.reindex[OF cls_inj])
  also have "... = (\<Sum>y \<in> g ` S. \<Sum>x \<in> ?cls y. f y)"
    by auto
  also have "... = (\<Sum>y \<in> g ` S. of_nat (card (?cls y)) * f y)"
    by (simp flip: sum_constant)
  also have "... = (\<Sum>y \<in> R. of_nat (card (?cls y)) * f y)"
    using rest_0 by (simp add: sum.subset_diff[OF \<open>g ` S \<subseteq> R\<close> \<open>finite R\<close>])
  finally show ?thesis
    by (simp add: eq_commute)
qed

end
