theory Problem_2
  imports
    "HOL-Analysis.Analysis"
begin

subsection "Problem 2"

text "Prove that a sequence is bounded, converges, and find the limit."
(* TAGS: real-analysis *)
context
  fixes a :: real
  assumes a_bounds: "0 < a" "a < 1"
begin
fun c :: "nat \<Rightarrow> real" where
"c 0 = a / 2" |
"c (Suc n) = (a + (c n)\<^sup>2) / 2"

abbreviation "x1 \<equiv> 1 - sqrt (1 - a)"
abbreviation "x2 \<equiv> 1 + sqrt (1 - a)"

lemma c_pos: "0 < c n"
  using a_bounds
  by (induction n, auto, smt zero_less_power)

lemma c_bounded: "c n < x1"
proof (induction n)
  case 0
  have "(1 - a/2)\<^sup>2 = 1 - a + (a/2)\<^sup>2"
    by (simp add: power2_diff)
  hence "1 - a < (1 - a/2)\<^sup>2" using a_bounds by auto
  hence "sqrt (1 - a) < 1 - a/2"
    using a_bounds and real_less_lsqrt by auto
  thus ?case by auto
next
  case (Suc n)
  then have "(c n)\<^sup>2 < (1 - sqrt (1-a))\<^sup>2" using c_pos
    by (smt power_less_imp_less_base real_sqrt_abs)
  also have "... = 2 - 2 * sqrt (1-a) - a"
    using a_bounds by (simp add: power2_diff)
  finally have "(a + (c n)\<^sup>2)/2 < 1 - sqrt (1-a)" by auto
  then show ?case by auto
qed

lemma c_incseq: "incseq c"
proof (rule incseq_SucI)
  fix n
  from c_bounded have "c n < x1" by auto
  have "c n < x1" "c n < x2"
    using c_bounded
    by (smt a_bounds real_sqrt_lt_0_iff)+
  moreover have "(c n)\<^sup>2 - 2*c n + a = (c n - x1)*(c n - x2)"
    using a_bounds
    by (auto simp add: algebra_simps power2_eq_square)
  ultimately have "(c n)\<^sup>2 - 2*c n + a > 0"
    by (smt nonzero_mult_div_cancel_right zero_le_divide_iff)
  thus "c n \<le> c (Suc n)" by auto
qed

theorem problem2: "c \<longlonglongrightarrow> x1"
proof -
  obtain L where "c \<longlonglongrightarrow> L"
    using c_incseq c_bounded incseq_convergent
    by (metis less_imp_le)
  then have "(\<lambda>n. c (Suc n)) \<longlonglongrightarrow> L"
    using LIMSEQ_Suc by blast
  hence "(\<lambda>n. (a + (c n)\<^sup>2) / 2 * 2) \<longlonglongrightarrow> L*2"
    using tendsto_mult_right by fastforce
  hence "(\<lambda>n. a + (c n)\<^sup>2) \<longlonglongrightarrow> L*2" by (simp del: distrib_right_numeral)
  hence "(\<lambda>n. a + (c n)\<^sup>2 - a) \<longlonglongrightarrow> L*2 - a"
    using tendsto_diff LIMSEQ_const_iff by blast
  hence "(\<lambda>n. (c n)\<^sup>2) \<longlonglongrightarrow> L*2 - a"
    by auto
  moreover from `c \<longlonglongrightarrow> L`
  have "(\<lambda>n. (c n)\<^sup>2) \<longlonglongrightarrow> L\<^sup>2"
    unfolding power2_eq_square
    using tendsto_mult by blast
  ultimately have "L*2 - a = L\<^sup>2"
    by (rule LIMSEQ_unique)
  hence "L\<^sup>2 - 2*L + a = 0" by auto
  moreover have "L\<^sup>2 - 2*L + a = (L - x1)*(L - x2)"
    using a_bounds
    by (auto simp add: algebra_simps power2_eq_square)
  ultimately have "L = x1 \<or> L = x2"
    by auto
  moreover from c_bounded and `c \<longlonglongrightarrow> L` have "L \<le> x1"
    by (meson LIMSEQ_le_const2 le_less_linear less_imp_triv)
  moreover from a_bounds have "x1 < x2" by auto
  ultimately have "L = x1" by auto
  thus ?thesis using `c \<longlonglongrightarrow> L` by auto
qed

end

end