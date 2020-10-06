theory %invisible WarmupI
  imports
    Complex_Main
    "HOL-Library.Sum_of_Squares"
    "HOL-Number_Theory.Number_Theory"
    "HOL-Analysis.Analysis"
    "HOL-Algebra.Algebra"
begin

section "Warmup problems"

text "Long ago, the Polish Math Olympiad published, apart from
12 problems to be solved and mailed over 3 months, a set of 12
warmup problems, which were similar in spirit, but easier."

subsection "Warmup 1"

text "Solve the equation $3^x = 4y + 5$ in the integers."

text "We begin with the following lemma:"

lemma even_power_3: "[3^k = 1::int] (mod 4) \<longleftrightarrow> even k"
proof -
  have "[3^k = (-1::int)^k] (mod 4)"
    by (intro cong_pow) (auto simp: cong_def)
  thus ?thesis
    by (auto simp: cong_def minus_one_power_iff)
qed

text "This is, of course, not the only strategy. We leave an alternative proof,
in the hope that it will be instructive in doing calculations mod $n$."

lemma "[3^k = 1::int] (mod 4) \<longleftrightarrow> even k"
proof (cases "even k")
  case True
  then obtain l where "2*l = k" by auto
  then have "[3^k = (3^2)^l] (mod 4)" (is "cong _ ... _")
    by (auto simp add: power_mult)
  also have "[... = (1::int)^l] (mod 4)" (is "cong _ ... _")
    by (intro cong_pow) (simp add: cong_def)
  also have "[... = 1] (mod 4)" by auto
  finally have "[3^k = 1::int] (mod 4)".
  thus ?thesis using `even k` by blast
next
  case False
  then obtain l where "2*l + 1 = k"
    using oddE by blast
  then have "[3^k = 3^(2*l+1)] (mod 4)" (is "cong _ ... _") by auto
  also have "[... = (3^2)^l * 3] (mod 4)" (is "cong _ ... _")
    by (metis power_mult power_add power_one_right cong_def)
  also have "[... = (1::int)^l * 3] (mod 4)" (is "cong _ ... _")
    by (intro cong_mult cong_pow) (auto simp add: cong_def)
  also have "[... = 3] (mod 4)" by auto
  finally have "[3^k \<noteq> 1::int] (mod 4)" by (auto simp add: cong_def)
  then show ?thesis using `odd k` by blast
qed

text "This allows us to prove the theorem, provided we assume x is a natural number."

theorem warmup1_natx:
  fixes x :: nat and y :: int
  shows "3^x = 4*y + 5 \<longleftrightarrow> even x \<and> y = (3^x - 5) div 4"
proof -
  have "even x \<and> y = (3^x - 5) div 4" if "3^x = 4*y + 5"
  proof -
    from that have "[3^x = 4*y + 5] (mod 4)" by auto
    also have "[4*y + 5 = 5] (mod 4)"
      by (metis cong_mult_self_left cong_add_rcancel_0)
    also have "[5 = 1::int] (mod 4)" by (auto simp add: cong_def)
    finally have "[(3::int)^x = 1] (mod 4)".
    hence "even x" using even_power_3 by auto
    thus ?thesis using that by auto
  qed
  moreover have "3 ^ x = 4 * y + 5" if "even x \<and> y = (3^x - 5) div 4"
  proof -
    from that have "even x" and y_form: "y = (3^x - 5) div 4" by auto
    then have "[3^x = 1::int] (mod 4)" using even_power_3 by blast 
    then have "((3::int)^x - 5) mod 4 = 0" by (simp add: cong_def mod_diff_cong)
    thus ?thesis using y_form by auto
  qed
  ultimately show ?thesis by blast
qed

lemma powr_int_pos:
  fixes x y :: int
  assumes *: "3 powr x = y"
  shows "x \<ge> 0"
proof (rule ccontr)
  assume neg_x: "\<not> x \<ge> 0"
  then have y_inv: "y = inverse ((3::nat)^nat (-x))" (is "y = inverse (?n::nat)")
    using powr_real_of_int and * by auto
  hence "real ?n * of_int y = 1" by auto 
  hence "?n * y = 1" using of_int_eq_iff by fastforce
  hence "?n = 1"
    by (metis nat_1_eq_mult_iff nat_int nat_numeral_as_int numeral_One of_nat_mult zmult_eq_1_iff) 
  hence "nat (-x) = 0" by auto
  thus False using neg_x by auto
qed

corollary warmup1: "3 powr x = 4*y + 5 \<longleftrightarrow> x \<ge> 0 \<and> even x \<and> y = (3^(nat x) - 5) div 4" for x y :: int
proof
  assume assm: "3 powr x = 4*y + 5"
  then have "x \<ge> 0" using powr_int_pos by fastforce
  hence "3 powr (nat x) = 4*y + 5" using assm by simp
  hence "(3::real)^(nat x) = 4*y + 5" using powr_realpow by auto
  hence with_nat: "3^(nat x) = 4*y + 5" using of_int_eq_iff by fastforce
  hence "even (nat x) \<and> y = (3^(nat x) - 5) div 4" using warmup1_natx by auto
  thus "x \<ge> 0 \<and> even x \<and> y = (3^(nat x) - 5) div 4" using `x \<ge> 0` and even_nat_iff by auto
next
  assume assm: "x \<ge> 0 \<and> even x \<and> y = (3^(nat x) - 5) div 4"
  then have "3^(nat x) = 4*y + 5" using warmup1_natx and even_nat_iff by blast
  thus "3 powr x = 4*y + 5" using assm powr_real_of_int by fastforce
qed

subsection "Warmup 2"
text "Prove that, for all real $a$ and $b$ we have
$$(a+b)^4 \\leq 8(a^4 + b^4).$$"

text "This problem is simple enough for Isabelle to solve it automatically
 --- with the Sum of Squares decision procedure."

theorem
  "(a+b)^4 \<le> 8*(a^4 + b^4)" for a b :: real
  by sos

text "Of course, we would rather elaborate.
We will make use of the inequality known as @{term sum_squares_bound}:
@{thm [display] sum_squares_bound [no_vars]}"
theorem
  "(a+b)^4 \<le> 8*(a^4 + b^4)" for a b :: real
proof -
  have lemineq: "2*x^3*y \<le> x^4 + x^2*y^2" for x y :: real
    using sum_squares_bound [of x y]
      and mult_left_mono [where c="x^2"]
    by (force simp add: numeral_eq_Suc algebra_simps)

  have "(a+b)^4 = a^4 + 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + b^4" by algebra
  also have "... \<le> a^4 + 2*(a^4 + a^2*b^2) + 6*a^2*b^2 + 2*(b^4 + a^2*b^2) + b^4"
    using lemineq [of a b]
      and lemineq [of b a]
    by (simp add: algebra_simps)
  also have "... = 3*a^4 + 3*b^4 + 10*a^2*b^2" by (simp add: algebra_simps)
  also have "... \<le> 8*(a^4 + b^4)"
    using sum_squares_bound [of "a^2" "b^2"]
    by simp
  finally show ?thesis.
qed

text "Another interesting proof is by Jensen's inequality.
In Isabelle, it's known as the @{term convex_on} lemma:
@{thm [display] convex_on [no_vars]}

Note that the sequences @{term u} and @{term x} are modeled as functions
@{typ \<open>nat \<Rightarrow> real\<close>}, thus instead of $u_i$ we have @{term \<open>u i\<close>}.

Make sure not to confuse the @{term convex_on} lemma
with the @{term convex_on} predicate, which is defined by
@{term convex_on_def}:
@{thm [display] convex_on_def [no_vars]}

The bulk of the work, of course, is in showing that our function,
$x \\mapsto x^4$, is convex."

theorem
  "(a+b)^4 \<le> 8*(a^4 + b^4)" for a b :: real
proof -
  let ?f = "\<lambda>x. x^4"
  have "convex_on UNIV ?f"
  proof (rule f''_ge0_imp_convex)
    show "convex UNIV" by auto
    let ?f' = "\<lambda>x. 4*x^3"
    show "((\<lambda>x. x^4) has_real_derivative ?f' x) (at x)" for x :: real
      using DERIV_pow [where n=4] by fastforce
    let ?f'' = "\<lambda>x. 12*x^2"
    show "((\<lambda>x. 4*x^3) has_real_derivative ?f'' x) (at x)" for x :: real
      using DERIV_pow [where n=3]
        and DERIV_cmult [where c=4]
      by fastforce
    show "0 \<le> 12 * x^2" for x :: real
      by auto
  qed
  hence "(a/2 + b/2)^4 \<le> a^4/2 + b^4/2" (is "?lhs \<le> ?rhs")
    using convex_onD [where t="1/2"] by fastforce
  also have "?lhs = ((a + b)/2)^4" by algebra
  also have "... = (a+b)^4/16" using power_divide [of "a+b" 2, where n=4] by fastforce
  finally show ?thesis by auto
qed

end %invisible
