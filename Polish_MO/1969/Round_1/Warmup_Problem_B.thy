theory Warmup_Problem_B
  imports
    Complex_Main
    "HOL-Library.Sum_of_Squares"
    "HOL-Analysis.Analysis"
begin

subsection "Warmup problem B"
(* TAGS: inequality multiple-solutions calculus *)
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

theorem warmup2:
  "(a+b)^4 \<le> 8*(a^4 + b^4)" for a b :: real
proof -
  let ?f = "\<lambda>x. x^4"
  have "convex_on UNIV ?f"
  proof (rule f''_ge0_imp_convex)
    show "convex UNIV" by auto
    let ?f' = "\<lambda>x. 4*x^3"
    show "(?f has_real_derivative ?f' x) (at x)" for x :: real
      using DERIV_pow [where n=4] by fastforce
    let ?f'' = "\<lambda>x. 12*x^2"
    show "(?f' has_real_derivative ?f'' x) (at x)" for x :: real
      using DERIV_pow [where n=3]
        and DERIV_cmult [where c=4]
      by fastforce
    show "0 \<le> ?f'' x" for x :: real
      by auto
  qed
  hence "(a/2 + b/2)^4 \<le> a^4/2 + b^4/2" (is "?lhs \<le> ?rhs")
    using convex_onD [where t="1/2"] by fastforce
  also have "?lhs = ((a + b)/2)^4" by algebra
  also have "... = (a+b)^4/16" using power_divide [of "a+b" 2, where n=4] by fastforce
  finally show ?thesis by auto
qed

end