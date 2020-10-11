section "Warmup problems (Series I)"

text "Long ago, the Polish Math Olympiad published, apart from
12 problems to be solved and mailed over 3 months, a set of 12
warmup problems, which were similar in spirit, but easier."

theory WarmupI
  imports
    Complex_Main
    Future_Library.Future_Library
    "HOL-Library.Sum_of_Squares"
    "HOL-Library.Quadratic_Discriminant"
    "HOL-Number_Theory.Cong"
    "HOL-Analysis.Analysis"
begin

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

text "Here is an alternative proof ---
hopefully it will be instructive in doing calculations mod $n$."

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

text "This allows us to prove the theorem, provided we assume $x$ is a natural number."

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
    then have "((3::int)^x - 5) mod 4 = 0"
      by (simp add: cong_def mod_diff_cong)
    thus ?thesis using y_form by auto
  qed
  ultimately show ?thesis by blast
qed

text "To consider negative values of $x$, we'll need to venture into the reals:"

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

corollary warmup1:
  fixes x y :: int
  shows "3 powr x = 4*y + 5 \<longleftrightarrow> x \<ge> 0 \<and> even x \<and> y = (3^(nat x) - 5) div 4"
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

subsection "Warmup 3"

text "This one is a straight-forward equation:"

theorem warmup3:
  "\<bar>x-1\<bar>*\<bar>x+2\<bar>*\<bar>x-3\<bar>*\<bar>x+4\<bar> = \<bar>x+1\<bar>*\<bar>x-2\<bar>*\<bar>x+3\<bar>*\<bar>x-4\<bar>
    \<longleftrightarrow> x \<in> {0, sqrt 7, -sqrt 7,
                sqrt ((13 + sqrt 73) / 2),
               -sqrt ((13 + sqrt 73) / 2),
                sqrt ((13 - sqrt 73) / 2),
               -sqrt ((13 - sqrt 73) / 2)}"
  (is "?eqn \<longleftrightarrow> ?sols")
proof -
  have "?eqn \<longleftrightarrow> \<bar>(x-1)*(x+2)*(x-3)*(x+4)\<bar> = \<bar>(x+1)*(x-2)*(x+3)*(x-4)\<bar>" (is "_ \<longleftrightarrow> \<bar>?lhs\<bar> = \<bar>?rhs\<bar>")
    by (simp add: abs_mult)
  also have "... \<longleftrightarrow> ?lhs - ?rhs = 0 \<or> ?lhs + ?rhs = 0" by (auto simp add: abs_eq_iff)
  also have "... \<longleftrightarrow> x*(x^2 - 7) = 0 \<or> x^4 - 13*x^2 + 24 = 0" by algebra
  also have "x*(x^2 - 7) = 0 \<longleftrightarrow> x \<in> {0, sqrt 7, -sqrt 7}" using plus_or_minus_sqrt by auto
  also have "x^4 - 13*x^2 + 24 = 0 \<longleftrightarrow> x\<^sup>2 \<in> {(13 + sqrt 73) / 2, (13 - sqrt 73) / 2}"
    using discriminant_nonneg [where x="x^2", of 1 "-13" 24]
    by (auto simp add: algebra_simps discrim_def)
  also have "... \<longleftrightarrow> x \<in> {sqrt ((13 + sqrt 73) / 2),
                         -sqrt ((13 + sqrt 73) / 2),
                          sqrt ((13 - sqrt 73) / 2),
                         -sqrt ((13 - sqrt 73) / 2)}"
  proof -
    have "0 \<le> (13 - sqrt 73) / 2" by (auto simp add: real_le_lsqrt)
    hence "x\<^sup>2 = (13 - sqrt 73) / 2
           \<longleftrightarrow> x \<in> {sqrt ((13 - sqrt 73) / 2),
                    -sqrt ((13 - sqrt 73) / 2)}"
      using plus_or_minus_sqrt
      by blast
    moreover have "x\<^sup>2 = (13 + sqrt 73) / 2
      \<longleftrightarrow> x \<in> {sqrt ((13 + sqrt 73) / 2),
              -sqrt ((13 + sqrt 73) / 2)}"
      by (smt insert_iff power2_minus power_divide real_sqrt_abs real_sqrt_divide real_sqrt_pow2 singletonD)
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed

subsection "Warmup 4"

text "There is a set of $n$ points on a plane with the property that,
in each triplet of points, there's a pair with distance at most 1.
Prove that the set can be covered with two circles of radius 1."

text "There's nothing special about the case of points on a plane,
the theorem can be proved without additional difficulties for any
metric space:"

theorem warmup4_generic:
  fixes S :: "'a::metric_space set"
  assumes "finite S"
  assumes property: "\<And>T. T \<subseteq> S \<and> card T = 3 \<Longrightarrow> \<exists>p\<in>T. \<exists>q\<in>T. p \<noteq> q \<and> dist p q \<le> 1"
  obtains O\<^sub>1 O\<^sub>2 where "S \<subseteq> cball O\<^sub>1 1 \<union> cball O\<^sub>2 1"
proof
  let ?pairs = "S \<times> S"
  let ?dist = "\<lambda>(a, b). dist a b"
  let ?big_pair = "arg_max_on ?dist ?pairs"
  let ?O\<^sub>1 = "(fst ?big_pair)"
  let ?O\<^sub>2 = "(snd ?big_pair)"
  show "S \<subseteq> cball ?O\<^sub>1 1 \<union> cball ?O\<^sub>2 1"
  proof
    fix x
    assume "x \<in> S"

    from `finite S` and `x \<in> S`
    have "finite ?pairs" and "?pairs \<noteq> {}" by auto
    hence OinS: "?big_pair \<in> ?pairs" by (simp add: arg_max_if_finite)

    have "\<forall>(P,Q)\<in>?pairs. dist ?O\<^sub>1 ?O\<^sub>2 \<ge> dist P Q" 
      using `finite ?pairs` and `?pairs \<noteq> {}`
      by (metis (mono_tags, lifting) arg_max_greatest prod.case_eq_if)
    hence greatest: "dist P Q \<le> dist ?O\<^sub>1 ?O\<^sub>2" if "P \<in> S" and "Q \<in> S" for P Q
      using that by blast

    let ?T = "{?O\<^sub>1, ?O\<^sub>2, x}"
    have TinS: "?T \<subseteq> S" using OinS and `x \<in> S` by auto

    {
      presume "?O\<^sub>1 \<noteq> ?O\<^sub>2" and "x \<notin> {?O\<^sub>1, ?O\<^sub>2}"
      then have "card ?T = 3" by auto
    }
    then consider
      (primary) "card ?T = 3" |
      (limit) "x \<in> {?O\<^sub>1, ?O\<^sub>2}" |
      (degenerate) "?O\<^sub>1 = ?O\<^sub>2" by blast
    thus "x \<in> cball ?O\<^sub>1 1 \<union> cball ?O\<^sub>2 1"
    proof cases
      case primary
      obtain p and q where "p \<noteq> q" and "dist p q \<le> 1" and "p \<in> ?T" and "q \<in> ?T"
        using property [of ?T] and `card ?T = 3` TinS
        by auto
      then have
        "dist ?O\<^sub>1 ?O\<^sub>2 \<le> 1 \<or> dist ?O\<^sub>1 x \<le> 1 \<or> dist ?O\<^sub>2 x \<le> 1"
        by (metis dist_commute insertE singletonD)
      thus "x \<in> cball ?O\<^sub>1 1 \<union> cball ?O\<^sub>2 1"
        using greatest and TinS
        by fastforce
    next
      case limit
      then have "dist x ?O\<^sub>1 = 0 \<or> dist x ?O\<^sub>2 = 0" by auto
      thus ?thesis by auto
    next
      case degenerate
      from this greatest TinS have "dist ?O\<^sub>1 x = 0" by auto
      thus ?thesis by auto
    qed
  qed
qed

text "Let's make sure that the particular case of points on a plane also works out:"

corollary warmup4:
  fixes S :: "(real ^ 2) set"
  assumes "finite S"
  assumes property: "\<And>T. T \<subseteq> S \<and> card T = 3 \<Longrightarrow> \<exists>p\<in>T. \<exists>q\<in>T. p \<noteq> q \<and> dist p q \<le> 1"
  obtains O\<^sub>1 O\<^sub>2 where "S \<subseteq> cball O\<^sub>1 1 \<union> cball O\<^sub>2 1"
  using warmup4_generic and assms by auto

end
