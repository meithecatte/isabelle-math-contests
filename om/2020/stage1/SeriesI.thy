section "Series I (September)"
subsection "Problem 1"
theory SeriesI
  imports
    Complex_Main
    "HOL-Analysis.Analysis"
begin

text "Let $a, b$ be real numbers. Let's assume that, for all
real numbers $x, y$ the inequality
$|(ax + by)(ay + bx)| \\leq x^2 + y^2$
is satisfied. Show that $a^2 + b^2 \\leq 2$."
theorem problem1:
  fixes a b :: real
  assumes given: "\<And>x y :: real. \<bar>(a*x + b*y)*(a*y + b*x)\<bar> \<le> x\<^sup>2 + y\<^sup>2"
  shows "a\<^sup>2 + b\<^sup>2 \<le> 2"
proof -
  from given [where x=1 and y=1] have "(a+b)\<^sup>2 \<le> 2"
    by (simp add: power2_eq_square)
  moreover from given [where x=1 and y="-1"] have "(a-b)\<^sup>2 \<le> 2"
    by (simp add: power2_eq_square right_diff_distrib')
  ultimately have "(a+b)\<^sup>2 + (a-b)\<^sup>2 \<le> 4" by auto
  moreover have "(a+b)\<^sup>2 + (a-b)\<^sup>2 = 2*(a\<^sup>2 + b\<^sup>2)" by algebra
  ultimately show "a\<^sup>2 + b\<^sup>2 \<le> 2" by auto
qed

subsection "Problem 3"
text "Let's assume that a positive integer $n$ has no divisor $d$
that satisfies $\\sqrt{n} \\leq d \\leq \\sqrt[3]{n^2}$. Prove that
$n$ has a prime divisor $p > \\sqrt[3]{n^2}$."

theorem problem3:
  fixes n :: nat
  assumes [iff]: "n \<noteq> 0"
  assumes divrange: "\<And>d :: nat. sqrt n \<le> d \<Longrightarrow> d \<le> n powr (2/3) \<Longrightarrow> \<not>d dvd n"
  obtains p where "prime p" and "p > n powr (2/3)"
proof -
  have forbidden_range: "\<not>d dvd n" if "n powr (1/3) \<le> d" and "d \<le> n powr (2/3)" for d :: nat
  proof
    assume "d dvd n"
    from that consider
    (low) "n powr (1/3) \<le> d" "d \<le> sqrt n" |
    (high) "sqrt n \<le> d" "d \<le> n powr (2/3)"
      by fastforce
    then show False
    proof cases
      case low
      from `d dvd n` have mirror_divisor: "(n div d) dvd n" by auto

      have "n/d \<le> n / n powr (1/3)"
        using low by (simp add: frac_le)
      also have "... = n powr 1 / n powr (1/3)" by auto
      also have "... = n powr (2/3)" by (simp del: powr_one flip: powr_diff)
      finally have "n/d \<le> n powr (2/3)".
      moreover from `d dvd n` have "n/d = n div d" by auto
      ultimately have upper_bound: "n div d \<le> n powr (2/3)" by auto

      from `d dvd n` have "d \<noteq> 0"
        by (meson `n \<noteq> 0` dvd_0_left)
      hence "n/d \<ge> n / sqrt n"
        using low by (simp add: frac_le)
      also have "n / sqrt n = sqrt n"
        using real_div_sqrt `n \<noteq> 0` by auto
      finally have "n/d \<ge> sqrt n".
      hence lower_bound: "n div d \<ge> sqrt n" using `n/d = n div d` by auto

      show False using divrange [of "n div d"] mirror_divisor
        and lower_bound upper_bound by auto
    next
      case high
      then show False using divrange `d dvd n` by auto
    qed
  qed

  have "n > 1"
  proof -
    {
      presume "n = 1"
      from this and divrange [of 1] have "\<not> 1 dvd 1" by auto
      moreover have "1 dvd (1::nat)" by auto
      ultimately have False by contradiction
    }
    thus "n > 1" using `n \<noteq> 0`
      by fastforce
  qed

  let ?smalldivs = "{d. d dvd n \<and> d < n powr (1/3)}"
  have "finite ?smalldivs" using finite_divisors_nat by fastforce
  moreover have "?smalldivs \<noteq> {}" proof -
    have "1 \<in> ?smalldivs" using `n > 1` by auto
    thus ?thesis by auto
  qed

  moreover define a where "a = Max ?smalldivs"
  ultimately have "a \<in> ?smalldivs" using Max_in by auto
  hence "a < n powr (1/3)" and "a dvd n" by auto
  hence "a \<noteq> 0" using `n \<noteq> 0` by algebra
  have "\<And>d. d dvd n \<Longrightarrow> d > a \<Longrightarrow> d \<ge> n powr (1/3)"
    using Max_ge `finite ?smalldivs` `?smalldivs \<noteq> {}` a_def
    by (metis (no_types, lifting) mem_Collect_eq not_le)
  hence div_above_a: "\<And>d. d dvd n \<Longrightarrow> d > a \<Longrightarrow> d > n powr (2/3)"
    using forbidden_range
    by force

  note `a < n powr (1/3)`
  also have "n powr (1/3) < n powr 1" using `n > 1` by (intro powr_less_mono) auto
  finally have "a < n" by auto
  hence "n div a > 1"
    using `a dvd n` by fastforce
  then obtain p where "prime p" and "p dvd (n div a)"
    by (metis less_irrefl prime_factor_nat)
  hence "p*a dvd n" using `a dvd n` and `n div a > 1`
    by (metis div_by_0 dvd_div_iff_mult gr_implies_not_zero)
  from this and div_above_a [of "p*a"] have "p*a > n powr (2/3)"
    using `prime p` and prime_nat_iff by fastforce
  moreover have "a * n powr (1/3) < n powr (1/3) * n powr (1/3)"
    using `a < n powr (1/3)` by auto
  moreover have "... = n powr (2/3)" by (simp flip: powr_add)
  ultimately have "p*a > a*n powr (1/3)" by simp
  hence "p > n powr (1/3)" using `a \<noteq> 0` by simp
  hence "p > n powr (2/3)" using forbidden_range [of p] and `p * a dvd n` by force
  moreover note `prime p`
  ultimately show ?thesis using that [of p] by auto
qed
end