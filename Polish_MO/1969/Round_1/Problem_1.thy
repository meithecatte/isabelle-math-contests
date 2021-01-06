theory Problem_1
  imports Complex_Main
begin

subsection "Problem 1"
(* TAGS: number-theory diophantine-equation *)
text "Solve the equation in the integers:"

theorem problem1:
  fixes x y :: int
  assumes "x \<noteq> 0" and "y \<noteq> 0"
  shows "1 / x\<^sup>2 + 1 / (x*y) + 1 / y\<^sup>2 = 1
    \<longleftrightarrow> x = 1 \<and> y = -1 \<or> x = -1 \<and> y = 1"
    (is "?eqn \<longleftrightarrow> ?sols")
proof
  \<comment> \<open>Unfortunately, removing the conversions between int and real takes a few lines\<close>
  let ?x = "real_of_int x" and ?y = "real_of_int y"
  assume "?eqn"
  then have "1 / ?x\<^sup>2 + 1 / (?x*?y) + 1 / ?y\<^sup>2 = 1" by auto
  hence "?x\<^sup>2*?y\<^sup>2 / ?x\<^sup>2 + ?x\<^sup>2*?y\<^sup>2 / (?x*?y) + ?x\<^sup>2*?y\<^sup>2 / ?y\<^sup>2 = ?x\<^sup>2*?y\<^sup>2"
    by algebra
  hence "?x\<^sup>2 + ?x*?y + ?y\<^sup>2 = ?x\<^sup>2 * ?y\<^sup>2" using `x \<noteq> 0` `y \<noteq> 0`
    by (simp add: power2_eq_square)
  hence inteq: "x\<^sup>2 + x*y + y\<^sup>2 = x\<^sup>2 * y\<^sup>2"
    using of_int_eq_iff by fastforce

  define g where "g = gcd x y"
  then have "g \<noteq> 0" and "g > 0" using `x \<noteq> 0` `y \<noteq> 0` by auto
  define x' y' where "x' = x div g" and "y' = y div g"
  then have "x' * g = x" and "y' * g = y" using g_def by auto
  from inteq and this have "g\<^sup>2 * (x'\<^sup>2 + x' * y' + y'\<^sup>2) = x'\<^sup>2 * y'\<^sup>2 * g^4"
    by algebra
  hence reduced: "x'\<^sup>2 + x' * y' + y'\<^sup>2 = x'\<^sup>2 * y'\<^sup>2 * g\<^sup>2" using `g \<noteq> 0` by algebra

  hence "x' dvd y'\<^sup>2" and "y' dvd x'\<^sup>2"
    by algebra+
  moreover have "coprime x' (y'\<^sup>2)" "coprime (x'\<^sup>2) y'"
    unfolding x'_def y'_def g_def
    using assms div_gcd_coprime by auto
  ultimately have "is_unit x'" "is_unit y'"
    unfolding coprime_def by auto
  hence abs1: "\<bar>x'\<bar> = 1 \<and> \<bar>y'\<bar> = 1" using assms by auto
  then consider (same_sign) "x' = y'" | (diff_sign) "x' = -y'" by fastforce
  thus ?sols
  proof cases
    case same_sign
    then have "x' * y' = 1"
      using abs1 and zmult_eq_1_iff by fastforce
    hence "g\<^sup>2 = 3"
      using abs1 same_sign and reduced by algebra
    hence "1\<^sup>2 < g\<^sup>2" and "g\<^sup>2 < 2\<^sup>2" by auto
    hence "1 < g" and "g < 2"
      using `g > 0` and power2_less_imp_less by fastforce+
    hence False by auto
    thus ?sols by auto
  next
    case diff_sign
    then have "x' * y' = -1"
      using abs1
      by (smt mult_cancel_left2 mult_cancel_right2)
    hence "g\<^sup>2 = 1"
      using abs1 diff_sign and reduced by algebra
    hence "g = 1" using `g > 0`
      by (smt power2_eq_1_iff)
    hence "x = x'" and "y = y'"
      unfolding x'_def and y'_def by auto
    thus ?sols using abs1 and diff_sign by auto
  qed
next
  assume ?sols
  then show ?eqn by auto
qed

end