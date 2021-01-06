theory Problem_2
  imports
    "HOL-Number_Theory.Number_Theory"
    "Common.NT_Facts"
begin
(* TAGS: number-theory *)
text \<open>Positive integers $p$, $a$ and $b$ satisfy the equation $p^2 + a^2 = b^2$.
Prove that if $p$ is a prime greater than 3, then $a$ is a multiple of 12 and
$2(p + a + 1)$ is a perfect square.\<close>

theorem problem2:
  fixes p a b :: int
  assumes "p\<^sup>2 + a\<^sup>2 = b\<^sup>2"
    and p: "prime p"   "p > 3"
    and pos: "a > 0"   "b > 0"
  shows "12 dvd a"
    and "\<exists>k. k\<^sup>2 = 2*(p + a + 1)"
proof -
  from `p\<^sup>2 + a\<^sup>2 = b\<^sup>2` have *: "p * p = (b + a) * (b - a)"
    by (simp add: power2_eq_square flip: square_diff_square_factored)
  hence "b + a dvd p * p"
    by auto
  have "b + a \<in> {1, p, p*p}"
  proof -
    from `b + a dvd p*p` obtain x y where
      "b + a = x * y" and "x dvd p" and "y dvd p"
      using dvd_productE by blast
    with `prime p` have "\<bar>x\<bar> = 1 \<or> \<bar>x\<bar> = p" and "\<bar>y\<bar> = 1 \<or> \<bar>y\<bar> = p"
      by (auto simp add: prime_int_iff)
    with pos and `b + a = x * y` show "b + a \<in> {1, p, p*p}"
      by (cases "x \<ge> 0"; cases "y \<ge> 0"; auto; smt zero_less_mult_iff)
  qed
  moreover have "b + a \<noteq> 1" using `a > 0` `b > 0` by auto
  moreover have "b + a \<noteq> p"
  proof
    assume "b + a = p"
    with * and pos have "b - a = p"
      by auto
    from `b - a = p` and `b + a = p` have "a = 0" by auto
    thus False using pos by auto
  qed
  ultimately have 1: "b + a = p * p" by auto
  with * pos have 2: "b - a = 1" by auto

  from 1 and 2 have **: "2 * a = p * p - 1" by auto
  moreover have "[p * p = 1] (mod 24)" using p by (intro pp_mod24)
      \<comment> \<open>This property is proved in @{theory Common.NT_Facts}\<close>

  ultimately have "24 dvd 2*a"
    unfolding cong_def using mod_eq_dvd_iff by fastforce
  thus "12 dvd a"
    by auto

  from ** have "2*(p + a + 1) = (p + 1)\<^sup>2"
    by (auto simp add: ac_simps power2_sum) (simp add: power2_eq_square)
  thus "\<exists>k. k\<^sup>2 = 2*(p + a + 1)"
    by auto
qed

end