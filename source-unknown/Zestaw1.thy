theory Zestaw1
  imports
    Complex_Main
    "HOL-Library.Sum_of_Squares"
    "HOL-Number_Theory.Cong"
    "HOL-Analysis.Analysis"
begin

(* These problems come from my high school's math circle. I know they originate
   in some old Polish Math Olympiad, but I haven't yet been able to locate the
   exact year. *)

(* Warmup 1: Solve the equation 3\<^sup>x = 4y + 5 in the integers *)

(* We begin with the following lemma: *)

lemma even_power_3: "[3^k = 1::int] (mod 4) \<longleftrightarrow> even k"
proof -
  have "[3^k = (-1::int)^k] (mod 4)"
    by (intro cong_pow) (auto simp: cong_def)
  thus ?thesis
    by (auto simp: cong_def minus_one_power_iff)
qed

(* This is, of course, not the only strategy. We leave an alternative proof,
   in the hope that it will be instructive in doing calculations mod n. *)

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

value "(of_int 3) powr (of_int 4)"

(* TODO (didn't really investigate): original problem statement gives x :: int,
 (how) can I generalize this to x :: int without infinite pain? *)
theorem warmup1:
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
    then have "[(3::int)^x - 5 = 1 - 5] (mod 4)"
      by (metis even_power_3 cong_diff cong_refl)
    also have "[1 - 5 = 0::int] (mod 4)"
      by (auto simp: cong_def)
    finally have "(3^x - 5::int) mod 4 = 0"
      by (auto simp: cong_def)
    thus ?thesis using y_form by auto
  qed
  ultimately show ?thesis by blast
qed

(* Warmup 2: Prove that, for all real a and b we have: *)

(* This problem is simple enough for Isabelle to solve it automatically
 - with the Sum of Squares decision procedure *)

theorem warmup2_sos:
  fixes a b :: real
  shows "(a+b)^4 \<le> 8*(a^4 + b^4)"
  by sos

(* Of course, we would rather elaborate: *)
theorem warmup2:
  fixes a b :: real
  shows "(a+b)^4 \<le> 8*(a^4 + b^4)"
proof -
  have lemineq: "2*x^3*y \<le> x^4 + x^2*y^2" for x y :: real
    using sum_squares_bound [of x y]
      and mult_left_mono [of _ _ "x^2"]
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

end
