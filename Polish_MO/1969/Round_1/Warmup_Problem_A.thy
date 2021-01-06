theory Warmup_Problem_A
  imports
    Complex_Main
    "HOL-Number_Theory.Cong"
begin

subsection "Warmup problem A"
(* TAGS: number-theory congruences *)
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

theorem warmupA_natx:
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

corollary warmupA:
  fixes x y :: int
  shows "3 powr x = 4*y + 5 \<longleftrightarrow> x \<ge> 0 \<and> even x \<and> y = (3^(nat x) - 5) div 4"
proof
  assume assm: "3 powr x = 4*y + 5"
  then have "x \<ge> 0" using powr_int_pos by fastforce
  hence "3 powr (nat x) = 4*y + 5" using assm by simp
  hence "(3::real)^(nat x) = 4*y + 5" using powr_realpow by auto
  hence with_nat: "3^(nat x) = 4*y + 5" using of_int_eq_iff by fastforce
  hence "even (nat x) \<and> y = (3^(nat x) - 5) div 4" using warmupA_natx by auto
  thus "x \<ge> 0 \<and> even x \<and> y = (3^(nat x) - 5) div 4" using `x \<ge> 0` and even_nat_iff by auto
next
  assume assm: "x \<ge> 0 \<and> even x \<and> y = (3^(nat x) - 5) div 4"
  then have "3^(nat x) = 4*y + 5" using warmupA_natx and even_nat_iff by blast
  thus "3 powr x = 4*y + 5" using assm powr_real_of_int by fastforce
qed

end