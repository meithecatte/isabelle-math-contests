theory Problem_3
  imports Complex_Main
begin

text \<open>Positive integers \<open>a\<close>, \<open>b\<close>, \<open>z\<close> satisfy \<open>ab = z\<^sup>2 + 1\<close>. Prove that
there exist positive integers \<open>x\<close> and \<open>y\<close> such that
(* TAGS: number-theory *)
$$\frac{a}{b} = \frac{x^2 + 1}{y^2 + 1}.$$\<close>

theorem problem3:
  fixes a b z :: int
  assumes "a > 0"  "b > 0"  "z > 0"
  assumes "a*b = z\<^sup>2 + 1"
  shows "\<exists>x y. rat_of_int a / of_int b = of_int (x\<^sup>2 + 1)/of_int (y\<^sup>2 + 1)" (is "\<exists>x y. ?P x y")
proof (rule, rule)
  let ?x = "z + a" and ?y = "z + b"
  have "a * (?y\<^sup>2 + 1) = b * (?x\<^sup>2 + 1)"
    using `a*b = z\<^sup>2 + 1`
    unfolding power2_eq_square
    by algebra
  moreover have "rat_of_int b \<noteq> 0"
    using `b > 0` by simp
  moreover have "rat_of_int (?y\<^sup>2 + 1) \<noteq> 0"
  proof -
    have "?y\<^sup>2 + 1 > 0" by simp
    thus ?thesis by linarith
  qed
  ultimately show "?P ?x ?y"
    by (simp add: frac_eq_eq flip: of_int_mult of_int_add)
qed

end
