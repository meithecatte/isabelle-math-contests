theory Problem_1
  imports Complex_Main
begin
(* TAGS: functional-equation *)
text \<open>Find all functions $f : \<real> \to \<real>$ satisfying
$$x f(x) + f(-x) = 1.$$\<close>

theorem
  fixes f :: "real \<Rightarrow> real"
  shows "(\<forall>x. x * f x + f (-x) = 1)
    \<longleftrightarrow> (\<forall>x. f x = (1 + x) / (x\<^sup>2 + 1))"
    (is "(\<forall>x. ?eq x) \<longleftrightarrow> (\<forall>x. ?def x)")
proof
  assume "\<forall>x. ?eq x"
  then have "?eq x" for x..
  hence f_negx: "f (-x) = 1 - x*f x" for x by smt
  have f_x: "f x = 1 + x*f (-x)" for x
    using f_negx[where x="-x"] by simp
  have "f x = 1 + x - x*x*f x" for x
    using f_x[of x]
    by (simp add: f_negx) algebra
  hence "f x + x\<^sup>2 * f x = 1 + x" for x
    unfolding power2_eq_square by smt
  hence "(x\<^sup>2 + 1)*f x = 1 + x" for x
    by (simp add: Rings.ring_distribs(2) add.commute)
  moreover have "x\<^sup>2 + 1 \<noteq> 0" for x :: real
    unfolding power2_eq_square by (smt zero_le_square)
  ultimately have "f x = (1 + x) / (x\<^sup>2 + 1)" for x
    apply (intro eq_divide_imp)
    by (auto simp add: ac_simps)
  thus "\<forall>x. ?def x"..
next
  assume "\<forall>x. ?def x"
  then have [simp]: "?def x" for x..
  have [simp]: "x*x + 1 \<noteq> 0" for x :: real
    by (smt zero_le_square)
  show "\<forall>x. ?eq x"
    apply (auto simp add: power2_eq_square
        simp flip: add_divide_distrib)
    by algebra
qed

end