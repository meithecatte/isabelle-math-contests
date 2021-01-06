theory Problem_789
  imports Complex_Main
begin

text \<open>Find all functions $f : \<real> \to \<real>$ satisfying
$$f(f(x) + y) = 4yf(x) + f(x^2 - y).$$\<close>
(* TAGS: functional-equation *)
theorem
  fixes f :: "real \<Rightarrow> real"
  shows "(\<forall>x y. f (f x + y) = 4*y*f x + f (x\<^sup>2 - y))
    \<longleftrightarrow> (\<forall>x. f x = x\<^sup>2) \<or> (\<forall>x. f x = 0)"
  (is "(\<forall>x y. ?eqn x y) \<longleftrightarrow> _")
proof
  assume "\<forall>x y. ?eqn x y"
  then have eqn: "?eqn x y" for x y by auto
  have [simp]: "f (x\<^sup>2 + f x) = 4*x\<^sup>2*f x + f 0" for x
    using eqn[where y="x\<^sup>2" and x=x]
    unfolding power2_eq_square by smt
  have opts: "f x = 0 \<or> f x = x\<^sup>2" for x
    using eqn[where y="-f x" and x=x, simplified]
    by auto
  {
    fix a
    presume "f a \<noteq> a\<^sup>2"
    then have "a \<noteq> 0" and [simp]: "f a = 0"
      using opts by fastforce+
    fix y
    have *: "f y = f (a\<^sup>2 - y)"
      using eqn[where x=a and y=y] by simp
    presume "f y \<noteq> 0"
    hence "f y = y\<^sup>2" using opts by auto
    moreover from * and `f y \<noteq> 0` have "f (a\<^sup>2 - y) = (a\<^sup>2 - y)\<^sup>2"
      using opts by auto
    ultimately have "y\<^sup>2 = (a\<^sup>2 - y)\<^sup>2"
      using * by auto
    with `a \<noteq> 0` have "a\<^sup>2 = 2*y"
      by (simp add: power2_eq_square) algebra
  }
  hence **: "f a \<noteq> a\<^sup>2 \<Longrightarrow> 2*y \<noteq> a\<^sup>2 \<Longrightarrow> f y = 0" for a y
    by fastforce

  {
    fix a and y
    assume "f a \<noteq> a\<^sup>2" and "2*y = a\<^sup>2"
    moreover obtain b where "2*y \<noteq> b\<^sup>2" and "b \<noteq> 0" and "b \<noteq> y"
      by (smt four_x_squared one_power2)
    ultimately have "f b \<noteq> b\<^sup>2" using ** [where y=b and a=a]
      by simp
    with ** [where a=b and y=y] and `2*y \<noteq> b\<^sup>2`
    have "f y = 0" by simp
  }
  with ** have "f a \<noteq> a\<^sup>2 \<Longrightarrow> f y = 0" for a y
    by blast
  thus "(\<forall>x. f x = x\<^sup>2) \<or> (\<forall>x. f x = 0)"
    using opts by blast
next
  assume "(\<forall>x. f x = x\<^sup>2) \<or> (\<forall>x. f x = 0)"
  then show "\<forall>x y. ?eqn x y"
    apply (auto simp add: power2_eq_square)
    apply (thin_tac "\<forall>x. f x = x * x")
    by algebra
qed 