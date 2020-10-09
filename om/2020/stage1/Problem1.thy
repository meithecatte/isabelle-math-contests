section "Series I (September)"
subsection "Problem 1"
theory Problem1
  imports Complex_Main
begin

text "Let $a, b$ be real numbers. Let's assume that, for all
real numbers $x, y$ the inequality
$|(ax + by)(ay + bx)| \\leq x^2 + y^2$
is satisfied. Show that $a^2 + b^2 \\leq 2$."
theorem OM1:
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

end