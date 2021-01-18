theory Problem_1
  imports "HOL-Number_Theory.Number_Theory"
begin

text \<open>Find all positive integers \<open>n\<close> such that \<open>4\<^sup>n + 2007\<close> is a perfect square.\<close>
(* TAGS: number-theory *)
theorem problem1:
  assumes "n > 0"
  shows "\<nexists>k::nat. k\<^sup>2 = 4^n + 2007"
proof
  assume "\<exists>k::nat. k\<^sup>2 = 4^n + 2007"
  then obtain k::nat where kk: "k\<^sup>2 = 4^n + 2007" by blast
  with `n > 0` have "[k\<^sup>2 = 3] (mod 4)"
    by (simp add: cong_def flip: mod_add_eq)
  hence "(k mod 4) * (k mod 4) mod 4 = 3"
    by (simp add: cong_def mod_mult_eq power2_eq_square)
  thus False
    using mod_exhaust_less_4[of k] by auto 
qed

end