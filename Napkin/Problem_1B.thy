theory Problem_1B
  imports "HOL-Algebra.Algebra"
begin

text \<open>Problem 1B asks for a special case of Lagrange's theorem, thus we
avoid using the general variant.\<close>
(* TAGS: group-theory *)
theorem (in comm_group) problem1B:
  assumes finite: "finite (carrier G)"
  assumes closed: "g \<in> carrier G"
  shows "g [^] order G = \<one>"
proof -
  let ?f = "\<lambda>x. g \<otimes> x"
  have [simp]: "?f ` carrier G = carrier G"
    by (simp add: closed group.surj_const_mult)
  have "inj_on ?f (carrier G)"
    by (simp add: closed group.inj_on_cmult)
  hence "(\<Otimes>x \<in> carrier G. x) = (\<Otimes>x \<in> carrier G. g \<otimes> x)"
    using finprod_reindex[where h="?f" and A="carrier G" and f="\<lambda>x. x", symmetric]
    by simp
  also have "... = (\<Otimes>x \<in> carrier G. g) \<otimes> (\<Otimes>x \<in> carrier G. x)" 
    using closed by (intro finprod_multf) auto
  finally have "(\<Otimes>x \<in> carrier G. g) = \<one>"
    using closed by (intro r_cancel_one'[THEN iffD1]) auto
  thus ?thesis
    using closed unfolding order_def by (simp add: finprod_const)
qed

end