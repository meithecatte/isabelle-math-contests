theory Warmup_Problem_C
  imports
    Complex_Main
    "HOL-Library.Quadratic_Discriminant"
begin

subsection "Warmup problem C"
(* TAGS: equation *)
text "This one is a straight-forward equation:"

theorem warmup3:
  "\<bar>x-1\<bar>*\<bar>x+2\<bar>*\<bar>x-3\<bar>*\<bar>x+4\<bar> = \<bar>x+1\<bar>*\<bar>x-2\<bar>*\<bar>x+3\<bar>*\<bar>x-4\<bar>
    \<longleftrightarrow> x \<in> {0, sqrt 7, -sqrt 7,
                sqrt ((13 + sqrt 73) / 2),
               -sqrt ((13 + sqrt 73) / 2),
                sqrt ((13 - sqrt 73) / 2),
               -sqrt ((13 - sqrt 73) / 2)}"
  (is "?eqn \<longleftrightarrow> ?sols")
proof -
  have "?eqn \<longleftrightarrow> \<bar>(x-1)*(x+2)*(x-3)*(x+4)\<bar> = \<bar>(x+1)*(x-2)*(x+3)*(x-4)\<bar>" (is "_ \<longleftrightarrow> \<bar>?lhs\<bar> = \<bar>?rhs\<bar>")
    by (simp add: abs_mult)
  also have "... \<longleftrightarrow> ?lhs - ?rhs = 0 \<or> ?lhs + ?rhs = 0" by (auto simp add: abs_eq_iff)
  also have "... \<longleftrightarrow> x*(x^2 - 7) = 0 \<or> x^4 - 13*x^2 + 24 = 0" by algebra
  also have "x*(x^2 - 7) = 0 \<longleftrightarrow> x \<in> {0, sqrt 7, -sqrt 7}" using plus_or_minus_sqrt by auto
  also have "x^4 - 13*x^2 + 24 = 0 \<longleftrightarrow> x\<^sup>2 \<in> {(13 + sqrt 73) / 2, (13 - sqrt 73) / 2}"
    using discriminant_nonneg [where x="x^2", of 1 "-13" 24]
    by (auto simp add: algebra_simps discrim_def)
  also have "... \<longleftrightarrow> x \<in> {sqrt ((13 + sqrt 73) / 2),
                         -sqrt ((13 + sqrt 73) / 2),
                          sqrt ((13 - sqrt 73) / 2),
                         -sqrt ((13 - sqrt 73) / 2)}"
  proof -
    have "0 \<le> (13 - sqrt 73) / 2" by (auto simp add: real_le_lsqrt)
    hence "x\<^sup>2 = (13 - sqrt 73) / 2
           \<longleftrightarrow> x \<in> {sqrt ((13 - sqrt 73) / 2),
                    -sqrt ((13 - sqrt 73) / 2)}"
      using plus_or_minus_sqrt
      by blast
    moreover have "x\<^sup>2 = (13 + sqrt 73) / 2
      \<longleftrightarrow> x \<in> {sqrt ((13 + sqrt 73) / 2),
              -sqrt ((13 + sqrt 73) / 2)}"
      by (smt insert_iff power2_minus power_divide real_sqrt_abs real_sqrt_divide real_sqrt_pow2 singletonD)
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed

end