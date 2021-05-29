theory PoTD_15
  imports
    "HOL-Analysis.Analysis"
    "HOL-Library.Quadratic_Discriminant"
begin
(* TAGS: real-analysis *)

text \<open>Let \<open>a\<close> be a positive real number. Define a sequence \<open>x\<^sub>n\<close> by

\<open>x\<^sub>0 = 0, x\<^bsub>n+1\<^esub> = a + x\<^sub>n\<^sup>2, n \<ge> 0\<close>.

Find a necessary and sufficient condition on \<open>a\<close> for a finite
limit $\lim_{n \to \infty} x_n$ existing.\<close>

context
  fixes a :: real
  assumes "a > 0"
begin

text \<open>We will define the sequence as a function \<open>x : \<nat> \<rightarrow> \<real>\<close>.\<close>

fun x :: "nat \<Rightarrow> real" ("x\<^bsub>_\<^esub>") where
  "x\<^bsub>0\<^esub> = 0" |
  "x\<^bsub>Suc n\<^esub> = a + x\<^bsub>n\<^esub>\<^sup>2"

lemma x_nonneg: "x\<^bsub>n\<^esub> \<ge> 0"
  using `a > 0` by (induction n, auto)

lemma x_incseq: "x\<^bsub>n\<^esub> \<le> x\<^bsub>Suc n\<^esub>"
proof (induction n)
  case 0
  from `a > 0` show "x\<^bsub>0\<^esub> \<le> x\<^bsub>Suc 0\<^esub>" by simp 
next
  case (Suc k)
  from `x\<^bsub>k\<^esub> \<le> x\<^bsub>Suc k\<^esub>`
  have "x\<^bsub>k\<^esub>\<^sup>2 \<le> x\<^bsub>Suc k\<^esub>\<^sup>2"
    using x_nonneg by (smt (z3) power2_le_imp_le) 
  hence "a + x\<^bsub>k\<^esub>\<^sup>2 \<le> a + x\<^bsub>Suc k\<^esub>\<^sup>2" by auto
  thus "x\<^bsub>Suc k\<^esub> \<le> x\<^bsub>Suc (Suc k)\<^esub>" by auto
qed

theorem "convergent x \<longleftrightarrow> a \<le> 1/4" 
proof
  assume "convergent x"
  then obtain L where "x \<longlonglongrightarrow> L"
    using convergent_def by auto
  define f where "f u = a + u\<^sup>2" for u :: real
  have "continuous (at u) f" for u :: real
    unfolding f_def by auto
  with `x \<longlonglongrightarrow> L` have "(f \<circ> x) \<longlonglongrightarrow> f L"
    using continuous_at_sequentially by auto
      \<comment> \<open>\<open>continuous_at_sequentially\<close> is the theorem usually known as sequential continuity.\<close>
  moreover have "(f \<circ> x) \<longlonglongrightarrow> L"
  proof -
    have "f \<circ> x = (\<lambda>n. x\<^bsub>Suc n\<^esub>)"
      using f_def by auto
        \<comment> \<open>i.e. \<open>f \<circ> x\<close> is the same sequence as \<open>x\<close>, but without the first element.\<close>
    thus "(f \<circ> x) \<longlonglongrightarrow> L"
      using `x \<longlonglongrightarrow> L` and LIMSEQ_Suc by fastforce 
  qed
  ultimately have "f L = L"
    by (rule LIMSEQ_unique)
  hence "L\<^sup>2 - L + a = 0"
    unfolding f_def by simp
  hence "discrim 1 (-1) a \<ge> 0"
    using discriminant_negative[of 1 "-1" a] by fastforce
  thus "a \<le> 1/4"
    unfolding discrim_def by simp
next
  assume "a \<le> 1/4"
  have "x\<^bsub>n\<^esub> \<le> 1/2" for n
  proof (induction n)
    case 0
    then show "x\<^bsub>0\<^esub> \<le> 1/2" by simp
  next
    case (Suc k)
    from `x k \<le> 1/2`
    have "x\<^bsub>k\<^esub>\<^sup>2 \<le> (1/2)\<^sup>2"
      using x_nonneg by (smt (z3) power2_le_imp_le)
    hence "a + x\<^bsub>k\<^esub>\<^sup>2 \<le> 1/2"
      using `a \<le> 1/4` by (simp add: power2_eq_square)
    then show "x\<^bsub>Suc k\<^esub> \<le> 1/2" by simp
  qed
  with x_incseq obtain L where "x \<longlonglongrightarrow> L" and "\<forall>n. x\<^bsub>n\<^esub> \<le> L"
    using incseq_convergent by (blast intro!: incseq_SucI)
  thus "convergent x" by (auto simp add: convergent_def)
qed

end
end
