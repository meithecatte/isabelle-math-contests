section "Series II"

theory SeriesII
  imports
    Complex_Main
    "HOL-Analysis.Analysis"
begin

subsection "Problem 5"

text \<open>Real numbers $M, a_1, a_2, \ldots, a_{10}$ are given. Prove that,
if $a_1x_1 + a_2x_2 + \cdots + a_{10}x_{10} \leq M$ for all $x_i$ such that
$|x_i| = 1$, then
$$ \sqrt{a_1^2 + a_2^2 + \cdots + a_{10}^2} \leq M.$$\<close>

lemma sqr_sum_ineq:
  "list_all (\<lambda>x. x \<ge> 0) xs \<Longrightarrow> sum_list (map power2 xs) \<le> (sum_list xs)\<^sup>2"
  for xs :: "real list"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  note IH = `list_all (\<lambda>x. x \<ge> 0) xs \<Longrightarrow> sum_list (map power2 xs) \<le> (sum_list xs)\<^sup>2`
  note nonneg = `list_all (\<lambda>x. x \<ge> 0) (x # xs)`
  then have "x \<ge> 0" and nonneg': "list_all (\<lambda>x. x \<ge> 0) xs" by auto
  hence "sum_list xs \<ge> 0" using sum_list_nonneg unfolding list_all_def by auto

  have "sum_list (map power2 (x # xs)) = x\<^sup>2 + sum_list (map power2 xs)" by auto
  also have "... \<le> x\<^sup>2 + (sum_list xs)\<^sup>2" using IH and nonneg' by auto
  also have "... \<le> x\<^sup>2 + 2*x*(sum_list xs) + (sum_list xs)\<^sup>2"
    using `x \<ge> 0` and `sum_list xs \<ge> 0` by auto
  also have "... = (x + sum_list xs)\<^sup>2" by algebra
  also have "... = (sum_list (x # xs))\<^sup>2" by auto
  finally show "sum_list (map power2 (x # xs)) \<le> (sum_list (x # xs))\<^sup>2".
qed

definition sgn' :: "real \<Rightarrow> real" where
"sgn' x = (if x \<ge> 0 then 1 else -1)"

lemma [simp]: "x * sgn' x = \<bar>x\<bar>"
  unfolding sgn'_def by auto

lemma [simp]: "\<bar>sgn' x\<bar> = 1"
  unfolding sgn'_def by auto

theorem problem5:
  fixes M :: real and as :: "real list"
  assumes *: "\<And>xs. list_all (\<lambda>x. \<bar>x\<bar> = 1) xs \<Longrightarrow> sum_list (map2 (*) as xs) \<le> M"
  shows "sqrt (sum_list (map power2 as)) \<le> M"
proof -
  define xs where "xs = map sgn' as"
  then have "list_all (\<lambda>x. \<bar>x\<bar> = 1) xs" unfolding list_all_def by auto
  with * [of xs] have sum_abs_below_M: "sum_list (map abs as) \<le> M"
    unfolding xs_def by (auto simp add: map2_map_map [where f=id, simplified])
  moreover have sum_abs_nonneg: "sum_list (map abs as) \<ge> 0"
    using sum_list_abs abs_ge_zero order_trans by blast
  ultimately have "M \<ge> 0" by auto

  have [simp]: "power2 \<circ> abs = (power2 :: 'a \<Rightarrow> ('a :: linordered_idom))"
    by auto
  have "list_all (\<lambda>x. x \<ge> 0) (map abs as)" unfolding list_all_def by auto
  from sqr_sum_ineq [OF this]
  have "sum_list (map power2 as) \<le> (sum_list (map abs as))\<^sup>2"
    by auto
  also have "... \<le> M\<^sup>2" using sum_abs_below_M sum_abs_nonneg by auto
  finally have "sum_list (map power2 as) \<le> M\<^sup>2".
  with `M \<ge> 0` show "sqrt (sum_list (map power2 as)) \<le> M"
    by (metis abs_of_nonneg real_sqrt_abs real_sqrt_le_iff)
qed

end
