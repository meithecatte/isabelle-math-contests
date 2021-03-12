theory Problem_5
  imports
    Main
    "HOL-Library.Multiset"
    "HOL-Number_Theory.Number_Theory"
    "Common.Future_Library"
begin

text \<open>The Bank of Bath issues coins with an \<open>H\<close> on one side and a \<open>T\<close> on the other.
Harry has \<open>n\<close> of these coins arranged in a line from left to right.
He repeatedly performs the following operation:
if there are exactly \<open>k > 0\<close> coins showing \<open>H\<close>,
then he turns over the \<open>k\<close>th coin from the left;
otherwise, all coins show \<open>T\<close> and he stops.

a) Show that, for each initial configuration, Harry stops
after a finite number of operations.

b) Find the average number of steps Harry will take over all \<open>2\<^sup>n\<close> possible initial configurations.\<close>
(* TAGS: combinatorics *)

section "Definitions"

datatype coin = H | T

fun flip :: "coin \<Rightarrow> coin" where
  "flip H = T" |
  "flip T = H"

definition headcount :: "coin list \<Rightarrow> nat" where
  "headcount cs = count (mset cs) H"

definition step :: "coin list \<Rightarrow> coin list" where
  "step x = (case headcount x of
    0 \<Rightarrow> x |
    Suc n \<Rightarrow> x[n := flip (x ! n)])"

section "A closed formula for the number of steps"

definition heads :: "coin list \<Rightarrow> nat set" where
  "heads cs = {n. n < length cs \<and> cs ! n = H}"

lemma finite_heads[simp]: "finite (heads cs)"
  unfolding heads_def by simp

lemma headcount_heads: "headcount cs = card (heads cs)"
  unfolding headcount_def heads_def
  by (smt Collect_cong count_mset length_filter_conv_card)

lemma headcount_le: "headcount cs \<le> length cs"
  by (metis count_mset headcount_def length_filter_le)

definition steps :: "coin list \<Rightarrow> nat" where
  "steps cs = headcount cs + 2*\<Sum> (heads cs) - 2*\<Sum> {0..<headcount cs}"

section "Lifting @{term steps} from @{typ nat} to @{typ int}"

lemma steps_sub:
  "2*\<Sum> {0..<headcount cs} \<le> 2*\<Sum> (heads cs)"
  using sum_min unfolding headcount_heads by simp

lemma steps_alt:
  "int (steps cs) = int (headcount cs) + int (2*\<Sum> (heads cs)) - int (2*\<Sum> {0..<headcount cs})"
proof -
  have "int (headcount cs) + int (2 * \<Sum> (heads cs))
        \<ge> int (2 * \<Sum> {0..<headcount cs})"
    using steps_sub[of cs] by linarith
  then show ?thesis
    unfolding steps_def int_ops(6) int_plus
    by auto
qed

section "@{term steps} describes the behavior of @{term step}"

lemma step_stopped:
  "H \<notin> set x \<Longrightarrow> steps x = 0"
proof -
  assume "H \<notin> set x"
  then have "headcount x = 0" unfolding headcount_def
    by simp
  with finite_heads and headcount_heads have "heads x = {}" by simp
  show "steps x = 0"
    using `heads x = {}` and `headcount x = 0` by (simp add: steps_def)
qed

lemma step_running:
  assumes "H \<in> set x"
  shows "steps x = Suc (steps (step x))"
proof -
  from assms have "headcount x \<noteq> 0"
    unfolding headcount_def by simp
  then obtain n where headcount: "headcount x = Suc n"
    using not0_implies_Suc by blast
  with assms have x': "step x = x[n := flip (x ! n)]" unfolding step_def by simp

  from headcount and headcount_le have n_lt: "n < length x"
    by (metis Suc_le_lessD)

  show ?thesis
  proof (cases "x ! n")
    case H
    then have "heads (step x) = heads x - {n}"
      using x' n_lt unfolding heads_def
      by (auto simp add: nth_list_update)
    moreover have "n \<in> heads x"
      using `x ! n = H` n_lt unfolding heads_def
      by auto
    ultimately have "\<Sum> (heads (step x)) = \<Sum> (heads x) - n"
      by (simp add: sum_diff1_nat)
    moreover have "n \<le> \<Sum> (heads x)"
      using `n \<in> heads x` member_le_sum by fastforce
    ultimately have *: "\<Sum> (heads x) = \<Sum> (heads (step x)) + n"
      by simp
    from `n \<in> heads x`
    have "headcount x = Suc (headcount (step x))"
      unfolding headcount_heads `heads (step x) = heads x - {n}`
      by (intro card.remove) simp
    with headcount have "headcount (step x) = n" by simp
    with * have "int (steps x) = int (steps (step x)) + 1"
      unfolding steps_alt
      by (simp add: headcount)
    thus ?thesis by simp
  next
    case T
    then have "heads (step x) = insert n (heads x)"
      using x' n_lt unfolding heads_def
      by (auto simp add: nth_list_update)
    moreover have "n \<notin> heads x"
      using `x ! n = T` n_lt unfolding heads_def
      by auto
    ultimately have "\<Sum> (heads (step x)) = \<Sum> (heads x) + n"
      by simp
    moreover have "headcount (step x) = Suc (headcount x)"
      unfolding headcount_heads `heads (step x) = insert n (heads x)`
      using `n \<notin> heads x`
      by (intro card_insert_disjoint; auto)
    ultimately have "int (steps x) = int (steps (step x)) + 1"
      unfolding steps_alt
      by (simp add: headcount)
    thus ?thesis by simp
  qed
qed

corollary steps_stopped_iff:
  "H \<notin> set x \<longleftrightarrow> steps x = 0"
  using step_stopped step_running by auto

text \<open>The above two lemmas can be combined using the saturating property of @{typ nat} subtraction.\<close>

lemma stopped_idempotent:
  "H \<notin> set x \<Longrightarrow> step x = x"
proof -
  assume "H \<notin> set x"
  then have "headcount x = 0" unfolding headcount_def by simp
  thus "step x = x" unfolding step_def by simp
qed

lemma steps_decreases:
  "steps (step x) = steps x - 1"
  apply (cases "H \<in> set x")
  using step_running step_stopped stopped_idempotent by auto

lemma step_funpow[simp]:
  "steps ((step^^k) x) = steps x - k"
  apply (induction k)
  by (auto simp add: steps_decreases)

corollary terminates:
  "H \<notin> set ((step^^steps x) x)"
  by (simp add: steps_stopped_iff)

proposition steps_is_least:
  "(LEAST k. H \<notin> set ((step^^k) x)) = steps x"
proof (intro Least_equality)
  show "H \<notin> set ((step^^steps x) x)" by (fact terminates)
  fix y
  assume y_end: "H \<notin> set ((step^^y) x)"
  {
    assume "y < steps x"
    then have "steps ((step^^y) x) \<noteq> 0"
      by simp
    with y_end have False by (simp add: steps_stopped_iff)
  }
  then show "steps x \<le> y"
    by fastforce
qed

section "Average step count"

definition positions :: "nat \<Rightarrow> coin list set" where
  "positions n = {cs. length cs = n}"

definition step_avg :: "nat \<Rightarrow> real" where
  "step_avg n = (\<Sum>p \<in> positions n. steps p) / card (positions n)"

lemma coin_finite: "finite (UNIV::coin set)"
  and coin_card: "card (UNIV::coin set) = 2"
proof -
  have "x = H \<or> x = T" for x :: coin
    by (cases x) auto
  hence "(UNIV::coin set) = {H, T}"
    by auto
  moreover have "finite {H, T}"
    by simp
  ultimately show "finite (UNIV::coin set)"
    by simp
  have "card {H, T} = 2"
    by simp
  with `UNIV = {H, T}` show "card (UNIV::coin set) = 2"
    by simp
qed

lemma numpos: "card (positions n) = 2^n"
  unfolding positions_def
  using card_lists_length_eq[OF coin_finite]
  by (auto simp add: coin_card)

corollary finite_positions[intro]: "finite (positions n)"
  using card.infinite numpos by fastforce

lemma real_sum: "real (sum f S) = sum (real \<circ> f) S"
  using int_sum of_int_sum by simp

lemma heads_inj: "length a = length b \<Longrightarrow> heads a = heads b \<Longrightarrow> a = b"
proof -
  assume len: "length a = length b" and heads_eq: "heads a = heads b"
  {
    fix n
    assume "n < length a"
    from heads_eq have *: "n < length a \<and> a ! n = H \<longleftrightarrow> n < length b \<and> b ! n = H"
      unfolding heads_def by auto
    hence "a ! n = H \<longleftrightarrow> b ! n = H"
      using len `n < length a` by simp
    hence "a ! n = b ! n"
      by (metis flip.cases)
  }
  with list_eq_iff_nth_eq len show ?thesis
    by blast
qed

corollary heads_inj_on_positions: "inj_on heads (positions n)"
  using heads_inj by (auto simp add: positions_def intro: inj_onI)

lemma heads_positions_subset:
  "h \<in> heads ` positions n \<longleftrightarrow> h \<subseteq> {0..<n}"
proof
  assume h: "h \<subseteq> {0..<n}"
  let ?L = "map (\<lambda>n. if n \<in> h then H else T) [0..<n]"
  have "?L \<in> positions n"
    unfolding positions_def by simp
  moreover have "heads ?L = h"
    unfolding heads_def
    using h apply auto
    by (meson coin.simps(2))
  ultimately show "h \<in> heads ` positions n" by auto
qed (auto simp add: positions_def heads_def)

lemma card_headcount[simp]: "card {p \<in> positions n. headcount p = k} = n choose k"
  (is "card ?S = _")
proof -
  have "?S = {p \<in> positions n. card (heads p) = k}"
    unfolding headcount_heads..
  also have "card ... = card {h \<in> heads ` positions n. card h = k}"
    (is "card ?A = card ?B")
  proof (intro bij_betw_same_card bij_betw_imageI)
    show "inj_on heads ?A"
      by (metis (mono_tags, lifting) inj_onD inj_onI mem_Collect_eq heads_inj_on_positions) 
  qed auto
  also have "... = card {h. h \<subseteq> {0..<n} \<and> card h = k}"
    using heads_positions_subset by auto
  also have "... = n choose k"
    by (simp add: n_subsets)
  finally show ?thesis.
qed


lemma headcount_image[iff]: "headcount ` positions n \<subseteq> {0..n}"
  unfolding positions_def
  by (auto simp: headcount_le)

lemma part1: "(\<Sum>p \<in> positions n. headcount p) = n * 2^(n-1)"
proof -
  have "(\<Sum>p \<in> positions n. headcount p) = (\<Sum>k\<in>{0..n}. (n choose k) * k)"
    apply (intro sum_count[where f="\<lambda>x. x" and g=headcount, OF finite_positions, simplified])
    by (simp, fact headcount_image)
  also have "... = (\<Sum>k\<le>n. (n choose k) * k)"
    using atMost_atLeast0 by simp
  finally show ?thesis
    by (simp add: choose_linear_sum ac_simps)
qed

lemma part3: "(\<Sum>p \<in> positions n. 2*\<Sum> {0..<headcount p}) = n * (n-1) * 2^(n-2)"
proof -
  have *: "\<Sum> {0..<n} = \<Sum> {0..n-1}" for n::nat
    by (cases n; auto simp: atLeastLessThanSuc_atLeastAtMost)
  have "(\<Sum>p \<in> positions n. 2*\<Sum> {0..<headcount p})
      = (\<Sum>k\<in>{0..n}. of_nat (card {p \<in> positions n. headcount p = k}) * (2 * \<Sum>{0..<k}))"
    apply (intro sum_count)
    by auto
  also have "... = (\<Sum>k\<in>{0..n}. (n choose k) * ((k - 1) * Suc (k - 1)))"
    by (simp add: * gauss_sum_nat)
  also have "... = (\<Sum>k\<in>{0..n}. (n choose k) * (k - 1) * k)"
  proof -
    have "(k - 1) * Suc (k - 1) = (k - 1) * k" for k::nat
      by (cases k; auto)
    thus ?thesis
      by (simp add: ac_simps)
  qed
  also have "... = (\<Sum>k\<in>{2..n}. (n choose k) * (k - 1) * k)"
  proof (cases "n < 2")
    case False
    then have "{0..n} = {0, 1} \<union> {2..n}"
      by auto
    moreover have "(\<Sum>k\<in>{0, 1}. (n choose k) * (k - 1) * k) = 0"
      by auto
    ultimately show ?thesis by simp
  qed auto
  also have "... = (\<Sum>k\<in>{2..n}. ((n-2) choose (k-2)) * n * (n - 1))"
  proof -
    {
      fix k :: nat
      assume "k \<ge> 2"
      then obtain k' where "k = Suc (Suc k')"
        using add_2_eq_Suc le_Suc_ex by blast
      hence "(k - 1) * (k * (n choose k)) = (n - 1) * n * ((n-2) choose (k-2))"
        by (auto simp del: mult_Suc_right mult_Suc simp add: binomial_absorption numeral_eq_Suc)
    }
    thus ?thesis
      by (intro sum.cong; auto simp: ac_simps)
  qed
  also have "... = n * (n - 1) * (\<Sum>k\<in>{2..n}. (n - 2) choose (k - 2))"
    by (simp flip: sum_distrib_right)
  also have "... = n * (n - 1) * (\<Sum>k\<in>{0..n-2}. (n - 2) choose k)"
  proof (cases "n < 2")
    case False
    then obtain n' where n': "n = Suc (Suc n')"
      by (metis less_iff_Suc_add not_less_eq numeral_2_eq_2)
    then have [simp]: "(\<Sum>k\<in>{2..n}. f k) = (\<Sum>k\<in>{0..n-2}. f (k + 2))" for f :: "nat \<Rightarrow> nat"
      using sum.shift_bounds_cl_nat_ivl[where k=2 and m=0 and n=n' and g=f]
      by (simp add: numeral_eq_Suc)
    show ?thesis by simp
  qed auto
  also have "... = n * (n - 1) * 2^(n-2)"
    using atMost_atLeast0 choose_row_sum by simp
  finally show ?thesis.
qed

lemma part2: "(\<Sum>p \<in> positions n. 2*\<Sum> (heads p)) = n * (n-1) * 2^(n-1)"
proof -
  have "(\<Sum>p \<in> positions n. 2*\<Sum> (heads p)) = (\<Sum>h \<in> heads ` positions n. 2*\<Sum>h)"
    using sum.reindex[OF heads_inj_on_positions, symmetric, where n=n and g="\<lambda>h. 2*\<Sum>h"]
    by simp
  also have "... = (\<Sum>h \<in> Pow {0..<n}. 2*\<Sum>h)"
  proof -
    have "heads ` positions n = Pow {0..<n}"
      using heads_positions_subset by auto
    thus ?thesis by simp
  qed
  also have "... = n * (n - 1) * 2^(n - 1)"
  proof (induction n)
    case (Suc n)
    note IH = this
    show ?case
    proof (cases n)
      case 0
      then show ?thesis by simp eval
    next
      case (Suc n')
      have "Pow {0..<Suc n} = Pow {0..<n} \<union> insert n ` Pow {0..<n}"
        by (simp add: Pow_insert atLeast0_lessThan_Suc)
      moreover have "Pow {0..<n} \<inter> insert n ` Pow {0..<n} = {}"
        by auto
      moreover have "inj_on (insert n) (Pow {0..<n})"
        by (force intro: inj_onI)
      moreover have "x\<in>Pow {0..<n} \<Longrightarrow> \<Sum> (insert n x) = n + \<Sum>x" for x
        apply (intro sum.insert)
         apply auto
        using infinite_super by blast
      ultimately show ?thesis
        apply (simp add: sum.union_disjoint sum.reindex sum.distrib Suc.IH card_Pow)
        by (simp add: `n = Suc n'` algebra_simps)
    qed 
  qed simp
  finally show ?thesis.
qed

lemma stepsum:
  "sum steps (positions n)
  = 2^(n-1) * (n\<^sup>2 + n) div 2"
  (is "?L = ?R")
proof -
  have "int (\<Sum>p \<in> positions n. steps p)
  = int (\<Sum>p \<in> positions n. headcount p)
  + int (\<Sum>p \<in> positions n. 2*\<Sum> (heads p))
  - int (\<Sum>p \<in> positions n. 2*\<Sum> {0..<headcount p})"
    unfolding int_sum steps_alt sum_subtractf sum.distrib..
  hence "int ?L = int ?R"
    unfolding part1 part2 part3
    apply (cases n rule: fib.cases)
    by (auto simp add: algebra_simps power2_eq_square)
  thus "?L = ?R" by linarith
qed


theorem avg_steps:
  "step_avg n = real (n\<^sup>2 + n) / 4"
proof -
  have even: "even (n\<^sup>2 + n)" unfolding power2_eq_square by simp
  hence "real (2 ^ (n - 1) * (n\<^sup>2 + n) div 2) / real (2 ^ n)
      = real (2 ^ (n - 1) * ((n\<^sup>2 + n) div 2)) / real (2 ^ n)"
    by fastforce
  also have "... = 2^(n - 1) * real (n\<^sup>2 + n) / 2^Suc n"
    by (simp add: real_of_nat_div[OF even])
  also have "... = real (n\<^sup>2 + n) / 4"
    apply (cases n)
    by auto
  finally show ?thesis
    unfolding step_avg_def numpos stepsum.
qed

end