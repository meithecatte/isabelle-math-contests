theory Problem_1
  imports Complex_Main
begin

text \<open>Consider a set \<open>S\<close> of \<open>n \<ge> 3\<close> positive real numbers.
Show that at most \<open>n - 2\<close> distinct integer powers of \<open>3\<close> can be expressed
as a sum of three distinct elements of \<open>S\<close>.\<close>
(* TAGS: number-theory *)

definition intpow3 where
  "intpow3 x \<longleftrightarrow> (\<exists>k::int. 3 powr k = x)"

lemma card3_distinct[elim]:
  "card {a, b, c} = 3 \<Longrightarrow> a \<noteq> b \<and> b \<noteq> c \<and> c \<noteq> a"
  by (metis One_nat_def add_Suc_right add_cancel_left_right card.empty card.insert card_2_iff equalityI finite.intros(1) insert_subset nat.simps(3) numeral_eq_Suc one_add_one order_refl pred_numeral_simps(3))+

definition threepows where
  "threepows S = {a + b + c | a b c. {a, b, c} \<subseteq> S \<and> card {a, b, c} = 3 \<and> intpow3 (a + b + c)}"

lemma threepows_mono:
  "A \<subseteq> B \<Longrightarrow> threepows A \<subseteq> threepows B"
  by (auto simp: threepows_def)

lemma threepows_intpow3:
  "x \<in> threepows S \<Longrightarrow> intpow3 x"
  by (auto simp: threepows_def)

lemma threepowsI[intro]:
  assumes "{a, b, c} \<subseteq> S" and "card {a, b, c} = 3" and "intpow3 (a + b + c)"
  shows "a + b + c \<in> threepows S"
  using assms by (auto simp: threepows_def)

lemma threepowsE[elim]:
  assumes "x \<in> threepows S"
  assumes "\<And>a b c. x = a + b + c \<Longrightarrow> {a, b, c} \<subseteq> S \<Longrightarrow> card {a, b, c} = 3 \<Longrightarrow> intpow3 (a + b + c) \<Longrightarrow> P x"
  shows "P x"
  using assms by (auto simp: threepows_def)

lemma threepows_trivial:
  assumes "card S < 3" and "finite S"
  shows "threepows S = {}"
proof (rule ccontr)
  assume "threepows S \<noteq> {}"
  then obtain x where "x \<in> threepows S" by auto
  thus False
  proof (rule threepowsE)
    fix a b c
    assume "{a, b, c} \<subseteq> S" "card {a, b, c} = 3"
    have "card {a, b, c} \<le> card S"
      using `finite S` `{a, b, c} \<subseteq> S` by (intro card_mono)
    thus False
      using `card {a, b, c} = 3` `card S < 3` by simp
  qed
qed

lemma threepows_largest:
  fixes k::int
  assumes "3 powr k \<in> threepows S"
  obtains a where "a \<in> S" and "a \<ge> 3 powr (k - 1)"
proof -
  {
    assume "\<nexists>a. a \<in> S \<and> a \<ge> 3 powr (k - 1)"
    then have *: "a \<in> S \<Longrightarrow> a < 3 powr (k - 1)" for a by auto

    have "x \<in> threepows S \<Longrightarrow> x < 3 * 3 powr (k - 1)" for x
    proof (erule threepowsE)
      fix a b c
      assume "{a, b, c} \<subseteq> S" and "x = a + b + c"
      with * have "a < 3 powr (k - 1)" and "b < 3 powr (k - 1)" and "c < 3 powr (k - 1)"
        by auto
      thus "x < 3 * 3 powr (k - 1)"
        unfolding `x = a + b + c` by simp
    qed

    with assms have "3 powr k < 3 * 3 powr (k - 1)"
      by simp
    hence False by (simp add: powr_mult_base)
  }
  thus thesis using that by blast
qed

theorem problem1:
  fixes S :: "real set"
  assumes "card S \<ge> 3"
  assumes "\<And>x. x \<in> S \<Longrightarrow> x > 0"
  shows "card (threepows S) \<le> card S - 2"
  using assms
proof (induction "card S" arbitrary: S rule: less_induct)
  case less
  then have "finite S"
    using card_infinite by fastforce 
  show ?case
  proof (cases "card (threepows S) = 0")
    case False
    then have "finite (threepows S)" and "threepows S \<noteq> {}"
      by (auto intro: card_ge_0_finite)
    then have "Max (threepows S) \<in> threepows S"
      by (intro Max_in)
    with threepows_intpow3 intpow3_def obtain k::int where k: "3 powr k = Max (threepows S)"
      by blast
    let ?discard = "{x \<in> S. x \<ge> 3 powr (k - 1)}"
    have "threepows S - {Max (threepows S)} = threepows (S - ?discard)"
    proof -
      have "Max (threepows S) \<notin> threepows (S - ?discard)"
      proof
        assume "Max (threepows S) \<in> threepows (S - ?discard)"
        then obtain a where "a \<in> S - ?discard" and "a \<ge> 3 powr (k - 1)"
          unfolding k[symmetric] by (rule threepows_largest)
        thus False by simp
      qed
      moreover have "threepows (S - ?discard) \<subseteq> threepows S"
        by (intro threepows_mono; auto)
      moreover have "x = Max (threepows S)"
        if "x \<in> threepows S" and not_in_discard: "x \<notin> threepows (S - ?discard)" for x
        using `x \<in> threepows S`
      proof (rule threepowsE)
        fix a b c
        assume "x = a + b + c"  "{a, b, c} \<subseteq> S"  "card {a, b, c} = 3"  "intpow3 (a + b + c)"
        have "{a, b, c} \<inter> ?discard \<noteq> {}"
        proof
          assume "{a, b, c} \<inter> ?discard = {}"
          with `{a, b, c} \<subseteq> S` have "{a, b, c} \<subseteq> S - ?discard" by simp
          hence "a + b + c \<in> threepows (S - ?discard)"
            using `card {a, b, c} = 3` `intpow3 (a + b + c)` by (intro threepowsI)
          with `x = a + b + c` and not_in_discard show False by simp
        qed
        then have "a \<ge> 3 powr (k - 1) \<or> b \<ge> 3 powr (k - 1) \<or> c \<ge> 3 powr (k - 1)"
          by auto
        moreover from less.prems and `{a, b, c} \<subseteq> S` have "a > 0 \<and> b > 0 \<and> c > 0"
          by simp
        ultimately have *: "a + b + c > 3 powr (k - 1)"
          by linarith
        have "a + b + c \<ge> 3 powr k"
        proof (intro leI notI)
          assume **: "a + b + c < 3 powr k"
          moreover from `intpow3 (a + b + c)` obtain k'::int where "a + b + c = 3 powr k'"
            unfolding intpow3_def by metis
          with * and ** have "3 powr (k - 1) < 3 powr k'" and "3 powr k' < 3 powr k"
            by auto
          hence "k - 1 < k'" and "k' < k"
            by auto
          thus False by auto
        qed
        moreover from `x \<in> threepows S` have "x \<le> Max (threepows S)"
          using `finite (threepows S)` by (intro Max.coboundedI; auto)
        ultimately show "x = Max (threepows S)"
          using `x = a + b + c` and k by simp
      qed
      ultimately show ?thesis
        by auto
    qed
    hence card_threepows: "card (threepows S) = Suc (card (threepows (S - ?discard)))"
      by (metis \<open>Max (threepows S) \<in> threepows S\<close> \<open>finite (threepows S)\<close> card_Suc_Diff1)

    have "?discard \<noteq> {}"
    proof -
      from k `Max (threepows S) \<in> threepows S` threepows_largest
      obtain a where "a \<in> S" and "a \<ge> 3 powr (k - 1)"
        by metis
      hence "a \<in> ?discard" by simp
      thus "?discard \<noteq> {}" by auto
    qed
    hence discard_strict: "card (S - ?discard) < card S"
      using `finite S` by (intro psubset_card_mono; auto)
    show ?thesis
    proof (cases "card (S - ?discard) < 3")
      case True
      then have "threepows (S - ?discard) = {}"
        using `finite S` by (intro threepows_trivial; auto)
      hence "card (threepows S) = 1"
        by (simp add: card_threepows)
      with `card S \<ge> 3` show ?thesis by simp
    next
      case False
      hence "card (threepows (S - ?discard)) \<le> card (S - ?discard) - 2"
        using discard_strict `finite S` by (intro less; auto)
      hence "card (threepows S) \<le> Suc (card (S - ?discard) - 2)"
        unfolding card_threepows by simp
      then show ?thesis
        using discard_strict False by simp
    qed
  qed simp
qed
end