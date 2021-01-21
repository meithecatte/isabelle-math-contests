theory Problem_4
  imports Main
begin

text \<open>Let \<open>a\<close> and \<open>b\<close> be positive integers, and let \<open>A\<close> and \<open>B\<close> be finite sets of integers
satisfying

\<^item> \<open>A\<close> and \<open>B\<close> are disjoint.
\<^item> if an integer \<open>i\<close> belongs to either \<open>A\<close> or \<open>B\<close> then either
  \<open>i + a\<close> belongs to \<open>A\<close> or \<open>i - b\<close> belongs to \<open>B\<close>.

Prove that \<open>a\<bar>A\<bar> = b\<bar>B\<bar>\<close>.\<close>
(* TAGS: combinatorics *)

context
  fixes a b :: int
  fixes A B :: "int set"
  assumes pos: "a > 0"  "b > 0"
  assumes finite: "finite A"  "finite B"
  assumes disjoint: "A \<inter> B = {}"
  assumes property: "\<forall>i \<in> A \<union> B. i + a \<in> A \<or> i - b \<in> B"
begin

definition allows (infix "allows" 50) where
  "x allows i \<longleftrightarrow> (x \<in> A \<and> i + a = x) \<or> (x \<in> B \<and> i - b = x)"

lemma allows_right_unique:
  assumes "x allows i" and "x allows j"
  shows "i = j"
proof (rule ccontr)
  assume "i \<noteq> j"
  with assms have "x \<in> A \<and> x \<in> B" unfolding allows_def by auto
  with disjoint show False by auto
qed

definition allowers where
  "allowers i = {x. x allows i}"

lemma has_allowers: "i \<in> A \<union> B \<Longrightarrow> allowers i \<noteq> {}"
  unfolding allowers_def allows_def using property by auto

lemma allowers_in_set: "allowers i \<subseteq> A \<union> B"
  unfolding allowers_def allows_def by auto

lemma allowers_finite: "finite (allowers i)"
  using allowers_in_set apply (rule finite_subset)
  using finite by auto

lemma card_allowers: "i \<in> A \<union> B \<Longrightarrow> card (allowers i) > 0"
  using has_allowers allowers_finite by fastforce

lemma allowers_inj: "inj_on allowers (A \<union> B)"
proof (rule inj_onI)
  fix i j
  assume "i \<in> A \<union> B"  "j \<in> A \<union> B"
  with has_allowers obtain x where "x \<in> allowers i" by auto
  moreover assume "allowers i = allowers j"
  ultimately have "x allows i" and "x allows j"
    by (auto simp: allowers_def)
  thus "i = j" by (rule allows_right_unique)
qed

lemma one_allower:
  assumes "i \<in> A \<union> B"
  shows "card (allowers i) = 1"
proof -
  let ?C = "allowers ` (A \<union> B)"
  have "pairwise disjnt ?C"
  proof
    fix P Q
    assume "P \<in> ?C" and "Q \<in> ?C" and "P \<noteq> Q"
    then obtain i and j
      where *: "allowers i = P"  "allowers j = Q"
        and "i \<in> A \<union> B"  "j \<in> A \<union> B"
      by auto
    with `P \<noteq> Q` have "i \<noteq> j" by auto
    {
      fix x
      assume "x \<in> P" and "x \<in> Q"
      with * have "x allows i" and "x allows j"
        unfolding allowers_def by auto
      with allows_right_unique have "i = j" by auto
      with `i \<noteq> j` have False..
    }
    thus "disjnt P Q" unfolding disjnt_def by auto
  qed
  moreover have "P \<in> ?C \<Longrightarrow> finite P" for P
    using allowers_finite by auto
  ultimately have sum_card: "card (\<Union> ?C) = sum card ?C"
    by (intro card_Union_disjoint; auto)

  have "\<Union> ?C \<subseteq> A \<union> B"
    apply (intro Union_least)
    using allowers_in_set by auto
  hence "card (\<Union> ?C) \<le> card (A \<union> B)"
    using finite by (intro card_mono; auto)
  moreover have "card ?C = card (A \<union> B)"
    using allowers_inj by (intro card_image)
  ultimately have sum_card_le: "sum card ?C \<le> card ?C"
    using sum_card by simp

  show "card (allowers i) = 1" when "\<not> card (allowers i) > 1"
    using card_allowers assms that by force
  show "\<not> card (allowers i) > 1"
  proof
    assume "card (allowers i) > 1"
    moreover have "sum card ?C = card (allowers i) + sum card (?C - {allowers i})"
      apply (intro sum.remove)
      using finite assms by auto
    moreover have "sum card (?C - {allowers i}) \<ge> card (?C - {allowers i})"
      apply (intro sum_bounded_below[where K="(1::nat)", simplified])
      using card_allowers by fastforce
    moreover have "Suc (card (?C - {allowers i})) = card ?C"
      apply (intro card.remove[symmetric])
      using finite assms by auto
    ultimately have "sum card ?C > card ?C"
      by auto
    with sum_card_le show False by simp
  qed
qed

definition allower where
  "allower i = the_elem (allowers i)"

lemma the_elem_in_set:
  assumes "is_singleton S"
  shows "the_elem S \<in> S"
  using assms by (metis is_singleton_the_elem singletonI)

lemma allower_allows:
  assumes "i \<in> A \<union> B"
  shows "allower i \<in> allowers i" and "(allower i) allows i"
proof -
  from assms have "is_singleton (allowers i)"
    using one_allower is_singleton_altdef by blast
  thus "allower i \<in> allowers i"
    unfolding allower_def by (intro the_elem_in_set)
  thus "(allower i) allows i"
    unfolding allowers_def..
qed

lemma allower_in_set:
  assumes "i \<in> A \<union> B"
  shows "allower i \<in> A \<union> B"
  using allowers_in_set allower_allows assms by auto

lemma allower_bij: "bij_betw allower (A \<union> B) (A \<union> B)"
  unfolding bij_betw_def
proof
  show "inj_on allower (A \<union> B)"
    apply (intro inj_onI)
    by (metis allower_allows(2) allows_right_unique)
  hence "card (allower ` (A \<union> B)) = card (A \<union> B)"
    by (intro card_image)
  moreover have "allower ` (A \<union> B) \<subseteq> A \<union> B"
    using allower_in_set by auto
  ultimately show "allower ` (A \<union> B) = A \<union> B"
    using finite by (intro card_subset_eq; auto)
qed

theorem "a * int (card A) = b * int (card B)"
proof -
  let ?A = "{i \<in> A \<union> B. allower i \<in> A}"
  let ?B = "{i \<in> A \<union> B. allower i \<in> B}"
  have *: "?A \<union> ?B = A \<union> B"
    using allower_in_set by auto
  have disjoint': "?A \<inter> ?B = {}"
    using disjoint by auto

  have in_a: "i \<in> ?A \<Longrightarrow> allower i = i + a" for i
    using allower_allows allows_def
    by (metis (mono_tags, lifting) IntI disjoint empty_iff mem_Collect_eq) 
  have in_b: "i \<in> ?B \<Longrightarrow> allower i = i - b" for i
    using allower_allows allows_def
    by (metis (mono_tags, lifting) IntI disjoint empty_iff mem_Collect_eq)

  have "allower ` ?A \<subseteq> A" and "allower ` ?B \<subseteq> B"
    by auto
  moreover have "allower ` (?A \<union> ?B) = A \<union> B"
    using allower_bij unfolding * bij_betw_def by auto
  ultimately have "allower ` ?A = A" and "allower ` ?B = B"
    using disjoint by auto
  moreover have "inj_on allower ?A" and "inj_on allower ?B"
    using bij_betw_imp_inj_on allower_bij inj_on_subset * by blast+
  ultimately have cards: "card ?A = card A"   "card ?B = card B"
    using card_image by fastforce+

  have "\<Sum>(A \<union> B) = sum allower (A \<union> B)"
    using sum.reindex_bij_betw[OF allower_bij, of "\<lambda>x. x"]..
  also have "... = sum allower (?A \<union> ?B)"
    using * by simp
  also have "... = sum allower ?A + sum allower ?B"
    using finite disjoint' by (intro sum.union_disjoint; auto)
  also have "... = (\<Sum>i \<in> ?A. i + a) + (\<Sum>i \<in> ?B. i - b)"
    using in_a in_b sum.cong
    by (metis (no_types, lifting))
  also have "... = (\<Sum>?A + a * int (card ?A)) + (\<Sum>?B - b * int (card ?B))"
    by (simp add: sum.distrib sum_subtractf)
  also have "... = (\<Sum>?A + \<Sum>?B) + a * int (card A) - b * int (card B)"
    unfolding cards
    by (simp add: ac_simps)
  also have "... = \<Sum>(?A \<union> ?B) + a * int (card A) - b * int (card B)"
  proof -
    have "\<Sum>(?A \<union> ?B) = \<Sum>?A + \<Sum>?B"
      using finite disjoint' by (intro sum.union_disjoint; auto)
    thus ?thesis by simp
  qed
  also have "... = \<Sum>(A \<union> B) + a * int (card A) - b * int (card B)"
    unfolding *..
  finally show "a * int (card A) = b * int (card B)"
    by simp
qed

end
end