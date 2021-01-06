theory Warmup_Problem_D
  imports
    Complex_Main
    Common.Future_Library
    "HOL-Analysis.Analysis"
begin

subsection "Warmup problem D"
(* TAGS: metric-space geometry *)
text "There is a set of $n$ points on a plane with the property that,
in each triplet of points, there's a pair with distance at most 1.
Prove that the set can be covered with two circles of radius 1."

text "There's nothing special about the case of points on a plane,
the theorem can be proved without additional difficulties for any
metric space:"

theorem warmup4_generic:
  fixes S :: "'a::metric_space set"
  assumes "finite S"
  assumes property: "\<And>T. T \<subseteq> S \<and> card T = 3 \<Longrightarrow> \<exists>p\<in>T. \<exists>q\<in>T. p \<noteq> q \<and> dist p q \<le> 1"
  obtains O\<^sub>1 O\<^sub>2 where "S \<subseteq> cball O\<^sub>1 1 \<union> cball O\<^sub>2 1"
proof
  let ?pairs = "S \<times> S"
  let ?dist = "\<lambda>(a, b). dist a b"
  define widest_pair where "widest_pair = arg_max_on ?dist ?pairs"
  let ?O\<^sub>1 = "(fst widest_pair)"
  let ?O\<^sub>2 = "(snd widest_pair)"
  show "S \<subseteq> cball ?O\<^sub>1 1 \<union> cball ?O\<^sub>2 1"
  proof
    fix x
    assume "x \<in> S"

    from `finite S` and `x \<in> S`
    have "finite ?pairs" and "?pairs \<noteq> {}" by auto
    hence OinS: "widest_pair \<in> ?pairs"
      unfolding widest_pair_def by (simp add: arg_max_if_finite)

    have "\<forall>(P,Q)\<in>?pairs. dist ?O\<^sub>1 ?O\<^sub>2 \<ge> dist P Q" 
      unfolding widest_pair_def
      using `finite ?pairs` and `?pairs \<noteq> {}`
      by (metis (mono_tags, lifting) arg_max_greatest prod.case_eq_if)
    hence greatest: "dist P Q \<le> dist ?O\<^sub>1 ?O\<^sub>2" if "P \<in> S" and "Q \<in> S" for P Q
      using that by blast

    let ?T = "{?O\<^sub>1, ?O\<^sub>2, x}"
    have TinS: "?T \<subseteq> S" using OinS and `x \<in> S` by auto

    have "card ?T = 3" if "?O\<^sub>1 \<noteq> ?O\<^sub>2" and "x \<notin> {?O\<^sub>1, ?O\<^sub>2}" using that by auto
    then consider
      (primary) "card ?T = 3" |
      (limit) "x \<in> {?O\<^sub>1, ?O\<^sub>2}" |
      (degenerate) "?O\<^sub>1 = ?O\<^sub>2" by blast
    thus "x \<in> cball ?O\<^sub>1 1 \<union> cball ?O\<^sub>2 1"
    proof cases
      case primary
      obtain p and q where "p \<noteq> q" and "dist p q \<le> 1" and "p \<in> ?T" and "q \<in> ?T"
        using property [of ?T] and `card ?T = 3` TinS
        by auto
      then have
        "dist ?O\<^sub>1 ?O\<^sub>2 \<le> 1 \<or> dist ?O\<^sub>1 x \<le> 1 \<or> dist ?O\<^sub>2 x \<le> 1"
        by (metis dist_commute insertE singletonD)
      thus "x \<in> cball ?O\<^sub>1 1 \<union> cball ?O\<^sub>2 1"
        using greatest and TinS
        by fastforce
    next
      case limit
      then have "dist x ?O\<^sub>1 = 0 \<or> dist x ?O\<^sub>2 = 0" by auto
      thus ?thesis by auto
    next
      case degenerate
      with greatest and TinS have "dist ?O\<^sub>1 x = 0" by auto
      thus ?thesis by auto
    qed
  qed
qed

text "Let's make sure that the particular case of points on a plane also works out:"

corollary warmup4:
  fixes S :: "(real ^ 2) set"
  assumes "finite S"
  assumes property: "\<And>T. T \<subseteq> S \<and> card T = 3 \<Longrightarrow> \<exists>p\<in>T. \<exists>q\<in>T. p \<noteq> q \<and> dist p q \<le> 1"
  obtains O\<^sub>1 O\<^sub>2 where "S \<subseteq> cball O\<^sub>1 1 \<union> cball O\<^sub>2 1"
  using warmup4_generic and assms by auto

end
