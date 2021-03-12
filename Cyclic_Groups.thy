chapter \<open>Cyclic groups\<close>

theory Cyclic_Groups
  imports
    "HOL-Algebra.Algebra"
begin

section \<open>Auxiliary lemmas\<close>

text \<open>Firstly, we mirror the proof of @{text "generate_pow_card"} from @{text "HOL-Algebra"},
but with some minor modifications that eliminate one of the assumptions\<close>
context group begin

lemma pow_mod_ord [simp]:
  fixes k::int
  assumes [simp]: "a \<in> carrier G"
  shows "a [^] (k mod ord a) = a [^] k"
proof -
  have "a [^] (k mod ord a) = a [^] (k - k div ord a * ord a)"
    by (simp add: minus_div_mult_eq_mod)
  also have "... = a [^] (k - ord a * (k div ord a))"
    by (simp add: ac_simps)
  also have "... = a [^] k \<otimes> inv (((a [^] int (ord a)) [^] (k div ord a)))"
    by (simp add: int_pow_diff int_pow_pow)
  also have "... = a [^] k"
    by (simp add: int_pow_int)
  finally show ?thesis.
qed

lemma has_not_identity:
  assumes "order G \<noteq> 1"
  shows "\<exists>a. a \<in> carrier G \<and> a \<noteq> \<one>"
proof -
  {
    assume "a = \<one>" if "a \<in> carrier G" for a
    with one_closed have "carrier G = {\<one>}" by auto
    with assms have "False" unfolding order_def by auto
  }
  thus ?thesis by auto
qed

end

lemma iso_preserves_order:
  assumes "group G" and "group H"
    and "G \<cong> H"
  shows "order G = order H"
proof -
  from `G \<cong> H` obtain h where "h \<in> iso G H"
    unfolding is_iso_def by auto
  hence "bij_betw h (carrier G) (carrier H)"
    unfolding iso_def by auto
  thus "order G = order H"
    unfolding order_def
    using bij_betw_same_card by blast
qed

lemma range_mod_int:
  fixes n :: int
  assumes "n > 0"
  shows "range (\<lambda>m. m mod n) = {0..<n}" (is "?A = ?B")
proof (rule Set.set_eqI)
  fix m
  show "m \<in> ?A \<longleftrightarrow> m \<in> ?B"
  proof
    assume "m \<in> ?A"
    with assms show "m \<in> ?B"
      by auto
  next
    assume "m \<in> ?B"
    moreover have "m mod n \<in> ?A"
      by (rule rangeI)
    ultimately show "m \<in> ?A"
      by simp
  qed
qed

section \<open>Properties of the @{term integer_mod_group}\<close>

lemma integer_mod_group_order [simp]:
  "order (integer_mod_group n) = n"
  unfolding order_def carrier_integer_mod_group
  by auto

lemma cyclic_integer_mod_group [simp]:
  "cyclic_group (integer_mod_group n)"
proof -
  let ?G = "integer_mod_group n"
  interpret G: group ?G by auto
  show ?thesis
  proof (cases "n = 0")
    case True
    then show ?thesis unfolding integer_mod_group_def by auto
  next
    case False
    have "range (\<lambda>k::int. x [^]\<^bsub>?G\<^esub> k) = range (\<lambda>k::int. k * x mod n)" for x
      by (simp add: int_pow_integer_mod_group)
    also obtain x where "range (\<lambda>k::int. k * x mod n) = {0..<n} \<and> x \<in> carrier ?G" (is "?range_fine x")
    proof (cases "n = 1")
      case True
      then have "?range_fine 0" by auto
      then show ?thesis using that by blast
    next
      case False
      note n_range = this `n \<noteq> 0`
      have "x \<in> range (\<lambda>x. x mod int n)" if "x \<in> {0..<n}" for x::int
      proof
        show "x = x mod n" using that by auto
      qed auto
      with n_range have "?range_fine 1" by auto
      then show ?thesis using that by blast
    qed
    finally show ?thesis
      by (metis `n \<noteq> 0` carrier_integer_mod_group G.cyclic_group)
  qed
qed

lemma integer_mod_group_iff_mod_self [simp]:
  "x \<in> carrier (integer_mod_group n) \<longleftrightarrow> x mod n = x"
  by (auto simp add: carrier_integer_mod_group zmod_trivial_iff)

lemma integer_mod_group_eq_if_cong:
  assumes "n dvd a - b"
  assumes "a \<in> carrier (integer_mod_group n)" "b \<in> carrier (integer_mod_group n)"
  shows "a = b"
  using assms
  by (metis mod_eq_dvd_iff integer_mod_group_iff_mod_self)

section \<open>Isomorphisms of cyclic groups\<close>

lemma (in group) cyclic_iso_integer_mod_group:
  assumes "cyclic_group G"
  shows "G \<cong> integer_mod_group (order G)"
proof -
  let ?n = "order G"
  let ?H = "integer_mod_group ?n"
  from `cyclic_group G` cyclic_group obtain g where
    g [simp]: "g \<in> carrier G" and
    carrier_range: "carrier G = range (\<lambda>k::int. g [^] k)"
    by auto
  have ord_g [simp]: "?n = ord g"
  proof -
    have "ord g = order (subgroup_generated G {g})"
      using cyclic_order_is_ord[OF g] by auto
    also have "... = card (range (\<lambda>k::int. g [^] k))"
      unfolding order_def
      using carrier_subgroup_generated_by_singleton[OF g] by auto
    also have "... = order G"
      unfolding order_def
      using carrier_range by auto
    finally show "?n = ord g"..
  qed
  define h where
    "h x = g [^] x" for x::int
  have contained: "h x \<in> carrier G" if "x \<in> carrier ?H" for x
    unfolding h_def by auto
  moreover have "h x \<otimes> h y = h ((x + y) mod ?n)" for x y
    unfolding h_def by (simp add: int_pow_mult)
  ultimately have hom: "h \<in> hom ?H G" by (intro homI) auto

  have "inj_on h (carrier ?H)"
  proof (intro inj_onI)
    fix x y
    assume in_H:"x \<in> carrier ?H" "y \<in> carrier ?H"
    assume "h x = h y"
    then have "?n dvd (x - y)" using int_pow_eq[OF g] unfolding h_def by fastforce
    thus "x = y" using integer_mod_group_eq_if_cong in_H by auto
  qed

  moreover have "h ` carrier ?H = carrier G"
  proof
    show "h ` carrier ?H \<subseteq> carrier G"
      using contained by auto
    show "carrier G \<subseteq> h ` carrier ?H"
    proof
      fix x
      assume x: "x \<in> carrier G"
      with carrier_range obtain k where "h k = x"
        unfolding h_def by auto
      then obtain k' where "h k' = x" "k' mod ?n = k'"
        unfolding h_def
        by (metis pow_mod_ord[OF g] ord_g mod_mod_trivial)
      then have "k' \<in> carrier ?H"
        using integer_mod_group_iff_mod_self by auto
      with `h k' = x` show "x \<in> h ` carrier ?H" by auto
    qed
  qed
  ultimately have "bij_betw h (carrier ?H) (carrier G)" by (intro bij_betw_imageI) auto
  with hom have "h \<in> iso ?H G" by (intro isoI) auto
  hence iso: "?H \<cong> G" by (intro is_isoI) auto
  show "G \<cong> ?H"
    apply (rule group.iso_sym)
    using iso by auto
qed

corollary cyclic_iso_order:
  assumes groups: "group G" "group H"
    and "cyclic_group G" and "cyclic_group H"
  shows "G \<cong> H \<longleftrightarrow> order G = order H"
  by (metis assms group.iso_sym iso_trans group.cyclic_iso_integer_mod_group iso_preserves_order)

section "Prime-order group is cyclic"

lemma (in group) cyclic_prime:
  assumes "Factorial_Ring.prime (order G)"
  shows "cyclic_group G"
proof -
  from assms have "order G \<noteq> 1" by auto
  with has_not_identity obtain g where g: "g \<in> carrier G" and "g \<noteq> \<one>" by auto
  hence "ord g \<noteq> 1" using ord_eq_1 by auto
  with assms ord_dvd_group_order have ord_order: "ord g = order G"
    using prime_nat_iff g by blast

  let ?H = "generate G {g}"
  have "card ?H = card (carrier G)" using ord_order unfolding order_def
    by (simp add: generate_pow_card[OF g])
  moreover have "?H \<subseteq> carrier G" using g generate_incl by auto
  moreover have "finite (carrier G)" using assms order_gt_0_iff_finite by auto
  ultimately have "?H = carrier G" by (simp add: card_subset_eq)
  hence "subgroup_generated G {g} = G"
    unfolding subgroup_generated_def using g
    by auto
  thus "cyclic_group G" using cyclic_group_generated by metis
qed

section "Element order in cyclic groups"

lemma integer_group_1_gen [simp]:
  "generate integer_group {1} = UNIV"
proof -
  have "x \<in> generate integer_group {1}" for x
    by (simp add: group.generate_pow)
  thus ?thesis by auto
qed

lemma integer_mod_group_1_gen:
  "generate (integer_mod_group n) {1 mod n} = carrier (integer_mod_group n)"
proof -
  let ?G = "integer_mod_group n"
  consider "n = 0" | "n = 1" | "n > 1" by fastforce
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      unfolding integer_mod_group_def by simp
  next
    case 2
    then show ?thesis
      using group.generate_one[of ?G, OF group_integer_mod_group]
      unfolding integer_mod_group_def
      by force
  next
    case 3
    then show ?thesis
      by (simp add: range_mod_int group.generate_pow full_SetCompr_eq int_pow_integer_mod_group carrier_integer_mod_group)
  qed
qed

lemma ord_1_integer_mod_group:
  "group.ord (integer_mod_group n) (1 mod n) = n"
proof -
  let ?G = "integer_mod_group n"
  have in_carrier: "1 mod n \<in> carrier ?G"
    using zmod_trivial_iff by auto
  hence "group.ord ?G (1 mod n) = card (generate ?G {1 mod n})"
    by (simp add: group.generate_pow_card)
  also have "... = order ?G" 
    unfolding order_def
    by (metis of_nat_1 zmod_int integer_mod_group_1_gen)
  finally show ?thesis
    by simp
qed

proposition ord_integer_mod_group:
  assumes "a \<in> carrier (integer_mod_group n)"
  shows "group.ord (integer_mod_group n) a = (if a = 0 then 1 else n div gcd a n)"
proof -
  let ?G = "integer_mod_group n"
  interpret G: group ?G by auto
  have in_carrier: "1 mod n \<in> carrier ?G"
    using zmod_trivial_iff by auto
  have *: "int (1 mod n) [^]\<^bsub>?G\<^esub> a = a"
    apply (simp add: int_pow_integer_mod_group)
    apply auto
    using assms integer_mod_group_iff_mod_self apply blast
    using assms by force
  show ?thesis
    using G.ord_pow_gen[where x="1 mod n" and k=a, OF in_carrier]
    using assms
    by (simp only: ord_1_integer_mod_group gcd.commute *)
qed

end