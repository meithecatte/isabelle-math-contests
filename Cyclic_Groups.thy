theory Cyclic_Groups
  imports
    "HOL-Algebra.Algebra"
begin


text \<open>Firstly, we mirror the proof of @{text "generate_pow_card"} from @{text "HOL-Algebra"},
but with some minor modifications that eliminate one of the assumptions\<close>
context group begin
lemma ord_elems_inf_carrier:
  assumes "a \<in> carrier G" "ord a \<noteq> 0"
  shows "{a[^]x | x. x \<in> (UNIV :: nat set)} = {a[^]x | x. x \<in> {0 .. ord a - 1}}" (is "?L = ?R")
proof
  show "?R \<subseteq> ?L" by blast
  { fix y assume "y \<in> ?L"
    then obtain x::nat where x: "y = a[^]x" by auto
    define r q where "r = x mod ord a" and "q = x div ord a"
    then have "x = q * ord a + r"
      by (simp add: div_mult_mod_eq)
    hence "y = (a[^]ord a)[^]q \<otimes> a[^]r"
      using x assms by (metis mult.commute nat_pow_mult nat_pow_pow)
    hence "y = a[^]r" using assms by simp
    have "r < ord a" using assms by (simp add: r_def)
    hence "r \<in> {0 .. ord a - 1}" by (force simp: r_def)
    hence "y \<in> {a[^]x | x. x \<in> {0 .. ord a - 1}}" using \<open>y=a[^]r\<close> by blast
  }
  thus "?L \<subseteq> ?R" by auto
qed

lemma generate_pow_nat:
  assumes a: "a \<in> carrier G" and "ord a \<noteq> 0"
  shows "generate G { a } = { a [^] k | k. k \<in> (UNIV :: nat set) }"
proof
  show "{ a [^] k | k. k \<in> (UNIV :: nat set) } \<subseteq> generate G { a }"
  proof
    fix b assume "b \<in> { a [^] k | k. k \<in> (UNIV :: nat set) }"
    then obtain k :: nat where "b = a [^] k" by blast
    hence "b = a [^] (int k)"
      by (simp add: int_pow_int)
    thus "b \<in> generate G { a }"
      unfolding generate_pow[OF a] by blast
  qed
next
  show "generate G { a } \<subseteq> { a [^] k | k. k \<in> (UNIV :: nat set) }"
  proof
    fix b assume "b \<in> generate G { a }"
    then obtain k :: int where k: "b = a [^] k"
      unfolding generate_pow[OF a] by blast
    show "b \<in> { a [^] k | k. k \<in> (UNIV :: nat set) }"
    proof (cases "k < 0")
      assume "\<not> k < 0"
      hence "b = a [^] (nat k)"
        by (simp add: k)
      thus ?thesis by blast
    next
      assume "k < 0"
      hence b: "b = inv (a [^] (nat (- k)))"
        using k a by (auto simp: int_pow_neg)
      obtain m where m: "ord a * m \<ge> nat (- k)"
        by (metis assms(2) dvd_imp_le dvd_triv_right le_zero_eq mult_eq_0_iff not_gr_zero)
      hence "a [^] (ord a * m) = \<one>"
        by (metis a nat_pow_one nat_pow_pow pow_ord_eq_1)
      then obtain k' :: nat where "(a [^] (nat (- k))) \<otimes> (a [^] k') = \<one>"
        using m a nat_le_iff_add nat_pow_mult by auto
      hence "b = a [^] k'"
        using b a by (metis inv_unique' nat_pow_closed nat_pow_comm)
      thus "b \<in> { a [^] k | k. k \<in> (UNIV :: nat set) }" by blast
    qed
  qed
qed

lemma generate_pow_card:
  assumes a: "a \<in> carrier G"
  shows "ord a = card (generate G { a })"
proof (cases "ord a = 0")
  case True
  then have "infinite (carrier (subgroup_generated G {a}))"
    using infinite_cyclic_subgroup_order[OF a] by auto
  then have "infinite (generate G {a})"
    unfolding subgroup_generated_def
    using a by simp
  then show ?thesis
    using `ord a = 0` by auto
next
  case False
  note finite_subgroup = this
  then have "generate G { a } = (([^]) a) ` {0..ord a - 1}"
    using generate_pow_nat ord_elems_inf_carrier a by auto
  hence "card (generate G {a}) = card {0..ord a - 1}"
    using ord_inj[OF a] card_image by metis
  also have "... = ord a" using finite_subgroup by auto
  finally show ?thesis.. 
qed

end

lemma cyclic_integer_mod_group:
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

lemma (in group) cyclic_order_is_ord:
  assumes "g \<in> carrier G"
  shows "ord g = order (subgroup_generated G {g})"
  unfolding order_def subgroup_generated_def
  using assms generate_pow_card by simp

lemma (in group) pow_mod_ord [simp]:
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

lemma integer_mod_group_iff_mod_self:
  "x \<in> carrier (integer_mod_group n) \<longleftrightarrow> x mod n = x"
  by (auto simp add: carrier_integer_mod_group zmod_trival_iff)

lemma integer_mod_group_eq_if_cong:
  assumes "n dvd a - b"
  assumes "a \<in> carrier (integer_mod_group n)" "b \<in> carrier (integer_mod_group n)"
  shows "a = b"
  using assms
  by (metis mod_eq_dvd_iff integer_mod_group_iff_mod_self)

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

lemma (in group) has_not_identity:
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

end