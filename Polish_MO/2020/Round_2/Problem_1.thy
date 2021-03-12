theory Problem_1
  imports Main
begin

text \<open>Jacek has \<open>n\<close> cards, labelled with consecutive numbers \<open>1, \<dots>, n\<close>. He places
them in a row on the table, in any order he chooses. He will be taking the cards
off the table in the ordering given by the cards' labels — he will first take card
number 1, then number 2, and so on. Before Jacek begins taking the cards off the table,
Placek will color each card red, blue or yellow. Prove that Placek may color the cards
in such a manner, that while Jacek is taking them off the table, at all times the following
property is maintained: between any two cards of the same color, there is at least
one card of a different color.\<close>
(* TAGS: combinatorics *)
datatype color = Red | Blue | Yellow

definition property :: "color list \<Rightarrow> bool" where
  "property clrs \<longleftrightarrow> (\<forall>a < length clrs. \<forall>b < length clrs.
    a < b \<and> clrs ! a = clrs ! b \<longrightarrow> (\<exists>m \<in> {a..b}. clrs ! m \<noteq> clrs ! a))"

lemma successively_conv_nth: "successively R xs \<longleftrightarrow> (\<forall>i<length xs - 1. R (xs ! i) (xs ! Suc i))"
  by (induction xs rule: induct_list012; force simp: nth_Cons split: nat.splits)

lemma propertyD: "property xs \<Longrightarrow> i < j \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i = xs ! j \<Longrightarrow> \<exists>m \<in> {i..j}. xs ! m \<noteq> xs ! i"
  unfolding property_def by auto

(* proof of lemma contributed by Manuel Eberl *)
lemma property_altdef[simp]: "property xs \<longleftrightarrow> distinct_adj xs"
proof (intro iffI)
  assume p: "property xs"
  show "distinct_adj xs"
    unfolding distinct_adj_def successively_conv_nth
  proof (intro allI impI)
    fix i assume i: "i < length xs - 1"
    show "xs ! i \<noteq> xs ! Suc i"
    proof
      assume *: "xs ! i = xs ! Suc i"
      with p i have "\<exists>m\<in>{i..Suc i}. xs ! m \<noteq> xs ! i"
        by (intro propertyD) auto
      thus False using * by (auto simp: le_Suc_eq)
    qed
  qed
next
  assume "distinct_adj xs"
  show "property xs" unfolding property_def
  proof safe
    fix i j assume ij: "i < j" "j < length xs" "xs ! i = xs ! j"
    from \<open>distinct_adj xs\<close> have "xs ! i \<noteq> xs ! Suc i"
      using ij by (auto simp: successively_conv_nth distinct_adj_def)
    thus "\<exists>m\<in>{i..j}. xs ! m \<noteq> xs ! i"
      using ij by (intro bexI[of _ "Suc i"]) auto
  qed
qed

lemma property_insert:
  assumes "property (l @ r)"
  obtains clr where "property (l @ clr # r)"
proof -
  obtain clr where clr: "clr \<noteq> last l"  "clr \<noteq> hd r"
    by (metis color.distinct(1,3,5))
  let ?list = "l @ [clr] @ r"
  have "distinct_adj l"  "distinct_adj r"
    using assms by auto
  hence "property ?list"
    unfolding property_altdef distinct_adj_append_iff
    using clr by auto
  thus ?thesis using that by simp
qed

definition remove_smallest :: "nat list \<Rightarrow> nat list" where
  "remove_smallest xs = remove1 (Min (set xs)) xs"

lemma remove1_split:
  assumes "a \<in> set xs"
  shows "\<exists>l r. xs = l @ a # r \<and> remove1 a xs = l @ r"
using assms proof (induction xs)
  case (Cons x xs)
  show ?case
  proof cases
    assume "x = a"
    show ?thesis
      apply (rule exI[of _ "[]"])
      using `x = a` by simp
  next
    assume "x \<noteq> a"
    then have "a \<in> set xs"
      using `a \<in> set (x # xs)`
      by simp
    then obtain l r where *: "xs = l @ a # r \<and> remove1 a xs = l @ r"
      using Cons.IH by auto
    show ?thesis
      apply (rule exI[of _ "x # l"])
      apply (rule exI[of _ r])
      using `x \<noteq> a` * by auto
  qed
qed simp

lemma remove_smallest_distinct:
  "distinct xs \<Longrightarrow> distinct (remove_smallest xs)"
  unfolding remove_smallest_def by simp

lemma remove_smallest_subset:
  "set (remove_smallest xs) \<subseteq> set xs"
  unfolding remove_smallest_def by (rule set_remove1_subset)

lemma remove_smallest_length[simp]: "xs \<noteq> [] \<Longrightarrow> length (remove_smallest xs) < length xs"
  by (simp add: remove_smallest_def length_remove1)

lemma remove_smallest_map:
  assumes "map f xs = map g xs"
  shows "map f (remove_smallest xs) = map g (remove_smallest xs)"
proof cases
  assume "xs = []"
  then show ?thesis by (simp add: remove_smallest_def)
next
  assume "xs \<noteq> []"
  then have "Min (set xs) \<in> set xs"
    by auto
  then obtain l r where *: "xs = l @ Min (set xs) # r" and **: "remove_smallest xs = l @ r"
    unfolding remove_smallest_def
    using remove1_split by fast
  from assms have "\<forall>x \<in> set xs. f x = g x" by auto
  hence "(\<forall>x \<in> set l. f x = g x) \<and> (\<forall>x \<in> set r. f x = g x)"
    apply (subst (asm) *)
    by auto
  then show ?thesis
    unfolding **
    by simp
qed

lemma removal_induction:
  assumes "P []"
  assumes "\<And>xs. xs \<noteq> [] \<Longrightarrow> P (remove_smallest xs) \<Longrightarrow> P xs"
  shows "P ys"
  using assms
  apply induction_schema
    apply auto[1]
  by lexicographic_order

theorem problem1:
  fixes order :: "nat list"
  assumes "distinct order"
  shows "\<exists>colors :: nat \<Rightarrow> color. \<forall>n. property (map colors ((remove_smallest^^n) order))"
    (is "\<exists>colors. \<forall>n. ?P colors n order")
using assms proof (induction rule: removal_induction)
  case 1
  have "remove_smallest [] = []"
    by (simp add: remove_smallest_def)
  hence "(remove_smallest^^n) [] = []" for n
    by (induction n) auto
  then show ?case by simp
next
  case (2 order)
  then have distinct: "distinct (remove_smallest order)"
    using remove_smallest_distinct by auto
  note "2.IH"[OF distinct]
  then obtain colors where IH': "?P colors n (remove_smallest order)" for n
    by auto
  let ?m = "Min (set order)"
  obtain xs ys where xsmys: "order = xs @ ?m # ys" and xsys: "remove_smallest order = xs @ ys"
    unfolding remove_smallest_def
    using `order \<noteq> []` by atomize_elim (auto intro: remove1_split)
  let ?l = "map colors xs" and ?r = "map colors ys"
  have "property (?l @ ?r)"
    using xsys IH'[of 0] by simp
  then obtain clr where property_clr: "property (?l @ clr # ?r)"
    by (auto intro: property_insert)
  let ?colors' = "colors(?m := clr)"
  have "?m \<notin> set xs"  "?m \<notin> set ys" 
    by (metis `distinct order` xsmys distinct_append not_distinct_conv_prefix)
       (metis `distinct order` xsmys distinct.simps(2) distinct_append)
  hence property0: "property (map ?colors' order)"
    using property_clr by (subst (2) xsmys) simp
  have "?m \<notin> set (remove_smallest order)"
    unfolding remove_smallest_def
    using `distinct order` by simp
  hence "?m \<notin> set ((remove_smallest^^n) (remove_smallest order))" (is "?m \<notin> set (?xs n)")
    for n
    by (induction n) (use remove_smallest_subset in auto)
  hence map_colors: "map ?colors' (?xs n) = map colors (?xs n)" for n
    by simp
  show ?case
    apply (intro exI[of _ ?colors'] allI)
    subgoal for n
      apply (cases n)
       apply (simp only: funpow_0, rule property0)
      by (auto simp only: funpow_Suc_right o_apply map_fun_upd map_colors IH')
    done
qed

end