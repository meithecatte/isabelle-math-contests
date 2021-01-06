chapter "Dihedral Groups"

theory Dihedral_Groups
  imports
    "HOL-Algebra.Algebra"
begin

text \<open>Ideally, we would define a regular polygon and prove theorems about isometries
for which the regular polygons are a fixed point. This would require more geometry
than than the tiny amount available in Isabelle, so we instead use a more abstract definition.\<close>

context
  fixes n :: nat
begin

text \<open>@{term "(False, k)"} corresponds to $r^k$; @{term "(True, k)"} is $sr^k$.}\<close>
definition dihedral_carrier :: "(bool \<times> int) set" where
  "dihedral_carrier = (if n = 0 then UNIV else UNIV \<times> {0..<n})"

fun dihedral_op where
"dihedral_op (k, a) (False, b) = (k, (a + b) mod int n)" |
"dihedral_op (k, a) (True, b) = (\<not>k, (b - a) mod int n)"

definition dihedral_group :: "(bool \<times> int) monoid" where
  "dihedral_group = \<lparr>carrier = dihedral_carrier,
                     monoid.mult = dihedral_op,
                     one = (False, 0)\<rparr>"
end

lemma dihedral_op_closed [simp]: "dihedral_op n a b \<in> dihedral_carrier n"
  unfolding dihedral_carrier_def
  apply (cases n)
  apply simp
  apply (cases b, cases a)
  subgoal for n' sb by (cases sb) auto
  done

lemma dihedral_op_assoc [simp]:
  "dihedral_op n (dihedral_op n a b) c = dihedral_op n a (dihedral_op n b c)"
  apply (cases a, cases b, cases c)
  subgoal for sa _ sb _ sc _
    apply (cases sa; cases sb; cases sc)
    by (auto simp add: ac_simps diff_diff_add add_diff_eq diff_diff_eq2 mod_add_right_eq mod_diff_right_eq mod_diff_left_eq)
  done

lemma dihedral_op_id [simp]:
  "x \<in> dihedral_carrier n \<Longrightarrow> dihedral_op n (False, 0) x = x"
  apply (cases x)
  subgoal for sx
    apply (cases sx; cases n)
    unfolding dihedral_carrier_def by auto
  done

lemma dihedral_op_inv:
  assumes "x \<in> dihedral_carrier n"
  shows "\<exists>x' \<in> dihedral_carrier n. dihedral_op n x' x = (False, 0)"
proof
  let ?x' = "if fst x then x else (False, (-snd x) mod n)"
  show "dihedral_op n ?x' x = (False, 0)"
    apply (cases x)
    by (auto simp add: mod_add_left_eq)
  show "?x' \<in> dihedral_carrier n"
    using assms unfolding dihedral_carrier_def
    by auto
qed

lemma group_dihedral_group: "group (dihedral_group n)"
  unfolding dihedral_group_def
  apply (rule groupI)
      apply auto
   apply (simp add: dihedral_carrier_def)
  by (intro dihedral_op_inv)

lemma dihedral_carrier [simp]: "carrier (dihedral_group n) = dihedral_carrier n"
  unfolding dihedral_group_def by simp

lemma dihedral_order: "order (dihedral_group n) = 2*n"
  by (simp add: order_def dihedral_carrier_def card_cartesian_product flip: UNIV_Times_UNIV)

(* TODO: prove the (False, _) case by monomorphism from cyclic group
lemma dihedral_ord:
  assumes "x \<in> carrier (dihedral_group n)"
  shows "group.ord (dihedral_group n) x = (if fst x then 2 else n "
proof -
  let ?G = "dihedral_group n"
  have "(True, k) [^]\<^bsub>?G\<^esub> 2 = \<one>\<^bsub>?G\<^esub>"
    apply simp
*)
end