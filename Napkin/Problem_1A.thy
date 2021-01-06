theory Problem_1A
  imports "HOL-Algebra.Algebra"
begin

text \<open>It seems that one cannot use $\heartsuit$ as variable. My disappointment
is immeasurable and my day is ruined.\<close>
(* TAGS: group-theory *)
theorem problem1A:
  assumes group: "group G"
  assumes subgrp: "subgroup H G"
  assumes proper: "H \<subset> carrier G"
  assumes iso: "G \<cong> G\<lparr>carrier := H\<rparr>"
  shows "infinite (carrier G)"
proof
  from iso obtain h where bij: "bij_betw h (carrier G) H"
    unfolding is_iso_def iso_def by auto

  assume finite: "finite (carrier G)"
  with proper have "card H < card (carrier G)"
    by (simp add: psubset_card_mono)
  moreover from finite and bij have "card H = card (carrier G)"
    using bij_betw_same_card by fastforce
  ultimately show False by auto
qed
end