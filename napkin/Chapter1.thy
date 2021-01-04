theory Chapter1
  imports "HOL-Algebra.Algebra"
begin

text "It seems that one cannot use \<heartsuit> as variable. My disappointment
is immeasurable and my day is ruined."

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

text \<open>Problem 1B asks for a special case of Lagrange's theorem, thus we
avoid using the general variant.\<close>

theorem (in comm_group) problem1B:
  assumes finite: "finite (carrier G)"
  assumes closed: "g \<in> carrier G"
  shows "g [^] order G = \<one>"
proof -
  let ?f = "\<lambda>x. g \<otimes> x"
  have [simp]: "?f ` carrier G = carrier G"
    by (simp add: closed group.surj_const_mult)
  have "inj_on ?f (carrier G)"
    by (simp add: closed group.inj_on_cmult)
  hence "(\<Otimes>x \<in> carrier G. x) = (\<Otimes>x \<in> carrier G. g \<otimes> x)"
    using finprod_reindex[where h="?f" and A="carrier G" and f="\<lambda>x. x", symmetric]
    by simp
  also have "... = (\<Otimes>x \<in> carrier G. g) \<otimes> (\<Otimes>x \<in> carrier G. x)" 
    using closed by (intro finprod_multf) auto
  finally have "(\<Otimes>x \<in> carrier G. g) = \<one>"
    using closed by (intro r_cancel_one'[THEN iffD1]) auto
  thus ?thesis
    using closed unfolding order_def by (simp add: finprod_const)
qed

end