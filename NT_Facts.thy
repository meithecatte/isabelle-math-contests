chapter "Some facts from Number Theory"

theory NT_Facts
  imports "HOL-Number_Theory.Number_Theory"
begin

section "Quadratic residues of primes"

lemma pp_mod8:
  fixes p :: int
  assumes "prime p" and "p > 2"
  shows "[p*p = 1] (mod 8)"
proof -
  from assms have "odd p"
    using prime_odd_int by blast
  hence "p mod 8 = 1 \<or> p mod 8 = 3 \<or> p mod 8 = 5 \<or> p mod 8 = 7"
    by presburger
  hence "(p mod 8) * (p mod 8) mod 8 = 1"
    by auto
  thus "[p * p = 1] (mod 8)"
    by (simp add: mod_mult_eq cong_def)
qed

lemma pp_mod3:
  fixes p :: int
  assumes "prime p" and "p > 3"
  shows "[p*p = 1] (mod 3)"
proof -
  from assms have "\<not>3 dvd p"
    by (simp add: prime_int_not_dvd)
  hence "p mod 3 = 1 \<or> p mod 3 = 2"
    by presburger
  hence "(p mod 3) * (p mod 3) mod 3 = 1"
    by auto
  thus "[p * p = 1] (mod 3)"
    by (simp add: mod_mult_eq cong_def)
qed

corollary pp_mod24:
  fixes p :: int
  assumes "prime p" "p > 3"
  shows "[p * p = 1] (mod 24)"
  apply (intro coprime_cong_mult[where m=8 and n=3 and a="p*p" and b=1, simplified])
  using assms apply (intro pp_mod8; auto)
  using assms apply (intro pp_mod3; auto)
  by (smt dvd_add_right_iff not_coprimeE)

end