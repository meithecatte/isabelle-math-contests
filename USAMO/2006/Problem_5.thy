theory Problem_5
  imports Main
    "HOL-Number_Theory.Number_Theory"
    "Common.Future_Library"
begin

text \<open>A mathematical frog jumps along the number line.
The frog starts at 1, and jumps according to the following rule:
if the frog is at integer $n$, then it can jump to $n + 1$ or $n + 2^{m_n+1}$,
where $2^{m_n}$ is the largest power of 2 that is a factor of $n$.
Show that if $k \geq 2$, is a positive integer and $i$ is a non-negative integer,
then the minimum number of jumps needed to reach $2^i k$ is greater than
the minimum number of jumps needed to reach $2^i$.\<close>
(* TAGS: number-theory combinatorics nondeterministic-process *)

definition jump :: "nat \<Rightarrow> nat" where
  "jump n = n + 2^(multiplicity 2 n + 1)"

text \<open>@{term "reachable s n"} is true if the frog can reach integer $n$ with $s$ jumps.\<close>
inductive reachable :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  Start[intro]: "reachable 0 1" |
  Incr[intro]: "reachable s n \<Longrightarrow> reachable (Suc s) (Suc n)" |
  Jump[intro]: "reachable s n \<Longrightarrow> reachable (Suc s) (jump n)"

text \<open>The @{emph \<open>height\<close>} of a number is the minimum number of jumps required.\<close>
definition height :: "nat \<Rightarrow> nat" where
  "height n = arg_min id (\<lambda>s. reachable s n)"

subsection \<open>Alternative definition of @{term jump}\<close>

text \<open>@{term "jump 0"} isn't really well-defined. We introduce an alternative definition:\<close>

definition jump' where
  "jump' n = (if n = 0 then 0 else jump n)"

lemma jump': "n \<noteq> 0 \<Longrightarrow> jump n = jump' n"
  unfolding jump_def jump'_def by simp

lemma jump'_0[simp]: "jump' 0 = 0" by (simp add: jump'_def)

inductive reachable' :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  Start[intro]: "reachable' 0 1" |
  Incr[intro]: "reachable' s n \<Longrightarrow> reachable' (Suc s) (Suc n)" |
  Jump[intro]: "reachable' s n \<Longrightarrow> reachable' (Suc s) (jump' n)"

lemma zero_unreachable:
  "\<not>reachable s 0"
proof
  assume "reachable s 0"
  moreover have "jump n > 0" for n unfolding jump_def by simp
  ultimately show False
    apply (cases rule: reachable.cases)
     apply presburger
    by (metis not_less0)
qed

lemma reachable':
  "reachable s n = reachable' s n"
proof
  assume "reachable s n"
  then show "reachable' s n"
  proof (induction rule: reachable.induct)
    case (Jump s n)
    from `reachable s n` have "n \<noteq> 0"
      by (metis zero_unreachable)
    with Jump show ?case by (auto simp add: jump')
  qed (intro reachable'.intros)+
next
  assume "reachable' s n"
  then show "reachable s n"
  proof (induction rule: reachable'.induct)
    case (Jump s n)
    from `reachable s n` have "n \<noteq> 0"
      by (metis zero_unreachable)
    with Jump show ?case by (auto simp flip: jump')
  qed (intro reachable.intros)+
qed

lemma zero_unreachable': "\<not> reachable' s 0"
  using zero_unreachable by (simp add: reachable')

definition height' :: "nat \<Rightarrow> nat" where
  "height' n = arg_min id (\<lambda>s. reachable' s n)"

lemma height'[simp]:
  "height n = height' n"
  unfolding height_def height'_def by (simp add: reachable')

subsection \<open>Properties of @{term jump'}\<close>

lemma jump_even[simp]: "jump' (2*n) = 2 * jump' n"
  by (auto simp add: jump'_def jump_def multiplicity_times_same)

lemma jump_odd[simp]: "jump' (Suc (2*n)) = Suc (Suc (Suc (2*n)))"
  unfolding jump'_def jump_def
  by (auto intro: not_dvd_imp_multiplicity_0)

lemma jump_gt0[simp]: "n > 0 \<Longrightarrow> jump' n > 0"
  unfolding jump'_def jump_def by auto

subsection \<open>Representing paths\<close>

lemma reachable_height:
  "n \<noteq> 0 \<Longrightarrow> reachable' (height' n) n"
  \<comment> \<open>This is not a tautology, we need to prove that the number is reachable at all.\<close>
  unfolding height'_def
proof (intro arg_min_natI)
  assume "n \<noteq> 0"
  then show "reachable' (n - 1) n"
  proof (induction n)
    case (Suc n)
    then show ?case
      using Start Incr by (cases n) auto
  qed auto
qed

text \<open>Based on this, we define a notion of a path — a specific set of moves
with a desired result.\<close>

datatype move = Incr | Jump
type_synonym path = "move list"

fun make_move :: "move \<Rightarrow> nat \<Rightarrow> nat" where
"make_move Incr n = Suc n" |
"make_move Jump n = jump' n"

fun make_moves :: "path \<Rightarrow> nat \<Rightarrow> nat" where
"make_moves moves n = fold make_move moves n"

lemma path_exists:
  assumes "reachable' s n"
  shows "\<exists>path. make_moves path 1 = n \<and> length path = s"
  using assms
proof induction
  case (Incr s n)
  then obtain path where "make_moves path 1 = n" and "length path = s"
    by auto
  hence "make_moves (path @ [Incr]) 1 = Suc n" and "length (path @ [Incr]) = Suc s"
    by auto
  then show ?case by blast
next
  case (Jump s n)
  then obtain path where "make_moves path 1 = n" and "length path = s"
    by auto
  moreover have "n \<noteq> 0" using Jump.hyps zero_unreachable' by meson
  ultimately have "make_moves (path @ [Jump]) 1 = jump' n" and "length (path @ [Jump]) = Suc s"
    by auto
  then show ?case by blast
qed simp

lemma path_implies_reachable:
  "reachable' (length path) (make_moves path 1)"
proof (induction path rule: rev_induct)
  case Nil
  then show ?case using Start by auto
next
  case (snoc move path)
  then show ?case
    by (cases move) auto
qed

lemma heightI[intro]:
  assumes "make_moves p 1 = x"
  shows "height' x \<le> length p"
proof -
  from assms have "reachable' (length p) x"
    using path_implies_reachable by auto
  thus "height' x \<le> length p"
    unfolding height'_def using arg_min_nat_le[where m=id] by auto
qed

lemma heightD:
  assumes "x \<noteq> 0"
  obtains p where "make_moves p 1 = x" and "length p = height' x"
proof -
  from `x \<noteq> 0` have "reachable' (height' x) x"
    using reachable_height by simp
  with that show thesis using path_exists by auto
qed

subsection \<open>The case for even $k$\<close>

text \<open>From a path leading to $k$, we can derive a path to $k/2$ — for each step,
look at the change to the current integer without the lowest bit. As it turns out,
each of those can be mimicked in one move.\<close>

fun halfpath :: "nat \<Rightarrow> path \<Rightarrow> path" where
"halfpath n [] = []" |
"halfpath n (Incr # p) =
  (if even n
   then halfpath (Suc n) p
   else Incr # halfpath (Suc n) p)" |
"halfpath n (Jump # p) =
  (if even n
   then Jump # halfpath (jump' n) p
   else Incr # halfpath (jump' n) p)"

lemma halfpath:
  assumes "n \<noteq> 0"  "b < 2"
    and "make_moves p (2*n+b) = 2*v"
  shows "make_moves (halfpath (2*n+b) p) n = v"
  using assms
proof (induction p arbitrary: n b)
  case Nil
  then show ?case by simp
next
  case (Cons move p)
  then consider "b = 0" | "b = 1" by fastforce
  thus ?case
  proof cases
    case 1
    then show ?thesis
    proof (cases move)
      case Incr
      from Cons.IH[of n 1] `n \<noteq> 0` Cons show ?thesis
        unfolding Incr 1 by simp
    next
      case Jump
      from Cons.IH[of "jump' n" 0] `n \<noteq> 0` Cons.prems show ?thesis
        unfolding Jump 1 by simp
    qed
  next
    case 2
    then show ?thesis
    proof (cases move)
      case Incr
      from Cons.IH[of "Suc n" 0] `n \<noteq> 0` Cons show ?thesis
        unfolding Incr 2 by simp
    next
      case Jump
      from Cons.IH[of "Suc n" 1] `n \<noteq> 0` Cons show ?thesis
        unfolding Jump 2 by simp
    qed
  qed
qed

lemma halfpath_shorter:
  "length (halfpath n p) \<le> length p"
  apply (induction p arbitrary: n)
   apply simp
  subgoal for move
    apply (cases move)
    by (auto simp add: le_SucI)
  done

lemma halfpath_hd:
  "p \<noteq> [] \<Longrightarrow> hd (halfpath 1 p) = Incr"
  apply (cases p)
   apply simp
  subgoal for move
    apply (cases move)
    by auto
  done

corollary even_reduce:
  assumes "x \<noteq> 0"
  shows "height' x < height' (2*x)"
proof -
  from assms have "2*x \<noteq> 0" by simp
  then obtain path where path: "make_moves path 1 = 2*x"   "length path = height' (2*x)"
    using heightD by blast
  then have "path \<noteq> []" by auto
  then obtain m p where m_p: "path = m # p"
    using list.exhaust by blast 
  let ?path' = "halfpath (make_move m 1) p"
  obtain b where *: "make_move m 1 = 2 + b"   "b < 2"
    by (cases m; auto simp add: jump'_def jump_def)
  hence "make_moves p (2 + b) = 2*x"
    using path m_p by auto
  hence "make_moves ?path' 1 = x"
    using halfpath[where n=1] and * by auto
  hence "height' x \<le> length ?path'" by auto
  also have "... \<le> length p"
    by (fact halfpath_shorter)
  also have "... < length path"
    using m_p by auto
  also have "... = height' (2*x)"
    by (fact path(2))
  finally show "height' x < height' (2*x)".
qed

corollary twopow_reduce:
  assumes "x \<noteq> 0"
  shows "height' x < height' (2^(Suc i) * x)"
proof (induction i)
  case (Suc i)
  have "height' x < height' (2^Suc i * x)" by fact
  also have "... < height' (2 * (2^Suc i * x))" using assms by (intro even_reduce) auto
  finally show ?case by (simp add: ac_simps)
qed (simp add: even_reduce assms)

subsection \<open>The case for odd $k$\<close>

text \<open>The strategy here is similar, but we disregard some high-order bits instead.\<close>

lemma jump_multiplicity:
  "multiplicity 2 (jump' x) = multiplicity 2 x"
  unfolding jump'_def jump_def
  by (auto intro: multiplicity_sum_lt simp del: power_Suc)

lemma jump_mod:
  "[jump' (x mod 2^n) = jump' x] (mod 2^n)"
proof (cases "x mod 2^n = x")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "x mod 2^n = 0")
    case True
    then have "2^n dvd x" by auto
    moreover have "x \<noteq> 0" using `x mod 2^n \<noteq> x` `x mod 2^n = 0` by simp
    ultimately have "multiplicity 2 x \<ge> n"
      by (auto intro: multiplicity_geI)
    with jump_multiplicity have "multiplicity 2 (jump' x) \<ge> n" by auto
    hence "2^n dvd jump' x"
      by (simp add: multiplicity_dvd')

    then show ?thesis
      using `x mod 2^n = 0` by (auto simp add: cong_def)
  next
    case False
    then have "x \<noteq> 0" by (meson mod_0) 

    have "x = x mod 2^n + 2^n * (x div 2^n)"
      by simp
    also have "multiplicity 2 ... = multiplicity 2 (x mod 2^n)"
    proof (intro multiplicity_sum_lt)
      show "x mod 2^n \<noteq> 0" by fact

      have "x div 2^n \<noteq> 0"
      proof
        assume "x div 2^n = 0"
        then have "x mod 2^n = x" by presburger
        with `x mod 2^n \<noteq> x` show False..
      qed
      thus "2^n * (x div 2^n) \<noteq> 0" by simp

      have "multiplicity 2 (x mod 2^n) < n"
        using `x mod 2^n \<noteq> 0`
        by (metis dvd_div_eq_0_iff mod_div_trivial odd_one multiplicity_lessI)

      also have "n \<le> multiplicity 2 (2^n * (x div 2^n))"
        using \<open>2^n * (x div 2^n) \<noteq> 0\<close> dvd_triv_left multiplicity_geI odd_one by blast

      finally show "multiplicity 2 (x mod 2^n) < multiplicity 2 (2^n * (x div 2^n))".
    qed
    finally have "[2^(multiplicity 2 (x mod 2^n) + 1) = 2^(multiplicity 2 x + 1)] (mod 2^n)"
      by simp

    have "[jump (x mod 2^n) = jump x] (mod 2^n)"
      unfolding jump_def by (intro cong_add, simp, fact)
    with `x \<noteq> 0` and `x mod 2^n \<noteq> 0`
    show "[jump' (x mod 2^n) = jump' x] (mod 2^n)"
      by (auto simp add: jump'_def)
  qed
qed

lemma jump_mod_rollover:
  assumes "x < 2^n" and "jump' x \<ge> 2^n"
  shows "[jump' x = 2^(multiplicity 2 x)] (mod 2^n)"
proof -
  have "x \<noteq> 0"
  proof
    assume "x = 0"
    then have "jump' x = 0" by simp
    with assms have "0 < 2^n" and "0 \<ge> 2^n" by auto
    thus False by auto
  qed

  let ?v = "(2::nat)^(multiplicity 2 x)"
  have "jump' x = x + 2*?v" unfolding jump'_def jump_def using `x \<noteq> 0` by simp
  moreover have "?v dvd x" by (fact multiplicity_dvd)
  ultimately have "?v dvd jump' x" by auto

  show ?thesis
  proof (cases "2^n dvd ?v")
    case False
    then have "?v dvd 2^n"
      by (simp add: dvd_power_iff_le)
    then obtain m where m: "2^n = ?v * m" by auto
    moreover from `?v dvd x` obtain x' where x': "x = ?v * x'" by auto
    moreover from `?v dvd jump' x` obtain j' where j': "jump' x = ?v * j'" by auto
    ultimately have "x' < m" and "j' \<ge> m" using assms
      by auto (metis nat_mult_less_cancel_disj)

    moreover have "j' = x' + 2"
    proof -
      from `jump' x = x + 2*?v` have "?v * j' = ?v*x' + ?v*2"
        using x' j' by simp
      also have "... = ?v * (x' + 2)" by simp
      finally show "j' = x' + 2"
        by (simp only: mult_cancel1, simp)
    qed

    ultimately have "j' = m \<or> j' = m + 1" by auto

    moreover have "j' \<noteq> m"
    proof
      assume "j' = m"
      then have "2^n = jump' x"
        using j' m by simp
      hence "multiplicity 2 x = multiplicity (2::nat) (2^n)"
        by (simp add: jump_multiplicity)
      also have "... = n" by simp
      finally have "?v = 2^n" by simp
      with `\<not> 2^n dvd ?v` show False by simp
    qed

    ultimately have "j' = m + 1" by auto
    hence "jump' x = 2^n + ?v" using j' m by auto
    thus ?thesis unfolding cong_def by simp
  next
    case True
    with `?v dvd jump' x` show ?thesis
      unfolding cong_def by auto
  qed
qed

text \<open>Instead of constructing the new path explicitly, we inductively prove
that one exists. To show that the resulting path is strictly shorter, we
maintain the invariant that the path was constructed by removing steps from the original.
Thus, since the number we end up on is different, the path cannot be equal and must be shorter.\<close>

inductive skipping :: "path \<Rightarrow> path \<Rightarrow> bool" where
  SkipEmpty[intro]: "skipping [] p" |
  SkipCons[intro]: "skipping p q \<Longrightarrow> skipping (m # p) (m # q)" |
  SkipSemicons[intro]: "skipping p q \<Longrightarrow> skipping p (m # q)"

lemma length_skipping:
  assumes "skipping p q"
  shows "length p \<le> length q"
  using assms by induction auto

lemma skipping_equal:
  assumes "skipping p q" and "length p = length q"
  shows "p = q"
  using assms
proof induction
  case (SkipSemicons p q m)
  hence "length p \<le> length q" by (intro length_skipping)
  hence "length p < length (m # q)" by simp
  with `length p = length (m # q)` have False by simp
  thus ?case..
qed auto

lemma skipping_self[simp]: "skipping a a"
  by (induction a) auto

lemma skipping_semiprepend[simp]:
  "skipping a (p @ a)"
  by (induction p) auto

lemma skip_append[intro]:
  assumes "skipping p q"
  shows "skipping (p @ a) (q @ a)"
  using assms
  by induction auto

lemma skip_semiappend[intro]:
  assumes "skipping p q"
  shows "skipping p (q @ a)"
  using assms
  by induction auto

lemma modpath:
  assumes "make_moves p 0 = x"
  shows "\<exists>p'. make_moves p' 0 = x mod 2^k \<and> skipping p' p"
  using assms
proof (induction p arbitrary: x k rule: rev_induct)
  case Nil
  then show ?case by force
next
  case (snoc m p)
  then show ?case
  proof (cases "x mod 2^k = 0")
    case True
    then show ?thesis
      by (auto intro: exI[of _ "[]"])
  next
    case False
    then show ?thesis
    proof (cases m)
      case Incr
      with snoc have x_eq: "x = Suc (make_moves p 0)" by simp
      with `x mod 2^k \<noteq> 0` have *: "x mod 2^k = Suc (make_moves p 0 mod 2^k)"
        using mod_Suc by auto
      from snoc.IH obtain p' where "make_moves p' 0 = make_moves p 0 mod 2^k" and "skipping p' p"
        by auto
      with * have "make_moves (p' @ [Incr]) 0 = x mod 2^k"
        by auto
      thus ?thesis
        apply (intro exI[of _ "p' @ [Incr]"])
        using `skipping p' p` `m = Incr` by auto
    next
      case Jump
      with snoc have x_eq: "x = jump' (make_moves p 0)" (is "x = jump' ?x'") by simp
      hence x_cong: "[jump' (?x' mod 2^k) = x] (mod 2^k)" by (simp add: jump_mod)
      then consider (nowrap) "jump' (?x' mod 2^k) = x mod 2^k"
        | (wrap) "jump' (?x' mod 2^k) > 2^k"
        by (smt `x mod 2^k \<noteq> 0` cong_def linorder_neqE_nat mod_less mod_self)
        
      then show ?thesis
      proof cases
        case nowrap
        from snoc.IH obtain p' where "make_moves p' 0 = ?x' mod 2^k" and "skipping p' p" by auto
        with nowrap have "make_moves (p' @ [Jump]) 0 = x mod 2^k" by simp
        then show ?thesis
          apply (intro exI[of _ "p' @ [Jump]"])
          using `skipping p' p` `m = Jump` by auto
      next
        let ?k' = "multiplicity 2 (?x' mod 2^k)"
        case wrap
        then have jump_mod2k: "[jump' (?x' mod 2^k) = 2^?k'] (mod 2^k)"
          by (intro jump_mod_rollover; auto)
        with x_cong have "[x = 2^?k'] (mod 2^k)"
          by (metis cong_trans cong_sym)
        have x_mod: "x mod 2^k = 2^?k'"
        proof -
          from `[x = 2^?k'] (mod 2^k)` have "x mod 2^k = 2^?k' mod 2^k"
            unfolding cong_def.
          hence "x mod 2^k = 0 \<or> x mod 2^k = 2^?k'"
            by (simp add: exp_mod_exp)
          with `x mod 2^k \<noteq> 0` show "x mod 2^k = 2^?k'"
            by simp
        qed
        hence "?k' < k"
          by (metis mod_less_divisor nat_power_less_imp_less nat_zero_less_power_iff power_eq_0_iff power_zero_numeral)
        hence "Suc ?k' \<le> k" by simp
        hence dvd: "(2::nat)^Suc ?k' dvd 2^k"
          using le_imp_power_dvd by blast 
        
        have "?x' mod 2^Suc ?k' = 2^?k'"
        proof -
          have "2^?k' dvd ?x' mod 2^k" by (fact multiplicity_dvd)
          with `Suc ?k' \<le> k` have "2^?k' dvd ?x'"
            by (meson Suc_leD dvd_mod_imp_dvd dvd_power_le gcd_nat.refl)
          hence "2^?k' dvd ?x' mod 2^Suc ?k'"
            by (simp add: dvd_mod)
          then obtain w where w: "?x' mod 2^Suc ?k' = 2^?k' * w" by blast
          have "?x' mod 2^Suc ?k' < 2^Suc ?k'" by simp
          with w have "2^?k' * w < 2^Suc ?k'" by simp
          hence "w < 2" by simp
          hence "w = 0 \<or> w = 1" by auto
          moreover have "w \<noteq> 0"
          proof
            assume "w = 0"
            with w have "2^Suc ?k' dvd ?x'" by auto
            with dvd have "2^Suc ?k' dvd ?x' mod 2^k"
              by (simp add: dvd_mod)
            hence "?k' \<ge> Suc ?k'"
            proof (intro multiplicity_geI)
              show "?x' mod 2^k \<noteq> 0"
                by (metis jump'_0 not_less0 wrap)
            qed auto
            thus False by simp
          qed

          ultimately have "w = 1" by simp
          with w show "?x' mod 2^Suc ?k' = 2^?k'" by simp
        qed
        moreover obtain p' where "make_moves p' 0 = ?x' mod 2^Suc ?k'" and "skipping p' p"
          using snoc.IH by blast
        ultimately have "make_moves p' 0 = x mod 2^k" using x_mod by simp
        then show ?thesis
          apply (intro exI[of _ "p'"])
          using `skipping p' p` by auto
      qed
    qed
  qed
qed

lemma strip_zero:
  assumes "make_moves p 0 = x" and "x \<noteq> 0"
  shows "\<exists>p'. make_moves p' 1 = x \<and> length p' < length p"
  using assms
proof (induction p)
  case (Cons m p)
  show ?case
  proof (cases m)
    case Incr
    with Cons show ?thesis by (intro exI[of _ p]; auto)
  next
    case Jump
    with Cons.prems have "make_moves p 0 = x" by auto
    with Cons show ?thesis by auto
  qed
qed auto

lemma odd_height:
  assumes "odd k" and "k > 1"
  shows "height' (2^i) < height' (2^i * k)"
proof -
  from assms have "2^i * k \<noteq> 0"
    by (simp add: odd_pos)
  with heightD obtain p where "make_moves p 1 = 2^i * k"
    and **: "length p = height' (2^i * k)"
    by blast
  then have p_result: "make_moves (Incr # p) 0 = 2^i * k" by simp
  with modpath obtain p' where "make_moves p' 0 = 2^i * k mod 2^Suc i"
    and skipping: "skipping p' (Incr # p)"
    by blast
  hence p'_result: "make_moves p' 0 = 2^i"
    using `odd k`
    by (simp add: odd_iff_mod_2_eq_one)
  from skipping and length_skipping have "length p' \<le> Suc (length p)"
    by force
  also have "length p' \<noteq> Suc (length p)"
  proof
    assume "length p' = Suc (length p)"
    hence "p' = Incr # p" by (intro skipping_equal; auto simp add: skipping)
    hence "make_moves p' 0 = make_moves (Incr # p) 0" by simp
    hence "k = 1" using p_result p'_result by simp
    with `k > 1` show False by simp
  qed
  finally have *: "length p' \<le> length p" by simp

  have "(2::nat)^i \<noteq> 0" by simp
  with p'_result obtain p''
    where p'': "make_moves p'' 1 = 2^i"
      and "length p'' < length p'"
    using strip_zero by blast
  with * have "length p'' < length p" by simp
  moreover from p'' have "height' (2^i) \<le> length p''" by auto
  ultimately show "height' (2^i) < height' (2^i * k)" using ** by simp
qed

theorem problem5:
  assumes "k \<ge> 2"
  shows "height (2^i) < height (2^i * k)"
proof -
  let ?n = "multiplicity 2 k"
  obtain k' where "k = 2^?n * k'" and "odd k'"
    using multiplicity_decompose' assms
    by (metis not_numeral_le_zero odd_one)
  then have "height' (2^i) < height' (2^i * k)"
  proof (cases ?n)
    case 0
    hence "k = k'" using `k = 2^?n * k'` by simp
    hence "odd k" using `odd k'` by simp
    thus "height' (2^i) < height' (2^i * k)"
      using assms by (auto intro: odd_height)
  next
    case (Suc n)
    have "height' (2^i) < height' (2^Suc n * 2^i)"
      by (intro twopow_reduce; auto)
    also have "... = height' (2^(?n + i))"
      by (simp add: power_add Suc ac_simps)
    also have "... \<le> height' (2^(?n + i) * k')"
    proof (cases "k' = 1")
      case True
      then show ?thesis by simp
    next
      case False
      then have "height' (2^(?n + i)) < height' (2^(?n + i) * k')"
        using `odd k'` by (intro odd_height; auto simp add: Suc_lessI odd_pos)
      then show ?thesis by simp
    qed
    also have "... = height' (2^i * (2^?n * k'))"
      by (simp add: ac_simps power_add)
    finally show "height' (2^i) < height' (2^i * k)"
      using `k = 2^?n * k'` by simp
  qed
  thus ?thesis by simp
qed

end