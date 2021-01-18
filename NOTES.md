This document contains various notes on the mathematical library of Isabelle/HOL.

# Functions

In general, functions are defined on an entire type. As such, [`undefined` may sometimes
get involved][undefined]. In general, there is no way to prove that `undefined`
doesn't occur. For a surjective function `f`, `⋀x. f x ≠ undefined` is outright
provably false. If you need to model a partial function, consider using `'a ⇀ 'b`
(which expands to `'a ⇒ 'b option`).

 - `inj f`, `surj f`, `bij f` - respective properties *on the entire types*
 - `inj_on f A`, `bij_betw f A B` - said properties on a specified set
 - ``f ` S`` - image of set `S` through `f` (thus, surjectivity onto a set can be specified as ``f ` A = B``)
   - also known as mapping over a set
 - `f^^n` - repeated application
   - beware of operator precedence here. `f^^n x = f^^(n x)`, not `(f^^n) x`
 - `λx. x + 2` (`%x. x + 2`) - inline function (aka. lambda or closure)
 - `f(a := y)` - change a single value of a function, i.e. `λx. if x = a then y else f x`
   - this can be chained: `f(a := b, c := d)`
   - also works for partial functions: `f(a ↦ b)` (that's a `\mapsto` arrow)
   - and lists: `xs[n := x]`
   - and records: `r⦇field := v⦈`
 - from `HOL-Library.FuncSet`:
     - `A → B` - set of functions `f` such that ``f ` A ⊆ B``
     - `extensional A` - set of functions that have the value `undefined` on all inputs outside of the set `A`.
       You probably won't ever want to prove that a specific function belongs to such a set (unless as a precondition of some lemma...).
       Instead, the goal is to fix a specific value outside of `A`, such that each function we can define on `A` has only one representative.
       - See `extensionalityI`

# Induction

There are plenty of examples of induction on natural numbers or lists. However,
there are many other induction rules that can be used (specify the rule with
`(induction x y arbitrary: z rule: foo)`). Some examples:

- `rev_induct` - list induction, but the new element is at the end (`xs @ [x]`)
- `list_nonempty_induct` - list induction, but has assumption `xs ≠ []` and `[x]` is the base case
- `list_induct2` - induction on two lists at once (where the lists are of equal length)
- `list_induct2'` - induction on two lists at once (with separate cases for `?P (x # xs) []` and `?P [] (y # ys)`)
- `int_induct` - induction on integers. Pick an arbitrary threshold value, and prove
    two inductive steps: ascending, above the threshold, and descending, below the threshold
- `less_induct` - the *strong induction*, where the inductive hypothesis is that all numbers smaller than the current one satisfy `?P`
- `finite_induct` - proves a statement about a finite set by adding one element at a time
  - beware of `finite.induct`, which is the same thing but also makes you handle the case where the "new" element was actually already in the set
- `finite_induct_select` - lets you choose a specific element to remove/insert on each iteration
- `finite_linorder_min_induct`, `finite_linorder_max_induct` - the elements are inserted into the set in sorted order
- `finite_ranking_induct` - likewise, but lets you specify a comparison key
- `prime_divisors_induct` - induction on the prime factorization of a number

Moreover, any recursive function `foo` will also have a corresponding induction rule `foo.induct`,
with a case for each defining equation. Useful for non-conventional recursion schemes.

# Pigeonhole Principle

At first, it might seem hard to formalize this kind of reasoning. Most of the time,
what you actually want is the property that if `f: A -> B` is an injective function,
then `card A <= card B`. When you have `card A > card B`, you can infer that the
function in question cannot be injective.

# Number Theory

Even though `nat` doesn't contain negative numbers, the subtraction operator is nevertheless
defined for `nat`. The result gets capped at 0, i.e. `3 - 5 = 0`. This may make rearranging expressions
a considerable difficulty for proof automation.

One workaround I've developed is to lift the definition in the integers:

```isabelle
context
  fixes g :: "nat ⇒ nat"
  fixes h :: "nat ⇒ nat"
  assumes gh: "⋀x. g x ≥ h x"
begin

definition f :: "nat ⇒ nat" where
  "f x = g x - h x"

lemma f_alt: "int (f x) = int (g x) - int (h x)"
  by (simp add: f_def nat_minus_as_int gh)
```

Then, instead of unfolding `f_def`, add `int` around your claim and use `f_alt`. From `int x = int y`, `x = y` easily follows.
For an extended example, see my solution of [IMO 2019 Problem 5][imo2019-p5].

Other useful stuff:

 - `a div b`, `a mod b` - Euclidean division
 - `[a = b] (mod c)` - congruences (in `HOL-Number_Theory.Cong`)
 - `multiplicity p n` - exponent of `p` in factorization of `n` (in `HOL-Computational_Algebra.Factorial_Ring`, imported in `HOL-Number_Theory`)
 - `prime p`
   - the definition you probably want is in `HOL-Computational_Algebra.Factorial_Ring`, but if you (even transitively) import `HOL-Algebra.Divisibility`,
     you will end up with a definition for prime elements in monoids as the default.  To correct this, use `hide_const (open) Divisibility.prime`.
   - if you need to prove that a larger number is prime, the AFP has [a `by pratt` proof method][pratt] that is much more efficient than simple `by simp`.
 - `n choose k` - the binomial coefficient. Beware of the precedence, `a + b choose c + d = ((a + b) choose c) + d`

# Abstract algebra

## The two definitions of a group

The more fundamental structures have two independent definitions.
For example, groups are first introduced in `HOL.Groups.group`:

```isabelle
locale semigroup =
  fixes f :: "'a ⇒ 'a ⇒ 'a"  (infixl "❙*" 70)
  assumes assoc [ac_simps]: "a ❙* b ❙* c = a ❙* (b ❙* c)"

locale group = semigroup +
  fixes z :: 'a ("❙1")
  fixes inverse :: "'a ⇒ 'a"
  assumes group_left_neutral: "❙1 ❙* a = a"
  assumes left_inverse [simp]:  "inverse a ❙* a = ❙1"
```

This defines a locale in which an abstract associative operation with all the properties
we know and love is available. This is convenient when you want to prove simple
statements about the elements inside a group, but gets unwieldy when we want to think
about groups as first-class objects, with subgroups and stuff.

For this reason, most of group theory is developed in terms of the definition in `HOL-Algebra`.
The `HOL-Algebra` group has two main differences:
 - Instead of using the entire type, an explicit carrier set is defined. (Subtyping is *possible*
   in Isabelle/HOL (see the `typedef` command), but not particularily pleasant.)
 - The values that define the group are wrapped up into a record.

```isabelle
record 'a partial_object =
  carrier :: "'a set"

record 'a monoid =  "'a partial_object" +
  mult    :: "['a, 'a] ⇒ 'a" (infixl "⊗ı" 70)
  one     :: 'a ("𝟭ı")
```

Note that apart from a `'a monoid` type, this also defines `('a, 'b) monoid_scheme`. This has nothing
to do with the mathematical notion of a scheme in algebraic geometry, and comes from Isabelle's
mechanism for extensible records.

For an in-depth explanation of records, see [tutorial.pdf] section 8.2, but the gist is that
each record has a secret `…` field that stores the contents of any potential record extensions.
The `scheme` is the type of a potentially-extended record, where the last type parameter
is the type of that field. As you might expect, `'a monoid` is a synonym of `('a, unit) monoid_scheme`.

## Locale or not

Of course, we still need to declare the actual laws. This is still done with a locale:

```isabelle
locale monoid =
  fixes G (structure)
  assumes m_closed [intro, simp]:
         "⟦x ∈ carrier G; y ∈ carrier G⟧ ⟹ x ⊗ y ∈ carrier G"
      and m_assoc:
         "⟦x ∈ carrier G; y ∈ carrier G; z ∈ carrier G⟧
          ⟹ (x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
      and one_closed [intro, simp]: "𝟭 ∈ carrier G"
      and l_one [simp]: "x ∈ carrier G ⟹ 𝟭 ⊗ x = x"
      and r_one [simp]: "x ∈ carrier G ⟹ x ⊗ 𝟭 = x"
```

We can use this in two ways. Firstly, we can actually state our theorem inside
the locale. This is most commonly used if only one group is involved.
In this situation, our group is `G`, the operation is `⊗` (`\otimes`),
the identity is `𝟭` (`\one`), and inverses can be obtained with the `inv` function.

```isabelle
lemma (in group) inv_eq_1_iff [simp]:
  assumes "x ∈ carrier G" shows "inv x = 𝟭 ⟷ x = 𝟭"
proof -
  have "x = 𝟭" if "inv x = 𝟭"
  proof -
    have "inv x ⊗ x = 𝟭"
      using assms l_inv by blast
    then show "x = 𝟭"
      using that assms by simp
  qed
  then show ?thesis
    by auto
qed
```

Secondly, each locale also defines a predicate which combines all its assumptions:

```isabelle
  assumes "group G"
```

In this situation, the group being used must be provided explicitly — the operation is
`⊗⇘G⇙` (where the subscript arrows can be typed as `=_(` and `=_)` respectively),
the identity is `𝟭⇘G⇙`, the inverse function is `inv⇘G⇙`, and so on.

## Subgroups

We can talk about subgroups with `subgroup H G`. Note that while `G` is an entire
group (that is, `('a, 'b) monoid_scheme`), `H` is only a set of elements.

If you want to use `H` as a full-fledged group, you'll need to use record update syntax:

```isabelle
lemma (in subgroup) subgroup_is_group [intro]:
  assumes "group G"
  shows "group (G⦇carrier := H⦈)"
```

(the funny parentheses can be typed with `(|` and `|)`)

 - `generate G S` - subgroup (as set) of `G` generated by `S`
 - `subgroup_generated G S` - subgroup (as full group) of `G` generated by `S`

## Cosets

 - `x <# H` - left coset
 - `H #> x` - right coset
 - `A <#> B` - product of sets: `A <#> B = {a ⊗ b | a ∈ A ∧ b ∈ B}`
 - `normal H G` or `H ⊲ G` (`\lhd`) - `H` is a normal subgroup of `G`
 - `G Mod N` - quotient group

**NOTE:** `H ⊲ G` assumes `group G`, but `subgroup H G` doesn't.

## Abelian groups

You most likely want `comm_group`. Do not confuse this with the `abelian_group` locale,
which talks about `add_monoid G`, the additive group of a ring called `G`.

## Morphisms

For groups, we have `hom G H`, the set of all homomorphisms `G => H`. Likewise, there's
`iso G H`. Moreover, when we merely want to say that an isomorphism exists, there is the
`≅` (`\cong`) operator.

For rings, there's `ring_hom` and `ring_iso`, and the operator is `≃` (`\simeq`) instead.

For more exotic morphisms, we have `mon G H` (set of injective homomorphisms),
`epi G H` (set of surjective homomorphisms).

For automorphisms, see `auto G`. There doesn't seem to be an equivalent for endomorphisms,
perhaps because they aren't that interesting as an object. For the automorphism group, see
`AutoGroup G`.

On a related topic, there's `Bij S` (bijections on S) and `BijGroup S` (group of bijections).

## Specific groups

 - `G ×× H` (`\times\times`) - direct product (group of pairs)
 - `sym_group n` - group of permutations of n elements (symmetric group)
 - `alt_group n` - group of even permutations of n elements (alternating group)
 - `free_Abelian_group S` - free Abelian group on generators S
 - for free groups, see [this AFP entry][free-groups]

### Cyclic groups

 - `cyclic_group G` - predicate: generator exists
 - `integer_mod_group n` - concrete instance of cyclic group of order `n`. In particular,
   `integer_mod_group 0 = integer_group`

Note that some facts about cyclic groups, such as `cyclic_group (integer_mod_group n)`,
are missing from `HOL-Algebra`. See `Cyclic_Groups.thy`.

## Other useful things

 - exponentiation in groups: `x [^] n`
 - `order S = card (carrier S)`
 - order of an element: `ord x`

# Analysis

The main analysis definitions in Isabelle are based on *filters*. For an introduction, see [this paper][filters]
(freely available [here][scihub]).

 - `DERIV_intros`, `tendsto_intros` - lemma collections, to be used with `(auto intro: DERIV_intros)` or similar
 - the `real_asymp` proof method (available in `HOL-Real_Asymp.Real_Asymp`) is able to prove many limits automatically
   (there's [a paper][real-asymp] that describes its mechanisms)

[tutorial.pdf]: https://isabelle.in.tum.de/dist/Isabelle2020/doc/tutorial.pdf
[free-groups]: https://www.isa-afp.org/entries/Free-Groups.html
[undefined]: https://www.joachim-breitner.de/blog/732-Isabelle_functions__Always_total,_sometimes_undefined
[filters]: https://dx.doi.org/10.1007%2F978-3-642-39634-2_21
[scihub]: https://en.wikipedia.org/wiki/Sci-Hub
[real-asymp]: https://www21.in.tum.de/~eberlm/pdfs/real_asymp.pdf
[pratt]: https://www.isa-afp.org/entries/Pratt_Certificate.html
[imo2019-p5]: https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/IMO/2019/IMO-2019-Problem_5.pdf

