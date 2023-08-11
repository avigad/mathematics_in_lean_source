import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic

open BigOperators

namespace C05S03

/- TEXT:
.. _section_infinitely_many_primes:

Infinitely Many Primes
----------------------

Let us continue our exploration of induction and recursion with another
mathematical standard: a proof that there are infinitely many primes.
One way to formulate this is as the statement that
for every natural number
:math:`n`, there is a prime number greater than :math:`n`.
To prove this, let :math:`p` be any prime factor of :math:`n! + 1`.
If :math:`p` is less than :math:`n`, it divides :math:`n!`.
Since it also divides :math:`n! + 1`, it divides 1, a contradiction.
Hence :math:`p` is greater than :math:`n`.

To formalize that proof, we need to show that any number greater than or equal
to 2 has a prime factor.
To do that, we will need to show that any natural number that is
not equal to 0 or 1 is greater-than or equal to 2.
And this brings us to a quirky feature of formalization:
it is often trivial statements like this that are among the most
annoying to formalize.
Here we consider a few ways to do it.

To start with, we can use the ``cases`` tactic and the fact that the
successor function respects the ordering on the natural numbers.
BOTH: -/
-- QUOTE:
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat' apply Nat.succ_le_succ
    apply zero_le
-- QUOTE.

/- TEXT:
Another strategy is to use the tactic ``interval_cases``,
which automatically splits the goal into cases when
the variable in question is contained in an interval
of natural numbers or integers.
Remember that you can hover over it to see its documentation.
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction
-- QUOTE.

/- TEXT:
Recall that the semicolon after ``interval_cases m`` means
that the next tactic is applied to each of the cases that it generates.
Yet another option is to use the tactic, ``decide``, which tries
to find a decision procedure to solve the problem.
Lean knows that you can decide the truth value of a statement that
begins with a bounded quantifier ``∀ x, x < n → ...`` or ``∃ x, x < n ∧ ...``
by deciding each of the finitely many instances.
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide
-- QUOTE.

/- TEXT:
With the theorem ``two_le`` in hand, let's start by showing that every
natural number greater than two has a prime divisor.
Mathlib contains a function ``Nat.minFac`` that
returns the smallest prime divisor,
but for the sake of learning new parts of the library,
we'll avoid using it and prove the theorem directly.

Here, ordinary induction isn't enough.
We want to use *strong induction*, which allows us to prove
that every natural number :math:`n` has a property :math:`P`
by showing that for every number :math:`n`, if :math:`P` holds
of all values less than :math:`n`, it holds at :math:`n` as well.
In Lean, this principle is called ``Nat.strong_induction_on``,
and we can use the ``with`` keyword to tell the induction tactic
to use it.
Notice that when we do that, there is no base case; it is subsumed
by the general induction step.

The argument is simply as follows. Assuming :math:`n ≥ 2`,
if :math:`n` is prime, we're done. If it isn't,
then by one of the characterizations of what it means to be a prime number,
it has a nontrivial factor, :math:`m`,
and we can apply the inductive hypothesis to that.
Step through the next proof to see how that plays out.
The line ``dsimp at ih`` simplifies the expression of the
inductive hypothesis to make it more readable.
The proof still works if you delete that line.
BOTH: -/
-- QUOTE:
theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  dsimp at ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  . rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn
-- QUOTE.

/- TEXT:
We can now prove the following formulation of our theorem.
See if you can fill out the sketch.
You can use ``Nat.factorial_pos``, ``Nat.dvd_factorial``,
and ``Nat.dvd_sub``.
BOTH: -/
-- QUOTE:
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    exact Nat.succ_le_of_lt (Nat.factorial_pos _)
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine' ⟨p, _, pp⟩
  show p > n
  by_contra ple
  push_neg  at ple
  have : p ∣ Nat.factorial (n + 1) := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.dvd_factorial
    apply pp.pos
    linarith
-- BOTH:
  have : p ∣ 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub' pdvd this
    simp
-- BOTH:
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- TEXT:
Let's consider a variation of the proof above, where instead
of using the factorial function,
we suppose that we are given by a finite set
:math:`\{ p_1, \ldots, p_n \}` and we consider a prime factor of
:math:`\prod_{i = 1}^n p_i + 1`.
That prime factor has to be distinct from each
:math:`p_i`, showing that there is no finite set that contains
all the prime numbers.

Formalizing this argument requires us to reason about finite
sets. In Lean, for any type ``α``, the type ``Finset α``
represents finite sets of elements of type ``α``.
Reasoning about finite sets computationally requires having
a procedure to test equality on ``α``, which is why the snippet
below includes the assumption ``[DecidableEq α]``.
For concrete data types like ``ℕ``, ``ℤ``, and ``ℚ``,
the assumption is satisfied automatically. When reasoning about
the real numbers, it can be satisfied using classical logic
and abandoning the computational interpretation.

We use the command ``open Finset`` to avail ourselves of shorter names
for the relevant theorems. Unlike the case with sets,
most equivalences involving finsets do not hold definitionally,
so they need to be expanded manually using equivalences like
``Finset.subset_iff``, ``Finset.mem_union``, ``Finset.mem_inter``,
and ``Finset.mem_sdiff``. The ``ext`` tactic can still be used
to reduce show that two finite sets are equal by showing
that every element of one is an element of the other.
BOTH: -/
-- QUOTE:
open Finset

-- EXAMPLES:
section
variable {α : Type _} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end
-- QUOTE.

/- TEXT:
We have used a new trick: the ``tauto`` tactic (and a strengthened
version, ``tauto!``, which uses classical logic) can be used to
dispense with propositional tautologies. See if you can use
these methods to prove the two examples below.
BOTH: -/
section
variable {α : Type _} [DecidableEq α] (r s t : Finset α)

-- QUOTE:
example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_inter, mem_union, mem_union, mem_union, mem_inter]
  tauto

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

-- BOTH:
example : (r \ s) \ t = r \ (s ∪ t) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_sdiff, mem_sdiff, mem_sdiff, mem_union]
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto
-- QUOTE.
-- BOTH:

end

/- TEXT:
The theorem ``Finset.dvd_prod_of_mem`` tells us that if an
``n`` is an element of a finite set ``s``, then ``n`` divides
``∏ i in s, i``.
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h
-- QUOTE.

/- TEXT:
We also need to know that the converse holds in the case where
``n`` is prime and ``s`` is a set of primes.
To show that, we need the following lemma, which you should
be able to prove using the theorem ``Nat.Prime.eq_one_or_self_of_dvd``.
BOTH: -/
-- QUOTE:
theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  cases prime_q.eq_one_or_self_of_dvd _ h
  · linarith [prime_p.two_le]
  assumption
-- QUOTE.
-- BOTH:

/- TEXT:
We can use this lemma to show that if a prime ``p`` divides a product of a finite
set of primes, then it divides one of them.
Mathlib provides a useful principle of induction on finite sets:
to show that a property holds of an arbitrary finite set ``s``,
show that it holds of the empty set, and show that it is preserved
when we add a single new element ``a ∉ s``.
The principle is known as ``Finset.induction_on``.
When we tell the induction tactic to use it, we can also specify the names
``a`` and ``s``, the name for the assumption ``a ∉ s`` in the inductive step,
and the name of the inductive hypothesis.
The expression ``Finset.insert a s`` denotes the union of ``s`` with the singleton ``a``.
The identities ``Finset.prod_empty`` and ``Finset.prod_insert`` then provide
the relevant rewrite rules for the product.
In the proof below, the first ``simp`` applies ``Finset.prod_empty``.
Step through the beginning of the proof to see the induction unfold,
and then finish it off.
BOTH: -/
-- QUOTE:
theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rcases h₁ with h₁ | h₁
  · left
    exact prime_p.eq_of_dvd_of_prime h₀.1 h₁
  right
  exact ih h₀.2 h₁

-- BOTH:
-- QUOTE.
/- TEXT:
We need one last property of finite sets.
Given an element ``s : Set α`` and a predicate
``P`` on ``α``, in  :numref:`Chapter %s <sets_and_functions>`
we wrote ``{ x ∈ s | P x }`` for the set of
elements of ``s`` that satisfy ``P``.
Given ``s : Finset α``,
the analogous notion is written ``s.filter P``.
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter
-- QUOTE.

/- TEXT:
We now prove an alternative formulation of the statement that there are infinitely many
primes, namely, that given any ``s : Finset ℕ``, there is a prime ``p`` that is not
an element of ``s``.
Aiming for a contradiction, we assume that all the primes are in ``s``, and then
cut down to a set ``s'`` that contains all and only the primes.
Taking the product of that set, adding one, and finding a prime factor
of the result
leads to the contradiction we are looking for.
See if you can complete the sketch below.
You can use ``Finset.prod_pos`` in the proof of the first ``have``.
BOTH: -/
-- QUOTE:
theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg  at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    apply Nat.succ_le_of_lt
    apply Finset.prod_pos
    intro n ns'
    apply (mem_s'.mp ns').pos
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_prod_of_mem
    rw [mem_s']
    apply pp
-- BOTH:
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- TEXT:
We have thus seen two ways of saying that there are infinitely many primes:
saying that they are not bounded by any ``n``, and saying that they are
not contained in any finite set ``s``.
The two proofs below show that these formulations are equivalent.
In the second, in order to form ``s.filter Q``, we have to assume that there
is a procedure for deciding whether or not ``Q`` holds. Lean knows that there
is a procedure for ``Nat.Prime``. In general, if we use classical logic
by writing ``open Classical``,
we can dispense with the assumption.

In mathlib, ``Finset.sup s f`` denotes the supremum of the values of ``f x`` as ``x``
ranges over ``s``, returning ``0`` in the case where ``s`` is empty and
the codomain of ``f`` is ``ℕ``. In the first proof, we use ``s.sup id``,
where ``id`` is the identity function, to refer to the maximum value in ``s``.
BOTH: -/
-- QUOTE:
theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k
-- QUOTE.

/- TEXT:
A small variation on our second proof that there are infinitely many primes
shows that there are infinitely many primes congruent to 3 modulo 4.
The argument goes as follows.
First, notice that if the product of two numbers :math:`m` and :math:`n`
is equal to 3 modulo 4, then one of the two numbers is congruent to three modulo 4.
After all, both have to be odd, and if they are both congruent to 1 modulo 4,
so is their product.
We can use this observation to show that if some number
greater than 2 is congruent to 3 modulo 4,
then that number has a prime divisor that is also congruent to 3 modulo 4.

Now suppose there are only finitely many prime numbers congruent to 3
modulo 4, say, :math:`p_1, \ldots, p_k`.
Without loss of generality, we can assume that :math:`p_1 = 3`.
Consider the product :math:`4 \prod_{i = 2}^k p_i + 3`.
It is easy to see that this is congruent to 3 modulo 4, so it has
a prime factor :math:`p` congruent to 3 modulo 4.
It can't be the case that :math:`p = 3`; since :math:`p`
divides :math:`4 \prod_{i = 2}^k p_i + 3`, if :math:`p`
were equal to 3 then it would also divide :math:`\prod_{i = 2}^k p_i`,
which implies that :math:`p` is equal to
one of the :math:`p_i` for :math:`i = 2, \ldots, k`;
and we have excluded 3 from this list.
So :math:`p` has to be one of the other elements :math:`p_i`.
But in that case, :math:`p` divides :math:`4 \prod_{i = 2}^k p_i`
and hence 3, which contradicts the fact that it is not 3.

In Lean, the notation ``n % m``, read "``n`` modulo ``m``,"
denotes the remainder of the division of ``n`` by ``m``.
EXAMPLES: -/
-- QUOTE:
example : 27 % 4 = 3 := by norm_num
-- QUOTE.

/- TEXT:
We can then render the statement "``n`` is congruent to 3 modulo 4"
as ``n % 4 = 3``. The following example and theorems sum up
the facts about this function that we will need to use below.
The first named theorem is another illustration of reasoning by
a small number of cases.
In the second named theorem, remember that the semicolon means that
the subsequent tactic block is applied to both of the goals
that result from the application of ``two_le``.
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]
  norm_num

-- BOTH:
theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases hm : m % 4 <;> simp [hm]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases hn : n % 4 <;> simp [hn]

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h
-- QUOTE.

/- TEXT:
We will also need the following fact, which says that if
``m`` is a nontrivial divisor of ``n``, then so is ``n / m``.
See if you can complete the proof using ``Nat.div_dvd_of_dvd``
and ``Nat.div_lt_self``.
BOTH: -/
-- QUOTE:
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · exact Nat.div_dvd_of_dvd h₀
  exact Nat.div_lt_self (lt_of_le_of_lt (zero_le _) h₂) h₁
-- QUOTE.

-- BOTH:
/- TEXT:
Now put all the pieces together to prove that any
number congruent to 3 modulo 4 has a prime divisor with that
same property.
BOTH: -/
-- QUOTE:
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  dsimp at ih
  rw [Nat.prime_def_lt] at np
  push_neg  at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
/- EXAMPLES:
  . sorry
  . sorry
SOLUTIONS: -/
  · by_cases mp : m.Prime
    · use m
    rcases ih m mltn h1 mp with ⟨p, pp, pdvd, p4eq⟩
    use p
    exact ⟨pp, pdvd.trans mdvdn, p4eq⟩
  obtain ⟨nmdvdn, nmltn⟩ := aux mdvdn mge2 mltn
  by_cases nmp : (n / m).Prime
  · use n / m
  rcases ih (n / m) nmltn h1 nmp with ⟨p, pp, pdvd, p4eq⟩
  use p
  exact ⟨pp, pdvd.trans nmdvdn, p4eq⟩

-- BOTH:
-- QUOTE.
/- TEXT:
We are in the home stretch. Given a set ``s`` of prime
numbers, we need to talk about the result of removing 3 from that
set, if it is present. The function ``Finset.erase`` handles that.
EXAMPLES: -/
-- QUOTE:
example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption
-- QUOTE.

/- TEXT:
We are now ready to prove that there are infinitely many primes
congruent to 3 modulo 4.
Fill in the missing parts below.
Our solution uses ``Nat.dvd_add_iff_left`` and ``Nat.dvd_sub'``
along the way.
BOTH: -/
-- QUOTE:
theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg  at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [add_comm, Nat.add_mul_mod_self_left]
    norm_num
-- BOTH:
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [← hs p]
    exact ⟨pp, p4eq⟩
-- BOTH:
  have pne3 : p ≠ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    intro peq
    rw [peq, ← Nat.dvd_add_iff_left (dvd_refl 3)] at pdvd
    rw [Nat.prime_three.dvd_mul] at pdvd
    norm_num at pdvd
    have : 3 ∈ s.erase 3 := by
      apply mem_of_dvd_prod_primes Nat.prime_three _ pdvd
      intro n
      simp [← hs n]
      tauto
    simp at this
-- BOTH:
  have : p ∣ 4 * ∏ i in erase s 3, i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_trans _ (dvd_mul_left _ _)
    apply dvd_prod_of_mem
    simp
    constructor <;> assumption
-- BOTH:
  have : p ∣ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub' pdvd this
    simp
-- BOTH:
  have : p = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply pp.eq_of_dvd_of_prime Nat.prime_three this
-- BOTH:
  contradiction
-- QUOTE.

/- TEXT:
If you managed to complete the proof, congratulations! This has been a serious
feat of formalization.
TEXT. -/
-- OMIT:
/-
Later:
o fibonacci numbers
o binomial coefficients

(The former is a good example of having more than one base case.)

TODO: mention ``local attribute`` at some point.
-/
