import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/- TEXT:
.. _counting_arguments:

Counting Arguments
------------------

The art of counting things is a central part of combinatorics.
Mathlib contains several basic identities for counting elements of finsets:
BOTH: -/
-- QUOTE:
open Finset

-- EXAMPLES:
variable {α β : Type*} [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α → β)

example : #(s ×ˢ t) = #s * #t := by simp

example : #(s ∪ t) = #s + #t - #(s ∩ t) := card_union _ _

example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by simp [h]

example (h : Function.Injective f) : #(s.image f) = #s := by rw [card_image_of_injective _ h]

example (h : Set.InjOn f s) : #(s.image f) = #s := by rw [card_image_of_injOn h]
-- QUOTE.

/- TEXT:
Opening the ``Finset`` namespace allows us to use the notation ``#s`` for ``s.card``, as well as
to use the shortened names `card_union` and so on.

Mathlib can also count elements of fintypes:
EXAMPLES: -/
section
-- QUOTE:
open Fintype

variable {α β : Type*} [Fintype α] [Fintype β]

example : card (α × β) = card α * card β := by simp

example : card (α ⊕ β) = card α + card β := by simp

example (n : ℕ) : card (Fin n → α) = (card α)^n := by simp

variable {n : ℕ} {γ : Fin n → Type*} [∀ i, Fintype (γ i)]

example : card ((i : Fin n) → γ i) = ∏ i, card (γ i) := by simp

example : card (Σ i, γ i) = ∑ i, card (γ i) := by simp
-- QUOTE.

end

/- TEXT:
When the ``Fintype`` namespace is not open, we have to use ``Fintype.card`` instead of `card`.

The following is an example of calculating the cardinality of a finset, namely, `range n` together
with a copy of range `n` shifted by more than `n`.
The calculation requires showing the the two sets in the union are disjoint;
the first line of the proof yields the side condition
``Disjoint (range n) (image (fun i ↦ m + i) (range n))``, which is established at the end of the
proof.
The ``Disjoint`` predicate is too general to be directly useful to us, but the theorem
``disjoint_iff_ne`` puts it in a form we can use.
EXAMPLES: -/
-- QUOTE:
#check Disjoint

example (m n : ℕ) (h : m ≥ n) :
    card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint, card_range, card_image_of_injective, card_range]; omega
  . apply add_right_injective
  . simp [disjoint_iff_ne]; omega
-- QUOTE.

/- TEXT:
Throughout this section, ``omega`` will be a workhorse for us, for dealing with arithmetic
calculations and inequalities.

Here is a more interesting example. Consider the subset of
:math:`\{0, \ldots, n\} \times \{0, \ldots, n\}` consisting
of pairs :math:`(i, j)` such that :math:`i < j`. If you think of these as lattice points in the coordinate
plane, they constitute an upper triangle of the square with corners :math:`(0, 0)` and
:math:`(n, n)`, not
including the diagonal. The cardinality of the full square is :math:`(n + 1)^2`, and removing the size of
the diagonal and halving the result shows us that the cardinality of the triangle is
:math:`n (n + 1) / 2`.

Alternatively, we note that the rows of the triangle have sizes :math:`0, 1, \ldots, n`, so the
cardinality is the sum of the first :math:`n` natural numbers. The first ``have`` of the proof
below describes the triangle as the union of the rows, where row :math:`j` consists of
the numbers :math:`0, 1, ..., j - 1` paired with :math:`j`.
In the proof below, the notation ``(., j)`` abbreviates the function
``fun i ↦ (i, j)``. The rest of the proof is just a calculation with finset cardinalities.
BOTH: -/
-- QUOTE:
def triangle (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range (n+1) ×ˢ range (n+1) | p.1 < p.2}

-- EXAMPLES:
example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n = (range (n+1)).biUnion (fun j ↦ (range j).image (., j)) := by
    ext p
    simp only [triangle, mem_filter, mem_product, mem_range, mem_biUnion, mem_image]
    constructor
    . rintro ⟨⟨hp1, hp2⟩, hp3⟩
      use p.2, hp2, p.1, hp3
    . rintro ⟨p1, hp1, p2, hp2, rfl⟩
      omega
  rw [this, card_biUnion]; swap
  · -- take care of disjointness first
    intro x _ y _ xney
    simp [disjoint_iff_ne, xney]
  -- continue the calculation
  transitivity (∑ i in range (n+1), i)
  · congr; ext i
    rw [card_image_of_injective, card_range]
    intros i1 i2; simp
  rw [sum_range_id]; rfl
-- QUOTE.

/- TEXT:
The following variation on the proof does the calculation with fintypes instead of finsets.
The type ``α ≃ β`` is the type of equivalences between ``α`` and ``β``, consisting of a map
in the forward direction, the map in the backward direction, and proofs that these two are
inverse to one another. The first ``have`` in the proof shows that ``triangle n`` is equivalent to
the disjoint union of ``Fin i`` as ``i`` ranges over ``Fin (n + 1)``. Interestingly, the forward
function and the reverse function are constructed with tactics, rather than written explicitly.
Since they do nothing more than move data and information around, ``rfl`` establishes that they
are inverses.

After that, ``rw [←Fintype.card_coe]`` rewrites ``#(triangle n)`` as the cardinality of the subtype
``{ x // x ∈ triangle n }``, and the rest of the proof is a calculation.
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n ≃ Σ i : Fin (n + 1), Fin i.val :=
    { toFun := by
        rintro ⟨⟨i, j⟩, hp⟩
        simp [triangle] at hp
        exact ⟨⟨j, hp.1.2⟩, ⟨i, hp.2⟩⟩
      invFun := by
        rintro ⟨i, j⟩
        use ⟨j, i⟩
        simp [triangle]
        exact j.isLt.trans i.isLt
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [←Fintype.card_coe]
  trans; apply (Fintype.card_congr this)
  rw [Fintype.card_sigma, sum_fin_eq_sum_range]
  convert Finset.sum_range_id (n + 1)
  simp_all
-- QUOTE.

/- TEXT:
Here is yet another approach. The first line of the proof below reduces the problem to showing
``2 * #(triangle n) = (n + 1) * n``. We can do that by showing that two copies of the triangle
exactly fill the rectangle ``range n ×ˢ range (n + 1)``.
As an exercise, see if you can fill in the steps of the calculation.
In the solutions, we rely on ``omega``
extensively in the second-to-last step, but we unfortunately have to do a fair amount of
work by hand.
BOTH: -/
-- QUOTE:
example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  apply Nat.eq_div_of_mul_eq_right (by norm_num)
  let turn (p : ℕ × ℕ) : ℕ × ℕ := (n - 1 - p.1, n - p.2)
  calc 2 * #(triangle n)
      = #(triangle n) + #(triangle n) := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          ring
BOTH: -/
    _ = #(triangle n) + #(triangle n |>.image turn) := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          rw [Finset.card_image_of_injOn]
          rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [turn]
          simp_all [triangle]; omega
BOTH: -/
    _ = #(range n ×ˢ range (n + 1)) := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          rw [←Finset.card_union_of_disjoint]; swap
          . rw [Finset.disjoint_iff_ne]
            rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [turn] at *
            simp_all [triangle]; omega
          congr; ext p; rcases p with ⟨p1, p2⟩
          simp [triangle, turn]
          constructor
          . rintro (h | h) <;> omega
          rcases Nat.lt_or_ge p1 p2 with h | h
          . omega
          . intro h'
            right
            use n - 1 - p1, n - p2
            omega
BOTH: -/
    _ = (n + 1) * n := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          simp [mul_comm]
BOTH: -/
-- QUOTE.

/- TEXT:
You can convince yourself that we get the same triangle, shifted down, if we replace ``n`` by
``n + 1``
and replace ``<`` by ``≤`` in the definition of ``triangle``.
The exercise below asks you to use this fact to show that the two triangles have the same size.
BOTH: -/
-- QUOTE:
def triangle' (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range n ×ˢ range n | p.1 ≤ p.2}

-- EXAMPLES:
example (n : ℕ) : #(triangle' n) = #(triangle n) := by sorry
/- SOLUTIONS:
example (n : ℕ) : #(triangle' n) = #(triangle n) := by
  let f (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.2 + 1)
  have : triangle n = (triangle' n |>.image f) := by
    ext p; rcases p with ⟨p1, p2⟩
    simp [triangle, triangle', f]
    constructor
    . intro h
      use p1, p2 - 1
      omega
    . simp; omega
  rw [this, card_image_of_injOn]
  rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [f] at *
BOTH: -/
-- QUOTE.

/- TEXT:
Let us close this section with an example and an exercise from a `tutorial <https://www.youtube.com/watch?v=_cJctOIXWE4&list=PLlF-CfQhukNn7xEbfL38eLgkveyk9_myQ&index=8&t=2737s&ab_channel=leanprovercommunity>`_
on combinatorics given by Bhavik Mehta at *Lean for the Curious Mathematician* in 2023.
Suppose we have a bipartite graph with vertex sets ``s`` and ``t``, such that for every ``a`` in
``s``, there are at least three edges leaving ``a``, and for every ``b`` in ``t``, there is at most
one edge entering ``b``. Then the total number of edges in the graph is at least three times the
cardinality of ``s`` and at most the cardinality of ``t``, from which is follows that the
cardinality of ``t`` is at least three times the cardinality of ``s``.
The following theorem implements this argument, where we use the relation ``r`` to represent
the edges of the graph. The proof is an elegant calculation.
EXAMPLES: -/
section
-- QUOTE:
open Classical
variable (s t : Finset Nat) (a b : Nat)

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #{b ∈ t | r a b})
    (h_right : ∀ b ∈ t, #{a ∈ s | r a b} ≤ 1) :
    3 * #(s) ≤ #(t) := by
  calc
    3 * #(s) = ∑ a ∈ s, 3 := by simp [sum_const_nat, mul_comm]
    _ ≤ ∑ a ∈ s, #({b ∈ t | r a b}) := sum_le_sum h_left
    _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := sum_comm
    _ = ∑ b ∈ t, #({a ∈ s | r a b}) := by simp
    _ ≤ ∑ b ∈ t, 1 := sum_le_sum h_right
    _ ≤ #(t) := by simp
-- QUOTE.

/- TEXT:
The following exercise is also taken from Mehta's tutorial. Suppose ``A`` is a subset of
``range (2 * n)`` with ``n + 1`` elements.
It's easy to see that ``A`` must contain two
consecutive integers, and hence two elements that are coprime.
If you watch the tutorial, you will see that a good deal of effort was spent in
establishing the following fact, which is now proved automatically by ``omega``.
EXAMPLES: -/
-- QUOTE:
example (m k : ℕ) (h : m ≠ k) (h' : m / 2 = k / 2) : m = k + 1 ∨ k = m + 1 := by omega
-- QUOTE.

/- TEXT:
The proof of the claim uses the pigeonhole principle, in the form
``exists_lt_card_fiber_of_mul_lt_card_of_maps_to``, to show that there are two distinct elements
``m`` and ``k`` in ``A`` such that ``m / 2 = k / 2``.
See if you can complete the justification of that fact and then use it to finish the proof.
BOTH: -/
-- QUOTE:
example {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have : ∃ t ∈ range n, 1 < #({u ∈ A | u / 2 = t}) := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
-- EXAMPLES:
    · sorry
/- SOLUTIONS:
    · intro u hu
      specialize hA' hu
      simp only [mem_range] at *
      exact Nat.div_lt_of_lt_mul hA'
EXAMPLES: -/
    · sorry
/- SOLUTIONS:
    · simp [hA]
BOTH: -/
  rcases this with ⟨t, ht, ht'⟩
  simp only [one_lt_card, mem_filter] at ht'
-- EXAMPLES:
  sorry
/- SOLUTIONS:
  rcases ht' with ⟨m, ⟨hm, hm'⟩, k, ⟨hk, hk'⟩, hmk⟩
  have : m = k + 1 ∨ k = m + 1 := by omega
  rcases this with rfl | rfl
  . use k, hk, k+1, hm; simp
  . use m, hm, m+1, hk; simp
BOTH: -/
-- QUOTE.
