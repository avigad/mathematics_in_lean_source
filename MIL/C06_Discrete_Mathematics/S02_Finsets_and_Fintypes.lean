import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/- TEXT:
.. _finsets_and_fintypes:

Finsets and Fintypes
--------------------

Dealing with finite sets and types in Mathlib can be confusing, because the library offers
multiple ways of handling them. In this section we will discuss one of them.

We have already come across the type ``Finset`` in :numref:`section_induction_and_recursion`
and :numref:`section_infinitely_many_primes`.
As the name suggests, an element of type ``Finset α`` is a finite set of elements of type ``α``.
We will call the elements of such a type "finsets."
``Finset`` is designed to have a computational interpretation,
and many basic operations on ``Finset α`` assume that ``α`` has decidable equality, which guarantees
that there is an algorithm for testing whether ``a : α`` is an element
of a finset ``s``.
EXAMPLES: -/
-- QUOTE:
section
variable {α : Type*} [DecidableEq α] (a : α) (s t : Finset α)

#check a ∈ s
#check s ∩ t

end
-- QUOTE.

/- TEXT:
If you remove the declaration ``[DecidableEq α]``, Lean will complain on the line
``#check s ∩ t`` because it cannot compute the intersection.
All of the data types that you should expect to be able to compute with
have decidable equality, however,
and f you work classically by opening the ``Classical`` namespace and
declaring ``noncomputable section``, you can reason about finsets of elements of any type
at all.

Finsets support most of the set-theoretic operations that sets do:
EXAMPLES: -/
section
-- QUOTE:
open Finset

variable (a b c : Finset ℕ)
variable (n : ℕ)

#check a ∩ b
#check a ∪ b
#check a \ b
#check (∅ : Finset ℕ)

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  ext x
  simp only [mem_inter, mem_union]
  tauto

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  rw [inter_union_distrib_left]
-- QUOTE.

/- TEXT:
Note that we have opened the ``Finset`` namespace,
where theorems specific to finsets are found.
If you step through the last example below, you will see applying ``ext``
followed by ``simp`` reduces the identity to a problem
in propositional logic.
As an exercise, you can try proving some of set identities from
:numref:`Chapter %s <sets_and_functions>`, transported to finsets.

You have already seen the notation ``Finset.range n`` for the
finite set of natural numbers :math:`\{ 0, 1, \ldots, n-1 \}`.
``Finset`` also allows you to define finite sets by enumerating
the elements:
TEXT. -/
-- QUOTE:
#check ({0, 2, 5} : Finset Nat)

def example1 : Finset ℕ := {0, 1, 2}
-- QUOTE.

/- TEXT:
There are various ways to get Lean to recognize that order of elements and
duplicates do not matter in a set presented in this way.
EXAMPLES: -/
-- QUOTE:
example : ({0, 1, 2} : Finset ℕ) = {1, 2, 0} := by decide

example : ({0, 1, 2} : Finset ℕ) = {0, 1, 1, 2} := by decide

example : ({0, 1} : Finset ℕ) = {1, 0} := by rw [Finset.pair_comm]

example (x : Nat) : ({x, x} : Finset ℕ) = {x} := by simp

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i
  simp [or_comm, or_assoc, or_left_comm]

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i
  simp
  tauto
-- QUOTE.

/- TEXT:
You can use ``insert`` to add a single element to a Finset, and ``Finset.erase``
to delete a single element.
Note that ``erase`` is in the ``Finset`` namespace, but ``insert`` is in the root
namespace.
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (a : ℕ) (h : a ∉ s) : (insert a s |>.erase a) = s :=
  Finset.erase_insert h

example (s : Finset ℕ) (a : ℕ) (h : a ∈ s) : insert a (s.erase a) = s :=
  Finset.insert_erase h
-- QUOTE.

/- TEXT:
In fact, ``{0, 1, 2}`` is just notation for ``insert 0 (insert 1 (singleton 2))``.
EXAMPLES: -/
-- QUOTE:
set_option pp.notation false in
#check ({0, 1, 2} : Finset ℕ)
-- QUOTE.

/- TEXT:
Unfortunately, we cannot use set-builder notation with finsets: we can't write
an expression like ``{ x : ℕ | Even x ∧ x < 5 }`` because Lean can't straightforwardly infer that such a set is finite.
However, you can start with a finset and separate the elements you want using ``Finset.filter``.
EXAMPLES: -/
-- QUOTE:
#check (range n).filter Even
#check (range n).filter (fun x ↦ Even x ∧ x ≠ 3)

example : (range 10).filter Even = {0, 2, 4, 6, 8} := by decide
-- QUOTE.

/- TEXT:
Mathlib knows that the image of a finset under a function is a finset.
EXAMPLES: -/
-- QUOTE:
#check (range 5).image (fun x ↦ x * 2)

example : (range 5).image (fun x ↦ x * 2) = (range 10).filter Even := by decide
-- QUOTE.

/- TEXT:
Lean also knows that the cartesian product ``s ×ˢ t`` of two finsets is a finset,
and that the powerset of a finset is a finset. (Note that the notation ``s ×ˢ t``
also works for sets.)
EXAMPLES: -/
section
variable (s t : Finset Nat)
-- QUOTE:
#check s ×ˢ t
#check s.powerset
-- QUOTE.

end

/- TEXT:
Defining an operation on finsets in terms of their elements is tricky, because any such definition
has to be independent of the order in which the elements are presented.
Of course, you can always define functions by composing existing operations.
Another thing you can do is use ``Finset.fold`` *fold* a binary operation over the
elements, provided that the operation is associative and commutative,
since these properties guarantee that the result is independent of the order that
the operation is applied. Finite sums, products, and unions are defined in that way.
In the last example below, ``biUnion`` stands for "bounded indexed union."
With conventional mathematical notation, the expression would be written
:math:`\bigcup_{i ∈ s} g(i)`.
EXAMPLES: -/
section
-- QUOTE:
#check Finset.fold

def f (n : ℕ) : Int := (↑n)^2

#check (range 5).fold (fun x y : Int ↦ x + y) 0 f
#eval (range 5).fold (fun x y : Int ↦ x + y) 0 f

#check ∑ i ∈ range 5, i^2
#check ∏ i ∈ range 5, i + 1

variable (g : Nat → Finset Int)

#check (range 5).biUnion g
-- QUOTE.

end

/- TEXT:
There is a natural principle of induction on finsets: to prove that every finset
has a property, show that the empty set has the property and that the property is
preserved when we add one new element to a finset. (The ``@`` in ``@insert`` is need
in the induction step to give names to the parameters ``a`` and ``s`` because they
have been marked implicit. )
EXAMPLES: -/
-- QUOTE:
#check Finset.induction

example {α : Type*} [DecidableEq α] (f : α → ℕ)  (s : Finset α) (h : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s anins ih =>
      rw [prod_insert anins]
      apply mul_ne_zero
      · apply h; apply mem_insert_self
      apply ih
      intros x xs
      exact h x (mem_insert_of_mem xs)
-- QUOTE.

/- TEXT:
If ``s`` is a finset, ``Finset.Nonempty s`` is defined to be ``∃ x, x ∈ s``.
You can use classical choice to pick an element of a nonempty finset. Similarly,
the library defines ``Finset.toList s`` which uses choice to pick the elements of
``s`` in some order.
EXAMPLES: -/
-- QUOTE:
noncomputable example (s : Finset ℕ) (h : s.Nonempty) : ℕ := Classical.choose h

example (s : Finset ℕ) (h : s.Nonempty) : Classical.choose h ∈ s :=
   Classical.choose_spec h

noncomputable example (s : Finset ℕ) : List ℕ := s.toList

example (s : Finset ℕ) (a : ℕ) : a ∈ s.toList ↔ a ∈ s := mem_toList
-- QUOTE.

/- TEXT:
You can use ``Finset.min`` and ``Finset.max`` to choose the minimum or maximum element
of a finset of elements of a linear order, and similarly you can use ``Finset.sup``
and ``Finset.max`` with finstes of elements of a lattice, but there is a catch.
What should the minimum element of an empty finset be?
You can check that the primed versions of the functions below add a precondition
that the finset is nonempty.
The non-primed versions ``Finset.min`` and ``Finset.max``
add a top or bottom element, respectively, to handle the case where the finset is empty,
and the non-primed versions ``Finset.inf`` and ``Finset.sup`` assume that
the lattice comes equipped with a top or bottom element, respectively.
EXAMPLES: -/
-- QUOTE:
#check Finset.min
#check Finset.min'
#check Finset.max
#check Finset.max'
#check Finset.inf
#check Finset.inf'
#check Finset.sup
#check Finset.sup'

example : Finset.Nonempty {2, 6, 7} := ⟨6, by trivial⟩
example : Finset.min' {2, 6, 7} ⟨6, by trivial⟩ = 2 := by trivial
-- QUOTE.

/- TEXT:
One of the most important features of finsets is that each one has a finite cardinality.
EXAMPLES: -/
-- BEGIN QUOTE:
#check Finset.card
#eval (range 5).card

example (s : Finset ℕ) : s.card = ∑ i ∈ s, 1 := by
  rw [card_eq_sum_ones]

example (s : Finset ℕ) : s.card = ∑ i ∈ s, 1 := by simp
-- END QUOTE.

/- TEXT:
The next section is all about reasoning about cardinality.

When formalizing mathematics, one often has to make a decision as to whether to express
one's definitions and theorems in terms of sets or types.
Restricting attention to an entire type often simplifies notation and proofs, but working
with subsets of a type can be more flexible.
The type-based analogue of a finset is a *fintype*, that is, a type ``Fintype α`` for some
``α``.
By definition, a fintype is just a data type that comes equipped with a finset ``univ`` that
contains all its elements.
EXAMPLES: -/
section
-- BEGIN QUOTE:
variable {α : Type*} [Fintype α]

example : ∀ x : α, x ∈ Finset.univ := by
  intro x; exact mem_univ x
-- END QUOTE.

/- TEXT:
``Fintype.card α`` is equal to the cardinality of the corresponding finset.
EXAMPLES: -/
-- QUOTE:
example : Fintype.card α = (Finset.univ : Finset α).card := rfl
-- QUOTE.
end

/- TEXT:
We have already seen a prototypical example of a fintype, namely, the types ``Fin n`` for
each ``n``.
But Lean also recognizes that the fintypes are closed under operations like the product operation.
EXAMPLES: -/
-- QUOTE:
example : Fintype.card (Fin 5) = 5 := by simp
example : Fintype.card ((Fin 5) × (Fin 3)) = 15 := by simp
-- QUOTE.

/- TEXT:
Any element ``s`` of ``Finset α`` can be coercied to a type ``(↑s : Finset α)``, namely,
the subtype of elements of ``α`` that are contained in ``s``.
EXAMPLES: -/
section
-- QUOTE:
variable (s : Finset ℕ)

example : (↑s : Type) = {x : ℕ // x ∈ s} := rfl
example : Fintype.card ↑s = s.card := by simp
-- QUOTE.
end

/- TEXT:
Lean and Mathlib use *type class inference* to track the additional structure on fintypes,
namely, the universal finset that contains all the elements.
In other words, you can think of a fintype as an algebraic structure equipped with that
extra data.
Chapter :numref:`Chapter %s <structures>` explains how this works.
EXAMPLES: -/
