-- BOTH:
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

/- TEXT:
.. _finite:

Finite types and sets
----

.. index:: finite

Everything we have seen so far applies to all types and sets, without cardinality restriction.
Working with finite types and sets in Lean is surprisingly subtle, for at least two reasons.
First there is a general principle that abstract mathematics is easier to formalize that concrete
ones. This comes in particular from the fact that informal expositions of concrete arguments about
finite structures tend to appeal to intuition a lot, without any actual proof.
More importantly finite mathematical objects often live at the intersection of mathematics and
computer science. Being able to actually compute with a finite object imposes a lot more
constraints. For instance, there is a difference between knowing that a set is finite and having an
enumeration of its elements. Even from a purely mathematical point of view, the computer science
side is useful since it can sometimes be used by Lean to automatically prove some statements.

The fundamental finite type family is `Fin : ℕ → Type`. For any natural number `n`, `Fin n` is
a type having exactly `n` inhabitants. Each of these inhabitants `x` is made of a natural number
`x.val` and a proof `x.isLt` that `x.val < n`.

BOTH: -/

-- QUOTE:
variable (n : ℕ) (x : Fin n)

#check (x.isLt : x.val < n)

-- QUOTE.
#check Finite
/- TEXT:
Using this type family, Mathlib defines the fundamental `Finite` type class. Given a type `α`
an instance of `Finite α` is the statement that there exists some bijection between `α` and
`Fin n` for some unspecified `n`. Since this is a type class, instances can be synthesed from
other instances.

BOTH: -/

-- QUOTE:
variable {α β : Type _} [Finite α] [Finite β]


#synth Finite (α × β)

#synth Finite (α → β)
-- QUOTE.

/- TEXT:
Then `Infinite α` is defined as `¬ Finite α`, and is also a class.

BOTH: -/

-- QUOTE:
variable {γ : Type _} [Infinite γ] [Nonempty α]

#synth Infinite (α → γ)
#synth Infinite (α × γ)
-- QUOTE.

/- TEXT:
Note that `Finite α` has no computational content. For instance defining the cardinal of `α`
as a natural number from the assumption `Finite α` requires the axiom of choice. This is not
an accident. Say for instance we define `α` to be `Fin 0` if the Riemann hypothesis is false and
`Fin 1` otherwise. We can easily prove `Finite α` but any function computing the cardinality of
`α` needs to decide the Riemann hypothesis on the way. Of course one can replace the Riemann
hypothesis with any Gödel-like statement to technically prove there cannont be any such function.
Later we will discuss variations of `Finite` that carry data allowing to perform computations.

We now turn to finite sets. There is a predicate `Set.Finite` that is analogous to `Finite` for
type. It asserts finiteness of a set without recording any data. It is equivalent to saying
that the associated type is finite. Recall the inhabitants of the type associated to `s : Set α`
are made of an inhabitant of `α` and a proof that it belongs to `s`. In the left-hand side of
the statement below, Lean automatically inserts the coercion turning `s` into this type.

BOTH: -/

-- QUOTE:
recall Set.finite_coe_iff {α : Type _} {s : Set α} : Finite s ↔ s.Finite

-- QUOTE.

/- TEXT:
Since `Set.Finite` is not a class, lemmas proving finiteness need to be invoked explicitly.
For instance:
BOTH: -/

-- QUOTE:
recall Set.Finite.prod {α β} {s : Set α} {t : Set β} : Set.Finite s → Set.Finite t →
  Set.Finite (s ×ˢ t)

recall Set.Finite.image {α β} {s : Set α} (f : α → β) : Set.Finite s → Set.Finite (f '' s)

recall Set.Finite.preimage {α β} {s : Set β} {f : α → β} (_ : Set.InjOn f $ f ⁻¹' s) :
Set.Finite s → Set.Finite (f ⁻¹' s)

-- QUOTE.

/- TEXT:
Then `Set.Infinite` is defined to be the negation of `Set.Finite`.

This is all very simple  since none of the notions we've seen so far has any computational content.
We now turn to versions which do carry data allowing some computations. On the set side,
the main player is `Finset`. Given any type `α`, `Finset α` is the type of finite sets of
inhabitants of `α`, with enough data to compute.

-/

#eval Finset.min {5, 3, 7, 8}

#eval Finset.min' {5, 3, 7, 8} ⟨5, by decide⟩

#check Set.Finite
#check Fintype.ofFinite
/-
Ne pas oublier les principes de récurrence sur Finset.
-/
