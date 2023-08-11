import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

noncomputable section

/- TEXT:
.. index:: measure theory

.. _measure_theory:

Measure Theory
--------------

The general context for integration in mathlib is measure theory. Even the elementary
integrals of the previous section are in fact Bochner integrals. Bochner integration is
a generalization of Lebesgue integration where the target space can be any Banach space,
not necessarily finite dimensional.

The first component in the development of measure theory
is the notion of a :math:`\sigma`-algebra of sets, which are called the
*measurable* sets.
The type class ``MeasurableSpace`` serves to equip a type with such a structure.
The sets ``empty`` and ``univ`` are measurable,
the complement of a measurable set is measurable,
and a countable union or intersection of measurable sets is measurable.
Note that these axioms are redundant; if you ``#print MeasurableSpace``,
you will see the ones that mathlib uses.
As the examples below show, countability assumptions can be expressed using the
``Encodable`` type class.
BOTH: -/
-- QUOTE:
variable {α : Type*} [MeasurableSpace α]

-- EXAMPLES:
example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example : Encodable ℕ := by infer_instance

example (n : ℕ) : Encodable (Fin n) := by infer_instance

-- BOTH:
variable {ι : Type*} [Encodable ι]

-- EXAMPLES:
example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h
-- QUOTE.

/- TEXT:
Once a type is measurable, we can measure it. On paper, a measure on a set
(or type) equipped with a
:math:`\sigma`-algebra is a function from the measurable sets to
the extended non-negative reals that is
additive on countable disjoint unions.
In mathlib, we don't want to carry around measurability assumptions
every time we write an application of the measure to a set.
So we extend the measure to any set ``s``
as the infimum of measures of measurable sets containing ``s``.
Of course, many lemmas still require
measurability assumptions, but not all.
BOTH: -/
-- QUOTE:
open MeasureTheory
variable {μ : Measure α}

-- EXAMPLES:
example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis
-- QUOTE.

/- TEXT:
Once a type has a measure associated with it, we say that a property ``P``
holds *almost everywhere* if the set of elements where the property fails
has measure 0.
The collection of properties that hold almost everywhere form a filter,
but mathlib introduces special notation for saying that a property holds
almost everywhere.
EXAMPLES: -/
-- QUOTE:
example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in μ.ae, P x :=
  Iff.rfl
-- QUOTE.
