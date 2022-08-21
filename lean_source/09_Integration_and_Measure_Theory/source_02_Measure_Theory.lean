import analysis.normed_space.finite_dimension
import analysis.convolution
import measure_theory.function.jacobian
import measure_theory.integral.bochner
import measure_theory.measure.lebesgue

open set filter
open_locale topological_space filter ennreal
noncomputable theory

/- TEXT:
.. index:: measure theory

.. _measure_theory:

Measure theory
--------------

The general context for integration in mathlib is measure theory. Even the elementary
integrals of the previous section are secretely Bochner integrals. Bochner integration is
a generalization of Lebesgue integration where the target space can be any Banach space,
not necessarily finite dimensional.

The first layer is the notion of a :math:`\sigma`-algebra of sets that are "measurable".
Equipping a type with such a structure is the role of the type class ``measurable_space``.
The empty and univ sets are measurable, the complement of a measurable set is measurable,
and a countable union or intersection of measurable sets is measurable (of course these axioms are
redundant). In this context the countability assumption is spelled using ``encodable``.
BOTH: -/

-- QUOTE:
variables {α : Type*} [measurable_space α]


example : measurable_set (∅ : set α) := measurable_set.empty

example : measurable_set (univ : set α) := measurable_set.univ

example {s : set α} (hs : measurable_set s) : measurable_set sᶜ :=
hs.compl

example : encodable ℕ :=
by apply_instance

example (n : ℕ) : encodable (fin n) :=
by apply_instance

variables {ι : Type*} [encodable ι]

example {f : ι → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋃ b, f b) :=
measurable_set.Union h

example {f : ι → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋂ b, f b) :=
measurable_set.Inter h

-- QUOTE.

/- TEXT:
Once a type is measurable we can measure it. On paper, a measure on a type equipped with a
:math:`\sigma`-algebra is a function from measurable sets to extended non-negative reals that is
additive on countable disjoint unions. In mathlib we don't want to carry around measurability assumptions
each time we write an application of the measure to a set. So we extend the measure to any set ``s``
as the infimum of measures of measurable sets containing ``s``. Of course many lemmas still require
measurability assumptions, but not all.

BOTH: -/

-- QUOTE:
open measure_theory

variables {μ : measure α}

example (s : set α) : μ s = ⨅ t (st : s ⊆ t) (ht : measurable_set t), μ t :=
measure_eq_infi s

example  (s : ι → set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
measure_Union_le s

example {f : ℕ → set α} (hmeas : ∀ i, measurable_set (f i)) (hdis : pairwise (disjoint on f)) :
  μ (⋃ i, f i) = ∑' i, μ (f i) :=
μ.m_Union hmeas hdis
-- QUOTE.

/- TEXT:
Measures come with a notion of properties holding almost everywhere. This is of course a special case of what
filters do, but we have a special notation for this.
BOTH: -/

-- QUOTE:
example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in μ.ae, P x :=
iff.rfl
-- QUOTE.
