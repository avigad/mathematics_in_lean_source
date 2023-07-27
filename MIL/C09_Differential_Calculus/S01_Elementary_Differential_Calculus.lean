import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter
open Topology Filter Classical Real

noncomputable section

/- TEXT:
.. index:: elementary calculus

.. _elementary_differential_calculus:

Elementary Differential Calculus
--------------------------------

Let ``f`` be a function from the reals to the reals. There is a difference
between talking about the derivative of ``f`` at a single point and
talking about the derivative function.
In mathlib, the first notion is represented as follows.
EXAMPLES: -/
-- QUOTE:
open Real

/-- The sin function has derivative 1 at 0. -/
example : HasDerivAt sin 1 0 := by simpa using hasDerivAt_sin 0
-- QUOTE.

/- TEXT:
We can also express that ``f`` is differentiable at a point without
specifying its derivative there
by writing ``DifferentiableAt ℝ``.
We specify ``ℝ`` explicitly because in a slightly more general context,
when talking about functions from ``ℂ`` to ``ℂ``,
we want to be able to distinguish between being differentiable in the real sense
and being differentiable in the sense of the complex derivative.
EXAMPLES: -/
-- QUOTE:
example (x : ℝ) : DifferentiableAt ℝ sin x :=
  (hasDerivAt_sin x).differentiableAt
-- QUOTE.

/- TEXT:
It would be inconvenient to have to provide a proof of differentiability
every time we want to refer to a derivative.
So mathlib provides a function ``deriv f : ℝ → ℝ`` that is defined for any
function ``f : ℝ → ℝ``
but is defined to take the value ``0`` at any point where ``f`` is not differentiable.
EXAMPLES: -/
-- QUOTE:
example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) : deriv f x = a :=
  h.deriv

example {f : ℝ → ℝ} {x : ℝ} (h : ¬DifferentiableAt ℝ f x) : deriv f x = 0 :=
  deriv_zero_of_not_differentiableAt h
-- QUOTE.

/- TEXT:
Of course there are many lemmas about ``deriv`` that do require differentiability assumptions.
For instance, you should think about a counterexample to the next lemma without the
differentiability assumptions.
EXAMPLES: -/
-- QUOTE:
example {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  deriv_add hf hg
-- QUOTE.

/- TEXT:
Interestingly, however, there are statements that can avoid differentiability
assumptions by taking advantage
of the fact that the value of ``deriv`` defaults to zero when the function is
not differentiable.
So making sense of the following statement requires knowing the precise
definition of ``deriv``.
EXAMPLES: -/
-- QUOTE:
example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 :=
  h.deriv_eq_zero
-- QUOTE.

/- TEXT:
We can even state Rolle's theorem without any differentiability assumptions, which
seems even weirder.
EXAMPLES: -/
-- QUOTE:
open Set

example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI
-- QUOTE.

/- TEXT:
Of course, this trick does not work for the general mean value theorem.
EXAMPLES: -/
-- QUOTE:
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'
-- QUOTE.

/- TEXT:
Lean can automatically compute some simple derivatives using the ``simp`` tactic.
EXAMPLES: -/
-- QUOTE:
example : deriv (fun x : ℝ ↦ x ^ 5) 6 = 5 * 6 ^ 4 := by simp

example : deriv sin π = -1 := by simp
-- QUOTE.
