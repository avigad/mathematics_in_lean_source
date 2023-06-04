import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution

open Set Filter

open Topology Filter

noncomputable section

/- TEXT:
.. index:: integration

.. _elementary_integration:

Elementary Integration
----------------------

We first focus on integration of functions on finite intervals in ``ℝ``. We can integrate
elementary functions.
EXAMPLES: -/
-- QUOTE:
open MeasureTheory intervalIntegral

open Interval

-- this introduces the notation [a, b]
example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example {a b : ℝ} (h : (0 : ℝ) ∉ [a, b]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
  integral_one_div h
-- QUOTE.

/- TEXT:
The fundamental theorem of calculus relates integration and differentiation.
Below we give simplified statements of the two parts of this theorem. The first part
says that integration provides an inverse to differentiation and the second one
specifies how to compute integrals of derivatives.
(These two parts are very closely related, but their optimal versions,
which are not shown here, are not equivalent.)
EXAMPLES: -/
-- QUOTE:
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : deriv (fun u => ∫ x : ℝ in a..u, f x) b = f b :=
  (integral_hasStrictDerivAt_right (hf.IntervalIntegrable _ _) (hf.StronglyMeasurableAtFilter _ _)
        hf.ContinuousAt).HasDerivAt.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [a, b], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'
-- QUOTE.

/- TEXT:
Convolution is also defined in mathlib and its basic properties are proved.
EXAMPLES: -/
-- QUOTE:
open convolution

example (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x => ∫ t, f t * g (x - t) :=
  rfl
-- QUOTE.

