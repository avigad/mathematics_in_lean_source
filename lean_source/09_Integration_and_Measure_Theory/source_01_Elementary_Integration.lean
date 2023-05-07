import measure_theory.integral.interval_integral
import analysis.special_functions.integrals
import analysis.convolution

open set filter
open_locale topology filter

noncomputable theory

/- TEXT:
.. index:: integration

.. _elementary_integration:

Elementary Integration
----------------------

We first focus on integration of functions on finite intervals in ``ℝ``. We can integrate
elementary functions.
EXAMPLES: -/
-- QUOTE:
open measure_theory interval_integral
open_locale interval  -- this introduces the notation [a, b]

example (a b : ℝ): ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 :=
integral_id

example {a b : ℝ}  (h : (0:ℝ) ∉ [a, b]) : ∫ x in a..b, 1/x = real.log (b / a) :=
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
example (f : ℝ → ℝ) (hf : continuous f) (a b : ℝ) :
  deriv (λ u, ∫ (x : ℝ) in a..u, f x) b = f b :=
(integral_has_strict_deriv_at_right
    (hf.interval_integrable _ _) (hf.strongly_measurable_at_filter _ _)
  hf.continuous_at).has_deriv_at.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ}
  (h : ∀ x ∈ [a, b], has_deriv_at f (f' x) x) (h' : interval_integrable f' volume a b) :
  ∫ y in a..b, f' y = f b - f a :=
integral_eq_sub_of_has_deriv_at h h'
-- QUOTE.

/- TEXT:
Convolution is also defined in mathlib and its basic properties are proved.
EXAMPLES: -/

-- QUOTE:
open_locale convolution

example  (f : ℝ → ℝ) (g : ℝ → ℝ) :
  f ⋆ g = λ x, ∫ t, (f t) * (g (x - t)) :=
rfl
-- QUOTE.