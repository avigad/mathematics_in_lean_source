import analysis.special_functions.trigonometric.deriv
import analysis.calculus.mean_value


open set filter
open_locale topological_space filter classical real


noncomputable theory

/- TEXT:
.. index:: elementary calculus

.. _elementary_calculus:

Elementary differential calculus
--------------------------------

In this section we only consider derivatives of functions from reals to reals. The most important thing to 
understand is the distinction between claiming that a function has a derivative at some point and referring
to the derivative function.

TEXT. -/

-- QUOTE:
open real

/-- The sin function has derivative 1 at 0. -/
example : has_deriv_at sin 1 0 :=
by simpa using has_deriv_at_sin 0

-- QUOTE.

/- TEXT:
One can simply state that ``f`` is differentiable at some point, without giving its derivative number there.
This uses ``differentiable_at ℝ`` where ``ℝ`` is here so that, in a slightly more general context, we can 
distinguish functions from ``ℂ`` to ``ℂ`` that are differentiable in the real sense or in the complex sense. 

TEXT. -/

-- QUOTE:
example (x : ℝ) : differentiable_at ℝ sin x :=
(has_deriv_at_sin x).differentiable_at
-- QUOTE.

/- TEXT:

It would be extremely unconvenient to require a proof a differentiability floating around each time we want
to write a derivative. So there is some ``deriv f : ℝ → ℝ`` which is defined for any function ``f : ℝ → ℝ``
but is defined to take value ``0`` at any point where ``f`` is not differentiable.

TEXT. -/

-- QUOTE:

example {f : ℝ → ℝ} {x a : ℝ} (h : has_deriv_at f a x) : deriv f x = a :=
h.deriv

example {f : ℝ → ℝ} {x : ℝ} (h : ¬ differentiable_at ℝ f x) : deriv f x = 0 :=
deriv_zero_of_not_differentiable_at h
-- QUOTE.

/- TEXT:
Of course there are many lemmas about ``deriv`` that do require differentiability assumptions.
For instance you should think about a counter-example to the next lemma without differentiability assumption.
TEXT. -/

-- QUOTE:
example {f g : ℝ → ℝ} {x : ℝ} (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) :
  deriv (f + g) x = deriv f x + deriv g x :=
deriv_add hf hg
-- QUOTE.

/- TEXT:
There are however statement who suprisingly do *not* involve this assumption but rather take advantage
of the fact that the value of `deriv` default to zero when there is no derivative.
As usual, reading statements still require to understand the definitions involved.

TEXT. -/

-- QUOTE:
example {f : ℝ → ℝ} {a : ℝ} (h : is_local_min f a) : deriv f a = 0 :=
h.deriv_eq_zero
-- QUOTE.

/- TEXT:
This allows to state Rolle's theorem without any differentiability assumption, which
looks even weirder.

TEXT. -/

-- QUOTE:
example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) 
  (hfc : continuous_on f (Icc a b)) (hfI : f a = f b) :
  ∃ c ∈ Ioo a b, deriv f c = 0 :=
exists_deriv_eq_zero f hab hfc hfI
-- QUOTE.

/- TEXT:
Of course this trick does not work for the general mean value theorem.
TEXT. -/

-- QUOTE:

example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : continuous_on f (Icc a b))
 (hf' : differentiable_on ℝ f (Ioo a b)) : 
 ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
exists_deriv_eq_slope f hab hf hf'


-- QUOTE.

/- TEXT:

Lean can automatically compute some simple derivatives using `simp` tactic.
TEXT. -/

-- QUOTE:
open real

example : deriv (λ x : ℝ, x^5) 6 = 5 * 6^4 := by simp

example (x₀ : ℝ) (h₀ : x₀ ≠ 0) : deriv (λ x:ℝ, 1 / x) x₀ = -(x₀^2)⁻¹ := by simp

example : deriv sin π = -1 := by simp
-- QUOTE.

/- TEXT:
Sometimes you need `ring` and/or `field_simp` after `simp`
TEXT. -/

-- QUOTE:

example (x₀ : ℝ) (h : x₀ ≠ 0) :
  deriv (λ x : ℝ, exp(x^2) / x^5) x₀ = (2 * x₀^2 - 5) * exp (x₀^2) / x₀^6 :=
begin
  have : x₀^5 ≠ 0, { exact pow_ne_zero 5 h, },
  field_simp,
  ring,
end

example (y : ℝ) : has_deriv_at (λ x : ℝ, 2 * x + 5) 2 y :=
begin
  have := ((has_deriv_at_id y).const_mul 2).add_const 5,
  rwa [mul_one] at this,
end

example (y : ℝ) : deriv (λ x : ℝ, 2 * x + 5) y = 2 := by simp

-- QUOTE.
