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
TEXT. -/

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

TEXT. -/

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
TEXT. -/

-- QUOTE:
example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in μ.ae, P x :=
iff.rfl
-- QUOTE.

/- TEXT:
Integration
-----------

Now that we have measurable spaces and measures we can consider integrals. As explained above, the very general
integration that we use allow any Banach space as the target. As usual we don't want our notation to 
carry around assumptions so we can always write an integral and it will be zero if the function is not integrable.
And of course most lemmas do have integrability assumptions.


TEXT. -/

-- QUOTE:
section

variables {E : Type*} [normed_group E] [normed_space ℝ E] [complete_space E]
  {f : α → E}

example {f g : α → E} (hf : integrable f μ) (hg : integrable g μ) : 
  ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
integral_add hf hg

-- QUOTE.

/- TEXT:
As an example of a complicated interaction between our various conventions, let us see how to integrate constant functions.
Recall that ``μ`` takes values in ``ℝ≥0∞``, the type of extended non-negative reals. There is a function
``ennreal.to_real : ℝ≥0∞ → ℝ`` which sends ``⊤``, the point at infinity, to zero. 
For any ``s : set α``, if ``μ s = ⊤`` then constant functions are not integrable so their integral
is zero by definition, and so is ``(μ s).to_real``. So in all cases we have the following lemma.
TEXT. -/


-- QUOTE:

example {s : set α} (c : E) :
  ∫ x in s, c ∂μ = (μ s).to_real • c :=
set_integral_const c

-- QUOTE.

/- TEXT:
We now quickly review how to access the most important theorems in integration theory, starting
with the dominated convergence theorem. There are several versions, we only show the most basic one.
TEXT. -/

-- QUOTE:
example {F : ℕ → α → E} {f : α → E} (bound : α → ℝ)
  (hmeas : ∀ n, ae_strongly_measurable (F n) μ) 
  (hint : integrable bound μ)
  (hbound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (hlim : ∀ᵐ a ∂μ, tendsto (λ (n : ℕ), F n a) at_top (𝓝 (f a))) :
  tendsto (λ n, ∫ a, F n a ∂μ) at_top (𝓝 (∫ a, f a ∂μ)) :=
tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim

-- QUOTE.

/- TEXT:
Then we have Fubini's theorem for integrals on product type.

TEXT. -/

-- QUOTE:
example
  {α : Type*} [measurable_space α] 
  {μ : measure α} [sigma_finite μ] 
  {β : Type*} [measurable_space β] {ν : measure β} [sigma_finite ν]  
  (f : α × β → E) (hf : integrable f (μ.prod ν)) :
  ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
integral_prod f hf

-- QUOTE.
end

/- TEXT:
There is a very general version of convolution using any continuous bilinear form.

TEXT. -/

section
-- QUOTE:
open_locale convolution

variables {𝕜 : Type*} {G : Type*} {E : Type*} {E' : Type*} {F : Type*} [normed_group E]
  [normed_group E'] [normed_group F] [nondiscrete_normed_field 𝕜]
  [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 F]
  [measurable_space G] [normed_space ℝ F] [complete_space F] [has_sub G]

example (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F) (μ : measure G) : 
  f ⋆[L, μ] g = λ x, ∫ t, L (f t) (g (x - t)) ∂μ := 
rfl

-- QUOTE.

end
/- TEXT:
And finally we have a very general version of the change of variables formula. In the statement below,
``borel_space E`` means the :math:`\sigma`-algebra on ``E`` is generated by open sets.
And ``is_add_haar_measure μ`` means ``μ`` is left-invariant and gives
finite mass to compact sets and positive mass to open sets.
TEXT. -/

-- QUOTE:


example {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]  
  [measurable_space E] [borel_space E] (μ : measure E) [μ.is_add_haar_measure]
  {F : Type*}[normed_group F] [normed_space ℝ F] [complete_space F]
  {s : set E} {f : E → E} {f' : E → (E →L[ℝ] E)}  
  (hs : measurable_set s) 
  (hf : ∀ (x : E), x ∈ s → has_fderiv_within_at f (f' x) s x) 
  (h_inj : inj_on f s)
  (g : E → F) : 
  ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ :=
integral_image_eq_integral_abs_det_fderiv_smul μ hs hf h_inj g

-- QUOTE.
