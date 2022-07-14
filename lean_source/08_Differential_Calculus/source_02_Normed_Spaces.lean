import analysis.normed_space.banach_steinhaus
import analysis.normed_space.finite_dimension

import analysis.calculus.inverse

open set filter
open_locale topological_space filter

noncomputable theory

/- TEXT:
.. index:: normed space

.. _normed_spaces:

Differential calculus in normed spaces
--------------------------------------

Normed spaces
^^^^^^^^^^^^^

In order to level-up from calculus on ``ℝ``, we need the context of normed vector spaces.
The first stage is normed groups, ie additive commutative groups equipped with a real-valued
norm function satisfying the following conditions. 
TEXT. -/
section
-- QUOTE:
variables {E : Type*} [normed_group E] 

example (x : E) : 0 ≤ ∥x∥ := 
norm_nonneg x

example {x : E} : ∥x∥ = 0 ↔ x = 0 := 
norm_eq_zero

example (x y : E) : ∥x + y∥ ≤ ∥x∥ + ∥y∥ :=
norm_add_le x y

-- QUOTE.

/- TEXT:
This is already connected to the topology library that was discussed in the topology chapter.

TEXT. -/

-- QUOTE:
example : metric_space E := by apply_instance

example {X : Type*} [topological_space X] {f : X → E} (hf : continuous f) : continuous (λ x, ∥f x∥) :=
hf.norm
-- QUOTE.

/- TEXT:
In order to connect normed groups to linear algebra, we add a ``normed_space``
instance assumption on top of the ``normed_group`` one. In addition to having a vector
space structure, this puts a condition relating the scalar action with the norm.
TEXT. -/

-- QUOTE:
variables [normed_space ℝ E] 

example (a : ℝ) (x : E) : ∥a • x∥ = |a| * ∥x∥ :=
norm_smul a x
-- QUOTE.

/- TEXT:
In case of finite dimensional vector spaces, we get completeness for free.
TEXT. -/

-- QUOTE:
example [finite_dimensional ℝ E]: complete_space E :=
by apply_instance


-- QUOTE.

/- TEXT:
In all the previous example we used real numbers as the base field, but the general context 
for calculus is vector spaces over non-discrete normed fields. They are fields equipped with a real
valued norm which is multiplicative and such that not every element has norm zero or one
(equivalently there is an element whose norm is bigger than one).

TEXT. -/

-- QUOTE:
example (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (x y : 𝕜) : ∥x * y∥ = ∥x∥ * ∥y∥ :=
norm_mul x y

example (𝕜 : Type*) [nondiscrete_normed_field 𝕜] : ∃ x : 𝕜, 1 < ∥x∥ :=
normed_field.exists_one_lt_norm 𝕜
-- QUOTE.

/- TEXT:
Completeness of finite dimensional vector spaces hold in this context as long as the base field is complete.
TEXT. -/

-- QUOTE:
example (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (E : Type*) [normed_group E]
  [normed_space 𝕜 E] [complete_space 𝕜] [finite_dimensional 𝕜 E] : complete_space E :=
finite_dimensional.complete 𝕜 E

-- QUOTE.
end
/- TEXT:
Continuous linear maps
^^^^^^^^^^^^^^^^^^^^^^

We now turn to morphisms in the category of normed spaces: continuous linear maps.
These are implemented as bundled maps with notation ``E →L[𝕜] F``.
TEXT. -/
section
-- QUOTE:
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
          {E : Type*} [normed_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_group F] [normed_space 𝕜 F]

example : E →L[𝕜] E := continuous_linear_map.id 𝕜 E

example (f : E →L[𝕜] F) : continuous f := 
f.cont
-- QUOTE.

/- TEXT:
Continuous linear maps have an operator norm characterized by the following properties.
TEXT. -/

-- QUOTE:
variables (f : E →L[𝕜] F)

example (x : E) : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
f.le_op_norm x

example {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M :=
f.op_norm_le_bound hMp hM
-- QUOTE.
end
/- TEXT:
There is also a notion of bundled continuous linear *isomorphism*. Their type is ``E ≃L[𝕜] F``.

As a challenging exercise, you can prove the Banach-Steinhaus theorem, or Uniform Boundedness Principle.
If a family of continuous linear maps from a Banach space into a normed space is pointwise
bounded, then the norms of these linear maps are uniformly bounded. The main ingredient is Baire's theorem
``nonempty_interior_of_Union_of_closed`` (you proved a version of this in the topology chapter).
Minor ingredients include ``continuous_linear_map.op_norm_le_of_shell``, ``interior_subset`` and
``interior_Inter_subset`` and ``is_closed_le``. 

TEXT. -/


-- QUOTE:
section
variables
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜] 
  {E : Type*} [normed_group E] [normed_space 𝕜 E] 
  {F : Type*} [normed_group F] [normed_space 𝕜 F] 

open metric

example {ι : Type*} [complete_space E] {g : ι → E →L[𝕜] F}
  (h : ∀ x, ∃ C, ∀ i, ∥g i x∥ ≤ C) :
  ∃ C', ∀ i, ∥g i∥ ≤ C' :=
begin
  /- sequence of subsets consisting of those `x : E` with norms `∥g i x∥` bounded by `n` -/
  let e : ℕ → set E := λ n, ⋂ i : ι, { x : E | ∥g i x∥ ≤ n },
  /- each of these sets is closed -/
  have hc : ∀ n : ℕ, is_closed (e n), 
  sorry, 
  /- the union is the entire space; this is where we use `h` -/
  have hU : (⋃ n : ℕ, e n) = univ,
  sorry,
  /- apply the Baire category theorem to conclude that for some `m : ℕ`, `e m` contains some `x` -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry,
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry,
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ∥k∥ := sorry,
  /- show all elements in the ball have norm bounded by `m` after applying any `g i` -/
  have real_norm_le : ∀ (z ∈ ball x ε) (i : ι), ∥g i z∥ ≤ m,
  sorry,
  have εk_pos : 0 < ε / ∥k∥ := sorry,
  refine ⟨(m + m : ℕ) / (ε / ∥k∥), λ i, continuous_linear_map.op_norm_le_of_shell ε_pos _ hk _⟩,
  sorry,
  sorry
end
-- QUOTE.
-- SOLUTIONS:

example {ι : Type*} [complete_space E] {g : ι → E →L[𝕜] F}
  (h : ∀ x, ∃ C, ∀ i, ∥g i x∥ ≤ C) :
  ∃ C', ∀ i, ∥g i∥ ≤ C' :=
begin
  /- sequence of subsets consisting of those `x : E` with norms `∥g i x∥` bounded by `n` -/
  let e : ℕ → set E := λ n, ⋂ i : ι, { x : E | ∥g i x∥ ≤ n },
  /- each of these sets is closed -/
  have hc : ∀ n : ℕ, is_closed (e n), 
  from λ i, is_closed_Inter (λ i, is_closed_le (g i).cont.norm continuous_const),
  /- the union is the entire space; this is where we use `h` -/
  have hU : (⋃ n : ℕ, e n) = univ,
  { refine eq_univ_of_forall (λ x, _),
    cases h x with C hC,
    obtain ⟨m, hm⟩ := exists_nat_ge C,
    exact ⟨e m, mem_range_self m, mem_Inter.mpr (λ i, le_trans (hC i) hm)⟩ },
  /- apply the Baire category theorem to conclude that for some `m : ℕ`, `e m` contains some `x` -/
  obtain ⟨m : ℕ, x : E, hx : x ∈ interior (e m)⟩ := nonempty_interior_of_Union_of_closed hc hU,
  obtain ⟨ε, ε_pos, hε : ball x ε ⊆ interior (e m)⟩ := is_open_iff.mp is_open_interior x hx,
  obtain ⟨k : 𝕜, hk : 1 < ∥k∥⟩ := normed_field.exists_one_lt_norm 𝕜,
  /- show all elements in the ball have norm bounded by `m` after applying any `g i` -/
  have real_norm_le : ∀ (z ∈ ball x ε) (i : ι), ∥g i z∥ ≤ m,
  { intros z hz i,
    replace hz := mem_Inter.mp (interior_Inter_subset _ (hε hz)) i,
    apply interior_subset hz },
  have εk_pos : 0 < ε / ∥k∥ := div_pos ε_pos (zero_lt_one.trans hk),
  refine ⟨(m + m : ℕ) / (ε / ∥k∥), λ i, continuous_linear_map.op_norm_le_of_shell ε_pos _ hk _⟩,
  { exact div_nonneg (nat.cast_nonneg _) εk_pos.le },
  intros y le_y y_lt,
  calc ∥g i y∥
      = ∥g i (y + x) - g i x∥   : by rw [(g i).map_add, add_sub_cancel]
  ... ≤ ∥g i (y + x)∥ + ∥g i x∥ : norm_sub_le _ _
  ... ≤ m + m : add_le_add (real_norm_le (y + x) (by rwa [add_comm, add_mem_ball_iff_norm]) i)
          (real_norm_le x (mem_ball_self ε_pos) i)
  ... = (m + m : ℕ) : by norm_cast
  ... ≤ (m + m : ℕ) * (∥y∥ / (ε / ∥k∥))
      : le_mul_of_one_le_right (nat.cast_nonneg _)
          ((one_le_div $ div_pos ε_pos (zero_lt_one.trans hk)).2 le_y)
  ... = (m + m : ℕ) / (ε / ∥k∥) * ∥y∥ : (mul_comm_div _ _ _).symm,
end
-- BOTH:
end
-- BOTH.

/- TEXT:
Asymptotic comparisons
^^^^^^^^^^^^^^^^^^^^^^

The remaining missing piece in order to define differentiability is asymptotics comparisons.
These are the big O, little o, and equivalent relations. The definitions and notations are shown below.
They all have extensive libraries of lemmas, but here we will only use little o to define differentiability.

TEXT. -/

-- QUOTE:
open asymptotics
open_locale asymptotics

example {α : Type*} {E : Type*} [normed_group E] {F : Type*} [normed_group F]
  (c : ℝ) (l : filter α) (f : α → E) (g : α → F) : 
  is_O_with c l f g ↔ ∀ᶠ x in l, ∥ f x ∥ ≤ c * ∥ g x ∥ :=
is_O_with_iff

example {α : Type*} {E : Type*} [normed_group E] {F : Type*} [normed_group F]
  (c : ℝ) (l : filter α) (f : α → E) (g : α → F) : 
  f =O[l] g ↔ ∃ C, is_O_with C l f g :=
is_O_iff_is_O_with

example {α : Type*} {E : Type*} [normed_group E] {F : Type*} [normed_group F]
  (c : ℝ) (l : filter α) (f : α → E) (g : α → F) : 
  f =o[l] g ↔ ∀ C > 0, is_O_with C l f g :=
is_o_iff_forall_is_O_with

example {α : Type*} {E : Type*} [normed_group E] (c : ℝ) (l : filter α) (f g : α → E) : 
  f ~[l] g ↔ (f - g) =o[l] g :=
iff.rfl
-- QUOTE.

/- TEXT:

Differentiability
^^^^^^^^^^^^^^^^^

We are now ready to discuss differentiable functions between normed spaces. As in the elementary
one-dimensional case, there is a predicate ``has_fderiv_at`` and a function ``fderiv``. Here the letter
f stands for Fréchet.
TEXT. -/
section
-- QUOTE:
variables
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜] 
  {E : Type*} [normed_group E] [normed_space 𝕜 E] 
  {F : Type*} [normed_group F] [normed_space 𝕜 F] 

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
  has_fderiv_at f f' x₀ ↔ (λ x, f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] (λ x, x - x₀) :=
iff.rfl

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : has_fderiv_at f f' x₀) : 
  fderiv 𝕜 f x₀ = f' :=
hff'.fderiv

-- QUOTE.

/- TEXT:

We also have iterated derivatives that take values in the type of multilinear maps ``E [×n]→L[𝕜] F``, and
continuously differential functions. The type ``with_top ℕ`` is ``ℕ`` with an additional element ``⊤`` that 
is bigger than every natural number. So :math:`\mathcal{C}^\infty` functions are functions ``f`` that satisfy
``cont_diff 𝕜 ⊤ f``.

TEXT. -/

-- QUOTE:

example (n : ℕ) (f : E → F) : E → (E [×n]→L[𝕜] F) := 
iterated_fderiv 𝕜 n f
  
example (n : with_top ℕ) {f : E → F} : 
  cont_diff 𝕜 n f ↔
    (∀ (m : ℕ), (m : with_top ℕ) ≤ n → continuous (λ x, iterated_fderiv 𝕜 m f x))
  ∧ (∀ (m : ℕ), (m : with_top ℕ) < n → differentiable 𝕜 (λ x, iterated_fderiv 𝕜 m f x)) :=
cont_diff_iff_continuous_differentiable
-- QUOTE.

/- TEXT:

There is a stricter notion of differentiability called ``has_strict_fderiv_at`` which enters the statement
of the inverse function theorem and the implicit function theorem (both those theorems are in mathlib). 
The important thing to know in ordinary contexts is that over ``ℝ`` or ``ℂ``, continuously differentiable 
functions are strictly differentiable.
TEXT. -/

-- QUOTE:
example {𝕂 : Type*} [is_R_or_C 𝕂] {E : Type*} [normed_group E] [normed_space 𝕂 E] 
  {F : Type*} [normed_group F] [normed_space 𝕂 F]
  {f : E → F} {x : E} {n : with_top ℕ}
  (hf : cont_diff_at 𝕂 n f x) (hn : 1 ≤ n) :
  has_strict_fderiv_at f (fderiv 𝕂 f x) x :=
hf.has_strict_fderiv_at hn
-- QUOTE.

/- TEXT: 
The local inverse theorem is stated using a function that produce an inverse function from a
function and the assumptions that it is strictly differentiable at a point ``a`` and its differential is an isomorphism.

The first example below gets this local inverse, then the next one state that it is indeed a local inverse 
from the left and from the right and is strictly differentiable.
TEXT. -/


-- QUOTE:
section local_inverse

variables [complete_space E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

example (hf : has_strict_fderiv_at f ↑f' a) : F → E := 
has_strict_fderiv_at.local_inverse f f' a hf

example  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∀ᶠ x in 𝓝 a, hf.local_inverse f f' a (f x) = x := 
hf.eventually_left_inverse

example  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∀ᶠ x in 𝓝 (f a), f (hf.local_inverse f f' a x) = x := 
hf.eventually_right_inverse

example [complete_space E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E} (hf : has_strict_fderiv_at f ↑f' a) :
  has_strict_fderiv_at (has_strict_fderiv_at.local_inverse f f' a hf) (f'.symm : F →L[𝕜] E) (f a) :=
has_strict_fderiv_at.to_local_inverse hf

end local_inverse
-- QUOTE.

/- TEXT:
At the end of this very short tour of calculus in mathlib, we should also point out that there
are many variations that we haven't discuss. For instance you may want to discuss one-sided 
derivatives in the one-dimensional context. This is all in mathlib in a very general context,
see ``has_fderiv_within_at`` or the even more general ``has_fderiv_at_filter``.

TEXT. -/
#check has_fderiv_within_at
#check has_fderiv_at_filter
end