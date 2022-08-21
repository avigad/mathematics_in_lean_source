.. index:: normed space

.. _normed_spaces:

Differential Calculus in Normed Spaces
--------------------------------------

Normed spaces
^^^^^^^^^^^^^

Differentiation can be generalized beyond ``ℝ`` using the notion of a
*normed vector space*, which encapsulates both direction and distance.
We start with the notion of a *normed group*, which as an additive commutative
group equipped with a real-valued norm function
satisfying the following conditions.

.. code-block:: lean

  variables {E : Type*} [normed_group E]
  
  example (x : E) : 0 ≤ ∥x∥ :=
  norm_nonneg x
  
  example {x : E} : ∥x∥ = 0 ↔ x = 0 :=
  norm_eq_zero
  
  example (x y : E) : ∥x + y∥ ≤ ∥x∥ + ∥y∥ :=
  norm_add_le x y

Every normed space is a metric space with distance function
:math:`d(x, y) = \| x - y \|`, and hence it is also a topological space.
Lean and mathlib know this.

.. code-block:: lean

  example : metric_space E := by apply_instance
  
  example {X : Type*} [topological_space X] {f : X → E} (hf : continuous f) :
    continuous (λ x, ∥f x∥) :=
  hf.norm

In order to use the notion of a norm with concepts from linear algebra,
we add the assumption ``normed_space ℝ E`` on top of ``normed_group E``.
This stipulates that ``E`` is a vector space over ``ℝ`` and that
scalar multiplication satsifies the following condition.

.. code-block:: lean

  variables [normed_space ℝ E]
  
  example (a : ℝ) (x : E) : ∥a • x∥ = |a| * ∥x∥ :=
  norm_smul a x

A complete normed space is known as a *Banach space*.
Every finite-dimensional vector space is complete.

.. code-block:: lean

  example [finite_dimensional ℝ E] : complete_space E :=
  by apply_instance

In all the previous examples, we used the real numbers as the base field.
More generally, we can make sense of calculus with a vector space over any
*non-discrete normed field*. These are fields that are equipped with a
real-valued norm that is multiplicative and has the property that
not every element has norm zero or one
(equivalently, there is an element whose norm is bigger than one).

.. code-block:: lean

  example (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (x y : 𝕜) : ∥x * y∥ = ∥x∥ * ∥y∥ :=
  norm_mul x y
  
  example (𝕜 : Type*) [nondiscrete_normed_field 𝕜] : ∃ x : 𝕜, 1 < ∥x∥ :=
  normed_field.exists_one_lt_norm 𝕜

A finite-dimensional vector space over a nondiscrete normed field is
complete as long as the field itself is complete.

.. code-block:: lean

  example (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (E : Type*) [normed_group E]
    [normed_space 𝕜 E] [complete_space 𝕜] [finite_dimensional 𝕜 E] : complete_space E :=
  finite_dimensional.complete 𝕜 E

Continuous linear maps
^^^^^^^^^^^^^^^^^^^^^^

We now turn to the morphisms in the category of normed spaces, namely,
continuous linear maps.
In mathlib, the type of ``𝕜``-linear continuous maps between normed spaces
``E`` and ``F`` is written ``E →L[𝕜] F``.
They are implemented as *bundled maps*, which means that an element of this type
a structure that that includes the function itself and the properties
of being linear and continuous.
Lean will insert a coercion so that a continuous linear map can be treated
as a function.

.. code-block:: lean

  variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
            {E : Type*} [normed_group E] [normed_space 𝕜 E]
            {F : Type*} [normed_group F] [normed_space 𝕜 F]
  
  example : E →L[𝕜] E := continuous_linear_map.id 𝕜 E
  
  example (f : E →L[𝕜] F) : E → F :=
  f
  
  example (f : E →L[𝕜] F) : continuous f :=
  f.cont
  
  example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
  f.map_add x y
  
  example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
  f.map_smul a x

Continuous linear maps have an operator norm that is characterized by the
following properties.

.. code-block:: lean

  variables (f : E →L[𝕜] F)
  
  example (x : E) : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
  f.le_op_norm x
  
  example {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
    ∥f∥ ≤ M :=
  f.op_norm_le_bound hMp hM

There is also a notion of bundled continuous linear *isomorphism*.
Their type of such isomorphisms is ``E ≃L[𝕜] F``.

As a challenging exercise, you can prove the Banach-Steinhaus theorem, also
known as the Uniform Boundedness Principle.
The principle states that a family of continuous linear maps from a Banach space
into a normed space is pointwise
bounded, then the norms of these linear maps are uniformly bounded.
The main ingredient is Baire's theorem
``nonempty_interior_of_Union_of_closed.`` (You proved a version of this in the topology chapter.)
Minor ingredients include ``continuous_linear_map.op_norm_le_of_shell``,
``interior_subset`` and ``interior_Inter_subset`` and ``is_closed_le``.

.. code-block:: lean

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
    /- apply the Baire category theorem to conclude that for some `m : ℕ`,
       `e m` contains some `x` -/
    obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry,
    obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry,
    obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ∥k∥ := sorry,
    /- show all elements in the ball have norm bounded by `m` after applying any `g i` -/
    have real_norm_le : ∀ (z ∈ ball x ε) (i : ι), ∥g i z∥ ≤ m,
    sorry,
    have εk_pos : 0 < ε / ∥k∥ := sorry,
    refine ⟨(m + m : ℕ) / (ε / ∥k∥),
             λ i, continuous_linear_map.op_norm_le_of_shell ε_pos _ hk _⟩,
    sorry,
    sorry
  end

Asymptotic comparisons
^^^^^^^^^^^^^^^^^^^^^^

Defining differentiability also requires asymptotic comparisons.
Mathlib has an extensive library covering the big O and little o relations,
whose definitions are shown below.
Opening the ``asymptotics`` locale allows us to use the corresponding
notation.
Here we will only use little o to define differentiability.

.. code-block:: lean

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

Differentiability
^^^^^^^^^^^^^^^^^

We are now ready to discuss differentiable functions between normed spaces.
In analogy the elementary one-dimensional,
mathlib defines a predicate ``has_fderiv_at`` and a function ``fderiv``.
Here the letter
"f" stands for *Fréchet*.

.. code-block:: lean

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

We also have iterated derivatives that take values in the type of multilinear maps
``E [×n]→L[𝕜] F``,
and we have continuously differential functions.
The type ``with_top ℕ`` is ``ℕ`` with an additional element ``⊤`` that
is bigger than every natural number.
So :math:`\mathcal{C}^\infty` functions are functions ``f`` that satisfy
``cont_diff 𝕜 ⊤ f``.

.. code-block:: lean

  example (n : ℕ) (f : E → F) : E → (E [×n]→L[𝕜] F) :=
  iterated_fderiv 𝕜 n f
  
  example (n : with_top ℕ) {f : E → F} :
    cont_diff 𝕜 n f ↔
      (∀ (m : ℕ), (m : with_top ℕ) ≤ n → continuous (λ x, iterated_fderiv 𝕜 m f x))
    ∧ (∀ (m : ℕ), (m : with_top ℕ) < n → differentiable 𝕜 (λ x, iterated_fderiv 𝕜 m f x)) :=
  cont_diff_iff_continuous_differentiable

There is a stricter notion of differentiability called
``has_strict_fderiv_at``, which is used in the statement
of the inverse function theorem and the statement of the implicit function
theorem, both of which are in mathlib.
Over ``ℝ`` or ``ℂ``, continuously differentiable
functions are strictly differentiable.

.. code-block:: lean

  example {𝕂 : Type*} [is_R_or_C 𝕂] {E : Type*} [normed_group E] [normed_space 𝕂 E]
    {F : Type*} [normed_group F] [normed_space 𝕂 F]
    {f : E → F} {x : E} {n : with_top ℕ}
    (hf : cont_diff_at 𝕂 n f x) (hn : 1 ≤ n) :
    has_strict_fderiv_at f (fderiv 𝕂 f x) x :=
  hf.has_strict_fderiv_at hn

The local inverse theorem is stated using an operation that produces an
inverse function from a
function and the assumptions that the function is strictly differentiable at a
point ``a`` and that its derivative is an isomorphism.

The first example below gets this local inverse.
The next one states that it is indeed a local inverse
from the left and from the right, and that it is strictly differentiable.

.. code-block:: lean

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
  
  example [complete_space E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
      (hf : has_strict_fderiv_at f ↑f' a) :
    has_strict_fderiv_at (has_strict_fderiv_at.local_inverse f f' a hf)
      (f'.symm : F →L[𝕜] E) (f a) :=
  has_strict_fderiv_at.to_local_inverse hf
  
  end local_inverse

This has been only a quick tour of the differential calculus in mathlib.
The library contains many variations that we have not discussed.
For example, you may want to use one-sided derivatives in the
one-dimensional setting. The means to do so are found in mathlib in a more
general context;
see ``has_fderiv_within_at`` or the even more general ``has_fderiv_at_filter``.
