import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Analysis.NormedSpace.FiniteDimension
-- import Mathlib.Analysis.Calculus.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Prod


open Set Filter

open Topology Filter

noncomputable section

/- TEXT:
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
EXAMPLES: -/
section

-- QUOTE:
variable {E : Type _} [NormedAddCommGroup E]

example (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x

example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y
-- QUOTE.

/- TEXT:
Every normed space is a metric space with distance function
:math:`d(x, y) = \| x - y \|`, and hence it is also a topological space.
Lean and mathlib know this.
EXAMPLES: -/
-- QUOTE:
example : MetricSpace E := by infer_instance

example {X : Type _} [TopologicalSpace X] {f : X → E} (hf : Continuous f) :
    Continuous fun x => ‖f x‖ :=
  hf.norm
-- QUOTE.

/- TEXT:
In order to use the notion of a norm with concepts from linear algebra,
we add the assumption ``normed_space ℝ E`` on top of ``normed_add_group E``.
This stipulates that ``E`` is a vector space over ``ℝ`` and that
scalar multiplication satisfies the following condition.
EXAMPLES: -/
-- QUOTE:
variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  norm_smul a x
-- QUOTE.

/- TEXT:
A complete normed space is known as a *Banach space*.
Every finite-dimensional vector space is complete.
EXAMPLES: -/
-- QUOTE:
example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance
-- QUOTE.

/- TEXT:
In all the previous examples, we used the real numbers as the base field.
More generally, we can make sense of calculus with a vector space over any
*non-discrete normed field*. These are fields that are equipped with a
real-valued norm that is multiplicative and has the property that
not every element has norm zero or one
(equivalently, there is an element whose norm is bigger than one).
EXAMPLES: -/
-- QUOTE:
example (𝕜 : Type _) [NontriviallyNormedField 𝕜] (x y : 𝕜) : ‖x * y‖ = ‖x‖ * ‖y‖ :=
  norm_mul x y

example (𝕜 : Type _) [NontriviallyNormedField 𝕜] : ∃ x : 𝕜, 1 < ‖x‖ :=
  NormedField.exists_one_lt_norm 𝕜
-- QUOTE.

/- TEXT:
A finite-dimensional vector space over a nondiscrete normed field is
complete as long as the field itself is complete.
EXAMPLES: -/
-- QUOTE:
example (𝕜 : Type _) [NontriviallyNormedField 𝕜] (E : Type _) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E
-- QUOTE.

end

/- TEXT:
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
EXAMPLES: -/
section

-- QUOTE:
variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F :=
  f

example (f : E →L[𝕜] F) : Continuous f :=
  f.cont

example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
  f.map_add x y

example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
  f.map_smul a x
-- QUOTE.

/- TEXT:
Continuous linear maps have an operator norm that is characterized by the
following properties.
EXAMPLES: -/
-- QUOTE:
variable (f : E →L[𝕜] F)

example (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_op_norm x

example {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.op_norm_le_bound hMp hM
-- QUOTE.

end

/- TEXT:
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
BOTH: -/
section

-- QUOTE:
variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Metric

-- EXAMPLES:
example {ι : Type _} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n`
  let e : ℕ → Set E := fun n => ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- each of these sets is closed
  have hc : ∀ n : ℕ, IsClosed (e n)
  sorry
  -- the union is the entire space; this is where we use `h`
  have hU : (⋃ n : ℕ, e n) = univ
  sorry
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
       `e m` contains some `x` -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ‖k‖ := sorry
  -- show all elements in the ball have norm bounded by `m` after applying any `g i`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m
  sorry
  have εk_pos : 0 < ε / ‖k‖ := sorry
  refine' ⟨(m + m : ℕ) / (ε / ‖k‖), fun i => ContinuousLinearMap.op_norm_le_of_shell ε_pos _ hk _⟩
  sorry
  sorry
-- QUOTE.

-- SOLUTIONS:
example {ι : Type _} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n`
  let e : ℕ → Set E := fun n => ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- each of these sets is closed
  have hc : ∀ n : ℕ, IsClosed (e n) := fun i =>
    isClosed_iInter fun i => isClosed_le (g i).cont.norm continuous_const
  -- the union is the entire space; this is where we use `h`
  have hU : (⋃ n : ℕ, e n) = univ := by
    refine' eq_univ_of_forall fun x => _
    cases' h x with C hC
    obtain ⟨m, hm⟩ := exists_nat_ge C
    exact ⟨e m, mem_range_self m, mem_iInter.mpr fun i => le_trans (hC i) hm⟩
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
       `e m` contains some `x` -/
  obtain ⟨m : ℕ, x : E, hx : x ∈ interior (e m)⟩ := nonempty_interior_of_iUnion_of_closed hc hU
  obtain ⟨ε, ε_pos, hε : ball x ε ⊆ interior (e m)⟩ := isOpen_iff.mp isOpen_interior x hx
  obtain ⟨k : 𝕜, hk : 1 < ‖k‖⟩ := NormedField.exists_one_lt_norm 𝕜
  -- show all elements in the ball have norm bounded by `m` after applying any `g i`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m := by
    intro z hz i
    replace hz := mem_iInter.mp (interior_iInter_subset _ (hε hz)) i
    apply interior_subset hz
  have εk_pos : 0 < ε / ‖k‖ := div_pos ε_pos (zero_lt_one.trans hk)
  refine' ⟨(m + m : ℕ) / (ε / ‖k‖), fun i => ContinuousLinearMap.op_norm_le_of_shell ε_pos _ hk _⟩
  · exact div_nonneg (Nat.cast_nonneg _) εk_pos.le
  intro y le_y y_lt
  calc
    ‖g i y‖ = ‖g i (y + x) - g i x‖ := by rw [(g i).map_add, add_sub_cancel]
    _ ≤ ‖g i (y + x)‖ + ‖g i x‖ := (norm_sub_le _ _)
    _ ≤ m + m :=
      (add_le_add (real_norm_le (y + x) (by rwa [add_comm, add_mem_ball_iff_norm]) i)
        (real_norm_le x (mem_ball_self ε_pos) i))
    _ = (m + m : ℕ) := by norm_cast
    _ ≤ (m + m : ℕ) * (‖y‖ / (ε / ‖k‖)) :=
      (le_mul_of_one_le_right (Nat.cast_nonneg _)
        ((one_le_div <| div_pos ε_pos (zero_lt_one.trans hk)).2 le_y))
    _ = (m + m : ℕ) / (ε / ‖k‖) * ‖y‖ := (mul_comm_div _ _ _).symm


-- BOTH:
end

/- TEXT:
Asymptotic comparisons
^^^^^^^^^^^^^^^^^^^^^^

Defining differentiability also requires asymptotic comparisons.
Mathlib has an extensive library covering the big O and little o relations,
whose definitions are shown below.
Opening the ``asymptotics`` locale allows us to use the corresponding
notation.
Here we will only use little o to define differentiability.
EXAMPLES: -/
-- QUOTE:
open Asymptotics

open Asymptotics

example {α : Type _} {E : Type _} [NormedGroup E] {F : Type _} [NormedGroup F] (c : ℝ)
    (l : Filter α) (f : α → E) (g : α → F) : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff

example {α : Type _} {E : Type _} [NormedGroup E] {F : Type _} [NormedGroup F] (c : ℝ)
    (l : Filter α) (f : α → E) (g : α → F) : f =O[l] g ↔ ∃ C, IsBigOWith C l f g :=
  isBigO_iff_isBigOWith

example {α : Type _} {E : Type _} [NormedGroup E] {F : Type _} [NormedGroup F] (c : ℝ)
    (l : Filter α) (f : α → E) (g : α → F) : f =o[l] g ↔ ∀ C > 0, IsBigOWith C l f g :=
  isLittleO_iff_forall_isBigOWith

example {α : Type _} {E : Type _} [NormedAddCommGroup E] (c : ℝ) (l : Filter α) (f g : α → E) :
    f ~[l] g ↔ (f - g) =o[l] g :=
  Iff.rfl
-- QUOTE.

/- TEXT:
Differentiability
^^^^^^^^^^^^^^^^^

We are now ready to discuss differentiable functions between normed spaces.
In analogy the elementary one-dimensional,
mathlib defines a predicate ``has_fderiv_at`` and a function ``fderiv``.
Here the letter
"f" stands for *Fréchet*.
EXAMPLES: -/
section

-- QUOTE:
variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔ (fun x => f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] fun x => x - x₀ :=
  Iff.rfl

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) : fderiv 𝕜 f x₀ = f' :=
  hff'.fderiv
-- QUOTE.

/- TEXT:
We also have iterated derivatives that take values in the type of multilinear maps
``E [×n]→L[𝕜] F``,
and we have continuously differential functions.
The type ``with_top ℕ`` is ``ℕ`` with an additional element ``⊤`` that
is bigger than every natural number.
So :math:`\mathcal{C}^\infty` functions are functions ``f`` that satisfy
``cont_diff 𝕜 ⊤ f``.
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  iteratedFDeriv 𝕜 n f

example (n : WithTop ℕ) {f : E → F} :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, (m : WithTop ℕ) ≤ n → Continuous fun x => iteratedFderiv 𝕜 m f x) ∧
        ∀ m : ℕ, (m : WithTop ℕ) < n → Differentiable 𝕜 fun x => iteratedFderiv 𝕜 m f x :=
  contDiff_iff_continuous_differentiable
-- QUOTE.

/- TEXT:
There is a stricter notion of differentiability called
``has_strict_fderiv_at``, which is used in the statement
of the inverse function theorem and the statement of the implicit function
theorem, both of which are in mathlib.
Over ``ℝ`` or ``ℂ``, continuously differentiable
functions are strictly differentiable.
EXAMPLES: -/
-- QUOTE:
example {𝕂 : Type _} [IsROrC 𝕂] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕂 E] {F : Type _}
    [NormedAddCommGroup F] [NormedSpace 𝕂 F] {f : E → F} {x : E} {n : WithTop ℕ}
    (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) : HasStrictFderivAt f (fderiv 𝕂 f x) x :=
  hf.HasStrictFderivAt hn
-- QUOTE.

/- TEXT:
The local inverse theorem is stated using an operation that produces an
inverse function from a
function and the assumptions that the function is strictly differentiable at a
point ``a`` and that its derivative is an isomorphism.

The first example below gets this local inverse.
The next one states that it is indeed a local inverse
from the left and from the right, and that it is strictly differentiable.
EXAMPLES: -/
-- QUOTE:
section LocalInverse
variable [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

example (hf : HasStrictFderivAt f (↑f') a) : F → E :=
  HasStrictFderivAt.localInverse f f' a hf

example (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  hf.eventually_left_inverse

example (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 (f a), f (hf.localInverse f f' a x) = x :=
  hf.eventually_right_inverse

example [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E} (hf : HasStrictFderivAt f (↑f') a) :
    HasStrictFderivAt (HasStrictFderivAt.localInverse f f' a hf) (f'.symm : F →L[𝕜] E) (f a) :=
  HasStrictFderivAt.to_localInverse hf

end LocalInverse
-- QUOTE.

/- TEXT:
This has been only a quick tour of the differential calculus in mathlib.
The library contains many variations that we have not discussed.
For example, you may want to use one-sided derivatives in the
one-dimensional setting. The means to do so are found in mathlib in a more
general context;
see ``has_fderiv_within_at`` or the even more general ``has_fderiv_at_filter``.
EXAMPLES: -/
#check HasFderivWithinAt

#check HasFderivAtFilter

end

