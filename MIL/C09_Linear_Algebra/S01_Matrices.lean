-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import MIL.Common

/- TEXT:
.. _matrices:

Matrices
------------------

.. index:: matrices

Beware the matrix notation list rows but the vector notation
is neither a row vector nor a column vector. Multiplication of a matrix with a vector
from the left (resp. right) interprets the vector as a row (resp. column) vector.

EXAMPLES: -/
-- QUOTE:

section matrices

#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
/-
* `⬝ᵥ` for `Matrix.dotProduct`
* `*ᵥ` for `Matrix.mulVec`
* `ᵥ*` for `Matrix.vecMul`
* `ᵀ` for `Matrix.transpose`
* `ᴴ` for `Matrix.conjTranspose`

Concrete matrices with concrete entries

Note we are not suggesting to replace Sage with #eval or #norm_num
-/
open Matrix

#eval row (Fin 1) ![1, 2]

#eval col (Fin 1) ![1, 2]

#eval ![1, 2] ⬝ᵥ ![3, 4] -- vector dot product

#eval !![1, 2; 3, 4] *ᵥ ![1, 1]  -- matrices acting on vectors on the left

#eval !![1, 2] *ᵥ ![1, 1]  -- matrices acting on vectors on the left

#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6]  -- matrices acting on vectors on the right

#eval !![1, 2; 3, 4]ᵀ

#eval !![(1 : ℤ), 2; 3, 4].det

#simp !![(1 : ℝ), 2; 3, 4].det
#norm_num !![(1 : ℝ), 2; 3, 4].det

-- Marche pas comme on veut
#norm_num !![(1 : ℝ), 2; 3, 4] ⁻¹

example : !![(1 : ℝ), 2; 3, 4].det = -2 := by
  simp only [det_fin_two_of, one_mul]
  norm_num

example : !![(1 : ℝ), 2; 3, 4].trace = 5 := by
  simp [trace]
  norm_num

-- variable {R : Type*} [AddCommMonoid R]
-- @[simp]
-- theorem trace_fin_one_of (a : R) : trace !![a] = a :=
--   trace_fin_one _
--
-- @[simp]
-- theorem trace_fin_two_of (a b c d : R) : trace !![a, b; c, d] = a + d :=
--   trace_fin_two _
--
-- @[simp]
-- theorem trace_fin_three_of (a b c d e f g h i : R) :
--     trace !![a, b, c; d, e, f; g, h, i] = a + e + i :=
--   trace_fin_three _

-- L’exemple ci-dessous est très décevant sans les lemmes ci-dessus (qui sont proposés dans Mathlib)
#norm_num !![(1 : ℝ), 2; 3, 4].trace

variable (a b c d : ℝ) in
#simp !![a, b; c, d].det

-- Discuss inverse of matrix. See     Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean

-- QUOTE.

/- TEXT:
General matrices, the story of ``Matrix n m R``.

EXAMPLES: -/
-- QUOTE:
section

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n]

example (A B : Matrix n n R) : trace (A*B - B*A) = 0 := by
  rw [trace_sub, trace_mul_comm, sub_self]

end
end matrices
-- QUOTE.

/- TEXT:
Abstract vector spaces and linear maps
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index:: vector space

We now move on to abstract linear algebra, taking place in a vector space over any field.
Mathlib actually deals with a more general version of linear algebra involving the word module,
but for now we will pretend this is only an excentric spelling habit.

The way to say “let $`K`$ be a field and let $`V`$ be a vector space over $`K`$” is:

EXAMPLES: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-- QUOTE.

/- TEXT:
We explained in :numref:`Chapter %s <hierarchies>` why we need two separate
typeclasses ``[AddCommGroup V] [Module K V]``.
The short version is the following.
Mathematically we want to say that having a $`K`$-vector space structure
implies having an additive commutative group structure.
We could tell this to Lean. But then whenever Lean would need to find such a
group structure on a type $`V`$, it would go hunting for vector space
structures using a *completely unspecified* field $`K`$ that cannot be infered
from $`V`$.
This would be very bad for the type class synthesis system.

The multiplication of a vector `v` by a scalar `a` is denoted by
`a • v`. We a couple of algebraic rules about the interaction of this operation with addition in the
following examples. Of course `simp` of `apply?` would find those proofs, but it is still useful to
remember than scalar multiplication is abbreviated `smul` in lemma names.
Unfortunately there is not yet an analogue of the `ring` or `group` tactic that would prove
all equalities following from the vector space axioms (there is no deep obstruction here, we
simply need to find a skilled tactic writer having time for this).

EXAMPLES: -/

-- QUOTE:
example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

example (a b : K) (u : V) : (a + b) • u = a • u + b • u :=
  add_smul a b u

example (a b : K) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u

-- QUOTE.

/- TEXT:
Next we need linear maps. Like group morphisms, linear maps in Mathlib are bundled maps, ie packages
made of a map and proofs of its linearity properties.
Those bundled maps are converted to ordinary functions when applied.
See :numref:`Chapter %s <hierarchies>` for more information about this design.

The type of linear maps between two ``K``-vector spaces
``V`` and ``W`` is denoted by ``V →ₗ[K] W``. The subscript `l` stands for linear.
At first it may feel odd to specify ``K`` in this notation.
But this is crucial when several fields come into play.
For instance real-linear maps from $`ℂ`$ to $`ℂ`$ are every map $`z ↦ az + b\bar{z}`$
while only the maps $`z ↦ az`$ are complex linear, and this difference is crucial in
complex analysis.

EXAMPLES: -/
-- QUOTE:

variable {W : Type*} [AddCommGroup W] [Module K W]

variable (φ : V →ₗ[K] W)

example (a : K) (v : V) : φ (a • v) = a • φ v :=
  map_smul φ a v

example (v w : V) : φ (v + w) = φ v + φ w :=
  map_add φ v w

-- QUOTE.

/- TEXT:
Note that ``V →ₗ[K] W`` itself carries interesting algebraic structures (this
is part of the motivation for bundling those maps).

EXAMPLES: -/
-- QUOTE:
variable (ψ : V →ₗ[K] W)

#check (2 • φ + ψ : V →ₗ[K] W)

-- QUOTE.

/- TEXT:
One down-side of using bundled maps is that we cannot use ordinary function composition.
We need to use ``LinearMap.comp`` or the notation ``∘ₗ``.

EXAMPLES: -/
-- QUOTE:
variable (θ : W →ₗ[K] V)

#check (φ.comp θ : W →ₗ[K] W)
#check (φ ∘ₗ θ : W →ₗ[K] W)
-- QUOTE.

/- TEXT:
There are two main ways to construct linear maps.
First you can build the structure by providing the function and the linearity proof.
As usual, this is facilitated by the structure code action: you can type
``example : V →ₗ[K] V := _`` and use the code action “Generate a skeleton” attached to the
underscore.
EXAMPLES: -/
-- QUOTE:

example : V →ₗ[K] V where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..

-- QUOTE.

/- TEXT:
You may wonder why the proof fields of ``LinearMap`` have names ending with a prime.
This is because they are defined before the coercion to functions is defined, hence they are
phrased in terms of ``LinearMap.toFun``. Then they are restated as ``LinearMap.map_add``
and ``LinearMap.smul`` in terms of the coercion to function.
This is not yet the end of the story. One also want a version of ``map_add`` that applies to
any (bundled) map preserving addition, such as additive group morphisms, linear maps, continuous
linear maps, ``K``-algebra maps etc… This one is ``map_add`` (in the root namespace).
The intermediate version, ``LinearMap.map_add`` is a bit redudant but allows to use dot notation, which
can be nice sometimes. A similar story exists for ``map_smul``, and the general framework
is explained in :numref:`Chapter %s <hierarchies>`.
EXAMPLES: -/
-- QUOTE:

#check φ.map_add'
#check φ.map_add
#check map_add φ

-- QUOTE.

/- TEXT:
One can also build linear maps from the ones that are already defined in Mathlib
using various combinators.
For instance the above example is already known as ``LinearMap.lsmul K V 3``.
There are several reason why ``K`` and ``V`` are explicit arguments here.
The most pressing one is that from a bare ``LinearMap.lsmul 3`` there would be no way
for Lean to infer ``V`` or even ``K``.
But also ``LinearMap.lsmul K V`` is an interesting object by itself: it has type
``K →ₗ[K] V →ₗ[K] V``, meaning it is a ``K``-linear map from ``K``
—seen as a vector space over itself— to the space of ``K``-linear maps from ``V`` to ``V``.
EXAMPLES: -/
-- QUOTE:

#check LinearMap.lsmul K V 3
#check LinearMap.lsmul K V

-- QUOTE.

/- TEXT:
There is also a type ``LinearEquiv`` of linear isomorphisms denoted by ``V ≃ₗ[K] W``.
The inverse of ``f : V ≃ₗ[K] W`` is ``f.symm : W ≃ₗ[K] V``,
composition of ``f`` and ``g`` is ``f.trans g`` also denoted by ``f ≪≫ₗ g``, and
the identity isomorphism of ``V`` is ``LinearEquiv.refl K V``.
Elements of this type are automatically coerced to morphisms and functions when necessary.
EXAMPLES: -/
-- QUOTE:
example (f : V ≃ₗ[K] W) :
    f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
  f.self_trans_symm
-- QUOTE.

/- TEXT:
One can use ``LinearEquiv.ofBijective`` to build an isomorphism from a bijective morphism.
Doing so makes the inverse function noncomputable.
EXAMPLES: -/
-- QUOTE:
noncomputable example (f : V →ₗ[K] W) (h : Function.Bijective f) : V ≃ₗ[K] W :=
  .ofBijective f h
-- QUOTE.
/- TEXT:
Sums and products of vector spaces
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We can also build new vector spaces out of old ones using direct sums and direct
products (we will discuss tensor products below after discussing multi-linear maps).
Let us start with two vectors spaces. In this case there is no difference between sum and product,
and we can simply use the product type.
In the following snippet of code we simply show how to get all the structure maps (inclusions
and projections) as linear maps, as well as the universal properties constructing linear maps
into products and out of sums (if you are not familiar with the category-theoretic distinction
between sums and products, you can simply ignore the universal property vocabulary and focus
on the types of the following examples).
EXAMPLES: -/
-- QUOTE:

section binary_product

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {T : Type*} [AddCommGroup T] [Module K T]

-- First projection map
example : V × W →ₗ[K] V := LinearMap.fst K V W

-- Second projection map
example : V × W →ₗ[K] W := LinearMap.snd K V W

-- Universal property of the product
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ

-- The product map does the expected thing, first component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl

-- The product map does the expected thing, second component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl

-- We can also combine maps in parallel
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ

-- This is simply done by combining the projections with the universal property
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
  φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ.snd K V W) := rfl

-- First inclusion map
example : V →ₗ[K] V × W := LinearMap.inl K V W

-- Second inclusion map
example : W →ₗ[K] V × W := LinearMap.inr K V W

-- Universal property of the sum (aka coproduct)
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ

-- The coproduct map does the expected thing, first component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
  LinearMap.coprod_inl φ ψ

-- The coproduct map does the expected thing, second component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
  LinearMap.coprod_inr φ ψ



end binary_product

-- QUOTE.
/- TEXT:
Let us now turn to sums and products of arbitrary families of vector spaces.
Here we will simply see how to define a family of vector spaces and access the universal
properties of sums and products.
Note that the direct sum notation is scoped to the ``DirectSum`` namespace, and
that the universal property of direct sums requires decidable equality on the
indexing type (this is somehow an implementation accident).
EXAMPLES: -/

-- QUOTE:
section families
open DirectSum

variable {ι : Type*} [DecidableEq ι] (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

example (φ : Π i, V i →ₗ[K] W) : (⨁ i, V i) →ₗ[K] W :=
  DirectSum.toModule K ι W φ


example (φ : Π i, W →ₗ[K] V i) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ

example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i

example : Π i, V i →+ (⨁ i, V i) := DirectSum.of V

example : Π i, V i →ₗ[K] (⨁ i, V i) := DirectSum.lof K ι V

variable (i : ι) in
#check LinearMap.single (R := K) (φ := V) i  -- The linear inclusion of V i into the product

variable (i : ι) in
#check DirectSum.lof K ι V i -- The linear inclusion of V i into the sum

example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
  linearEquivFunOnFintype K ι V

end families
-- QUOTE.

/- TEXT:
EXAMPLES: -/
-- QUOTE:

-- QUOTE.
/- TEXT:
Subspaces
^^^^^^^^^

Just as linear maps are bundled, a linear subspace of ``V`` is also a bundled structure consisting of
a set in ``V`` with the relevant closure properties.
Again the word module appear instead of space because of the more general context that
Mathlib actually uses for linear algebra.
EXAMPLES: -/
-- QUOTE:
example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx

-- QUOTE.

/- TEXT:
In the example above, it is important to understand that ``Submodule K V`` is the type of ``K``-linear
subspaces of ``V``, rather than a predicate ``IsSubmodule U`` where ``U`` is an element of ``Set V``.
``Submodule K V`` is endowed with a coercion to ``Set V`` and a membership predicate on ``V``.
See :numref:`section_hierarchies_subobjects` for an explanation of how and why this is done.

Of course, two subspaces are the same if and only if they have the same elements. This fact
is registered for use with the ``ext`` tactic, which can be used to prove two subspaces are
equal in the same way it is used to prove that two sets are equal.

To state and prove, for example, that ``ℝ`` is a ``ℝ``-linear subspace of ``ℂ``,
what we really want is to construct a term of type ``Submodule ℝ ℂ`` whose projection to
``Set ℂ`` is ``ℝ``, or, more precisely, the image of ``ℝ`` in ``ℂ``.
EXAMPLES: -/
-- QUOTE:
noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp

-- QUOTE.

/- TEXT:
The prime at the end of proof fields in ``Submodule`` are analogous to the one in ``LinearMap``.
Those fields are stated in terms of the ``carrier`` fields because they are defined before the
``MemberShip`` instance. They are then superseded by ``Submodule.add_mem``, ``Submodule.zero_mem``
and ``Submodule.smul_mem`` that we saw above.

As an exercise in manipulating subspaces and linear maps, you will define the pre-image of
a subspace by a linear map (of course we will see below that Mathlib already knows about this).
Remember that ``Set.mem_preimage`` can be used to rewrite a statement involving
membership and preimage. This is the only lemma you will need in addition to the lemmas
discussed above about ``LinearMap`` and ``Submodule``.
BOTH: -/
-- QUOTE:
def preimage (φ : V →ₗ[K] W) (H : Submodule K W) : Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rw [Set.mem_preimage, map_zero]
    exact H.zero_mem
-- BOTH:
  add_mem' := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rintro a b ha hb
    rw [Set.mem_preimage, map_add]
    apply H.add_mem <;> assumption
-- BOTH:
  smul_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro a v hv
    rw [Set.mem_preimage, map_smul]
    exact H.smul_mem a hv
-- BOTH:
-- QUOTE.

/- TEXT:
Using type classes, Mathlib knows that a subspace of a vector space inherits a vector space structure.
EXAMPLES: -/
-- QUOTE:
example (U : Submodule K V) : Module K U := inferInstance
-- QUOTE.

/- TEXT:
This example is subtle. The object ``U`` is not a type, but Lean automatically coerces it to
a type by interpreting it as a subtype of ``V``.
So the above example can be restated more explicitly as:
EXAMPLES: -/
-- QUOTE:
example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance
-- QUOTE.

/- TEXT:
An important benefit of having a type ``Submodule K V`` instead of a predicate
``IsSubmodule : Set V → Prop`` is that one can easily endow ``Submodule K V`` with additional structure.
Importantly, it has the structure of a complete lattice structure with respect to
inclusion. For instance, instead of having a lemma stating that an intersection of
two subspaces of ``V`` is again a subspace, we
have used the lattice operation ``⊓`` to construct the intersection. We can then apply arbitrary
lemmas about lattices to the construction.

Let us check that the set underlying the infimum of two subspaces is indeed, by definition,
their intersection.
EXAMPLES: -/
-- QUOTE:
example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl
-- QUOTE.

/- TEXT:
It may look strange to have a different notation for what amounts to the intersection of the
underlying sets, but the correspondence does not carry over to the supremum operation and set
union, since a union of subspaces is not, in general, a subspace.
Instead one needs to use the subspace generated by the union, which is done
using ``Submodule.span``.
EXAMPLES: -/
-- QUOTE:
example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]
-- QUOTE.

/- TEXT:
Another subtlety is that ``V`` itself does not have type ``Submodule K V``,
so we need a way to talk about ``V`` seen as a subspace of ``V``.
This is also provided by the lattice structure: the full subspace is the top element of
this lattice.
EXAMPLES: -/
-- QUOTE:
example (x : V) : x ∈ (⊤ : Submodule K V) := trivial
-- QUOTE.

/- TEXT:
Similarly the bottom element of this lattice is the subspace whose only element is the
zero element.
EXAMPLES: -/
-- QUOTE:
example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K
-- QUOTE.

/- TEXT:
In particular we can discuss the case of submodules that are in (internal) direct sum.


TODO: Discuss here submodule in direct sum, and the link with abstract direct sums.
EXAMPLES: -/
-- QUOTE:

example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  h.submodule_independent.pairwiseDisjoint hij |>.eq_bot

open DirectSum in
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
   : (⨁ i, U i) →ₗ[K] V := LinearEquiv.ofBijective (coeLinearMap U) h

-- QUOTE.
/- TEXT:
As promised earlier, we now describe how to push and pull subspaces by linear maps.
As usual in Mathlib, the first operation is called ``map`` and the second one is called
``comap``.
EXAMPLES: -/
-- QUOTE:
variable (E : Submodule K V) in
#check Submodule.map φ E

variable (F : Submodule K W) in
#check Submodule.comap φ F
-- QUOTE.
/- TEXT:
Note those live in the ``Submodule`` namespace so one can use dot notation and write
``E.map φ`` instead of ``Submodule.map φ E``, but this is pretty awkward to read (although some
Mathlib contributors use this spelling).

In particular the range and kernel of a linear map are subspaces. Those special cases are important
enough to get declarations.
EXAMPLES: -/
-- QUOTE:
example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = .comap φ ⊥ := rfl
-- QUOTE.

/- TEXT:
Note that we cannot write ``φ.ker`` instead of ``LinearMap.ker φ`` because ``LinearMap.ker`` also
applies to classes of maps preserving more structure, hence it does not expect an argument
whose type starts with ``LinearMap``, hence dot notation doesn’t work here.
However we were able to use the other flavor of dot notation in the right-hand side. Because
Lean expects a term with type ``Submodule K V`` after elaborating the left-hand side, it interprets
``.comap`` as ``Submodule.comap``.

The following lemmas give the key relations between those submodule and the properties of ``φ``.
EXAMPLES: -/
-- QUOTE:

open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm
-- QUOTE.
/- TEXT:
As an exercise, let us prove the Galois connection property for ``map`` and ``comap``.
One can use the following lemmas but this is not required since they are true by definition.
EXAMPLES: -/
-- QUOTE:

#check Submodule.mem_map_of_mem
#check Submodule.mem_map
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h - ⟨x, hx, rfl⟩
    exact h hx
-- QUOTE.

/- TEXT:

TODO: discuss ``Submodule.span`` and ``Submodule.span_induction``

EXAMPLES: -/
-- QUOTE:

-- QUOTE.

/- TEXT:
Quotient vector spaces use the general quotient notation (typed with ``\quot``, not the ordinary
``/``).
The projection onto a quotient space is ``Submodule.mkQ`` and the universal property is
``Submodule.liftQ``.
EXAMPLES: -/
-- QUOTE:

variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange

-- QUOTE.
/- TEXT:
Bases
^^^^^

We now want to discuss bases of vector spaces. Informally there are many ways to define this notion.
One can use a universal property.
One can say a basis is a family of vectors that is linearly independent and spanning.
Or one can combine those properties and directly say that a basis is a family of vectors
such that every vectors can be written uniquely as a linear combination of bases vectors.
Yet another way to say it is that a basis provides a linear isomorphism with a power of
the base field ``K``, seen as a vector space over ``K``.

This isomorphism version is actually the one that Mathlib uses as a definition under the hood, and
other charaterizations are proven from it.
One must be slightly careful with the “power of ``K``” idea in the case of infinite bases.
Indeed only finite linear combinations make sense in this algebraic context. So what we need
as a reference vector space is not a direct product of copies of ``K`` but a direct sum.
We could use ``⨁ i : ι, K`` for some type ``ι`` indexing the basis
But we rather use the more specialized spelling ``ι →₀ K`` which means
“functions from ``ι`` to ``K`` with finite support, ie function which vanishes outside a finite set
in ``ι``.
Evaluating such a function coming from a basis ``B`` at a vector ``v`` and
``i : ι`` returns the component (or coordinate) of ``v`` on the ``i``-th basis vector.

The type of bases indexed by a type ``ι`` of ``V`` as a ``K`` vector space is ``Basis ι K V``.
The isomorphism
EXAMPLES: -/
-- QUOTE:
variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

-- The basis vector with index ``i``
#check B i -- V

-- the linear isomorphism with the model space given by ``B``
#check B.repr -- V ≃ₗ[K] ι →₀ K

-- the component function of ``v``
#check B.repr v -- ι →₀ K

-- the component of ``v`` with index ``i``
#check B.repr v i -- K

-- QUOTE.

/- TEXT:
In particular the model vector space ``ι →₀ K`` has a so-called canonical basis whose ``repr``
function evaluated on any vector is the identity isomorphism. It is called
``Finsupp.basisSingleOne`` where ``Finsupp`` means function with finite support and
``basisSingleOne`` refers to the fact that basis vectors are function which
vanish expect for a single input value. More precisely the basis vector indexed by ``i : ι``
is ``Finsupp.single i 1`` which is the finitely supported function taking value ``1`` at ``i``
and ``0`` everywhere else.

EXAMPLES: -/
-- QUOTE:
variable [DecidableEq ι]

example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

#check Finsupp.basisSingleOne

example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl

-- QUOTE.
/- TEXT:
The story of finitely supported functions is uneeded when the indexing type is finite.
In this case we can use the simpler ``Pi.basisFun`` which gives a basis of the whole
``ι → K``.
EXAMPLES: -/
-- QUOTE:

#check Pi.basisFun

example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
  simp

-- QUOTE.
/- TEXT:
Going back to the general case of bases of abstract vector space, we can express
any vector as a linear combination of basis vectors.
Let us first see the easy case of finite bases.
EXAMPLES: -/
-- QUOTE:

example [Fintype ι] : ∑ i : ι, B.repr v i • (B i) = v :=
  B.sum_repr v


-- QUOTE.

/- TEXT:
When ``ι`` is not finite, the above statement makes no sense a priori: we cannot take a sum over ``ι``.
However the support of the function being summed is finite (it is the support of ``B.repr v``).
But we need to apply a construction that takes this into account.
Here Mathlib uses a special purpose function that requires some time to get used to.

EXAMPLES: -/
-- QUOTE:

#check Submodule.span

lemma Basis.induction {p : V → Prop} (mem : ∀ i, p (B i)) (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y)) (smul : ∀ (a : K) x, p x → p (a • x)) (v : V) : p v :=
  Submodule.span_induction (p := p) (B.mem_span v) (by simp [mem]) zero add smul


example : ∑ᶠ i : ι, B.repr v i • (B i) = v := by

  apply B.induction _ _ _ _ v
  · intro i
    simp [Finsupp.single_apply]
    rw [finsum_eq_single, if_pos]
    rfl
    aesop
  · simp
  · intro v w hv hw
    simp [add_smul]
    rw [finsum_add]
    sorry
  · intro a v h
    simp [mul_smul, ← smul_finsum, h]
  -- rw [finsum_eq_sum]
  -- swap
  -- apply (B.repr v).finite_support.subset
  -- apply support_smul_subset_left
  -- conv_rhs => rw [← B.total_repr v]
  -- rw [@Finsupp.total_apply_of_mem_supported ]
  -- refine (Finsupp.mem_supported K (B.repr v)).mpr ?_
  -- simp
  -- intro i hi
  -- simp at hi ⊢
  -- constructor
  -- exact hi
  -- exact Basis.ne_zero B i
-- QUOTE.
/-

* `Basis.constr b R f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.
* `Basis.reindex` uses an equiv to map a basis to a different indexing set.
* `Basis.map` uses a linear equiv to map a basis to a different module.

## Main statements

* `Basis.mk`: a linear independent set of vectors spanning the whole module determines a basis

* `Basis.ext` states that two linear maps are equal if they coincide on a basis.
  Similar results are available for linear equivs (if they coincide on the basis vectors),
  elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.


Bases, representing vectors and linear maps in a basis

Dimension

Endomorphisms (polynomial evaluation, minimal polynomial, Caley-Hamilton,
eigenvalues, eigenvectors)

Multilinear algebra (multilinear maps, alternating maps, quadratic forms,
inner products, matrix representation, spectral theorem, tensor products)

Modules over rings


in Mathlib/RingTheory/Ideal/Operations.lean:
instance Submodule.moduleSubmodule {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] :
Module (Ideal R) (Submodule R M)

-/
