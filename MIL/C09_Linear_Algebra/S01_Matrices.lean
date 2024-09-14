-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

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
Another way to build subspaces is to use ``Submodule.span`` which builds the smallest subspace
containing a given set ``s``.
On paper it is common to use that this space is made of all linear combinations of elements of
``s``.
But it is often more efficient to use its universal property expressed by ``Submodule.span_le``,
and the whole theory of Galois connections.


EXAMPLES: -/
-- QUOTE:
example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V
-- QUOTE.
/- TEXT:
When those are not enough, one can use the relevant induction principle
``Submodule.span_induction`` which ensures a property holds for every element of the
span of ``s`` as long as it holds on ``zero`` and elements of ``s`` and is stable under
sum and scalar multiplication.


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
An important special case of linear maps are endomorphisms: linear maps from a vector space to itself.
They are interesting because they form a ``K``-algebra. In particular we can evaluate polynomials
with coefficients in ``K`` on them, and they can have eigenvalues and eigenvectors.

Mathlib uses the abreviation ``Module.End K V := V →ₗ[K] V`` which is convenient when
using a lot of these (especially after opening the ``Module`` namespace).
EXAMPLES: -/
-- QUOTE:
section endomorphisms
open Polynomial Module

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  LinearMap.mul_eq_comp φ ψ -- rfl would also work

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ


-- QUOTE.
/- TEXT:
As an exercise manipulating endormorphisms, subspaces and polynomials, let us prove the
(binary) kernels lemma: for any endomorphism $`φ`$ and any two relatively
prime polynomials $`P`$ and $`Q`$, we have $`\ker P(φ) ⊕ \ker Q(φ) = \ker \big(PQ(φ)\big)`$.

Note that ``IsCoprime x y`` is defined as ``∃ a b, a * x + b * y = 1``.
EXAMPLES: -/
-- QUOTE:

#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
  rw [Submodule.eq_bot_iff]
  rintro x hx
  rw [Submodule.mem_inf, mem_ker, mem_ker] at hx
  rcases h with ⟨U, V, hUV⟩
  have := congr((aeval φ) $hUV.symm x)
  simpa [hx]
-- BOTH:

#check Submodule.add_mem_sup
#check map_mul
#check LinearMap.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply sup_le
    · rw [mul_comm, map_mul]
      apply ker_le_ker_comp -- or alternative below:
      -- intro x hx
      -- rw [mul_comm, mem_ker] at *
      -- simp [hx]
    · rw [map_mul]
      apply ker_le_ker_comp -- or alternative as above
  · intro x hx
    rcases h with ⟨U, V, hUV⟩
    have key : x = aeval φ (U*P) x + aeval φ (V*Q) x := by simpa using congr((aeval φ) $hUV.symm x)
    rw [key, add_comm]
    apply Submodule.add_mem_sup <;> rw [mem_ker] at *
    · rw [← mul_apply, ← map_mul, show P*(V*Q) = V*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]
    · rw [← mul_apply, ← map_mul, show Q*(U*P) = U*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]

-- QUOTE.
/- TEXT:
We now move to the discussions of eigenspaces and eigenvalues. By the definition, the eigenspace
associated to an endormorphism $`φ`$ and a scalar $`a`$ is the kernel of $`φ - aId`$.
The first thing to understand is how to spell $`aId`$. We could use
``a • LinearMap.id``, but Mathlib uses `algebraMap K (End K V) a` which directly plays nicely
with the ``K``-algebra structure.

EXAMPLES: -/
-- QUOTE:
example (a : K) : algebraMap K (End K V) a = a • LinearMap.id := rfl

-- QUOTE.
/- TEXT:
Then the next thing to note is that eigenspaces are defined for all values of ``a``, although
they are interesting only when they are non-zero.
However an eigenvector is, by definition, a non-zero element of an eigenspace. The corresponding
predicate is ``End.HasEigenvector``.
EXAMPLES: -/
-- QUOTE:
example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - algebraMap K (End K V) a) :=
  rfl


-- QUOTE.
/- TEXT:
Then there is a predicate ``End.HasEigenvalue`` and the corresponding subtype ``End.Eigenvalues``.
EXAMPLES: -/
-- QUOTE:

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalue are roots of the minimal polynomial
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true
example [FiniteDimensional K V] (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly

end endomorphisms
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
The isomorphism is called ``Basis.repr``.
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
Instead of starting with such an isomorphism, one can start with a family ``b`` of vectors that is
linearly independent and spanning, this is ``Basis.mk``.

The assumption that the family is spanning is spelled out as ``⊤ ≤ Submodule.span K (Set.range b)``.
Where ``⊤`` is the top submodule of ``V``, ie ``V`` seen as submodule of itself.
This spelling looks a bit tortuous, but we will see below that it is almost equivalent by definition
to the more readable ``∀ v, v ∈ Submodule.span K (Set.range b)`` (this underscore below refers to
the useless information ``v ∈ ⊤``).
EXAMPLES: -/
-- QUOTE:
noncomputable example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)

-- The family of vectors underlying the above basis is indeed ``b``.
example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
    Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
  Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i

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
Here Mathlib uses a special purpose function that requires some time to get used to:
``Finsupp.linearCombination`` (which is built on top of the more general ``Finsupp.sum``).
Given a finetely supported function ``c`` from a type ``ι`` to the base field ``K`` and any
function ``f`` from ``ι`` to ``V``, ``Finsupp.total ι V K f c`` is the sum over the support of ``c``
of the scalar multiplication ``c • f``. In particular, we can replace it by a sum over any finite
set containing the support of ``c``.

EXAMPLES: -/
-- QUOTE:

example (c : ι →₀ K) (f : ι → V) (s : Finset ι) (h : c.support ⊆ s) :
    Finsupp.linearCombination K f c = ∑ i ∈ s, c i • f i :=
  Finsupp.linearCombination_apply_of_mem_supported K h
-- QUOTE.
/- TEXT:
One could also assume that ``f`` is finitely supported and still get a well defined sum.
But the choice made by ``Finsupp.linearCombination`` is the one relevant to our basis discussion since it allows
to state the generalization of ``Basis.sum_repr``.
EXAMPLES: -/
-- QUOTE:

example : Finsupp.linearCombination K B (B.repr v) = v :=
  B.linearCombination_repr v
-- QUOTE.
/- TEXT:
One could wonder why ``K`` is an explicit argument here, whereas it can be inferred from
the type of ``c``. The point is that the partially applied ``Finsupp.linearCombination K f``
is interesting in itself, it is not a bare function from ``ι →₀ K`` to ``V`` but a
``K``-linear map.
EXAMPLES: -/
-- QUOTE:
variable (f : ι → V) in
#check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)
-- QUOTE.
/- TEXT:
The above subltety also explain why dot notation cannot be used to write
``c.linearCombination K f`` instead of ``Finsupp.linearCombination K f c``.
Indeed ``Finsupp.linearCombination`` does not take ``c`` as an argument,
``Finsupp.linearCombination K f`` is coerced to a function type and then this function
takes ``c`` as an argument.

Returning to the mathematical discussion, it is important to understand that the
representation of vectors in a basis is less useful in formalized
mathematics than you may think.
Indeed it is very often more efficient to directly use more abstract properties of bases.
In particular the universal property of bases connecting them to other free objects in algebra
allows to construct linear maps by specifying the images of basis vectors.
This is ``Basis.constr``. For any ``K``-vector space ``W``, our basis ``B``
gives a linear isomorphism ``Basis.constr B K`` from ``ι → W`` to ``V →ₗ[K] W``.
This isomorphism is characterized by the fact that it sends any function ``u : ι → W``
to a linear map sending the basis vector ``B i`` to ``u i``, for every ``i : ι``.
EXAMPLES: -/
-- QUOTE:
section

#check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))

variable (u : ι → W)

#check (B.constr K u : V →ₗ[K] W)

example (i : ι) : B.constr K u (B i) = u i := B.constr_basis K u i
end
-- QUOTE.
/- TEXT:
This property is indeed characteristic because linear maps are determined by their values
on bases:
EXAMPLES: -/
-- QUOTE:
example (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h

-- QUOTE.
/- TEXT:
If we also have a basis ``B'`` on the target space then we can identify linear maps
with matrices. This identification is a ``K``-linear isomorphism.
EXAMPLES: -/
-- QUOTE:
noncomputable section
variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

#check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

open Matrix -- get access to the ``*ᵥ`` notation for multiplication between matrices and vectors.

example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v
end
-- QUOTE.
/- TEXT:
Returning to the case of a single vector space, bases are also useful to define the concept of
dimension.
Here again, there is the elementary case of finite-dimensional vector spaces.
For such spaces we expect a dimension which is a natural number.
This is ``FiniteDimensional.finrank``. It takes the base field as an explicit argument
since a given abelian group can be a vector space over different fields.

EXAMPLES: -/
-- QUOTE:
section
#check FiniteDimensional.finrank K V

--  ``Fin n → K`` is the archetypical space with dimension ``n`` over ``K``.
example (n : ℕ) : FiniteDimensional.finrank K (Fin n → K) = n :=
  FiniteDimensional.finrank_fin_fun K

-- seen as a vector space over itself, ``ℂ`` has dimension one.
example : FiniteDimensional.finrank ℂ ℂ = 1 :=
  FiniteDimensional.finrank_self ℂ

-- but as a real vector space it has dimension two.
example : FiniteDimensional.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

-- QUOTE.
/- TEXT:
Note that ``FiniteDimensional.finrank`` is defined for any vector space. It returns
zero for infinite dimensional vector spaces, just as division by zero returns zero.

Of course many lemmas require a finite dimensional assumption. This is the role of
the ``FiniteDimension`` typeclass. For instance think of how the next example fails without this
assumption.
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] : 0 < FiniteDimensional.finrank K V ↔ Nontrivial V  :=
  FiniteDimensional.finrank_pos_iff

-- QUOTE.
/- TEXT:
In the above statement, ``Nontrivial V`` means ``V`` has at least two different elements.
Note that ``FiniteDimensional.finrank_pos_iff`` has no explicit argument.
This is fine when using it from left to right, but not when using it from right to left
because Lean has no way to guess ``K`` from the statement ``Nontrivial V``.
In that case it is useful to use the name argument syntax, after checking that the lemma
is stated over a ring named ``R``. So we can write:
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] (h : 0 < FiniteDimensional.finrank K V) : Nontrivial V := by
  apply (FiniteDimensional.finrank_pos_iff (R := K)).1
  exact h

-- QUOTE.
/- TEXT:
The above spelling is strange because we already have ``h`` as an assumption, so we could
just as well give the full proof ``FiniteDimensional.finrank_pos_iff.1 h`` but it
is good to know for more complicated cases.

By definition, ``FiniteDimensional K V`` can be read from any basis. Recall we have
a basis ``B`` of ``V`` indexed by a type ``ι``.
EXAMPLES: -/
-- QUOTE:
example [Finite ι] : FiniteDimensional K V := FiniteDimensional.of_fintype_basis B

example [FiniteDimensional K V] : Finite ι :=
  (FiniteDimensional.fintypeBasisIndex B).finite
end
-- QUOTE.
/- TEXT:
Using that the subtype corresponding to a linear subspace has a vector space structure,
we can talk about the dimension of a subspace.
EXAMPLES: -/
-- QUOTE:

section
variable (E F : Submodule K V) [FiniteDimensional K V]

open FiniteDimensional

example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
    finrank K E + finrank K F :=
  Submodule.finrank_sup_add_finrank_inf_eq E F

example : finrank K E ≤ finrank K V := Submodule.finrank_le E
-- QUOTE.
/- TEXT:
We are now ready for an exercise about ``finrank`` and subspaces.
EXAMPLES: -/
-- QUOTE:
example (h : finrank K V < finrank K E + finrank K F) : Nontrivial (E ⊓ F : Submodule K V) := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
  rw [← finrank_pos_iff (R := K)]
  have := Submodule.finrank_sup_add_finrank_inf_eq E F
  have := Submodule.finrank_le E
  have := Submodule.finrank_le F
  have := Submodule.finrank_le (E ⊔ F)
  linarith
-- BOTH:
end
-- QUOTE.

/- TEXT:
Let us now move to the general case of dimension theory. In this case
``finrank`` is useless, but still have that, for any two bases of the same
vector space, there is a bijection between the type indexing those bases. So we
can still hope to define rank as a cardinal, ie an element of the “quotient of
the collection of types under the existence of a bijection equivalence
relation”.

When discussing cardinal, it gets harder to ignore foundational issues around Russel’s paradox
like we do everywhere else in this book.
There is no type of all types because it would lead to logical inconsistencies.
This issue is solved by the hierarchy of universes that
we usually try to ignore.

Each type has a universe level, and those levels behave similarly to natural
numbers. In particular there is zeroth level, and the corresponding universe
``Type 0`` is simply denoted by ``Type``. This universe is enough to hold
almost all of classical mathematics. For instance ``ℕ`` and ``ℝ`` have type ``Type``.
Each level ``u`` has a successor denoted
by ``u + 1``, and ``Type u`` has type ``Type (u+1)``.

But universe levels are not natural numbers, they have a really different nature and don’t
have a type. In particular you cannot state in Lean something like ``u ≠ u + 1``.
There is simply no type where this would take place. Even stating
``Type u ≠ Type (u+1)`` does not make any sense since ``Type u`` and ``Type
(u+1)`` have different types.

Whenever we write ``Type*``, Lean inserts a universe level variable named ``u_n`` where ``n`` is a
number. This allows definitions and statements to live in all universes.

Given a universe level ``u``, we can define an equivalence relation on ``Type u`` saying
two types ``α`` and ``β`` are equivalent if there is a bijection between them.
The quotient type ``Cardinal.{u}`` lives in ``Type (u+1)``. The curly braces
denote a universe variable. The image of ``α : Type u`` in this quotient is
``Cardinal.mk α : Cardinal.{u}``.

But we cannot directly compare cardinals in different universes. So technically we
cannot define the rank of a vector space ``V`` as the cardinal of all types indexing
a basis of ``V``.
So instead it is defined as the supremum ``Module.rank K V `` of cardinals of
all linearly independent sets in ``V``. If ``V`` has universe level ``u`` then
its rank has type ``Cardinal.{u}``.


EXAMPLES: -/
-- QUOTE:
#check V -- Type u_2
#check Module.rank K V -- Cardinal.{u_2}

-- QUOTE.
/- TEXT:
One can still relate this definition to bases. Indeed there is also a commutative ``max``
operation on universe levels, and given two universe levels ``u`` and ``v``
there is an operation ``Cardinal.lift.{u, v} : Cardinal.{v} → Cardinal.{max v u}``
that allows to put cardinals in a common universe and state the dimension theorem.
EXAMPLES: -/
-- QUOTE:

universe u v in
variable {ι : Type u} (B : Basis ι K V)
         {ι' : Type v} (B' : Basis ι' K V) in
example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
  mk_eq_mk_of_basis B B'
-- QUOTE.
/- TEXT:
We can relate the finite dimensional case to this discussion using the coercion
from natural numbers to finite cardinals (or more precisly the finite cardinals which live in ``Cardinal.{v}`` where ``v`` is the universe level of ``V``).
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] :
    (FiniteDimensional.finrank K V : Cardinal) = Module.rank K V :=
  finrank_eq_rank K V
-- QUOTE.
/-


Multilinear algebra (multilinear maps, alternating maps, quadratic forms,
inner products, matrix representation, spectral theorem, tensor products)

Modules over rings


in Mathlib/RingTheory/Ideal/Operations.lean:
instance Submodule.moduleSubmodule {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] :
Module (Ideal R) (Submodule R M)

-/