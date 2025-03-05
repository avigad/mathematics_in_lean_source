-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:
.. index:: vector subspace

Subspaces and quotients
-----------------------

Subspaces
^^^^^^^^^

Just as linear maps are bundled, a linear subspace of ``V`` is also a bundled structure consisting of
a set in ``V``, called the carrier of the subspace, with the relevant closure properties.
Again the word module appears instead of vector space because of the more general context that
Mathlib actually uses for linear algebra.
BOTH: -/
-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

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
Those fields are stated in terms of the ``carrier`` field because they are defined before the
``MemberShip`` instance. They are then superseded by ``Submodule.add_mem``, ``Submodule.zero_mem``
and ``Submodule.smul_mem`` that we saw above.

As an exercise in manipulating subspaces and linear maps, you will define the pre-image of
a subspace by a linear map (of course we will see below that Mathlib already knows about this).
Remember that ``Set.mem_preimage`` can be used to rewrite a statement involving
membership and preimage. This is the only lemma you will need in addition to the lemmas
discussed above about ``LinearMap`` and ``Submodule``.
BOTH: -/
-- QUOTE:
def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
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

Complete lattice structure and internal direct sums
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

An important benefit of having a type ``Submodule K V`` instead of a predicate
``IsSubmodule : Set V → Prop`` is that one can easily endow ``Submodule K V`` with additional structure.
Importantly, it has the structure of a complete lattice structure with respect to
inclusion. For instance, instead of having a lemma stating that an intersection of
two subspaces of ``V`` is again a subspace, we
use the lattice operation ``⊓`` to construct the intersection. We can then apply arbitrary
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
In particular we can discuss the case of subspaces that are in (internal) direct sum.
In the case of two subspaces, we use the general purpose predicate ``IsCompl``
which makes sense for any bounded partially ordered type.
In the case of general families of subspaces we use ``DirectSum.IsInternal``.

EXAMPLES: -/
-- QUOTE:

-- If two subspaces are in direct sum then they span the whole space.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

-- If two subspaces are in direct sum then they intersect only at zero.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum
variable {ι : Type*} [DecidableEq ι]

-- If subspaces are in direct sum then they span the whole space.
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- If subspaces are in direct sum then they pairwise intersect only at zero.
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_iSupIndep.pairwiseDisjoint hij).eq_bot

-- Those conditions characterize direct sums.
#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

-- The relation with external direct sums: if a family of subspaces is
-- in internal direct sum then the map from their external direct sum into `V`
-- is a linear isomorphism.
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end
-- QUOTE.

/- TEXT:

Subspace spanned by a set
^^^^^^^^^^^^^^^^^^^^^^^^^

In addition to building subspaces out of existing subspaces, we can build them out
of any set ``s`` using ``Submodule.span K s`` which builds the smallest subspace
containing ``s``.
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

As an exercise, let us reprove one implication of ``Submodule.mem_sup``.
Remember that you can use the `module` tactic to close goals that follow from
the axioms relating the various algebraic operations on ``V``.
BOTH: -/
-- QUOTE:

example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  induction h using Submodule.span_induction with
/- EXAMPLES:
  | mem y h =>
      sorry
  | zero =>
      sorry
  | add x y hx hy hx' hy' =>
      sorry
  | smul a x hx hx' =>
      sorry
SOLUTIONS: -/
  | mem x h =>
      rcases h with (hx|hx)
      · use x, hx, 0, T.zero_mem
        module
      · use 0, S.zero_mem, x, hx
        module
  | zero =>
      use 0, S.zero_mem, 0, T.zero_mem
      module
  | add x y hx hy hx' hy' =>
      rcases hx' with ⟨s, hs, t, ht, rfl⟩
      rcases hy' with ⟨s', hs', t', ht', rfl⟩
      use s + s', S.add_mem hs hs', t + t', T.add_mem ht ht'
      module
  | smul a x hx hx' =>
      rcases hx' with ⟨s, hs, t, ht, rfl⟩
      use a • s, S.smul_mem a hs, a • t, T.smul_mem a ht
      module

-- QUOTE.
/- TEXT:

Pushing and pulling subspaces
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As promised earlier, we now describe how to push and pull subspaces by linear maps.
As usual in Mathlib, the first operation is called ``map`` and the second one is called
``comap``.
BOTH: -/
-- QUOTE:

section

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)
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

example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- or `rfl`
-- QUOTE.


/- TEXT:
Note that we cannot write ``φ.ker`` instead of ``LinearMap.ker φ`` because ``LinearMap.ker`` also
applies to classes of maps preserving more structure, hence it does not expect an argument
whose type starts with ``LinearMap``, hence dot notation doesn’t work here.
However we were able to use the other flavor of dot notation in the right-hand side. Because
Lean expects a term with type ``Submodule K V`` after elaborating the left-hand side, it interprets
``.comap`` as ``Submodule.comap``.

The following lemmas give the key relations between those submodule and the properties of ``φ``.
BOTH: -/
-- QUOTE:

open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm
-- QUOTE.
/- TEXT:
As an exercise, let us prove the Galois connection property for ``map`` and ``comap``.
One can use the following lemmas but this is not required since they are true by definition.
BOTH: -/
-- QUOTE:

#check Submodule.mem_map_of_mem
#check Submodule.mem_map
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h - ⟨x, hx, rfl⟩
    exact h hx
-- QUOTE.

/- TEXT:
Quotient spaces
^^^^^^^^^^^^^^^

Quotient vector spaces use the general quotient notation (typed with ``\quot``, not the ordinary
``/``).
The projection onto a quotient space is ``Submodule.mkQ`` and the universal property is
``Submodule.liftQ``.
BOTH: -/
-- QUOTE:

variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example : ker E.mkQ = E := E.ker_mkQ

example : range E.mkQ = ⊤ := E.range_mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange

-- QUOTE.
/- TEXT:
As an exercise, let us prove the correspondence theorem for subspaces of quotient spaces.
Mathlib knows a slightly more precise version as ``Submodule.comapMkQRelIso``.
BOTH: -/
-- QUOTE:

open Submodule

#check Submodule.map_comap_eq
#check Submodule.comap_map_eq

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
/- EXAMPLES:
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
SOLUTIONS: -/
  toFun F := ⟨comap E.mkQ F, by
    conv_lhs => rw [← E.ker_mkQ, ← comap_bot]
    gcongr
    apply bot_le⟩
  invFun P := map E.mkQ P
  left_inv P := by
    dsimp
    rw [Submodule.map_comap_eq, E.range_mkQ]
    exact top_inf_eq P
  right_inv := by
    intro P
    ext x
    dsimp only
    rw [Submodule.comap_map_eq, E.ker_mkQ, sup_of_le_left]
    exact P.2
-- QUOTE.
