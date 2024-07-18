-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import MIL.Common

/- TEXT:
.. _matrices:

Matrices
------------------

.. index:: matrices


Courses in abstract algebra often start with groups and
then progress to rings, fields, and vector spaces. This involves some contortions when discussing
multiplication on rings since the multiplication operation does not come from a group structure
but many of the proofs carry over verbatim from group theory to this new setting.
The most common fix, when doing mathematics with pen and paper,
is to leave those proofs as exercises. A less efficient but safer and
more formalization-friendly way of proceeding is to use monoids. A *monoid* structure on a type `M`
is an internal composition law that is associative and has a neutral element.
Monoids are used primarily to accommodate both groups and the multiplicative structure of
rings. But there are also a number of natural examples; for instance, the set of natural numbers
equipped with addition forms a monoid.

From a practical point of view, you can mostly ignore monoids when using Mathlib. But you need
to know they exist when you are looking for a lemma by browsing Mathlib files. Otherwise, you
might end up looking for a statement in the group theory files when it is actually in the found
with monoids because it does not require elements to be invertible.

The type of monoid structures on a type ``M`` is written ``Monoid M``.
The function ``Monoid`` is a type class so it will almost always appear as an instance implicit
argument (in other words, in square brackets).
By default, ``Monoid`` uses multiplicative notation for the operation; for additive notation
use ``AddMonoid`` instead.
The commutative versions of these structures add the prefix ``Comm`` before ``Monoid``.
EXAMPLES: -/
-- QUOTE:
example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y
-- QUOTE.

/- TEXT:
Note that although ``AddMonoid`` is found in the library,
it is generally confusing to use additive notation with a non-commutative operation.

The type of morphisms between monoids ``M`` and ``N`` is called ``MonoidHom M N`` and written
``M →* N``. Lean will automatically see such a morphism as a function from ``M`` to ``N`` when
we apply it to elements of ``M``. The additive version is called ``AddMonoidHom`` and written
``M →+ N``.
EXAMPLES: -/
-- QUOTE:
example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero
-- QUOTE.

/- TEXT:
These morphisms are bundled maps, i.e. they package together a map and some of its properties.
Remember that :numref:`section_hierarchies_morphisms` explains bundled maps;
here we simply note the slightly unfortunate consequence that we cannot use ordinary function
composition to compose maps. Instead, we need to use ``MonoidHom.comp`` and ``AddMonoidHom.comp``.
EXAMPLES: -/
-- QUOTE:
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f
-- QUOTE.

/- TEXT:
Groups and their morphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^

We will have much more to say about groups, which are monoids with the extra
property that every element has an inverse.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_self x
-- QUOTE.

/- TEXT:

.. index:: group (tactic), tactics ; group

Similar to the ``ring`` tactic that we saw earlier, there is a ``group`` tactic that proves
any identity that holds in any group. (Equivalently, it proves the identities that hold in
free groups.)

EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group
-- QUOTE.

/- TEXT:
.. index:: abel, tactics ; abel

There is also a tactic for identities in commutative additive groups called ``abel``.

EXAMPLES: -/
-- QUOTE:
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel
-- QUOTE.

/- TEXT:
Interestingly, a group
morphism is nothing more than a monoid morphism between groups. So we can copy and paste one of our
earlier examples, replacing ``Monoid`` with ``Group``.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y
-- QUOTE.

/- TEXT:
Of course we do get some new properties, such as this one:
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x
-- QUOTE.

/- TEXT:
You may be worried that constructing group morphisms will require us to do unnecessary work since
the definition of monoid morphism enforces that neutral elements are sent to neutral elements
while this is automatic in the case of group morphisms. In practice the extra work is not hard,
but, to avoid it, there is a function building a group morphism from a function
between groups that is compatible with the composition laws.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h
-- QUOTE.

/- TEXT:
There is also a type ``MulEquiv`` of group (or monoid) isomorphisms denoted by ``≃*`` (and
``AddEquiv`` denoted by ``≃+`` in additive notation).
The inverse of ``f : G ≃* H`` is ``MulEquiv.symm f : H ≃* G``,
composition of ``f`` and ``g`` is ``MulEquiv.trans f g``, and
the identity isomorphism of ``G`` is ``M̀ulEquiv.refl G``.
Using anonymous projector notation, the first two can be written ``f.symm`` and
``f.trans g`` respectively.
Elements of this type are automatically coerced to morphisms and functions when necessary.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm
-- QUOTE.

/- TEXT:
One can use ``MulEquiv.ofBijective`` to build an isomorphism from a bijective morphism.
Doing so makes the inverse function noncomputable.
EXAMPLES: -/
-- QUOTE:
noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h
-- QUOTE.

/- TEXT:
Subgroups
^^^^^^^^^

Just as group morphisms are bundled, a subgroup of ``G`` is also a bundled structure consisting of
a set in ``G`` with the relevant closure properties.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx
-- QUOTE.

/- TEXT:
In the example above, it is important to understand that ``Subgroup G`` is the type of subgroups
of ``G``, rather than a predicate ``IsSubgroup H`` where ``H`` is an element of ``Set G``.
``Subgroup G`` is endowed with a coercion to ``Set G`` and a membership predicate on ``G``.
See :numref:`section_hierarchies_subobjects` for an explanation of how and why this is done.

Of course, two subgroups are the same if and only if they have the same elements. This fact
is registered for use with the ``ext`` tactic, which can be used to prove two subgroups are
equal in the same way it is used to prove that two sets are equal.

To state and prove, for example, that ``ℤ`` is an additive subgroup of ``ℚ``,
what we really want is to construct a term of type ``AddSubgroup ℚ`` whose projection to
``Set ℚ`` is ``ℤ``, or, more precisely, the image of ``ℤ`` in ``ℚ``.
EXAMPLES: -/
-- QUOTE:
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp
-- QUOTE.

/- TEXT:
Using type classes, Mathlib knows that a subgroup of a group inherits a group structure.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance
-- QUOTE.

/- TEXT:
This example is subtle. The object ``H`` is not a type, but Lean automatically coerces it to
a type by interpreting it as a subtype of ``G``.
So the above example can be restated more explicitly as:
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance
-- QUOTE.

/- TEXT:
An important benefit of having a type ``Subgroup G`` instead of a predicate
``IsSubgroup : Set G → Prop`` is that one can easily endow ``Subgroup G`` with additional structure.
Importantly, it has the structure of a complete lattice structure with respect to
inclusion. For instance, instead of having a lemma stating that an intersection of
two subgroups of ``G`` is again a subgroup, we
have used the lattice operation ``⊓`` to construct the intersection. We can then apply arbitrary
lemmas about lattices to the construction.

Let us check that the set underlying the infimum of two subgroups is indeed, by definition,
their intersection.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl
-- QUOTE.

/- TEXT:
It may look strange to have a different notation for what amounts to the intersection of the
underlying sets, but the correspondence does not carry over to the supremum operation and set
union, since a union of subgroups is not, in general, a subgroup.
Instead one needs to use the subgroup generated by the union, which is done
using ``Subgroup.closure``.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]
-- QUOTE.

/- TEXT:
Another subtlety is that ``G`` itself does not have type ``Subgroup G``,
so we need a way to talk about ``G`` seen as a subgroup of ``G``.
This is also provided by the lattice structure: the full subgroup is the top element of
this lattice.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial
-- QUOTE.

/- TEXT:
Similarly the bottom element of this lattice is the subgroup whose only element is the
neutral element.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot
-- QUOTE.

/- TEXT:
As an exercise in manipulating groups and subgroups, you can define the conjugate of a subgroup
by an element of the ambient group.
BOTH: -/
-- QUOTE:
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    use 1
    constructor
    exact H.one_mem
    group
-- BOTH:
  inv_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - ⟨h, h_in, rfl⟩
    use h⁻¹, H.inv_mem h_in
    group
-- BOTH:
  mul_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - - ⟨h, h_in, rfl⟩ ⟨k, k_in, rfl⟩
    use h*k, H.mul_mem h_in k_in
    group
-- BOTH:
-- QUOTE.

