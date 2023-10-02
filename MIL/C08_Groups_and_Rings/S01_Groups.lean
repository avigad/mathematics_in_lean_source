
-- BOTH:
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

/- TEXT:
.. _groups:

Monoids and Groups
------------------

.. index:: monoid
.. index:: group (algebraic structure)


Algebra courses often start the description of fundamental algebraic structures with groups and
then progress to rings, fields and vector spaces. This involves some contortions when discussing
multiplication on rings since this operation does not come from a group structure, and yet many
proofs from the group theory chapter carry over verbatim in this new setting. The most common fix
on paper is to leave those proofs as exercises. A less efficient but safer and
formalization-friendlier of proceeding is to discuss monoids. A monoid structure on a type `M`
is an internal composition law which is associative and has a neutral element.
The main use of this structure is to accommodate both groups and the multiplicative structure
rings. But there are also a number of natural examples, for instance natural numbers equipped with
addition form a monoid.

From a practical point of view, you can almost ignore monoids when using Mathlib. But you need
to know they exist when looking for a lemma by browsing Mathlib files. Indeed you may be looking
in group theory files for a statement which is actually located in a monoid file because it does not
require elements to be invertible.

The type of monoids structures on a type ``M`` with multiplicative notation is ``Monoid M``.
The function ``Monoid`` is a type class so it will almost always appear as an instance implicit
argument (ie. in square brackets). The additive notation version is ``AddMonoid``.
The commutative versions add the ``Comm`` prefix before ``Monoid``.
-/

example {M : Type*} [Monoid M] (x : M) : x*1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

/- Note in particular that ``AddMonoid`` exists, although it would be very confusing to use
additive notation in a non-commutative case on paper.

The type of morphisms between monoids ``M`` and ``N`` is called ``MonoidHom M N`` and denoted by
``M →* N``. Lean will automatically see such a morphism as a function from ``M`` to ``N`` when
users apply them to elements of ``M``. The additive version is called ``AddMonoidHom`` and denoted
by ``M →+ N``.
-/

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
f.map_zero

/-
Those morphisms are bundled maps, ie package together a map and some properties of this map.
Section :numref:`_section_hierarchies_morphisms` contain a lot more explanations about that.
Here we simply note the slightly unfortunate consequence that we cannot use ordinary function
composition. We need to use ``MonoidHom.comp`` and ``AddMonoidHom.comp``.

-/

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
  (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f
/-
After this brief excursion through monoids, we want to spend a lot more time with groups.
Compared to monoids, groups have the extra property that every element has an inverse.

-/

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_self x

/- Similar to the `ring` tactic that we saw earlier, there is a ``group`` tactic that proves
every identity which follows from the group axioms with any extra assumption
(hence one can see it as a tactic proving identities that hold in free groups). -/

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x*z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

/- And there is similar a tactic for identities in commutative additive groups called ``abel``. -/

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

/- We can now move to group morphism. Actually moving isn't the right word since a group
morphism is nothing but a monoid morphism between groups. So we can copy-paste one of our
earlier examples, replacing ``Monoid`` with ``Group``.
-/

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
f.map_mul x y

/- Of course we do get some new properties, such as -/

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
f.map_inv x

/- You may be worried that constructing group morphisms will involve unneeded work since
the definition of monoid morphism enforces that neutral elements are sent to neutral element
while this is automatic in the case of group morphisms. In practice the extra work is always
trivial but, just in case, there are functions building a group morphism from a function
between groups that is compatible with the composition laws.
-/

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) : G →* H :=
MonoidHom.mk' f h

/-
In the same way group morphisms are bundled, subgroups are also bundles made of a set in ``G``
and some stability properties.
-/

example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H :=
H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) : x⁻¹ ∈ H :=
H.inv_mem hx

/-
In the above example, it is important to understand that ``Subgroup G`` is the type of subgroups
of ``G``. It is endowed with a coercion to ``Set G`` and a membership predicate on ``G``.
See Section :numref:`section_hierarchies_subobjects` for explanations about why and how things are
set up like this.

If you want how to state and prove something like ``ℤ`` is an additive subgroup of ``ℚ`` then
the answer to constructor a term with type ``AddSubgroup ℚ`` whose projection to ``Set ℚ``
is ``ℤ``, or more precisely the image of ``ℤ`` in ``ℚ``.
-/

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

/-
An important benefit of having a type ``Subgroup G`` instead of a predicate
``IsSubgroup : Set G → Prop`` is that one can easily endow it with additional structure.
Crucially this includes a complete lattice structure with respect to inclusion.
For instance, instead of having a lemma stating that an intersection of two subgroups of ``G``, we
have the lattice operation ``⊓`` and all lemmas about lattices are readily available.

Let us check that the set underlying the infimum of two subgroups is indeed, by definition,
their intersection.
-/

example {G : Type*} [Group G] (H H' : Subgroup G) :
  ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl

/-
In the intersection case it may look strange to have a different notation, but this is somehow
an accident which does not carry over to the supremum operation since a union of subgroup
is not a subgroup. Instead one needs to use the subgroup generated by the union, which is done
using ``Subgroup.closure``.
-/

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  simp [Subgroup.closure_union, Subgroup.closure_eq]

/-
Tying the previous two topics together, one can push forward and pull back subgroups using
group morphisms. The naming convention in Mathlib is to call those operations ``map``
and ``comap``. Those names are slightly strange but much shorter that push-forward or direct-image.
-/

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
Subgroup.comap f H'
/-
**TODO:**

Lagrange, Sylow
Permutation groups
Free groups, presentation
Group actions
Cayley
Cosets
Quotient groups
1er thm isomph

rings, mph, subring
ideals, quotients
Restes chinois
polynomials?
-/
