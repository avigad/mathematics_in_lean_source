-- BOTH:

import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Localization.Basic
import MIL.Common


/- TEXT:
.. _rings:

Monoids and Groups
------------------

.. index:: ring (algebraic structure)

Rings, their units, morphisms and subrings
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The type of ring structures on a type ``R`` is ``Ring R``. The variant where multiplication is
assumed to be commutative is ``CommRing R``. We already saw that the ``ring`` tactic will prove
any equality that uses only the axioms of commutative rings.
-/
example {R : Type*} [CommRing R] (x y : R) : (x + y)^2 = x^2 + y^2 + 2*x*y := by ring

/-
More exotic variants do not ask that ``R`` equipped with addition form a group, but only an additive
monoid. The corresponding type classes are ``Semiring R`` and ``CommSemiring R``.
Arguably the most important motivation is to include natural numbers and related types such as
functions taking values in natural number.
The next important example is the type of ideals in a ring, which will be discussed below.
In particular the name of the ``ring`` tactic is doubly misleading: it does assume commutativity
but a ``CommSemiring`` is enough.
-/

example (x y : ℕ) : (x + y)^2 = x^2 + y^2 + 2*x*y := by ring

/-
There also versions that do not assume existence of a multiplicative unit or associativity of
multiplication but we will not discuss those.

It is important to realize that several concepts that are traditionaly taught in an introduction
to ring theory are actually about the underlying multiplicative monoid.
From a practical point of view, you can almost ignore this when using Mathlib. But you need
to know they exist when looking for a lemma by browsing Mathlib files. Indeed you may be looking
in ring theory files for a statement which is actually located in a monoid file because it deals
only with multiplication.

The most prominent example is the definition of units in a ring. Every (multiplicative) monoid ``M``
has a predicate ``IsUnit : M → Prop`` asserting existence of a two-sided inverse, and a
type ``Units M`` of units, with notation ``Mˣ`` and a coercion to ``M``.
It bundles an invertible element, its inverse and properties than ensure they are inverse of each
other.
This implementation detail is mostly relevant only when defining computable functions. In most
situations one can use ``IsUnit.unit {x : M} : IsUnit x → Mˣ`` to build a unit.
In the commutative case, one also has ``Units.mkOfMulEqOne (x y : M) : x * y = 1 → Mˣ``
which builds ``x`` seen as unit.
-/

example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {M : Type*} [Monoid M] {x : Mˣ} : (x : M)*x⁻¹ = 1 := Units.mul_inv x

example {M : Type*} [Monoid M] : Group Mˣ := inferInstance

/-
The type of ring morphisms between two (semi)-rings ``R`` and ``S`` is ``RingHom R S``,
with notation ``R →+* S``.

-/

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y := f.map_add x y

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f

/-
As with submonoids and subgroups, there is a ``Subring R`` type for subrings of a ring ``R``,
but is a lot less useful than subgroups since those are not the right object to quotient by.
-/

example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance

/-
Also notice that ``RingHom.range`` produces a subring.

Ideals and quotients
^^^^^^^^^^^^^^^^^^^^

For historical reasons, Mathlib only has a theory of ideals for commutative rings
(it was originally developped in the context of rushing towards foundations of modern
algebraic geometry). So in this section we work with commutative (semi)rings.
Ideals of ``R`` are defined as submodules of ``R`` seen as an ``R``-module. This notion will
be covered only in the linear algebra chapter, but this implementation detail can mostly be
safely ignored since most relevant lemmas are restated in the special context of ideals.
However dot notation won't always work as expected. For instance one cannot replace
``Ideal.Quotient.mk I`` by ``I.Quotient.mk`` in the snippet below because the parser
immediately replaces the ``Ideal R`` with ``Submodule R R``.
-/

example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R⧸I :=
  Ideal.Quotient.mk I

/-
The universal property of quotient rings is ``Ideal.Quotient.lift``
-/
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (H : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
  Ideal.Quotient.lift I f H

/-
In particular it leads to the first isomorphism theorem for rings.
-/

theorem RingHom.ker_rangeRestrict {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    RingHom.ker f.rangeRestrict = RingHom.ker f :=
  Ideal.ext fun _ ↦ ⟨fun h ↦ congr(((↑) : RingHom.range f → S) $h), fun h ↦ Subtype.ext h⟩

noncomputable def RingHom.quotientKerEquivRange {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : R ⧸ (RingHom.ker f) ≃+* f.range :=
  (Ideal.quotEquivOfEq f.ker_rangeRestrict.symm).trans
  (RingHom.quotientKerEquivOfSurjective (f.rangeRestrict_surjective))

/-
One can use ring morphisms to push or pull ideals using ``Ideal.map`` and ``Ideal.comap``. As usual,
the later is more convenient to use since it does not involve an existential quantifier.
This explains why it is used to state the condition allowing to build morphisms between quotient
rings.
-/

example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J f H


/-
One subtle point to understand is that the type ``R ⧸ I`` really depends on ``I``
(up to definitional equality), so have a proof that two ideals ``I`` and ``J`` are equal is not
enough to make the corresponding quotients equal. However the universal properties does give
an isomorphism in this case.
-/

example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq h

/-
The Chinese remainder theorem
-/

/-
Localization
^^^^^^^^^^^^

Localization creates inverses for certain elements in a ring. For instance localizing ``ℤ``
at every non-zero element gives the field ``ℚ``. Actually the core construction takes place for
monoids.
-/

#check Localization

/-

-/
#check IsLocalization.lift

/-
Algebras and polynomials
^^^^^^^^^^^^^^^^^^^^^^^^

Given a commutative (semi)ring ``R``, an algebra over ``R`` is a semiring ``A`` equipped
with a ring morphism whose image commutes with every element of ``A``. This is encoded as
a type class ``Algebra R A``.
The morphism from ``R`` to ``A`` is called the structure map and is ``algebraMap R A : R →*+ A``
in Lean. Multiplication of ``a : A`` by ``algebraMap R A r`` for some ``r : R`` is called the scalar
multiplication of ``a`` by ``r`` and denoted by ``r • a``.

Note that this notion of algebra is sometimes called an associate unital algebra to emphasis the
existence of more general notions of algebra whose definition is less concise.

Very important examples of non-commutative algebras include endomorphisms algebra (or square
matrices algebras), and those will be covered in the linear algebra chapter. In this chapter we
will only discuss the most important commutative algebras: polynomials.

The fact that ``algebraMap R A`` is ring morphism packages a lot of properties of scalar
multiplication, such as the following ones.
-/

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r + r') • a = r • a + r' • a :=
  add_smul r r' a

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r * r') • a = r • r' • a :=
  mul_smul r r' a

/-
The morphisms of ``R`` algebras between two ``R``-algebras ``A`` and ``B`` are ring morphisms
which commute with scalar multiplication by elements of ``R``. They are bundled morphism
with type ``AlgHom R A B`` which is denoted by ``A →ₐ[R] B``.
-/

/-


We start with univariate polynomials. The algbera of univariate polynomials with coefficients
in ``R`` is ``Polynomial R`` which is denoted by ``R[X]`` as soon as one opens the ``Polynomial``
namespace. The algebra structure map from ``R`` to ``R[X]`` is denoted by ``C``, which stands for
"constant" since the corresponding polynomial functions are always constant. The indeterminate
is denoted by ``X``.
-/
noncomputable section Polynomials

open Polynomial

example {R : Type*} [CommRing R] : R[X] := X

example {R : Type*} [CommRing R] (r : R) := X - C r

/-
In the first example above, it is crucial that we give the expected type to Lean since it
has no way to guess it from the body of the definition. In the second example, the target polynomial
algebra can be inferred from our use of ``C r`` since the type of ``r`` is known.

Polynomial give rise to polynomial functions. In particular they can be evaluated on ``R``
using ``Poynomial.eval``.
-/

example {R : Type*} [CommRing R] (P: R[X]) (x : R) := P.eval x

#check Polynomial.root_X_sub_C

#check Polynomial.comp

end Polynomials
#check MvPolynomial
