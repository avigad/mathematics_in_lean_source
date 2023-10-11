-- BOTH:

import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.ZMod.Quotient
import MIL.Common

noncomputable section

/- TEXT:
.. _rings:

Rings
-----

.. index:: ring (algebraic structure)

Rings, their units, morphisms and subrings
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The type of ring structures on a type ``R`` is ``Ring R``. The variant where multiplication is
assumed to be commutative is ``CommRing R``. We already saw that the ``ring`` tactic will prove
any equality that uses only the axioms of commutative rings.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (x y : R) : (x + y)^2 = x^2 + y^2 + 2*x*y := by ring

-- QUOTE.
/- TEXT:
More exotic variants do not ask that ``R`` equipped with addition form a group, but only an additive
monoid. The corresponding type classes are ``Semiring R`` and ``CommSemiring R``.
Arguably the most important motivation is to include natural numbers and related types such as
functions taking values in natural number.
The next important example is the type of ideals in a ring, which will be discussed below.
In particular the name of the ``ring`` tactic is doubly misleading: it does assume commutativity
but a ``CommSemiring`` is enough.
EXAMPLES: -/
-- QUOTE:

example (x y : ℕ) : (x + y)^2 = x^2 + y^2 + 2*x*y := by ring

-- QUOTE.
/- TEXT:
There also versions that do not assume existence of a multiplicative unit or associativity of
multiplication but we will not discuss those.

It is important to realize that several concepts that are traditionally taught in an introduction
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
EXAMPLES: -/
-- QUOTE:

example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {M : Type*} [Monoid M] {x : Mˣ} : (x : M)*x⁻¹ = 1 := Units.mul_inv x

example {M : Type*} [Monoid M] : Group Mˣ := inferInstance

-- QUOTE.
/- TEXT:
The type of ring morphisms between two (semi)-rings ``R`` and ``S`` is ``RingHom R S``,
with notation ``R →+* S``.

EXAMPLES: -/
-- QUOTE:

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y := f.map_add x y

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f

-- QUOTE.
/- TEXT:
As with submonoids and subgroups, there is a ``Subring R`` type for subrings of a ring ``R``,
but is a lot less useful than subgroups since those are not the right object to quotient by.
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance

-- QUOTE.
/- TEXT:
Also notice that ``RingHom.range`` produces a subring.

Ideals and quotients
^^^^^^^^^^^^^^^^^^^^

For historical reasons, Mathlib only has a theory of ideals for commutative rings
(it was originally developed in the context of rushing towards foundations of modern
algebraic geometry). So in this section we work with commutative (semi)rings.
Ideals of ``R`` are defined as submodules of ``R`` seen as an ``R``-module. This notion will
be covered only in the linear algebra chapter, but this implementation detail can mostly be
safely ignored since most relevant lemmas are restated in the special context of ideals.
However dot notation won't always work as expected. For instance one cannot replace
``Ideal.Quotient.mk I`` by ``I.Quotient.mk`` in the snippet below because the parser
immediately replaces the ``Ideal R`` with ``Submodule R R``.
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R⧸I :=
  Ideal.Quotient.mk I

-- QUOTE.
/- TEXT:
The universal property of quotient rings is ``Ideal.Quotient.lift``
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (H : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
  Ideal.Quotient.lift I f H

-- QUOTE.
/- TEXT:
In particular it leads to the first isomorphism theorem for rings.
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S](f : R →+* S) : R ⧸ RingHom.ker f ≃+* f.range :=
RingHom.quotientKerEquivRange f

-- QUOTE.
/- TEXT:
One can use ring morphisms to push or pull ideals using ``Ideal.map`` and ``Ideal.comap``. As usual,
the later is more convenient to use since it does not involve an existential quantifier.
This explains why it is used to state the condition allowing to build morphisms between quotient
rings.
EXAMPLES: -/
-- QUOTE:

example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J f H

-- QUOTE.
/- TEXT:
One subtle point to understand is that the type ``R ⧸ I`` really depends on ``I``
(up to definitional equality), so have a proof that two ideals ``I`` and ``J`` are equal is not
enough to make the corresponding quotients equal. However the universal properties does give
an isomorphism in this case.
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq h

-- QUOTE.
/- TEXT:
For instance we can now quote the Chinese remainder isomorphism.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
Ideal.quotientInfRingEquivPiQuotient f hf
-- QUOTE.
/- TEXT:
The elementary version about ``Zmod`` can be easily deduced from it:
EXAMPLES: -/
-- QUOTE:

open BigOperators

example {ι : Type*} [Fintype ι] (a : ι → ℕ) (coprime : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* ∀ i, ZMod (a i) :=
  ZMod.prodEquivPi a coprime

-- QUOTE.
/- TEXT:
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

The fact that ``algebraMap R A`` is ring morphism packages a lot of properties of scalar
multiplication, such as the following ones.
EXAMPLES: -/
-- QUOTE:

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r + r') • a = r • a + r' • a :=
  add_smul r r' a

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r * r') • a = r • r' • a :=
  mul_smul r r' a

-- QUOTE.
/- TEXT:
The morphisms of ``R`` algebras between two ``R``-algebras ``A`` and ``B`` are ring morphisms
which commute with scalar multiplication by elements of ``R``. They are bundled morphism
with type ``AlgHom R A B`` which is denoted by ``A →ₐ[R] B``.

Very important examples of non-commutative algebras include endomorphisms algebra (or square
matrices algebras), and those will be covered in the linear algebra chapter. In this chapter we
will only discuss the most important commutative algebras: polynomials.

The algebra of univariate polynomials with coefficients in ``R`` is ``Polynomial R`` which is
denoted by ``R[X]`` as soon as one opens the ``Polynomial`` namespace. The algebra structure map
from ``R`` to ``R[X]`` is denoted by ``C``, which stands for "constant" since the corresponding
polynomial functions are always constant. The indeterminate is denoted by ``X``.
EXAMPLES: -/
-- QUOTE:
section Polynomials

open Polynomial

example {R : Type*} [CommRing R] : R[X] := X

example {R : Type*} [CommRing R] (r : R) := X - C r

-- QUOTE.
/- TEXT:
In the first example above, it is crucial that we give the expected type to Lean since it
has no way to guess it from the body of the definition. In the second example, the target polynomial
algebra can be inferred from our use of ``C r`` since the type of ``r`` is known.

Because ``C`` is a ring morphism from ``R`` to ``R[X]``, we can use all ring morphisms lemmas
such as ``map_zero``, ``map_one``, ``map_mul``, ``map_pow`` before computing in the ring
``R[X]`` in the following example.
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X^2 - C (r ^ 2) := by
  rw [C.map_pow]
  ring

-- QUOTE.
/- TEXT:
You can access coefficients using ``Polynomial.coeff``
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [CommRing R](r:R) : (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] : (X^2 + 2*X + C 3 : R[X]).coeff 1 = 2 := by simp

-- QUOTE.
/- TEXT:
Defining the degree of a polynomial is always tricky because of the special case of the zero
polynomial. Mathlib has two variants: ``Polynomial.natDegree : R[X] → ℕ`` which assigns degree
``0`` to the zero polynomial, and ``Polynomial.degree : R[X] → WithBot ℕ`` where ``WithBot ℕ``
can be seen as ``ℕ ∪ {-∞}``, except ``-∞`` is denoted ``⊥`` (the same symbol as the bottom element
is a complete lattice for instance). This special value is used as the degree of the zero
polynomial, and it is absorbent for addition (and almost for multiplication, except that
``⊥ * 0 = 0``).

The ``degree`` version is morally the correct one. For instance it allows to state the expected
formula for the degree of a product (assuming the base ring has no zero divisor).
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    degree (p * q) = degree p + degree q :=
  Polynomial.degree_mul

-- QUOTE.
/- TEXT:
Whereas the version for ``natDegree`` needs to assume non-zero polynomials.
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  Polynomial.natDegree_mul hp hq

-- QUOTE.
/- TEXT:
However, ``ℕ`` is much nicer to use than ``WithBot ℕ``, hence both versions exists and there
are lemmas to convert between them. Also ``natDegree`` is the correct definition to use
when computing the degree of a composition. Composition of polynomial is ``Polynomial.comp``
and we have
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    natDegree (comp p q) = natDegree p * natDegree q :=
  Polynomial.natDegree_comp

-- QUOTE.
/- TEXT:
Polynomial give rise to polynomial functions. In particular they can be evaluated on ``R``
using ``Poynomial.eval``.
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [CommRing R] (P: R[X]) (x : R) := P.eval x

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp

-- QUOTE.
/- TEXT:
In particular there is ``IsRoot`` predicate that selects elements of ``r`` where a polynomial
evaluation vanishes.
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [CommRing R] (P : R[X]) (r : R) : IsRoot P r ↔ P.eval r = 0 := Iff.rfl

-- QUOTE.
/- TEXT:
We would like to say that, assuming ``R`` has no zero divisor, a polynomial has at most as many
roots, counted with multiplicities, as its degree. But again the case of the zero polynomial is
painful. So Mathlib defines ``Polynomial.roots`` as sending a polynomial ``P`` to a multiset,
ie. a finite set with multiplicities defined to be empty if ``P`` is zero and its roots
with multiplicities otherwise. This is defined only when the underlying ring is a domain
since otherwise it has no good property.
EXAMPLES: -/
-- QUOTE:

example {R : Type*} [CommRing R] [IsDomain R] (r : R) : (X - C r).roots = {r} :=
  roots_X_sub_C r

example {R : Type*} [CommRing R] [IsDomain R] (r : R) (n : ℕ): ((X - C r)^n).roots = n • {r} :=
  by simp

-- QUOTE.
/- TEXT:
Both `Polynomial.eval` and `Polynomial.roots` consider only the coefficients ring. They do not
allow to say that ``X^2 - 2 : ℚ[X]`` has a root in ``ℝ`` or that ``X^2 + 1 : ℝ[X]`` has a root in
``ℂ``. For this we need ``Polynomial.aeval`` which will evaluate ``P : R[X]`` in any ``R``-algebra.
More precisely, given a semiring ``A`` and a ``Algebra R A`` instance, ``Polynomial.aeval`` sends
every element of ``a`` on the ``R``-algebra morphism of evaluation at ``a``. Since ``AlgHom``
has a coercion to functions, one can apply it to a polynomial.
But ``aeval`` does not have a polynomial as an argument, so one cannot use dot notation like in
``P.eval`` above.
EXAMPLES: -/
-- QUOTE:

example : aeval Complex.I (X^2 + 1 : ℝ[X]) = 0 := by simp

-- QUOTE.
/- TEXT:
The function corresponding to ``roots`` in this context is ``aroots`` which takes a polynomial
and then an algebra and outputs a multiset (with the same caveat about the zero polynomial as
for ``roots``).
EXAMPLES: -/
-- QUOTE:
open Complex Polynomial

example : aroots (X^2 + 1 : ℝ[X]) ℂ = {I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    rw [C_neg]
    linear_combination show (C I * C I : ℂ[X]) = -1 by simp [← C_mul]
  have p_ne_zero : (X - C I) * (X - C (-I)) ≠ 0 := by
    intro H
    apply_fun eval 0 at H
    simp [eval] at H
  simp only [factored, roots_mul p_ne_zero, roots_X_sub_C]
  rfl

-- Mathlib knows about D'Alembert-Gauss theorem: ``ℂ`` is algebraically closed.
example : IsAlgClosed ℂ := inferInstance

-- QUOTE.
/- TEXT:
More generally, given an ring morphism ``f : R →+* S`` one can evaluate ``P : R[X]`` at a point
in ``S`` using ``Polynomial.eval₂``. This one produces an actual function from ``R[X]`` to ``S``
since it does not assume the existence of a ``Algebra R S`` instance, so dot notation works as
you would expect.
EXAMPLES: -/
-- QUOTE:

#check (Complex.ofReal : ℝ →+* ℂ)

example : (X^2 + 1 : ℝ[X]).eval₂ Complex.ofReal Complex.I = 0 := by simp

-- QUOTE.
/- TEXT:
Let us end by briefly mentioning multi-variate polynomials. Given a commutative semiring ``R``,
the ``R``-algebra of polynomial with coefficients in ``R`` and indeterminates indexed by
a type ``σ`` is ``MVPolynomial σ R``. Given ``i : σ``, the corresponding polynomial is
``MvPolynomial.X i`` (of course one can open the ``MVPolynomial`` namespace to shorten this
to ``X i``).
For instance, if we want two indeterminates we can use
``Fin 2`` as ``σ`` and write the polynomial defining the unit circle in :math:`\mathbb{R}^2`` as:
EXAMPLES: -/
-- QUOTE:

open MvPolynomial

def circleEquation : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2 - 1

-- QUOTE.
/- TEXT:
Recall that function application has a very high precedence so the above equation is read as
``(X 0) ^ 2 + (X 1) ^ 2 - 1``.

And we can evaluate it to make sure the point with coordinates :math:`(1, 0)` is on the circle.
Recall the ``![...]`` notation denotes elements of ``Fin n → X`` for some natural number ``n``
determined by the number of arguments and some type ``X`` determined by the type of arguments.
EXAMPLES: -/
-- QUOTE:

example : MvPolynomial.eval ![0, 1] circleEquation = 0 := by simp [circleEquation]

end Polynomials
-- QUOTE.
