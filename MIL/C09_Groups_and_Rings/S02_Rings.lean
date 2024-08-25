-- BOTH:
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Analysis.Complex.Polynomial.Basic
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
assumed to be commutative is ``CommRing R``. We have already seen that the ``ring`` tactic will
prove any equality that follows from the axioms of a commutative ring.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
-- QUOTE.

/- TEXT:
More exotic variants do not require that the addition on ``R`` forms a group but only an additive
monoid. The corresponding type classes are ``Semiring R`` and ``CommSemiring R``.
The type of natural numbers is an important instance of ``CommSemiring R``, as is any type
of functions taking values in the natural numbers.
Another important example is the type of ideals in a ring, which will be discussed below.
The name of the ``ring`` tactic is doubly misleading, since it assumes commutativity but works
in semirings as well. In other words, it applies to any ``CommSemiring``.
EXAMPLES: -/
-- QUOTE:
example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
-- QUOTE.

/- TEXT:
There are also versions of the ring and semiring classes that do not assume the existence of a
multiplicative unit or
the associativity of multiplication. We will not discuss those here.

Some concepts that are traditionally taught in an introduction to ring theory are actually about
the underlying multiplicative monoid.
A prominent example is the definition of the units of a ring. Every (multiplicative) monoid ``M``
has a predicate ``IsUnit : M → Prop`` asserting existence of a two-sided inverse, a
type ``Units M`` of units with notation ``Mˣ``, and a coercion to ``M``.
The type ``Units M`` bundles an invertible element with its inverse as well as properties than ensure
that each is indeed the inverse of the other.
This implementation detail is relevant mainly when defining computable functions. In most
situations one can use ``IsUnit.unit {x : M} : IsUnit x → Mˣ`` to build a unit.
In the commutative case, one also has ``Units.mkOfMulEqOne (x y : M) : x * y = 1 → Mˣ``
which builds ``x`` seen as unit.
EXAMPLES: -/
-- QUOTE:
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x

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
The isomorphism variant is ``RingEquiv``, with notation ``≃+*``.

As with submonoids and subgroups, there is a ``Subring R`` type for subrings of a ring ``R``,
but this type is a lot less useful than the type of subgroups since one cannot quotient a ring by
a subring.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance
-- QUOTE.

/- TEXT:
Also notice that ``RingHom.range`` produces a subring.

Ideals and quotients
^^^^^^^^^^^^^^^^^^^^

For historical reasons, Mathlib only has a theory of ideals for commutative rings.
(The ring library was originally developed to make quick progress toward the foundations of modern
algebraic geometry.) So in this section we will work with commutative (semi)rings.
Ideals of ``R`` are defined as submodules of ``R`` seen as ``R``-modules. Modules will
be covered later in a chapter on linear algebra, but this implementation detail can mostly be
safely ignored since most (but not all) relevant lemmas are restated in the special context of
ideals. But anonymous projection notation won't always work as expected. For instance,
one cannot replace ``Ideal.Quotient.mk I`` by ``I.Quotient.mk`` in the snippet below because there
are two ``.``s and so it will parse as ``(Ideal.Quotient I).mk``; but ``Ideal.Quotient`` by itself
doesn't exist.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

example {R : Type*} [CommRing R] {a : R} {I : Ideal R} :
    Ideal.Quotient.mk I a = 0 ↔ a ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem
-- QUOTE.

/- TEXT:
The universal property of quotient rings is ``Ideal.Quotient.lift``.
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
example {R S : Type*} [CommRing R] [CommRing S](f : R →+* S) :
    R ⧸ RingHom.ker f ≃+* f.range :=
  RingHom.quotientKerEquivRange f
-- QUOTE.

/- TEXT:
Ideals form a complete lattice structure with the inclusion relation, as well as a semiring
structure. These two structures interact nicely.
EXAMPLES: -/
section
-- QUOTE:
variable {R : Type*} [CommRing R] {I J : Ideal R}

-- EXAMPLES:
example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ J := Ideal.mul_le_left

example : I * J ≤ I := Ideal.mul_le_right

example : I * J ≤ I ⊓ J := Ideal.mul_le_inf
-- QUOTE.

end

/- TEXT:
One can use ring morphisms to push ideals forward and pull them back using ``Ideal.map`` and
``Ideal.comap``, respectively. As usual,
the latter is more convenient to use since it does not involve an existential quantifier.
This explains why it is used to state the condition that allows us to build morphisms between
quotient rings.
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J f H
-- QUOTE.

/- TEXT:
One subtle point is that the type ``R ⧸ I`` really depends on ``I``
(up to definitional equality), so having a proof that two ideals ``I`` and ``J`` are equal is not
enough to make the corresponding quotients equal. However, the universal properties do provide
an isomorphism in this case.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq h
-- QUOTE.

/- TEXT:
We can now present the Chinese remainder isomorphism as an example. Pay attention to the difference
between the indexed infimum symbol ``⨅`` and the big product of types symbol ``Π``. Depending on
your font, those can be pretty hard to distinguish.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  Ideal.quotientInfRingEquivPiQuotient f hf
-- QUOTE.

/- TEXT:
The elementary version of the Chinese remainder theorem, a statement about ``ZMod``, can be easily
deduced from the previous one:
BOTH: -/
-- QUOTE:
open BigOperators PiNotation

-- EXAMPLES:
example {ι : Type*} [Fintype ι] (a : ι → ℕ) (coprime : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  ZMod.prodEquivPi a coprime
-- QUOTE.

/- TEXT:
As a series of exercises, we will reprove the Chinese remainder theorem in the general case.

We first need to define the map appearing in the theorem, as a ring morphism, using the
universal property of quotient rings.
BOTH: -/
section
-- QUOTE:
variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

#check Pi.ringHom
#check ker_Pi_Quotient_mk

/-- The homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i`` featured in the Chinese
  Remainder Theorem. -/
def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  Ideal.Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Ideal.Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])
-- QUOTE.
-- BOTH:

/- TEXT:
Make sure the following next two lemmas can be proven by ``rfl``.
BOTH: -/
-- QUOTE:
lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rfl
-- BOTH:

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rfl
-- QUOTE.
-- BOTH:

/- TEXT:
The next lemma proves the easy half of the Chinese remainder theorem, without any assumption on
the family of ideals. The proof is less than one line long.
EXAMPLES: -/
-- QUOTE:
#check injective_lift_iff

-- BOTH:
lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [chineseMap, injective_lift_iff, ker_Pi_Quotient_mk]
-- QUOTE.
-- BOTH:

/- TEXT:
We are now ready for the heart of the theorem, which will show the surjectivity
of our ``chineseMap``. First we need to know the different ways one can express the coprimality
(also called co-maximality assumption). Only the first two will be needed below.
EXAMPLES: -/
-- QUOTE:
#check IsCoprime
#check isCoprime_iff_add
#check isCoprime_iff_exists
#check isCoprime_iff_sup_eq
#check isCoprime_iff_codisjoint
-- QUOTE.

/- TEXT:
We take the opportunity to use induction on ``Finset``. Relevant lemmas on ``Finset`` are given
below.
Remember that the ``ring`` tactic works for semirings and that the ideals of a ring form a semiring.
EXAMPLES: -/
-- QUOTE:
#check Finset.mem_insert_of_mem
#check Finset.mem_insert_self

-- BOTH:
theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
/- EXAMPLES:
        1 = I + K                  := sorry
        _ = I + K * (I + J i)      := sorry
        _ = (1 + K) * I + K * J i  := sorry
        _ ≤ I + K ⊓ J i            := sorry
SOLUTIONS: -/
        1 = I + K                  := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
        _ = I + K * (I + J i)      := by rw [hf i (Finset.mem_insert_self i s), mul_one]
        _ = (1 + K) * I + K * J i  := by ring
        _ ≤ I + K ⊓ J i            := by gcongr ; apply mul_le_left ; apply mul_le_inf

-- QUOTE.

/- TEXT:
We can now prove surjectivity of the map appearing in the Chinese remainder theorem.
BOTH: -/
-- QUOTE:
lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
    (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  intro g
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
      intros j hj
      exact hI _ _ (by simpa [ne_comm, isCoprime_iff_add] using hj)
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rcases isCoprime_iff_exists.mp (isCoprime_Inf hI') with ⟨u, hu, e, he, hue⟩
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, eq_zero_iff_mem.mpr hu]
    · exact fun j hj ↦ eq_zero_iff_mem.mpr (he j hj)
-- BOTH:
  choose e he using key
  use mk _ (∑ i, f i * e i)
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext i
  rw [chineseMap_mk', map_sum, Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intros j hj
    simp [(he j).2 i hj.symm]
-- QUOTE.
-- BOTH:

/- TEXT:
Now all the pieces come together in the following:
BOTH: -/
-- QUOTE:
noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
    chineseMap f with }
-- QUOTE.

end

/- TEXT:
Algebras and polynomials
^^^^^^^^^^^^^^^^^^^^^^^^

Given a commutative (semi)ring ``R``, an *algebra over* ``R`` is a semiring ``A`` equipped
with a ring morphism whose image commutes with every element of ``A``. This is encoded as
a type class ``Algebra R A``.
The morphism from ``R`` to ``A`` is called the structure map and is denoted
``algebraMap R A : R →+* A`` in Lean.
Multiplication of ``a : A`` by ``algebraMap R A r`` for some ``r : R`` is called the scalar
multiplication of ``a`` by ``r`` and denoted by ``r • a``.
Note that this notion of algebra is sometimes called an *associative unital algebra* to emphasize the
existence of more general notions of algebra.

The fact that ``algebraMap R A`` is ring morphism packages together a lot of properties of scalar
multiplication, such as the following:
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
The morphisms between two ``R``-algebras ``A`` and ``B`` are ring morphisms
which commute with scalar multiplication by elements of ``R``. They are bundled morphisms
with type ``AlgHom R A B``, which is denoted by ``A →ₐ[R] B``.

Important examples of non-commutative algebras include algebras of endomorphisms and
algebras of square matrices, both of which will be covered in the chapter on linear algebra.
In this chapter we will discuss one of the most important examples of a commutative algebra,
namely, polynomial algebras.

The algebra of univariate polynomials with coefficients in ``R`` is called ``Polynomial R``,
which can be written as ``R[X]`` as soon as one opens the ``Polynomial`` namespace.
The algebra structure map from ``R`` to ``R[X]`` is denoted by ``C``,
which stands for "constant" since the corresponding
polynomial functions are always constant. The indeterminate is denoted by ``X``.
EXAMPLES: -/
section Polynomials
-- QUOTE:
open Polynomial

example {R : Type*} [CommRing R] : R[X] := X

example {R : Type*} [CommRing R] (r : R) := X - C r
-- QUOTE.

/- TEXT:
In the first example above, it is crucial that we give Lean the expected type since it cannot be
determined from the body of the definition. In the second example, the target polynomial
algebra can be inferred from our use of ``C r`` since the type of ``r`` is known.

Because ``C`` is a ring morphism from ``R`` to ``R[X]``, we can use all ring morphisms lemmas
such as ``map_zero``, ``map_one``, ``map_mul``, and ``map_pow`` before computing in the ring
``R[X]``. For example:
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X ^ 2 - C (r ^ 2) := by
  rw [C.map_pow]
  ring
-- QUOTE.

/- TEXT:
You can access coefficients using ``Polynomial.coeff``
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (r:R) : (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] : (X ^ 2 + 2 * X + C 3 : R[X]).coeff 1 = 2 := by simp
-- QUOTE.

/- TEXT:
Defining the degree of a polynomial is always tricky because of the special case of the zero
polynomial. Mathlib has two variants: ``Polynomial.natDegree : R[X] → ℕ`` assigns degree
``0`` to the zero polynomial, and ``Polynomial.degree : R[X] → WithBot ℕ`` assigns ``⊥``.
In the latter, ``WithBot ℕ`` can be seen as ``ℕ ∪ {-∞}``, except that ``-∞`` is denoted ``⊥``,
the same symbol as the bottom element in a complete lattice. This special value is used as the
degree of the zero polynomial, and it is absorbent for addition. (It is almost absorbent for
multiplication, except that ``⊥ * 0 = 0``.)

Morally speaking, the ``degree`` version is the correct one. For instance, it allows us to state
the expected formula for the degree of a product (assuming the base ring has no zero divisor).
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
However, ``ℕ`` is much nicer to use than ``WithBot ℕ``, so Mathlib makes both versions available
and provides lemmas to convert between them. Also, ``natDegree`` is the more convenient definition
to use when computing the degree of a composition. Composition of polynomial is ``Polynomial.comp``
and we have:
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    natDegree (comp p q) = natDegree p * natDegree q :=
  Polynomial.natDegree_comp
-- QUOTE.

/- TEXT:
Polynomials give rise to polynomial functions: any polynomial can be evaluated on ``R``
using ``Polynomial.eval``.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (P: R[X]) (x : R) := P.eval x

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp
-- QUOTE.

/- TEXT:
In particular, there is a predicate, ``IsRoot``, that holds for elements ``r`` in ``R`` where a
polynomial vanishes.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (P : R[X]) (r : R) : IsRoot P r ↔ P.eval r = 0 := Iff.rfl
-- QUOTE.

/- TEXT:
We would like to say that, assuming ``R`` has no zero divisor, a polynomial has at most as many
roots as its degree, where the roots are counted with multiplicities.
But once again the case of the zero polynomial is painful.
So Mathlib defines ``Polynomial.roots`` to send a polynomial ``P`` to a multiset,
i.e. the finite set that is defined to be empty if ``P`` is zero and the roots of ``P``,
with multiplicities, otherwise. This is defined only when the underlying ring is a domain
since otherwise the definition does not have good properties.
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] [IsDomain R] (r : R) : (X - C r).roots = {r} :=
  roots_X_sub_C r

example {R : Type*} [CommRing R] [IsDomain R] (r : R) (n : ℕ):
    ((X - C r) ^ n).roots = n • {r} :=
  by simp
-- QUOTE.

/- TEXT:
Both ``Polynomial.eval`` and ``Polynomial.roots`` consider only the coefficients ring. They do not
allow us to say that ``X ^ 2 - 2 : ℚ[X]`` has a root in ``ℝ`` or that ``X ^ 2 + 1 : ℝ[X]`` has a root in
``ℂ``. For this, we need ``Polynomial.aeval``, which will evaluate ``P : R[X]`` in any ``R``-algebra.
More precisely, given a semiring ``A`` and an instance of ``Algebra R A``, ``Polynomial.aeval`` sends
every element of ``a`` along the ``R``-algebra morphism of evaluation at ``a``. Since ``AlgHom``
has a coercion to functions, one can apply it to a polynomial.
But ``aeval`` does not have a polynomial as an argument, so one cannot use dot notation like in
``P.eval`` above.
EXAMPLES: -/
-- QUOTE:
example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp

-- QUOTE.
/- TEXT:
The function corresponding to ``roots`` in this context is ``aroots`` which takes a polynomial
and then an algebra and outputs a multiset (with the same caveat about the zero polynomial as
for ``roots``).
EXAMPLES: -/
-- QUOTE:
open Complex Polynomial

example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {Complex.I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    have key : (C I * C I : ℂ[X]) = -1 := by simp [← C_mul]
    rw [C_neg]
    linear_combination key
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
#check (Complex.ofRealHom : ℝ →+* ℂ)

example : (X ^ 2 + 1 : ℝ[X]).eval₂ Complex.ofRealHom Complex.I = 0 := by simp
-- QUOTE.

/- TEXT:
Let us end by mentioning multivariate polynomials briefly. Given a commutative semiring ``R``,
the ``R``-algebra of polynomials with coefficients in ``R`` and indeterminates indexed by
a type ``σ`` is ``MVPolynomial σ R``. Given ``i : σ``, the corresponding polynomial is
``MvPolynomial.X i``. (As usual, one can open the ``MVPolynomial`` namespace to shorten this
to ``X i``.)
For instance, if we want two indeterminates we can use
``Fin 2`` as ``σ`` and write the polynomial defining the unit circle in :math:`\mathbb{R}^2`` as:
EXAMPLES: -/
-- QUOTE:
open MvPolynomial

def circleEquation : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2 - 1
-- QUOTE.

/- TEXT:
Recall that function application has a very high precedence so the expression above is read as
``(X 0) ^ 2 + (X 1) ^ 2 - 1``.
We can evaluate it to make sure the point with coordinates :math:`(1, 0)` is on the circle.
Recall the ``![...]`` notation denotes elements of ``Fin n → X`` for some natural number ``n``
determined by the number of arguments and some type ``X`` determined by the type of arguments.
EXAMPLES: -/
-- QUOTE:
example : MvPolynomial.eval ![0, 1] circleEquation = 0 := by simp [circleEquation]
-- QUOTE.

end Polynomials
