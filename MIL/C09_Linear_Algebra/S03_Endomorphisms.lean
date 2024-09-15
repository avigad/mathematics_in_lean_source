-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


/- TEXT:

Endomorphisms
--------------

An important special case of linear maps are endomorphisms: linear maps from a vector space to itself.
They are interesting because they form a ``K``-algebra. In particular we can evaluate polynomials
with coefficients in ``K`` on them, and they can have eigenvalues and eigenvectors.

Mathlib uses the abreviation ``Module.End K V := V →ₗ[K] V`` which is convenient when
using a lot of these (especially after opening the ``Module`` namespace).

EXAMPLES: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


section endomorphisms
open Polynomial Module LinearMap

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
As an exercise manipulating endomorphisms, subspaces and polynomials, let us prove the
(binary) kernels lemma: for any endomorphism :math:`φ` and any two relatively
prime polynomials :math:`P` and :math:`Q`, we have :math:`\ker P(φ) ⊕ \ker Q(φ) = \ker \big(PQ(φ)\big)`.

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
associated to an endomorphism :math:`φ` and a scalar :math:`a` is the kernel of :math:`φ - aId`.
The first thing to understand is how to spell :math:`aId`. We could use
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
