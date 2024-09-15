-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:

.. _matrices_bases_dimension:

Matrices, bases and dimension
-----------------------------

.. _matrices:

Matrices
^^^^^^^^

.. index:: matrices

TODO: make text for this section

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
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]

variable (φ : V →ₗ[K] W)

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

open LinearMap

#check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

open Matrix -- get access to the ``*ᵥ`` notation for multiplication between matrices and vectors.

example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v
end
-- QUOTE.

-- TODO: Need some exercises for this section

/- TEXT:

Dimension
^^^^^^^^^

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

-- TODO: Decide what to do about the topics below.
/-


Multilinear algebra (multilinear maps, alternating maps, quadratic forms,
inner products, matrix representation, spectral theorem, tensor products)

Modules over rings


in Mathlib/RingTheory/Ideal/Operations.lean:
instance Submodule.moduleSubmodule {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] :
Module (Ideal R) (Submodule R M)

-/
