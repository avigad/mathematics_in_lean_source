-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Data.Complex.FiniteDimensional

import MIL.Common

/- TEXT:

.. _matrices_bases_dimension:

Matrices, bases and dimension
-----------------------------

.. _matrices:

Matrices
^^^^^^^^

.. index:: matrices

Before introducing bases for abstract vector spaces, we go back to the much more elementary setup
of linear algebra in :math:`K^n` for some field :math:`K`.
Here the main objects are vectors and matrices.
For concrete vectors, one can use the ``![…]`` notation, where components are separated by commas.
For concrete matrices we can use the ``!![…]`` notation, lines are separated by semi-colons
and components of lines are separated by commas.
When entries have a computable type such as ``ℕ`` or ``ℚ``, we can use
the ``eval`` command to play with basic operations.

EXAMPLES: -/
-- QUOTE:

section matrices

-- Adding vectors
#eval ![1, 2] + ![3, 4]  -- ![4, 6]

-- Adding matrices
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- Multiplying matrices
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![13, 16; 29, 36]

-- QUOTE.
/- TEXT:
It is important to understand that this use of ``#eval`` is interesting only for
exploration, it is not meant to replace a computer algebra system such as Sage.
The data representation used here for matrices is *not* computationally
efficient in any way. It uses functions instead of arrays and is optimized for
proving, not computing.
The virtual machine used by ``#eval`` is also not optimized for this use.


Beware the matrix notation list rows but the vector notation
is neither a row vector nor a column vector. Multiplication of a matrix with a vector
from the left (resp. right) interprets the vector as a row (resp. column) vector.
This corresponds to operations
``Matrix.vecMul``, with notation ``ᵥ*`` and ``Matrix.mulVec``, with notation ` `*ᵥ``.
Those notations are scoped in the ``Matrix`` namespace that we therefore need to open.
EXAMPLES: -/
-- QUOTE:
open Matrix

-- matrices acting on vectors on the left
#eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

-- matrices acting on vectors on the left, resulting in a size one matrix
#eval !![1, 2] *ᵥ ![1, 1]  -- ![3]

-- matrices acting on vectors on the right
#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- ![9, 12]
-- QUOTE.
/- TEXT:
In order to generate matrices with identical rows or columns specified by a vector, we
use ``Matrix.replicateRow`` and ``Matrix.replicateCol``, with arguments the type indexing the
rows or columns and the vector.
For instance one can get single row or single column matrixes (more precisely matrices whose rows
or columns are indexed by ``Fin 1``).
EXAMPLES: -/
-- QUOTE:
#eval replicateRow (Fin 1) ![1, 2] -- !![1, 2]

#eval replicateCol (Fin 1) ![1, 2] -- !![1; 2]
-- QUOTE.
/- TEXT:
Other familiar operations include the vector dot product, matrix transpose, and,
for square matrices, determinant and trace.
EXAMPLES: -/
-- QUOTE:

-- vector dot product
#eval ![1, 2] ⬝ᵥ ![3, 4] -- `11`

-- matrix transpose
#eval !![1, 2; 3, 4]ᵀ -- `!![1, 3; 2, 4]`

-- determinant
#eval !![(1 : ℤ), 2; 3, 4].det -- `-2`

-- trace
#eval !![(1 : ℤ), 2; 3, 4].trace -- `5`


-- QUOTE.
/- TEXT:
When entries do not have a computable type, for instance if they are real numbers, we cannot
hope that ``#eval`` can help. Also this kind of evaluation cannot be used in proofs without
considerably expanding the trusted code base (i.e. the part of Lean that you need to trust when
checking proofs).

So it is good to also use the ``simp`` and ``norm_num`` tactics in proofs, or
their command counter-part for quick exploration.
EXAMPLES: -/
-- QUOTE:

#simp !![(1 : ℝ), 2; 3, 4].det -- `4 - 2*3`

#norm_num !![(1 : ℝ), 2; 3, 4].det -- `-2`

#norm_num !![(1 : ℝ), 2; 3, 4].trace -- `5`

variable (a b c d : ℝ) in
#simp !![a, b; c, d].det -- `a * d – b * c`

-- QUOTE.
/- TEXT:
The next important operation on square matrices is inversion.
In the same way as division of numbers is always defined and returns the artificial value
zero for division by zero, the inversion operation is defined on all matrices and returns
the zero matrix for non-invertible matrices.

More precisely, there is general function ``Ring.inverse`` that does this in any ring,
and, for any matrix ``A``, ``A⁻¹`` is defined as ``Ring.inverse A.det • A.adjugate``.
According to Cramer’s rule, this is indeed the inverse of ``A`` when the determinant of ``A`` is
not zero.
EXAMPLES: -/
-- QUOTE:

#norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 4]⁻¹ -- !![-2, 1; 3 / 2, -(1 / 2)]

-- QUOTE.
/- TEXT:
Of course this definition is really useful only for invertible matrices.
There is a general type class ``Invertible`` that helps recording this.
For instance, the ``simp`` call in the next example will use the ``inv_mul_of_invertible``
lemma which has an ``Invertible`` type-class assumption, so it will trigger
only if this can be found by the type-class synthesis system.
Here we make this fact available using a ``have`` statement.
EXAMPLES: -/
-- QUOTE:

example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  have : Invertible !![(1 : ℝ), 2; 3, 4] := by
    apply Matrix.invertibleOfIsUnitDet
    norm_num
  simp

-- QUOTE.
/- TEXT:
In this fully concrete case, we could also use the ``norm_num`` machinery,
and ``apply?`` to find the final line:
EXAMPLES: -/
-- QUOTE:
example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  norm_num [Matrix.inv_def]
  exact one_fin_two.symm

-- QUOTE.
/- TEXT:
All the concrete matrices above have their rows and columns indexed by ``Fin n`` for
some ``n`` (not necessarily the same for rows and columns).
But sometimes it is more convenient to index matrices using arbitrary finite types.
For instance the adjacency matrix of a finite graph has rows and columns naturally indexed by
the vertices of the graph.

In fact when simply wants to define matrices without defining any operation on them,
finiteness of the indexing types are not even needed, and coefficients can have any type,
without any algebraic structure.
So Mathlib simply defines ``Matrix m n α`` to be ``m → n → α`` for any types ``m``, ``n`` and ``α``,
and the matrices we have been using so far had types such as ``Matrix (Fin 2) (Fin 2) ℝ``.
Of course algebraic operations require more assumptions on ``m``, ``n`` and ``α``.

Note the main reason why we do not use ``m → n → α`` directly is to allow the type class
system to understand what we want. For instance, for a ring ``R``, the type ``n → R`` is
endowed with the point-wise multiplication operation, and similarly ``m → n → R``
has this operation which is *not* the multiplication we want on matrices.

In the first example below, we force Lean to see through the definition of ``Matrix``
and accept the statement as meaningful, and then prove it by checking all entries.

But then the next two examples reveal that Lean uses the point-wise multiplication
on ``Fin 2 → Fin 2 → ℤ`` but the matrix multiplication on ``Matrix (Fin 2) (Fin 2) ℤ``.
EXAMPLES: -/
-- QUOTE:
section

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) * (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : !![1, 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
  norm_num
-- QUOTE.
/- TEXT:
In order to define matrices as functions without losing the benefits of ``Matrix``
for type class synthesis, we can use the equivalence ``Matrix.of`` between functions
and matrices. This equivalence is secretly defined using ``Equiv.refl``.

For instance we can define Vandermonde matrices corresponding to a vector ``v``.
EXAMPLES: -/
-- QUOTE:

example {n : ℕ} (v : Fin n → ℝ) :
    Matrix.vandermonde v = Matrix.of (fun i j : Fin n ↦ v i ^ (j : ℕ)) :=
  rfl
end
end matrices
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
other characterizations are proven from it.
One must be slightly careful with the “power of ``K``” idea in the case of infinite bases.
Indeed only finite linear combinations make sense in this algebraic context. So what we need
as a reference vector space is not a direct product of copies of ``K`` but a direct sum.
We could use ``⨁ i : ι, K`` for some type ``ι`` indexing the basis
But we rather use the more specialized spelling ``ι →₀ K`` which means
“functions from ``ι`` to ``K`` with finite support”, i.e. functions which vanish outside a finite set
in ``ι`` (this finite set is not fixed, it depends on the function).
Evaluating such a function coming from a basis ``B`` at a vector ``v`` and
``i : ι`` returns the component (or coordinate) of ``v`` on the ``i``-th basis vector.

The type of bases indexed by a type ``ι`` of ``V`` as a ``K`` vector space is ``Basis ι K V``.
The isomorphism is called ``Basis.repr``.
BOTH: -/
-- QUOTE:
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section

open Module

variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

-- The basis vector with index ``i``
#check (B i : V)

-- the linear isomorphism with the model space given by ``B``
#check (B.repr : V ≃ₗ[K] ι →₀ K)

-- the component function of ``v``
#check (B.repr v : ι →₀ K)

-- the component of ``v`` with index ``i``
#check (B.repr v i : K)

-- QUOTE.
/- TEXT:
Instead of starting with such an isomorphism, one can start with a family ``b`` of vectors that is
linearly independent and spanning, this is ``Basis.mk``.

The assumption that the family is spanning is spelled out as ``⊤ ≤ Submodule.span K (Set.range b)``.
Here ``⊤`` is the top submodule of ``V``, i.e. ``V`` seen as submodule of itself.
This spelling looks a bit tortuous, but we will see below that it is almost equivalent by definition
to the more readable ``∀ v, v ∈ Submodule.span K (Set.range b)`` (the underscores in the snippet
below refers to the useless information ``v ∈ ⊤``).
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
``basisSingleOne`` refers to the fact that basis vectors are functions which
vanish expect for a single input value. More precisely the basis vector indexed by ``i : ι``
is ``Finsupp.single i 1`` which is the finitely supported function taking value ``1`` at ``i``
and ``0`` everywhere else.

BOTH: -/
-- QUOTE:
variable [DecidableEq ι]
-- QUOTE.

-- EXAMPLES:
-- QUOTE:
example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl

-- QUOTE.
/- TEXT:
The story of finitely supported functions is unneeded when the indexing type is finite.
In this case we can use the simpler ``Pi.basisFun`` which gives a basis of the whole
``ι → K``.
EXAMPLES: -/
-- QUOTE:

example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
  simp

-- QUOTE.
/- TEXT:
Going back to the general case of bases of abstract vector spaces, we can express
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
Given a finitely supported function ``c`` from a type ``ι`` to the base field ``K`` and any
function ``f`` from ``ι`` to ``V``, ``Finsupp.linearCombination K f c`` is the
sum over the support of ``c`` of the scalar multiplication ``c • f``. In
particular, we can replace it by a sum over any finite set containing the
support of ``c``.

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
One could wonder why ``K`` is an explicit argument here, despite the fact it can be inferred from
the type of ``c``. The point is that the partially applied ``Finsupp.linearCombination K f``
is interesting in itself. It is not a bare function from ``ι →₀ K`` to ``V`` but a
``K``-linear map.
EXAMPLES: -/
-- QUOTE:
variable (f : ι → V) in
#check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)

-- QUOTE.
/- TEXT:
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
BOTH: -/
-- QUOTE:
section

variable {W : Type*} [AddCommGroup W] [Module K W]
         (φ : V →ₗ[K] W) (u : ι → W)

#check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))

#check (B.constr K u : V →ₗ[K] W)

example (i : ι) : B.constr K u (B i) = u i :=
  B.constr_basis K u i

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
BOTH: -/
-- QUOTE:


variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

open LinearMap

#check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

open Matrix -- get access to the ``*ᵥ`` notation for multiplication between matrices and vectors.

example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v


variable {ι'' : Type*} (B'' : Basis ι'' K W) [Fintype ι''] [DecidableEq ι'']

example (φ : V →ₗ[K] W) : (toMatrix B B'' φ) = (toMatrix B' B'' .id) * (toMatrix B B' φ) := by
  simp

end

-- QUOTE.
/- TEXT:
As an exercise on this topic, we will prove part of the theorem which guarantees that
endomorphisms have a well-defined determinant.
Namely we want to prove that when two bases are indexed by the same type, the matrices
they attach to any endomorphism have the same determinant.
This would then need to be complemented using that bases all have isomorphic indexing types to
get the full result.

Of course Mathlib already knows this, and ``simp`` can close the goal immediately, so you
shouldn’t use it too soon, but rather use the provided lemmas.
BOTH: -/
-- QUOTE:

open Module LinearMap Matrix

-- Some lemmas coming from the fact that `LinearMap.toMatrix` is an algebra morphism.
#check toMatrix_comp
#check id_comp
#check comp_id
#check toMatrix_id

-- Some lemmas coming from the fact that ``Matrix.det`` is a multiplicative monoid morphism.
#check Matrix.det_mul
#check Matrix.det_one

example [Fintype ι] (B' : Basis ι K V) (φ : End K V) :
    (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
  set M := toMatrix B B φ
  set M' := toMatrix B' B' φ
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have F : M = P' * M' * P := by
    rw [← toMatrix_comp, ← toMatrix_comp, id_comp, comp_id]
  have F' : P' * P = 1 := by
    rw [← toMatrix_comp, id_comp, toMatrix_id]
  rw [F, Matrix.det_mul, Matrix.det_mul,
      show P'.det * M'.det * P.det = P'.det * P.det * M'.det by ring, ← Matrix.det_mul, F',
      Matrix.det_one, one_mul]
-- BOTH:
end

-- QUOTE.
/- TEXT:

Dimension
^^^^^^^^^

Returning to the case of a single vector space, bases are also useful to define the concept of
dimension.
Here again, there is the elementary case of finite-dimensional vector spaces.
For such spaces we expect a dimension which is a natural number.
This is ``Module.finrank``. It takes the base field as an explicit argument
since a given abelian group can be a vector space over different fields.

EXAMPLES: -/
-- QUOTE:
section

#check (Module.finrank K V : ℕ)

-- `Fin n → K` is the archetypical space with dimension `n` over `K`.
example (n : ℕ) : Module.finrank K (Fin n → K) = n :=
  Module.finrank_fin_fun K

-- Seen as a vector space over itself, `ℂ` has dimension one.
example : Module.finrank ℂ ℂ = 1 :=
  Module.finrank_self ℂ

-- But as a real vector space it has dimension two.
example : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

-- QUOTE.
/- TEXT:
Note that ``Module.finrank`` is defined for any vector space. It returns
zero for infinite dimensional vector spaces, just as division by zero returns zero.

Of course many lemmas require a finite dimension assumption. This is the role of
the ``FiniteDimensional`` typeclass. For instance, think about how the next
example fails without this assumption.
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] : 0 < Module.finrank K V ↔ Nontrivial V  :=
  Module.finrank_pos_iff

-- QUOTE.
/- TEXT:
In the above statement, ``Nontrivial V`` means ``V`` has at least two different elements.
Note that ``Module.finrank_pos_iff`` has no explicit argument.
This is fine when using it from left to right, but not when using it from right to left
because Lean has no way to guess ``K`` from the statement ``Nontrivial V``.
In that case it is useful to use the name argument syntax, after checking that the lemma
is stated over a ring named ``R``. So we can write:
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] (h : 0 < Module.finrank K V) : Nontrivial V := by
  apply (Module.finrank_pos_iff (R := K)).1
  exact h

-- QUOTE.
/- TEXT:
The above spelling is strange because we already have ``h`` as an assumption, so we could
just as well give the full proof ``Module.finrank_pos_iff.1 h`` but it
is good to know for more complicated cases.

By definition, ``FiniteDimensional K V`` can be read from any basis.
EXAMPLES: -/
-- QUOTE:
variable {ι : Type*} (B : Module.Basis ι K V)

example [Finite ι] : FiniteDimensional K V := FiniteDimensional.of_fintype_basis B

example [FiniteDimensional K V] : Finite ι :=
  (FiniteDimensional.fintypeBasisIndex B).finite
end
-- QUOTE.
/- TEXT:
Using that the subtype corresponding to a linear subspace has a vector space structure,
we can talk about the dimension of a subspace.
BOTH: -/
-- QUOTE:

section
variable (E F : Submodule K V) [FiniteDimensional K V]

open Module

example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
    finrank K E + finrank K F :=
  Submodule.finrank_sup_add_finrank_inf_eq E F

example : finrank K E ≤ finrank K V := Submodule.finrank_le E
-- QUOTE.
/- TEXT:
In the first statement above, the purpose of the type ascriptions is to make sure that
coercion to ``Type*`` does not trigger too early.

We are now ready for an exercise about ``finrank`` and subspaces.
BOTH: -/
-- QUOTE:
example (h : finrank K V < finrank K E + finrank K F) :
    Nontrivial (E ⊓ F : Submodule K V) := by
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
``finrank`` is useless, but we still have that, for any two bases of the same
vector space, there is a bijection between the types indexing those bases. So we
can still hope to define the rank as a cardinal, i.e. an element of the “quotient of
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
``Type u ≠ Type (u+1)`` does not make any sense since ``Type u`` and ``Type (u+1)``
have different types.

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
So instead it is defined as the supremum ``Module.rank K V`` of cardinals of
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

universe u v -- `u` and `v` will denote universe levels

variable {ι : Type u} (B : Module.Basis ι K V)
         {ι' : Type v} (B' : Module.Basis ι' K V)

example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
  mk_eq_mk_of_basis B B'
-- QUOTE.
/- TEXT:
We can relate the finite dimensional case to this discussion using the coercion
from natural numbers to finite cardinals (or more precisely the finite cardinals which live in ``Cardinal.{v}`` where ``v`` is the universe level of ``V``).
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] :
    (Module.finrank K V : Cardinal) = Module.rank K V :=
  Module.finrank_eq_rank K V
-- QUOTE.
