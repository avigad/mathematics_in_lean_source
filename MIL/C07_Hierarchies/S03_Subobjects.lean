import MIL.Common
import Mathlib.GroupTheory.QuotientGroup


/- TEXT:
.. _section_hierarchies_subobjects:

Sub-objects
-----------

After defining some algebraic structure and its morphisms, the next step is to consider sets
that inherit this algebraic structure, for instance subgroups or subrings.
This largely overlaps our previous topic. Indeed a set in ``X`` is implemented as a function from
``X`` to ``Prop`` so sub-objects are function satisfying a certain predicate.
Hence we can reuse of lot of the ideas that led to the ``FunLike`` class and its descendants.
We won't reuse ``FunLike`` itself because this would break the abstraction barrier from ``Set X``
to ``X → Prop``. Instead there is a ``SetLike`` class. Instead of wrapping an injection into a
function type, that class wraps an injection into a ``Set`` type and defines the corresponding
coercion and ``Membership`` instance.

BOTH: -/

-- QUOTE:
@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' := Submonoid₁.ext

-- QUOTE.

/- TEXT:
Equipped with the above ``SetLike`` instance, we can already state naturally that
a submonoid ``N`` contains ``1`` without using ``N.carrier``.
We can also silently treat ``N`` as a set in ``M`` as take its direct image under a map.
BOTH: -/

-- QUOTE:
example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N
-- QUOTE.

/- TEXT:
We also have a coercion to ``Type`` which uses ``Subtype`` so, given a submonoid ``N`` we can write
a parameter ``(x : N)`` which can be coerced to an element of ``M`` belonging to ``N``.

BOTH: -/

-- QUOTE:
example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property
-- QUOTE.

/- TEXT:
Using this coercion to ``Type`` we can also tackle the task of equipping a submonoid with a
monoid structure. We will use the coercion from the type associated to ``N`` as above, and the
lemma ``SetCoe.ext`` asserting this coercion is injective. Both are provided by the ``SetLike``
instance.

BOTH: -/

-- QUOTE:
instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))
-- QUOTE.

/- TEXT:
Note that, in the above instance, instead of using the coercion to ``M`` and calling the
``property`` field, we could have used destructuring binders as follows.

BOTH: -/

-- QUOTE:
example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)
-- QUOTE.

/- TEXT:

In order to apply lemmas about submonoids to subgroups or subrings, we need a class, just
like for morphisms. Note this class take a ``SetLike`` instance as a parameter so it does not need
a carrier field and can use the membership notation in its fields.
BOTH: -/

-- QUOTE:
class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem
-- QUOTE.

/- TEXT:

As an exercise you should define a ``Subgroup₁`` structure, endow it with a ``SetLike`` instance
and a ``SubmonoidClass₁`` instance, put a ``Group`` instance on the subtype associated to a
``Subgroup₁`` and define a ``SubgroupClass₁`` class.

SOLUTIONS: -/
@[ext]
structure Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  /-- The inverse of an element of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier


/-- Subgroups in `M` can be seen as sets in `M`. -/
instance [Group G] : SetLike (Subgroup₁ G) G where
  coe := fun H ↦ H.toSubmonoid₁.carrier
  coe_injective' := Subgroup₁.ext

instance [Group G] (H : Subgroup₁ G) : Group H :=
{ SubMonoid₁Monoid H.toSubmonoid₁ with
  inv := fun x ↦ ⟨x⁻¹, H.inv_mem x.property⟩
  mul_left_inv := fun x ↦ SetCoe.ext (mul_left_inv (x : G)) }

class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G]
    extends SubmonoidClass₁ S G  : Prop where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem := fun H ↦ H.toSubmonoid₁.mul_mem
  one_mem := fun H ↦ H.toSubmonoid₁.one_mem

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G :=
{ (inferInstance : SubmonoidClass₁ (Subgroup₁ G) G) with
  inv_mem := Subgroup₁.inv_mem }

/- TEXT:
Another very important thing to know about subobjects of a given algebraic object in Mathlib
always form a complete lattice, and this structure is used a lot. For instance you may look for
the lemma saying that an intersection of submonoids is a submonoid. But this won't be a lemma,
this will be an infimum construction. Let us do the case of two submonoids.

BOTH: -/

-- QUOTE:
instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩
-- QUOTE.

/- TEXT:
This allows to get the intersections of two submonoids as a submonoid.

BOTH: -/

-- QUOTE:
example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P
-- QUOTE.

/- TEXT:
You may think it's a shame that we had to use the inf symbol ``⊓`` in the above example instead
of the intersection symbol ``∩``. But think about the supremum. The union of two submonoids is not
a submonoid. However submonoids still form a lattice (even a complete one). Actually ``N ⊔ P`` is
the submonoid generated by the union of ``N`` and ``P`` and of course it would be very confusing to
denote it by ``N ∪ P``. So you can see the use of ``N ⊓ P`` as much more consistent. It is also
a lot more consistent across various kind of algebraic structures. It may look a bit weird at first
to see the sum of two vector subspace ``E`` and ``F`` denoted by ``E ⊔ F`` instead of ``E + F``.
But you will get used to it. And soon you will consider the ``E + F`` notation as a distraction
emphasizing the anecdotal fact that elements of ``E ⊔ F`` can be written as a sum of an element of
``E`` and an element of ``F`` instead of emphasizing the fundamental fact that ``E ⊔ F`` is the
smallest vector subspace containing both ``E`` and ``F``.

Our last topic for this chapter is that of quotients. Again we want to explain how
convenient notation are built and code duplication is avoided in Mathlib. Here the main device
is the ``HasQuotient`` class which allows notations like ``M ⧸ N``. Beware the quotient symbol
``⧸`` is a special unicode character, not a regular ASCII division symbol.

As an example, we will build the quotient of a commutative monoid by a submonoid, leave proofs
to you. In the last example, you can use ``Setoid.refl`` but it won't automatically pick up
the relevant ``Setoid`` structure. You can fix this issue by providing all arguments using
the ``@`` syntax, as in ``@Setoid.refl M N.Setoid``.

BOTH: -/

-- QUOTE:
def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
      rintro a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩
      refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
      rw [← mul_assoc, h, mul_comm b, mul_assoc, h', ← mul_assoc, mul_comm z, mul_assoc]
-- BOTH:
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro a₁ b₁ ⟨w, hw, z, hz, ha⟩ a₂ b₂ ⟨w', hw', z', hz', hb⟩
    refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
    rw [mul_comm w, ← mul_assoc, mul_assoc a₁, hb, mul_comm, ← mul_assoc, mul_comm w, ha,
        mul_assoc, mul_comm z, mul_assoc b₂, mul_comm z', mul_assoc]
-- BOTH:
        )
  mul_assoc := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    dsimp only
    rw [mul_assoc]
    apply @Setoid.refl M N.Setoid
-- BOTH:
  one := QuotientMonoid.mk N 1
  one_mul := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [one_mul] ; apply @Setoid.refl M N.Setoid
-- BOTH:
  mul_one := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [mul_one] ; apply @Setoid.refl M N.Setoid
-- QUOTE.
