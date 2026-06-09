import MIL.Common
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Real.Basic

set_option autoImplicit true

/- TEXT:
.. _section_hierarchies_basics:

Basics
------

At the very bottom of all hierarchies in Lean, we find data-carrying
classes. The following class records that the given type ``α`` is endowed with
a distinguished element called ``one``. At this stage, it has no property at all.
BOTH: -/

-- QUOTE:
class One₁ (α : Type) where
  /-- The element one -/
  one : α
-- QUOTE.

/- TEXT:
Since we'll make a much heavier use of classes in this chapter, we need to understand some
more details about what the ``class`` command is doing.
First, the ``class`` command above defines a structure ``One₁`` with parameter ``α : Type`` and
a single field ``one``. It also mark this structure as a class so that arguments of type
``One₁ α`` for some type ``α`` will be inferrable using the instance resolution procedure,
as long as they are marked as instance-implicit, i.e. appear between square brackets.
Those two effects could also have been achieved using the ``structure`` command with ``class``
attribute, i.e. writing ``@[class] structure`` instance of ``class``. But the class command also
ensures that ``One₁ α`` appears as an instance-implicit argument in its own fields. Compare:
BOTH: -/

-- QUOTE:
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one
-- QUOTE.

/- TEXT:
In the second check, we can see that ``self : One₂ α`` is an explicit argument.
Let us make sure the first version is indeed usable without any explicit argument.
BOTH: -/

-- QUOTE:
example (α : Type) [One₁ α] : α := One₁.one
-- QUOTE.

/- TEXT:
Remark: in the above example, the argument ``One₁ α`` is marked as instance-implicit,
which is a bit silly since this affects only *uses* of the declaration and declaration created by
the ``example`` command cannot be used. However it allows us to avoid giving a name to that
argument and, more importantly, it starts installing the good habit of marking ``One₁ α``
arguments as instance-implicit.

Another remark is that all this will work only when Lean knows what is ``α``. In the above
example, leaving out the type ascription ``: α`` would generate an error message like:
``typeclass instance problem is stuck, it is often due to metavariables One₁ (?m.263 α)``
where ``?m.263 α`` means "some type depending on ``α``" (and 263 is simply an auto-generated
index that would be useful to distinguish between several unknown things). Another way
to avoid this issue would be to use a type annotation, as in:
BOTH: -/
-- QUOTE:
example (α : Type) [One₁ α] := (One₁.one : α)
-- QUOTE.

/- TEXT:
You may have already encountered that issue when playing with limits of sequences
in :numref:`sequences_and_convergence` if you tried to state for instance that
``0 < 1`` without telling Lean whether you meant this inequality to be about natural numbers
or real numbers.

Our next task is to assign a notation to ``One₁.one``. Since we don't want collisions
with the builtin notation for ``1``, we will use ``𝟙``. This is achieved by the following
command where the first line tells Lean to use the documentation
of ``One₁.one`` as documentation for the symbol ``𝟙``.
BOTH: -/
-- QUOTE:
@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl
-- QUOTE.

/- TEXT:
We now want a data-carrying class recording a binary operation. We don't want to choose
between addition and multiplication for now so we'll use diamond.
BOTH: -/

-- QUOTE:
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia
-- QUOTE.

/- TEXT:
As in the ``One₁`` example, the operation has no property at all at this stage. Let us
now define the class of semigroup structures where the operation is denoted by ``⋄``.
For now, we define it by hand as a structure with two fields, a ``Dia₁`` instance and some
``Prop``-valued field ``dia_assoc`` asserting associativity of ``⋄``.
BOTH: -/

-- QUOTE:
class Semigroup₀ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
-- QUOTE.

/- TEXT:
Note that while stating `dia_assoc`, the previously defined field `toDia₁` is in the local
context hence can be used when Lean searches for an instance of `Dia₁ α` to make sense
of `a ⋄ b`. However this `toDia₁` field does not become part of the type class instances database.
Hence doing ``example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b`` would fail with
error message ``failed to synthesize instance Dia₁ α``.

We can fix this by adding the ``instance`` attribute later.
BOTH: -/

-- QUOTE:
attribute [instance] Semigroup₀.toDia₁

example {α : Type} [Semigroup₀ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- TEXT:
Before building up, we need to use a different syntax to add this `toDia₁` field,
to tell Lean that `Dia₁ α` should be treated as if its fields were fields of `Semigroup₁` itself.
This also conveniently adds the `toDia₁` instance automatically.
The ``class`` command supports this using the ``extends`` syntax as in:
BOTH: -/

-- QUOTE:
class Semigroup₁ (α : Type) extends toDia₁ : Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- TEXT:
Note this syntax is also available in the ``structure`` command, although in that
case it fixes only the hurdle of writing fields such as `toDia₁` since there
is no instance to define in that case.

The field name `toDia₁` is optional in the `extends` syntax.
By default it takes the name of the class being extended and prefixes it with "to".
BOTH: -/

-- QUOTE:
class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
-- QUOTE.

/- TEXT:
Let us now try to combine a diamond operation and a distinguished one element with axioms saying
this element is neutral on both sides.
BOTH: -/
-- QUOTE:
class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- QUOTE.

/- TEXT:
In the next example, we tell Lean that ``α`` has a ``DiaOneClass₁`` structure and state a
property that uses both a `Dia₁` instance and a `One₁` instance. In order to see how Lean finds
those instances we set a tracing option whose result can be seen in the Infoview. This result
is rather terse by default but it can be expanded by clicking on lines ending with black arrows.
It includes failed attempts where Lean tried to find instances before having enough type
information to succeed. The successful attempts do involve the instances generated by the
``extends`` syntax.
BOTH: -/

-- QUOTE:
set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙
-- QUOTE.

/- TEXT:
Note that we don't need to include extra fields where combining existing classes. Hence we can
define monoids as:
BOTH: -/

-- QUOTE:
class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α
-- QUOTE.

/- TEXT:
While the above definition seems straightforward, it hides an important subtlety. Both
``Semigroup₁ α`` and ``DiaOneClass₁ α`` extend ``Dia₁ α``, so one could fear that having
a ``Monoid₁ α`` instance gives two unrelated diamond operations on ``α``, one coming from
a field ``Monoid₁.toSemigroup₁`` and one coming from a field ``Monoid₁.toDiaOneClass₁``.

Indeed if we try to build a monoid class by hand using:
BOTH: -/

-- QUOTE:
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α
-- QUOTE.

/- TEXT:
then we get two completely unrelated diamond operations
``Monoid₂.toSemigroup₁.toDia₁.dia`` and ``Monoid₂.toDiaOneClass₁.toDia₁.dia``.

The version generated using the ``extends`` syntax does not have this defect.
BOTH: -/

-- QUOTE:
example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl
-- QUOTE.

/- TEXT:
So the ``class`` command did some magic for us (and the ``structure`` command would have done it
too). An easy way to see what are the fields of our classes is to check their constructor. Compare:
BOTH: -/

-- QUOTE:
/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk
-- QUOTE.

/- TEXT:
So we see that ``Monoid₁`` takes ``Semigroup₁ α`` argument as expected but then it won't
take a would-be overlapping ``DiaOneClass₁ α`` argument but instead tears it apart and includes
only the non-overlapping parts. And it also auto-generated an instance ``Monoid₁.toDiaOneClass₁``
which is *not* a field but has the expected signature which, from the end-user point of view,
restores the symmetry between the two extended classes ``Semigroup₁`` and ``DiaOneClass₁``.
BOTH: -/

-- QUOTE:
#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁
-- QUOTE.

/- TEXT:
We are now very close to defining groups. We could add to the monoid structure a field asserting
the existence of an inverse for every element. But then we would need to work to access these
inverses. In practice it is more convenient to add it as data. To optimize reusability,
we define a new data-carrying class, and then give it some notation.
BOTH: -/

-- QUOTE:
class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙
-- QUOTE.

/- TEXT:
The above definition may seem too weak, we only ask that ``a⁻¹`` is a left-inverse of ``a``.
But the other side is automatic. In order to prove that, we need a preliminary lemma.
BOTH: -/

-- QUOTE:
lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]
-- QUOTE.

/- TEXT:
In this lemma, it is pretty annoying to give full names, especially since it requires knowing
which part of the hierarchy provides those facts. One way to fix this is to use the ``export``
command to copy those facts as lemmas in the root name space.
BOTH: -/

-- QUOTE:
export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)
-- QUOTE.

/- TEXT:
We can then rewrite the above proof as:
BOTH: -/

-- QUOTE:
example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]
-- QUOTE.

/- TEXT:
It is now your turn to prove things about our algebraic structures.
BOTH: -/

-- QUOTE:
lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  left_inv_eq_right_inv₁ (inv_dia a) h
-- BOTH:

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  by rw [← inv_dia a⁻¹, inv_eq_of_dia (inv_dia a)]
-- QUOTE.

/- TEXT:
At this stage we would like to move on to define rings, but there is a serious issue.
A ring structure on a type contains both an additive group structure and a multiplicative
monoid structure, and some properties about their interaction. But so far we hard-coded
a notation ``⋄`` for all our operations. More fundamentally, the type class system
assumes every type has only one instance of each type class. There are various
ways to solve this issue. Surprisingly Mathlib uses the naive idea to duplicate
everything for additive and multiplicative theories with the help of some code-generating
attribute. Structures and classes are defined in both additive and multiplicative notation
with an attribute ``to_additive`` linking them. In case of multiple inheritance like for
semi-groups, the auto-generated "symmetry-restoring" instances need also to be marked.
This is a bit technical; you don't need to understand details. The important point is that
lemmas are then only stated in multiplicative notation and marked with the attribute ``to_additive``
to generate the additive version as ``left_inv_eq_right_inv'`` with its auto-generated additive
version ``left_neg_eq_right_neg'``. In order to check the name of this additive version we
used the ``whatsnew in`` command on top of ``left_inv_eq_right_inv'``.
BOTH: -/

-- QUOTE:



class AddSemigroup₃ (α : Type) extends Add α where
  /-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
  /-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'
-- QUOTE.

/- TEXT:
Equipped with this technology, we can easily define also commutative semigroups, monoids and
groups, and then define rings.

BOTH: -/
-- QUOTE:
class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1
-- QUOTE.

/- TEXT:
We should remember to tag lemmas with ``simp`` when appropriate.
BOTH: -/

-- QUOTE:
attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

-- QUOTE.

/- TEXT:
Then we need to repeat ourselves a bit since we switch to standard notations, but at least
``to_additive`` does the work of translating from the multiplicative notation to the additive one.
BOTH: -/

-- QUOTE:
@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  left_inv_eq_right_inv' (Group₃.inv_mul a) h
-- BOTH:
-- QUOTE.

/- TEXT:
Note that ``to_additive`` can be asked to tag a lemma with ``simp`` and propagate that attribute
to the additive version as follows.
BOTH: -/

-- QUOTE:
@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] (a : G) : a * a⁻¹ = 1 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [← inv_mul a⁻¹, inv_eq_of_mul (inv_mul a)]
-- BOTH:

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [← mul_assoc₃] using congr_arg (a⁻¹ * ·) h
-- BOTH:

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [mul_assoc₃] using congr_arg (· * a⁻¹) h
-- BOTH:

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

-- QUOTE.

/- TEXT:
We are now ready for rings. For demonstration purposes we won't assume that addition is
commutative, and then immediately provide an instance of ``AddCommGroup₃``. Mathlib does not
play this game, first because in practice this does not make any ring instance easier and
also because Mathlib's algebraic hierarchy goes through semirings which are like rings but without
opposites so that the proof below does not work for them. What we gain here, besides a nice exercise
if you have never seen it, is an example of building an instance using the syntax that allows
to provide a parent structure as an instance parameter and then supply the extra fields.
Here the `Ring₃ R` argument supplies anything `AddCommGroup₃ R` wants except for `add_comm`.
BOTH: -/

-- QUOTE:
class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ add_comm := by
/- EXAMPLES:
    sorry }
SOLUTIONS: -/
    intro a b
    have : a + (a + b + b) = a + (b + a + b) := calc
      a + (a + b + b) = (a + a) + (b + b) := by simp [add_assoc₃, add_assoc₃]
      _ = (1 * a + 1 * a) + (1 * b + 1 * b) := by simp
      _ = (1 + 1) * a + (1 + 1) * b := by simp [Ring₃.right_distrib]
      _ = (1 + 1) * (a + b) := by simp [Ring₃.left_distrib]
      _ = 1 * (a + b) + 1 * (a + b) := by simp [Ring₃.right_distrib]
      _ = (a + b) + (a + b) := by simp
      _ = a + (b + a + b) := by simp [add_assoc₃]
    exact add_right_cancel₃ (add_left_cancel₃ this) }
-- QUOTE.
/- TEXT:
Of course we can also build concrete instances, such as a ring structure on integers (of course
the instance below uses that all the work is already done in Mathlib).
BOTH: -/

-- QUOTE:
instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
-- QUOTE.
/- TEXT:
As an exercise you can now set up a simple hierarchy for order relations, including a class
for ordered commutative monoids, which have both a partial order and a commutative monoid structure
such that ``∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b``. Of course you need to add fields and maybe
``extends`` clauses to the following classes.
BOTH: -/
-- QUOTE:

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type)
-- SOLUTIONS:
  extends LE₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c
-- BOTH:

class PartialOrder₁ (α : Type)
-- SOLUTIONS:
  extends Preorder₁ α where
  le_antisymm : ∀ a b : α, a ≤₁ b → b ≤₁ a → a = b
-- BOTH:

class OrderedCommMonoid₁ (α : Type)
-- SOLUTIONS:
  extends PartialOrder₁ α, CommMonoid₃ α where
  mul_of_le : ∀ a b : α, a ≤₁ b → ∀ c : α, c * a ≤₁ c * b
-- BOTH:

instance : OrderedCommMonoid₁ ℕ where
-- SOLUTIONS:
  le := (· ≤ ·)
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ ↦ le_trans
  le_antisymm := fun _ _ ↦ le_antisymm
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  mul_of_le := fun _ _ h c ↦ Nat.mul_le_mul_left c h
-- QUOTE.
/- TEXT:



We now want to discuss algebraic structures involving several types. The prime example
is modules over rings. If you don't know what is a module, you can pretend it means vector space
and think that all our rings are fields. Those structures are commutative additive groups
equipped with a scalar multiplication by elements of some ring.

We first define the data-carrying type class of scalar multiplication by some type ``α`` on some
type ``β``, and give it a right associative notation.
BOTH: -/

-- QUOTE:
class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul
-- QUOTE.

/- TEXT:
Then we can define modules (again think about vector spaces if you don't know what is a module).
BOTH: -/

-- QUOTE:
class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n
-- QUOTE.

/- TEXT:
There is something interesting going on here. While it isn't too surprising that the
ring structure on ``R`` is a parameter in this definition, you probably expected ``AddCommGroup₃ M``
to be part of the ``extends`` clause just as ``SMul₃ R M`` is.  Trying to do that would lead
to a field ``Module₃.toAddCommGroup₃`` marked as an instance. This instance
would have the signature:
``(R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M``.
With such an instance in the type class database, each time Lean would look for a
``AddCommGroup₃ M`` instance for some ``M``, it would need to go hunting for a completely
unspecified type ``R`` and a ``Ring₃ R`` instance before embarking on the main quest of finding a
``Module₁ R M`` instance. Those two side-quests are represented by the meta-variables mentioned in
the error message and denoted by ``?R`` and ``?inst✝`` there. Such a ``Module₃.toAddCommGroup₃``
instance would then be a huge trap for the instance resolution procedure.

What about ``extends SMul₃ R M`` then? That one creates a field
``Module₁.toSMul₃ : {R : Type} →  [inst : Ring₃ R] → {M : Type} → [inst_1 : AddCommGroup₃ M] → [self : Module₁ R M] → SMul₃ R M``
whose end result ``SMul₃ R M`` mentions both ``R`` and ``M`` so this field can
safely be used as an instance. The rule is easy to remember: each class appearing in the
``extends`` clause should mention every type appearing in the parameters.

Let us create our first module instance: a ring is a module over itself using its multiplication
as a scalar multiplication.
BOTH: -/
-- QUOTE:
instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib
-- QUOTE.
/- TEXT:
As a second example, every abelian group is a module over ``ℤ`` (this is one of the reason to
generalize the theory of vector spaces by allowing non-invertible scalars). First one can define
scalar multiplication by a natural number for any type equipped with a zero and an addition:
``n • a`` is defined as ``a + ⋯ + a`` where ``a`` appears ``n`` times. Then this is extended
to scalar multiplication by an integer by ensuring ``(-1) • a = -a``.
BOTH: -/
-- QUOTE:

def nsmul₁ {M : Type*} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a
-- QUOTE.
/- TEXT:
Proving this gives rise to a module structure is a bit tedious and not interesting for the
current discussion, so we will sorry all axioms. You are *not* asked to replace those sorries
with proofs. If you insist on doing it then you will probably want to state and prove several
intermediate lemmas about ``nsmul₁`` and ``zsmul₁``.
BOTH: -/
-- QUOTE:

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry
-- QUOTE.
/- TEXT:
A much more important issue is that we now have two module structures over the ring ``ℤ``
for ``ℤ`` itself: ``abGrpModule ℤ`` since ``ℤ`` is a abelian group, and ``selfModule ℤ`` since
``ℤ`` is a ring. Those two module structure correspond to the same abelian group structure,
but it is not obvious that they have the same scalar multiplication. They actually do, but
this isn't true by definition, it requires a proof. This is very bad news for the type class
instance resolution procedure and will lead to very frustrating failures for users of this
hierarchy. When directly asked to find an instance, Lean will pick one, and we can see
which one using:
BOTH: -/
-- QUOTE:

#synth Module₁ ℤ ℤ -- abGrpModule ℤ

-- QUOTE.
/- TEXT:
But in a more indirect context it can happen that Lean infers the other one and then gets confused.
This situation is known as a bad diamond. This has nothing to do with the diamond operation
we used above, it refers to the way one can draw the paths from ``ℤ`` to its ``Module₁ ℤ``
going through either ``AddCommGroup₃ ℤ`` or ``Ring₃ ℤ``.

It is important to understand that not all diamonds are bad. In fact there are diamonds everywhere
in Mathlib, and also in this chapter. Already at the very beginning we saw one can go
from ``Monoid₁ α`` to ``Dia₁ α`` through either ``Semigroup₁ α`` or ``DiaOneClass₁ α`` and
thanks to the work done by the ``class`` command, the resulting two ``Dia₁ α`` instances
are definitionally equal. In particular a diamond having a ``Prop``-valued class at the bottom
cannot be bad since any two proofs of the same statement are definitionally equal.

But the diamond we created with modules is definitely bad. The offending piece is the ``smul``
field which is data, not a proof, and we have two constructions that are not definitionally equal.
The robust way of fixing this issue is to make sure that going from a rich structure to a
poor structure is always done by forgetting data, not by defining data. This well-known pattern
has been named "forgetful inheritance" and extensively discussed in
https://inria.hal.science/hal-02463336v2.

In our concrete case, we can modify the definition of ``AddMonoid₃`` to include a ``nsmul`` data
field and some ``Prop``-valued fields ensuring this operation is provably the one we constructed
above. Those fields are given default values using ``:=`` after their type in the definition below.
Thanks to these default values, most instances would be constructed exactly as with our previous
definitions. But in the special case of ``ℤ`` we will be able to provide specific values.
BOTH: -/
-- QUOTE:

class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩
-- QUOTE.
/- TEXT:

Let us check we can still construct a product monoid instance without providing the ``nsmul``
related fields.
BOTH: -/
-- QUOTE:

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero
-- QUOTE.
/- TEXT:
And now let us handle the special case of ``ℤ`` where we want to build ``nsmul`` using the coercion
of ``ℕ`` to ``ℤ`` and the multiplication on ``ℤ``. Note in particular how the proof fields
contain more work than in the default value above.
BOTH: -/
-- QUOTE:

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]
-- QUOTE.
/- TEXT:
Let us check we solved our issue. Because Lean already has a definition of scalar multiplication
of a natural number and an integer, and we want to make sure our instance is used, we won't use
the ``•`` notation but call ``SMul.mul`` and explicitly provide our instance defined above.
BOTH: -/
-- QUOTE:

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
-- QUOTE.
/- TEXT:
This story then continues with incorporating a ``zsmul`` field into the definition of groups
and similar tricks. You are now ready to read the definition of monoids, groups, rings and modules
in Mathlib. They are more complicated than what we have seen here, because they are part of a huge
hierarchy, but all principles have been explained above.

As an exercise, you can come back to the order relation hierarchy you built above and try
to incorporate a type class ``LT₁`` carrying the Less-Than notation ``<₁`` and make sure
that every preorder comes with a ``<₁`` which has a default value built from ``≤₁`` and a
``Prop``-valued field asserting the natural relation between those two comparison operators.
TEXT. -/

-- SOLUTIONS:
class LT₁ (α : Type) where
  /-- The Less-Than relation -/
  lt : α → α → Prop

@[inherit_doc] infix:50 " <₁ " => LT₁.lt

class PreOrder₂ (α : Type) extends LE₁ α, LT₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c
  lt := fun a b ↦ a ≤₁ b ∧ ¬b ≤₁ a
  lt_iff_le_not_le : ∀ a b : α, a <₁ b ↔ a ≤₁ b ∧ ¬b ≤₁ a := by intros; rfl
