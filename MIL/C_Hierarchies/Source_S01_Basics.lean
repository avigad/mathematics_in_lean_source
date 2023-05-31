import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

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
as long as they are marked as instance-implicit, ie appear between square brackets.
Those two effects could also have been achieved using the ``structure`` command with ``class``
attribute, ie writing ``@[class] structure`` instance of ``class``. But the class command also
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
the ``example`` command cannot be used. However it allows to avoid giving a name to that
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

Our next task is to assign a notation to ``One₁.one``. This we don't want collisions
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
class Semigroup₁ (α : Type) where
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
attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- TEXT:
Before building up, we need a more convenient way to extend structures than explicitly
writing fields like `toDia₁` and adding the instance attribute by hand. The ``class``
supports this using the ``extends`` syntax as in:
BOTH: -/

-- QUOTE:
class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- TEXT:
Note this syntax is also available in the ``structure`` command, although it that
case it fixes only the hurdle of writing fields such as `toDia₁` since there
is no instance to define in that case.


Let us now try to combine a diamond operation and a distinguished one with axioms saying
this element is neutral on both sides.
BOTH: -/
-- QUOTE:
class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diatiplication -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diatiplication -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- QUOTE.

/- TEXT:
In the next example, we tell Lean that ``α`` has a ``DiaOneClass₁`` structure and state a
property that uses both a `Dia₁` instance and a `One₁` instance. In order to see how Lean finds
those instances we set a tracing option whose result can be seen in the info view. This result
is rather terse by default but can be expended by clicking one lines ending with black arrows.
It includes failed attempts where Lean tried to find instances before having enough type
information to succceed. The successful attempts do involve the instances generated by the
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
So the ``class`` command did some magic for us. An easy way to see what are the fields of
our classes is to check their constructor. Compare:
BOTH: -/

-- QUOTE:
/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk
-- QUOTE.

/- TEXT:
So we see that ``Monoid₁`` takes ``Semigroup₁ α`` argument as expected but then it won't
take a would-be overlapping ``DiaOneClass₁ α`` argument but instead tears it appart and includes
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

class Group₁ (G : Type) extends Monoid₁ G, Inv G where
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
ways to solve this issue. Surprisingly mathlib uses the naive idea to duplicate
everything for additive and multiplicative theories with the help of some code-generating
attribute. Structures and classes are defined in both additive and multiplicative notation
with an attibute ``to_additive`` linking them. In case of multiple inheritance like for
semi-groups, the auto-generated "symmetry-restoring" instances need also to be marked.
This is a bit technical you don't need to understand details. The important point is that
lemmas are then only stated in multiplicative notation and marked with the attribute ``to_additive``
to generate the additive version as ``left_inv_eq_right_inv'`` with it's auto-generated additive
version ``left_neg_eq_right_neg'``. In order to check the name of this additive version we
used that ``wathsnew in`` command on top of ``left_inv_eq_right_inv'``.
BOTH: -/

-- QUOTE:



class AddSemigroup₃ (α : Type) extends Add α where
/-- Multiplication is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'
-- QUOTE.

/- TEXT:
Equipped with this technology, we can define rings, after some more intermediate classes.

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

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R := sorry
-- QUOTE.
/- TEXT:
We now want to discuss algebraic structures involving several types. The prime example
is modules over rings. If you don't know what is a module, you can pretend it means vector space
and think that all our rings are fields. Those structures are commutative additive groups
equipped with a scalar multiplication by elements of some ring.

We first define the data-carrying type class of scalar multiplication by some type ``α`` on some
type ``β``, and give it a right associative notation.
-/
class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul

class Module₁ (R : outParam Type) [Ring₃ R] (M : Type) extends AddCommGroup₃ M, SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = m
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n
