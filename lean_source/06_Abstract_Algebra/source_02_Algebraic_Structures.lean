import data.real.basic

/- TEXT:
.. _section_algebraic_structures:

Algebraic Structures
--------------------

To clarify what we mean by the phrase *algebraic structure*,
it will help to consider some examples.

#. A *partially ordered set* consists of a set :math:`P` and
   a binary relation :math:`\le` on :math:`P` that is transitive
   and antireflexive.

#. A *group* consists of a set :math:`G` with an associative
   binary operation, an identity element
   :math:`1`, and a function :math:`g \mapsto g^{-1}` that returns
   an inverse for each :math:`g` in :math:`G`.
   A group is *abelian* or *commutative* if the operation is commutative.

#. A *lattice* is a partially ordered set with meets and joins.

#. A *ring* consists of an (additively written) abelian group
   :math:`(R, +, 0, x \mapsto -x)`
   together with an associative multiplication operation
   :math:`\cdot` and an identity :math:`1`,
   such that multiplication distributes over addition.
   A ring is *commutative* if the multiplication is commutative.

#. An *ordered ring* :math:`(R, +, 0, -, \cdot, 1, \le)` consists of a ring
   together with a partial order on its elements, such that :math:`a \le b` implies
   :math:`a + c \le b + c` for every :math:`a`, :math:`b`, and :math:`c` in :math:`R`,
   and :math:`0 \le a` and :math:`0 \le b` implies :math:`0 \le a b` for
   every :math:`a` and :math:`b` in :math:`R`.

#. A *metric space* consists of a set :math:`X` and a function
   :math:`d : X \times X \to \mathbb{R}` such that the following hold:

   - :math:`d(x, y) \ge 0` for every :math:`x` and :math:`y` in :math:`X`.
   - :math:`d(x, y) = 0` if and only if :math:`x = y`.
   - :math:`d(x, y) = d(y, x)` for every :math:`x` and :math:`y` in :math:`X`.
   - :math:`d(x, z) \le d(x, y) + d(y, z)` for every :math:`x`, :math:`y`, and
     :math:`z` in :math:`X`.

#. A *topological space* consists of a set :math:`X` and a collection :math:`\mathcal T`
   of subsets of :math:`X`, called the *open subsets of* :math:`X`, such that
   the following hold:

   - The empty set and :math:`X` are open.
   - The intersection of two open sets is open.
   - An arbitrary union of open sets is open.

In each of these examples, the elements of the structure belong to a
set, the *carrier set*,
that sometimes stands proxy for the entire structure.
For example, when we say "let :math:`G` be a group" and then
"let :math:`g \in G`," we are using :math:`G` to stand for both
the structure and its carrier.
Not every algebraic structure is associated with a single carrier set in this way.
For example, a *bipartite graph* involves a relation between two sets,
as does a *Galois connection*,
A *category* also involves two sets of interest, commonly called the *objects*
and the *morphisms*.

The examples indicate some of the things that a proof assistant has to do
in order to support algebraic reasoning.
First, it needs to recognize concrete instances of structures.
The number systems :math:`\mathbb{Z}`, :math:`\mathbb{Q}`,
and :math:`\mathbb{R}` are all ordered rings,
and we should be able to apply a generic theorem about ordered rings
in any of these instances.
Sometimes a concrete set may be an instance of a structure in more than one way.
For example, in addition to the usual topology on :math:`\mathbb{R}`,
which forms the basis for real analysis,
we can also consider the *discrete* topology on :math:`\mathbb{R}`,
in which every set is open.

Second, a proof assistant needs to support generic notation on structures.
In Lean, the notation ``*``
is used for multiplication in all the usual number systems,
as well as for multiplication in generic groups and rings.
When we use an expression like ``f x * y``,
Lean has to use information about the types of ``f``, ``x``, and ``y``
to determine which multiplication we have in mind.

Third, it needs to deal with the fact that structures can inherit
definitions, theorems, and notation from other structures in various ways.
Some structures extend others by adding more axioms.
A commutative ring is still a ring, so any definition
that makes sense in a ring also makes sense in a commutative ring,
and any theorem that holds in a ring also holds in a commutative ring.
Some structures extend others by adding more data.
For example, the additive part of any ring is an additive group.
The ring structure adds a multiplication and an identity,
as well as axioms that govern them and relate them to the additive part.
Sometimes we can define one structure in terms of another.
Any metric space has a canonical topology associated with it,
the *metric space topology*, and there are various topologies that can be
associated with any linear ordering.

Finally, it is important to keep in mind that mathematics allows us to
use functions and operations to define structures in the same way we
use functions and operations to define numbers.
Products and powers of groups are again groups.
For every :math:`n`, the integers modulo :math:`n` form a ring,
and for every :math:`k > 0`, the :math:`k \times k` matrices of polynomials
with coefficients in that ring again form a ring.
Thus we can calculate with structures just as easily as we can calculate
with their elements.
This means that algebraic structures lead dual lives in mathematics,
as containers for collections of objects and as objects in their own right.
A proof assistant has to accommodate this dual role.

When dealing with elements of a type that has an algebraic structure
associated with it,
a proof assistant needs to recognize the structure and find the relevant
definitions, theorems, and notation.
All this should sound like a lot of work, and it is.
But Lean uses a small collection of fundamental mechanisms to
carry out these tasks.
The goal of this section is to explain these mechanisms and show you
how to use them.

The first ingredient is almost too obvious to mention:
formally speaking, algebraic structures are structures in the sense
of :numref:`section_structures`.
An algebraic structure is a specification of a bundle of data satisfying
some axiomatic hypotheses, and we saw in :numref:`section_structures` that
this is exactly what the ``structure`` command is designed to accommodate.
It's a marriage made in heaven!

Given a data type ``α``, we can define the group structure on ``α``
as follows.
EXAMPLES: -/
-- QUOTE:
structure group₁ (α : Type*) :=
(mul: α → α → α)
(one: α)
(inv: α → α)
(mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z))
(mul_one: ∀ x : α, mul x one = x)
(one_mul: ∀ x : α, mul x one = x)
(mul_left_inv : ∀ x : α, mul (inv x) x = one)
-- QUOTE.

-- OMIT: TODO: explain the extends command later, and also redundant inheritance
/- TEXT:
Notice that the type ``α`` is a *parameter* in the definition of ``group₁``.
So you should think of an object ``struc : group₁ α`` as being
a group structure on ``α``.
We saw in :numref:`proving_identities_in_algebraic_structures`
that the counterpart ``mul_right_inv`` to ``mul_left_inv``
follows from the other group axioms, so there is no need
to add it to the definition.

This definition of a group is similar to the definition of ``group`` in
mathlib,
and we have chosen the name ``group₁`` to distinguish our version.
If you write ``#check group`` and ctrl-click on the definition,
you will see that the mathlib version of ``group`` is defined to
extend another structure; we will explain how to do that later.
If you type ``#print group`` you will also see that the mathlib
version of ``group`` has a number of extra fields.
For reasons we will explain later, sometimes it is useful to add
redundant information to a structure,
so that there are additional fields for objects and functions
that can be defined from the core
data. Don't worry about that for now.
Rest assured that our simplified version ``group₁`` is
morally the same as the definition of a group that mathlib uses.

It is sometimes useful to bundle
the type together with the structure, and mathlib also
contains a definition of a ``Group`` structure that is equivalent to
the following:
EXAMPLES: -/
-- QUOTE:
structure Group₁ :=
(α : Type*)
(str : group₁ α)
-- QUOTE.

/- TEXT:
The mathlib version is found in ``algebra.category.Group.basic``,
and you can ``#check`` it if you add this to the imports at the
beginning of the examples file.

For reasons that will become clearer below, it is more often
useful to keep the type ``α`` separate from the structure ``group α``.
We refer to the two objects together as a *partially bundled structure*,
since the representation combines most, but not all, of the components
into one structure. It is common in mathlib
to use capital roman letters like ``G`` for a type
when it is used as the carrier type for a group.

Let's construct a group, which is to say, an element of the ``group₁`` type.
For any pair of types ``α`` and ``β``, Mathlib defines the type ``equiv α β``
of *equivalences* between ``α`` and ``β``.
Mathlib also defines the suggestive notation ``α ≃ β`` for this type.
An element ``f : α ≃ β`` is a bijection between ``α`` and ``β``
represented by four components:
a function ``f.to_fun`` from ``α`` to ``β``,
the inverse function ``f.inv_fun`` from ``β`` to ``α``,
and two properties that specify these functions are indeed inverse
to one another.
EXAMPLES: -/
section
-- QUOTE:
variables (α β γ : Type*)
variables (f : α ≃ β) (g : β ≃ γ)

#check equiv α β
#check (f.to_fun : α → β)
#check (f.inv_fun : β → α)
#check (f.right_inv: ∀ x : β, f (f.inv_fun x) = x)
#check (f.left_inv: ∀ x : α, f.inv_fun (f x) = x)

#check (equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)
-- QUOTE.

/- TEXT:
Notice the creative naming of the last three constructions. We think of the
identity function ``equiv.refl``, the inverse operation ``equiv.symm``,
and the composition operation ``equiv.trans`` as explicit evidence
that the property of being in bijective correspondence is an equivalence relation.

Notice also that ``f.trans g`` requires composing the forward functions
in reverse order. Mathlib has declared a *coercion* from ``equiv α β``
to the function type ``α → β``, so we can omit writing ``.to_fun``
and have Lean insert it for us.
EXAMPLES: -/
-- QUOTE:
example (x : α) : (f.trans g).to_fun x = g.to_fun (f.to_fun x) := rfl

example (x : α) : (f.trans g) x = g (f x) := rfl

example : (f.trans g : α → γ) = g ∘ f := rfl
-- QUOTE.

end

/- TEXT:
Mathlib also defines the type ``perm α`` of equivalences between
``α`` and itself.
EXAMPLES: -/
-- QUOTE:
example (α : Type*) : equiv.perm α = (α ≃ α) := rfl
-- QUOTE.

/- TEXT:
It should be clear that ``equiv.perm α`` forms a group under composition
of equivalences. We orient things so that ``mul f g`` is
equal to ``g.trans f``, whose forward function is ``f ∘ g``.
In other words, multiplication is what we ordinarily think of as
composition of the bijections. Here we define this group:
EXAMPLES: -/
-- QUOTE:
def perm_group {α : Type*} : group₁ (equiv.perm α) :=
{ mul          := λ f g, equiv.trans g f,
  one          := equiv.refl α,
  inv          := equiv.symm,
  mul_assoc    := λ f g h, (equiv.trans_assoc _ _ _).symm,
  one_mul      := equiv.trans_refl,
  mul_one      := equiv.refl_trans,
  mul_left_inv := equiv.self_trans_symm }
-- QUOTE.

/- TEXT:
In fact, mathlib defines exactly this ``group`` structure on ``equiv.perm α``
in the file ``group_theory.perm.basic``.
As always, you can hover over the theorems used in the definition of
``perm_group`` to see their statements,
and you can jump to their definitions in the original file to learn
more about how they are implemented.

In ordinary mathematics, we generally think of notation as
independent of structure.
For example, we can consider groups :math:`(G_1, \cdot, 1, \cdot^{-1})`,
:math:`(G_2, \circ, e, i(\cdot))`, and :math:`(G_3, +, 0, -)`.
In the first case, we write the binary operation as :math:`\cdot`,
the identity at :math:`1`, and the inverse function as :math:`x \mapsto x^{-1}`.
In the second and third cases, we use the notational alternatives shown.
When we formalize the notion of a group in Lean, however,
the notation is more tightly linked to the structure.
In Lean, the components of any ``group`` are named
``mul``, ``one``, and ``inv``,
and in a moment we will see how multiplicative notation is
set up to refer to them.
If we want to use additive notation, we instead use an isomorphic structure
``additive_group``. Its components are named ``add``, ``zero``,
and ``neg``, and the associated notation is what you would expect it to be.

Recall the type ``point`` that we defined in :numref:`section_structures`,
and the addition function that we defined there.
These definitions are reproduced in the examples file that accompanies
this section.
As an exercise, define an ``add_group₁`` structure that is similar
to the ``group₁`` structure we defined above, except that it uses the
additive naming scheme just described.
Define negation and a zero on the ``point`` data type,
and define the ``add_group₁`` structure on ``point``.
BOTH: -/
-- QUOTE:
structure add_group₁ (α : Type*) :=
/- EXAMPLES:
(add : α → α → α)
-- fill in the rest
SOLUTIONS: -/
(add: α → α → α)
(zero: α)
(neg: α → α)
(add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z))
(add_zero: ∀ x : α, add x zero = x)
(zero_add: ∀ x : α, add x zero = x)
(add_left_neg : ∀ x : α, add (neg x) x = zero)
-- BOTH:

@[ext] structure point := (x : ℝ) (y : ℝ) (z : ℝ)

namespace point

def add (a b : point) : point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/- EXAMPLES:
def neg (a b : point) : point := sorry

def zero : point := sorry

def add_group_point : add_group point := sorry
SOLUTIONS: -/
def neg (a : point) : point := ⟨-a.x, -a.y, -a.z⟩

def zero : point := ⟨0, 0, 0⟩

def add_group_point : add_group₁ point :=
{ add          := point.add,
  zero         := point.zero,
  neg          := point.neg,
  add_assoc    := by { simp [point.add, add_assoc] },
  add_zero     := by { simp [point.add, point.zero], intro, ext; refl },
  zero_add     := by { simp [point.add, point.zero], intro, ext; refl },
  add_left_neg := by { simp [point.add, point.neg, point.zero] } }
-- BOTH:

end point
-- QUOTE.

/- TEXT:
We are making progress.
Now we know how to define algebraic structures in Lean,
and we know how to define instances of those structures.
But we also want to associate notation with structures
so that we can use it with each instance.
Moreover, we want to arrange it so that we can define an operation
on a structure and use it with any particular instance,
and we want to arrange it so that we can prove a theorem about
a structure and use it with any instance.

In fact, mathlib is already set up to use generic group notation,
definitions, and theorems for ``equiv.perm α``.
EXAMPLES: -/
section
-- QUOTE:
variables {α : Type*} (f g : equiv.perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g^n

example : f * g * (g⁻¹) = f :=
by { rw [mul_assoc, mul_right_inv, mul_one] }

example : f * g * (g⁻¹) = f := mul_inv_cancel_right f g

example {α : Type*} (f g : equiv.perm α) : g.symm.trans (g.trans f) = f :=
mul_inv_cancel_right f g
-- QUOTE.

end

/- TEXT:
You can check that this is not the case for the additive group structure
on ``point`` that we asked you to define above.
Our task now is to understand that magic that goes on under the hood
in order to make the examples for ``equiv.perm α`` work the way they do.

The issue is that Lean needs to be able to *find* the relevant
notation and the implicit group structure,
using the information that is found in the expressions that we type.
Similarly, when we write ``x + y`` with expressions ``x`` and ``y``
that have type ``ℝ``, Lean needs to interpret the ``+``
symbol as the relevant addition function on the reals.
It also has to recognize the type ``ℝ`` as an instance of a commutative ring,
so that all the definitions and theorems for a commutative ring are available.
For another example,
continuity is defined in Lean relative to any two topological spaces.
When we have ``f : ℝ → ℂ`` and we write ``continuous f``, Lean has to find the
relevant topologies on ``ℝ`` and ``ℂ``.

The magic is achieved with a combination of three things.

#. *Logic.* A definition that should be interpreted in any group takes, as
   arguments, the type of the group and the group structure as arguments.
   Similarly, a theorem about the elements of an arbitrary group
   begins with universal quantifiers over
   the type of the group and the group structure.

#. *Implicit arguments.* The arguments for the type and the structure
   are generally left implicit, so that we do not have to write them
   or see them in the Lean information window. Lean fills the
   information in for us silently.

#. *Type class inference.* Also known as *class inference*,
   this is a simple but powerful mechanism
   that enables us to register information for Lean to use later on.
   When Lean is called on to fill in implicit arguments to a
   definition, theorem, or piece of notation,
   it can make use of information that has been registered.

Whereas an annotation ``(grp : group G)`` tells Lean that it should
expect to be given that argument explicitly and the annotation
``{grp : group G}`` tells Lean that it should try to figure it out
from contextual cues in the expression,
the annotation ``[grp : group G]`` tells Lean that the corresponding
argument should be synthesized using type class inference.
Since the whole point to the use of such arguments is that
we generally do not need to refer to them explicitly,
Lean allows us to write ``[group G]`` and leave the name anonymous.
You have probably already noticed that Lean chooses names like ``_inst_1``
automatically.
When we use the anonymous square-bracket annotation with the ``variables`` command,
then as long as the variables are still in scope,
Lean automatically adds the argument ``[group G]`` to any definition or
theorem that mentions ``G``.

How do we register the information that Lean needs to use to carry
out the search?
Returning to our group example, we need only make two changes.
First, instead of using the ``structure`` command to define the group structure,
we use the keyword ``class`` to indicate that it is a candidate
for class inference.
Second, instead of defining particular instances with ``def``,
we use the keyword ``instance`` to register the particular instance with
Lean. As with the names of class variables, we are allowed to leave the
name of an instance definition anonymous,
since in general we intend Lean to find it and put it to use
without troubling us with the details.
EXAMPLES: -/
-- QUOTE:
class group₂ (α : Type*) :=
(mul: α → α → α)
(one: α)
(inv: α → α)
(mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z))
(mul_one: ∀ x : α, mul x one = x)
(one_mul: ∀ x : α, mul x one = x)
(mul_left_inv : ∀ x : α, mul (inv x) x = one)

instance {α : Type*} : group₂ (equiv.perm α) :=
{ mul          := λ f g, equiv.trans g f,
  one          := equiv.refl α,
  inv          := equiv.symm,
  mul_assoc    := λ f g h, (equiv.trans_assoc _ _ _).symm,
  one_mul      := equiv.trans_refl,
  mul_one      := equiv.refl_trans,
  mul_left_inv := equiv.self_trans_symm }
-- QUOTE.

/- TEXT:
The following illustrates their use.
EXAMPLES: -/
-- QUOTE:
#check @group₂.mul

def my_square {α : Type*} [group₂ α] (x : α) := group₂.mul x x

#check @my_square

section
variables {β : Type*} (f g : equiv.perm β)

example : group₂.mul f g = g.trans f := rfl

example : my_square f = f.trans f := rfl

end
-- QUOTE.

/- TEXT:
The ``#check`` command shows that ``group₂.mul`` has an implicit argument
``[group₂ α]`` that we expect to be found by class inference,
where ``α`` is the type of the arguments to ``group₂.mul``.
In other words, ``{α : Type*}`` is the implicit argument for the type
of the group elements and ``[group₂ α]`` is the implicit argument for the
group structure on ``α``.
Similarly, when we define a generic squaring function ``my_square``
for ``group₂``, we use an implicit argument ``{α : Type*}`` for
the type of the elements and an implicit argument ``[group₂ α]`` for
the ``group₂`` structure.

In the first example,
when we write ``group₂.mul f g``, the type of ``f`` and ``g``
tells Lean that in the argument ``α`` to ``group₂.mul``
has to be instantiated to ``equiv.perm β``.
That means that Lean has to find an element of ``group₂ (equiv.perm β)``.
The previous ``instance`` declaration tells Lean exactly how to do that.
Problem solved!

This simple mechanism for registering information so that Lean can find it
when it needs it is remarkably useful.
Here is one way it comes up.
In Lean's foundation, a data type ``α`` may be empty.
In a number of applications, however, it is useful to know that a
type has at least one element.
For example, the function ``list.head``, which returns the first
element of a list, can return the default value when the list is empty.
To make that work, the Lean library defines a class ``inhabited α``,
which does nothing more than store a default value.
We can show that the ``point`` type is an instance:
EXAMPLES: -/
-- QUOTE:
instance : inhabited point := { default := ⟨0, 0, 0⟩ }

#check (default : point)

example : ([] : list point).head = default := rfl
-- QUOTE.

/- TEXT:
The class inference mechanism is also used for generic notation.
The expression ``x + y`` is an abbreviation for ``has_add.add x y``
where---you guessed it---``has_add α`` is a class that stores
a binary function on ``α``.
Writing ``x + y`` tells Lean to find a registered instance of ``[has_add.add α]``
and use the corresponding function.
Below, we register the addition function for ``point``.
EXAMPLES: -/
-- QUOTE:
instance : has_add point := { add := point.add }

section
variables x y : point

#check x + y

example : x + y = point.add x y := rfl

end
-- QUOTE.

/- TEXT:
In this way, we can assign the notation ``+`` to binary operations on other
types as well.

But we can do even better. We have seen that ``*`` can be used in any
group, ``+`` can be used in any additive group, and both can be used in
any ring.
When we define a new instance of a ring in Lean,
we don't have to define ``+`` and ``*`` for that instance,
because Lean knows that these are defined for every ring.
We can use this method to specify notation for our ``group₂`` class:
EXAMPLES: -/
-- QUOTE:
instance has_mul_group₂ {α : Type*} [group₂ α] : has_mul α := ⟨group₂.mul⟩

instance has_one_group₂ {α : Type*} [group₂ α] : has_one α := ⟨group₂.one⟩

instance has_inv_group₂ {α : Type*} [group₂ α] : has_inv α := ⟨group₂.inv⟩

section
variables {α : Type*} (f g : equiv.perm α)

#check f * 1 * g⁻¹

def foo: f * 1 * g⁻¹ = g.symm.trans ((equiv.refl α).trans f) := rfl

end
-- QUOTE.

/- TEXT:
In this case, we have to supply names for the instances, because
Lean has a hard time coming up with good defaults.
What makes this approach work is that Lean carries out a recursive search.
According to the instances we have declared, Lean can find an instance of
``has_mul (equiv.perm α)`` by finding an
instance of ``group₂ (equiv.perm α)``, and it can find an instance of
``group₂ (equiv.perm α)`` because we have provided one.
Lean is capable of finding these two facts and chaining them together.

The example we have just given is dangerous, because Lean's
library also has an instance of ``group (equiv.perm α)``, and
multiplication is defined on any group.
So it is ambiguous as to which instance is found.
In fact, Lean favors more recent declarations unless you explicitly
specify a different priority.
Also, there is another way to tell Lean that one structure is an
instance of another, using the ``extends`` keyword.
This is how ``mathlib`` specifies that, for example,
every commutative ring is a ring.
You can find more information in a
`section on class inference <https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#managing-type-class-inference>`_ in *Theorem Proving in Lean*.

In general, it is a bad idea to specify a value of
``*`` for an instance of an algebraic structure that already has
the notation defined.
Redefining the notion of ``group`` in Lean is an artificial example.
In this case, however, both interpretations of the group notation unfold to
``equiv.trans``, ``equiv.refl``, and ``equiv.symm``, in the same way.

As a similarly artificial exercise,
define a class ``add_group₂`` in analogy to ``group₂``.
Define the usual notation for addition, negation, and zero
on any ``add_group₂``
using the classes ``has_add``, ``has_neg``, and ``has_zero``.
Then show ``point`` is an instance of ``add_group₂``.
Try it out and make sure that the additive group notation works for
elements of ``point``.
BOTH: -/
-- QUOTE:
class add_group₂ (α : Type*) :=
/- EXAMPLES:
(add : α → α → α)
-- fill in the rest
-- QUOTE.
SOLUTIONS: -/
(add: α → α → α)
(zero: α)
(neg: α → α)
(add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z))
(add_zero: ∀ x : α, add x zero = x)
(zero_add: ∀ x : α, add x zero = x)
(add_left_neg : ∀ x : α, add (neg x) x = zero)

instance has_add_add_group₂ {α : Type*} [add_group₂ α] :
has_add α := ⟨add_group₂.add⟩

instance has_zero_add_group₂ {α : Type*} [add_group₂ α] :
has_zero α := ⟨add_group₂.zero⟩

instance has_neg_add_group₂ {α : Type*} [add_group₂ α] :
has_neg α := ⟨add_group₂.neg⟩

instance : add_group₂ point :=
{ add          := point.add,
  zero         := point.zero,
  neg          := point.neg,
  add_assoc    := by { simp [point.add, add_assoc] },
  add_zero     := by { simp [point.add, point.zero], intro, ext; refl },
  zero_add     := by { simp [point.add, point.zero], intro, ext; refl },
  add_left_neg := by { simp [point.add, point.neg, point.zero] } }

section
variables (x y : point)

#check x + -y + 0
end

/- TEXT:
It is not a big problem that we have already declared instances
``has_add``, ``has_neg``, and ``has_zero`` for ``point`` above.
Once again, the two ways of synthesizing the notation should come up
with the same answer.

Class inference is subtle, and you have to be careful when using it,
because it configures automation that invisibly governs the interpretation of
the expressions we type.
When used wisely, however, class inference is a powerful tool.
It is what makes algebraic reasoning possible in Lean.
TEXT. -/

