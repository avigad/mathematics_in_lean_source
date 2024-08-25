import MIL.Common
import Mathlib.Topology.Instances.Real

set_option autoImplicit true

/- TEXT:
.. _section_hierarchies_morphisms:

Morphisms
---------

So far in this chapter, we discussed how to create a hierarchy of mathematical structures.
But defining structures is not really completed until we have morphisms. There are two
main approaches here. The most obvious one is to define a predicate on functions.
BOTH: -/

-- QUOTE:
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- TEXT:
In this definition, it is a bit unpleasant to use a conjunction. In particular users
will need to remember the ordering we chose when they want to access the two conditions.
So we could use a structure instead.

BOTH: -/
-- QUOTE:
structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- TEXT:
Once we are here, it is even tempting to make it a class and use the type class instance resolution
procedure to automatically infer ``isMonoidHom₂`` for complicated functions out of instances for
simpler functions. For instance a composition of monoid morphisms is a monoid morphism and this
seems like a useful instance. However such an instance would be very tricky for the resolution
procedure since it would need to hunt down ``g ∘ f`` everywhere. Seeing it failing in ``g (f x)``
would be very frustrating. More generally one must always keep in mind that recognizing which
function is applied in a given expression is a very difficult problem, called the "higher-order
unification problem". So Mathlib does not use this class approach.

A more fundamental question is whether we use predicates as above (using either a ``def`` or a
``structure``) or use structures bundling a function and predicates. This is partly a psychological
issue. It is extremely rare to consider a function between monoids that is not a morphism.
It really feels like "monoid morphism" is not an adjective you can assign to a bare function,
it is a noun. On the other hand one can argue that a continuous function between topological spaces
is really a function that happens to be continuous. This is one reason why Mathlib has a
``Continuous`` predicate. For instance you can write:

BOTH: -/
-- QUOTE:
example : Continuous (id : ℝ → ℝ) := continuous_id
-- QUOTE.
/- TEXT:
We still have bundles of continuous functions, which are convenient for instance to put a topology
on a space of continuous functions, but they are not the primary tool to work with continuity.

By contrast, morphisms between monoids (or other algebraic structures) are bundled as in:

BOTH: -/
-- QUOTE:
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

-- QUOTE.
/- TEXT:
Of course we don't want to type ``toFun`` everywhere so we register a coercion using
the ``CoeFun`` type class. Its first argument is the type we want to coerce to a function.
The second argument describes the target function type. In our case it is always ``G → H``
for every ``f : MonoidHom₁ G H``. We also tag ``MonoidHom₁.toFun`` with the ``coe`` attribute to
make sure it is displayed almost invisibly in the tactic state, simply by a ``↑`` prefix.

BOTH: -/
-- QUOTE:
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun
-- QUOTE.

/- TEXT:
Let us check we can indeed apply a bundled monoid morphism to an element.

BOTH: -/

-- QUOTE:
example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one
-- QUOTE.
/- TEXT:
We can do the same with other kind of morphisms until we reach ring morphisms.

BOTH: -/

-- QUOTE:
@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

-- QUOTE.

/- TEXT:
There are a couple of issues about this approach. A minor one is we don't quite know where to put
the ``coe`` attribute since the ``RingHom₁.toFun`` does not exist, the relevant function is
``MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁`` which is not a declaration that can be tagged with an
attribute (but we could still define a ``CoeFun  (RingHom₁ R S) (fun _ ↦ R → S)`` instance).
A much more important one is that lemmas about monoid morphisms won't directly apply
to ring morphisms. This leaves the alternative of either juggling with ``RingHom₁.toMonoidHom₁``
each time we want to apply a monoid morphism lemma or restate every such lemmas for ring morphisms.
Neither option is appealing so Mathlib uses a new hierarchy trick here. The idea is to define
a type class for objects that are at least monoid morphisms, instantiate that class with both monoid
morphisms and ring morphisms and use it to state every lemma. In the definition below,
``F`` could be ``MonoidHom₁ M N``, or ``RingHom₁ M N`` if ``M`` and ``N`` have a ring structure.

BOTH: -/

-- QUOTE:
class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'
-- QUOTE.

/- TEXT:
However there is a problem with the above implementation. We haven't registered a coercion to
function instance yet. Let us try to do it now.

BOTH: -/

-- QUOTE:
def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun
-- QUOTE.

/- TEXT:
Making this an instance would be bad. When faced with something like ``f x`` where the type of ``f``
is not a function type, Lean will try to find a ``CoeFun`` instance to coerce ``f`` into a function.
The above function has type:
``{M N F : Type} → [Monoid M] → [Monoid N] → [MonoidHomClass₁ F M N] → CoeFun F (fun x ↦ M → N)``
so, when it trying to apply it, it wouldn't be a priori clear to Lean in which order the unknown
types ``M``, ``N`` and ``F`` should be inferred. This is a kind of bad instance that is slightly
different from the one we saw already, but it boils down to the same issue: without knowing ``M``,
Lean would have to search for a monoid instance on an unknown type, hence hopelessly try *every*
monoid instance in the database. If you are curious to see the effect of such an instance you
can type ``set_option synthInstance.checkSynthOrder false in`` on top of the above declaration,
replace ``def badInst`` with ``instance``, and look for random failures in this file.

Here the solution is easy, we need to tell Lean to first search what is ``F`` and then deduce ``M``
and ``N``. This is done using the ``outParam`` function. This function is defined as the identity
function, but is still recognized by the type class machinery and triggers the desired behavior.
Hence we can retry defining our class, paying attention to the ``outParam`` function:
BOTH: -/

-- QUOTE:
class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun
-- QUOTE.

/- TEXT:
Now we can proceed with our plan to instantiate this class.

BOTH: -/

-- QUOTE:
instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
-- QUOTE.

/- TEXT:
As promised every lemma we prove about ``f : F`` assuming an instance of ``MonoidHomClass₁ F`` will
apply both to monoid morphisms and ring morphisms.
Let us see an example lemma and check it applies to both situations.
BOTH: -/

-- QUOTE:
lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h

-- QUOTE.

/- TEXT:
At first sight, it may look like we got back to our old bad idea of making ``MonoidHom₁`` a class.
But we haven't. Everything is shifted one level of abstraction up. The type class resolution
procedure won't be looking for functions, it will be looking for either
``MonoidHom₁`` or ``RingHom₁``.

One remaining issue with our approach is the presence of repetitive code around the ``toFun``
field and the corresponding ``CoeFun`` instance and ``coe`` attribute. It would also be better
to record that this pattern is used only for functions with extra properties, meaning that the
coercion to functions should be injective. So Mathlib adds one more layer of abstraction with
the base class ``DFunLike`` (where “DFun” stands for dependent function).
Let us redefine our ``MonoidHomClass`` on top of this base layer.

BOTH: -/

-- QUOTE:
class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' _ _ := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul
-- QUOTE.

/- TEXT:
Of course the hierarchy of morphisms does not stop here. We could go on and define a class
``RingHomClass₃`` extending ``MonoidHomClass₃`` and instantiate it on ``RingHom`` and
then later on ``AlgebraHom`` (algebras are rings with some extra structure). But we've
covered the main formalization ideas used in Mathlib for morphisms and you should be ready
to understand how morphisms are defined in Mathlib.

As an exercise, you should try to define your class of bundled order-preserving function between
ordered types, and then order preserving monoid morphisms. This is for training purposes only.
Like continuous functions, order preserving functions are primarily unbundled in Mathlib where
they are defined by the ``Monotone`` predicate. Of course you need to complete the class
definitions below.
BOTH: -/

-- QUOTE:
@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]
-- SOLUTIONS:
extends DFunLike F α (fun _ ↦ β) where
  le_of_le : ∀ (f : F) a a', a ≤ a' → f a ≤ f a'
-- BOTH:

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where
-- SOLUTIONS:
  coe := OrderPresHom.toFun
  coe_injective' _ _ := OrderPresHom.ext
  le_of_le := OrderPresHom.le_of_le
-- BOTH:

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
-- SOLUTIONS:
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' _ _ := OrderPresMonoidHom.ext
  le_of_le := fun f ↦ f.toOrderPresHom.le_of_le
-- BOTH:

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β
/- EXAMPLES:
  := sorry
SOLUTIONS: -/
where
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' _ _ := OrderPresMonoidHom.ext
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
-- QUOTE.
