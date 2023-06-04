import Mathlib.Topology.Instances.Real

/- TEXT:
.. _section_hierarchies_morphisms:

Morphisms
---------

So far in this chapter we discussed how to create a hierarchy of mathematical structures,
but defining structures is not really completed until we have morphisms. There are two
main approaches here. The most obvious one is to define a predicate on functions.
BOTH: -/

-- QUOTE:
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- TEXT:
In this definition it is a bit unpleasant to use a conjunction. In particular users
will need to remember the ordering we chose when they want to access the individual parts.
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
procedure since it would need to hunt down ``g ∘ f`` everywhere. Sometimes it would not
succeed, for instance in ``g (f x)``. And sometimes it would succeed to much by seeing
``id ∘ f`` or ``g ∘ id`` everywhere, leading to a diverging instance search.

So Mathlib does not use this class approach. A more fundamental question is whether we use
predicates as above (using either a ``def`` or a ``structure``) or use structures bundling a
function and predicates. This is partly a psychological issue. It is
extremely rare to consider a function between monoids that is not a morphism. It really feels
like "monoid morphism" is not an adjective you can assign to a bare function, it is a noun.
On the other hand one can argue that a continuous function between topological spaces is
really a function that happens to be continuous. This is one reason why Mathlib has a
``Continuous`` predicate. For instance you can write:

BOTH: -/
-- QUOTE:
example : Continuous (id : ℝ → ℝ) := continuous_id
-- QUOTE.
/- TEXT:
But morphisms between monoids (or other algebraic structures) are bundled as in:

BOTH: -/
-- QUOTE:

structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one' : toFun 1 = 1
  map_mul' : ∀ g g', toFun (g * g') = toFun g * toFun g'

-- QUOTE.
/- TEXT:
Of course we don't want to type ``toFun`` everywhere so we register a coercion using
the ``CoeFun`` type class. Its first argument is the type we want to coerce to function.
The second argument describes the target function typ. In our case it is always ``G → H``
for every ``f : MonoidHom₁ G H``.

BOTH: -/
-- QUOTE:
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H)where
  coe := MonoidHom₁.toFun
-- QUOTE.

/- TEXT:
Let us check we can indeed now apply a bundled monoid morphism to an element.

BOTH: -/
-- QUOTE:
example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 := by
  exact f.map_one'
-- QUOTE.
/- TEXT:
Note that Lean happily accepts that proof because ``f.map_one'`` has type ``f.toFun 1 = 1``
which is definitionaly equal to the expected type.
-/
#check MonoidHom
