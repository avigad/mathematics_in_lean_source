import algebra.big_operators.ring
import data.real.basic

/- TEXT:
.. _section_structures:

Structures
----------

In the broadest sense of the term, a *structure* is a specification
of a collection of data, possibly with contraints that the
data is required to satisfy.
An *instance* of the structure is a particular bundle of data satisfying
the constraints. For example, we can specify that a point is
a tuple of three real numbers:
BOTH: -/
-- QUOTE:
@[ext] structure point := (x : ℝ) (y : ℝ) (z : ℝ)
-- QUOTE.

/- TEXT:
The ``@[ext]`` annotation tells Lean to automatically generate theorems
that can be used to prove that two instances of a structure are equal
when their components are equal, a property known as *extensionality*.
EXAMPLES: -/
-- QUOTE:
#check point.ext

example (a b : point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
  a = b :=
begin
  ext,
  repeat { assumption }
end
-- QUOTE.

/- TEXT:
We can then define particular instances of the ``point`` structure.
Lean provides multiple ways of doing that.
EXAMPLES: -/
-- QUOTE:
def my_point1 : point :=
{ x := 2,
  y := -1,
  z := 4 }

def my_point2 :=
{ point .
  x := 2,
  y := -1,
  z := 4 }

def my_point3 : point := ⟨2, -1, 4⟩

def my_point4 := point.mk 2 (-1) 4
-- QUOTE.

/- TEXT:
In the first two examples, the fields of the structure are named
explicitly.
In the first case, because Lean knows that the expected type of
``my_point1`` is a ``point``, you can start the definition by
writing an underscore, ``_``. Clicking on the light bulb
that appears nearby in VS Code will then
give you the option of inserting a template definition
with the field names listed for you.

The function ``point.mk`` referred to in the definition of ``my_point4``
is known as the *constructor* for the ``point`` structure, because
it serves to construct elements.
You can specify a different name if you want, like ``build``.
EXAMPLES: -/
-- QUOTE:
structure point' := build :: (x : ℝ) (y : ℝ) (z : ℝ)

#check point'.build 2 (-1) 4
-- QUOTE.

/- TEXT:
The next two examples show how to define functions on structures.
Whereas the second example makes the ``point.mk``
constructor explicit, the first example uses an anonymous constructor
for brevity.
Lean can infer the relevant constructor from the indicated type of
``add``.
It is conventional to put definitions and theorems associated
with a structure like ``point`` in a namespace with the same name.
In the example below, because we have opened the ``point``
namespace, the full name of ``add`` is ``point.add``.
When the namespace is not open, we have to use the full name.
But remember that it is often convenient to use
anonymous projection notation,
which allows us to write ``a.add b`` instead of ``point.add a b``.
Lean interprets the former as the latter because ``a`` has type ``point``.
BOTH: -/
-- QUOTE:
namespace point

def add (a b : point) : point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

-- EXAMPLES:
def add' (a b : point) : point :=
{ x := a.x + b.x,
  y := a.y + b.y,
  z := a.z + b.z }

#check add my_point1 my_point2
#check my_point1.add my_point2

end point

#check point.add my_point1 my_point2
#check my_point1.add my_point2
-- QUOTE.

/- TEXT:
Below we will continue to put definitions in the relevant
namespace, but we will leave the namespacing commands out of the quoted
snippets. To prove properties of the addition function,
we can use ``rw`` to expand the definition and ``ext`` to
reduce an equation between two elements of the structure to equations
between the components.
Below we use the ``protected`` keyword so that the name of the
theorem is ``point.add_comm``, even when the namespace is open.
This is helpful when we want to avoid ambiguity with a generic
theorem like ``add_comm``.
EXAMPLES: -/
namespace point

-- QUOTE:
protected theorem add_comm (a b : point) : add a b = add b a :=
begin
  rw [add, add],
  ext; dsimp,
  repeat { apply add_comm }
end

example (a b : point) : add a b = add b a :=
by simp [add, add_comm]
-- QUOTE.

/- TEXT:
Because Lean can unfold definitions and simplify projections
internally, sometimes the equations we want hold definitionally.
EXAMPLES: -/
-- QUOTE:
theorem add_x (a b : point) : (a.add b).x = a.x + b.x := rfl
-- QUOTE.

/- TEXT:
It is also possible to define functions on structures using
pattern matching,
in a manner similar to the way we defined recursive functions in
:numref:`section_induction_and_recursion`.
The definitions ``add_alt`` and ``add_alt'`` below are essentially the
same; the only difference is that we use anonymous constructor notation
in the second.
Although it is sometimes convenient to define functions this way,
the definitional properties are not as convenient.
For example, the expressions ``add_alt a b`` and ``add_alt' a b``
cannot be simplified until we decompose ``a`` and ``b`` into
components, which we can do with ``cases``, ``rcases``, etc.

EXAMPLES: -/
-- QUOTE:
def add_alt : point → point → point
| (point.mk x₁ y₁ z₁) (point.mk x₂ y₂ z₂) := ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def add_alt' : point → point → point
| ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩ := ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem add_alt_x (a b : point) : (a.add_alt b).x = a.x + b.x :=
by { cases a, cases b, refl }

theorem add_alt_comm (a b : point) : add_alt a b = add_alt b a :=
begin
  rcases a with ⟨xa, ya, za⟩,
  rcases b with ⟨xb, yb, zb⟩,
  rw [add_alt, add_alt],
  ext; dsimp,
  apply add_comm,
  repeat { apply add_comm },
end

example (a b : point) : add_alt a b = add_alt b a :=
begin
  rcases a with ⟨xa, ya, za⟩,
  rcases b with ⟨xb, yb, zb⟩,
  simp [add_alt, add_comm]
end

example : ∀ a b : point, add_alt a b = add_alt b a :=
begin
  rintros ⟨xa, ya, za⟩ ⟨xb, yb, zb⟩,
  simp [add_alt, add_comm]
end

example : ∀ a b : point, add a b = add b a :=
λ ⟨xa, ya, za⟩ ⟨xb, yb, zb⟩, by simp [add, add_comm]
-- QUOTE.

/- TEXT:
Mathematical constructions often involve taking apart bundled information and
putting it together again in different ways.
It therefore makes sense that Lean and mathlib offer so many ways
of doing this efficiently.
As an exercise, try proving that ``point.add`` is associative.
Then define scalar multiplication for a point and show that it
distributes over addition.
BOTH: -/
-- QUOTE:
protected theorem add_assoc (a b c : point) :
  (a.add b).add c = a.add (b.add c) :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
by { simp [add, add_assoc] }
-- BOTH:

def smul (r : ℝ) (a : point) : point :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
⟨r * a.x, r * a.y, r * a.z⟩
-- BOTH:

theorem smul_distrib (r : ℝ) (a b : point) :
  (smul r a).add (smul r b) = smul r (a.add b) :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
by { simp [add, smul, mul_add] }
-- BOTH:
-- QUOTE.

end point

/- TEXT:
Using structures is only the first step on the road to
algebraic abstraction.
We don't yet have a way to link ``point.add`` to the generic ``+`` symbol,
or to connect ``point.add_comm`` and ``point.add_assoc`` to
the generic ``add_comm`` and ``add_assoc`` theorems.
These tasks belong to the *algebraic* aspect of using structures,
and we will explain how to carry them out in the next section.
For now, just think of a structure as a way of bundling together objects
and information.

It is especially useful that a structure can specify not only
data types but also constraints that the data must satisfy.
In Lean, the latter are represented as fields of type ``Prop``.
For example, the *standard 2-simplex* is defined to be the set of
points :math:`(x, y, z)` satisfying :math:`x ≥ 0`, :math:`y ≥ 0`, :math:`z ≥ 0`,
and :math:`x + y + z = 1`.
If you are not familiar with the notion, you should draw a picture,
and convince yourself that this set is
the equilateral triangle in three-space with vertices
:math:`(1, 0, 0)`, :math:`(0, 1, 0)`, and :math:`(0, 0, 1)`,
together with its interior.
We can represent it in Lean as follows:
BOTH: -/
-- QUOTE:
structure standard_two_simplex :=
(x : ℝ)
(y : ℝ)
(z : ℝ)
(x_nonneg : 0 ≤ x)
(y_nonneg : 0 ≤ y)
(z_nonneg : 0 ≤ z)
(sum_eq   : x + y + z = 1)
-- QUOTE.

/- TEXT:
Notice that the last four fields refer to ``x``, ``y``, and ``z``,
that is, the first three fields.
We can define a map from the two-simplex to itself that swaps ``x`` and ``y``:
BOTH: -/
namespace standard_two_simplex

-- EXAMPLES:
-- QUOTE:
def swap_xy (a : standard_two_simplex) : standard_two_simplex :=
{ x := a.y,
  y := a.x,
  z := a.z,
  x_nonneg := a.y_nonneg,
  y_nonneg := a.x_nonneg,
  z_nonneg := a.z_nonneg,
  sum_eq   := by rw [add_comm a.y a.x, a.sum_eq] }
-- QUOTE.

-- OMIT: (TODO) add a link when we have a good explanation of noncomputable theory.
/- TEXT:
More interestingly, we can compute the midpoint of two points on
the simplex. We need to add ``noncomputable theory`` in order to
use division on the real numbers.
BOTH: -/
-- QUOTE:
noncomputable theory

-- EXAMPLES:
def midpoint (a b : standard_two_simplex) : standard_two_simplex :=
{ x        := (a.x + b.x) / 2,
  y        := (a.y + b.y) / 2,
  z        := (a.z + b.z) / 2,
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num),
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num),
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num),
  sum_eq   := by { field_simp, linarith [a.sum_eq, b.sum_eq]} }
-- QUOTE.

/- TEXT:
Here we have established ``x_nonneg``, ``y_nonneg``, and ``z_nonneg``
with concise proof terms, but establish ``sum_eq`` in tactic mode,
using ``by``. You can just as well use a ``begin ... end`` block
for that purpose.

Given a parameter :math:`\lambda` satisfying :math:`0 \le \lambda \le 1`,
we can take the weighted average :math:`\lambda a + (1 - \lambda) b`
of two points :math:`a` and :math:`b` in the standard 2-simplex.
We challenge you to define that function, in analogy to the ``midpoint``
function above.
BOTH: -/
-- QUOTE:
def weighted_average (lambda : real)
    (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : standard_two_simplex) :
  standard_two_simplex :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
{ x        := lambda * a.x + (1 - lambda) * b.x,
  y        := lambda * a.y + (1 - lambda) * b.y,
  z        := lambda * a.z + (1 - lambda) * b.z,
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg)
                (mul_nonneg (by linarith) b.x_nonneg),
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg)
                (mul_nonneg (by linarith) b.y_nonneg),
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg)
                (mul_nonneg (by linarith) b.z_nonneg),
  sum_eq   :=
    begin
      transitivity (a.x + a.y + a.z) * lambda + (b.x + b.y + b.z) * (1 - lambda),
      { ring },
      simp [a.sum_eq, b.sum_eq]
    end }
-- QUOTE.
-- BOTH:

end standard_two_simplex

/- TEXT:
Structures can depend on parameters.
For example, we can generalize the standard 2-simplex to the standard
:math:`n`-simplex for any :math:`n`.
At this stage, you don't have to know anything about the type `fin n`
except that it has :math:`n` elements, and that Lean knows
how to sum over it.
BOTH: -/
-- QUOTE:
open_locale big_operators

structure standard_simplex (n : ℕ) :=
(v          : fin n → ℝ)
(nonneg     : ∀ i : fin n, 0 ≤ v i)
(sum_eq_one : ∑ i, v i = 1)

namespace standard_simplex

def midpoint (n : ℕ) (a b : standard_simplex n) : standard_simplex n :=
{ v := λ i, (a.v i + b.v i) / 2,
  nonneg :=
    begin
      intro i,
      apply div_nonneg,
      { linarith [a.nonneg i, b.nonneg i] },
      norm_num
    end,
  sum_eq_one :=
    begin
      simp [div_eq_mul_inv, ←finset.sum_mul, finset.sum_add_distrib,
        a.sum_eq_one, b.sum_eq_one],
      field_simp
    end  }

end standard_simplex
-- QUOTE.

/- TEXT:
As an exercise, see if you can define the weighted average of
two points in the standard :math:`n`-simplex.
You can use ``finset.sum_add_distrib``
and ``finset.mul_sum`` to manipulate the relevant sums.

SOLUTIONS: -/
namespace standard_simplex

def weighted_average {n : ℕ} (lambda : real)
    (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : standard_simplex n) : standard_simplex n :=
{ v          := λ i, lambda * a.v i + (1 - lambda) * b.v i,
  nonneg     := λ i, add_nonneg (mul_nonneg lambda_nonneg (a.nonneg i))
                  (mul_nonneg (by linarith) (b.nonneg i)),
  sum_eq_one :=
    begin
      transitivity lambda * (∑ i, a.v i) + (1 - lambda) * (∑ i, b.v i),
      { rw [finset.sum_add_distrib, finset.mul_sum, finset.mul_sum] },
      simp [a.sum_eq_one, b.sum_eq_one]
    end }

end standard_simplex

/- TEXT:
We have seen that structures can be used to bundle together data
and properties.
Interestingly, they can also be used to bundle together properties
without the data.
For example, the next structure, ``is_linear``, bundles together
the two components of linearity.
EXAMPLES: -/
-- QUOTE:
structure is_linear (f : ℝ → ℝ) :=
(is_additive : ∀ x y, f (x + y) = f x + f y)
(preserves_mul : ∀ x c, f (c * x) = c * f x)

section
variables (f : ℝ → ℝ) (linf : is_linear f)

#check linf.is_additive
#check linf.preserves_mul

end
-- QUOTE.

/- TEXT:
It is worth pointing out that structures are not the only way to bundle
together data.
The ``point`` data structure can be defined using the generic type product,
and ``is_linear`` can be defined with a simple ``and``.
EXAMPLES: -/
-- QUOTE:
def point'' := ℝ × ℝ × ℝ

def is_linear' (f : ℝ → ℝ) :=
(∀ x y, f (x + y) = f x + f y) ∧ (∀ x c, f (c * x) = c * f x)
-- QUOTE.

/- TEXT:
Generic type constructions can even be used in place of structures
with dependencies between their components.
For example, the *subtype* construction combines a piece of data with
a property.
You can think of the type ``preal`` in the next example as being
the type of positive real numbers.
Any ``x : preal`` has two components: the value, and the property of being
positive.
You can access these components as ``x.val``, which has type ``ℝ``,
and ``x.property``, which represents the fact ``0 < x.val``.
EXAMPLES: -/
-- QUOTE:
def preal := { y : ℝ // 0 < y }

section
variable x : preal

#check x.val
#check x.property

#check x.1
#check x.2

end
-- QUOTE.

/- TEXT:
We could have used subtypes to define the standard 2-simplex,
as well as the standard :math:`n`-simplex for an arbitrary :math:`n`.
EXAMPLES: -/
-- QUOTE:
def standard_two_simplex' :=
{ p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def standard_simplex' (n : ℕ) :=
{ v : fin n → ℝ // (∀ i : fin n, 0 ≤ v i) ∧ (∑ i, v i = 1) }
-- QUOTE.

/- TEXT:
Similarly, *Sigma types* are generalizations of ordered pairs,
whereby the type of the second component depends on the type of
the first.
EXAMPLES: -/
-- QUOTE:
def std_simplex := Σ n : ℕ, standard_simplex n

section
variable s : std_simplex

#check s.fst
#check s.snd

#check s.1
#check s.2

end
-- QUOTE.

/- TEXT:
Given ``s : std_simplex``, the first component ``s.fst`` is a natural
number, and the second component is an element of the corresponding
simplex ``standard_simplex s.fst``.
The difference between a Sigma type and a subtype is that
the second component of a Sigma type is data rather than a proposition.

But even though we can use products, subtypes, and Sigma types
instead of structures, using structures has a number of advantages.
Defining a structure abstracts away the underlying representation
and provides custom names for the functions that access the components.
This makes proofs more robust:
proofs that rely only on the interface to a structure
will generally continue to work when we change the definition,
as long as we redefine the old accessors in terms of the new definition.
Moreover, as we are about to see, Lean provides support for
weaving structures together into a rich, interconnected hierarchy,
and for managing the interactions between them.
TEXT. -/

/- OMIT: (TODO)
Comments from Patrick:
We could make this paragraph much less abstract by showing how to access the components of a point with the definition def point'' := ℝ × ℝ × ℝ. However if we do that it would probably be honest to also mention the possibility of using fin 3 → ℝ as the definition. This interesting anyhow, because I think very few mathematician realize that defining ℝ^n as an iterated cartesian product is a polite lie that would be a nightmare if taken seriously.

By the way, should be include some comment about similarities and differences with object-oriented programming? All the examples from that page would clearly fit very well with classes in python say. And we'll have to face the name-clash between classes in Lean and classes in C++ or python sooner or later. Life would be so much simpler if classes in Lean could use another name...
OMIT. -/
