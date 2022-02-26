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
when their components are equal.
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
writing ``{! !}``. Clicking on the light bulb
that appears nearby in VS Code will then
give you the option of inserting a template definition
with the field names listed for you.

By default, the *constructor* for the ``point`` structure is named
``point.mk``. You can specify a different name if you want.
EXAMPLES: -/
-- QUOTE:
structure point' := build :: (x : ℝ) (y : ℝ) (z : ℝ)

#check point'.build 2 (-1) 4
-- QUOTE.

/- TEXT:
The next two examples show how to define functions
on structures using pattern matching.
Whereas the second example makes the ``point.mk``
constructor explicit, the first example uses anonymous constructors
for brevity.
Lean can infer the relevant constructor from the indicated type of
``add``.
It is conventional to put definitions and theorems associated
with a structure like ``point`` in a namespace with the same name.
In the example below, the full name of ``add`` is ``point.add``,
which allows us to use the anonymous projection notation.
BOTH: -/
-- QUOTE:
namespace point

def add : point → point → point
| ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩ := ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

-- EXAMPLES:
def add' : point → point → point
| (point.mk x₁ y₁ z₁) (point.mk x₂ y₂ z₂) :=
  { x := x₁ + x₂,
    y := y₁ + y₂,
    z := z₁ + z₂ }

#check add my_point1 my_point2
#check my_point1.add my_point2

end point

#check point.add my_point1 my_point2
#check my_point1.add my_point2
-- QUOTE.

/- TEXT:
Below we will continue to put definitions in the relevant
namespace, but we will leave the namespacing commands out of the quoted
snippets.

Within a proof, structures can be decomposed with the ``cases`` or ``rcases``
tactics. You can also use ``rintros`` or a pattern-matching
lambda.

EXAMPLES: -/
namespace point

-- QUOTE:
theorem add_comm (a b : point) : add a b = add b a :=
begin
  cases a with xa ya za,
  cases b with xb yb zb,
  rw [add, add],
  ext; dsimp,
  repeat { apply add_comm }
end

example (a b : point) : add a b = add b a :=
begin
  rcases a with ⟨xa, ya, za⟩,
  rcases b with ⟨xb, yb, zb⟩,
  simp [add, add_comm]
end

example : ∀ a b : point, add a b = add b a :=
begin
  rintros ⟨xa, ya, za⟩ ⟨xb, yb, zb⟩,
  simp [add, add_comm]
end

example : ∀ a b : point, add a b = add b a :=
λ ⟨xa, ya, za⟩ ⟨xb, yb, zb⟩, by simp [add, add_comm]
-- QUOTE.

/- TEXT:
In fact, even proving that the addition function does
the right thing on the ``x`` coordinate
requires decomposing the instances with ``cases``.
EXAMPLES: -/
-- QUOTE:
theorem add_x (a b : point) : (a.add b).x = a.x + b.x :=
by { cases a, cases b, refl }
-- QUOTE.

/- TEXT:
Starting a proof with ``cases`` is a common pattern when dealing with functions
that were defined by pattern matching.
An alternative is to define functions using projections,
in which case, the relevant equations often hold definitionally.
EXAMPLES: -/
-- QUOTE:
def add'' (a b : point) : point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

theorem add''_x (a b : point) : (a.add'' b).x = a.x + b.x := rfl
-- QUOTE.

/- TEXT:
Mathematical constructions often involve taking apart bundled information and
putting it together again in different ways.
It therefore makes sense that Lean and mathlib offer so many ways
of doing this efficiently.
As an exercise, try proving that ``point.add`` is associative.
Then define scalar multiplication for a point and show that it
distributes over addition.
You can use pattern matching or projections in the definition,
as you prefer.
BOTH: -/
-- QUOTE:
theorem add_assoc (a b c : point) : (a.add b).add c = a.add (b.add c) :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
by { cases a, cases b, cases c, simp [add, add_assoc] }
-- BOTH:

/- EXAMPLES:
def smul (r : ℝ) : point → point := sorry
SOLUTIONS: -/
def smul (r : ℝ) : point → point
| ⟨x, y, z⟩ := ⟨r * x, r * y, r * z⟩
-- BOTH:

theorem smul_distrib (r : ℝ) (a b : point) :
  (smul r a).add (smul r b) = smul r (a.add b) :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
by { cases a, cases b, simp [add, smul, mul_add] }
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
and we will explain how to do carry them out in the next section.
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
def swap_xy : standard_two_simplex → standard_two_simplex
| ⟨x, y, z, xnn, ynn, znn, hsum⟩ :=
  { x := y,
    y := x,
    z := z,
    x_nonneg := ynn,
    y_nonneg := xnn,
    z_nonneg := znn,
    sum_eq   := by rwa add_comm y x }
-- QUOTE.

/- TEXT:
More interestingly, we can compute the midpoint of two points on
the simplex. We need to add ``noncomputable theory`` in order to
use division on the real numbers.
BOTH: -/
-- QUOTE:
noncomputable theory

-- EXAMPLES:
def midpoint : standard_two_simplex → standard_two_simplex → standard_two_simplex
| ⟨x1, y1, z1, xnn1, ynn1, znn1, hsum1⟩ ⟨x2, y2, z2, xnn2, ynn2, znn2, hsum2⟩ :=
  { x        := (x1 + x2) / 2,
    y        := (y1 + y2) / 2,
    z        := (z1 + z2) / 2,
    x_nonneg := div_nonneg (add_nonneg xnn1 xnn2) (by norm_num),
    y_nonneg := div_nonneg (add_nonneg ynn1 ynn2) (by norm_num),
    z_nonneg := div_nonneg (add_nonneg znn1 znn2) (by norm_num),
    sum_eq   := by { field_simp, linarith } }
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
Onec again, you can use pattern matching or projections, as you prefer.
BOTH: -/
-- QUOTE:
def weighted_average (lambda : real)
    (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)  :
/- EXAMPLES:
  standard_two_simplex → standard_two_simplex → standard_two_simplex := sorry
SOLUTIONS: -/
  standard_two_simplex → standard_two_simplex → standard_two_simplex
| ⟨x1, y1, z1, xnn1, ynn1, znn1, hsum1⟩ ⟨x2, y2, z2, xnn2, ynn2, znn2, hsum2⟩ :=
  { x        := lambda * x1 + (1 - lambda) * x2,
    y        := lambda * y1 + (1 - lambda) * y2,
    z        := lambda * z1 + (1 - lambda) * z2,
    x_nonneg := add_nonneg (mul_nonneg lambda_nonneg xnn1)
                  (mul_nonneg (by linarith) xnn2),
    y_nonneg := add_nonneg (mul_nonneg lambda_nonneg ynn1)
                  (mul_nonneg (by linarith) ynn2),
    z_nonneg := add_nonneg (mul_nonneg lambda_nonneg znn1)
                  (mul_nonneg (by linarith) znn2),
    sum_eq   :=
      begin
        transitivity (x1 + y1 + z1) * lambda + (x2 + y2 + z2) * (1 - lambda),
        { ring },
        simp [hsum1, hsum2]
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

def midpoint (n : ℕ): standard_simplex n → standard_simplex n → standard_simplex n
| ⟨v1, nonneg1, sum1⟩ ⟨v2, nonneg2, sum2⟩ :=
  { v := λ i, (v1 i + v2 i) / 2,
    nonneg :=
      begin
        intro i,
        apply div_nonneg,
        { linarith [nonneg1 i, nonneg2 i] },
        norm_num
      end,
    sum_eq_one :=
    begin
      simp [div_eq_mul_inv, ←finset.sum_mul, finset.sum_add_distrib,
        sum1, sum2],
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
    (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)  :
  standard_simplex n → standard_simplex n → standard_simplex n
| ⟨v1, nonneg1, sum1⟩ ⟨v2, nonneg2, sum2⟩ :=
  { v        := λ i, lambda * v1 i + (1 - lambda) * v2 i,
    nonneg   := λ i, add_nonneg (mul_nonneg lambda_nonneg (nonneg1 i))
                  (mul_nonneg (by linarith) (nonneg2 i)),
    sum_eq_one :=
      begin
        transitivity lambda * (∑ i, v1 i) + (1 - lambda) * (∑ i, v2 i),
        { rw [finset.sum_add_distrib, finset.mul_sum, finset.mul_sum] },
        simp [sum1, sum2]
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
You can think of of the type ``preal`` in the next example as being
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

