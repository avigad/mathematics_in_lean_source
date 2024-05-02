-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace C03S02

/- TEXT:
.. _the_existential_quantifier:

The Existential Quantifier
--------------------------

The existential quantifier, which can be entered as ``\ex`` in VS Code,
is used to represent the phrase "there exists."
The formal expression ``∃ x : ℝ, 2 < x ∧ x < 3`` in Lean says
that there is a real number between 2 and 3.
(We will discuss the conjunction symbol, ``∧``, in :numref:`conjunction_and_biimplication`.)
The canonical way to prove such a statement is to exhibit a real number
and show that it has the stated property.
The number 2.5, which we can enter as ``5 / 2``
or ``(5 : ℝ) / 2`` when Lean cannot infer from context that we have
the real numbers in mind, has the required property,
and the ``norm_num`` tactic can prove that it meets the description.

.. index:: use, tactics ; use

There are a few ways we can put the information together.
Given a goal that begins with an existential quantifier,
the ``use`` tactic is used to provide the object,
leaving the goal of proving the property.
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num
-- QUOTE.

/- TEXT:
You can give the ``use`` tactic proofs as well as data:
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2
-- QUOTE.

/- TEXT:
In fact, the ``use`` tactic automatically tries to use available assumptions as well.
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2
-- QUOTE.

/- TEXT:
.. index:: anonymous constructor

Alternatively, we can use Lean's *anonymous constructor* notation
to construct a proof of an existential quantifier.
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩
-- QUOTE.

/- TEXT:
Notice that there is no ``by``; here we are giving an explicit proof term.
The left and right angle brackets,
which can be entered as ``\<`` and ``\>`` respectively,
tell Lean to put together the given data using
whatever construction is appropriate
for the current goal.
We can use the notation without going first into tactic mode:
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩
-- QUOTE.

/- TEXT:
So now we know how to *prove* an exists statement.
But how do we *use* one?
If we know that there exists an object with a certain property,
we should be able to give a name to an arbitrary one
and reason about it.
For example, remember the predicates ``FnUb f a`` and ``FnLb f a``
from the last section,
which say that ``a`` is an upper bound or lower bound on ``f``,
respectively.
We can use the existential quantifier to say that "``f`` is bounded"
without specifying the bound:
TEXT. -/
-- BOTH:
-- QUOTE:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a
-- QUOTE.

/- TEXT:
We can use the theorem ``FnUb_add`` from the last section
to prove that if ``f`` and ``g`` have upper bounds,
then so does ``fun x ↦ f x + g x``.
TEXT. -/
-- BOTH:
theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

section

-- QUOTE:
variable {f g : ℝ → ℝ}

-- EXAMPLES:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb
-- QUOTE.

/- TEXT:
.. index:: cases, tactics ; cases

The ``rcases`` tactic unpacks the information
in the existential quantifier.
The annotations like ``⟨a, ubfa⟩``, written with the
same angle brackets as the anonymous constructors,
are known as *patterns*, and they describe the information
that we expect to find when we unpack the main argument.
Given the hypothesis ``ubf`` that there is an upper bound
for ``f``,
``rcases ubf with ⟨a, ubfa⟩`` adds a new variable ``a``
for an upper bound to the context,
together with the hypothesis ``ubfa`` that it has the given property.
The goal is left unchanged;
what *has* changed is that we can now use
the new object and the new hypothesis
to prove the goal.
This is a common method of reasoning in mathematics:
we unpack objects whose existence is asserted or implied
by some hypothesis, and then use it to establish the existence
of something else.

Try using this method to establish the following.
You might find it useful to turn some of the examples
from the last section into named theorems,
as we did with ``fn_ub_add``,
or you can insert the arguments directly
into the proofs.
TEXT. -/
-- QUOTE:
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  sorry

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  intro x
  exact add_le_add (lbfa x) (lbgb x)

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa⟩
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (ubfa x) h

/- TEXT:
.. index:: rintro, tactics ; rintro, rcases, tactics ; rcases

The "r" in ``rcases`` stands for "recursive," because it allows
us to use arbitrarily complex patterns to unpack nested data.
The ``rintro`` tactic
is a combination of ``intro`` and ``rcases``:
TEXT. -/
-- QUOTE:
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- TEXT:
In fact, Lean also supports a pattern-matching fun
in expressions and proof terms:
TEXT. -/
-- QUOTE:
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

-- BOTH:
end

/- TEXT:
The task of unpacking information in a hypothesis is
so important that Lean and Mathlib provide a number of
ways to do it. For example, the ``obtain`` tactic provides suggestive syntax:
TEXT. -/
-- QUOTE:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- TEXT:
Think of the first ``obtain`` instruction as matching the "contents" of ``ubf``
with the given pattern and assigning the components to the named variables.
``rcases`` and ``obtain`` are said to ``destruct`` their arguments, though
there is a small difference in that ``rcases`` clears ``ubf`` from the context
when it is done, whereas it is still present after ``obtain``.

Lean also supports syntax that is similar to that used in other functional programming
languages:
TEXT. -/
-- QUOTE:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- TEXT:
In the first example, if you put your cursor after ``cases ubf``,
you will see that the tactic produces a single goal, which Lean has tagged
``intro``. (The particular name chosen comes from the internal name for
the axiomatic primitive that builds a proof of an existential statement.)
The ``case`` tactic then names the components. The second example is similar,
except using ``next`` instead of ``case`` means that you can avoid mentioning
``intro``. The word ``match`` in the last two examples highlights that
what we are doing here is what computer scientists call "pattern matching."
Notice that the third proof begins by ``by``, after which the tactic version
of ``match`` expects a tactic proof on the right side of the arrow.
The last example is a proof term: there are no tactics in sight.

For the rest of this book, we will stick to ``rcases``, ``rintros``, and ``obtain``,
as the preferred ways of using an existential quantifier.
But it can't hurt to see the alternative syntax, especially if there is
a chance you will find yourself in the company of computer scientists.

To illustrate one way that ``rcases`` can be used,
we prove an old mathematical chestnut:
if two integers ``x`` and ``y`` can each be written as
a sum of two squares,
then so can their product, ``x * y``.
In fact, the statement is true for any commutative
ring, not just the integers.
In the next example, ``rcases`` unpacks two existential
quantifiers at once.
We then provide the magic values needed to express ``x * y``
as a sum of squares as a list to the ``use`` statement,
and we use ``ring`` to verify that they work.
TEXT. -/
section

-- QUOTE:
variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring
-- QUOTE.

/- TEXT:
This proof doesn't provide much insight,
but here is one way to motivate it.
A *Gaussian integer* is a number of the form :math:`a + bi`
where :math:`a` and :math:`b` are integers and :math:`i = \sqrt{-1}`.
The *norm* of the Gaussian integer :math:`a + bi` is, by definition,
:math:`a^2 + b^2`.
So the norm of a Gaussian integer is a sum of squares,
and any sum of squares can be expressed in this way.
The theorem above reflects the fact that norm of a product of
Gaussian integers is the product of their norms:
if :math:`x` is the norm of :math:`a + bi` and
:math:`y` in the norm of :math:`c + di`,
then :math:`xy` is the norm of :math:`(a + bi) (c + di)`.
Our cryptic proof illustrates the fact that
the proof that is easiest to formalize isn't always
the most perspicuous one.
In :numref:`section_building_the_gaussian_integers`,
we will provide you with the means to define the Gaussian
integers and use them to provide an alternative proof.

The pattern of unpacking an equation inside an existential quantifier
and then using it to rewrite an expression in the goal
comes up often,
so much so that the ``rcases`` tactic provides
an abbreviation:
if you use the keyword ``rfl`` in place of a new identifier,
``rcases`` does the rewriting automatically (this trick doesn't work
with pattern-matching lambdas).
TEXT. -/
-- QUOTE:
theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring
-- QUOTE.

end

/- TEXT:
As with the universal quantifier,
you can find existential quantifiers hidden all over
if you know how to spot them.
For example, divisibility is implicitly an "exists" statement.
TEXT. -/
-- BOTH:
section
variable {a b c : ℕ}

-- EXAMPLES:
-- QUOTE:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring
-- QUOTE.

/- TEXT:
And once again, this provides a nice setting for using
``rcases`` with ``rfl``.
Try it out in the proof above.
It feels pretty good!

Then try proving the following:
TEXT. -/
-- QUOTE:
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩
  rcases divbc with ⟨e, rfl⟩
  use d * e; ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩
  rcases divac with ⟨e, rfl⟩
  use d + e; ring

-- BOTH:
end

/- TEXT:
.. index:: surjective function

For another important example, a function :math:`f : \alpha \to \beta`
is said to be *surjective* if for every :math:`y` in the
codomain, :math:`\beta`,
there is an :math:`x` in the domain, :math:`\alpha`,
such that :math:`f(x) = y`.
Notice that this statement includes both a universal
and an existential quantifier, which explains
why the next example makes use of both ``intro`` and ``use``.
TEXT. -/
-- BOTH:
section

open Function

-- EXAMPLES:
-- QUOTE:
example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring
-- QUOTE.

/- TEXT:
Try this example yourself using the theorem ``mul_div_cancel₀``.:
TEXT. -/
-- QUOTE:
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  dsimp; rw [mul_div_cancel₀ _ h]

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  field_simp

/- TEXT:
.. index:: field_simp, tactic ; field_simp

At this point, it is worth mentioning that there is a tactic, ``field_simp``,
that will often clear denominators in a useful way.
It can be used in conjunction with the ``ring`` tactic.
TEXT. -/
-- QUOTE:
example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring
-- QUOTE.

/- TEXT:
The next example uses a surjectivity hypothesis
by applying it to a suitable value.
Note that you can use ``rcases`` with any expression,
not just a hypothesis.
TEXT. -/
-- QUOTE:
example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num
-- QUOTE.

-- BOTH:
end

/- TEXT:
See if you can use these methods to show that
the composition of surjective functions is surjective.
TEXT. -/
-- BOTH:
section
open Function
-- QUOTE:
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- EXAMPLES:
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro z
  rcases surjg z with ⟨y, rfl⟩
  rcases surjf y with ⟨x, rfl⟩
  use x

-- BOTH:
end
