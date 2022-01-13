-- BOTH:
import data.real.basic

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
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 5 / 2,
  norm_num
end
-- QUOTE.

/- TEXT:
.. index:: anonyomous constructor

Alternatively, we can use Lean's *anonyomous constructor* notation
to construct the proof.
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
    by norm_num,
  exact ⟨5 / 2, h⟩
end
-- QUOTE.

/- TEXT:
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
For example, remember the predicates ``fn_ub f a`` and ``fn_lb f a``
from the last section,
which say that ``a`` is an upper bound or lower bound on ``f``,
respectively.
We can use the existential quantifier to say that "``f`` is bounded"
without specifying the bound:
TEXT. -/
-- BOTH:
-- QUOTE:
def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a
-- QUOTE.

/- TEXT:
We can use the theorem ``fn_ub_add`` from the last section
to prove that if ``f`` and ``g`` have upper bounds,
then so does ``λ x, f x + g x``.
TEXT. -/

-- BOTH:
theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

section
-- QUOTE:
variables {f g : ℝ → ℝ}

-- MAIN:
example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin
  cases ubf with a ubfa,
  cases ubg with b ubfb,
  use a + b,
  apply fn_ub_add ubfa ubfb
end
-- QUOTE.

/- TEXT:
.. index:: cases, tactics ; cases

The ``cases`` tactic unpacks the information
in the existential quantifier.
Given the hypothesis ``ubf`` that there is an upper bound
for ``f``,
``cases`` adds a new variable for an upper
bound to the context,
together with the hypothesis that it has the given property.
The ``with`` clause allows us to specify the names
we want Lean to use.
The goal is left unchanged;
what *has* changed is that we can now use
the new object and the new hypothesis
to prove the goal.
This is a common pattern in mathematics:
we unpack objects whose existence is asserted or implied
by some hypothesis, and then use it to establish the existence
of something else.

Try using this pattern to establish the following.
You might find it useful to turn some of the examples
from the last section into named theorems,
as we did with ``fn_ub_add``,
or you can insert the arguments directly
into the proofs.
TEXT. -/
-- QUOTE:
example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) :=
sorry

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
sorry
-- QUOTE.

-- SOLUTIONS:
example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) :=
begin
  cases lbf with a lbfa,
  cases lbg with b lbgb,
  use a + b,
  intro x,
  exact add_le_add (lbfa x) (lbgb x)
end

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
begin
  cases ubf with a lbfa,
  use c * a,
  intro x,
  exact mul_le_mul_of_nonneg_left (lbfa x) h
end

/- TEXT:
.. index:: rintros, tactics ; rintros, rcases, tactics ; rcases

The task of unpacking information in a hypothesis is
so important that Lean and mathlib provide a number of
ways to do it.
A cousin of the ``cases`` tactic, ``rcases``, is more
flexible in that it allows us to unpack nested data.
(The "r" stands for "recursive.")
In the ``with`` clause for unpacking an existential quantifier,
we name the object and the hypothesis by presenting
them as a pattern ``⟨a, h⟩`` that ``rcases`` then tries to match.
The ``rintro`` tactic (which can also be written ``rintros``)
is a combination of ``intros`` and ``rcases``.
These examples illustrate their use:
TEXT. -/
-- QUOTE:
example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin
  rcases ubf with ⟨a, ubfa⟩,
  rcases ubg with ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩
end

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
begin
  rintros ⟨a, ubfa⟩ ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩
end
-- QUOTE.

/- TEXT:
In fact, Lean also supports a pattern-matching lambda
in expressions and proof terms:
TEXT. -/
-- QUOTE:
example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
λ ⟨a, ubfa⟩ ⟨b, ubfb⟩, ⟨a + b, fn_ub_add ubfa ubfb⟩
-- QUOTE.

-- BOTH:
end

/- TEXT:
These are power-user moves, and there is no harm
in favoring the use of ``cases`` until you are more comfortable
with the existential quantifier.
But we will come to learn that all of these tools,
including ``cases``, use, and the anonymous constructors,
are like Swiss army knives when it comes to theorem proving.
They can be used for a wide range of purposes,
not just for unpacking exists statements.

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
variables {α : Type*} [comm_ring α]

def sum_of_squares (x : α) := ∃ a b, x = a^2 + b^2

theorem sum_of_squares_mul {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq⟩,
  rcases sosy with ⟨c, d, yeq⟩,
  rw [xeq, yeq],
  use [a*c - b*d, a*d + b*c],
  ring
end
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
In the chapters to come,
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
theorem sum_of_squares_mul' {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, rfl⟩,
  rcases sosy with ⟨c, d, rfl⟩,
  use [a*c - b*d, a*d + b*c],
  ring
end
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
variables {a b c : ℕ}

-- MAIN:
-- QUOTE:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c :=
begin
  cases divab with d beq,
  cases divbc with e ceq,
  rw [ceq, beq],
  use (d * e), ring
end
-- QUOTE.

/- TEXT:
And once again, this provides a nice setting for using
``rcases`` with ``rfl``.
Try it out in the proof above.
It feels pretty good!

Then try proving the following:
TEXT. -/
-- QUOTE:
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
sorry
-- QUOTE.

-- SOLUTIONS:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c :=
begin
  rcases divab with ⟨d, rfl⟩,
  rcases divbc with ⟨e, rfl⟩,
  use (d * e), ring
end

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, rfl⟩,
  rcases divac with ⟨e, rfl⟩,
  use (d + e), ring
end

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
open function

-- MAIN:
-- QUOTE:
example {c : ℝ} : surjective (λ x, x + c) :=
begin
  intro x,
  use x - c,
  dsimp, ring
end
-- QUOTE.

/- TEXT:
Try this example yourself:
TEXT. -/
-- QUOTE:
example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro x,
  use x / c,
  dsimp, rw [mul_div_cancel' _ h]
end

example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro x,
  use x / c,
  field_simp [h], ring
end

/- TEXT:
index:: field_simp, tactic ; field_simp

At this point, it is worth mentioning that there is a tactic, `field_simp`,
that will often clear denominators in a useful way.
It can be used in conjunction with the ``ring`` tactic.
TEXT. -/
-- QUOTE:
example (x y : ℝ) (h : x - y ≠ 0) : (x^2 - y^2) / (x - y) = x + y :=
by { field_simp [h], ring }
-- QUOTE.

/- TEXT:
You can use the theorem ``div_mul_cancel``.
The next example uses a surjectivity hypothesis
by applying it to a suitable value.
Note that you can use ``cases`` with any expression,
not just a hypothesis.
TEXT. -/
-- QUOTE:
example {f : ℝ → ℝ} (h : surjective f) : ∃ x, (f x)^2 = 4 :=
begin
  cases h 2 with x hx,
  use x,
  rw hx,
  norm_num
end
-- QUOTE.

-- BOTH:
end

/- TEXT:
See if you can use these methods to show that
the composition of surjective functions is surjective.
TEXT. -/
-- BOTH:
section
open function
-- QUOTE:
variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

-- MAIN
example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
sorry
-- QUOTE.

-- SOLUTIONS:
example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
begin
  intro z,
  rcases surjg z with ⟨y, rfl⟩,
  rcases surjf y with ⟨x, rfl⟩,
  use [x, rfl]
end

-- BOTH:
end
