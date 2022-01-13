import data.real.basic

/- TEXT:
.. _disjunction:

Disjunction
-----------

.. index:: left, right, tactics ; left, tactics ; right

The canonical way to prove a disjunction ``A ∨ B`` is to prove
``A`` or to prove ``B``.
The ``left`` tactic chooses ``A``,
and the ``right`` tactic chooses ``B``.
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {x y : ℝ}

-- MAIN:
example (h : y > x^2) : y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

example (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }
-- QUOTE.

/- TEXT:
We cannot use an anonymous constructor to construct a proof
of an "or" because Lean would have to guess
which disjunct we are trying to prove.
When we write proof terms we can use
``or.inl`` and ``or.inr`` instead
to make the choice explicitly.
Here, ``inl`` is short for "introduction left" and
``inr`` is short for "introduction right."
TEXT. -/
-- QUOTE:
example (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h
-- QUOTE.

/- TEXT:
It may seem strange to prove a disjunction by proving one side
or the other.
In practice, which case holds usually depends a case distinction
that is implicit or explicit in the assumptions and the data.
The ``cases`` tactic allows us to make use of a hypothesis
of the form ``A ∨ B``.
In contrast to the use of ``cases`` with conjunction or an
existential quantifier,
here the ``cases`` tactic produces *two* goals.
Both have the same conclusion, but in the first case,
``A`` is assumed to be true,
and in the second case,
``B`` is assumed to be true.
In other words, as the name suggests,
the ``cases`` tactic carries out a proof by cases.
As usual, we can tell Lean what names to use for the hypotheses.
In the next example, we tell Lean
to use the name ``h`` on each branch.
TEXT. -/
-- QUOTE:
example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h h,
  { rw abs_of_nonneg h,
    intro h, left, exact h },
  rw abs_of_neg h,
  intro h, right, exact h
end
-- QUOTE.

/- TEXT:
The absolute value function is defined in such a way
that we can immediately prove that
``x ≥ 0`` implies ``abs x = x``
(this is the theorem ``abs_of_nonneg``)
and ``x < 0`` implies ``abs x = -x`` (this is ``abs_of_neg``).
The expression ``le_or_gt 0 x`` establishes ``0 ≤ x ∨ x < 0``,
allowing us to split on those two cases.
Try proving the triangle inequality using the two
first two theorems in the next snippet.
They are given the same names they have in mathlib.
TEXT. -/
-- BOTH:
-- QUOTE:
namespace my_abs

-- MAIN:
theorem le_abs_self : x ≤ abs x :=
sorry

theorem neg_le_abs_self : -x ≤ abs x :=
sorry

theorem abs_add : abs (x + y) ≤ abs x + abs y :=
sorry
-- QUOTE.

-- SOLUTIONS:
theorem le_abs_selfαα : x ≤ abs x :=
sorry

theorem neg_le_abs_selfαα : -x ≤ abs x :=
sorry

theorem abs_addαα : abs (x + y) ≤ abs x + abs y :=
sorry

/- TEXT:
In case you enjoyed these (pun intended) and
you want more practice with disjunction,
try these.
TEXT. -/
-- QUOTE:
theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
sorry

theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
sorry
-- QUOTE.

-- SOLUTIONS:
theorem lt_absαα : x < abs y ↔ x < y ∨ x < -y :=
sorry

theorem abs_ltαα : abs x < y ↔ - y < x ∧ x < y :=
sorry

-- BOTH:
end my_abs
end

/- TEXT:
You can also use ``rcases`` and ``rintros`` with disjunctions.
When these result in a genuine case split with multiple goals,
the patterns for each new goal are separated by a vertical bar.
TEXT. -/
-- QUOTE:
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, exact xlt },
  { contradiction },
  right, exact xgt
end
-- QUOTE.

/- TEXT:
You can still nest patterns and use the ``rfl`` keyword
to substitute equations:
TEXT. -/
-- QUOTE:
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right },
  rw [mul_comm, mul_assoc],
  apply dvd_mul_right
end
-- QUOTE.

/- TEXT:
See if you can prove the following with a single (long) line.
Use ``rcases`` to unpack the hypotheses and split on cases,
and use a semicolon and ``linarith`` to solve each branch.
TEXT. -/
-- QUOTE:
example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
sorry
-- QUOTE.

-- SOLUTIONS:
example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
sorry

/- TEXT:
On the real numbers, an equation ``x * y = 0``
tells us that ``x = 0`` or ``y = 0``.
In mathlib, this fact is known as ``eq_zero_or_eq_zero_of_mul_eq_zero``,
and it is another nice example of how a disjunction can arise.
See if you can use it to prove the following:
TEXT. -/
-- QUOTE:
example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

example {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry
-- QUOTE.

-- SOLUTIONS:
example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

example {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry

/- TEXT:
Remember that you can use the ``ring`` tactic to help
with calculations.

In an arbitrary ring :math:`R`, an element :math:`x` such
that :math:`x y = 0` for some nonzero :math:`y` is called
a *left zero divisor*,
an element :math:`x` such
that :math:`y x = 0` for some nonzero :math:`y` is called
a *right zero divisor*,
and an element that is either a left or right zero divisor
is called simply a *zero divisor*.
The theorem ``eq_zero_or_eq_zero_of_mul_eq_zero``
says that the real numbers have no nontrivial zero divisors.
A commutative ring with this property is called an *integral domain*.
Your proofs of the two theorems above should work equally well
in any integral domain:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {R : Type*} [comm_ring R] [is_domain R]
variables (x y : R)

-- MAIN:
example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

example (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry
-- QUOTE.

-- SOLUTIONS:
example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

example (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry

-- BOTH:
end

/- TEXT:
In fact, if you are careful, you can prove the first
theorem without using commutativity of multiplication.
In that case, it suffices to assume that ``R`` is
a ``domain`` instead of an ``integral_domain``.

.. index:: excluded middle

Sometimes in a proof we want to split on cases
depending on whether some statement is true or not.
For any proposition ``P``, we can use
``classical.em P : P ∨ ¬ P``.
The name ``em`` is short for "excluded middle."
TEXT. -/
-- QUOTE:
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end
-- QUOTE.

/- TEXT:
.. index:: by_cases, tactics ; by_cases

You can shorten ``classical.em`` to ``em``
by opening the ``classical`` namespace with the command
``open classical``.
Alternatively, you can use the ``by_cases`` tactic.
The ``open_locale classical`` command guarantees that Lean can
make implicit use of the law of the excluded middle.
TEXT. -/
-- BOTH:
section
-- QUOTE:
open_locale classical

-- MAIN:
example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction
end
-- QUOTE.

/- TEXT:
Notice that the ``by_cases`` tactic lets you
specify a label for the hypothesis that is
introduced in each branch,
in this case, ``h' : P`` in one and ``h' : ¬ P``
in the other.
If you leave out the label,
Lean uses ``h`` by default.
Try proving the following equivalence,
using ``by_cases`` to establish one direction.
TEXT. -/
-- QUOTE:
example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
sorry
-- QUOTE.

-- SOLUTIONS:
example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
sorry

-- BOTH:
end