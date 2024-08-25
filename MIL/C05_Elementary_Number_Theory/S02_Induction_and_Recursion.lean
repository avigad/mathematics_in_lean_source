import Mathlib.Data.Nat.GCD.Basic
import MIL.Common

/- TEXT:
.. _section_induction_and_recursion:

Induction and Recursion
-----------------------

The set of natural numbers :math:`\mathbb{N} = \{ 0, 1, 2, \ldots \}`
is not only fundamentally important in its own right,
but also a plays a central role in the construction of new mathematical objects.
Lean's foundation allows us to declare *inductive types*,
which are types generated inductively by a given list of
*constructors*.
In Lean, the natural numbers are declared as follows.
OMIT: -/
namespace hidden

-- QUOTE:
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-- QUOTE.

end hidden

/- TEXT:
You can find this in the library by writing ``#check Nat`` and
then using ``ctrl-click`` on the identifier ``Nat``.
The command specifies that ``Nat`` is the datatype generated
freely and inductively by the two constructors ``zero : Nat`` and
``succ : Nat → Nat``.
Of course, the library introduces notation ``ℕ`` and ``0`` for
``nat`` and ``zero`` respectively. (Numerals are translated to binary
representations, but we don't have to worry about the details of that now.)

What "freely" means for the working mathematician is that the type
``Nat`` has an element ``zero`` and an injective successor function
``succ`` whose image does not include ``zero``.
EXAMPLES: -/
-- QUOTE:
example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h
-- QUOTE.

/- TEXT:
What the word "inductively" means for the working mathematician is that
the natural numbers comes with a principle of proof by induction
and a principle of definition by recursion.
This section will show you how to use these.

Here is an example of a recursive definition of the factorial
function.
BOTH: -/
-- QUOTE:
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n
-- QUOTE.

/- TEXT:
The syntax takes some getting used to.
Notice that there is no ``:=`` on the first line.
The next two lines provide the base case and inductive step
for a recursive definition.
These equations hold definitionally, but they can also
be used manually by giving the name ``fac`` to ``simp`` or ``rw``.
EXAMPLES: -/
-- QUOTE:
example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]
-- QUOTE.

/- TEXT:
The factorial function is actually already defined in Mathlib as
``Nat.factorial``. Once again, you can jump to it by typing
``#check Nat.factorial`` and using ``ctrl-click.``
For illustrative purposes, we will continue using ``fac`` in the examples.
The annotation ``@[simp]`` before the definition
of ``Nat.factorial`` specifies that
the defining equation should be added to the database of identities
that the simplifier uses by default.

The principle of induction says that we can prove a general statement
about the natural numbers by proving that the statement holds of 0
and that whenever it holds of a natural number :math:`n`,
it also holds of :math:`n + 1`.
The line ``induction' n with n ih`` in the proof
below therefore results in two goals:
in the first we need to prove ``0 < fac 0``,
and in the second we have the added assumption ``ih : 0 < fac n``
and a required to prove ``0 < fac (n + 1)``.
The phrase ``with n ih`` serves to name the variable and
the assumption for the inductive hypothesis,
and you can choose whatever names you want for them.
EXAMPLES: -/
-- QUOTE:
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:
The ``induction'`` tactic is smart enough to include hypotheses
that depend on the induction variable as part of the
induction hypothesis.
Step through the next example to see what is going on.
EXAMPLES: -/
-- QUOTE:
theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right
-- QUOTE.

/- TEXT:
The following example provides a crude lower bound for the factorial
function.
It turns out to be easier to start with a proof by cases,
so that the remainder of the proof starts with the case
:math:`n = 1`.
See if you can complete the argument with a proof by induction using ``pow_succ``
or ``pow_succ'``.
BOTH: -/
-- QUOTE:
theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · simp [fac]
  simp at *
  rw [pow_succ', fac]
  apply Nat.mul_le_mul _ ih
  repeat' apply Nat.succ_le_succ
  apply zero_le

-- BOTH:
-- QUOTE.
/- TEXT:
Induction is often used to prove identities involving finite sums and
products.
Mathlib defines the expressions ``Finset.sum s f`` where
``s : Finset α`` is a finite set of elements of the type ``α`` and
``f`` is a function defined on ``α``.
The codomain of ``f`` can be any type that supports a commutative,
associative addition operation with a zero element.
If you import ``Algebra.BigOperators.Ring`` and issue the command
``open BigOperators``, you can use the more suggestive notation
``∑ x ∈ s, f x``. Of course, there is an analogous operation and
notation for finite products.

We will talk about the ``Finset`` type and the operations
it supports in the next section, and again in a later chapter.
For now, we will only make use
of ``Finset.range n``, which is the finite set of natural numbers
less than ``n``.
BOTH: -/
section

-- QUOTE:
variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

-- EXAMPLES:
#check Finset.sum s f
#check Finset.prod s f

-- BOTH:
open BigOperators
open Finset

-- EXAMPLES:
example : s.sum f = ∑ x ∈ s, f x :=
  rfl

example : s.prod f = ∏ x ∈ s, f x :=
  rfl

example : (range n).sum f = ∑ x ∈ range n, f x :=
  rfl

example : (range n).prod f = ∏ x ∈ range n, f x :=
  rfl
-- QUOTE.

/- TEXT:
The facts ``Finset.sum_range_zero`` and ``Finset.sum_range_succ``
provide a recursive description of summation up to :math:`n`,
and similarly for products.
EXAMPLES: -/
-- QUOTE:
example (f : ℕ → ℕ) : ∑ x ∈ range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x ∈ range n.succ, f x = ∑ x ∈ range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x ∈ range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x ∈ range n.succ, f x = (∏ x ∈ range n, f x) * f n :=
  Finset.prod_range_succ f n
-- QUOTE.

/- TEXT:
The first identity in each pair holds definitionally, which is to say,
you can replace the proofs by ``rfl``.

The following expresses the factorial function that we defined as a product.
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : fac n = ∏ i ∈ range n, (i + 1) := by
  induction' n with n ih
  · simp [fac, prod_range_zero]
  simp [fac, ih, prod_range_succ, mul_comm]
-- QUOTE.

/- TEXT:
The fact that we include ``mul_comm`` as a simplification rule deserves
comment.
It should seem dangerous to simplify with the identity ``x * y = y * x``,
which would ordinarily loop indefinitely.
Lean's simplifier is smart enough to recognize that, and applies the rule
only in the case where the resulting term has a smaller value in some
fixed but arbitrary ordering of the terms.
The following example shows that simplifying using the three rules
``mul_assoc``, ``mul_comm``, and ``mul_left_comm``
manages to identify products that are the same up to the
placement of parentheses and ordering of variables.
EXAMPLES: -/
-- QUOTE:
example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]
-- QUOTE.

/- TEXT:
Roughly, the rules work by pushing parentheses to the right
and then re-ordering the expressions on both sides until they
both follow the same canonical order. Simplifying with these
rules, and the corresponding rules for addition, is a handy trick.

Returning to summation identities, we suggest stepping through the following proof
that the sum of the natural numbers up to and including :math:`n` is
:math:`n (n + 1) / 2`.
The first step of the proof clears the denominator.
This is generally useful when formalizing identities,
because calculations with division generally have side conditions.
(It is similarly useful to avoid using subtraction on the natural numbers when possible.)
EXAMPLES: -/
-- QUOTE:
theorem sum_id (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring
-- QUOTE.

/- TEXT:
We encourage you to prove the analogous identity for sums of squares,
and other identities you can find on the web.
BOTH: -/
-- QUOTE:
theorem sum_sqr (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  symm;
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 6, ← ih]
  ring
-- QUOTE.

-- BOTH:
end

/- TEXT:
In Lean's core library, addition and multiplication are themselves defined
using recursive definitions,
and their fundamental properties are established using induction.
If you like thinking about foundational topics like that,
you might enjoy working through proofs
of the commutativity and associativity of multiplication and addition
and the distributivity of multiplication over addition.
You can do this on a copy of the natural numbers
following the outline below.
Notice that we can use the ``induction`` tactic with ``MyNat``;
Lean is smart enough to know to
use the relevant induction principle (which is, of course,
the same as that for ``Nat``).

We start you off with the commutativity of addition.
A good rule of thumb is that because addition and multiplication
are defined by recursion on the second argument,
it is generally advantageous to do proofs by induction on a variable
that occurs in that position.
It is a bit tricky to decide which variable to use in the proof
of associativity.

It can be confusing to write things without the usual notation
for zero, one, addition, and multiplication.
We will learn how to define such notation later.
Working in the namespace ``MyNat`` means that we can write
``zero`` and ``succ`` rather than ``MyNat.zero`` and ``MyNat.succ``,
and that these interpretations of the names take precedence over
others.
Outside the namespace, the full name of the ``add`` defined below,
for example, is ``MyNat.add``.

If you find that you *really* enjoy this sort of thing, try defining
truncated subtraction and exponentiation and proving some of their
properties as well.
Remember that truncated subtraction cuts off at zero.
To define that, it is useful to define a predecessor function, ``pred``,
that subtracts one from any nonzero number and fixes zero.
The function ``pred`` can be defined by a simple instance of recursion.
BOTH: -/
-- QUOTE:
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | x, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, ih]
  rfl

-- BOTH:
theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, mul, mul, ih, add_assoc]

-- BOTH:
theorem zero_mul (n : MyNat) : mul zero n = zero := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, ih]
  rfl

-- BOTH:
theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, mul, ih, add_assoc, add_assoc, add_comm n, succ_add]
  rfl

-- BOTH:
theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rw [zero_mul]
    rfl
  rw [mul, ih, succ_mul]

-- BOTH:
end MyNat
-- QUOTE.
