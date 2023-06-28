-- BOTH:
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

variable (a b c d e : ℝ)
open Real

/- TEXT:
.. _using_theorems_and_lemmas:

Using Theorems and Lemmas
-------------------------

.. index:: inequalities

Rewriting is great for proving equations,
but what about other sorts of theorems?
For example, how can we prove an inequality,
like the fact that :math:`a + e^b \le a + e^c` holds whenever :math:`b \le c`?
We have already seen that theorems can be applied to arguments and hypotheses,
and that the ``apply`` and ``exact`` tactics can be used to solve goals.
In this section, we will make good use of these tools.

Consider the library theorems ``le_refl`` and ``le_trans``:
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
-- QUOTE.

/- TEXT:
As we explain in more detail in  :numref:`implication_and_the_universal_quantifier`,
the implicit parentheses in the statement of ``le_trans``
associate to the right, so it should be interpreted as ``a ≤ b → (b ≤ c → a ≤ c)``.
The library designers have set the arguments ``a``, ``b`` and ``c`` to ``le_trans`` implicit,
so that Lean will *not* let you provide them explicitly (unless you
really insist, as we will discuss later).
Rather, it expects to infer them from the context in which they are used.
For example, when hypotheses ``h : a ≤ b`` and  ``h' : b ≤ c``
are in the context,
all the following work:
TEXT. -/
section
-- QUOTE:
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
-- QUOTE.

end

/- TEXT:
.. index:: apply, tactics ; apply, exact, tactics ; exact

The ``apply`` tactic takes a proof of a general statement or implication,
tries to match the conclusion with the current goal,
and leaves the hypotheses, if any, as new goals.
If the given proof matches the goal exactly
(modulo *definitional* equality),
you can use the ``exact`` tactic instead of ``apply``.
So, all of these work:
TEXT. -/
-- QUOTE:
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x
-- QUOTE.

/- TEXT:
In the first example, applying ``le_trans``
creates two goals,
and we use the dots to indicate where the proof of each begins.
The dots are optional, but they serve to *focus* the goal:
within the block introduced by the dot, only one goal is visible,
and it must be completed before the end of the block.
Here we end the first block by starting a new one with another dot.
We could just as well have decreased the indentation.
In the fourth example and in the last example,
we avoid going into tactic mode entirely:
``le_trans h₀ h₁`` and ``le_refl x`` are the proof terms we need.

Here are a few more library theorems:
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
-- QUOTE.

/- TEXT:
Use them together with ``apply`` and ``exact`` to prove the following:
TEXT. -/
-- Try this.
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  exact lt_of_le_of_lt h₂ h₃

/- TEXT:
.. index:: linarith, tactics ; linarith

In fact, Lean has a tactic that does this sort of thing automatically:
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
-- QUOTE.

/- TEXT:
The ``linarith`` tactic is designed to handle *linear arithmetic*.
TEXT. -/
section

-- QUOTE:
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
-- QUOTE.

end

/- TEXT:
In addition to equations and inequalities in the context,
``linarith`` will use additional inequalities that you pass as arguments.
In the next example, ``exp_le_exp.mpr h'`` is a proof of
``exp b ≤ exp c``, as we will explain in a moment.
Notice that, in Lean, we write ``f x`` to denote the application
of a function ``f`` to the argument ``x``,
exactly the same way we write ``h x`` to denote the result of
applying a fact or theorem ``h`` to the argument ``x``.
Parentheses are only needed for compound arguments,
as in ``f (x + y)``. Without the parentheses, ``f x + y``
would be parsed as ``(f x) + y``.
TEXT. -/
-- QUOTE:
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']
-- QUOTE.

/- TEXT:
.. index:: exponential, logarithm

Here are some more theorems in the library that can be used to establish
inequalities on the real numbers.
TEXT. -/
-- QUOTE:
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check @add_le_add_left
-- QUOTE.

/- TEXT:
Some of the theorems, ``exp_le_exp``, ``exp_lt_exp``, and ``log_le_log``
use a *bi-implication*, which represents the
phrase "if and only if."
(You can type it in VS Code with ``\lr`` of ``\iff``).
We will discuss this connective in greater detail in the next chapter.
Such a theorem can be used with ``rw`` to rewrite a goal to
an equivalent one:
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h
-- QUOTE.

/- TEXT:
In this section, however, we will use the fact that if ``h : A ↔ B``
is such an equivalence,
then ``h.mp`` establishes the forward direction, ``A → B``,
and ``h.mpr`` establishes the reverse direction, ``B → A``.
Here, ``mp`` stands for "modus ponens" and
``mpr`` stands for "modus ponens reverse."
You can also use ``h.1`` and ``h.2`` for ``h.mp`` and ``h.mpr``,
respectively, if you prefer.
Thus the following proof works:
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl
-- QUOTE.

/- TEXT:
The first line, ``apply add_lt_add_of_lt_of_le``,
creates two goals,
and once again we use a dot to separate the
proof of the first from the proof of the second.

.. index:: norm_num, tactics ; norm_num

Try the following examples on your own.
The example in the middle shows you that the ``norm_num``
tactic can be used to solve concrete numeric goals.
TEXT. -/
-- QUOTE:
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry
  have h₁ : 0 < 1 + exp b := by sorry
  apply (log_le_log h₀ h₁).mpr
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  rw [exp_le_exp]
  apply add_le_add_left h₀

-- an alternative using `linarith`.
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have : exp (a + d) ≤ exp (a + e) := by
    rw [exp_le_exp]
    linarith
  linarith [this]

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by linarith [exp_pos a]
  have h₁ : 0 < 1 + exp b := by linarith [exp_pos b]
  apply (log_le_log h₀ h₁).mpr
  apply add_le_add_left (exp_le_exp.mpr h)

-- SOLUTION.
/- TEXT:
From these examples, it should be clear that being able to
find the library theorems you need constitutes an important
part of formalization.
There are a number of strategies you can use:

* You can browse mathlib in its
  `GitHub repository <https://github.com/leanprover-community/mathlib4>`_.

* You can use the API documentation on the mathlib
  `web pages <https://leanprover-community.github.io/mathlib4_docs/>`_.

* You can rely on mathlib naming conventions and Ctrl-space completion in
  the editor to guess a theorem name (or Cmd-space on a Mac keyboard).
  In Lean, a theorem named ``A_of_B_of_C`` establishes
  something of the form ``A`` from hypotheses of the form ``B`` and ``C``,
  where ``A``, ``B``, and ``C``
  approximate the way we might read the goals out loud.
  So a theorem establishing something like ``x + y ≤ ...`` will probably
  start with ``add_le``.
  Typing ``add_le`` and hitting Ctrl-space will give you some helpful choices.
  Note that hitting Ctrl-space twice displays more information about the available
  completions.

* If you right-click on an existing theorem name in VS Code,
  the editor will show a menu with the option to
  jump to the file where the theorem is defined,
  and you can find similar theorems nearby.

* You can use the ``apply?`` tactic,
  which tries to find the relevant theorem in the library.
TEXT. -/
-- QUOTE:
example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a
-- QUOTE.

/- TEXT:
To try out ``apply?`` in this example,
delete the ``exact`` command and uncomment the previous line.
Using these tricks,
see if you can find what you need to do the
next example:
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply sub_le_sub_left
  exact exp_le_exp.mpr h

-- alternatively:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  linarith [exp_le_exp.mpr h]

/- TEXT:
Using the same tricks, confirm that ``linarith`` instead of ``apply?``
can also finish the job.

Here is another example of an inequality:
TEXT. -/
-- QUOTE:
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) :=
      add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring

-- QUOTE.

/- TEXT:
Mathlib tends to put spaces around binary operations like ``*`` and ``^``,
but in this example, the more compressed format increases readability.
There are a number of things worth noticing.
First, an expression ``s ≥ t`` is definitionally equivalent to ``t ≤ s``.
In principle, this means one should be able to use them interchangeably.
But some of Lean's automation does not recognize the equivalence,
so mathlib tends to favor ``≤`` over ``≥``.
Second, we have used the ``ring`` tactic extensively.
It is a real timesaver!
Finally, notice that in the second line of the
second ``calc`` proof,
instead of writing ``by exact add_le_add (le_refl _) h``,
we can simply write the proof term ``add_le_add (le_refl _) h``.

In fact, the only cleverness in the proof above is figuring
out the hypothesis ``h``.
Once we have it, the second calculation involves only
linear arithmetic, and ``linarith`` can handle it:
TEXT. -/
-- QUOTE:
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
-- QUOTE.

/- TEXT:
How nice! We challenge you to use these ideas to prove the
following theorem. You can use the theorem ``abs_le'.mpr``.
TEXT. -/
-- QUOTE:
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  sorry

#check abs_le'.mpr
-- QUOTE.

-- SOLUTIONS:
theorem fact1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

theorem fact2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
  calc
    a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  · rw [le_div_iff h]
    apply fact1
  rw [le_div_iff h]
  apply fact2

/- TEXT:
If you managed to solve this, congratulations!
You are well on your way to becoming a master formalizer.
TEXT. -/
