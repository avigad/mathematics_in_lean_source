/- TEXT:
Calculating
-----------

We generally learn to carry out mathematical calculations
without thinking of them as proofs.
But when we justify each step in a calculation,
as Lean requires us to do,
the net result is a proof that the left-hand side of the calculation
is equal to the right-hand side.

.. index:: rewrite, rw, tactics ; rw and rewrite

In Lean, stating a theorem is tantamount to stating a goal,
namely, the goal of proving the theorem.
Lean provides the rewriting tactic ``rw``,
to replace the left-hand side of an identity by the right-hand side
in the goal. If ``a``, ``b``, and ``c`` are real numbers,
``mul_assoc a b c``  is the identity ``a * b * c = a * (b * c)``
and ``mul_comm a b`` is the identity ``a * b = b * a``.
Lean provides automation that generally eliminates the need
to refer the facts like these explicitly,
but they are useful for the purposes of illustration.
In Lean, multiplication associates to the left,
so the left-hand side of ``mul_assoc`` could also be written ``(a * b) * c``.
However, it is generally good style to be mindful of Lean's
notational conventions and leave out parentheses when Lean does as well.

Let's try out ``rw``.

.. index:: real numbers
TEXT. -/
-- An example.
-- QUOTE:
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
-- QUOTE.

/- TEXT:
The ``import`` line at the beginning of the example
imports the theory of the real numbers from ``mathlib``.
For the sake of brevity,
we generally suppress information like this when it
is repeated from example to example.

You are welcome to make changes to see what happens.
You can type the ``ℝ`` character as ``\R`` or ``\real``
in VS Code.
The symbol doesn't appear until you hit space or the tab key.
If you hover over a symbol when reading a Lean file,
VS Code will show you the syntax that can be used to enter it.
If you are curious to see all available abbreviations, you can hit Ctrl-Shift-p
and then type abbreviations to get access to the ``Lean 4: Show all abbreviations`` command.
If your keyboard does not have an easily accessible backslash,
you can change the leading character by changing the
``lean4.input.leader`` setting.

.. index:: proof state, local context, goal

When a cursor is in the middle of a tactic proof,
Lean reports on the current *proof state* in the
*Lean infoview* window.
As you move your cursor past each step of the proof,
you can see the state change.
A typical proof state in Lean might look as follows:

.. code-block::

    1 goal
    x y : ℕ,
    h₁ : Prime x,
    h₂ : ¬Even x,
    h₃ : y > x
    ⊢ y ≥ 4

The lines before the one that begins with ``⊢`` denote the *context*:
they are the objects and assumptions currently at play.
In this example, these include two objects, ``x`` and ``y``,
each a natural number.
They also include three assumptions,
labelled ``h₁``, ``h₂``, and ``h₃``.
In Lean, everything in a context is labelled with an identifier.
You can type these subscripted labels as ``h\1``, ``h\2``, and ``h\3``,
but any legal identifiers would do:
you can use ``h1``, ``h2``, ``h3`` instead,
or ``foo``, ``bar``, and ``baz``.
The last line represents the *goal*,
that is, the fact to be proved.
Sometimes people use *target* for the fact to be proved,
and *goal* for the combination of the context and the target.
In practice, the intended meaning is usually clear.

Try proving these identities,
in each case replacing ``sorry`` by a tactic proof.
With the ``rw`` tactic, you can use a left arrow (``\l``)
to reverse an identity.
For example, ``rw [← mul_assoc a b c]``
replaces ``a * (b * c)`` by ``a * b * c`` in the current goal. Note that
the left-pointing arrow refers to going from right to left in the identity provided
by ``mul_assoc``, it has nothing to do with the left or right side of the goal.
TEXT. -/
-- Try these.
-- QUOTE:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

/- TEXT:
You can also use identities like ``mul_assoc`` and ``mul_comm`` without arguments.
In this case, the rewrite tactic tries to match the left-hand side with
an expression in the goal,
using the first pattern it finds.
TEXT. -/
-- An example.
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
-- QUOTE.

/- TEXT:
You can also provide *partial* information.
For example, ``mul_comm a`` matches any pattern of the form
``a * ?`` and rewrites it to ``? * a``.
Try doing the first of these examples without
providing any arguments at all,
and the second with only one argument.
TEXT. -/
/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
-- QUOTE:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

/- TEXT:
You an also use ``rw`` with facts from the local context.
TEXT. -/
-- Using facts from the local context.
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
-- QUOTE.

/- TEXT:
Try these, using the theorem ``sub_self`` for the second one:
TEXT. -/

-- QUOTE:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

/- TEXT:
Multiple rewrite commands can be carried out with a single command,
by listing the relevant identities separated by commas inside the square brackets.
TEXT. -/
-- Examples.
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

/- TEXT:
You still see the incremental progress by placing the cursor after
a comma in any list of rewrites.

Another trick is that we can declare variables once and for all outside
an example or theorem. Lean then includes them automatically.
TEXT. -/
section

-- QUOTE:
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

end

/- TEXT:
Inspection of the tactic state at the beginning of the above proof
reveals that Lean indeed included all variables.
We can delimit the scope of the declaration by putting it
in a ``section ... end`` block.
Finally, recall from the introduction that Lean provides us with a
command to determine the type of an expression:
TEXT. -/
-- QUOTE:
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
-- QUOTE.

/- TEXT:
The ``#check`` command works for both objects and facts.
In response to the command ``#check a``, Lean reports that ``a`` has type ``ℝ``.
In response to the command ``#check mul_comm a b``,
Lean reports that ``mul_comm a b`` is a proof of the fact ``a * b = b * a``.
The command ``#check (a : ℝ)`` states our expectation that the
type of ``a`` is ``ℝ``,
and Lean will raise an error if that is not the case.
We will explain the output of the last three ``#check`` commands later,
but in the meanwhile, you can take a look at them,
and experiment with some ``#check`` commands of your own.

Let's try some more examples. The theorem ``two_mul a`` says
that ``2 * a = a + a``. The theorems ``add_mul`` and ``mul_add``
express the distributivity of multiplication over addition,
and the theorem ``add_assoc`` expresses the associativity of addition.
Use the ``#check`` command to see the precise statements.

.. index:: calc, tactics ; calc
TEXT. -/
section
variable (a b : ℝ)

-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- TEXT:
Whereas it is possible to figure out what it going on in this proof
by stepping through it in the editor,
it is hard to read on its own.
Lean provides a more structured way of writing proofs like this
using the ``calc`` keyword.
TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- TEXT:
Notice that the proof does *not* begin with ``by``:
an expression that begins with ``calc`` is a *proof term*.
A ``calc`` expression can also be used inside a tactic proof,
but Lean interprets it as the instruction to use the resulting
proof term to solve the goal.
The ``calc`` syntax is finicky: the underscores and justification
have to be in the format indicated above.
Lean uses indentation to determine things like where a block
of tactics or a ``calc`` block begins and ends;
try changing the indentation in the proof above to see what happens.

One way to write a ``calc`` proof is to outline it first
using the ``sorry`` tactic for justification,
make sure Lean accepts the expression modulo these,
and then justify the individual steps using tactics.
TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry
-- QUOTE.

end

/- TEXT:
Try proving the following identity using both a pure ``rw`` proof
and a more structured ``calc`` proof:
TEXT. -/
-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

-- QUOTE:
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
-- QUOTE.

/- TEXT:
The following exercise is a little more challenging.
You can use the theorems listed underneath.
TEXT. -/
-- QUOTE:
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
-- QUOTE.

end

/- TEXT:
.. index:: rw, tactics ; rw and rewrite

We can also perform rewriting in an assumption in the context.
For example, ``rw [mul_comm a b] at hyp`` replaces ``a * b`` by ``b * a``
in the assumption ``hyp``.
TEXT. -/
-- Examples.

section
variable (a b c d : ℝ)

-- QUOTE:
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
-- QUOTE.

/- TEXT:
.. index:: exact, tactics ; exact

In the last step, the ``exact`` tactic can use ``hyp`` to solve the goal
because at that point ``hyp`` matches the goal exactly.

.. index:: ring (tactic), tactics ; ring

We close this section by noting that ``mathlib`` provides a
useful bit of automation with a ``ring`` tactic,
which is designed to prove identities in any commutative ring as long as they follow
purely from the ring axioms, without using any local assumption.
TEXT. -/
-- QUOTE:
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- TEXT:
The ``ring`` tactic is imported indirectly when we
import ``Mathlib.Data.Real.Basic``,
but we will see in the next section that it can be used
for calculations on structures other than the real numbers.
It can be imported explicitly with the command
``import Mathlib.Tactic``.
We will see there are similar tactics for other common kind of algebraic
structures.

There is a variation of ``rw`` called ``nth_rewrite`` that allows you to replace only particular instances of an expression in the goal.
Possible matches are enumerated starting with 1,
so in the following example, ``nth_rewrite 2 h`` replaces the second
occurrence of ``a + b`` with ``c``.
EXAMPLES: -/
-- QUOTE:
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
-- QUOTE.
