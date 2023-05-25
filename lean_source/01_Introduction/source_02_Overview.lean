import data.nat.basic
import data.nat.parity
import tactic

open nat
-- SOLUTIONS:
-- There are no exercises in this section.
/- TEXT:
Overview
--------

Put simply, Lean is a tool for building complex expressions in a formal language
known as *dependent type theory*.

.. index:: check, commands ; check

Every expression has a *type*, and you can use the `#check` command to
print it.
Some expressions have types like `ℕ` or `ℕ → ℕ`.
These are mathematical objects.
TEXT. -/
/- These are pieces of data. -/

-- QUOTE:
#check 2 + 2

def f (x : ℕ) := x + 3

#check f
-- QUOTE.

/- TEXT:
Some expressions have type `Prop`.
These are mathematical statements.
TEXT. -/
/- These are propositions, of type `Prop`. -/

-- QUOTE:
#check 2 + 2 = 4

def fermat_last_theorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x^n + y^n ≠ z^n

#check fermat_last_theorem
-- QUOTE.

/- TEXT:
Some expressions have a type, `P`, where `P` itself has type `Prop`.
Such an expression is a proof of the proposition `P`.
TEXT. -/
/- These are proofs of propositions. -/

-- QUOTE:
theorem easy : 2 + 2 = 4 := rfl

#check easy

theorem hard : fermat_last_theorem := sorry

#check hard
-- QUOTE.

/- TEXT:
If you manage to construct an expression of type `fermat_last_theorem` and
Lean accepts it as a term of that type,
you have done something very impressive.
(Using ``sorry`` is cheating, and Lean knows it.)
So now you know the game.
All that is left to learn are the rules.

This book is complementary to a companion tutorial,
`Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`_,
which provides a more thorough introduction to the underlying logical framework
and core syntax of Lean.
*Theorem Proving in Lean* is for people who prefer to read a user manual cover to cover before
using a new dishwasher.
If you are the kind of person who prefers to hit the *start* button and
figure out how to activate the potscrubber feature later,
it makes more sense to start here and refer back to
*Theorem Proving in Lean* as necessary.

Another thing that distinguishes *Mathematics in Lean* from
*Theorem Proving in Lean* is that here we place a much greater
emphasis on the use of *tactics*.
Given that we are trying to build complex expressions,
Lean offers two ways of going about it:
we can write down the expressions themselves
(that is, suitable text descriptions thereof),
or we can provide Lean with *instructions* as to how to construct them.
For example, the following expression represents a proof of the fact that
if ``n`` is even then so is ``m * n``:
TEXT. -/
/- Here are some proofs. -/

-- QUOTE:
example : ∀ m n : nat, even n → even (m * n) :=
assume m n ⟨k, (hk : n = k + k)⟩,
have hmn : m * n = m * k + m * k,
  by rw [hk, mul_add],
show ∃ l, m * n = l + l,
  from ⟨_, hmn⟩
-- QUOTE.

/- TEXT:
The *proof term* can be compressed to a single line:
TEXT. -/
-- QUOTE:
example : ∀ m n : nat, even n → even (m * n) :=
λ m n ⟨k, hk⟩, ⟨m * k, by rw [hk, mul_add]⟩
-- QUOTE.

/- TEXT:
The following is, instead, a *tactic-style* proof of the same theorem:
TEXT. -/
-- QUOTE:
example : ∀ m n : nat, even n → even (m * n) :=
begin
  -- say m and n are natural numbers, and assume n=2*k
  rintros m n ⟨k, hk⟩,
  -- We need to prove m*n is twice a natural. Let's show it's twice m*k.
  use m * k,
  -- substitute in for n
  rw hk,
  -- and now it's obvious
  ring
end
-- QUOTE.

/- TEXT:
As you enter each line of such a proof in VS Code,
Lean displays the *proof state* in a separate window,
telling you what facts you have already established and what
tasks remain to prove your theorem.
You can replay the proof by stepping through the lines,
since Lean will continue to show you the state of the proof
at the point where the cursor is.
In this example, you will then see that
the first line of the proof introduces ``m`` and ``n``
(we could have renamed them at that point, if we wanted to),
and also decomposes the hypothesis ``even n`` to
a ``k`` and the assumption that ``n = 2 * k``.
The second line, ``use m * k``,
declares that we are going to show that ``m * n`` is even by
showing ``m * n = 2 * (m * k)``.
The next line uses the ``rewrite`` tactic
to replace ``n`` by ``2 * k`` in the goal,
and the `ring` tactic solves the resulting goal ``m * (2 * k) = 2 * (m * k)``.

The ability to build a proof in small steps with incremental feedback
is extremely powerful. For that reason,
tactic proofs are often easier and quicker to write than
proof terms.
There isn't a sharp distinction between the two:
tactic proofs can be inserted in proof terms,
as we did with the phrase ``by rw [hk, mul_left_comm]`` in the example above.
We will also see that, conversely,
it is often useful to insert a short proof term in the middle of a tactic proof.
That said, in this book, our emphasis will be on the use of tactics.

In our example, the tactic proof can also be reduced to a one-liner:
TEXT. -/
-- QUOTE:
example : ∀ m n : nat, even n → even (m * n) :=
by { rintros m n ⟨k, hk⟩, use m * k, rw hk, ring }
-- QUOTE.

/- TEXT:
Here we have used tactics to carry out small proof steps.
But they can also provide substantial automation,
and justify longer calculations and bigger inferential steps.
For example, we can invoke Lean's simplifier with
specific rules for simplifying statements about parity to
prove our theorem automatically.
TEXT. -/
-- QUOTE:
example : ∀ m n : nat, even n → even (m * n) :=
by intros; simp * with parity_simps
-- QUOTE.

/- TEXT:
Another big difference between the two introductions is that
*Theorem Proving in Lean* depends only on core Lean and its built-in
tactics, whereas *Mathematics in Lean* is built on top of Lean's
powerful and ever-growing library, *mathlib*.
As a result, we can show you how to use some of the mathematical
objects and theorems in the library,
and some of the very useful tactics.
This book is not meant to be used as an overview of the library;
the `community <https://leanprover-community.github.io/>`_
web pages contain extensive documentation.
Rather, our goal is to introduce you to the style of thinking that
underlies that formalization,
so that you are comfortable browsing the library and
finding things on your own.

Interactive theorem proving can be frustrating,
and the learning curve is steep.
But the Lean community is very welcoming to newcomers,
and people are available on the
`Lean Zulip chat group <https://leanprover.zulipchat.com/>`_ round the clock
to answer questions.
We hope to see you there, and have no doubt that
soon enough you, too, will be able to answer such questions
and contribute to the development of *mathlib*.

So here is your mission, should you choose to accept it:
dive in, try the exercises, come to Zulip with questions, and have fun.
But be forewarned:
interactive theorem proving will challenge you to think about
mathematics and mathematical reasoning in fundamentally new ways.
Your life may never be the same.

*Acknowledgments.* We are grateful to Gabriel Ebner for setting up the
infrastructure for running this tutorial in VS Code.
We are also grateful for help and corrections from
Bryan Gin-ge Chen, Johan Commelin, Mathieu Guay-Paquet, Julian Külshammer,
Giovanni Mascellani, Hunter Monroe, Pietro Monticone, Bartosz Piotrowski,
and Guilherme Silva.
Our work has been partially supported by the Hoskinson Center for
Formal Mathematics.
TEXT. -/
