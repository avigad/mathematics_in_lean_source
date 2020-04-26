.. _logic:

Logic
=====

If mathematics is supposed to be about mathematical objects,
logic is distinguished by the fact that it is
not supposed to be about anything at all.
Rather, it is meant to describe the rules that
govern basic language constructs like
"and," "or," "not," and "if ... then," "every," and "some."
This chapter will show you how to reason about these
logical connectives in Lean, as well as carry out
basic reasoning with equations and inequalities.

Propositional Logic
-------------------

The syntax for the logical connectives is as follows:

.. code-block:: lean

    variables A B C : Prop

    -- if A then B
    #check A → B

    -- A and B
    #check A ∧ B

    -- A or B
    #check A ∨ B

    -- not A
    #check ¬ A

    -- A if and only if B
    #check A ↔ B

    #check true
    #check false

The first line, ``variables A B C : Prop``, declares some variables
ranging over propositions.
In VS Code, you can type the symbols ``→``, ``∧``, ``∨``, ``¬``, and ``↔`` as
``\r``, ``\and,`` ``\or``, ``\not`` and ``\iff``, respectively.
(The symbols don't appear until you hit space or the tab key.)
When reading a Lean file,
if you hover over a symbol,
VS Code will show you the syntax that can be used to enter it.

A typical proof state in Lean looks as follows:

.. code-block::

    1 goal
    x y : ℕ,
    h₁ : prime x,
    h₂ : ¬even x,
    h₃ : y > x
    ⊢ y ≥ 4

The lines before the one that begins with ``⊢`` denote the *context*:
they are the objects and assumptions currently at play.
These include two pieces of data, ``x`` and ``y``,
each a natural number.
They also include three assumptions,
labelled ``h₁``, ``h₂``, and ``h₃``.
In Lean, everything in a context is labelled with an identifier.
You can type these subscripted labels as ``h\1``, ``h\2``, and ``h\3``,
but any legal identifiers would do:
you can use ``h1``, ``h2``, ``h3`` instead,
or ``foo``, ``bar``, and ``baz``.
The last line represents the *target* of the current goal,
that is, the fact to be proved.

To prove an implication, we introduce it with a label.
This moves it to the context, where we can use it.
To *use* an element in the context,
whether it is an implication or an atomic fact,
we can apply it to the goal.

.. code-block:: lean

    variable A : Prop

    -- BEGIN
    example : A → A :=
    begin
      intro h,
      apply h
    end
    -- END

When a tactic proof is that short, one can put it on one line.

.. code-block:: lean

    variable A : Prop

    -- BEGIN
    example : A → A :=
    by { intro h, apply h }

    example : A → A :=
    by intro h; apply h
    -- END

The ``by`` command uses a single tactic to prove a goal.
The curly brackets are notation for a ``begin ... end`` pair,
which condense a sequence of tactic instructions to a single one.
We will see later that the semantics of the semicolon is slightly different;
``t1; t2`` also combines two tactics into one,
but if applying ``t1`` results in more than one goal, ``t2`` is applied
to all of them.
If you put the cursor after the comma in ``{ intro h, apply h }``,
Lean will still show you the proof state at that point.
A disadvantage of using the semicolon is that in this case
there is no intermediate state;
``intro h; apply h`` is really a single compound step.

Here is a more interesting example.

.. code-block:: lean

    variables A B C : Prop

    -- BEGIN
    example : (A → B) → (B → C) → A → C :=
    begin
      intros h₁ h₂ h₃,
      apply h₂,
      apply h₁,
      apply h₃
    end
    -- END

This illustrates an important feature of
the implication notation, namely,
that iterated implication associates *to the right*.
This means that the example above is parsed as ``(A → B) → ((B → C) → (A → C))``.
This convention supports the fact that it is common to state
a theorem as an implication from hypotheses to a conclusion.
Thus the example above can be read as the theorem that states that
``C`` follows from hypotheses ``(A → B)``, ``(B → C)``, and  ``A``.
Of course, to prove such a theorem,
the first thing you will do is introduce the hypotheses and name them.
Because this pattern is so common,
Lean also offers syntax to state a goal
with the hypotheses already introduced:

.. code-block:: lean

    variables A B C : Prop

    -- BEGIN
    example (h₁ : A → B) (h₂ : B → C) : A → C :=
    begin
      intro h₃,
      apply h₂,
      apply h₁,
      apply h₃
    end
    -- END

Because introduction and application are so fundamental,
it is often useful to replace tactic steps by the
corresponding proof term.
The notation for introduction is *lambda abstraction*:
if ``A`` is any ``Prop`` and ``t`` is a proof of ``B``
in a context that includes ``h : A``,
then ``λ h : A, t`` is a proof of ``A → B``.
The label ``h : A`` can be simplified to ``h`` when
Lean can infer ``A`` from the current context and goal.
The notation for application of an implication to a hypothesis
is simply to write one term next to the other:
given ``h₁ : A → B`` and ``h₂ : A``, the expression
``h₁ h₂`` denotes a proof of ``B``.
Thus all of the following work:

.. code-block:: lean

    variables A B C : Prop

    -- BEGIN
    example : A → A :=
    λ h : A, h

    example : A → A :=
    λ h, h

    example (h₁ : A → B) (h₂ : B → C) : A → C :=
    begin
      intro h₃,
      apply h₂ (h₁ h₃)
    end

    example (h₁ : A → B) (h₂ : B → C) : A → C :=
    begin
      intro h₃,
      exact h₂ (h₁ h₃)
    end

    example (h₁ : A → B) (h₂ : B → C) : A → C :=
    λ h₃, h₂ (h₁ h₃)
    -- END

The ``exact`` tactic is like the ``apply`` tactic,
except that it is expected to solve the current goal exactly,
rather than reduce it to other subgoals,
which can happen when one applies an implication.
Using ``exact`` provides structure to a tactic proof,
since it signals to Lean and to the reader that
the command finishes off the current goal.

Lean provides additional mechanisms to structure a tactic proof.
The ``have`` tactic introduces an intermediate subgoal:
if you type ``have h : A`` in a context in which the target is ``B``,
you are left with two subgoals:
first, you are required to prove ``A`` in the current context,
and then you are required to prove ``B`` in a context that includes ``A``.

.. code-block:: lean

    variables A B C : Prop

    -- BEGIN
    example (h₁ : A → B) (h₂ : B → C) : A → C :=
    begin
      intro h₃,
      have h₄ : B,
      { apply h₁, apply h₃ },
      show C,
      apply h₂, apply h₄
    end
    -- END

In this example, the ``show`` command does nothing substantial.
It only serves to confirm to Lean,
and to the reader of the proof,
that at that stage the goal is to prove ``C``.
(Later we will see that ``show`` is syntactic sugar for the ``change`` tactic,
and can often be used to re-express the target in an
equivalent form.)

Let's move on to "and," otherwise known as *conjunction*.
Given a target of ``A ∧ B,`` the ``split`` tactic reduces the current
goal to the two goals of proving ``A`` and ``B``,
respectively, each in the same context.
On the other hand, given ``h : A ∧ B`` as a *hypothesis*,
the expressions ``h.1`` and ``h.2`` provide proofs of ``A`` and ``B``, respectively.

.. code-block:: lean

    variables A B : Prop

    -- BEGIN
    example : A ∧ B → B ∧ A :=
    begin
      intro h,
      split,
      apply h.2,
      apply h.1
    end
    -- END

The notations ``h.1`` and ``h.2`` are instances of Lean's general
projection notation.
As we will see, it can be used in lots of situations where
an object or hypothesis represent and amalgamation.

Instead of using the ``split`` tactic,
we can use Lean's *anonymous constructor notation*
``⟨..., ..., ...⟩`` to tell Lean to put together the object
we want. You can type the corner brackets with ``\<`` and ``\>``.

.. code-block:: lean

    variables A B : Prop

    -- BEGIN
    example : A ∧ B → B ∧ A :=
    begin
      intro h,
      exact ⟨h.2, h.1⟩
    end
    -- END

Just as anonymous constructors provide a general
swiss-army-knife for putting together proofs and data,
the ``cases`` tactic provides a general methods
of *decomposing* proofs and data.
In the next example, it decomposes ``h : A ∧ B`` into
the two hypotheses ``h₁: A`` and ``h₂ : B``.

.. code-block:: lean

    variables A B : Prop

    -- BEGIN
    example : A ∧ B → B ∧ A :=
    begin
      intro h,
      cases h with h₁ h₂,
      exact ⟨h₂, h₁⟩
    end
    -- END

*Mathlib* provides a tactic, ``rintros``, that combines the
``intro`` and ``cases`` steps into one.
Because it is not a core Lean tactic, we need to add
the line ``import tactic`` to the top of the file.
The *pattern* ``⟨h₁, h₂⟩`` provides names for the hypotheses
that are introduced.

.. code-block:: lean

    import tactic

    variables A B : Prop

    example : A ∧ B → B ∧ A :=
    begin
      rintros ⟨h₁, h₂⟩,
      exact ⟨h₂, h₁⟩
    end

In fact, the use of lambda abstraction in a Lean expression
also supports this sort of pattern matching,

.. code-block:: lean

    variables A B : Prop

    -- BEGIN
    example : A ∧ B → B ∧ A :=
    λ ⟨h₁, h₂⟩, ⟨h₂, h₁⟩
    -- END

Even when writing tactic proofs,
it is often useful to use short proof terms like this
to finish off a subgoal,
for example, using the ``exact`` tactic.

According to Lean's parsing rules,
conjunction associates to the right,
so ``A ∧ B ∧ C`` is the same as ``A ∧ (B ∧ C)``.
The ``rintros`` tactic allows for more complex nested
patterns to decompose a hypothesis like this.
(The "r" stands for "recursive.")
Similarly, the ``rcases`` tactic,
like the ``cases`` tactic,
can be used to decompose a hypothesis
that is already introduced.

.. code-block:: lean

    import tactic

    variables A B : Prop

    -- BEGIN
    example : A ∧ (B ∧ C) ∧ D → (B ∧ D) ∧ A :=
    begin
      rintros ⟨h₁, ⟨h₂, _⟩, h₃⟩,
      exact ⟨⟨h₂, h₃⟩, h₁⟩
    end

    example (h : A ∧ (B ∧ C) ∧ D) : (B ∧ D) ∧ A :=
    begin
      rcases h with ⟨h₁, ⟨h₂, _⟩, h₃⟩,
      exact ⟨⟨h₂, h₃⟩, h₁⟩
    end
    -- END

This example illustrates another nice bit of Lean syntax:
you can use the underscore symbol as an *anonymous label*
to avoid naming a hypothesis or piece of data that you
do not need to refer to later on.

We will close this section with a discussion of *negation* and *falsity*.
In Lean, ``¬ A`` is defined to be ``A → false``.
This takes some getting used to,
but make sense if you think of ``¬ A`` as equivalent to
the statement "if ``A`` is true, then ``2 + 2 = 5``,"
where ``2 + 2 = 5`` is a prototypical falsehood.
An advantage to this definition is that Lean can unfold the definition
when necessary,
so that introduction and application work the same way for negation
as they do for implication.

.. code-block:: lean

    variables A B : Prop

    -- BEGIN
    example : (A → B) → ¬ B → ¬ A :=
    begin
      intros h₁ h₂ h₃,
      apply h₂,
      apply h₁,
      apply h₃
    end
    -- END

This proof may look familiar:
it is exactly the same proof we used to establish ``(A → B) → (B → C) → A → C``.
We can see that the example above is an instance of the general
result by naming the general result and then applying it:

.. code-block:: lean

    variables A B : Prop

    -- BEGIN
    theorem impl_compose : (A → B) → (B → C) → A → C :=
    λ h₁ h₂ h₃, h₂ (h₁ h₃)

    example : (A → B) → ¬ B → ¬ A :=
    by apply impl_compose

    example : (A → B) → ¬ B → ¬ A :=
    impl_compose A B false

    example (h₁ : A → B) (h₂ : ¬ B) : ¬ A :=
    impl_compose A B false h₁ h₂
    -- END

The fact that the arguments ``A``, ``B``, and ``false`` have to be provided
in the last two examples give us an opportunity to introduce another important
feature of Lean,
namely, the ability to declare arguments as *implicit*.
In the first example, the ``apply`` command works because Lean is able to
infer the arguments from the target of the goal.
For the same reason,
we can use an underscore character to leave the arguments
implicit in the proof-term representation:

.. code-block:: lean

    variables A B : Prop

    -- BEGIN
    example : (A → B) → ¬ B → ¬ A :=
    impl_compose _ _ _

    example (h₁ : A → B) (h₂ : ¬ B) : ¬ A :=
    impl_compose _ _ _ h₁ h₂
    -- END

But typing underscores can be tedious,
and so Lean allows us to use curly braces to
specify that the arguments will be suppressed by default:

.. code-block:: lean

    variables A B : Prop

    -- BEGIN
    theorem impl_compose {A B C : Prop} : (A → B) → (B → C) → A → C :=
    λ h₁ h₂ h₃, h₂ (h₁ h₃)

    example : (A → B) → ¬ B → ¬ A :=
    impl_compose

    example (h₁ : A → B) (h₂ : ¬ B) : ¬ A :=
    impl_compose h₁ h₂
    -- END

You needn't worry about the details right now.
We will have more to say about the use of implicit arguments
the next time they come up.

Given that ``¬ A`` is defined to be ``A → false``,
what can we say about ``false``?
One we have ``false`` in our context,
our swiss-army knife, the ``cases`` tactic,
can use it to establish any conclusion.
The intuition is that if we try to split on all the
ways a contradiction can come about, there aren't any,
and so the proof is done.
Alternatively, Lean has a ``contradiction`` tactic,
which tries to close a goal by finding any of a number
of types of overt contradiction in the context.

.. code-block:: lean

    variables A : Prop

    -- BEGIN
    example : false → A :=
    by { intro h, cases h }

    example : false → A :=
    by { intro h, contradiction }

    example (h₁ : B) (h₂ : ¬ B) : A :=
    by contradiction
    -- END

We recognize that we have thrown a lot of information at you,
and it may be overwhelming.
But don't worry if some of the details are still mysterious.
John von Neumann once wrote,
"in mathematics, you never understand things; you just get used to them."
The mechanisms underlying interactive theorem proving are not nearly
as deep,
but the fact remains that you do not need to understand them fully
to start proving theorems.
As we continue to use the patterns above,
you will get more and more used to them,
to the point where they become second nature.

To get you to that point, however,
we strongly encourage you to work through
the exercises below.
Click on the ``try it!`` button and
try to replace each ``sorry`` by a correct proof,
using the tactics and syntax we have covered in this section.
We also encourage you to ask questions on the Lean Zulip channel
if you have difficulty.
When you click ``try it!``,
the exercises will be opened in a file named ``propositional_logic.lean``
in the ``exercises/logic/`` directory.
On Zulip, you can helpfully specify that you are asking about
the third exercise by referring to it as
"the third problem in ``exercises/logic/propositional_logic.lean``."

.. code-block:: lean

    /* exercises/logic/propositional_logic.lean */

    import tactic

    variables A B C : Prop

    example : A ∧ (A → B) → A ∧ B :=
    sorry

    example : B → (A → B) :=
    sorry

    example (h : A ∧ B → C) : A → B → C :=
    sorry

    example (h : A → B → C) : A ∧ B → C :=
    sorry

    example : (A → B) ∧ (B → C) ∧ A → C :=
    sorry

    example : A → (A → B) → (A ∧ B → C) → C :=
    sorry

    -- use rcases
    example (h : A ∧ (A → B) ∧ (A ∧ B → C)) : C :=
    sorry

    example : A → ¬ (¬ A ∧ B) :=
    sorry

    example : ¬ (A ∧ B) → A → ¬ B :=
    sorry

    example : A ∧ ¬ A → B :=
    sorry


More Connectives
----------------

or, iff

include an example with ``classical.em A``,
but defer more on classical reasoning until later.

Quantifiers
-----------

Classical Logic
---------------

decidability, computability

proof by cases, proof by contradiction

``open_local_classical``

Equality
--------

Describe rewrite, simp, calc

Do some calculations with integers and reals.

Do some examples of identities in groups, with inverses and conjugates, inverses unique, etc.

Do some examples of proving identities in lattices, with meets and joins.

Do some trig identities.

A nice example, illustrating the ``ring`` tactic:

.. code-block:: lean

    import algebra.group_power tactic.ring

    variables {α : Type*} [comm_ring α]

    def sos (x : α) := ∃ a b, x = a^2 + b^2

    theorem sos_mul {x y : α} (sosx : sos x) (sosy : sos y) : sos (x * y) :=
    begin
      rcases sosx with ⟨a, b, xeq⟩,
      rcases sosy with ⟨c, d, yeq⟩,
      use [a*c - b*d, a*d + b*c],
      rw [xeq, yeq], ring
    end

Add exercises for all of these.

Inequalities
------------

AM-GM inequality.

Identities in lattices.

complete lattices have lubs.