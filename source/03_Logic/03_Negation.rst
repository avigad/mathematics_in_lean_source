.. _negation:

Negation
--------

The symbol ``¬`` is meant to express negation,
so ``¬ x < y`` says that ``x`` is not less than ``y``,
``¬ x = y`` (or, equivalently, ``x ≠ y``) says that
``x`` is not equal to ``y``,
and ``¬ ∃ z, x < z ∧ z < y`` says that there does not exist a ``z``
strictly between ``x`` and ``y``.
In Lean, the notation ``¬ A`` abbreviates ``A → false``,
which you can think of as saying that ``A`` implies a contradiction.
Practically speaking, this means that you already know something
about how to work with negations:
you can prove ``¬ A`` by introducing a hypothesis ``h : A``
and proving ``false``,
and if you have ``h : ¬ A`` and ``h' : A``,
then applying ``h`` to ``h'`` yields ``false``.

To illustrate, consider the irreflexivity principle ``lt_irrefl``
for a strict order,
which says that we have ``¬ a < a`` for every ``a``.
The asymmetry principle ``lt_asymm`` says that we have
``a < b → ¬ b < a``. Let's show that ``lt_asymm`` follows
from ``lt_irrefl``.

.. code-block:: lean

  example (h : a < b) : ¬ b < a :=
  begin
    intro h',
    have : a < a,
      from lt_trans h h',
    apply lt_irrefl a this
  end

.. index:: this, have, tactics ; have, from, tactics ; from

This example introduces a couple of new tricks.
First, when you use ``have`` without providing
a label,
Lean uses the name ``this``,
providing a convenient way to refer back to it.
Also, the ``from`` tactic is syntactic sugar for ``exact``,
providing a nice way to justify a ``have`` with an explicit
proof term.
But what you should really be paying attention to in this
proof is the result of the ``intro`` tactic,
which leaves a goal of ``false``,
and the fact that we eventually prove ``false``
by applying ``lt_irrefl`` to a proof of ``a < a``.

Here is another example, which uses the
predicate ``fn_has_ub`` defined in the last section,
which says that a function has an upper bound.

.. code-block:: lean

  example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
  begin
    intros fnub,
    cases fnub with a fnuba,
    cases h a with x hx,
    have : f x ≤ a,
      from fnuba x,
    linarith
  end

See if you can prove these in a similar way:

.. code-block:: lean

  example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
  sorry
  
  example : ¬ fn_has_ub (λ x, x) :=
  sorry

Mathlib offers a number of useful theorems for relating orders
and negations:

.. code-block:: lean

  #check (not_le_of_gt : a > b → ¬ a ≤ b)
  #check (not_lt_of_ge : a ≥ b → ¬ a < b)
  #check (lt_of_not_ge : ¬ a ≥ b → a < b)
  #check (le_of_not_gt : ¬ a > b → a ≤ b)

Recall the predicate ``monotone f``,
which says that ``f`` is nondecreasing.
Use some of the theorems just enumerated to prove the following:

.. code-block:: lean

  example (h : monotone f) (h' : f a < f b) : a < b :=
  sorry
  
  example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
  sorry

Remember that it is often convenient to use ``linarith``
when a goal follows from linear equations and
inequalities that in the context.

We can show that the first example in the last snippet
cannot be proved if we replace ``<`` by ``≤``.
Notice that we can prove the negation of a universally
quantified statement by giving a counterexample.
Complete the proof.

.. code-block:: lean

  example :
    ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
  begin
    intro h,
    let f := λ x : ℝ, (0 : ℝ),
    have monof : monotone f,
    { sorry },
    have h' : f 1 ≤ f 0,
      from le_refl _,
    sorry
  end

.. index:: let, tactics ; let

This example introduces the ``let`` tactic,
which adds a *local definition* to the context.
If you put the cursor after the ``let`` command,
in the goal window you will see that the definition
``f : ℝ → ℝ := λ (x : ℝ), 0`` has been added to the context.
Lean will unfold the definition of ``f`` when it has to.
In particular, when we prove ``f 1 ≤ f 0`` with ``le_refl``,
Lean reduces ``f 1`` and ``f 0`` to ``0``.

Use ``le_of_not_gt`` to prove the following:

.. code-block:: lean

  example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
  sorry

Implicit in many of the proofs we have just done
is the fact that if ``P`` is any property,
saying that there is nothing with property ``P``
is the same as saying that everything fails to have
property ``P``,
and saying that not everything has property ``P``
is equivalent to saying that something fails to have property ``P``.
In other words, all four of the following implications
are valid (but one of them cannot be proved with what we explained so
far):

.. code-block:: lean

  variables {α : Type*} (P : α → Prop) (Q : Prop)
  
  example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
  sorry
  
  example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
  sorry
  
  example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
  sorry
  
  example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
  sorry

The first, second, and fourth are straightforward to
prove using the methods you have already seen.
We encourage you to try it.
The third is more difficult, however,
because it concludes that an object exists
from the fact that its nonexistence is contradictory.
This is an instance of *classical* mathematical reasoning,
and, in general, you have to declare your intention
of using such reasoning by adding the command
``open_locale classical`` to your file.
With that command, we can use proof by contradiction
to prove the third implication as follows.

.. code-block:: lean

  open_locale classical
  
  example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
  begin
    by_contradiction h',
    apply h,
    intro x,
    show P x,
    by_contradiction h'',
    exact h' ⟨x, h''⟩
  end

.. index:: by_contradiction, by_contra, tactics ; by_contra and by_contradiction,

Make sure you understand how this works.
The ``by_contradiction`` tactic (also abbreviated to ``by_contra``)
allows us to prove a goal ``Q`` by assuming ``¬ Q``
and deriving a contradiction.
In fact, it is equivalent to using the
equivalence ``not_not : ¬ ¬ Q ↔ Q``.
Confirm that you can prove the forward direction
of this equivalence using ``by_contradiction``,
while the reverse direction follows from the
ordinary rules for negation.

.. code-block:: lean

  example (h : ¬ ¬ Q) : Q :=
  sorry
  
  example (h : Q) : ¬ ¬ Q :=
  sorry

Use proof by contradiction to establish the following,
which is the converse of one of the implications we proved above.
(Hint: use ``intro`` first.)

.. code-block:: lean

  example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
  sorry

.. index:: push_neg, tactics ; push_neg

It is often tedious to work with compound statements with
a negation in front,
and it is a common mathematical pattern to replace such
statements with equivalent forms in which the negation
has been pushed inward.
To facilitate this, mathlib offers a ``push_neg`` tactic,
which restates the goal in this way.
The command ``push_neg at h`` restates the hypothesis ``h``.

.. code-block:: lean

  example (h : ¬ ∀ a, ∃ x, f x > a) : fn_has_ub f :=
  begin
    push_neg at h,
    exact h
  end
  
  example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
  begin
    simp only [fn_has_ub, fn_ub] at h,
    push_neg at h,
    exact h
  end

In the second example, we use Lean's simplifier to
expand the definitions of ``fn_has_ub`` and ``fn_ub``.
(We need to use ``simp`` rather than ``rw``
to expand ``fn_ub``,
because it appears in the scope of a quantifier.)
You can verify that in the examples above
with ``¬ ∃ x, P x`` and ``¬ ∀ x, P x``,
the ``push_neg`` tactic does the expected thing.
Without even knowing how to use the conjunction
symbol,
you should be able to use ``push_neg``
to prove the following:

.. code-block:: lean

  example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
  sorry

.. index:: contrapose, tactics ; contrapose

Mathlib also has a tactic, ``contrapose``,
which transforms a goal ``A → B`` to ``¬ B → ¬ A``.
Similarly, given a goal of proving ``B`` from
hypothesis ``h : A``,
``contrapose h`` leaves you with a goal of proving
``¬ A`` from hypothesis ``¬ B``.
Using ``contrapose!`` instead of ``contrapose``
applies ``push_neg`` to the goal and the relevant
hypothesis as well.

.. code-block:: lean

  example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
  begin
    contrapose! h,
    exact h
  end
  
  example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
  begin
    contrapose! h,
    use x / 2,
    split; linarith
  end

We have not yet explained the ``split`` command
or the use of the semicolon after it,
but we will do that in the next section.

.. TODO: make sure we explain split and the semicolon
   in the next section

We close this section with
the principle of *ex falso*,
which says that anything follows from a contradiction.
In Lean, this is represented by ``false.elim``,
which establishes ``false → P`` for any proposition ``P``.
This may seem like a strange principle,
but it comes up fairly often.
We often prove a theorem by splitting on cases,
and sometimes we can show that one of
the cases is contradictory.
In that case, we need to assert that the contradiction
establishes the goal so we can move on to the next one.
(We will see instances of reasoning by cases in
:numref:`disjunction`.)

.. index:: exfalso, contradiction, absurd, tactics ; exfalso, tactics ; contradiction

Lean provides a number of ways of closing
a goal once a contradiction has been reached.

.. code-block:: lean

  example (h : 0 < 0) : a > 37 :=
  begin
    exfalso,
    apply lt_irrefl 0 h
  end
  
  example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)
  
  example (h : 0 < 0) : a > 37 :=
  begin
    have h' : ¬ 0 < 0,
      from lt_irrefl 0,
    contradiction
  end

The ``exfalso`` tactic replaces the current goal with
the goal of proving ``false``.
Given ``h : P`` and ``h' : ¬ P``,
the term ``absurd h h'`` establishes any proposition.
Finally, the ``contradiction`` tactic tries to close a goal
by finding a contradiction in the hypotheses,
such as a pair of the form ``h : P`` and ``h' : ¬ P``.
Of course, in this example, ``linarith`` also works.
