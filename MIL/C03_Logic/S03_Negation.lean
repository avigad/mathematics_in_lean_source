-- BOTH:
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C03S03

/- TEXT:
.. _negation:

Negation
--------

The symbol ``¬`` is meant to express negation,
so ``¬ x < y`` says that ``x`` is not less than ``y``,
``¬ x = y`` (or, equivalently, ``x ≠ y``) says that
``x`` is not equal to ``y``,
and ``¬ ∃ z, x < z ∧ z < y`` says that there does not exist a ``z``
strictly between ``x`` and ``y``.
In Lean, the notation ``¬ A`` abbreviates ``A → False``,
which you can think of as saying that ``A`` implies a contradiction.
Practically speaking, this means that you already know something
about how to work with negations:
you can prove ``¬ A`` by introducing a hypothesis ``h : A``
and proving ``False``,
and if you have ``h : ¬ A`` and ``h' : A``,
then applying ``h`` to ``h'`` yields ``False``.

To illustrate, consider the irreflexivity principle ``lt_irrefl``
for a strict order,
which says that we have ``¬ a < a`` for every ``a``.
The asymmetry principle ``lt_asymm`` says that we have
``a < b → ¬ b < a``. Let's show that ``lt_asymm`` follows
from ``lt_irrefl``.
TEXT. -/
-- BOTH:
section
variable (a b : ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this
-- QUOTE.

/- TEXT:
.. index:: this, have, tactics ; have, from, tactics ; from

This example introduces a couple of new tricks.
First, when you use ``have`` without providing
a label,
Lean uses the name ``this``,
providing a convenient way to refer back to it.
Because the proof is so short, we provide an explicit proof term.
But what you should really be paying attention to in this
proof is the result of the ``intro`` tactic,
which leaves a goal of ``False``,
and the fact that we eventually prove ``False``
by applying ``lt_irrefl`` to a proof of ``a < a``.

Here is another example, which uses the
predicate ``FnHasUb`` defined in the last section,
which says that a function has an upper bound.
TEXT. -/
-- BOTH:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith
-- QUOTE.

/- TEXT:
Remember that it is often convenient to use ``linarith``
when a goal follows from linear equations and
inequalities that in the context.

See if you can prove these in a similar way:
TEXT. -/
-- QUOTE:
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

example : ¬FnHasUb fun x ↦ x :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  rintro ⟨a, ha⟩
  rcases h a with ⟨x, hx⟩
  have := ha x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, ha⟩
  have : a + 1 ≤ a := ha (a + 1)
  linarith

/- TEXT:
Mathlib offers a number of useful theorems for relating orders
and negations:
TEXT. -/
-- QUOTE:
#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)
-- QUOTE.

/- TEXT:
Recall the predicate ``Monotone f``,
which says that ``f`` is nondecreasing.
Use some of the theorems just enumerated to prove the following:
TEXT. -/
-- QUOTE:
example (h : Monotone f) (h' : f a < f b) : a < b := by
  sorry

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h'
  apply not_lt_of_ge (h h'')

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  apply h'' h

/- TEXT:
We can show that the first example in the last snippet
cannot be proved if we replace ``<`` by ``≤``.
Notice that we can prove the negation of a universally
quantified statement by giving a counterexample.
Complete the proof.
TEXT. -/
-- QUOTE:
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by sorry
  have h' : f 1 ≤ f 0 := le_refl _
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b leab
    rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith

/- TEXT:
.. index:: let, tactics ; let

This example introduces the ``let`` tactic,
which adds a *local definition* to the context.
If you put the cursor after the ``let`` command,
in the goal window you will see that the definition
``f : ℝ → ℝ := fun x ↦ 0`` has been added to the context.
Lean will unfold the definition of ``f`` when it has to.
In particular, when we prove ``f 1 ≤ f 0`` with ``le_refl``,
Lean reduces ``f 1`` and ``f 0`` to ``0``.

Use ``le_of_not_gt`` to prove the following:
TEXT. -/
-- QUOTE:
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  linarith [h _ h']

-- BOTH:
end

/- TEXT:
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
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} (P : α → Prop) (Q : Prop)

-- EXAMPLES:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, Px⟩
  exact h x Px

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, nPx⟩
  apply nPx
  apply h'

/- TEXT:
The first, second, and fourth are straightforward to
prove using the methods you have already seen.
We encourage you to try it.
The third is more difficult, however,
because it concludes that an object exists
from the fact that its nonexistence is contradictory.
This is an instance of *classical* mathematical reasoning.
We can use proof by contradiction
to prove the third implication as follows.
TEXT. -/
-- QUOTE:
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩
-- QUOTE.

/- TEXT:
.. index:: by_contra, tactics ; by_contra and by_contradiction,

Make sure you understand how this works.
The ``by_contra`` tactic
allows us to prove a goal ``Q`` by assuming ``¬ Q``
and deriving a contradiction.
In fact, it is equivalent to using the
equivalence ``not_not : ¬ ¬ Q ↔ Q``.
Confirm that you can prove the forward direction
of this equivalence using ``by_contra``,
while the reverse direction follows from the
ordinary rules for negation.
TEXT. -/
-- QUOTE:
example (h : ¬¬Q) : Q := by
  sorry

example (h : Q) : ¬¬Q := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := by
  intro h'
  exact h' h

-- BOTH:
end

/- TEXT:
Use proof by contradiction to establish the following,
which is the converse of one of the implications we proved above.
(Hint: use ``intro`` first.)
TEXT. -/
-- BOTH:
section
variable (f : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  apply h'
  use x

/- TEXT:
.. index:: push_neg, tactics ; push_neg

It is often tedious to work with compound statements with
a negation in front,
and it is a common mathematical pattern to replace such
statements with equivalent forms in which the negation
has been pushed inward.
To facilitate this, mathlib offers a ``push_neg`` tactic,
which restates the goal in this way.
The command ``push_neg at h`` restates the hypothesis ``h``.
TEXT. -/
-- QUOTE:
example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h
-- QUOTE.

/- TEXT:
In the second example, we use dsimp to
expand the definitions of ``FnHasUb`` and ``FnUb``.
(We need to use ``dsimp`` rather than ``rw``
to expand ``FnUb``,
because it appears in the scope of a quantifier.)
You can verify that in the examples above
with ``¬∃ x, P x`` and ``¬∀ x, P x``,
the ``push_neg`` tactic does the expected thing.
Without even knowing how to use the conjunction
symbol,
you should be able to use ``push_neg``
to prove the following:
TEXT. -/
-- QUOTE:
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg  at h
  exact h

/- TEXT:
.. index:: contrapose, tactics ; contrapose

Mathlib also has a tactic, ``contrapose``,
which transforms a goal ``A → B`` to ``¬B → ¬A``.
Similarly, given a goal of proving ``B`` from
hypothesis ``h : A``,
``contrapose h`` leaves you with a goal of proving
``¬A`` from hypothesis ``¬B``.
Using ``contrapose!`` instead of ``contrapose``
applies ``push_neg`` to the goal and the relevant
hypothesis as well.
TEXT. -/
-- QUOTE:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith
-- QUOTE.

-- BOTH:
end

/- TEXT:
We have not yet explained the ``constructor`` command
or the use of the semicolon after it,
but we will do that in the next section.

We close this section with
the principle of *ex falso*,
which says that anything follows from a contradiction.
In Lean, this is represented by ``False.elim``,
which establishes ``False → P`` for any proposition ``P``.
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
TEXT. -/
section
variable (a : ℕ)

-- QUOTE:
example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction
-- QUOTE.

end

/- TEXT:
The ``exfalso`` tactic replaces the current goal with
the goal of proving ``False``.
Given ``h : P`` and ``h' : ¬ P``,
the term ``absurd h h'`` establishes any proposition.
Finally, the ``contradiction`` tactic tries to close a goal
by finding a contradiction in the hypotheses,
such as a pair of the form ``h : P`` and ``h' : ¬ P``.
Of course, in this example, ``linarith`` also works.
TEXT. -/
