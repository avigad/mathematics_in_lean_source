-- BOTH:
import Mathlib.Data.Real.Basic

namespace C03S01
/- TEXT:
.. _implication_and_the_universal_quantifier:

Implication and the Universal Quantifier
----------------------------------------

Consider the statement after the ``#check``:
TEXT. -/
-- QUOTE:
#check ∀ x : ℝ, 0 ≤ x → |x| = x
-- QUOTE.

/- TEXT:
In words, we would say "for every real number ``x``, if ``0 ≤ x`` then
the absolute value of ``x`` equals ``x``".
We can also have more complicated statements like:
TEXT. -/
-- QUOTE:
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε
-- QUOTE.

/- TEXT:
In words, we would say "for every ``x``, ``y``, and ``ε``,
if ``0 < ε ≤ 1``, the absolute value of ``x`` is less than ``ε``,
and the absolute value of ``y`` is less than ``ε``,
then the absolute value of ``x * y`` is less than ``ε``."
In Lean, in a sequence of implications there are
implicit parentheses grouped to the right.
So the expression above means
"if ``0 < ε`` then if ``ε ≤ 1`` then if ``|x| < ε`` ..."
As a result, the expression says that all the
assumptions together imply the conclusion.

You have already seen that even though the universal quantifier
in this statement
ranges over objects and the implication arrows introduce hypotheses,
Lean treats the two in very similar ways.
In particular, if you have proved a theorem of that form,
you can apply it to objects and hypotheses in the same way.
We will use as an example the following statement that we will help you to prove a
bit later:
TEXT. -/
-- QUOTE:
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end
-- QUOTE.

/- TEXT:
You have also already seen that it is common in Lean
to use curly brackets to make quantified variables implicit
when they can be inferred from subsequent hypotheses.
When we do that, we can just apply a lemma to the hypotheses without
mentioning the objects.
TEXT. -/
-- QUOTE:
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end
-- QUOTE.

/- TEXT:
At this stage, you also know that if you use
the ``apply`` tactic to apply ``my_lemma``
to a goal of the form ``|a * b| < δ``,
you are left with new goals that require you to  prove
each of the hypotheses.

.. index:: intro, tactics; intro

To prove a statement like this, use the ``intro`` tactic.
Take a look at what it does in this example:
TEXT. -/
-- QUOTE:
theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry
-- QUOTE.

/- TEXT:
We can use any names we want for the universally quantified variables;
they do not have to be ``x``, ``y``, and ``ε``.
Notice that we have to introduce the variables
even though they are marked implicit:
making them implicit means that we leave them out when
we write an expression *using* ``my_lemma``,
but they are still an essential part of the statement
that we are proving.
After the ``intro`` command,
the goal is what it would have been at the start if we
listed all the variables and hypotheses *before* the colon,
as we did in the last section.
In a moment, we will see why it is sometimes necessary to
introduce variables and hypotheses after the proof begins.

To help you prove the lemma, we will start you off:
TEXT. -/
-- QUOTE:
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := sorry
    _ ≤ |x| * ε := sorry
    _ < 1 * ε := sorry
    _ = ε := sorry
-- QUOTE.

-- OMIT:
/- TODO : remember to introduce ``suffices`` eventually

   We have introduced another new tactic here:
   ``suffices`` works like ``have`` in reverse,
   asking you to prove the goal using the
   stated fact,
   and then leaving you the new goal of proving that fact. -/
/- TEXT:
Finish the proof using the theorems
``abs_mul``, ``mul_le_mul``, ``abs_nonneg``,
``mul_lt_mul_right``, and ``one_mul``.
Remember that you can find theorems like these using
Ctrl-space completion (or Cmd-space completion on a Mac).
Remember also that you can use ``.mp`` and ``.mpr``
or ``.1`` and ``.2`` to extract the two directions
of an if-and-only-if statement.

Universal quantifiers are often hidden in definitions,
and Lean will unfold definitions to expose them when necessary.
For example, let's define two predicates,
``FnUb f a`` and ``FnLb f a``,
where ``f`` is a function from the real numbers to the real
numbers and ``a`` is a real number.
The first says that ``a`` is an upper bound on the
values of ``f``,
and the second says that ``a`` is a lower bound
on the values of ``f``.
BOTH: -/
-- QUOTE:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x
-- QUOTE.

/- TEXT:
.. index:: lambda abstraction

In the next example, ``fun x ↦ f x + g x`` is the
function that maps ``x`` to ``f x + g x``. Going from the expression ``f x + g x``
to this function is called a lambda abstraction in type theory.
BOTH: -/
section
variable (f g : ℝ → ℝ) (a b : ℝ)

-- EXAMPLES:
-- QUOTE:
example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb
-- QUOTE.

/- TEXT:
.. index:: dsimp, tactics ; dsimp, change, tactics ; change

Applying ``intro`` to the goal ``FnUb (fun x ↦ f x + g x) (a + b)``
forces Lean to unfold the definition of ``FnUb``
and introduce ``x`` for the universal quantifier.
The goal is then ``(fun (x : ℝ) ↦ f x + g x) x ≤ a + b``.
But applying ``(fun x ↦ f x + g x)`` to ``x`` should result in ``f x + g x``,
and the ``dsimp`` command performs that simplification.
(The "d" stands for "definitional.")
You can delete that command and the proof still works;
Lean would have to perform that contraction anyhow to make
sense of the next ``apply``.
The ``dsimp`` command simply makes the goal more readable
and helps us figure out what to do next.
Another option is to use the ``change`` tactic
by writing ``change f x + g x ≤ a + b``.
This helps make the proof more readable,
and gives you more control over how the goal is transformed.

The rest of the proof is routine.
The last two ``apply`` commands force Lean to unfold the definitions
of ``FnUb`` in the hypotheses.
Try carrying out similar proofs of these:
TEXT. -/
-- QUOTE:
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  sorry

example (hfa : FnUb f a) (hfb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  apply mul_nonneg
  apply nnf
  apply nng

example (hfa : FnUb f a) (hfb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  apply mul_le_mul
  apply hfa
  apply hfb
  apply nng
  apply nna

-- BOTH:
end

/- TEXT:
Even though we have defined ``FnUb`` and ``FnLb`` for functions
from the reals to the reals,
you should recognize that the definitions and proofs are much
more general.
The definitions make sense for functions between any two types
for which there is a notion of order on the codomain.
Checking the type of the theorem ``add_le_add`` shows that it holds
of any structure that is an "ordered additive commutative monoid";
the details of what that means don't matter now,
but it is worth knowing that the natural numbers, integers, rationals,
and real numbers are all instances.
So if we prove the theorem ``fnUb_add`` at that level of generality,
it will apply in all these instances.
TEXT. -/
section
-- QUOTE:
variable {α : Type _} {R : Type _} [OrderedCancelAddCommMonoid R]

#check @add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)
-- QUOTE.

end

/- TEXT:
You have already seen square brackets like these in
Section :numref:`proving_identities_in_algebraic_structures`,
though we still haven't explained what they mean.
For concreteness, we will stick to the real numbers
for most of our examples,
but it is worth knowing that mathlib contains definitions and theorems
that work at a high level of generality.

.. index:: monotone function

For another example of a hidden universal quantifier,
mathlib defines a predicate ``Monotone``,
which says that a function is nondecreasing in its arguments:
TEXT. -/
-- QUOTE:
example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h
-- QUOTE.

/- TEXT:
The property ``Monotone f`` is defined to be exactly the expression
after the colon. We need to put the ``@`` symbol before ``h`` because
if we don't,
Lean expands the implicit arguments to ``h`` and inserts placeholders.

Proving statements about monotonicity
involves using ``intro`` to introduce two variables,
say, ``a`` and ``b``, and the hypothesis ``a ≤ b``.
To *use* a monotonicity hypothesis,
you can apply it to suitable arguments and hypotheses,
and then apply the resulting expression to the goal.
Or you can apply it to the goal and let Lean help you
work backwards by displaying the remaining hypotheses
as new subgoals.
BOTH: -/
section
variable (f g : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb
-- QUOTE.

/- TEXT:
When a proof is this short, it is often convenient
to give a proof term instead.
To describe a proof that temporarily introduces objects
``a`` and ``b`` and a hypothesis ``aleb``,
Lean uses the notation ``fun a b aleb ↦ ...``.
This is analogous to the way that an expression
like ``fun x ↦ x^2`` describes a function
by temporarily naming an object, ``x``,
and then using it to describe a value.
So the ``intro`` command in the previous proof
corresponds to the lambda abstraction in the next proof term.
The ``apply`` commands then correspond to building
the application of the theorem to its arguments.
TEXT. -/
-- QUOTE:
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)
-- QUOTE.

/- TEXT:
Here is a useful trick: if you start writing
the proof term ``fun a b aleb ↦ _`` using
an underscore where the rest of the
expression should go,
Lean will flag an error,
indicating that it can't guess the value of that expression.
If you check the Lean Goal window in VS Code or
hover over the squiggly error marker,
Lean will show you the goal that the remaining
expression has to solve.

Try proving these, with either tactics or proof terms:
TEXT. -/
-- QUOTE:
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  sorry

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  apply mul_le_mul_of_nonneg_left _ nnc
  apply mf aleb

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  apply mf
  apply mg
  apply aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb)

/- TEXT:
Here are some more examples.
A function :math:`f` from :math:`\Bbb R` to
:math:`\Bbb R` is said to be *even* if
:math:`f(-x) = f(x)` for every :math:`x`,
and *odd* if :math:`f(-x) = -f(x)` for every :math:`x`.
The following example defines these two notions formally
and establishes one fact about them.
You can complete the proofs of the others.
TEXT. -/
-- QUOTE:
-- BOTH:
def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

-- EXAMPLES:
example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = f (-x) * g (-x) := by rw [of, og, neg_mul_neg]


example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef, og, neg_mul_eq_mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  rw [og, ← ef]

-- BOTH:
end

/- TEXT:
.. index:: erw, tactics ; erw

The first proof can be shortened using ``dsimp`` or ``change``
to get rid of the lambda abstraction.
But you can check that the subsequent ``rw`` won't work
unless we get rid of the lambda abstraction explicitly,
because otherwise it cannot find the patterns ``f x`` and ``g x``
in the expression.
Contrary to some other tactics, ``rw`` operates on the syntactic level,
it won't unfold definitions or apply reductions for you
(it has a variant called ``erw`` that tries a little harder in this
direction, but not much harder).

You can find implicit universal quantifiers all over the place,
once you know how to spot them.

Mathlib includes a good library for manipulating sets. Recall that Lean does not
use foundations based on set theory, so here the word set has its mundane meaning
of a collection of mathematical objets of some given type ``α``.
If ``x`` has type ``α`` and ``s`` has type ``Set α``, then ``x ∈ s`` is a proposition
that asserts that ``x`` is an element of ``s``. If ``y`` has some different type ``β`` then the
expression ``y ∈ s`` makes no sense. Here "makes no sense" means "has no type hence Lean does not
accept it as a well-formed statement". This contrasts with Zermelo-Fraenkel set theory for instance
where ``a ∈ b`` is a well-formed statement for every mathematical objects ``a`` and ``b``.
For instance ``sin ∈ cos`` is a well-formed statement in ZF. This defect of set theoretic
foundations is an important motivation for not using it in a proof assistant which is meant to assist
us by detecting meaningless expressions. In Lean ``sin`` has type ``ℝ → ℝ`` and ``cos`` has type
``ℝ → ℝ`` which is not equal to ``Set (ℝ → ℝ)``, even after unfolding definitions, so the statement
``sin ∈ cos`` makes no sense.
One can also use Lean to work on set theory itself. For instance the independence of the continuum
hypothesis from the axioms of Zermelo-Fraenkel has been formalized in Lean. But such a meta-theory
of set theory is completely beyond the scope of this book.

If ``s`` and ``t`` are of type ``Set α``,
then the subset relation ``s ⊆ t`` is defined to mean
``∀ {x : α}, x ∈ s → x ∈ t``.
The variable in the quantifier is marked implicit so that
given ``h : s ⊆ t`` and ``h' : x ∈ s``,
we can write ``h h'`` as justification for ``x ∈ t``.
The following example provides a tactic proof and a proof term
justifying the reflexivity of the subset relation,
and asks you to do the same for transitivity.
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable {α : Type _} (r s t : Set α)

-- EXAMPLES:
example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rsubs ssubt x xr
  apply ssubt
  apply rsubs
  apply xr

theorem Subset.transαα : r ⊆ s → s ⊆ t → r ⊆ t :=
  fun rsubs ssubt x xr ↦ ssubt (rsubs xr)

-- BOTH:
end

/- TEXT:
Just as we defined ``FnUb`` for functions,
we can define ``SetUb s a`` to mean that ``a``
is an upper bound on the set ``s``,
assuming ``s`` is a set of elements of some type that
has an order associated with it.
In the next example, we ask you to prove that
if ``a`` is a bound on ``s`` and ``a ≤ b``,
then ``b`` is a bound on ``s`` as well.
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type _} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

-- EXAMPLES:
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xs
  apply le_trans (h x xs) h'

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  fun x xs ↦ le_trans (h x xs) h'

-- BOTH:
end

/- TEXT:
.. index:: injective function

We close this section with one last important example.
A function :math:`f` is said to be *injective* if for
every :math:`x_1` and :math:`x_2`,
if :math:`f(x_1) = f(x_2)` then :math:`x_1 = x_2`.
Mathlib defines ``Function.Injective f`` with
``x₁`` and ``x₂`` implicit.
The next example shows that, on the real numbers,
any function that adds a constant is injective.
We then ask you to show that multiplication by a nonzero
constant is also injective, using the lemma name in the example as a source
of inspiration. Recall you should use Ctrl-space completion after guessing the beginning of
a lemma name.
TEXT. -/
-- BOTH:
section

-- QUOTE:
open Function

-- EXAMPLES:
example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  apply (mul_right_inj' h).mp h'

/- TEXT:
Finally, show that the composition of two injective functions is injective:
BOTH: -/
-- QUOTE:
variable {α : Type _} {β : Type _} {γ : Type _}
variable {g : β → γ} {f : α → β}

-- EXAMPLES:
example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h
  apply injf
  apply injg
  apply h

-- BOTH:
end
