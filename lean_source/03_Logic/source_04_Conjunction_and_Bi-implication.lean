-- BOTH:
import data.real.basic
import data.nat.prime

/- TEXT:
.. _conjunction_and_biimplication:

Conjunction and Bi-implication
------------------------------

.. index:: split, tactics ; split

You have already seen that the conjunction symbol, ``∧``,
is used to express "and."
The ``split`` tactic allows you to prove a statement of
the form ``A ∧ B``
by proving ``A`` and then proving ``B``.
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  { assumption },
  intro h,
  apply h₁,
  rw h
end
-- QUOTE.

/- TEXT:
.. index:: assumption, tactics ; assumption

In this example, the ``assumption`` tactic
tells Lean to find an assumption that will solve the goal.
Notice that the final ``rw`` finishes the goal by
applying the reflexivity of ``≤``.
The following are alternative ways of carrying out
the previous examples using the anonymous constructor
angle brackets.
The first is a slick proof-term version of the
previous proof,
which drops into tactic mode at the keyword ``by``.
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
⟨h₀, λ h, h₁ (by rw h)⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  have h : x ≠ y,
  { contrapose! h₁,
    rw h₁ },
  exact ⟨h₀, h⟩
end
-- QUOTE.

/- TEXT:
*Using* a conjunction instead of proving one involves unpacking the proofs of the
two parts.
You can uses the ``cases`` tactic for that,
as well as ``rcases``, ``rintros``, or a pattern-matching lambda,
all in a manner similar to the way they are used with
the existential quantifier.
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  cases h with h₀ h₁,
  contrapose! h₁,
  exact le_antisymm h₀ h₁
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩ h',
  exact h₁ (le_antisymm h₀ h')
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
λ ⟨h₀, h₁⟩ h', h₁ (le_antisymm h₀ h')
-- QUOTE.

/- TEXT:
In contrast to using an existential quantifier,
you can also extract proofs of the two components
of a hypothesis ``h : A ∧ B``
by writing ``h.left`` and ``h.right``,
or, equivalently, ``h.1`` and ``h.2``.
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  intro h',
  apply h.right,
  exact le_antisymm h.left h'
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
λ h', h.right (le_antisymm h.left h')
-- QUOTE.

/- TEXT:
Try using these techniques to come up with various ways of proving of the following:
TEXT. -/
-- QUOTE:
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
sorry
-- QUOTE.

-- SOLUTIONS:
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
begin
  cases h with h0 h1,
  split,
  { exact h0 },
  intro h2,
  apply h1,
  apply nat.dvd_antisymm h0 h2,
end

/- TEXT:
You can nest uses of ``∃`` and ``∧``
with anonymous constructors, ``rintros``, and ``rcases``.
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
⟨5/2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
begin
  rintros ⟨z, xltz, zlty⟩,
  exact lt_trans xltz zlty
end

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
λ ⟨z, xltz, zlty⟩, lt_trans xltz zlty
-- QUOTE.

/- TEXT:
You can also use the ``use`` tactic:
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
begin
  use 5 / 2,
  split; norm_num
end

example : ∃ m n : ℕ,
  4 < m ∧ m < n ∧ n < 10 ∧ nat.prime m ∧ nat.prime n :=
begin
  use [5, 7],
  norm_num
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩,
  use [h₀, λ h', h₁ (le_antisymm h₀ h')]
end
-- QUOTE.

/- TEXT:
In the first example, the semicolon after the ``split`` command tells Lean to use the
``norm_num`` tactic on both of the goals that result.

In Lean, ``A ↔ B`` is *not* defined to be ``(A → B) ∧ (B → A)``,
but it could have been,
and it behaves roughly the same way.
You have already seen that you can write ``h.mp`` and ``h.mpr``
or ``h.1`` and ``h.2`` for the two directions of ``h : A ↔ B``.
You can also use ``cases`` and friends.
To prove an if-and-only-if statement,
you can uses ``split`` or angle brackets,
just as you would if you were proving a conjunction.
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
begin
  split,
  { contrapose!,
    rintro rfl,
    reflexivity },
  contrapose!,
  exact le_antisymm h
end

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
⟨λ h₀ h₁, h₀ (by rw h₁), λ h₀ h₁, h₀ (le_antisymm h h₁)⟩
-- QUOTE.

/- TEXT:
The last proof term is inscrutable. Remember that you can
use underscores while writing an expression like that to
see what Lean expects.

Try out the various techniques and gadgets you have just seen
in order to prove the following:
TEXT. -/
-- QUOTE:
example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
sorry
-- QUOTE.

-- SOLUTIONS:
example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
begin
  split,
  { rintros ⟨h0, h1⟩,
    split,
    { exact h0 },
    intro h2,
    apply h1,
    rw h2 },
  rintros ⟨h0, h1⟩,
  split,
  { exact h0 },
  intro h2,
  apply h1,
  apply le_antisymm h0 h2
end

/- TEXT:
For a more interesting exercise, show that for any
two real numbers ``x`` and ``y``,
``x^2 + y^2 = 0`` if and only if ``x = 0`` and ``y = 0``.
We suggest proving an auxiliary lemma using
``linarith``, ``pow_two_nonneg``, and ``pow_eq_zero``.
TEXT. -/
-- QUOTE:
theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { sorry },
  exact pow_eq_zero h'
end

example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
sorry
-- QUOTE.

-- SOLUTIONS:
theorem auxαα {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { linarith [pow_two_nonneg x, pow_two_nonneg y] },
  exact pow_eq_zero h'
end

example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
begin
  split,
  { intro h,
    split,
    { exact aux h },
    rw add_comm at h,
    exact aux h },
  rintros ⟨rfl, rfl⟩,
  norm_num
end

/- TEXT:
In Lean, bi-implication leads a double-life.
You can treat it like a conjunction and use its two
parts separately.
But Lean also knows that it is a reflexive, symmetric,
and transitive relation between propositions,
and you can also use it with ``calc`` and ``rw``.
It is often convenient to rewrite a statement to
an equivalent one.
In the next example, we use ``abs_lt`` to
replace an expression of the form ``abs x < y``
by the equivalent expression ``- y < x ∧ x < y``,
and in the one after that we use ``dvd_gcd_iff``
to replace an expression of the form ``m ∣ gcd n k`` by the equivalent expression ``m ∣ n ∧ m ∣ k``.
TEXT. -/
section
open nat

-- QUOTE:
example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split; linarith
end

example : 3 ∣ gcd 6 15 :=
begin
  rw dvd_gcd_iff,
  split; norm_num
end
-- QUOTE.

end

/- TEXT:
See if you can use ``rw`` with the theorem below
to provide a short proof that negation is not a
nondecreasing function. (Note that ``push_neg`` won't
unfold definitions for you, so the ``rw monotone`` in
the proof of the theorem is needed.)
BOTH: -/
-- QUOTE:
theorem not_monotone_iff {f : ℝ → ℝ}:
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw monotone, push_neg }

-- EXAMPLES:
example : ¬ monotone (λ x : ℝ, -x) :=
sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬ monotone (λ x : ℝ, -x) :=
begin
  rw not_monotone_iff,
  use [0, 1],
  norm_num
end

/- TEXT:
The remaining exercises in this section are designed
to give you some more practice with conjunction and
bi-implication. Remember that a *partial order* is a
binary relation that is transitive, reflexive, and
antisymmetric.
An even weaker notion sometimes arises:
a *preorder* is just a reflexive, transitive relation.
For any pre-order ``≤``,
Lean axiomatizes the associated strict pre-order by
``a < b ↔ a ≤ b ∧ ¬ b ≤ a``.
Show that if ``≤`` is a partial order,
then ``a < b`` is equivalent to ``a ≤ b ∧ a ≠ b``:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {α : Type*} [partial_order α]
variables a b : α

-- EXAMPLES:
example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  sorry
end
-- QUOTE.

-- SOLUTIONS:
example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  split,
  { rintros ⟨h0, h1⟩,
    split,
    { exact h0 },
    intro h2,
    apply h1,
    rw h2 },
  rintros ⟨h0, h1⟩,
  split,
  { exact h0 },
  intro h2,
  apply h1,
  apply le_antisymm h0 h2
end

-- BOTH:
end

/- TEXT:
.. index:: simp, tactics ; simp

Beyond logical operations, you should not need
anything more than ``le_refl`` and ``le_antisymm``.
Then show that even in the case where ``≤``
is only assumed to be a preorder,
we can prove that the strict order is irreflexive
and transitive.
You do not need anything more than ``le_refl`` and ``le_trans``.
In the second example,
for convenience, we use the simplifier rather than ``rw``
to express ``<`` in terms of ``≤`` and ``¬``.
We will come back to the simplifier later,
but here we are only relying on the fact that it will
use the indicated lemma repeatedly, even if it needs
to be instantiated to different values.
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {α : Type*} [preorder α]
variables a b c : α

-- EXAMPLES:
example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  sorry
end

example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  sorry
end
-- QUOTE.

-- SOLUTIONS:
example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  rintros ⟨h0, h1⟩,
  exact h1 h0
end

example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  rintros ⟨h0, h1⟩ ⟨h2, h3⟩,
  split,
  { apply le_trans h0 h2 },
  intro h4,
  apply h1,
  apply le_trans h2 h4
end

-- BOTH:
end
