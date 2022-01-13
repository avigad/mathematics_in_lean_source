.. more_on_order_and_divisibility:

More on Order and Divisibility
------------------------------

.. index:: min, max

The ``min`` function on the real numbers is uniquely characterized
by the following three facts:

.. code-block:: lean

  #check (min_le_left a b : min a b ≤ a)
  #check (min_le_right a b : min a b ≤ b)
  #check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

Can you guess the names of the theorems that characterize
``max`` in a similar way?

Notice that we have to apply ``min`` to a pair of arguments ``a`` and ``b``
by writing ``min a b`` rather than ``min (a, b)``.
Formally, ``min`` is a function of type ``ℝ → ℝ → ℝ``.
When we write a type like this with multiple arrows,
the convention is that the implicit parentheses associate
to the right, so the type is interpreted as ``ℝ → (ℝ → ℝ)``.
The net effect is that if ``a`` and ``b`` have type ``ℝ``
then ``min a`` has type ``ℝ → ℝ`` and
``min a b`` has type ``ℝ``, so ``min`` acts like a function
of two arguments, as we expect. Handling multiple
arguments in this way is known as *currying*,
after the logician Haskell Curry.

The order of operations in Lean can also take some getting used to.
Function application binds tighter than infix operations, so the
expression ``min a b + c`` is interpreted as ``(min a b) + c``.
With time, these conventions will become second nature.

Using the theorem ``le_antisymm``, we can show that two
real numbers are equal if each is less than or equal to the other.
Using this and the facts above,
we can show that ``min`` is commutative:

.. code-block:: lean

  example : min a b = min b a :=
  begin
    apply le_antisymm,
    { show min a b ≤ min b a,
      apply le_min,
      { apply min_le_right },
      apply min_le_left },
    { show min b a ≤ min a b,
      apply le_min,
      { apply min_le_right },
      apply min_le_left }
  end

.. index:: show, tactics ; show

Here we have used curly brackets to separate proofs of
different goals.
Our usage is inconsistent:
at the outer level,
we use curly brackets and indentation for both goals,
whereas for the nested proofs,
we use curly brackets only until a single goal remains.
Both conventions are reasonable and useful.
We also use the ``show`` tactic to structure
the proof
and indicate what is being proved in each block.
The proof still works without the ``show`` commands,
but using them makes the proof easier to read and maintain.

It may bother you that the the proof is repetitive.
To foreshadow skills you will learn later on,
we note that one way to avoid the repetition
is to state a local lemma and then use it:

.. code-block:: lean

  example : min a b = min b a :=
  begin
    have h : ∀ x y, min x y ≤ min y x,
    { intros x y,
      apply le_min,
      apply min_le_right,
      apply min_le_left },
    apply le_antisymm, apply h, apply h
  end

We will say more about the universal quantifier in
:numref:`implication_and_the_universal_quantifier`,
but suffice it to say here that the hypothesis
``h`` says that the desired inequality holds for
any ``x`` and ``y``,
and the ``intros`` tactic introduces an arbitrary
``x`` and ``y`` to establish the conclusion.
The first ``apply`` after ``le_antisymm`` implicitly
uses ``h a b``, whereas the second one uses ``h b a``.

.. index:: repeat, tactics ; repeat

Another solution is to use the ``repeat`` tactic,
which applies a tactic (or a block) as many times
as it can.

.. code-block:: lean

  example : min a b = min b a :=
  begin
    apply le_antisymm,
    repeat {
      apply le_min,
      apply min_le_right,
      apply min_le_left }
  end

In any case,
whether or not you use these tricks,
we encourage you to prove the following:

.. code-block:: lean

  example : max a b = max b a :=
  sorry
  
  example : min (min a b) c = min a (min b c) :=
  sorry

Of course, you are welcome to prove the associativity of ``max`` as well.

It is an interesting fact that ``min`` distributes over ``max``
the way that multiplication distributes over addition,
and vice-versa.
In other words, on the real numbers, we have the identity
``min a (max b c) ≤ max (min a b) (min a c)``
as well as the corresponding version with ``max`` and ``min``
switched.
But in the next section we will see that this does *not* follow
from the transitivity and reflexivity of ``≤`` and
the characterizing properties of ``min`` and ``max`` enumerated above.
We need to use the fact that ``≤`` on the real numbers is a *total order*,
which is to say,
it satisfies ``∀ x y, x ≤ y ∨ y ≤ x``.
Here the disjunction symbol, ``∨``, represents "or".
In the first case, we have ``min x y = x``,
and in the second case, we have ``min x y = y``.
We will learn how to reason by cases in :numref:`disjunction`,
but for now we will stick to examples that don't require the case split.

Here is one such example:

.. code-block:: lean

  lemma aux : min a b + c ≤ min (a + c) (b + c) :=
  sorry
  
  example : min a b + c = min (a + c) (b + c) :=
  sorry

It is clear that ``aux`` provides one of the two inequalities
needed to prove the equality,
but applying it to suitable values yields the other direction
as well.
As a hint, you can use the theorem ``add_neg_cancel_right``
and the ``linarith`` tactic.

.. index:: absolute value

Lean's naming convention is made manifest
in the library's name for the triangle inequality:

.. code-block:: lean

  #check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)

Use it to prove the following variant:

.. code-block:: lean

  example : abs a - abs b ≤ abs (a - b) :=
  sorry

See if you can do this in three lines or less.
You can use the theorem ``sub_add_cancel``.

.. index:: divisibility

Another important relation that we will make use of
in the sections to come is the divisibility relation
on the natural numbers, ``x ∣ y``.
Be careful: the divisibility symbol is *not* the
ordinary bar on your keyboard.
Rather, it is a unicode character obtained by
typing ``\|`` in VS Code.
By convention, mathlib uses ``dvd``
to refer to it in theorem names.

.. code-block:: lean

  example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁
  
  example : x ∣ y * x * z :=
  begin
    apply dvd_mul_of_dvd_left,
    apply dvd_mul_left
  end
  
  example : x ∣ x^2 :=
  by apply dvd_mul_right

In the last example, the exponent is a natural
number, and applying ``dvd_mul_right``
forces Lean to expand the definition of ``x^2`` to
``x^1 * x``.
See if you can guess the names of the theorems
you need to prove the following:

.. code-block:: lean

  example (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 :=
  sorry

.. index:: gcd, lcm

With respect to divisibility, the *greatest common divisor*,
``gcd``, and least common multiple, ``lcm``,
are analogous to ``min`` and ``max``.
Since every number divides ``0``,
``0`` is really the greatest element with respect to divisibility:

.. code-block:: lean

  variables m n : ℕ
  open nat
  
  #check (gcd_zero_right n : gcd n 0 = n)
  #check (gcd_zero_left n  : gcd 0 n = n)
  #check (lcm_zero_right n : lcm n 0 = 0)
  #check (lcm_zero_left n  : lcm 0 n = 0)

The functions ``gcd`` and ``lcm`` for natural numbers are in the
``nat`` namespace,
which means that the full identifiers are ``nat.gcd`` and ``nat.lcm``.
Similarly, the names of the theorems listed are prefixed by ``nat``.
The command ``open nat`` opens the namespace,
allowing us to use the shorter names.

See if you can guess the names of the theorems you will need to
prove the following:

.. code-block:: lean

  example : gcd m n = gcd n m :=
  sorry

Hint: you can use ``dvd_antisymm``.
