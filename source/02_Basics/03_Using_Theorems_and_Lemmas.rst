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

.. code-block:: lean

  #check (le_refl : ∀ a : ℝ, a ≤ a)
  #check (le_trans : a ≤ b → b ≤ c → a ≤ c)

As we explain in more detail in  :numref:`implication_and_the_universal_quantifier`,
the implicit parentheses in the statement of ``le_trans``
associate to the right, so it should be interpreted as ``a ≤ b → (b ≤ c → a ≤ c)``.
The library designers have set the arguments to ``le_trans`` implicit,
so that Lean will *not* let you provide them explicitly (unless you
really insist, as we will discuss later).
Rather, it expects to infer them from the context in which they are used.
For example, when hypotheses ``h : a ≤ b`` and  ``h' : b ≤ c``
are in the context,
all the following work:

.. code-block:: lean

  variables (h : a ≤ b) (h' : b ≤ c)
  
  #check (le_refl : ∀ a : real, a ≤ a)
  #check (le_refl a : a ≤ a)
  #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
  #check (le_trans h : b ≤ c → a ≤ c)
  #check (le_trans h h' : a ≤ c)

.. index:: apply, tactics ; apply

The ``apply`` tactic takes a proof of a general statement or implication,
tries to match the conclusion with the current goal,
and leaves the hypotheses, if any, as new goals.
If the given proof matches the goal exactly
(modulo *definitional* equality),
you can use the ``exact`` tactic instead of ``apply``.
So, all of these work:

.. code-block:: lean

  example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  begin
    apply le_trans,
    { apply h₀ },
    apply h₁
  end
  
  example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  begin
    apply le_trans h₀,
    apply h₁
  end
  
  example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  by exact le_trans h₀ h₁
  
  example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁
  
  example (x : ℝ) : x ≤ x :=
  by apply le_refl
  
  example (x : ℝ) : x ≤ x :=
  by exact le_refl x
  
  example (x : ℝ) : x ≤ x :=
  le_refl x

In the first example, applying ``le_trans``
creates two goals,
and we use the curly braces to enclose the proof
of the first one.
In the fourth example and in the last example,
we avoid going into tactic mode entirely:
``le_trans h₀ h₁`` and ``le_refl x`` are the proof terms we need.

Here are a few more library theorems:

.. code-block:: lean

  #check (le_refl  : ∀ a, a ≤ a)
  #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
  #check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
  #check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
  #check (lt_trans : a < b → b < c → a < c)

Use them together with ``apply`` and ``exact`` to prove the following:

.. code-block:: lean

  example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
      (h₃ : d < e) :
    a < e :=
  sorry

.. index:: linarith, tactics ; linarith

In fact, Lean has a tactic that does this sort of thing automatically:

.. code-block:: lean

  example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
      (h₃ : d < e) :
    a < e :=
  by linarith

The ``linarith`` tactic is designed to handle *linear arithmetic*.

.. code-block:: lean

  example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) :
    d + a ≤ 5 * b :=
  by linarith

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

.. code-block:: lean

  example (h : 1 ≤ a) (h' : b ≤ c) :
    2 + a + exp b ≤ 3 * a + exp c :=
  by linarith [exp_le_exp.mpr h']

.. index:: exponential, logarithm

Here are some more theorems in the library that can be used to establish
inequalities on the real numbers.

.. code-block:: lean

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

Some of the theorems, ``exp_le_exp``, ``exp_lt_exp``, and ``log_le_log``
use a *bi-implication*, which represents the
phrase "if and only if."
(You can type it in VS Code with ``\lr`` of ``\iff``).
We will discuss this connective in greater detail in the next chapter.
Such a theorem can be used with ``rw`` to rewrite a goal to
an equivalent one:

.. code-block:: lean

  example (h : a ≤ b) : exp a ≤ exp b :=
  begin
    rw exp_le_exp,
    exact h
  end

In this section, however, we will use the fact that if ``h : A ↔ B``
is such an equivalence,
then ``h.mp`` establishes the forward direction, ``A → B``,
and ``h.mpr`` establishes the reverse direction, ``B → A``.
Here, ``mp`` stands for "modus ponens" and
``mpr`` stands for "modus ponens reverse."
You can also use ``h.1`` and ``h.2`` for ``h.mp`` and ``h.mpr``,
respectively, if you prefer.
Thus the following proof works:

.. code-block:: lean

  example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e :=
  begin
    apply add_lt_add_of_lt_of_le,
    { apply add_lt_add_of_le_of_lt h₀,
      apply exp_lt_exp.mpr h₁ },
    apply le_refl
  end

The first line, ``apply add_lt_add_of_lt_of_le``,
creates two goals,
and once again we use the curly brackets to separate the
proof of the first from the proof of the second.

.. index:: norm_num, tactics ; norm_num

Try the following examples on your own.
The example in the middle shows you that the ``norm_num``
tactic can be used to solve concrete numeric goals.

.. code-block:: lean

  example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
  begin
    sorry
  end
  
  example : (0 : ℝ) < 1 :=
  by norm_num
  
  example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
  begin
    have h₀ : 0 < 1 + exp a,
    { sorry },
    have h₁ : 0 < 1 + exp b,
    { sorry },
    apply (log_le_log h₀ h₁).mpr,
    sorry
  end

From these examples, it should be clear that being able to
find the library theorems you need constitutes an important
part of formalization.
There are a number of strategies you can use:

* You can browse mathlib in its
  `GitHub repository <https://github.com/leanprover-community/mathlib>`_.

* You can use the API documentation on the mathlib
  `web pages <https://leanprover-community.github.io/mathlib_docs/>`_.

* You can rely on mathlib naming conventions and tab completion in
  the editor to guess a theorem name.
  In Lean, a theorem named ``A_of_B_of_C`` establishes
  something of the form ``A`` from hypotheses of the form ``B`` and ``C``,
  where ``A``, ``B``, and ``C``
  approximate the way we might read the goals out loud.
  So a theorem establishing something like ``x + y ≤ ...`` will probably
  start with ``add_le``.
  Typing ``add_le`` and hitting tab will give you some helpful choices.

* If you right-click on an existing theorem name in VS Code,
  the editor will show a menu with the option to
  jump to the file where the theorem is defined,
  and you can find similar theorems nearby.

* You can use the ``library_search`` tactic,
  which tries to find the relevant theorem in the library.

.. code-block:: lean

      example : 0 ≤ a^2 :=
      begin
        -- library_search,
        exact pow_two_nonneg a
      end

To try out ``library_search`` in this example,
delete the ``exact`` command and uncomment the previous line.
If you replace ``library_search`` with ``suggest``,
you'll see a long list of suggestions.
In this case, the suggestions are not helpful, but in other cases
it does better.
Using these tricks,
see if you can find what you need to do the
next example:

.. code-block:: lean

  example (h : a ≤ b) : c - exp b ≤ c - exp a :=
    sorry

Using the same tricks, confirm that ``linarith`` instead of ``library_search``
can also finish the job.

Here is another example of an inequality:

.. code-block:: lean

  example : 2*a*b ≤ a^2 + b^2 :=
  begin
    have h : 0 ≤ a^2 - 2*a*b + b^2,
    calc
      a^2 - 2*a*b + b^2 = (a - b)^2     : by ring
      ... ≥ 0                           : by apply pow_two_nonneg,
    calc
      2*a*b
          = 2*a*b + 0                   : by ring
      ... ≤ 2*a*b + (a^2 - 2*a*b + b^2) : add_le_add (le_refl _) h
      ... = a^2 + b^2                   : by ring
  end

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

.. code-block:: lean

  example : 2*a*b ≤ a^2 + b^2 :=
  begin
    have h : 0 ≤ a^2 - 2*a*b + b^2,
    calc
      a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
      ... ≥ 0                       : by apply pow_two_nonneg,
    linarith
  end

How nice! We challenge you to use these ideas to prove the
following theorem. You can use the theorem ``abs_le'.mpr``.

.. code-block:: lean

  example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
  sorry
  
  #check abs_le'.mpr

If you managed to solve this, congratulations!
You are well on your way to becoming a master formalizer.
