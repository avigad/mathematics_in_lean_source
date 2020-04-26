.. _number_theory:

Number Theory
=============

Ideas:

* Some basic induction: recursive definitions of addition, multiplication, factorial, etc., à la the natural numbers game.

* Identities with fibonacci numbers, Catalan numbers, binomial coefficients

* Irrationality of sqrt 2 and generalizations

* A proof that there are infinitely many primes.

* Sums of four squares

* Prime numbers and congruences

We should also work in explanations of ``norm_num`` and ``dec_trivial``.
Here are some examples:

.. code-block:: lean

    import data.nat.parity tactic
    open nat

    example : ¬ even 5 := by norm_num

    example : prime 7 := by norm_num

    example (n : ℕ) (pn : prime n) (oddn : ¬ even n) : n > 2 :=
    begin
      by_contradiction h, simp at h,
      interval_cases n; revert pn oddn h; norm_num
    end

    example (n : ℕ) (pn : prime n) (oddn : ¬ even n) : n > 2 :=
    have ∀ n ≤ 2, prime n → ¬ even n → false, from dec_trivial,
    lt_of_not_ge (λ h', this _ h' pn oddn)

We should also find some excuse to talk about the various
number systems, nat, int, rat, real, and complex,
and ways of dealing with casts between them.

Maybe we can do this in the context of subtraction hell and moving
between nat and int.
