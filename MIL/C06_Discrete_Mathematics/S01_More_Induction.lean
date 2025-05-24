import MIL.Common
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Nat.GCD.Basic

namespace more_induction

/- TEXT:

.. _more_induction:

More Induction
--------------

In :numref:`section_induction_and_recursion`, we saw how to define the factorial function by
recursion on the natural numbers.
EXAMPLES: -/
-- QUOTE:
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n
-- QUOTE.

/- TEXT:
We also saw how to prove theorems using the ``induction'`` tactic.
EXAMPLES: -/
-- QUOTE:
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:
The ``induction`` tactic (without the prime tick mark) allows for more structured syntax.
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : 0 < fac n := by
  induction n
  case zero =>
    rw [fac]
    exact zero_lt_one
  case succ n ih =>
    rw [fac]
    exact mul_pos n.succ_pos ih

example (n : ℕ) : 0 < fac n := by
  induction n with
  | zero =>
    rw [fac]
    exact zero_lt_one
  | succ n ih =>
    rw [fac]
    exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:
The names of the cases, ``zero`` and ``succ``, are taken from the definition of the induction
principle.
Notice that the ``succ`` case allows you to choose whatever names you want for the
induction variable and the inductive hypothesis, here ``n`` and ``ih``.
You can even prove a theorem with the same notation used to define a recursive function.
EXAMPLES: -/
-- QUOTE:
theorem fac_pos' : ∀ n, 0 < fac n
  | 0 => by
    rw [fac]
    exact zero_lt_one
  | n + 1 => by
    rw [fac]
    exact mul_pos n.succ_pos (fac_pos' n)
-- QUOTE.

/- TEXT:
Notice also the absence of the ``:=``, the ``∀ n`` after the colon, the ``by`` keyword in each case,
and the inductive appeal to ``fac_pos' n``.
It is as though the theorem is a recursive function of ``n`` and in the inductive step we make
a recursive call.

This style of definition is remarkably flexible.
Lean's designers have built in elaborate means of defining recursive functions, and these
extend to doing proofs by induction.
For example, we can define the Fibonacci function with multiple base cases.
BOTH: -/
-- QUOTE:
@[simp] def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
-- QUOTE.

/- TEXT:
The ``@[simp]`` annotation means that the simplifier will use the defining equations.
You can also apply them by writing ``rw [fib]``.
Below it will be helpful to give a name to the ``n + 2`` case.
BOTH: -/
-- QUOTE:
theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl

-- EXAMPLES:
example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by rw [fib]
-- QUOTE.

/- TEXT:
Using Lean's notation for recursive functions, you can carry out proofs by induction on the
natural numbers that mirror the recursive definition of ``fib``.
The following example provides an explicit formula for the nth Fibonacci number in terms of
the golden mean, ``φ``, and its conjugate, ``φ'``.
We have to tell Lean that we don't expect our definitions to generate code because the
arithmetic operations on the real numbers are not computable.
EXAMPLES: -/
-- QUOTE:
noncomputable section

def phi  : ℝ := (1 + √5) / 2
def phi' : ℝ := (1 - √5) / 2

theorem phi_sq : phi^2 = phi + 1 := by
  field_simp [phi, add_sq]; ring

theorem phi'_sq : phi'^2 = phi' + 1 := by
  field_simp [phi', sub_sq]; ring

theorem fib_eq : ∀ n, fib n = (phi^n - phi'^n) / √5
  | 0 => by simp
  | 1 => by field_simp [phi, phi']
  | n+2 => by
    field_simp [fib_eq, pow_add, phi_sq, phi'_sq]
    ring

end
-- QUOTE.

/- TEXT:
Induction proofs involving the Fibonacci function do not have to be of that form.
Below we reproduce the ``Mathlib`` proof that consecutive Fibonacci numbers are coprime.
EXAMPLES: -/
-- QUOTE:
theorem fib_coprime_fib_succ (n : ℕ) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [fib, Nat.coprime_add_self_right]
    exact ih.symm
-- QUOTE.

/- TEXT:
Using Lean's computational interpretation, we can evaluate the Fibonacci numbers.
EXAMPLES: -/
-- QUOTE:
#eval fib 6
#eval List.range 20 |>.map fib
-- QUOTE.

/- TEXT:
The straightforward implementation of ``fib`` is computationally inefficient. In fact, it runs
in time exponential in its argument. (You should think about why.)
In Lean, we can implement the following tail-recursive version, whose running time is linear
in ``n``, and prove that it computes the same function.
EXAMPLES: -/
-- QUOTE:
def fib' (n : Nat) : Nat :=
  aux n 0 1
where aux
  | 0, x, _ => x
  | n+1, x, y => aux n y (x + y)

theorem fib'.aux_eq (m n : ℕ) : fib'.aux n (fib m) (fib (m + 1)) = fib (n + m) := by
  induction n generalizing m with
  | zero => simp [fib'.aux]
  | succ n ih => rw [fib'.aux, ←fib_add_two, ih, add_assoc, add_comm 1]

theorem fib'_eq_fib : fib' = fib := by
  ext n
  erw [fib', fib'.aux_eq 0 n]; rfl

#eval fib' 10000
-- QUOTE.

/- TEXT:
Notice the ``generalizing`` keyword in the proof of ``fib'.aux_eq``.
It serves to insert a ``∀ m`` in front of the inductive hypothesis, so that in the induction
step, ``m`` can take a different value.
You can step through the proof and check that in this case, ``m`` needs to be instantiated
to ``m + 1``.
As usual, you can hover over the ``induction`` keyword to read the documentation.

Notice also the use of ``erw`` (for "extended rewrite") instead of ``rw``.
This is used because to rewrite the goal ``fib'.aux_eq``, ``fib 0`` and ``fib 1``
have to be reduced to ``0`` and ``1``, respectively.
The tactic ``erw`` is simply more aggressive than ``rw`` in unfolding definitions to
match parameters.
This isn't always a good idea; it can waste a lot of time in some cases, so use ``erw``
sparingly.

Here is another example of the ``generalizing`` keyword in use, in the proof of another
identity that is found in ``Mathlib``.
An informal proof of the identity can be found `here <https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers>`_.
We provide two variants of the formal proof.
BOTH: -/
-- QUOTE:
theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib_add_two, Nat.succ_eq_add_one, ih]
    ring

-- EXAMPLES:
theorem fib_add' : ∀ m n, fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)
  | _, 0     => by simp
  | m, n + 1 => by
    have := fib_add' (m + 1) n
    rw [add_assoc m 1 n, add_comm 1 n] at this
    simp only [fib_add_two, Nat.succ_eq_add_one, this]
    ring
-- QUOTE.

/- TEXT:
As an exercise, use ``fib_add`` to prove the following.
EXAMPLES: -/
-- QUOTE:
example (n : ℕ): (fib n)^2 + (fib (n + 1))^2 = fib (2 * n + 1) := by sorry
-- QUOTE.
/- SOLUTIONS:
example (n : ℕ): (fib n)^2 + (fib (n + 1))^2 = fib (2 * n + 1) := by
  rw [two_mul, fib_add, pow_two, pow_two]
BOTH: -/

/- TEXT:
Lean's mechanisms for defining recursive functions are flexible enough to allow arbitrary
recursive calls, as long the complexity of the arguments decrease according to some
well-founded measure.
In the next example, we show that every natural number ``n ≠ 1`` has a prime divisor,
using the fact that if ``n`` is itself nonzero and not prime, it has a smaller divisor.
(You can check that Mathlib has a theorem of the same name in the ``Nat`` namespace,
though it has a different proof than the one we give here.)
EXAMPLES: -/
-- QUOTE:
#check (@Nat.not_prime_iff_exists_dvd_lt :
  ∀ {n : ℕ}, 2 ≤ n → (¬Nat.Prime n ↔ ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n))

theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
  | 0 => by simpa using Exists.intro 2 Nat.prime_two
  | 1 => by simp [Nat.not_prime_one]
  | n + 2 => by
    have hn : n+2 ≠ 1 := by omega
    simp only [Ne, not_false_iff, true_iff, hn]
    by_cases h : Nat.Prime (n + 2)
    · use n+2, h
    · have : 2 ≤ n + 2 := by omega
      rw [Nat.not_prime_iff_exists_dvd_lt this] at h
      rcases h with ⟨m, mdvdn, mge2, -⟩
      have : m ≠ 1 := by omega
      rw [ne_one_iff_exists_prime_dvd] at this
      rcases this with ⟨p, primep, pdvdm⟩
      use p, primep
      exact pdvdm.trans mdvdn
-- QUOTE.

/- TEXT:
The line ``rw [ne_one_iff_exists_prime_dvd] at this`` is like a magic trick: we are using
the very theorem we are proving in its own proof.
What makes it work is that the inductive call is instantiated at ``m``,
the current case is ``n + 2``, and the context has ``m < n + 2``.
Lean can find the hypothesis and use it to show that the induction is well-founded.
Lean is pretty good at figuring out what is decreasing; in this case, the choice of
``n`` in the statement of the theorem and the less-than relation is obvious.
In more complicated cases, Lean provides mechanisms to provide this information
explicitly. See the section on `well-founded recursion <https://lean-lang.org/doc/reference/latest//Definitions/Recursive-Definitions/#well-founded-recursion>`_ in the Lean Reference Manual.

Sometimes, in a proof, you need to split on cases depending on whether a natural number ``n``
is zero or a successor, without requiring an inductive hypothesis in the successor case.
For that, you can use the ``cases`` and ``rcases`` tactics.
EXAMPLES: -/
-- QUOTE:
theorem zero_lt_of_mul_eq_one (m n : ℕ) : n*m = 1 → 0 < n ∧ 0 < m := by
  cases n <;> cases m <;> simp

example (m n : ℕ) : n*m = 1 → 0 < n ∧ 0 < m := by
  rcases m with (_ | m); simp
  rcases n with (_ | n) <;> simp
-- QUOTE.

/- TEXT:
This is a useful trick.
Often you have a theorem about a natural number ``n`` for which the zero case is easy.
If you case on ``n`` and take care of the zero case quickly, you are left with the original
goal with ``n`` replaced by ``n + 1``.
EXAMPLES: -/
