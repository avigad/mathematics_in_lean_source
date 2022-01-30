import data.nat.gcd
import data.nat.prime
import tactic
import tactic.linarith

--import data.real.irrational

import ring_theory.int.basic
import data.real.sqrt
#check multiplicity

/- TEXT:

_section_irrational_roots:

Irrational Roots
----------------

There are more general statements in data.real.irrational.lean.

-/

example : nat.prime 17 :=
by norm_num

example : nat.prime 2 := nat.prime_two
example : nat.prime 3 := nat.prime_three

#check @nat.prime.dvd_mul
#check nat.prime.dvd_mul nat.prime_two
#check nat.prime_two.dvd_mul

lemma even_of_even_sqr {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
begin
  rw [pow_two, nat.prime_two.dvd_mul] at h,
  cases h; assumption
end

example {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
nat.prime.dvd_of_dvd_pow nat.prime_two h

#check @mul_left_cancel''

/-
Remember that you can use tab completion, library search,
ctrl-click, mathlib community pages.
Zulip.
-/
example (a b c : nat) (h : a * b = a * c) (h : a ≠ 0) :
  b = c :=
begin
  library_search
end

theorem foo {m n : ℕ} (coprime_mn : nat.coprime m n) : m^2 ≠ 2 * n^2 :=
begin
  intro sqr_eq,
  have : 2 ∣ m,
  { apply even_of_even_sqr,
    rw sqr_eq,
    apply dvd_mul_right },
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,
  have : 2 * (2 * k^2) = 2 * n^2,
  { rw [←sqr_eq, meq], ring },
  have : 2 * k^2 = n^2 := (mul_right_inj' (by norm_num)).mp this,
  have : 2 ∣ n,
  { apply even_of_even_sqr,
    rw ←this,
    apply dvd_mul_right },
  have : 2 ∣ nat.gcd m n,
  { apply nat.dvd_gcd; assumption },
  have : 2 ∣ 1,
  { convert this, symmetry, exact coprime_mn },
  norm_num at this
end

theorem bar {m n p : ℕ} (coprime_mn : nat.coprime m n) (prime_p : nat.prime p) :
  m^2 ≠ p * n^2 :=
begin
  intro sqr_eq,
  have : p ∣ m,
  { apply prime_p.dvd_of_dvd_pow,
    rw sqr_eq,
    apply dvd_mul_right },
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,
  have : p * (p * k^2) = p * n^2,
  { rw [←sqr_eq, meq], ring },
  have : p * k^2 = n^2,
  { apply (mul_right_inj' _).mp this,
    exact prime_p.ne_zero },
  have : p ∣ n,
  { apply prime_p.dvd_of_dvd_pow,
    rw ←this,
    apply dvd_mul_right },
  have : p ∣ nat.gcd m n,
  { apply nat.dvd_gcd; assumption },
  have : p ∣ 1,
  { convert this, symmetry, exact coprime_mn },
  have : 2 ≤ 1,
  { apply prime_p.two_le.trans,
    exact nat.le_of_dvd zero_lt_one this },
  norm_num at this
end

#check nat.factors
#check multiplicity

example (m n : nat) (h : gcd m n = 1) : 0 < m :=
begin
  library_search
end

theorem ne_zero_of_coprime {m n : ℕ} (h : nat.coprime m n) (h' : n ≠ 1): m ≠ 0 :=
begin
  contrapose! h',
  rwa [nat.coprime, h', nat.gcd_zero_left] at h,
end

theorem baz {m n p : ℕ} (coprime_mn : nat.coprime m n) (prime_p : nat.prime p) :
  m^2 ≠ p * n^2 :=
begin
  intro sqr_eq,
  -- have mnez : m ≠ 0,
  -- { contrapose! coprime_mn with mz,
  --   simp [mz] at sqr_eq,
  --   have : n = 0,
  --   { exact or.resolve_left sqr_eq prime_p.ne_zero },
  --   rw [mz, this, nat.gcd_zero_left],
  --   exact zero_ne_one },
  have nsqr_nez : n^2 ≠ 0,
  { contrapose! coprime_mn with nsqrz,
    simp [nsqrz] at sqr_eq,
    simp at nsqrz,
    simp [sqr_eq, nsqrz] },
  have nnez : n ≠ 0,
  { contrapose! nsqr_nez with nz,
    simp [nz] },
  have eq1 : (m^2).factors.count p = 2 * m.factors.count p,
    by rw nat.factors_count_pow,
  have eq2 : (p * n^2).factors.count p = 2 * n.factors.count p + 1,
  { rw [nat.count_factors_mul_of_pos prime_p.pos (nat.pos_of_ne_zero nsqr_nez),
      nat.factors_prime prime_p, nat.factors_count_pow],
    simp [add_comm] },
  have : (2 * m.factors.count p) % 2 = (2 * n.factors.count p + 1) % 2,
  { rw [←eq1, sqr_eq, eq2] },
  rw [add_comm, nat.add_mul_mod_self_left, nat.mul_mod_right] at this,
  norm_num at this
end

