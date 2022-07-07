import data.int.basic
import tactic

/- TEXT:
.. _section_building_the_gaussian_integers:

Building the Gaussian Integers
------------------------------

We will now illustrate the use of the algebraic hierarchy in Lean by
building an important mathematical object, the *Gaussian integers*,
and showing that it is a Euclidean domain. In other words, according to
the terminology we have been using, we will define the Gaussian integers
and show that they are an instance of the Euclidean domain structure.

In ordinary mathematical terms, the set of Gaussian integers :math:`\Bbb{Z}[i]`
is the set of complex numbers :math:`\{ a + b i \mid a, b \in \Bbb{Z}\}`.
But rather than define them as a subset of the complex numbers, our goal
here is to define them as a data type in their own right. We do this by
representing a Gaussian integer as a pair of integers, which we think of as the
*real* and *imaginary* parts.
BOTH: -/
-- QUOTE:
@[ext] structure gaussint := (re : ℤ) (im : ℤ)
-- QUOTE.

/- TEXT:
We first show that the Gaussian integers have the structure of a ring,
with ``0`` defined to be ``⟨0, 0⟩``, ``1`` defined to be ``⟨1, 0⟩``, and
addition defined pointwise. To work out the definition of multiplication,
remember that we want the element :math:`i`, represented by ``⟨0, 1⟩``, to
be a square root of :math:`-1`. Thus we want

.. math::

   (a + bi) \cdot (c + di) & = ac + bci + adi + bd i^2 \\
     & = (ac - bd) + (bc + ad)i,

which explains the definition of ``has_mul`` below.
BOTH: -/
namespace gaussint

-- QUOTE:
instance : has_zero gaussint := ⟨⟨0, 0⟩⟩
instance : has_one gaussint  := ⟨⟨1, 0⟩⟩
instance : has_add gaussint  := ⟨λ x y, ⟨x.re + y.re, x.im + y.im⟩⟩
instance : has_neg gaussint  := ⟨λ x, ⟨-x.re, -x.im⟩⟩
instance : has_mul gaussint  :=
  ⟨λ x y, ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
-- QUOTE.

/- TEXT:
As noted in :numref:`section_structures`, it is a good idea to put all the definitions
related to a data type in a namespace with the same name. Thus in the Lean
files associated with this chapter, these definitions are made in the
``gaussint`` namespace.

Notice that here we are defining the interpretations of the notation ``0``,
``1``, ``+``, ``-``, and ``*`` directly, rather than naming them
``gaussint.zero`` and the like and assigning the notation to those.
It is often useful to have an explicit name for the definitions, for example,
to use with ``simp`` and ``rewrite``.
BOTH: -/
-- QUOTE:
theorem zero_def : (0 : gaussint) = ⟨0, 0⟩ := rfl
theorem one_def : (1 : gaussint) = ⟨1, 0⟩ := rfl
theorem add_def (x y : gaussint) : x + y = ⟨x.re + y.re, x.im + y.im⟩ := rfl
theorem neg_def (x : gaussint) : -x = ⟨-x.re, -x.im⟩ := rfl
theorem mul_def (x y : gaussint) :
  x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ := rfl
-- QUOTE.

/- TEXT:
It is also useful to name the rules that compute the real and imaginary
parts, and to declare them to the simplifier.
BOTH: -/
-- QUOTE:
@[simp] theorem zero_re : (0 : gaussint).re = 0 := rfl
@[simp] theorem zero_im : (0 : gaussint).im = 0 := rfl
@[simp] theorem one_re : (1 : gaussint).re = 1 := rfl
@[simp] theorem one_im : (1 : gaussint).im = 0 := rfl
@[simp] theorem add_re (x y : gaussint) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : gaussint) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : gaussint) : (-x).re = - x.re := rfl
@[simp] theorem neg_im (x : gaussint) : (-x).im = - x.im := rfl
@[simp] theorem mul_re (x y : gaussint) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : gaussint) : (x * y).im = x.re * y.im + x.im * y.re := rfl
-- QUOTE.

/- TEXT:
It is now surprisingly easy to show that the Gaussian integers are an instance
of a commutative ring. We are putting the structure concept to good use.
Each particular Gaussian integer is an instance of the ``gaussint`` structure,
whereas the type ``gaussint`` itself, together with the relevant operations, is an
instance of the ``comm_ring`` structure. The ``comm_ring`` structure, in turn,
extends the notational structures ``has_zero``, ``has_one``, ``has_add``,
``has_neg``, and ``has_mul``.

If you type ``instance : comm_ring gaussint := _``, click on the light bulb
that appears in VS Code, and then ask Lean to fill in a skeleton for the
structure definition, you will see a scary number of entries.
Jumping to the definition of the structure, however, shows that many of the
fields have default definitions that Lean will fill in for you automatically.
The essential ones appear in the definition below. In each case, the key
identified are proved by unfolding definitions, using the ``ext`` tactic
to reduce the identities to their real and imaginary components,
simplifying, and, if necessary, carrying out the relevant ring calculation in
the integers.
BOTH: -/
-- QUOTE:
instance : comm_ring gaussint :=
{ zero := 0,
  one := 1,
  add := (+),
  neg := λ x, -x,
  mul := (*),

  add_assoc := by { intros, ext; simp; ring },
  zero_add := by { intros, ext; simp },
  add_zero := by { intros, ext; simp },
  add_left_neg := by { intros, ext; simp },
  add_comm := by { intros, ext; simp; ring },
  mul_assoc := by { intros, ext; simp; ring },
  one_mul := by { intros, ext; simp },
  mul_one := by { intros, ext; simp },
  left_distrib := by { intros, ext; simp; ring },
  right_distrib := by { intros, ext; simp; ring },
  mul_comm := by { intros, ext; simp; ring } }
-- QUOTE.

/- TEXT:
Lean's library defines the class of *nontrivial* types to be types with at
least two distinct elements. In the context of a ring, this is equivalent
to saying the the zero is not equal to the one. Since some common theorems
depend on that fact, we may as well establish it now.
BOTH: -/
-- QUOTE:
instance : nontrivial gaussint :=
by { use [0, 1], rw [ne, gaussint.ext_iff], simp }
-- QUOTE.

end gaussint

-- OMIT:




/-
An alternate form of the quotient-remainder theorem: when expressing `a = q * b + r`,
it chooses `q` so that we have `|r| ≤ b / 2`.
-/

namespace int

def div' (a b : ℤ) := (a + b / 2) / b

def mod' (a b : ℤ) := (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a :=
begin
  rw [div', mod'],
  linarith [int.div_add_mod (a + b / 2) b],
end

theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b :=
by linarith [div'_add_mod' a b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b): abs (mod' a b) ≤ b / 2 :=
begin
  rw [mod', abs_le],
  split,
  { linarith [int.mod_nonneg (a + b / 2) h.ne'] },
  { have := int.mod_lt_of_pos (a + b / 2) h,
    have := int.div_add_mod b 2,
    have := int.mod_lt_of_pos b zero_lt_two,
    linarith },
end

end int

-- OMIT:
-- This was the previous version:
namespace int

def div'' (a b : ℤ) := if 2 * (a % b) ≤ b then a / b else a / b + 1

def mod'' (a b : ℤ) := if 2 * (a % b) ≤ b then a % b else a % b - b

theorem div''_add_mod'' (a b : ℤ) : b * div'' a b + mod'' a b = a :=
begin
  rw [div'', mod''],
  split_ifs,
  { apply int.div_add_mod },
  rw [mul_add, mul_one, add_assoc, add_comm b, sub_add_cancel],
  apply int.div_add_mod
end

theorem mod''_eq (a b : ℤ) : mod'' a b = a - b * div'' a b :=
begin
  conv { to_rhs, congr, rw ←div''_add_mod'' a b },
  rw [add_comm, add_sub_cancel]
end

theorem abs_mod''_le (a b : ℤ) (h : 0 < b): abs (mod'' a b) ≤ b / 2 :=
begin
  rw [mod''],
  split_ifs with h' h',
  { rw [abs_of_nonneg (int.mod_nonneg _ (ne_of_lt h).symm)],
    refine int.le_div_of_mul_le (by norm_num) _,
    rwa mul_comm },
  rw abs_of_neg,
  { apply int.le_div_of_mul_le, norm_num,
    rw [neg_sub, sub_mul],
    linarith },
  have := int.mod_lt a (ne_of_lt h).symm,
  rw abs_of_pos h at this,
  rwa sub_neg
end

end int

/-
Conjugate and norm for Gaussian integers.
-/

private theorem aux {α : Type*} [linear_ordered_ring α] {x y : α} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { apply le_antisymm _ (sq_nonneg x),
    rw ←h,
    apply le_add_of_nonneg_right (sq_nonneg y) },
  exact pow_eq_zero h'
end

theorem sq_add_sq_eq_zero {α : Type*} [linear_ordered_ring α] (x y : α) :
  x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
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

namespace gaussint

def conj (x : gaussint) : gaussint := ⟨x.re, -x.im⟩

@[simp] theorem conj_re (x : gaussint) : (conj x).re = x.re := rfl
@[simp] theorem conj_im (x : gaussint) : (conj x).im = - x.im := rfl

def norm (x : gaussint) := x.re^2 + x.im^2

@[simp] theorem norm_nonneg (x : gaussint) : 0 ≤ norm x :=
by { apply add_nonneg; apply sq_nonneg }

theorem norm_eq_zero (x : gaussint) : norm x = 0 ↔ x = 0 :=
by { rw [norm, sq_add_sq_eq_zero, gaussint.ext_iff], refl }

theorem norm_pos (x : gaussint) : 0 < norm x ↔ x ≠ 0 :=
by { rw [lt_iff_le_and_ne, ne_comm, ne, norm_eq_zero], simp [norm_nonneg] }

instance : has_div gaussint :=
⟨λ x y, ⟨int.div' (x * conj y).re (norm y), int.div' (x * conj y).im (norm y)⟩⟩

instance : has_mod gaussint := ⟨λ x y, x - y * (x / y)⟩

theorem div_def (x y : gaussint) :
  x / y = ⟨int.div' (x * conj y).re (norm y), int.div' (x * conj y).im (norm y)⟩ := rfl

theorem mod_def (x y : gaussint) : x % y = x - y * (x / y) := rfl

theorem norm_mul (x y : gaussint) : norm (x * y) = norm x * norm y :=
by { simp [norm], ring }

theorem norm_conj (x : gaussint) : norm (conj x) = norm x :=
by { simp [norm] }

lemma norm_mod_lt (x : gaussint) {y : gaussint} (hy : y ≠ 0) : (x % y).norm < y.norm :=
begin
  have norm_y_pos : 0 < norm y,
    by rwa [norm_pos],
  have : (x % y) * conj y =
    ⟨int.mod' (x * conj y).re (norm y), int.mod' (x * conj y).im (norm y)⟩,
  { rw [mod_def, sub_mul, int.mod'_eq, int.mod'_eq, sub_eq_add_neg, norm, div_def],
    ext; simp; ring },
  have : norm (x % y) * norm y ≤ (norm y / 2) * norm y,
  { conv { to_lhs, rw [←norm_conj y, ←norm_mul, this, norm] },
    simp,
    transitivity 2 * (y.norm / 2)^2,
    { rw [two_mul],
      apply add_le_add;
      { rw [sq_le_sq],
        apply le_trans (int.abs_mod'_le _ _ norm_y_pos),
        apply le_abs_self } },
      rw [pow_two, ←mul_assoc, mul_comm, mul_comm (2 : ℤ)],
      apply mul_le_mul_of_nonneg_left _ _,
      { apply int.div_mul_le, norm_num },
      apply int.div_nonneg (norm_nonneg y), norm_num },
  have : norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right this norm_y_pos,
  apply lt_of_le_of_lt this,
  apply int.div_lt_of_lt_mul, { norm_num },
  linarith
end

lemma coe_nat_abs_norm (x : gaussint) : (x.norm.nat_abs : ℤ) = x.norm :=
int.nat_abs_of_nonneg (norm_nonneg _)

lemma nat_abs_norm_mod_lt (x y : gaussint) (hy : y ≠ 0) :
  (x % y).norm.nat_abs < y.norm.nat_abs :=
begin
  apply int.coe_nat_lt.1, simp,
  exact int.nat_abs_lt_nat_abs_of_nonneg_of_lt (norm_nonneg _) (norm_mod_lt x hy),
end

lemma norm_le_norm_mul_left (x : gaussint) {y : gaussint} (hy : y ≠ 0) :
  (norm x).nat_abs ≤ (norm (x * y)).nat_abs :=
by rw [norm_mul, int.nat_abs_mul];
  exact le_mul_of_one_le_right (nat.zero_le _)
    (int.coe_nat_le.1 (by rw [coe_nat_abs_norm]; exact int.add_one_le_of_lt ((norm_pos _).mpr hy)))

instance : euclidean_domain gaussint :=
{ quotient := (/),
  remainder := (%),
  quotient_mul_add_remainder_eq := λ x y, by {rw [mod_def, add_comm, sub_add_cancel] },
  quotient_zero := λ x, by { simp [div_def, norm, int.div'], refl },
  r := _,
  r_well_founded := measure_wf (int.nat_abs ∘ norm),
  remainder_lt := nat_abs_norm_mod_lt,
  mul_left_not_lt := λ a b hb0, not_lt_of_ge $ norm_le_norm_mul_left a hb0,
  .. gaussint.comm_ring }

end gaussint

