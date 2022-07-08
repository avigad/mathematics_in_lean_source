import data.int.basic
import ring_theory.principal_ideal_domain
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

   (a + bi) (c + di) & = ac + bci + adi + bd i^2 \\
     & = (ac - bd) + (bc + ad)i.

This explains the definition of ``has_mul`` below.
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
The essential ones appear in the definition below. In each case, the relevant
identity is proved by unfolding definitions, using the ``ext`` tactic
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

/- TEXT:
We will now show that the Gaussian integers have an important additional
property. A *Euclidean domain* is a ring :math:`R` equipped with a *norm*
function :math:`N : R \to \mathbb{N}` with the following two properties:

- For every :math:`a` and :math:`b \ne 0` in :math:`R`, there are
  :math:`q` and :math:`r` in :math:`R` such that :math:`a = bq + r` and
  either :math:`r = 0` or `N(a) < N(b)`.
- For every :math:`a` and :math:`b \ne 0`, :math:`N(a) \le N(ab)`.

The ring of integers :math:`\Bbb{Z}` with :math:`N(a) = |a|` is an
archetypal example of a Euclidean domain.
In that case, we can take :math:`q` to be the
result of integer division of :math:`a` by :math:`b` and :math:`r`
to be the remainder. These functions are defined in Lean so that the
satisfy the following:
EXAMPLES: -/
-- QUOTE:
example (a b : ℤ) : a = b * (a / b) + a % b := eq.symm $ int.div_add_mod a b

example (a b : ℤ) : b ≠ 0 → 0 ≤ a % b := int.mod_nonneg a

example (a b : ℤ) : b ≠ 0 → a % b < abs b := int.mod_lt a
-- QUOTE.

/- TEXT:
In an arbitrary ring, an element :math:`a` is said to be a *unit* if it divides
:math:`1`. A nonzero element :math:`a` is said to be *irreducible* if it cannot
be written in the form :math:`a = bc`
where neither :math:`b` nor :math:`c` is a unit. In the integers, every
irreducible element :math:`a` is *prime*, which is to say, whenever :math:`a`
divides a product :math:`bc`, it divides either :math:`b` or :math:`c`. But
in other rings this property can fail. In the ring
:math:`\Bbb{Z}[\sqrt{-5}]`, we have

.. math::

  6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5}),

and the elements :math:`2`, :math:`3`, :math:`1 + \sqrt{-5}`, and
:math:`1 - \sqrt{-5}` are all irreducible, but they are not prime. For example,
:math:`2` divides the product :math:`(1 + \sqrt{-5})(1 - \sqrt{-5})`,
but it does not divide either factor. In particular, we no longer have
unique factorization: the number :math:`6` can be factored into irreducible
elements in more than one way.

In contrast, every Euclidean domain is a unique factorization domain, which
implies that every irreducible element is prime.
The axioms for a Euclidean domain imply that one can write any nonzero element
as a finite product of irreducible elements. They also imply that one can use
the Euclidean algorithm to find a greatest common divisor of any two
nonzero elements ``a`` and ``b``, i.e.~an element that is divisible by any
other common divisor. This, in turn, implies that factorization
into irreducible elements is unique up to multiplication by units.

We now show that the Gaussian integers are a Euclidean domain with
the norm defined by :math:`N(a + bi) = (a + bi)(a - bi) = a^2 + b^2`.
The Gaussian integer :math:`a - bi` is called the *conjugate* of :math:`a + bi`.
It is not hard to check that for any complex numbers :math:`x` and :math:`y`,
we have :math:`N(xy) = N(x)N(y)`.

To see that this definition of the norm makes the complex numbers a Euclidean
domain, only the first property is challenging. Suppose
we want to write :math:`a + bi = (c + di) q + r` for suitable :math:`q`
and :math:`r`. Treating :math:`a + bi` and :math:`c + di` are complex
numbers, carry out the division

.. math::

  \frac{a + bi}{c + di} = \frac{(a + bi)(c - di)}{(c + di)(c-di)} =
    \frac{ac + bd}{c^2 + d^2} + \frac{bc -ad}{c^2+d^2} i.

The real and imaginary parts might not be integers, but we can round
them to the nearest integers :math:`u` and :math:`v`. We can then express the
right-hand size as :math:`(u + vi) + (u' + v'i)`, where
:math:`u' + v'i` is the part left over. Note that we have
:math:`|u'| \le 1/2` and :math:`|v'| \le 1/2`, and hence

.. math::

  N(u' + v' i) = (u')^2 + (v')^2 \le 1/4 + 1/4 \le 1/2.

Multiplying through by :math:`c + di`, we have

.. math::

  a + bi = (c + di) (u + vi) + (c + di) (u' + v'i).

Setting :math:`q = u + vi` and :math:`r = (c + di) (u' + v'i)`, we have
:math:`a + bi = (c + di) q + r`, and we only need to
bound :math:`N(r)`:

.. math::

  N(r) = N(c + di)N(u' + v'i) \le N(c + di) \cdot 1/2 < N(c + di).

The argument we just carried out requires viewing the Gaussian integers
as a subset of the complex numbers. One option for formalizing it in Lean
is therefore to embed the Gaussian integers in the complex numbers, embed
the integers in the Gaussian integers, define the rounding function from the
real numbers to the integers, and take great care to pass back and forth
between these number systems appropriately.
In fact, this is exactly the approach that is followed in mathlib,
where the Gaussian integers themselves are constructed as a special case
of a ring of *quadratic integers*.
See the file `gaussian_int.lean <https://github.com/leanprover-community/mathlib/blob/master/src/number_theory/zsqrtd/gaussian_int.lean>`_.

Here we will instead carry out an argument that stays in the integers.
This illustrates an choice one commonly faces when formalizing mathematics.
Given an argument that requires concepts or machinery that is not already
in the library, one has two choices: either formalizes the concepts or machinery
needed, or adapt the argument to make use of concepts and machinery you
already have.
The first choice is generally a good investment of time when the results
can be used in other contexts.
Pragmatically speaking, however, sometimes seeking a more elementary proof
is more efficient.

The usual quotient-remainder theorem for the integers says that for
every :math:`a` and nonzero :math:`b`, there are :math:`q` and :math:`r`
such that :math:`a = b q + r` and :math:`0 \le r < b`.
Here we will make use of the following variation, which says that there
are :math:`q'` and :math:`r'` such that
:math:`a = b q' + r'` and :math:`|r'| \le b/2`.
You can check that if the value of :math:`r` in the first statement
satisfies :math:`r \le b/2`, we can take :math:`q' = q` and :math:`r' = r`,
and otherwise we can take :math:`q' = q + 1` and :math:`r' = r - b`.
We are grateful to Heather Macbeth for suggesting the following more
elegant approach, which avoids definition by cases.
We simply add ``b / 2`` to ``a`` before dividing and then subtract it
from the remainder.
BOTH: -/
namespace int

-- QUOTE:
def div' (a b : ℤ) := (a + b / 2) / b

def mod' (a b : ℤ) := (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a :=
begin
  rw [div', mod'],
  linarith [int.div_add_mod (a + b / 2) b],
end

theorem abs_mod'_le (a b : ℤ) (h : 0 < b): abs (mod' a b) ≤ b / 2 :=
begin
  rw [mod', abs_le],
  split,
  { linarith [int.mod_nonneg (a + b / 2) h.ne'] },
  have := int.mod_lt_of_pos (a + b / 2) h,
  have := int.div_add_mod b 2,
  have := int.mod_lt_of_pos b zero_lt_two,
  linarith
end
-- QUOTE.

/- TEXT:
Note the use of our old friend, ``linarith``. We will also need to express
``mod'`` in terms of ``div'``.
BOTH: -/
-- QUOTE:
theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b :=
by linarith [div'_add_mod' a b]
-- QUOTE.

end int

/- TEXT:
We will use the fact that :math:`x^2 + y^2` is equal to zero if and only if
:math:`x` and :math:`y` are both zero. As an exercise, we ask you to prove
that this holds in any ordered ring.
SOLUTIONS: -/
private theorem aux {α : Type*} [linear_ordered_ring α] {x y : α} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { apply le_antisymm _ (sq_nonneg x),
    rw ←h,
    apply le_add_of_nonneg_right (sq_nonneg y) },
  exact pow_eq_zero h'
end

-- QUOTE:
-- BOTH:
theorem sq_add_sq_eq_zero {α : Type*} [linear_ordered_ring α] (x y : α) :
  x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
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
-- QUOTE.
-- BOTH:

/- TEXT:
We will put all the remaining definitions and theorems in this section
in the ``gaussint`` namespace.
First, we define the ``norm`` function and ask you to establish
some of its properties.
The proofs are all short.
BOTH: -/
namespace gaussint

-- QUOTE:
def norm (x : gaussint) := x.re^2 + x.im^2

@[simp] theorem norm_nonneg (x : gaussint) : 0 ≤ norm x :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
by { apply add_nonneg; apply sq_nonneg }
-- BOTH:

theorem norm_eq_zero (x : gaussint) : norm x = 0 ↔ x = 0 :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
by { rw [norm, sq_add_sq_eq_zero, gaussint.ext_iff], refl }
-- BOTH:

theorem norm_pos (x : gaussint) : 0 < norm x ↔ x ≠ 0 :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
by { rw [lt_iff_le_and_ne, ne_comm, ne, norm_eq_zero], simp [norm_nonneg] }
-- BOTH:

theorem norm_mul (x y : gaussint) : norm (x * y) = norm x * norm y :=
/- EXAMPLES:
sorry
SOLUTIONS: -/
by { simp [norm], ring }
-- BOTH:
-- QUOTE.

/- TEXT:
Next we define the conjugate function:
BOTH: -/
-- QUOTE:
def conj (x : gaussint) : gaussint := ⟨x.re, -x.im⟩

@[simp] theorem conj_re (x : gaussint) : (conj x).re = x.re := rfl
@[simp] theorem conj_im (x : gaussint) : (conj x).im = - x.im := rfl

theorem norm_conj (x : gaussint) : norm (conj x) = norm x :=
by { simp [norm] }
-- QUOTE.

/- TEXT:
Finally, we define division for the Gaussian integers
with the notation ``x / y``, that rounds the complex quotient to the nearest
Gaussian integer. We use our bespoke ``int.div'`` for that purpose.
As we calculated above, if ``x`` is :math:`a + bi` and ``y`` is :math:`c + di`,
then the real and imaginary parts of ``x / y`` are the nearest integers to

.. math::

  \frac{ac + bd}{c^2 + d^2} \quad \text{and} \quad \frac{bc -ad}{c^2+d^2},

respectively. Here the numerators are the real and imaginary parts of
:math:`(a + bi) (c - di)`, and the denominators are both equal to the norm
of :math:`c + di`.
BOTH: -/
-- QUOTE:
instance : has_div gaussint :=
⟨λ x y, ⟨int.div' (x * conj y).re (norm y), int.div' (x * conj y).im (norm y)⟩⟩
-- QUOTE.

/- TEXT:
Having defined ``x / y``, We define ``x % y`` to be the remainder,
``x - (x / y) * y``. As above, we record the definitions in the
theorems ``div_def`` and
``mod_def`` so that we can use them with ``simp`` and ``rewrite``.
BOTH: -/
-- QUOTE:
instance : has_mod gaussint := ⟨λ x y, x - y * (x / y)⟩

theorem div_def (x y : gaussint) :
  x / y = ⟨int.div' (x * conj y).re (norm y), int.div' (x * conj y).im (norm y)⟩ := rfl

theorem mod_def (x y : gaussint) : x % y = x - y * (x / y) := rfl
-- QUOTE.

/- TEXT:
These definitions immediately yield ``x = y * (x / y) + x % y`` for every
``x`` and ``y``, so all we need to do is show that the norm of ``x % y`` is
less than the norm of ``y`` when ``y`` is not zero.

We just defined the real and imaginary parts of ``x / y`` to be
``div' (x * conj y).re (norm y)`` and ``div' (x * conj y).im (norm y)``,
respectively.
Calculating, we have

  ``(x % y) * conj y = (x - x / y * y) * conj y = x * conj y - x * (y * conj j)``

The real and imaginary parts of the right-hand side are exactly ``mod' (x * conj y).re (norm y)`` and ``mod' (x * conj y).im (norm y)``.
By the properties of ``div'`` and ``mod'``,
these are guaranteed to be less than or equal to ``norm y / 2``.
So we have

  ``norm ((x % y) * conj y) ≤ (norm y / 2)^2 + (norm y / 2)^2 ≤ (norm y / 2) * norm y``.

On the other hand, we have

  ``norm ((x % y) * conj y) = norm (x % y) * norm (conj y) = norm (x % y) * norm y``.

Dividing through by ``norm y`` we have ``norm (x % y) ≤ (norm y) / 2 < norm y``,
as required.

This messy calculation is carried out in the next proof. We encourage you
to step through the details and see if you can find a nicer argument.
BOTH: -/
-- QUOTE:
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
-- QUOTE.

/- TEXT:
We are in the home stretch. Our ``norm`` function maps Gaussian integers to
nonnegative integers. We need a function that maps Gaussian integers to natural
numbers, and we obtain that by composing ``norm`` with the function
``int.nat_abs``, which maps integers to the natural numbers.
The first of the next two lemmas establishes that mapping the norm to the
natural numbers and back to the integers does not change the value.
The second one re-expresses the fact that the norm is decreasing.
BOTH: -/
-- QUOTE:
lemma coe_nat_abs_norm (x : gaussint) : (x.norm.nat_abs : ℤ) = x.norm :=
int.nat_abs_of_nonneg (norm_nonneg _)

lemma nat_abs_norm_mod_lt (x y : gaussint) (hy : y ≠ 0) :
  (x % y).norm.nat_abs < y.norm.nat_abs :=
begin
  apply int.coe_nat_lt.1, simp,
  exact int.nat_abs_lt_nat_abs_of_nonneg_of_lt (norm_nonneg _) (norm_mod_lt x hy)
end
-- QUOTE.

/- TEXT:
We also need to establish the second key property of the norm function
on a Euclidean domain.
BOTH: -/
-- QUOTE:
lemma not_norm_mul_left_lt_norm (x : gaussint) {y : gaussint} (hy : y ≠ 0) :
  ¬ (norm (x * y)).nat_abs < (norm x).nat_abs :=
begin
  apply not_lt_of_ge,
  rw [norm_mul, int.nat_abs_mul],
  apply le_mul_of_one_le_right (nat.zero_le _),
  apply int.coe_nat_le.1,
  rw [coe_nat_abs_norm],
  exact int.add_one_le_of_lt ((norm_pos _).mpr hy)
end
-- QUOTE.

/- TEXT:
We can now put it together to show that the Gaussian integers are an
instance of a Euclidean domain. We use the quotient and remainder function we
have defined.
The mathlib definition of a Euclidean domain is more general than the one
above in that it allows us to show that remainder decreases with respect
to any well-founded measure.
Comparing the values of a norm function that returns natural numbers is
just one instance of such a measure,
and in that case, the required properties are the theorems
``nat_abs_norm_mod_lt`` and ``not_norm_mul_left_lt_norm``.
BOTH: -/
-- QUOTE:
instance : euclidean_domain gaussint :=
{ quotient        := (/),
  remainder       := (%),
  quotient_mul_add_remainder_eq :=
                     λ x y, by {rw [mod_def, add_comm, sub_add_cancel] },
  quotient_zero   := λ x, by { simp [div_def, norm, int.div'], refl },
  r               := measure (int.nat_abs ∘ norm),
  r_well_founded  := measure_wf (int.nat_abs ∘ norm),
  remainder_lt    := nat_abs_norm_mod_lt,
  mul_left_not_lt := not_norm_mul_left_lt_norm,
  .. gaussint.comm_ring }
-- QUOTE.

/- TEXT:
An immediate payoff is that we now know that, in the Gaussian integers,
the notions of being prime and being irreducible coincide.
BOTH: -/
-- QUOTE:
example (x : gaussint) : irreducible x ↔ prime x :=
principal_ideal_ring.irreducible_iff_prime
-- QUOTE.

end gaussint

