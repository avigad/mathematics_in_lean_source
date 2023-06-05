.. _types_and_structures:

Types and Structures
====================

.. _types:

Types
-----

You have already seen that the library defines the
basic number types:

.. code-block:: lean

    import data.complex.basic

    #check ℕ
    #check ℤ
    #check ℚ
    #check ℝ
    #check ℂ

    #check nat
    #check int
    #check rat
    #check real
    #check complex

The blackboard bold symbols are notation for
the identifiers in the second group.

.. TODO: add chapter reference

You have also seen that Lean supports generic reasoning
about types, with variables that range over types.
It is conventional to use Greek letters ``α``, ``β``, ``γ``, ...
for types, though we often use capital Roman
letters for types with an associated structure:
``R`` for a ring, ``G`` for a group, ``M`` for a module, and so on.
We will discuss algebraic structures in a later chapter.

Types are usually marked as implicit arguments
to a function because they can generally be inferred
from other arguments.
Declaring a variable ``α`` to be of type ``Type*``
instead of ``Type`` makes a theorem more general,
since it means that ``α`` can be an element of any
type *universe*.
The details of universes need not concern us now,
but, roughly speaking,  universes are used to
avoid set-theoretic paradoxes.
For example, it would be problematic to declare a
type of all groups,
but we can reason about all groups in some universe.
To state a generic theorem about arbitrary groups,
we leave the universe unspecified.

We have also seen that Lean allows us to construct
new types. If ``α`` and ``β`` are types, then ``α → β``
is the type of functions from  ``α`` to ``β``,
and ``α × β`` is the type of ordered pairs from ``α`` and ``β``.
Lean also lets us define new types and type constructions.
The following shows us how we can define the Gaussian integers
by representing them as ordered pairs.

.. code-block:: lean

    def gaussian_integer := ℤ × ℤ

    notation `ℤ[i]` := gaussian_integer

    namespace gaussian_integer

    def zero : ℤ[i] := ⟨0, 0⟩
    def one : ℤ[i]  := ⟨1, 0⟩
    def ii : ℤ[i]   := ⟨0, 1⟩

    def add (z w : ℤ[i]) : ℤ[i] := ⟨z.1 + w.1, z.2 + w.2⟩
    def mul (z w : ℤ[i]) : ℤ[i] := ⟨z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1⟩
    def neg (z : ℤ[i])   : ℤ[i] := ⟨-z.1, -z.2⟩

    instance : has_zero ℤ[i] := ⟨zero⟩
    instance : has_one  ℤ[i] := ⟨one⟩
    instance : has_add  ℤ[i] := ⟨add⟩
    instance : has_mul  ℤ[i] := ⟨mul⟩
    instance : has_neg  ℤ[i] := ⟨neg⟩

    end gaussian_integer

.. TODO: add chapter reference

You can type the notation ``ℤ[i]`` as ``\Z[i]``,
and VS Code will make the replacement when you
hit the tab key or a space.
The ``instance`` commands declare the expected notation;
you will learn more about that later.
The following shows that, with these declarations,
we can use the new notation.
As soon as a type has a zero, a one,
and a notion of addition,
Lean can make sense of numerals,
interpreting them via their binary representation.

.. code-block:: lean

    def gaussian_integer := ℤ × ℤ

    notation `ℤ[i]` := gaussian_integer

    namespace gaussian_integer

    def zero : ℤ[i] := ⟨0, 0⟩
    def one : ℤ[i]  := ⟨1, 0⟩
    def ii : ℤ[i]   := ⟨0, 1⟩

    def add (z w : ℤ[i]) : ℤ[i] := ⟨z.1 + w.1, z.2 + w.2⟩
    def mul (z w : ℤ[i]) : ℤ[i] := ⟨z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1⟩
    def neg (z : ℤ[i])   : ℤ[i] := ⟨-z.1, -z.2⟩

    instance : has_zero ℤ[i] := ⟨zero⟩
    instance : has_one  ℤ[i] := ⟨one⟩
    instance : has_add  ℤ[i] := ⟨add⟩
    instance : has_mul  ℤ[i] := ⟨mul⟩
    instance : has_neg  ℤ[i] := ⟨neg⟩

    end gaussian_integer

    -- BEGIN
    open gaussian_integer

    variables z w : ℤ[i]

    #check (12345 : ℤ[i])
    #check z + 12345
    #check (z + 1) * -w

    theorem ii_mul_ii : ii * ii = -1 := rfl
    -- END

The command ``open gaussian_integer`` allows us to write ``ii``
instead of ``gaussian_integer.ii``.

.. These are not equivalent, so don't use them.
.. Introduce pattern matching somewhere else.
..
.. Lean supports another style of defining
.. the functions ``add``, ``mul``, and ``neg``, using
.. *pattern matching*.

.. .. code-block:: lean

..     def gaussian_integer := ℤ × ℤ

..     notation `ℤ[i]` := gaussian_integer

..     namespace gaussian_integer

..     -- BEGIN
..     def add : ℤ[i] → ℤ[i] → ℤ[i]
..     | (a, b) (c, d) := (a + c, b + d)

..     def mul : ℤ[i] → ℤ[i] → ℤ[i]
..     | (a, b) (c, d) := (a*c - b*d, a*d + b*c)

..     def neg : ℤ[i] → ℤ[i]
..     | (a, b) := (-a, -b)
..     -- END

..     end gaussian_integer

.. Notice that the ``:=`` symbol is replaced by a vertical bar.
.. Since the arguments to ``add``, which are of type ``ℤ[i]``,
.. are ordered pairs,
.. they can be assumed to be of the form ``(a, b)`` and ``(c, d)``.
.. The return value of the function is then defined in terms of
.. ``a``, ``b``, ``c``, and ``d``.

When we define a new type of object in a library,
it is a good idea to design an interface to the library
that hides the internal representation.
That way, users of the library don't have to think
about how the objects are defined,
and later theorems continue to hold even if the
internal representation changes.
The following snippet defines a function that
builds a Gaussian integer from a pair of integers,
as well as the functions that return the
real and imaginary parts.
Using the ``rfl`` proof term or ``rfl`` tactic
causes Lean to unfold the definition and try to reduce
both sides until they are the same.
The theorem ``re_mk`` can be proved that way because
``re (mk x y)`` unfolds to ``(x, y).1``,
and Lean knows how to reduce the projections of a pair.
That trick does not work for the theorem ``mk_re_im``
right away,
but it does work after we use the ``cases`` tactic
to expand ``z`` to a pair ``(z1, z2)``.
We ask you to state and prove the corresponding theorems
for multiplication, neg, and ``ii``.

.. code-block:: lean

    def gaussian_integer := ℤ × ℤ

    notation `ℤ[i]` := gaussian_integer

    namespace gaussian_integer

    def zero : ℤ[i] := ⟨0, 0⟩
    def one : ℤ[i]  := ⟨1, 0⟩
    def ii : ℤ[i]   := ⟨0, 1⟩

    def add (z w : ℤ[i]) : ℤ[i] := ⟨z.1 + w.1, z.2 + w.2⟩
    def mul (z w : ℤ[i]) : ℤ[i] := ⟨z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1⟩
    def neg (z : ℤ[i])   : ℤ[i] := ⟨-z.1, -z.2⟩

    instance : has_zero ℤ[i] := ⟨zero⟩
    instance : has_one  ℤ[i] := ⟨one⟩
    instance : has_add  ℤ[i] := ⟨add⟩
    instance : has_mul  ℤ[i] := ⟨mul⟩
    instance : has_neg  ℤ[i] := ⟨neg⟩

    -- BEGIN
    def mk (x y : ℤ) : ℤ[i] := (x, y)
    def re (w : ℤ[i]) : ℤ := w.1
    def im (w : ℤ[i]) : ℤ := w.2

    theorem re_mk (x y : ℤ) : re (mk x y) = x := rfl

    theorem im_mk (x y : ℤ) : im (mk x y) = y := rfl

    theorem mk_re_im (z : ℤ[i]): mk (re z) (im z) = z :=
    by { cases z, refl }

    theorem re_add (w z : ℤ[i]) : re (w + z) = re w + re z :=
    rfl

    theorem im_add (w z : ℤ[i]) : im (w + z) = im w + im z :=
    rfl

    theorem re_mul (w z : ℤ[i]) : re (w * z) = sorry :=
    sorry

    theorem im_mul (w z : ℤ[i]) : im (w * z) = sorry :=
    sorry

    theorem re_neg (w : ℤ[i]) : re (-w) = sorry :=
    sorry

    theorem im_neg (w : ℤ[i]) : im (-w) = sorry :=
    sorry

    theorem re_ii : re ii = sorry :=
    sorry

    theorem im_ii : im ii = sorry :=
    sorry
    -- END

    end gaussian_integer

At this stage, we have not proved anything about ``add``, ``mul``, and ``neg``.
We will use some automation to help with that.
First, we declare the theorems we have just proved as rules for the simplifier,
by adding the ``simp`` *attribute*.
We could have also done that when the theorems were originally proved,
by adding the annotation ``@[simp]`` just before.
We also show that we can prove that two Gaussian integers are equal
by proving that the real and imaginary parts are equal.
In the proof, the line ``simp [re, im, *] at *`` tells Lean to simplify
both the goal and the hypotheses using the definitions of ``re`` and ``im``,
the other hypotheses,
and any other rules previously marked with the ``simp`` attribute.
Adding the attribute ``ext`` means that the ``ext`` tactic will use that
theorem automatically to prove an equation between two Gaussian integers.

.. code-block:: lean

    import tactic

    def gaussian_integer := ℤ × ℤ

    notation `ℤ[i]` := gaussian_integer

    namespace gaussian_integer

    def zero : ℤ[i] := ⟨0, 0⟩
    def one : ℤ[i]  := ⟨1, 0⟩
    def ii : ℤ[i]   := ⟨0, 1⟩

    def add (z w : ℤ[i]) : ℤ[i] := ⟨z.1 + w.1, z.2 + w.2⟩
    def mul (z w : ℤ[i]) : ℤ[i] := ⟨z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1⟩
    def neg (z : ℤ[i])   : ℤ[i] := ⟨-z.1, -z.2⟩

    instance : has_zero ℤ[i] := ⟨zero⟩
    instance : has_one  ℤ[i] := ⟨one⟩
    instance : has_add  ℤ[i] := ⟨add⟩
    instance : has_mul  ℤ[i] := ⟨mul⟩
    instance : has_neg  ℤ[i] := ⟨neg⟩

    def mk (x y : ℤ) : ℤ[i] := (x, y)
    def re (w : ℤ[i]) : ℤ := w.1
    def im (w : ℤ[i]) : ℤ := w.2

    theorem re_mk (x y : ℤ) : re (mk x y) = x := rfl

    theorem im_mk (x y : ℤ) : im (mk x y) = y := rfl

    theorem mk_re_im (z : ℤ[i]): mk (re z) (im z) = z :=
    by { cases z, refl }

    theorem re_add (w z : ℤ[i]) : re (w + z) = re w + re z :=
    rfl

    theorem im_add (w z : ℤ[i]) : im (w + z) = im w + im z :=
    rfl

    theorem re_mul (w z : ℤ[i]) : re (w * z) = re w * re z - im w * im z :=
    rfl

    theorem im_mul (w z : ℤ[i]) : im (w * z) = re w * im z + im w * re z :=
    rfl

    theorem re_neg (w : ℤ[i]) : re (-w) = - re w :=
    rfl

    theorem im_neg (w : ℤ[i]) : im (-w) = - im w :=
    rfl

    theorem re_ii : re ii = 0 := rfl

    theorem im_ii : im ii = 1 := rfl

    -- BEGIN
    attribute [simp] re_add im_add re_mul im_mul re_neg im_neg
      re_ii im_ii re_ii im_ii

    @[ext] theorem ext {z w : ℤ[i]} (h1 : re z = re w) (h2 : im z = im w) :
      z = w :=
    begin
      cases z with z1 z2,
      cases w with w1 w2,
      simp [re, im, *] at *
    end
    -- END

    end gaussian_integer

After that, we can use the ``ext`` tactic and the simplifier to
prove theorems.
Step through the proof of ``add_assoc`` to see the
result of applying the ``ext`` tactic,
and change the first line that says ``simp [add_assoc]``
to just ``simp`` or ``simp only [re_add]`` to see the
effects of that.
In the next two lines, remember that the semicolon
after a tactic tells Lean to apply the next tactic to
every one of the resulting subgoals.
Use similar methods to prove other properties of addition,
multiplication, and negation,
such as the ones suggested with ``sorry``.
For the last one, you should prove theorems ``re_zero`` and ``im_zero``
and declare them to the simplifier.

.. code-block:: lean

    import tactic

    def gaussian_integer := ℤ × ℤ

    notation `ℤ[i]` := gaussian_integer

    namespace gaussian_integer

    def zero : ℤ[i] := ⟨0, 0⟩
    def one : ℤ[i]  := ⟨1, 0⟩
    def ii : ℤ[i]   := ⟨0, 1⟩

    def add (z w : ℤ[i]) : ℤ[i] := ⟨z.1 + w.1, z.2 + w.2⟩
    def mul (z w : ℤ[i]) : ℤ[i] := ⟨z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1⟩
    def neg (z : ℤ[i])   : ℤ[i] := ⟨-z.1, -z.2⟩

    instance : has_zero ℤ[i] := ⟨zero⟩
    instance : has_one  ℤ[i] := ⟨one⟩
    instance : has_add  ℤ[i] := ⟨add⟩
    instance : has_mul  ℤ[i] := ⟨mul⟩
    instance : has_neg  ℤ[i] := ⟨neg⟩

    def mk (x y : ℤ) : ℤ[i] := (x, y)
    def re (w : ℤ[i]) : ℤ := w.1
    def im (w : ℤ[i]) : ℤ := w.2

    theorem re_mk (x y : ℤ) : re (mk x y) = x := rfl

    theorem im_mk (x y : ℤ) : im (mk x y) = y := rfl

    theorem mk_re_im (z : ℤ[i]): mk (re z) (im z) = z :=
    by { cases z, refl }

    theorem re_add (w z : ℤ[i]) : re (w + z) = re w + re z :=
    rfl

    theorem im_add (w z : ℤ[i]) : im (w + z) = im w + im z :=
    rfl

    theorem re_mul (w z : ℤ[i]) : re (w * z) = re w * re z - im w * im z :=
    rfl

    theorem im_mul (w z : ℤ[i]) : im (w * z) = re w * im z + im w * re z :=
    rfl

    theorem re_neg (w : ℤ[i]) : re (-w) = - re w :=
    rfl

    theorem im_neg (w : ℤ[i]) : im (-w) = - im w :=
    rfl

    theorem re_ii : re ii = 0 := rfl

    theorem im_ii : im ii = 1 := rfl

    attribute [simp] re_add im_add re_mul im_mul re_neg im_neg
      re_ii im_ii re_ii im_ii

    @[ext] theorem ext {z w : ℤ[i]} (h1 : re z = re w) (h2 : im z = im w) :
      z = w :=
    begin
      cases z with z1 z2,
      cases w with w1 w2,
      simp [re, im, *] at *
    end

    -- BEGIN
    variables x y z : ℤ[i]

    theorem add_assoc : x + y + z = x + (y + z) :=
    begin
      ext,
      { simp [add_assoc] },
      simp [add_assoc]
    end

    example : x + y + z = x + (y + z) :=
    by ext; simp [add_assoc]

    example : x + y + z = x + (y + z) :=
    by ext; simp; ring

    theorem add_comm : x + y = y + x :=
    sorry

    theorem mul_assoc : x * y * z = x * (y * z) :=
    sorry

    theorem mul_comm : x * y = y * x :=
    sorry

    theorem add_neg : x + -x = 0 :=
    sorry
    -- END

    end gaussian_integer

The situation is still not ideal.
We would really like to make the Gaussian integers an
instance of a commutative ring, so that that
we can use all the generic theorems for rings,
as well as ``norm_num``, the ``ring`` tactic, and so on.
The following snippet of code does this.
The example after the instance declaration shows that we
can then calculate with numerals,
use subtraction and powers, and so on.

.. code-block:: lean

    import algebra.ring tactic

    def gaussian_integer := ℤ × ℤ

    notation `ℤ[i]` := gaussian_integer

    namespace gaussian_integer

    def zero : ℤ[i] := ⟨0, 0⟩
    def one : ℤ[i]  := ⟨1, 0⟩
    def ii : ℤ[i]   := ⟨0, 1⟩

    def add (z w : ℤ[i]) : ℤ[i] := ⟨z.1 + w.1, z.2 + w.2⟩
    def mul (z w : ℤ[i]) : ℤ[i] := ⟨z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1⟩
    def neg (z : ℤ[i])   : ℤ[i] := ⟨-z.1, -z.2⟩

    instance : has_zero ℤ[i] := ⟨zero⟩
    instance : has_one  ℤ[i] := ⟨one⟩
    instance : has_add  ℤ[i] := ⟨add⟩
    instance : has_mul  ℤ[i] := ⟨mul⟩
    instance : has_neg  ℤ[i] := ⟨neg⟩

    def mk (x y : ℤ) : ℤ[i] := (x, y)
    def re (w : ℤ[i]) : ℤ := w.1
    def im (w : ℤ[i]) : ℤ := w.2

    theorem re_mk (x y : ℤ) : re (mk x y) = x := rfl

    theorem im_mk (x y : ℤ) : im (mk x y) = y := rfl

    theorem mk_re_im (z : ℤ[i]): mk (re z) (im z) = z :=
    by { cases z, refl }

    theorem re_add (w z : ℤ[i]) : re (w + z) = re w + re z :=
    rfl

    theorem im_add (w z : ℤ[i]) : im (w + z) = im w + im z :=
    rfl

    theorem re_mul (w z : ℤ[i]) : re (w * z) = re w * re z - im w * im z :=
    rfl

    theorem im_mul (w z : ℤ[i]) : im (w * z) = re w * im z + im w * re z :=
    rfl

    theorem re_neg (w : ℤ[i]) : re (-w) = - re w :=
    rfl

    theorem im_neg (w : ℤ[i]) : im (-w) = - im w :=
    rfl

    theorem re_zero : re 0 = 0 := rfl

    theorem im_zero : im 0 = 0 := rfl

    theorem re_one : re 1 = 1 := rfl

    theorem im_one : im 1 = 0 := rfl

    theorem re_ii : re ii = 0 := rfl

    theorem im_ii : im ii = 1 := rfl

    attribute [simp] re_add im_add re_mul im_mul re_neg im_neg
      re_zero im_zero re_one im_one re_ii im_ii re_ii im_ii

    @[ext] theorem ext {z w : ℤ[i]}
      (h1 : re z = re w) (h2 : im z = im w) : z = w :=
    begin
      cases z with z1 z2,
      cases w with w1 w2,
      simp [re, im, *] at *
    end

    -- BEGIN
    instance : comm_ring gaussian_integer :=
    begin
      refine_struct {
        zero := (0 : gaussian_integer),
        add := (+),
        neg := has_neg.neg,
        one := 1,
        mul := (*),
        ..};
      intros; ext; simp; ring
    end

    variables x y : ℤ[i]

    example : (37 : gaussian_integer) * 37 = 1369 :=
    by norm_num

    example : (x - y)^2 = x^2 - 2*x*y + y^2 :=
    by ring
    -- END

    end gaussian_integer

.. TODO: reference to later chapter

We encourage you to play around with the ring structure on the
Gaussian integers and do some ring calculations on your own.
We will explain ``refine_struct`` and ``instance`` in a later
chapter on algebraic reasoning.
For now, the take-home message is that in type theory we can
construct and define new types,
and, when we do,
these types support notation, special-purpose tactics, and automation.

For another example of the use of cartesian products, the following
snippet defines the function :math:`f : (x, y) \mapsto (x + y)^2 + x`
and shows that it is injective. Finish off the proof.

.. code-block:: lean

    import tactic.linarith
    import data.nat.gcd

    open function

    def f (p : ℕ × ℕ) : ℕ := (p.1 + p.2)^2 + p.1

    theorem aux {x y x' y' : ℕ} (h : (x + y)^2 + x ≤ (x' + y')^2 + x') :
      x + y ≤ x' + y' :=
    begin
      contrapose! h,
      have h1 : x' + y' + 1 ≤ x + y := h,
      calc
        (x' + y')^2 + x' ≤ (x' + y')^2 + (x' + y') : by linarith
        ... = (x' + y' + 1) * (x' + y')            : by ring
        ... ≤ (x + y) * (x' + y')                  :
                mul_le_mul_of_nonneg_right h1 (zero_le _)
        ... < (x + y)^2                            :
                by { rw [nat.pow_two, mul_lt_mul_left],
                     exact h,
                     linarith }
        ... ≤ (x + y)^2 + x                        : by linarith
    end

    theorem inj_f : injective f :=
    begin
      intros p q h,
      dsimp [f] at h,
      have : p.1 + p.2 = q.1 + q.2,
      { sorry },
      rw this at h,
      have : p.1 = q.1,
      { sorry },
      have : p.2 = q.2,
      { sorry },
      ext; assumption
    end

.. solution
      have : p.1 + p.2 = q.1 + q.2,
      { apply le_antisymm; apply aux; rw h },
      rw this at h,
      have : p.1 = q.1,
      { linarith },
      have : p.2 = q.2,
      { linarith },
      ext; assumption

.. TODO: another reference to a later chapter,
   this time, a "numbers" chapter.

An alternative is to define :math:`f : (x, y) \mapsto 2^x 3^y`,
which is also injective.
Neither of these functions is surjective, however.
For a bijection, we can use *Cantor's pairing function*,
:math:`f : (x, y) \mapsto (x + y) (x + y + 1) / 2 + x`,
but proving that it is a bijection is challenging.
It requires an natural-number valued square root function
that is already defined in the library:

.. code-block:: lean

    import data.nat.sqrt

    open nat

    example (n : ℕ) : (sqrt n)^2 ≤ n :=
    by { rw nat.pow_two, exact nat.sqrt_le n }

    example (n : ℕ) : n < (sqrt n + 1)^2 :=
    by { rw nat.pow_two, exact nat.lt_succ_sqrt n }

But is also requires reasoning about division and parity
on the natural numbers.
We will say more about calculations like this in a later chapter.

We constructed the Gaussian integers as a cartesian product
of the integers.
Lean provides many other ways of defining new types.
One way is to carve a type out of a larger type using
a *subtype* construction.
For example, Lean's library defines a type ``pnat`` of
positive natural numbers:

.. code-block:: lean

    def pnat : Type := { n : ℕ // n > 0 }

An element ``x`` of this type consists of a natural number,
``x.val``,
and a proof ``x.prop`` that ``x.val`` has the property
``x.val > 0``.
The two pieces of data can be put together with
the function ``subtype.mk,``
known as the *constructor* for the subtype.
Two elements of the subtype are equal if and only if
their values are equal.

.. code-block:: lean

    import tactic

    variables x y : pnat

    #check x.val
    #check x.prop

    example : pnat := subtype.mk 5 (by norm_num)

    example : pnat := ⟨5, by norm_num⟩

    example (h : x.val = y.val) : x = y :=
    by { ext, apply h }

We will say more about subtypes later on.

.. TODO: I added a discussion of subtypes because Johan
.. asked for it. But giving all the details is a pain
.. in the neck. For example, to give examples with ``pnat``,
.. we need to talk about coercions, etc. So we should probably
.. save this for later, and maybe delete the whole discussion
.. of subtypes.

.. Defining a new type like ``pnat`` incurs some overhead,
.. because it means we have to mediate between the natural
.. numbers and the new type.
.. But it can be helpful when there are natural operations
.. on the new type that make it a useful domain of objects
.. in its own right.
.. For example, if we define addition and multiplication on
.. ``pnat``,
.. we can calculate with positive natural numbers
.. without having to prove over and over that they positive.

.. The example below defines addition on ``pnat`` and shows that
.. it is commutative.

.. .. code-block:: lean

..     import data.pnat.basic

..     namespace pnat

..     def add : pnat → pnat → pnat
..     | ⟨m, mpos⟩ ⟨n, npos⟩ := ⟨m + n, add_pos mpos npos⟩

..     @[simp] theorem val_add (x y : pnat) :
..     (↑(add x y) : ℕ) = ↑x + ↑y :=
..     by { cases x, cases y, refl }

..     theorem add_comm (x y : pnat) : add x y = add y x :=
..     by { ext, simp [add_comm] }

..     end pnat

.. (If we use something like this, we can ask the user to define
.. nnreal as an exercise.)
