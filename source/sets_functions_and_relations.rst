.. _sets_functions_and_relations:

Sets, Functions, and Relations
==============================

The vocabulary of sets, relations, and functions provides a uniform
language for carrying out constructions in all the branches of
mathematics.
Since functions and relations can be defined in terms of sets,
axiomatic set theory can be used as a foundation for mathematics.

Lean's foundation is based instead on the primitive notion of a *type*,
and it includes ways of defining functions between types.
Every expression in Lean has a type:
there are natural numbers, real numbers, functions from reals to reals,
groups, vector spaces, and so on.
Some expressions *are* types,
which is to say,
their type is ``Type``.
Lean and mathlib provide ways of defining new types,
and ways of defining objects of those types.

Conceptually, you can think of a type as just a set of objects.
Requiring every object to have a type has some advantages.
For example, it makes it possible to overload notation like ``+``,
and it sometimes makes input less verbose
because Lean can infer a lot of information from
an object's type.
The type system also enables Lean to flag errors when you
apply a function to the wrong number of arguments,
or apply a function to arguments of the wrong type.

Lean's library does define elementary set-theoretic notions.
In contrast to set theory,
in Lean a set is always a set of objects of some type,
such as a set natural numbers or a set of functions
from real numbers to real numbers.
The distinction between types and set takes some getting used to,
but this chapter will take you through the essentials.


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
Using the ``rfl`` proof term or ``refl`` tactic
causes Lean to unfold the definition and try to reduce
both sides until they are the same.
The theorem ``re_mk`` can be proved that way because
``re (mk x y)`` unfolsd to ``(x, y).1``,
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

.. _sets:

Sets
----

If ``α`` is any type, the type ``set α`` consists of sets
of elements of ``α``.
This type supports the usual set-theoretic operations and relations.
For example, ``s ⊆ t`` says that ``s`` is a subset of ``t``,
``s ∩ t`` denotes the intersection of ``s`` and ``t``,
and ``s ∪ t`` denotes their union.
The subset relation can be typed with ``\ss`` or ``\sub``,
intersection can be typed with ``\i`` or ``\cap``,
and union can be typed with ``\un`` or ``\cup``.
The library also defines the set ``univ``,
which consists of all the elements of type ``α``,
and the empty set, ``∅``, which can be typed as ``\empty``.

One way to prove things about sets is to use ``rw``
or the simplifier to expand the definitions.
In the second example below, we use ``simp only``
to tell the simplifier to use only the list
of identities we give it,
and not its full database of identities.
Unlike ``rw``, ``simp`` can perform simplifications
inside a universal or existential quantifier.
If you step through the proof,
you can see the effects of these commands.

.. code-block:: lean

    import tactic

    variable {α : Type*}
    variables (s t u : set α)

    open set

    example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
    begin
      rw [subset_def, inter_def, inter_def],
      rw subset_def at h,
      dsimp,
      rintros x ⟨xs, xu⟩,
      exact ⟨h _ xs, xu⟩,
    end

    example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
    begin
      simp only [subset_def, mem_inter_eq] at *,
      rintros x ⟨xs, xu⟩,
      exact ⟨h _ xs, xu⟩,
    end

In this example, we open the ``set`` namespace to have
access to the shorter names for the theorems.
But, in fact, we can delete the calls to ``rw`` and ``simp``
entirely:

.. code-block:: lean

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
    begin
      intros x xsu,
      exact ⟨h xsu.1, xsu.2⟩
    end
    -- END

What is going on here is known as *definitional reduction*:
to make sense of the ``intros`` command and the the anonymous constructors
Lean is forced to expand the definitions.
The following examples also illustrate the phenomenon:

.. code-block:: lean

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
    λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

    example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
    by exact λ x ⟨xs, xu⟩, ⟨h xs, xu⟩
    -- END

Due to a quirk of how Lean processes its input,
the first example fails if we replace ``theorem foo`` with ``example``.
This illustrates the pitfalls of relying on definitional reduction
too heavily.
It is often convenient,
but sometimes we have to fall back on unfolding definitions manually.

To deal with unions, we can use ``set.union_def`` and ``set.mem_union``.
Since ``x ∈ s ∪ t`` unfolds to ``x ∈ s ∨ x ∈ t``,
we can also use the ``cases`` tactic to force a definitional reduction.

.. code-block:: lean

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
    begin
      intros x hx,
      have xs : x ∈ s := hx.1,
      have xtu : x ∈ t ∪ u := hx.2,
      cases xtu with xt xu,
      { left,
        show x ∈ s ∩ t,
        exact ⟨xs, xt⟩ },
      right,
      show x ∈ s ∩ u,
      exact ⟨xs, xu⟩
    end
    -- END

Since intersection binds tighter than union,
the use of parentheses in the expression ``(s ∩ t) ∪ (s ∩ u)``
is unnecessary, but they make the meaning of the expression clearer.
The following is a shorter proof of the same fact:

.. code-block:: lean

    import tactic

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
    begin
      rintros x ⟨xs, xt | xu⟩,
      { left, exact ⟨xs, xt⟩ },
      right, exact ⟨xs, xu⟩
    end
    -- END

As an exercise, try proving the other inclusion:

.. code-block:: lean

    import tactic

    open set

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
    sorry
    -- END

The library also defines set difference, ``s \ t``,
where the backslash is a special unicode character
entered as ``\\``.
The expression ``x ∈ s \ t`` expands to ``x ∈ s ∧ x ∉ t``.
(The ``∉`` can be entered as ``\notin``.)
It can be rewritten manually using ``set.diff_eq`` and ``dsimp``
or ``set.mem_diff``,
but the following two proofs of the same inclusion
show how to avoid using them.

.. code-block:: lean

    import tactic

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s \ t \ u ⊆ s \ (t ∪ u) :=
    begin
      intros x xstu,
      have xs : x ∈ s := xstu.1.1,
      have xnt : x ∉ t := xstu.1.2,
      have xnu : x ∉ u := xstu.2,
      split,
      { exact xs }, dsimp,
      intro xtu, -- x ∈ t ∨ x ∈ u
      cases xtu with xt xu,
      { show false, from xnt xt },
      show false, from xnu xu
    end

    example : s \ t \ u ⊆ s \ (t ∪ u) :=
    begin
      rintros x ⟨⟨xs, xnt⟩, xnu⟩,
      use xs,
      rintros (xt | xu); contradiction
    end
    -- END

Notice that in the second use of ``rintros``,
we need to use parentheses around the disjunctive pattern
``xt | xu`` to get Lean to parse it correctly.
As an exercise, prove the reverse inclusion:

.. code-block:: lean

    import tactic

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s \ (t ∪ u) ⊆ s \ t \ u :=
    sorry
    -- END

.. a solution:
.. example : s \ (t ∪ u) ⊆ s \ t \ u :=
.. begin
..   rintros x ⟨xs, xntu⟩,
..   use xs,
..   { intro xt, exact xntu (or.inl xt) },
..   intro xu,
..   apply xntu (or.inr xu)
.. end

Two prove that two sets are equal,
it suffices to show that every element of one is an element
of the other.
This principle is known as "extensionality,"
and, unsurprisingly,
the ``ext`` tactic is equipped to handle it.

.. code-block:: lean

    import tactic

    open set

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s ∩ t = t ∩ s :=
    begin
      ext x,
      simp only [mem_inter_eq],
      split,
      { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
      rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
    end
    -- END

Once again, deleting the line ``simp only [mem_inter_eq]``
does not harm the proof.
In fact, if you like inscrutable proof terms,
the following one-line proof is for you:

.. code-block:: lean

    import data.set.basic

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s ∩ t = t ∩ s :=
    set.ext $ λ x, ⟨λ ⟨xs, xt⟩, ⟨xt, xs⟩, λ ⟨xt, xs⟩, ⟨xs, xt⟩⟩
    -- END

The dollar sign is a useful syntax:
writing ``f $ ...``
is essentially the same as writing ``f (...)``,
but it saves us the trouble of having to close
a set of parentheses at the end of a long expression.
Here is an even shorter proof,
using the simplifier:

.. code-block:: lean

    import tactic

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s ∩ t = t ∩ s :=
    by ext x; simp [and.comm]
    -- END

An alternative to using ``ext`` is to use
the theorem ``subset.antisymm``
which allows us to prove an equation ``s = t``
between sets by proving ``s ⊆ t`` and ``t ⊆ s``.

.. code-block:: lean

    import tactic

    open set

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s ∩ t = t ∩ s :=
    begin
      apply subset.antisymm,
      { rintros x ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
      rintros x ⟨xt, xs⟩, exact ⟨xs, xt⟩
    end
    -- END

Try finishing this proof term:

.. code-block:: lean

    import data.set.basic

    open set

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s ∩ t = t ∩ s :=
    subset.antisymm sorry sorry
    -- END

Remember that you can replace `sorry` by an underscore,
and when you hover over it,
Lean will show you what it expects at that point.

Here are some set-theoretic identities you might enjoy proving:

.. code-block:: lean

    import tactic

    open set

    variable {α : Type*}
    variables (s t u : set α)

    -- BEGIN
    example : s ∩ (s ∪ t) = s :=
    sorry

    example : s ∪ (s ∩ t) = s :=
    sorry

    example : (s \ t) ∪ t = s ∪ t :=
    sorry

    example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
    sorry
    -- END

When it comes to representing sets,
here is what is going on underneath the hood.
In type theory, a *property* or *predicate* on a type ``α``
is just a function ``P : α → Prop``.
This makes sense:
given ``a : α``, ``P a`` is just the proposition
that ``P`` holds of ``a``.
In the library, ``set α`` is defined to be ``α → Prop`` and ``x ∈ s`` is defined to be ``s x``.
In other words, sets are really properties, treated as objects.

The library also defines set-builder notation.
The expression ``{ y | P y }`` unfolds to ``(λ y, P y)``,
so ``x ∈ { y | P y }`` reduces to ``P x``.
So we can turn the property of being even into the set of even numbers:

.. code-block:: lean

    import data.set.basic data.nat.parity

    open set nat

    def evens : set ℕ := {n | even n}
    def odds :  set ℕ := {n | ¬ even n}

    example : evens ∪ odds = univ :=
    begin
      rw [evens, odds],
      ext n,
      simp,
      apply classical.em
    end

You should step through this proof and make sure
you understand what is going on.
Try deleting the line ``rw [evens, odds]``
and confirm that the proof still works.

As an exercise, prove the following inclusion.
Use ``intro n`` to unfold the definition of subset,
and use the simplifier to reduce the
set-theoretic constructions to logic.
We also recommend using the theorems
``prime.eq_two_or_odd`` and ``even_iff``.

.. code-block:: lean

    import data.nat.prime data.nat.parity tactic

    open set nat

    example : { n | prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
    sorry

.. a solution:
.. example : { n | prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
.. begin
..   intro n,
..   simp,
..   intro nprime,
..   cases prime.eq_two_or_odd nprime with h h,
..   { rw h, intro, linarith },
..   rw [even_iff, h],
..   norm_num
.. end

Indexed unions and intersections are
another important set-theoretic construction.
We can model a sequence :math:`A_0, A_1, A_2, \ldots` of sets of
elements of ``α``
as a function ``A : ℕ → set α``,
in which case ``⋃ i, A i`` denotes their union,
and ``⋂ i, A i`` denotes their intersection.
There is nothing special about the natural numbers here,
so ``ℕ`` can be replaced by any type ``I``
used to index the sets.
The following illustrates their use.

.. code-block:: lean

    import tactic

    open set

    variables α I : Type*
    variables A B : ℕ → set α
    variable  s : set α

    example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
    begin
      ext x,
      simp only [mem_inter_eq, mem_Union],
      split,
      { rintros ⟨xs, ⟨i, xAi⟩⟩,
        exact ⟨i, xAi, xs⟩ },
      rintros ⟨i, xAi, xs⟩,
      exact ⟨xs, ⟨i, xAi⟩⟩
    end

    example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
    begin
      ext x,
      simp only [mem_inter_eq, mem_Inter],
      split,
      { intro h,
        split,
        { intro i,
          exact (h i).1 },
        intro i,
        exact (h i).2 },
      rintros ⟨h1, h2⟩ i,
      split,
      { exact h1 i },
      exact h2 i
    end

Try proving the following identity.
One direction requires classical logic!
We recommend using ``by_cases xs : x ∈ s``
at an appropriate point in the proof.

.. code-block:: lean

    import tactic

    open set

    variables α I : Type*
    variable  A : ℕ → set α
    variable  s : set α

    -- BEGIN
    open_locale classical

    example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
    sorry
    -- END

.. a solution:
.. example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
.. begin
..   ext x,
..   simp only [mem_union, mem_Inter],
..   split,
..   { rintros (xs | xI),
..     { intro i, right, exact xs },
..     intro i, left, exact xI i },
..   intro h,
..   by_cases xs : x ∈ s,
..   { left, exact xs },
..   right,
..   intro i,
..   cases h i,
..   { assumption },
..   contradiction
.. end


.. _functions:

Functions
---------

In Lean, a function ``f : α → β`` is a function between types.
If ``p`` is a set of elements of type ``β``,
the library defines ``preimage f p``, written ``f ⁻¹' p``,
to be ``{ x | f x ∈ p }``.
The expression ``x ∈ f ⁻¹' p`` reduces to ``f x ∈ s``.
This is often convenient, as in the following example:

.. code-block:: lean

    import data.set.function

    variables {α β : Type*}
    variable  f : α → β
    variables u v : set β

    example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
    by { ext, refl }


If ``s`` is a set of elements of type ``α``,
the library also defines ``image f s``,
written ``f '' s``,
to be ``{y | ∃ x, x ∈ s ∧ f x = y}``.
So a hypothesis  ``y ∈ f '' s`` decomposes to a triple
``⟨x, xs, xeq⟩`` with ``x : α`` satisfying the hypotheses ``xs : x ∈ s``
and ``xeq : f x = y``.
The ``rfl`` tag in the ``rintros`` tactic (see :numref:`the_existential_quantifier`) was made precisely
for this sort of situation.

.. code-block:: lean

    import data.set.function

    variables {α β : Type*}
    variable  f : α → β
    variables s t : set α

    -- BEGIN
    example : f '' (s ∪ t) = f '' s ∪ f '' t :=
    begin
      ext y, split,
      { rintros ⟨x, xs | xt, rfl⟩,
        { left, use [x, xs] },
        right, use [x, xt] },
      rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
      { use [x, or.inl xs] },
      use [x, or.inr xt]
    end
    -- END

Notice also that the ``use`` tactic applies ``refl``
to close goals when it can.

Here is another example:

.. code-block:: lean

    import data.set.function

    variables {α β : Type*}
    variable  f : α → β
    variables s t : set α

    -- BEGIN
    example : s ⊆ f ⁻¹' (f '' s) :=
    begin
      intros x xs,
      show f x ∈ f '' s,
      use [x, xs]
    end
    -- END

We can replace the line ``use [x, xs]`` by
``apply mem_image_of_mem f xs`` if we want to
use a theorem specifically designed for that purpose.
But knowing that the image is defined in terms
of an existential quantifier is often convenient.

Here is a long list of set-theoretic identities for
you to enjoy.
You don't have to do all of them at once;
do a few of them,
and set the rest aside for a rainy day.

.. code-block:: lean

    import data.set.function

    open set function

    variables {α β : Type*}
    variable  f : α → β
    variables s t : set α
    variables u v : set β

    -- BEGIN
    example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
    sorry

    example : f '' (f⁻¹' u) ⊆ u :=
    sorry

    example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
    sorry

    example (h : s ⊆ t) : f '' s ⊆ f '' t :=
    sorry

    example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
    sorry

    example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
    sorry

    example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
    sorry

    example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
    sorry

    example : f '' s \ f '' t ⊆ f '' (s \ t) :=
    sorry

    example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
    sorry

    example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
    sorry

    example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
    sorry

    example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
    sorry

    example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
    sorry
    -- END

You might also enjoy looking up for making up some
identities involving indexed unions and proving them.

The fact that in type theory a function is always totally
defined on its domain type
sometimes forces some difficult choices.
For example, if we want to define ``x / y`` and ``log x``
as functions on the reals,
we have to assign a value to the first when ``y`` is ``0``,
and a value to the second for ``x ≤ 0``.
There are ways around this, but they are generally unpleasant.
For example, we can take ``log`` to be defined on
the subtype ``{ x // x > 0 }``,
but then we have to mediate between two different types,
the reals and that subtype.
The strategy generally followed by the Lean library
in these situations is to assign such functions somewhat arbitrary
but convenient values outside their natural domain.
For example, defining ``x / 0`` to be ``0`` means that the
identity ``(x + y) / z = x / 2 + y / z`` holds
for every ``x``, ``y``, and ``z``.
When you see a theorem in the library that uses the
division symbol,
you should be mindful that theorem depends on this
nonstandard definition,
but this generally does not cause problems in practice.
When we need to,
we can restrict the statement of a theorem so that
it does not rely on such values.
For example, if a theorem begins ``∀ x > 0, ...``,
dividing by ``x`` in the body of the statement is not problematic.
Limiting the scope of a quantifier in this way is known
as *relativization*.

For another example of relativization,
the library defines a predicate ``inj_on f s`` to say that
``f`` is injective on ``s``.
It is defined as follows:

.. code-block:: lean

    import data.set.function

    open set

    variables {α β : Type*}
    variables (f : α → β) (s : set α)

    -- BEGIN
    example : inj_on f s ↔
      ∀ {x₁ x₂}, x₁ ∈ s → x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂ :=
    iff.refl _
    -- END

Lean introduces the notation ``∀ x ∈ s, ...``
as an abbreviation for  ``∀ x, x ∈ s → ...``.
It also introduces the notation ``∃ x ∈ s, ...``.
When this expression is used  with ``rintros``, ``use``,
and anonymous constructors,
it behaves roughly the same as ``∃ x, x ∈ s ∧ ...``.

The statement ``injective f`` is provably equivalent
to ``inj_on f univ``.
Similarly, the library defines ``range f`` to be
``{x | ∃y, f y = x}``,
so ``range f`` is provably equal to ``f '' univ``.
This is a common theme in mathlib:
although many properties of functions are defined relative
to their full domain,
there are often relativized versions that restrict
the statements to a subset of the domain type.

Here is are some examples of ``inj_on`` and ``range`` in use:

.. code-block:: lean

    import analysis.special_functions.exp_log

    open set real

    -- BEGIN
    example : inj_on log { x | x > 0 } :=
    begin
      intros x y xpos ypos,
      intro e,   -- log x = log y
      calc
        x   = exp (log x) : by rw exp_log xpos
        ... = exp (log y) : by rw e
        ... = y           : by rw exp_log ypos
    end

    example : range exp = { y | y > 0 } :=
    begin
      ext y, split,
      { rintros ⟨x, rfl⟩,
        apply exp_pos },
      intro ypos,
      use log y,
      rw exp_log ypos
    end
    -- END

Try proving these:

.. code-block:: lean

    import data.real.basic

    open set real

    example : inj_on sqrt { x | x ≥ 0 } :=
    sorry

    example : inj_on (λ x, x^2) { x | x ≥ 0 } :=
    sorry

    example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
    sorry

    example : range (λ x, x^2) = {y | y ≥ 0} :=
    sorry

.. solution to the first:
.. example : inj_on sqrt { x | x ≥ 0 } :=
.. begin
..   intros x y xnonneg ynonneg,
..   intro e,
..   calc
..     x   = (sqrt x)^2 : by rw sqr_sqrt xnonneg
..     ... = (sqrt y)^2 : by rw e
..     ... = y          : by rw sqr_sqrt ynonneg
.. end

To define the inverse of a function ``f : α → β``,
we will use two new ingredients.
First, we need to deal with the fact that
an arbitrary type in Lean may be empty.
To define the inverse to ``f`` at ``y`` when there is
no ``x`` satisfying ``f x = y``,
we want to assign a default value in ``α``.
Adding the annotation ``[inhabited α]`` as a variable
is tantamount to assuming that ``α`` has a
canonical element, which is denoted ``default α``.
Second, in the case where there is more than one ``x``
such that ``f x = y``,
the inverse function needs to *choose* one of them.
This requires an appeal to the *axiom of choice*.
Lean allows various ways of accessing it;
one convenient method is to use the classical ``some``
operator, illustrated below.

.. code-block:: lean

    variables {α : Type*} [inhabited α]

    #check default α

    variables (P : α → Prop) (h : ∃ x, P x)

    #check classical.some h

    example : P (classical.some h) := classical.some_spec _

With these in hand, we can define the inverse function
as follows:

.. code-block:: lean

    import data.set.function

    variables {α β : Type*} [inhabited α]

    noncomputable theory
    open_locale classical

    def inverse (f : α → β) : β → α :=
    λ y : β, if h : ∃ x, f x = y then classical.some h else default α

    theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
      f (inverse f y) = y :=
    begin
      rw inverse, dsimp, rw dif_pos h,
      exact classical.some_spec h
    end

The lines ``noncomputable theory`` and ``open_locale classical``
are needed because we are using classical logic in an essential way.
On input ``y``, the function ``inverse f``
returns some value of ``x`` satisfying ``f x = y`` if there is one,
and a default element of ``α`` otherwise.
The theorem ``inverse_spec`` says that ``inverse f``
meets the first part of this specification.

Don't worry if you do not fully understand how these work.
The theorem ``inverse_spec`` alone should be enough to show
that ``inverse f`` is a left inverse if and only if ``f`` is injective
and a right inverse if and only if ``f`` is surjective.
Look up the definition of ``left_inverse`` and ``right_inverse``
by double-clicking or right-clicking on them in VS Code,
or using the commands ``#print left_inverse`` and ``#print right_inverse``.
Then try to prove the two theorems.
It is tricky!
It helps to have a careful pen-and-paper proof before
you start hacking through the details.
You should be able to prove each of them with about a half-dozen
short lines. If you are looking for an extra challenge,
try to condense each proof to a single-line proof term.

.. code-block:: lean

    import data.set.function

    open set function

    variables {α β : Type*} [inhabited α]

    noncomputable theory
    open_locale classical

    def inverse (f : α → β) : β → α :=
    λ y : β, if h : ∃ x, f x = y then classical.some h else default α

    theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
      f (inverse f y) = y :=
    begin
      rw inverse, dsimp, rw dif_pos h,
      exact classical.some_spec h
    end

    -- BEGIN
    variable  f : α → β

    example : injective f ↔ left_inverse (inverse f) f  :=
    sorry

    example : surjective f ↔ right_inverse (inverse f) f :=
    sorry
    -- END

.. solutions
.. example : injective f ↔ left_inverse (inverse f) f  :=
.. begin
..   split,
..   { intros h y,
..     apply h,
..     apply inverse_spec,
..     use y },
..   intros h x1 x2 e,
..   rw [←h x1, ←h x2, e]
.. end

.. example : injective f ↔ left_inverse (inverse f) f  :=
.. ⟨λ h y, h (inverse_spec _ ⟨y, rfl⟩), λ h x1 x2 e, by rw [←h x1, ←h x2, e]⟩

.. example : surjective f ↔ right_inverse (inverse f) f :=
.. begin
..   split,
..   { intros h y,
..     apply inverse_spec,
..     apply h },
..   intros h y,
..   use (inverse f y),
..   apply h
.. end

.. example : surjective f ↔ right_inverse (inverse f) f :=
.. ⟨λ h y, inverse_spec _ (h _), λ h y, ⟨inverse f y, h _⟩⟩

We close this section with a type-theoretic statement of Cantor's
famous theorem that there is no surjective function from a set
to its power set.
See if you can understand the proof,
and then fill in the two lines that are missing.

.. code-block:: lean

    import data.set.basic

    open function

    variable {α : Type*}

    -- BEGIN
    theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
    begin
      intros f surjf,
      let S := { i | i ∉ f i},
      rcases surjf S with j,
      have h₁ : j ∉ f j,
      { intro h',
        have : j ∉ f j,
          { by rwa h at h' },
        contradiction },
      have h₂ : j ∈ S,
        sorry,
      have h₃ : j ∉ S,
        sorry,
      contradiction
    end
    -- END

.. solutions:
.. from h₁
.. by rwa h at h₁  -- well, we haven't introduced ``rwa`` yet.
