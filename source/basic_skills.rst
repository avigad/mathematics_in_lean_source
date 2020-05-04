.. _basic_skills:

Basic Skills
============

This chapter is designed to introduce you to the nuts and
bolts of mathematical reasoning in Lean: calculating,
applying lemmas and theorems, and carrying out proof
by induction.


.. _calculating:

Calculating
-----------

We generally learn to carry out mathematical calculations
without thinking of them as proofs.
But when we justify each step in a calculation,
as Lean requires us to do,
the net result is a proof that the left-hand side of the calculation
is equal to the right-hand side.

In Lean, stating a theorem is tantamount to stating a goal,
namely, the goal of proving the theorem.
Lean provides the ``rewrite`` tactic, abbreviated ``rw``,
to replace the left-hand side of an identity by the right-hand side
in the goal. If ``a``, ``b``, and ``c`` are real numbers,
``mul_assoc a b c``  is the identity ``a * b * c = a * (b * c)``
and ``mul_comm a b`` is the identity ``a * b = b * a``.
In Lean, multiplication associates to the left,
so the left-hand side of ``mul_assoc`` could also be written ``(a * b) * c``.
However, it is generally good style to be mindful of Lean's
notational conventions and leave out parentheses when Lean does as well.

Let's try out ``rw``.

.. code-block:: lean

    import data.real.basic

    example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
    begin
      rw mul_comm a b,
      rw mul_assoc b a c
    end

As you move your cursor past each step of the proof,
you can see the goal of the proof change.
The ``import`` line at the beginning of the example
imports the theory of the real numbers from ``mathlib``.
For the sake of brevity,
we generally suppress information like this when it
is repeated from example to example.
Clicking the ``try me!`` button displays all the
example as it is meant to be processed and checked by Lean.

Incidentally, you can type the ``ℝ`` character as ``\R`` or ``\real``
in the VS Code editor.
The symbol doesn't appear until you hit space or the tab key.
If you hover over a symbol when reading a Lean file,
VS Code will show you the syntax that can be used to enter it.
If your keyboard does not have a backslash,
you can change the leading character by changing the
``lean.input.leader`` setting in VS Code.

Try proving these identities,
in each case replacing ``sorry`` by a tactic proof.
With the ``rw`` tactic, you can use a left arrow to reverse an identity.
For example, ``rw ← mul_assoc a b c``
replaces ``a * (b * c)`` by ``a * b * c`` in the current goal.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
    begin
      sorry
    end

    example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
    begin
      sorry
    end
    -- END

You can also use identities like ``mul_assoc`` and ``mul_comm`` without arguments.
In this case, the rewrite tactic tries to match the left-hand side with
an expression in the goal,
using the first pattern it finds.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c : ℝ) : a * b * c = b * c * a :=
    begin
      rw mul_assoc,
      rw mul_comm
    end
    -- END

You can also provide *partial* information.
For example, ``mul_comm a`` matches any pattern of the form
``a * ?`` and rewrites it to ``? * a``.
Try doing the first of these examples without
providing any arguments at all,
and the second with only one argument.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c : ℝ) : a * (b * c) = b * (c * a) :=
    begin
      sorry
    end

    example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
    begin
      sorry
    end
    -- END

In the Lean editor mode,
when a cursor is in the middle of a tactic proof,
Lean reports on the current *proof state*.
A typical proof state in Lean might look as follows:

.. code-block::

    1 goal
    x y : ℕ,
    h₁ : prime x,
    h₂ : ¬even x,
    h₃ : y > x
    ⊢ y ≥ 4

The lines before the one that begins with ``⊢`` denote the *context*:
they are the objects and assumptions currently at play.
In this example, these include two objects, ``x`` and ``y``,
each a natural number.
They also include three assumptions,
labelled ``h₁``, ``h₂``, and ``h₃``.
In Lean, everything in a context is labelled with an identifier.
You can type these subscripted labels as ``h\1``, ``h\2``, and ``h\3``,
but any legal identifiers would do:
you can use ``h1``, ``h2``, ``h3`` instead,
or ``foo``, ``bar``, and ``baz``.
The last line represents the *goal*,
that is, the fact to be proved.
Sometimes people use *target* for the fact to be proved,
and *goal* for the combination of the context and the target.
In practice, the intended meaning is usually clear.

You an also use ``rw`` with facts from the local context.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
      a * (b * e) = c * (d * f) :=
    begin
      rw h',
      rw ←mul_assoc,
      rw h,
      rw mul_assoc
    end
    -- END

Try these:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c d e f : ℝ) (h : b * c = e * f) :
      a * b * c * d = a * e * f * d :=
    begin
      sorry
    end

    example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
    begin
      sorry
    end
    -- END

For the second one, you can use the the theorem ``sub_self``,
where ``sub_self a`` is the identity ``a - a = 0``.

We now introduce some useful features of Lean.
First, multiple rewrite commands can be carried out
with a single command,
by listing the relevant identities within square brackets.
Second, when a tactic proof is just a single command,
we can replace the ``begin ... end`` block with a ``by``.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
      a * (b * e) = c * (d * f) :=
    begin
      rw [h', ←mul_assoc, h, mul_assoc]
    end

    example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
      a * (b * e) = c * (d * f) :=
    by rw [h', ←mul_assoc, h, mul_assoc]
    -- END

You still see the incremental progress by placing the cursor after
a comma in any list of rewrites.

Another trick is that we can declare variables once and forall outside
an example or theorem.
When Lean sees them mentioned in the statement of the theorem,
it includes them automatically.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    variables a b c d e f : ℝ

    example (h : a * b = c * d) (h' : e = f) :
      a * (b * e) = c * (d * f) :=
    by rw [h', ←mul_assoc, h, mul_assoc]
    -- END

We can delimit the scope of the declaration by putting it
in a ``section ... end`` block.
Finally, Lean provides us with a means of checking and expression
and determining its type:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    section
    variables a b c : ℝ

    #check a
    #check a + b
    #check (a : ℝ)
    #check mul_comm a b
    #check (mul_comm a b : a * b = b * a)
    #check mul_assoc c a b
    #check mul_comm a
    #check mul_comm
    #check @mul_comm

    end
    -- END

The ``#check`` command works for both objects and facts.
In response to the command ``#check a``, Lean reports that ``a`` has type ``ℝ``.
In response to the command ``#check mul_comm a b``,
Lean reports that ``mul_comm a b`` is a proof of the fact ``a + b = b + a``.
The command ``#check (a : ℝ)`` states our expectation that the
type of ``a`` is ``ℝ``,
and Lean will raise an error if that is not the case.
We will explain the output of the last three ``#check`` command later,
but in the meanwhile, you can take a look at them,
and experiment with some ``#check`` commands of your own.

Let's try some more examples. The theorem ``two_mul a`` says
that ``a + a = 2 * a``. The theorems ``add_mul`` and ``mul_add``
express the distributivity of multiplication over addition,
and the theorem ``add_assoc`` expresses the associativity of addition.
Use the ``#check`` command to see the precise statements.

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    begin
      rw [mul_add, add_mul, add_mul],
      rw [←add_assoc, add_assoc (a * a)],
      rw [mul_comm b a, ←two_mul]
    end
    -- END

Whereas it is possible to figure out what it going on in this proof
by stepping through it in the editor,
it is hard to read on its own.
Lean provides a more structured way of writing proofs like this
using the ``calc`` keyword.

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
      (a + b) * (a + b)
          = a * a + b * a + (a * b + b * b) :
              by rw [mul_add, add_mul, add_mul]
      ... = a * a + (b * a + a * b) + b * b :
              by rw [←add_assoc, add_assoc (a * a)]
      ... = a * a + 2 * (a * b) + b * b     :
              by rw [mul_comm b a, ←two_mul]
    -- END

Notice that there is no more ``begin ... end`` block:
an expression that begins with ``calc`` is a *proof term*.
A ``calc`` expression can also be used inside a tactic proof,
but Lean interprets it as the instruction to use the resulting
proof term to solve the goal exactly.

The ``calc`` syntax is finicky: the dots and colons and justification
have to be in the format indicated above.
Lean ignores whitespace like spaces, tabs, and returns,
so you have some flexibility to make the calculation look more attractive.
One way to write a ``calc`` proof is to outline it first
using the ``sorry`` tactic for justification,
make sure Lean accepts the expression modulo these,
and then justify the individual steps using tactics.

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
      (a + b) * (a + b)
          = a * a + b * a + (a * b + b * b) :
        begin
          sorry
        end
      ... = a * a + (b * a + a * b) + b * b : by sorry
      ... = a * a + 2 * (a * b) + b * b     : by sorry
    -- END

Try proving the following identity using both a pure ``rw`` proof
and a more structured ``calc`` proof:

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
    sorry
    -- END

The following exercise is a little more challenging.
You can use the theorems listed underneath.

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
    begin
      sorry
    end

    #check pow_two a
    #check mul_sub a b c
    #check add_mul a b c
    #check add_sub a b c
    #check sub_sub a b c
    #check add_zero a
    -- END

We can also perform rewriting in an assumption in the context.
For example, ``rw mul_comm a b at hyp`` replaces ``a*b`` by ``b*a``
in the assumption ``hyp``.

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
      c = 2 * a * d :=
    begin
      rw hyp' at hyp,
      rw mul_comm d a at hyp,
      rw ← two_mul (a*d) at hyp,
      rw ← mul_assoc 2 a d at hyp,
      exact hyp
    end
    -- END

In the last step, the ``exact`` tactic can use ``hyp`` to solve the goal
because at that point ``hyp`` matches the goal exactly.

We close this section by noting that ``mathlib`` provides a
useful bit of automation with a ``ring`` tactic,
which is designed to prove identities in any ring.

.. code-block:: lean

    import data.real.basic

    variables a b c : ℝ

    -- BEGIN
    example : (c * b) * a = b * (a * c) :=
    by ring

    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    by ring

    example : (a + b) * (a - b) = a^2 - b^2 :=
    by ring

    example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
      c = 2 * a * d :=
    begin
      rw [hyp, hyp'],
      ring
    end
    -- END

The ``ring`` tactic is imported indirectly when we
import ``data.real.basic``,
but we will see in the next section that it can be used
for calculations on structures other than the real numbers.
It can be imported explicitly with the command
``import tactic``.


.. _proving_identities_in_algebraic_structures:

Proving Identities in Algebraic Structures
------------------------------------------

Mathematically, a ring consists of a set, :math:`R`,
operations :math:`+` :math:`\times`, and constants :math:`0`
and :math:`1`, and an operation :math:`x \mapsto -x` such that:

* :math:`R` with :math:`+` is an *abelian group*, with :math:`0`
  as the additive identity and negation as inverse.
* Multiplication is associative with identity :math:`1`,
  and multiplication distributes over addition.

In Lean, with base our algebraic structures on *types* rather than sets.
Modulo this difference, we can take the ring axioms to be as follows:

.. code-block:: lean

    variables (R : Type*) [comm_ring R]

    #check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
    #check (add_comm : ∀ a b : R, a + b = b + a)
    #check (zero_add : ∀ a : R, 0 + a = a)
    #check (add_left_neg : ∀ a : R, -a + a = 0)
    #check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
    #check (mul_one : ∀ a : R, a * 1 = a)
    #check (one_mul : ∀ a : R, 1 * a = a)
    #check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
    #check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

You will learn more about the square brackets in the first line later,
but for the time being,
suffice it to say that the declaration gives us a type, ``R``,
and a ring structure on ``R``.
Lean then allows us to use generic ring notation with elements of ``R``,
and to make use of a library of theorems about rings.

The names of some of the theorems should look familiar:
they are exactly the ones we used to calculate with the real numbers
in the last section.
Lean is good not only for proving things about concrete mathematical
structures like the natural numbers and the integers,
but also for proving things about abstract structures,
characterized axiomatically, like rings.
Moreover, Lean supports *generic reasoning* about
both abstract and concrete structures,
and can be trained to recognized appropriate instances.
So any theorem about rings can be applied to concrete rings
like the integers, ``ℤ``, the rational numbers,  ``ℚ``,
and the complex numbers ``ℂ``.
It can also be applied to any instance of an abstract
structure that extends rings,
such as any *ordered ring* or any *field*.

Not all important properties of the real numbers hold in an
arbitrary ring, however.
For example, multiplication on the real numbers
is commutative,
but that does not hold in general.
If you have taken a course in linear algebra,
you will recognize that, for every :math:`n`,
the :math:`n` by :math:`n` matrices of real numbers
for a ring in which commutativity fails. If we declare ``R`` to be a
*commutative* ring, in fact, all the theorems
in the last section continue to hold when we replace
``ℝ`` by ``R``.

.. code-block:: lean

    import tactic
    variables (R : Type*) [comm_ring R]
    variables a b c d : R

    example : (c * b) * a = b * (a * c) :=
    by ring

    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    by ring

    example : (a + b) * (a - b) = a^2 - b^2 :=
    by ring

    example (hyp : c = d * a + b) (hyp' : b = a * d) :
      c = 2 * a * d :=
    begin
      rw [hyp, hyp'],
      ring
    end

We leave it to you to check that all the other proofs go through unchanged.

The goal of this section is to strengthen the skills
you have developed in the last section
and apply them to reasoning axiomatically about rings.
We will start with the axioms listed above,
and use them to derive other facts.
Most of the facts we prove are already in ``mathlib``.
We will give the versions we prove the same names
to help you learn the contents of the library
as well as the naming conventions.
To avoid error messages from Lean,
we will put our versions in a new *namespace*
called ``my_ring.``

The next example shows that we do not need ``add_zero`` or ``add_right_neg``
as ring axioms, because they follow from the other axioms.

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    theorem add_zero (a : R) : a + 0 = a :=
    by rw [add_comm, zero_add]

    theorem add_right_neg (a : R) : a + -a = 0 :=
    by rw [add_comm, add_left_neg]

    end my_ring

    #check @my_ring.add_zero
    #check @add_zero

The net effect is that we can temporarily reprove a theorem in the library,
and then go on using the library version after that.
But don't cheat!
In the exercises that follow, take care to use only the
general facts about rings that we have proved earlier in this section.

(If you are paying careful attention, you may have noticed that we
changed the round brackets in ``(R : Type*)`` for
curly brackets in ``{R : Type*}``.
This declares ``R`` to be an *implicit argument*.
We will explain what this means in a moment,
but don't worry about it in the meanwhile.)

Here is a useful theorem:

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b :=
    by rw [←add_assoc, add_left_neg, zero_add]
    -- END

    end my_ring

Prove the companion version:

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem neg_add_cancel_right (a b : R) : (a + b) + -b = 0 :=
    sorry
    -- END

    end my_ring

Use these to prove the following:

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
    sorry

    theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
    sorry
    -- END

    end my_ring

If you are clever, you can do each of them with three rewrites.

We can now explain the use of the curly braces.
Imagine you are in a situation where you have ``a``, ``b``, and ``c``
in your context,
as well as a hypothesis ``h : a + b = a + c``,
and you would like to draw the conclusion ``b = c``.
In Lean, you can apply a theorem to hypotheses and facts just
the same way that you can apply them the objects,
so you might think that ``add_left_cancel a b c h`` is a
proof of the fact ``b = c``.
But notice that explicitly writing ``a``, ``b``, and ``c``
is redundant, because the hypothesis ``h`` makes it clear that
those are the objects we have in mind.
In this case, typing a few extra characters is not onerous,
but if we wanted to apply ``add_left_cancel`` to more complicated expressions,
writing them would be tedious.
In cases like these,
Lean allows us to mark arguments as *implicit*,
meaning that they are supposed to be left out and inferred by other means,
such as later arguments and hypotheses.
The curly brackets in ``{a b c : R}`` do exactly that.
So, given the statement of the theorem above,
the correct expression is simply ``add_left_cancel h``.

To illustrate, let's show that ``a * 0 = 0``
follows from the ring axioms.

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem mul_zero (a : R) : a * 0 = 0 :=
    begin
      have h : a * 0 + a * 0 = a * 0 + 0,
      { rw [←mul_add, add_zero, add_zero] },
      rw add_left_cancel h
    end
    -- END

    end my_ring

We have used a new trick!
If you step through the proof,
you can see what is going on.
The ``have`` tactic introduces a new goal,
``a * 0 + a * 0 = a * 0 + 0``,
with the same context as the original goal.
In the next line, we could have omitted the curly brackets,
which serve as an inner ``begin ... end`` pair.
Using them promotes a modular style of proof:
Here the curly brackets could be omitted,
the part of the proof inside the brackets establishes the goal
that was introduced by the ``have``.
After that, we are back to proving the original goal,
except a new hypothesis ``h`` has been added:
having proved it, we are now free to use it.
At this point, the goal is exactly the result of ``add_left_cancel h``.
We could equally well have closed the proof with
``apply add_left_cancel h`` or ``exact add_left_cancel h``.
We will discuss ``apply`` and ``exact`` in the next section.

Remember that multiplication is not assumed to be commutative,
so the following theorem also requires some work.

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem zero_mul (a : R) : 0 * a  = 0 :=
    sorry
    -- END

    end my_ring

By now, you should also be able replace each ``sorry`` in the next
exercise with a proof,
still using only facts about rings that we have
established in this section.

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
    sorry

    theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b :=
    sorry

    theorem neg_zero : (-0 : R) = 0 :=
    begin
      apply neg_eq_of_add_eq_zero,
      rw add_zero
    end

    theorem neg_neg (a : R) : -(-a) = a :=
    sorry
    -- END

    end my_ring

We had to use the annotation ``(-0 : R)`` instead of ``0`` in the third theorem
because without specifying ``R``
it is impossible for Lean to infer which ``0`` we have in mind.

In Lean, subtraction in a ring is defined to be
addition of the additive inverse.

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem sub_eq_add_neg (a b : R) : a - b = a + -b :=
    rfl

    example (a b : R) : a - b = a + -b :=
    by reflexivity
    -- END

    end my_ring

The proof term ``rfl`` is short for ``reflexivity``.
Presenting it as a proof of ``a - b = a + -b`` forces Lean
to unfold the definition and recognize both sides as being the same.
The ``reflexivity`` tactic, which can be abbreviated as ``refl``,
does the same.
This is an instance of what is known as a *definitional equality*
in Lean's underlying logic.
This means that not only can one rewrite with ``sub_eq_add_neg``
to replace ``a - b = a + -b``,
but in some contexts you can use the two sides of the equation
interchangeably.
For example, you now have enough information to prove the theorem
``self_sub`` from the last section:

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem self_sub (a : R) : a - a = 0 :=
    sorry
    -- END

    end my_ring

Extra points if you do it two different ways:
once using ``rw``,
and once using either ``apply`` or ``exact``.

For another example of definitional equality,
Lean knows that ``1 + 1 = 2`` holds in any ring.
With a bit of cleverness,
you can use that to prove the theorem ``two_mul`` from
the last section:

.. code-block:: lean

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
    by refl

    theorem two_mul (a : R) : 2 * a = a + a :=
    sorry
    -- END

    end my_ring

We close this section by noting that some of the facts about
addition and negation that we established above do not
need the full strength of the ring axioms, or even
commutativity of addition. The weaker notion of a *group*
can be axiomatized as follows:

.. code-block:: lean

    variables (A : Type*) [add_group A]

    #check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
    #check (zero_add : ∀ a : A, 0 + a = a)
    #check (add_left_neg : ∀ a : A, -a + a = 0)

It is conventional to use additive notation when a group the
operation is commutative,
and multiplicative notation otherwise.
So Lean defines a multiplicative version as well as the
additive version (and also their abelian variants,
``add_comm_group`` and ``comm_group``).

.. code-block:: lean

    variables (G : Type*) [group G]

    #check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
    #check (one_mul : ∀ a : G, 1 * a = a)
    #check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

If you are feeling cocky, try proving the following facts about
groups, using only these axioms.
You will need to prove a number of helper lemmas along the way.
The proofs we have carried out in this section provide some hints.

.. code-block:: lean

    variables {G : Type*} [group G]

    #check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
    #check (one_mul : ∀ a : G, 1 * a = a)
    #check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

    namespace my_group

    theorem one_mul (a : G) : 1 * a = a :=
    sorry

    theorem one_right_inv (a : G) : a * a⁻¹ = 1 :=
    sorry

    theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
    sorry

    end my_group


.. _using_theorems_and_lemmas:

Using Theorems and Lemmas
-------------------------

This section will introduce ``apply`` and friends,
and prove some theorems that go beyond equations.

Examples will use ``≤``, ``dvd``, ``gcd`` and ``lcm`` on ``nat``,
``⊆`` on sets, and so on.

Basically, we'll theorems with ``∀`` and ``→`` to prove atomic statements.
Even with these restrictions, we can prove some nontrivial theorems,
like the fact that ``gcd`` distributes over ``lcm``,
or ``a * b ≤ (a^2 + b^2) / 2``.

We'll also demonstrate the use of calc for inequalities.


.. _proving_facts_about_algebraic_structures:

Proving Facts about Algebraic Structures
----------------------------------------

As we did in section :numref:`proving_identities_in_algebraic_structures`,
this section will apply skills from the last section in particular algebraic structures.

Examples may include:

* lattices: lubs, glbs, then theorems about distributivity, etc.

* ordered rings

* simple facts about metric spaces from axioms

* derive different versions of the triangle inequality from axioms for norms


.. _induction:

Induction
---------

We'll run through addition, multiplication, and exponentiation, à la the natural numbers game.

Then we'll do fibonacci numbers or something like that. By now, students should be able to prove interesting identities.


The AM-QM Inequality
--------------------

We'll try taking the students through a proof of this,
or something else that puts everything together:
induction, inequalities, calculations,
and theorems from the library.
