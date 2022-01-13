.. _sets:

Sets
----

.. index:: set operations

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
Given ``x : α`` and ``s : set α``,
the expression ``x ∈ s`` says that ``x`` is a member of ``s``.
Theorems that mention set membership often include ``mem``
in their name.
The expression ``x ∉ s`` abbreviates ``¬ x ∈ s``.
You can type ``∈`` as ``\in`` or ``\mem`` and ``∉`` as ``\notin``.

.. index:: simp, tactics ; simp

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

  example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  begin
    intros x xsu,
    exact ⟨h xsu.1, xsu.2⟩
  end

What is going on here is known as *definitional reduction*:
to make sense of the ``intros`` command and the anonymous constructors
Lean is forced to expand the definitions.
The following examples also illustrate the phenomenon:

.. code-block:: lean

  theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  λ x ⟨xs, xu⟩, ⟨h xs, xu⟩
  
  example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  by exact λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

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

Since intersection binds tighter than union,
the use of parentheses in the expression ``(s ∩ t) ∪ (s ∩ u)``
is unnecessary, but they make the meaning of the expression clearer.
The following is a shorter proof of the same fact:

.. code-block:: lean

  example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
  begin
    rintros x ⟨xs, xt | xu⟩,
    { left, exact ⟨xs, xt⟩ },
    right, exact ⟨xs, xu⟩
  end

As an exercise, try proving the other inclusion:

.. code-block:: lean

  example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
  sorry

It might help to know that when using ``rintros``,
sometimes we need to use parentheses around a disjunctive pattern
``h1 | h2`` to get Lean to parse it correctly.

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

As an exercise, prove the reverse inclusion:

.. code-block:: lean

  example : s \ (t ∪ u) ⊆ s \ t \ u :=
  sorry

To prove that two sets are equal,
it suffices to show that every element of one is an element
of the other.
This principle is known as "extensionality,"
and, unsurprisingly,
the ``ext`` tactic is equipped to handle it.

.. code-block:: lean

  example : s ∩ t = t ∩ s :=
  begin
    ext x,
    simp only [mem_inter_eq],
    split,
    { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
    rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
  end

Once again, deleting the line ``simp only [mem_inter_eq]``
does not harm the proof.
In fact, if you like inscrutable proof terms,
the following one-line proof is for you:

.. code-block:: lean

  example : s ∩ t = t ∩ s :=
  set.ext $ λ x, ⟨λ ⟨xs, xt⟩, ⟨xt, xs⟩, λ ⟨xt, xs⟩, ⟨xs, xt⟩⟩

The dollar sign is a useful syntax:
writing ``f $ ...``
is essentially the same as writing ``f (...)``,
but it saves us the trouble of having to close
a set of parentheses at the end of a long expression.
Here is an even shorter proof,
using the simplifier:

.. code-block:: lean

  example : s ∩ t = t ∩ s :=
  by ext x; simp [and.comm]

An alternative to using ``ext`` is to use
the theorem ``subset.antisymm``
which allows us to prove an equation ``s = t``
between sets by proving ``s ⊆ t`` and ``t ⊆ s``.

.. code-block:: lean

  example : s ∩ t = t ∩ s :=
  begin
    apply subset.antisymm,
    { rintros x ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
    rintros x ⟨xt, xs⟩, exact ⟨xs, xt⟩
  end

Try finishing this proof term:

.. code-block:: lean

  example : s ∩ t = t ∩ s :=
  subset.antisymm sorry sorry

Remember that you can replace `sorry` by an underscore,
and when you hover over it,
Lean will show you what it expects at that point.

Here are some set-theoretic identities you might enjoy proving:

.. code-block:: lean

  example : s ∩ (s ∪ t) = s :=
  sorry
  
  example : s ∪ (s ∩ t) = s :=
  sorry
  
  example : (s \ t) ∪ t = s ∪ t :=
  sorry
  
  example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
  sorry

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

In fact, set-builder notation is used to define

- ``s ∩ t`` as ``{x | x ∈ s ∧ x ∈ t}``,
- ``s ∪ t`` as ``{x | x ∈ s ∨ x ∈ t}``,
- ``∅`` as ``{x | false}``, and
- ``univ`` as ``{x | true}``.

We often need to indicate the type of ``∅`` and ``univ``
explicitly,
because Lean has trouble guessing which ones we mean.
The following examples show how Lean unfolds the last
two definitions when needed. In the second one,
``trivial`` is the canonical proof of ``true`` in the library.

.. code-block:: lean

  example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
  h
  
  example (x : ℕ) : x ∈ (univ : set ℕ) :=
  trivial

As an exercise, prove the following inclusion.
Use ``intro n`` to unfold the definition of subset,
and use the simplifier to reduce the
set-theoretic constructions to logic.
We also recommend using the theorems
``nat.prime.eq_two_or_odd`` and ``nat.even_iff``.

.. code-block:: lean

  example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
  sorry

Be careful: it is somewhat confusing that the library has multiple versions
of the predicate ``prime``.
The most general one makes sense in any commutative monoid with a zero element.
The predicate ``nat.prime`` is specific to the natural numbers.
Fortunately, there is a theorem that says that in the specific case,
the two notions agree, so you can always rewrite one to the other.

.. code-block:: lean

  #print prime
  #print nat.prime
  
  example (n : ℕ) : prime n ↔ nat.prime n := nat.prime_iff.symm
  
  example (n : ℕ) (h : prime n) : nat.prime n :=
  by { rw nat.prime_iff, exact h }

.. index:: rwa, tactics ; rwa
The `rwa` tactic follows a rewrite with the assumption tactic.
.. index:: bounded quantifiers

Lean introduces the notation ``∀ x ∈ s, ...``,
"for every ``x`` in ``s`` .,"
as an abbreviation for  ``∀ x, x ∈ s → ...``.
It also introduces the notation ``∃ x ∈ s, ...,``
"there exists an ``x`` in ``s`` such that .."
These are sometimes known as *bounded quantifiers*,
because the construction serves to restrict their significance
to the set ``s``.
As a result, theorems in the library that make use of them
often contain ``ball`` or ``bex`` in the name.
The theorem ``bex_def`` asserts that ``∃ x ∈ s, ...`` is equivalent
to ``∃ x, x ∈ s ∧ ...,``
but when they are used with ``rintros``, ``use``,
and anonymous constructors,
these two expressions behave roughly the same.
As a result, we usually don't need to use ``bex_def``
to transform them explicitly.
Here is are some examples of how they are used:

.. code-block:: lean

  variables (s t : set ℕ)
  
  example (h₀ : ∀ x ∈ s, ¬ even x) (h₁ : ∀ x ∈ s, prime x) :
    ∀ x ∈ s, ¬ even x ∧ prime x :=
  begin
    intros x xs,
    split,
    { apply h₀ x xs },
    apply h₁ x xs
  end
  
  example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
    ∃ x ∈ s, prime x :=
  begin
    rcases h with ⟨x, xs, _, prime_x⟩,
    use [x, xs, prime_x]
  end

See if you can prove these slight variations:

.. code-block:: lean

  section
  variable (ssubt : s ⊆ t)
  
  include ssubt
  
  example (h₀ : ∀ x ∈ t, ¬ even x) (h₁ : ∀ x ∈ t, prime x) :
    ∀ x ∈ s, ¬ even x ∧ prime x :=
  sorry
  
  example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
    ∃ x ∈ t, prime x :=
  sorry
  
  end

.. index:: include, commands; include

The ``include`` command is needed because ``ssubt`` does not
appear in the statement of the theorem.
Lean does not look inside tactic blocks when it decides
what variables and hypotheses to include,
so if you delete that line,
you will not see the hypothesis within a ``begin .end`` proof.
If you are proving theorems in a library,
you can delimit the scope of and ``include`` by putting it
between ``section`` and ``end``,
so that later theorems do not include it as an unnecessary hypothesis.

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

  variables {α I : Type*}
  variables A B : I → set α
  variable  s : set α
  open set
  
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

Parentheses are often needed with an
indexed union or intersection because,
as with the quantifiers,
the scope of the bound variable extends as far as it can.

Try proving the following identity.
One direction requires classical logic!
We recommend using ``by_cases xs : x ∈ s``
at an appropriate point in the proof.

.. code-block:: lean

  open_locale classical
  
  example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
  sorry

Mathlib also has bounded unions and intersections,
which are analogous to the bounded quantifiers.
You can unpack their meaning with ``mem_bUnion_iff``
and ``mem_bInter_iff``.
As the following examples show,
Lean's simplifier carries out these replacements as well.

.. code-block:: lean

  def primes : set ℕ := {x | nat.prime x}
  
  example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
  by { ext, rw mem_bUnion_iff, refl }
  
  example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
  by { ext, simp }
  
  example : (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x < 2} :=
  begin
    intro x,
    contrapose!,
    simp,
    apply nat.exists_prime_and_dvd
  end

Try solving the following example, which is similar.
If you start typing ``eq_univ``,
tab completion will tell you that ``apply eq_univ_of_forall``
is a good way to start the proof.
We also recommend using the theorem ``nat.exists_infinite_primes``.

.. code-block:: lean

  example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
  sorry

Give a collection of sets, ``s : set (set α)``,
their union, ``⋃₀ s``, has type ``set α``
and is defined as ``{x | ∃ t ∈ s, x ∈ t}``.
Similarly, their intersection, ``⋂₀ s``, is defined as
``{x | ∀ t ∈ s, x ∈ t}``.
These operations are called ``sUnion`` and ``sInter``, respectively.
The following examples show their relationship to bounded union
and intersection.

.. code-block:: lean

  variables {α : Type*} (s : set (set α))
  
  example : ⋃₀ s = ⋃ t ∈ s, t :=
  begin
    ext x,
    rw mem_bUnion_iff,
    refl
  end
  
  example : ⋂₀ s = ⋂ t ∈ s, t :=
  begin
    ext x,
    rw mem_bInter_iff,
    refl
  end

In the library, these identities are called
``sUnion_eq_bUnion`` and ``sInter_eq_bInter``.
