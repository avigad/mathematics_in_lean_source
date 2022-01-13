.. _functions:

Functions
---------

If ``f : α → β`` is a function and  ``p`` is a set of
elements of type ``β``,
the library defines ``preimage f p``, written ``f ⁻¹' p``,
to be ``{x | f x ∈ p}``.
The expression ``x ∈ f ⁻¹' p`` reduces to ``f x ∈ p``.
This is often convenient, as in the following example:

.. code-block:: lean

  variables {α β : Type*}
  variable  f : α → β
  variables s t : set α
  variables u v : set β
  open function
  open set
  
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

Notice also that the ``use`` tactic applies ``refl``
to close goals when it can.

Here is another example:

.. code-block:: lean

  example : s ⊆ f ⁻¹' (f '' s) :=
  begin
    intros x xs,
    show f x ∈ f '' s,
    use [x, xs]
  end

We can replace the line ``use [x, xs]`` by
``apply mem_image_of_mem f xs`` if we want to
use a theorem specifically designed for that purpose.
But knowing that the image is defined in terms
of an existential quantifier is often convenient.

The following equivalence is a good exercise:

.. code-block:: lean

  example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
  sorry

It shows that ``image f`` and ``preimage f`` are
an instance of what is known as a *Galois connection*
between ``set α`` and ``set β``,
each partially ordered by the subset relation.
In the library, this equivalence is named
``image_subset_iff``.
In practice, the right-hand side is often the
more useful representation,
because ``y ∈ f ⁻¹' t`` unfolds to ``f y ∈ t``
whereas working with ``x ∈ f '' s`` requires
decomposing an existential quantifier.

Here is a long list of set-theoretic identities for
you to enjoy.
You don't have to do all of them at once;
do a few of them,
and set the rest aside for a rainy day.

.. code-block:: lean

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

You can also try your hand at the next group of exercises,
which characterize the behavior of images and preimages
with respect to indexed unions and intersections.
In the third exercise, the argument ``i : I`` is needed
to guarantee that the index set is nonempty.
To prove any of these, we recommend using ``ext`` or ``intro``
to unfold the meaning of an equation or inclusion between sets,
and then calling ``simp`` to unpack the conditions for membership.

.. code-block:: lean

  variables {I : Type*} (A : I → set α) (B : I → set β)
  
  example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
  sorry
  
  example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
  sorry
  
  example (i : I) (injf : injective f) :
    (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
  sorry
  
  example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
  sorry
  
  example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
  sorry


.. code-block:: lean

  example : inj_on f s ↔
    ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  iff.refl _

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

  open set real
  
  example : inj_on log { x | x > 0 } :=
  begin
    intros x xpos y ypos,
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

Try proving these:

.. code-block:: lean

  example : inj_on sqrt { x | x ≥ 0 } :=
  sorry
  
  example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
  sorry
  
  example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
  sorry
  
  example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} :=
  sorry

To define the inverse of a function ``f : α → β``,
we will use two new ingredients.
First, we need to deal with the fact that
an arbitrary type in Lean may be empty.
To define the inverse to ``f`` at ``y`` when there is
no ``x`` satisfying ``f x = y``,
we want to assign a default value in ``α``.
Adding the annotation ``[inhabited α]`` as a variable
is tantamount to assuming that ``α`` has a
preferred element, which is denoted ``default``.
Second, in the case where there is more than one ``x``
such that ``f x = y``,
the inverse function needs to *choose* one of them.
This requires an appeal to the *axiom of choice*.
Lean allows various ways of accessing it;
one convenient method is to use the classical ``some``
operator, illustrated below.

.. code-block:: lean

  variables {α β : Type*} [inhabited α]
  
  #check (default : α)
  
  variables (P : α → Prop) (h : ∃ x, P x)
  
  #check classical.some h
  
  example : P (classical.some h) := classical.some_spec h

Given ``h : ∃ x, P x``, the value of ``classical.some h``
is some ``x`` satisfying ``P x``.
The theorem ``classical.some_spec h`` says that ``classical.some h``
meets this specification.

With these in hand, we can define the inverse function
as follows:

.. code-block:: lean

  noncomputable theory
  open_locale classical
  
  def inverse (f : α → β) : β → α :=
  λ y : β, if h : ∃ x, f x = y then classical.some h else default
  
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
This is an instance of a *dependent if* construction,
since in the positive case, the value returned,
``classical.some h``, depends on the assumption ``h``.
The identity ``dif_pos h`` rewrites ``if h : e then a else b``
to ``a`` given ``h : e``,
and, similarly, ``dif_neg h`` rewrites it to ``b`` given ``h : ¬ e``.
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
They are tricky!
It helps to do the proofs on paper before
you start hacking through the details.
You should be able to prove each of them with about a half-dozen
short lines.
If you are looking for an extra challenge,
try to condense each proof to a single-line proof term.

.. code-block:: lean

  variable  f : α → β
  
  open function
  
  example : injective f ↔ left_inverse (inverse f) f  :=
  sorry
  
  example : surjective f ↔ right_inverse (inverse f) f :=
  sorry

We close this section with a type-theoretic statement of Cantor's
famous theorem that there is no surjective function from a set
to its power set.
See if you can understand the proof,
and then fill in the two lines that are missing.

.. code-block:: lean

  theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
  begin
    intros f surjf,
    let S := { i | i ∉ f i},
    rcases surjf S with ⟨j, h⟩,
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

