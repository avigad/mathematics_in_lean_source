-- BOTH:
import data.set.lattice
import data.set.function
import analysis.special_functions.log.basic

/- TEXT:
.. _functions:

Functions
---------

If ``f : α → β`` is a function and  ``p`` is a set of
elements of type ``β``,
the library defines ``preimage f p``, written ``f ⁻¹' p``,
to be ``{x | f x ∈ p}``.
The expression ``x ∈ f ⁻¹' p`` reduces to ``f x ∈ p``.
This is often convenient, as in the following example:
TEXT. -/
-- BOTH:
section

-- QUOTE:
variables {α β : Type*}
variable  f : α → β
variables s t : set α
variables u v : set β
open function
open set

-- EXAMPLES:
example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }
-- QUOTE.

/- TEXT:
If ``s`` is a set of elements of type ``α``,
the library also defines ``image f s``,
written ``f '' s``,
to be ``{y | ∃ x, x ∈ s ∧ f x = y}``.
So a hypothesis  ``y ∈ f '' s`` decomposes to a triple
``⟨x, xs, xeq⟩`` with ``x : α`` satisfying the hypotheses ``xs : x ∈ s``
and ``xeq : f x = y``.
The ``rfl`` tag in the ``rintros`` tactic (see :numref:`the_existential_quantifier`) was made precisely
for this sort of situation.
TEXT. -/
-- QUOTE:
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
-- QUOTE.

/- TEXT:
Notice also that the ``use`` tactic applies ``refl``
to close goals when it can.

Here is another example:
TEXT. -/
-- QUOTE:
example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs]
end
-- QUOTE.

/- TEXT:
We can replace the line ``use [x, xs]`` by
``apply mem_image_of_mem f xs`` if we want to
use a theorem specifically designed for that purpose.
But knowing that the image is defined in terms
of an existential quantifier is often convenient.

The following equivalence is a good exercise:
TEXT. -/
-- QUOTE:
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
sorry
-- QUOTE.

-- SOLUTIONS:
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
begin
  split,
  { intros h x xs,
    have : f x ∈ f '' s,
    from mem_image_of_mem _ xs,
    exact h this },
  intros h y ymem,
  rcases ymem with ⟨x, xs, fxeq⟩,
  rw ← fxeq,
  apply h xs
end

/- TEXT:
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
TEXT. -/
-- QUOTE:
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
-- QUOTE.

-- SOLUTIONS:
example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
begin
  rintros x ⟨y, ys, fxeq⟩,
  rw ← h fxeq,
  exact ys
end

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, xmem, rfl⟩,
  exact xmem
end

example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  rcases h y with ⟨x, fxeq⟩,
  use x,
  split,
  { show f x ∈ u,
    rw fxeq, exact yu },
  exact fxeq
end

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
begin
  rintros y ⟨x, xs, fxeq⟩,
  use [x, h xs, fxeq]
end

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
by intro x; apply h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by ext x; refl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  rintros y ⟨x, ⟨xs, xt⟩, rfl⟩,
  use [x, xs, rfl, x, xt, rfl]
end

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂t, fx₂eq⟩⟩,
  use [x₁, x₁s],
  rw ← h fx₂eq,
  exact x₂t
end

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x₁, x₁s, rfl⟩, h⟩,
  use [x₁, x₁s],
  intro h',
  apply h,
  use [x₁, h', rfl]
end

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
λ x, id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  ext y, split,
  { rintros ⟨⟨x, xs, rfl⟩, fxv⟩,
    use [x, xs, fxv] },
  rintros ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩,
  use [x, xs, rfl, fxv],
end

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u :=
begin
  rintros y ⟨x, ⟨xs, fxu⟩, rfl⟩,
  use [x, xs, rfl, fxu],
end

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin
  rintros x ⟨xs, fxu⟩,
  use [x, xs, rfl, fxu],
end

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  rintros x (xs | fxu),
  { left, use [x, xs, rfl] },
  right, use fxu
end

/- TEXT:
You can also try your hand at the next group of exercises,
which characterize the behavior of images and preimages
with respect to indexed unions and intersections.
In the third exercise, the argument ``i : I`` is needed
to guarantee that the index set is nonempty.
To prove any of these, we recommend using ``ext`` or ``intro``
to unfold the meaning of an equation or inclusion between sets,
and then calling ``simp`` to unpack the conditions for membership.
BOTH: -/
-- QUOTE:
variables {I : Type*} (A : I → set α) (B : I → set β)

-- EXAMPLES:
example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  rintros ⟨i, x, xAi, fxeq⟩,
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
end

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

example (i : I) (injf : injective f) :
  (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  exact fxeq
end

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }
-- QUOTE.

-- SOLUTIONS:
example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  rintros ⟨i, x, xAi, fxeq⟩,
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
end

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

example (i : I) (injf : injective f) : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  exact fxeq
end

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }

-- OMIT:
/-
In type theory, a function ``f : α → β`` can be applied to any
element of the domain ``α``,
but we sometimes want to represent functions that are
meaningfully defined on only some of those elements.
For example, as a function of type ``ℝ → ℝ → ℝ``,
division is only meaningful when the second argument is nonzero.
In mathematics, when we write an expression of the form ``s / t``,
we should have implicitly or explicitly ruled out
the case that ``t`` is zero.

But since division has type ``ℝ → ℝ → ℝ`` in Lean,
it also has to return a value when the second argument is zero.
The strategy generally followed by the library is to assign such
functions convenient values outside their natural domain.
For example, defining ``x / 0`` to be ``0`` means that the
identity ``(x + y) / z = x / z + y / z`` holds for every
``x``, ``y``, and ``z``.

As a result, when we read an expression ``s / t`` in Lean,
we should not assume that ``t`` is a meaningful input value.
When we need to, we can restrict the statement of a theorem to
guarantee that it is.
For example, theorem ``div_mul_cancel`` asserts ``x ≠ 0 → x / y * y = x`` for
``x`` and ``y`` in suitable algebraic structures.

.. TODO: previous text (delete eventually)

.. The fact that in type theory a function is always totally
.. defined on its domain type
.. sometimes forces some difficult choices.
.. For example, if we want to define ``x / y`` and ``log x``
.. as functions on the reals,
.. we have to assign a value to the first when ``y`` is ``0``,
.. and a value to the second for ``x ≤ 0``.
.. The strategy generally followed by the Lean library
.. in these situations is to assign such functions somewhat arbitrary
.. but convenient values outside their natural domain.
.. For example, defining ``x / 0`` to be ``0`` means that the
.. identity ``(x + y) / z = x / z + y / z`` holds
.. for every ``x``, ``y``, and ``z``.
.. When you see a theorem in the library that uses the
.. division symbol,
.. you should be mindful that theorem depends on this
.. nonstandard definition,
.. but this generally does not cause problems in practice.
.. When we need to,
.. we can restrict the statement of a theorem so that
.. it does not rely on such values.
.. For example, if a theorem begins ``∀ x > 0, ...``,
.. dividing by ``x`` in the body of the statement is not problematic.
.. Limiting the scope of a quantifier in this way is known
.. as *relativization*.

.. TODO: comments from Patrick
.. This discussion is very important and we should really get it right. The natural tendency of mathematicians here is to think Lean does bullshit and will let them prove false things. So we should focus on why there is no issue, not on apologies or difficulties.

.. I think we could include a discussion of the fact that the meaning of f : α → β is actually more subtle that it seems. Saying f is a function from α to β is actually a slight oversimplification. The more nuanced meaning is that f is a function whose possible meaningful input values all have type α and whose output values have type β, but we should not assume that every term with type α is a meaningful input value.

.. Then we of course need to point out that defining terms of type α → β required to assign a value to every term of type α, and this can be irritating but this is balanced by the convenience of having a couple of unconditional lemma like the (x+y)/z thing.

.. Also, I feel it is very important to point out that real world math doesn't force you to (x+y)/⟨z, proof that z doesn't vanish⟩. So type theory is not different here.

.. TODO: deleted because we haven't discussed subtypes yet.
.. Be sure to do that eventually.
.. There are ways around this, but they are generally unpleasant.
.. For example, we can take ``log`` to be defined on
.. the subtype ``{ x // x > 0 }``,
.. but then we have to mediate between two different types,
.. the reals and that subtype.
-/
/- TEXT:
The library defines a predicate ``inj_on f s`` to say that
``f`` is injective on ``s``.
It is defined as follows:
TEXT. -/
-- QUOTE:
example : inj_on f s ↔
  ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
iff.refl _
-- QUOTE.

-- BOTH:
end

/- TEXT:
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
BOTH: -/
section
-- QUOTE:
open set real

-- EXAMPLES:
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
-- QUOTE.

/- TEXT:
Try proving these:
EXAMPLES: -/
-- QUOTE:
example : inj_on sqrt { x | x ≥ 0 } :=
sorry

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
sorry

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
sorry

example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} :=
sorry
-- QUOTE.

-- SOLUTIONS:
example : inj_on sqrt { x | x ≥ 0 } :=
begin
  intros x xnonneg y ynonneg,
  intro e,
  calc
    x   = (sqrt x)^2 : by rw sq_sqrt xnonneg
    ... = (sqrt y)^2 : by rw e
    ... = y          : by rw sq_sqrt ynonneg
end

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
begin
    intros x xnonneg y ynonneg,
    intro e,
    dsimp at *,
    calc
      x   = sqrt (x^2) : by rw sqrt_sq xnonneg
      ... = sqrt (y^2) : by rw e
      ... = y          : by rw sqrt_sq ynonneg,
end

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
begin
    ext y, split,
    { rintros ⟨x, ⟨xnonneg, rfl⟩⟩,
      apply sqrt_nonneg },
    intro ynonneg,
    use y^2,
    dsimp at *,
    split,
    apply pow_nonneg ynonneg,
    apply sqrt_sq,
    assumption,
end

example : range (λ x, x^2) = {y : ℝ | y ≥ 0} :=
begin
    ext y,
    split,
    { rintros ⟨x, rfl⟩,
       dsimp at *,
       apply pow_two_nonneg },
    intro ynonneg,
    use sqrt y,
    exact sq_sqrt ynonneg,
end

-- BOTH:
end

/- TEXT:
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
TEXT. -/
-- BOTH:
section
-- QUOTE:
variables {α β : Type*} [inhabited α]

-- EXAMPLES:
#check (default : α)

variables (P : α → Prop) (h : ∃ x, P x)

#check classical.some h

example : P (classical.some h) := classical.some_spec h
-- QUOTE.

/- TEXT:
Given ``h : ∃ x, P x``, the value of ``classical.some h``
is some ``x`` satisfying ``P x``.
The theorem ``classical.some_spec h`` says that ``classical.some h``
meets this specification.

With these in hand, we can define the inverse function
as follows:
BOTH: -/
-- QUOTE:
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
-- QUOTE.

/- TEXT:
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
BOTH: -/
-- QUOTE:
variable  f : α → β
open function

-- EXAMPLES:
example : injective f ↔ left_inverse (inverse f) f  :=
sorry

example : surjective f ↔ right_inverse (inverse f) f :=
sorry
-- QUOTE.

-- SOLUTIONS:
example : injective f ↔ left_inverse (inverse f) f  :=
begin
  split,
  { intros h y,
    apply h,
    apply inverse_spec,
    use y },
  intros h x1 x2 e,
  rw [←h x1, ←h x2, e]
end

example : injective f ↔ left_inverse (inverse f) f  :=
⟨λ h y, h (inverse_spec _ ⟨y, rfl⟩), λ h x1 x2 e, by rw [←h x1, ←h x2, e]⟩

example : surjective f ↔ right_inverse (inverse f) f :=
begin
  split,
  { intros h y,
    apply inverse_spec,
    apply h },
  intros h y,
  use (inverse f y),
  apply h
end

example : surjective f ↔ right_inverse (inverse f) f :=
⟨λ h y, inverse_spec _ (h _), λ h y, ⟨inverse f y, h _⟩⟩

-- BOTH:
end

-- OMIT:
/-
.. TODO: These comments after this paragraph are from Patrick.
.. We should decide whether we want to do this here.
.. Another possibility is to wait until later.
.. There may be good examples for the topology chapter,
.. at which point, the reader will be more of an expert.

.. This may be a good place to also introduce a discussion of the choose tactic, and explain why you choose (!) not to use it here.

.. Typically, you can include:

.. example {α β : Type*} {f : α → β} : surjective f ↔ ∃ g : β → α, ∀ b, f (g b) = b :=
.. begin
..   split,
..   { intro h,
..     dsimp [surjective] at h, -- this line is optional
..     choose g hg using h,
..     use g,
..     exact hg },
..   { rintro ⟨g, hg⟩,
..     intros b,
..     use g b,
..     exact hg b },
.. end
.. Then contrast this to a situation where we really want a def outputting an element or a function, maybe with a less artificial example than your inverse.

.. We should also tie this to the "function are global" discussion, and the whole thread of deferring proofs to lemmas instead of definitions. There is a lot going on here, and all of it is crucial for formalization.
-/

/- TEXT:
We close this section with a type-theoretic statement of Cantor's
famous theorem that there is no surjective function from a set
to its power set.
See if you can understand the proof,
and then fill in the two lines that are missing.
TEXT. -/
-- BOTH:
section
variable {α : Type*}
open function

-- EXAMPLES:
-- QUOTE:
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
-- QUOTE.

-- SOLUTIONS:
theorem Cantorαα : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with ⟨j, h⟩,
  have h₁ : j ∉ f j,
  { intro h',
    have : j ∉ f j,
      by rwa h at h',
    contradiction },
  have h₂ : j ∈ S,
    from h₁,
  have h₃ : j ∉ S,
    by rwa h at h₁,
  contradiction
end

-- BOTH:
end
