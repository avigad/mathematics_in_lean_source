import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

open Function

/- TEXT:
.. _the_schroeder_bernstein_theorem:

The Schröder-Bernstein Theorem
------------------------------

We close this chapter with an elementary but nontrivial theorem of set theory.
Let :math:`\alpha` and :math:`\beta` be sets.
(In our formalization, they will actually be types.)
Suppose :math:`f : \alpha → \beta` and :math:`g : \beta → \alpha`
are both injective.
Intuitively, this means that :math:`\alpha` is no bigger than :math:`\beta` and vice-versa.
If :math:`\alpha` and :math:`\beta` are finite, this implies that
they have the same cardinality, which is equivalent to saying that there
is a bijection between them.
In the nineteenth century, Cantor stated that same result holds even in the
case where :math:`\alpha` and :math:`\beta` are infinite.
This was eventually established by Dedekind, Schröder, and Bernstein
independently.

Our formalization will introduce some new methods that we will explain
in greater detail in chapters to come.
Don't worry if they go by too quickly here.
Our goal is to show you that you already have the skills to contribute
to the formal proof of a real mathematical result.

To understand the idea behind the proof, consider the image of the map
:math:`g` in :math:`\alpha`.
On that image, the inverse of :math:`g` is defined and is a bijection
with :math:`\beta`.

.. image:: /figures/schroeder_bernstein1.*
   :height: 150 px
   :alt: the Schröder Bernstein theorem
   :align: center

The problem is that the bijection does not include the shaded region
in the diagram, which is nonempty if :math:`g` is not surjective.
Alternatively, we can use :math:`f` to map all of
:math:`\alpha` to :math:`\beta`,
but in that case the problem is that if :math:`f` is not surjective,
it will miss some elements of :math:`\beta`.

.. image:: /figures/schroeder_bernstein2.*
   :height: 150 px
   :alt: the Schröder Bernstein theorem
   :align: center

But now consider the composition :math:`g \circ f` from :math:`\alpha` to
itself. Because the composition is injective, it forms a bijection between
:math:`\alpha` and its image, yielding a scaled-down copy of :math:`\alpha`
inside itself.

.. image:: /figures/schroeder_bernstein3.*
   :height: 150 px
   :alt: the Schröder Bernstein theorem
   :align: center

This composition maps the inner shaded ring to yet another such
set, which we can think of as an even smaller concentric shaded ring,
and so on.
This yields a
concentric sequence of shaded rings, each of which is in
bijective correspondence with the next.
If we map each ring to the next and leave the unshaded
parts of :math:`\alpha` alone,
we have a bijection of :math:`\alpha` with the image of :math:`g`.
Composing with :math:`g^{-1}`, this yields the desired
bijection between :math:`\alpha` and :math:`\beta`.

We can describe this bijection more simply.
Let :math:`A` be the union of the sequence of shaded regions, and
define :math:`h : \alpha \to \beta` as follows:

.. math::

  h(x) = \begin{cases}
    f(x) & \text{if $x \in A$} \\
    g^{-1}(x) & \text{otherwise.}
  \end{cases}

In other words, we use :math:`f` on the shaded parts,
and we use the inverse of :math:`g` everywhere else.
The resulting map :math:`h` is injective
because each component is injective
and the images of the two components are disjoint.
To see that it is surjective,
suppose we are given a :math:`y` in :math:`\beta`, and
consider :math:`g(y)`.
If :math:`g(y)` is in one of the shaded regions,
it cannot be in the first ring, so we have :math:`g(y) = g(f(x))`
for some :math:`x` is in the previous ring.
By the injectivity of :math:`g`, we have :math:`h(x) = f(x) = y`.
If :math:`g(y)` is not in the shaded region,
then by the definition of :math:`h`, we have :math:`h(g(y))= y`.
Either way, :math:`y` is in the image of :math:`h`.

This argument should sound plausible, but the details are delicate.
Formalizing the proof will not only improve our confidence in the
result, but also help us understand it better.
Because the proof uses classical logic, we tell Lean that our definitions
will generally not be computable.
BOTH: -/
-- QUOTE:
noncomputable section
open Classical
variable {α β : Type _} [Nonempty β]
-- QUOTE.

/- TEXT:
The annotation ``[Nonempty β]`` specifies that ``β`` is nonempty.
We use it because the mathlib primitive that we will use to
construct :math:`g^{-1}` requires it.
The case of the theorem where :math:`\beta` is empty is trivial,
and even though it would not be hard to generalize the formalization to cover
that case as well, we will not bother.
Specifically, we need the hypothesis ``[Nonempty β]`` for the operation
``invFun`` that is defined in mathlib.
Given ``x : α``, ``invFun g x`` chooses a preimage of ``x``
in ``β`` if there is one,
and returns an arbitrary element of ``β`` otherwise.
The function ``invFun g`` is always a left inverse if ``g`` is injective
and a right inverse if ``g`` is surjective.

-- LITERALINCLUDE: inv_fun g

We define the set corresponding to the union of the shaded regions as follows.

BOTH: -/
section

-- QUOTE:
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n
-- QUOTE.

/- TEXT:
The definition ``sb_aux`` is an example of a *recursive definition*,
which we will explain in the next chapter.
It defines a sequence of sets

.. math::

  S_0 &= \alpha ∖ g(\beta) \\
  S_{n+1} &= g(f(S_n)).

The definition ``sb_set`` corresponds to the set
:math:`A = \bigcup_{n \in \mathbb{N}} S_n` in our proof sketch.
The function :math:`h` described above is now defined as follows:
BOTH: -/
-- QUOTE:
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x
-- QUOTE.

/- TEXT:
We will need the fact that our definition of :math:`g^{-1}` is a
right inverse on the complement of :math:`A`,
which is to say, on the non-shaded regions of :math:`\alpha`.
This is so because the outermost ring, :math:`S_0`, is equal to
:math:`\alpha \setminus g(\beta)`, so the complement of :math:`A` is
contained in :math:`g(\beta)`.
As a result, for every :math:`x` in the complement of :math:`A`,
there is a :math:`y` such that :math:`g(y) = x`.
(By the injectivity of :math:`g`, this :math:`y` is unique,
but next theorem says only that ``inv_fun g x`` returns some ``y``
such that ``g y = x``.)

Step through the proof below, make sure you understand what is going on,
and fill in the remaining parts.
You will need to use ``inv_fun_eq`` at the end.
Notice that rewriting with ``sb_aux`` here replaces ``sb_aux f g 0``
with the right-hand side of the corresponding defining equation.
BOTH: -/
-- QUOTE:
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
/- EXAMPLES:
      sorry },
SOLUTIONS: -/
    exact ⟨mem_univ _, hx⟩
-- BOTH:
  have : ∃ y, g y = x := by
/- EXAMPLES:
      { sorry },
      sorry
SOLUTIONS: -/
    simp at this
    assumption
  exact invFun_eq this

-- BOTH:
-- QUOTE.
/- TEXT:
We now turn to the proof that :math:`h` is injective.
Informally, the proof goes as follows.
First, suppose :math:`h(x_1) = h(x_2)`.
If :math:`x_1` is in :math:`A`, then :math:`h(x_1) = f(x_1)`,
and we can show that :math:`x_2` is in :math:`A` as follows.
If it isn't, then we have :math:`h(x_2) = g^{-1}(x_2)`.
From :math:`f(x_1) = h(x_1) = h(x_2)` we have :math:`g(f(x_1)) = x_2`.
From the definition of :math:`A`, since :math:`x_1` is in :math:`A`,
:math:`x_2` is in :math:`A` as well, a contradiction.
Hence, if :math:`x_1` is in :math:`A`, so is :math:`x_2`,
in which case we have :math:`f(x_1) = h(x_1) = h(x_2) = f(x_2)`.
The injectivity of :math:`f` then implies :math:`x_1 = x_2`.
The symmetric argument shows that if :math:`x_2` is in :math:`A`,
then so is :math:`x_1`, which again implies :math:`x_1 = x_2`.

The only remaining possibility is that neither :math:`x_1` nor :math:`x_2`
is in :math:`A`. In that case, we have
:math:`g^{-1}(x_1) = h(x_1) = h(x_2) = g^{-1}(x_2)`.
Applying :math:`g` to both sides yields :math:`x_1 = x_2`.

Once again, we encourage you to step through the following proof
to see how the argument plays out in Lean.
See if you can finish off the proof using ``sb_right_inv``.
BOTH: -/
-- QUOTE:
theorem sb_injective (hf : Injective f) (hg : Injective g) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
/- EXAMPLES:
      . sorry
SOLUTIONS: -/
        rw [hxeq, sb_right_inv f g x₂nA]
-- BOTH:
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
/- EXAMPLES:
      . sorry,
SOLUTIONS: -/
    rw [if_pos x₁A, if_pos x₂A] at hxeq
    exact hf hxeq
-- BOTH:
  push_neg  at xA
/- EXAMPLES:
    sorry
SOLUTIONS: -/
  rw [if_neg xA.1, if_neg xA.2] at hxeq
  rw [← sb_right_inv f g xA.1, hxeq, sb_right_inv f g xA.2]

-- BOTH:
-- QUOTE.
/- TEXT:
The proof introduces some new tactics.
To start with, notice the ``set`` tactic, which introduces abbreviations
``A`` and ``h`` for ``sb_set f g`` and ``sb_fun f g`` respectively.
We name the corresponding defining equations ``A_def`` and ``h_def``.
The abbreviations are definitional, which is to say, Lean will sometimes
unfold them automatically when needed.
But not always; for example, when using ``rw``, we generally need to
use ``A_def`` and ``h_def`` explicitly.
So the definitions bring a tradeoff: they can make expressions shorter
and more readable, but they sometimes require us to do more work.

A more interesting tactic is the ``wlog`` tactic, which encapsulates
the symmetry argument in the informal proof above.
We will not dwell on it now, but notice that it does exactly what we want.
If you hover over the tactic you can take a look at its documentation.

The argument for surjectivity is even easier.
Given :math:`y` in :math:`\beta`,
we consider two cases, depending on whether :math:`g(y)` is in :math:`A`.
If it is, it can't be in :math:`S_0`, the outermost ring,
because by definition that is disjoint from the image of :math:`g`.
Thus it is an element of :math:`S_{n+1}` for some :math:`n`.
This means that it is of the form :math:`g(f(x))` for some
:math:`x` in :math:`S_n`.
By the injectivity of :math:`g`, we have :math:`f(x) = y`.
In the case where :math:`g(y)` is in the complement of :math:`A`,
we immediately have :math:`h(g(y))= y`, and we are done.

Once again, we encourage you to step through the proof and fill in
the missing parts.
The tactic ``cases n with n`` splits on the cases ``g y ∈ sb_aux f g 0``
and ``g y ∈ sb_aux f g n.succ``.
In both cases, calling the simplifier with ``simp [sb_aux]``
applies the corresponding defining equation of ``sb_aux``.
BOTH: -/
-- QUOTE:
theorem sb_surjective (hf : Injective f) (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    cases' n with n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, sbFun, if_pos this]
    exact hg hx
/- EXAMPLES:
    sorry
SOLUTIONS: -/
  use g y
  simp only [h_def, sbFun, if_neg gyA]
  apply leftInverse_invFun hg

-- BOTH:
-- QUOTE.
end

/- TEXT:
We can now put it all together. The final statement is short and sweet,
and the proof uses the fact that ``Bijective h`` unfolds to
``Injective h ∧ Surjective h``.
EXAMPLES: -/
-- QUOTE:
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf hg, sb_surjective f g hf hg⟩
-- QUOTE.

-- Auxiliary information
section
variable (g : β → α) (x : α)

-- TAG: inv_fun g
#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

-- TAG: end
end

