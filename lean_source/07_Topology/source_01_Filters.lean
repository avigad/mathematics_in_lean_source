import topology.instances.real

open set
open_locale topological_space filter

/- TEXT:
.. _filters:

.. index:: filter

Filters
-------

Filters on a type ``X`` are collections of sets of ``X`` satisfying three conditions. They are mostly used to
abstract two related kinds of ideas:

* *limits*, including all kinds of limits discussed above, in particular finite or infinite limits of sequences, finite or infinite limits of functions at a point or at infinity, etc...

* *things happening eventually*, including things happening for large enough ``n : ℕ``, or near enough a point ``x``, or for close enough pairs of points, or things happening almost everywhere in the sense of measure theory. Dually, filters can also express the idea of *things happening often*: for arbitrarily large ``n``, or at a point in any neighborhood of given a point etc...

The examples of filters appearing in these descriptions will be described in detail later, but we can already name them:

* ``(at_top : filter ℕ)`` : made of sets of ``ℕ`` containing ``{n | n ≥ N}`` for some ``N``
* ``𝓝 x`` : made of neighborhoods of ``x`` in a topological space
* ``𝓤 X`` : made of entourages of a uniform space (uniform spaces generalize metric spaces and topological groups)
* ``μ.a_e`` : made of sets whose complement has zero measure with respect to a measure ``μ``.

The general definition is as follows: a filter ``F : filter X`` is a
collection of sets ``F.sets : set (set X)`` such that

* ``F.univ_sets : univ ∈ F.sets`` (the set of all inhabitants of ``X`` belongs to ``F.sets``)
* ``F.sets_of_superset : ∀ {U V}, U ∈ F.sets → U ⊆ V → V ∈ F.sets`` (if ``U`` belongs to ``F.sets`` then anything larger also does)
* ``F.inter_sets : ∀ {U V}, U ∈ sets → V ∈ sets → U ∩ V ∈ sets`` (``F.sets`` is stable under intersection)

In mathlib, ``F`` is defined as a structure bundling ``F.sets`` and its
three properties, but the properties carry no additional data, so we
really want to blur the distinction between ``F`` and ``F.sets``. This
is done by defining ``U ∈ F`` to mean ``U ∈ F.sets``.
However the word sets still appears in some lemma names.

One can see from the axioms above that each filter defines a notion of "sufficiently large" set: the first
condition says that ``univ`` is sufficiently large, the second one says that a set containing a sufficiently 
large set is sufficiently large and the third one says that the intersection of two sufficiently large sets 
is sufficiently large. However a more useful way to see filters is that 
filters on a type ``X`` can be seen as generalized elements of ``set X``. For instance ``at_top`` is the 
"set of very large numbers", and ``𝓝 x₀`` is the "set of points very close to ``x₀``".
A first precise statement is that one can turn any ``s : set X`` into the so-called principal filter
associated to ``s``. This definition is already in mathlib and has a notation ``𝓟`` (localized in ``filter``),
but for demonstration purposes we use this as an opportunity to explicitly construct a filter:
TEXT. -/

-- QUOTE:
open filter

def principal {α : Type*} (s : set α) : filter α :=
{ sets := {t | s ⊆ t},
  univ_sets := sorry,
  sets_of_superset := sorry,
  inter_sets := sorry}
-- QUOTE.

-- SOLUTIONS:
-- In the next example we could use `tauto` in each proof instead of knowing the lemmas
example {α : Type*} (s : set α) : filter α :=
{ sets := {t | s ⊆ t},
  univ_sets := subset_univ s, 
  sets_of_superset := λ U V hU hUV, subset.trans hU hUV,
  inter_sets := λ U V hU hV, subset_inter hU hV }

/- TEXT:
For our second example, we'll use the filter ``at_top : filter ℕ`` (we could use any type with a preorder instead of ``ℕ``).
TEXT. -/

-- QUOTE:
example : filter ℕ :=
{ sets := {s | ∃ a, ∀ b, a ≤ b → b ∈ s},
  univ_sets := sorry,
  sets_of_superset := sorry,
  inter_sets := sorry }
-- QUOTE.

-- SOLUTIONS:
example : filter ℕ :=
{ sets := {s | ∃ a, ∀ b, a ≤ b → b ∈ s},
  univ_sets := begin
    use 42,
    finish,
  end,
  sets_of_superset := begin
    rintros U V ⟨N, hN⟩ hUV,
    use N,
    tauto,
  end,
  inter_sets := begin
    rintros U V ⟨N, hN⟩ ⟨N', hN'⟩,
    use max N N',
    intros b hb,
    rw max_le_iff at hb,
    split ; tauto,
  end }

/- TEXT:
We can also directly define the filter ``𝓝 x`` of neighborhoods of any ``x : ℝ``. 
A neighborhood of ``x`` is a set containing an open interval ``Ioo (x - ε) (x + ε)``
(of course this is only a special case of a more general construction in mathlib).


With these examples, we can already define what is means for a function ``f : X → Y``
to converge with respect to some ``G : filter Y`` along some ``F : filter X`` as
TEXT. -/
-- QUOTE:
def tendsto₁ {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) := 
∀ V ∈ G, f ⁻¹' V ∈ F
-- QUOTE.

/- TEXT:
When ``X = ℕ``, ``Y = ℝ`` then ``tendsto₁ u at_top (𝓝 x)`` is equivalent to asking that the sequence ``u : ℕ → ℝ``
converges to the real number ``x``. When both ``X`` and ``Y`` are ``ℝ``, ``tendsto f (𝓝 x₀) (𝓝 y₀)`` 
is equivalent to :math:`\lim_{x \to x₀} f(x) = y₀`. All other kinds of limits mentioned in the introduction are
also equivalent to ``tendsto₁`` for some filters on source and target.

The definition quoted above is definitionally equivalent to what is in mathlib, but it does not appear in this way,
hence the subscript in the name.
The issue with the above definition is that it exposes a quantifier and elements of ``G``, and it hides the intuition
coming from seeing filters as generalized sets. It is more efficient to
hide the ``∀ V`` and expose the intuition using more algebraic structure. 
The first ingredient is the push-forward operation :math:`f_*` associated to any map ``f : X → Y``:
``filter.map f``. Given a filter ``F`` on ``X``, we get ``filter.map f F : filter Y`` and, definitionnaly,
``V ∈ filter.map f F ↔ f ⁻¹' V ∈ F``. In this file we've opened the filter namespace, so
``filter.map`` can be written as ``map``. This allows rewriting the definition of ``tendsto`` using
the order relation on ``filter Y`` which is reversed inclusion of the set of members:
given ``G H : filter Y``, ``G ≤ H ↔ ∀ V : set Y, V ∈ H → V ∈ G``.

TEXT. -/

-- QUOTE:
def tendsto₂ {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) := 
map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) : 
  tendsto₂ f F G ↔ tendsto₁ f F G := iff.rfl
-- QUOTE.

/- TEXT:

One could argue that the order relation on filters seems backward. But recall that we can see filters on ``X`` as
generalized elements of ``set X``, through the inclusion of ``𝓟 : set X → filter X`` given by principal filters. 
This inclusion is order preserving so the order relation on filter can indeed be seen as the "inclusion relation 
between generalized sets". In this analogy, push-forward is analogous to the direct image. 
And indeed ``map f (𝓟 s) = 𝓟 (f '' s)``. 

We can now understand intuitively why a sequence ``u : ℕ → ℝ`` converges to
a point ``x₀`` if and only if ``map u at_top ≤ 𝓝 x₀``: this inequality means the "direct image under u" of 
"the set of very big natural numbers" is "included" in "the set of points very close to ``x₀``".

As promised, the above formulation exhibits no quantifier and no set. It also allows leveraging the algebraic property
of the push-forward operation. First each ``filter.map f`` is monotone. And then ``filter.map`` is compatible with
composition.
TEXT. -/

-- QUOTE:
#check @filter.map_mono -- ∀ {α β} {m : α → β}, monotone (map m)
#check @filter.map_map -- ∀ {α β γ} {f : filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f
-- QUOTE.

/- TEXT:
Together these two properties allow us to prove that limits compose, covering in one shot all 2197 variants from the introduction.
You can practice proving the following statement using either the definition involving the quantifier or the algebraic definition
together with the two above lemmas.
TEXT. -/
-- QUOTE:
example {X Y Z : Type*} {F : filter X} {G : filter Y} {H : filter Z} {f : X → Y} {g : Y → Z} 
  (hf : tendsto₁ f F G) (hg : tendsto₁ g G H) : tendsto₁ (g ∘ f) F H :=
sorry
-- QUOTE.
-- SOLUTIONS:
example {X Y Z : Type*} {F : filter X} {G : filter Y} {H : filter Z} {f : X → Y} {g : Y → Z} 
  (hf : tendsto₁ f F G) (hg : tendsto₁ g G H) : tendsto₁ (g ∘ f) F H :=
calc map (g ∘ f) F = map g (map f F) : by rw map_map
... ≤ map g G : map_mono hf
... ≤ H : hg

example {X Y Z : Type*} {F : filter X} {G : filter Y} {H : filter Z} {f : X → Y} {g : Y → Z} 
  (hf : tendsto₁ f F G) (hg : tendsto₁ g G H) : tendsto₁ (g ∘ f) F H :=
begin
  intros V hV,
  rw preimage_comp,
  apply hf,
  apply hg,
  exact hV
end

/- TEXT:

The push-forward construction uses a map to push filters from the map source to the map target. 
There also a pull-back operation going in the other direction: ``filter.comap``, generalizing the
preimage operation on sets. For any given map ``f``,
``filter.map f`` and ``filter.comap f`` form a Galois connection: 
``filter.map_le_iff_le_comap : filter.map f F ≤ G ↔ F ≤ filter.comap f G``. 
In particular this operation could be used to provided another formulation of ``tendsto`` that would be propositionally
(but not definitionaly) equivalent to the existing one.

This operation can be used to restrict filters to a subtype. For instance suppose we have ``f : ℝ → ℝ``, 
``x₀ : ℝ`` and ``y₀ : ℝ`` and we want to state that ``f x`` goes to ``y₀`` when ``x`` goes to ``x₀`` among rational numbers. 
We can pull-back the filter ``𝓝 x₀`` to ``ℚ`` using the coercion map
``coe : ℚ → ℝ`` and state ``tendsto (f ∘ coe : ℚ → ℝ) (comap coe (𝓝 x₀)) (𝓝 y₀)``.
TEXT. -/

-- QUOTE:
variables (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap (coe : ℚ → ℝ) (𝓝 x₀)
#check tendsto (f ∘ coe) (comap (coe : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)
-- QUOTE.

/- TEXT:
The pull-back operation is also compatible with composition, but contravariant.
TEXT. -/

-- QUOTE:
#check @comap_comap
-- QUOTE.

/- TEXT:
Let's now move up to the plane ``ℝ × ℝ`` and try to understand how neighborhoods of some point
``(x₀, y₀)`` are related to ``𝓝 x₀`` and ``𝓝 y₀``. There is a product operation 
``filter.prod : filter X → filter Y → filter (X × Y)``, denoted by ``×ᶠ`` which answers this question:
TEXT. -/
-- QUOTE:
example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ᶠ 𝓝 y₀ := nhds_prod_eq
-- QUOTE.

/- TEXT:
This operation is defined in term of the pull-back operation and the ``inf`` operation:
``F ×ᶠ G = (comap prod.fst F) ⊓ (comap prod.snd G)``.
Here the ``inf`` operation refers to the lattice structure on ``filter X`` for any type ``X``:
``F ⊓ G`` is the greatest filter that is smaller than both ``F`` and ``G``, generalizing the notion
of the intersection of sets.

A lot of proofs in mathlib use all of the aforementioned structure (``map``, ``comap``, ``inf``, ``sup``, ``prod``) 
to give algebraic proofs about convergence without ever referring to members of filters.
You can practice this on the following lemma, unfolding the definition of ``tendsto``
and ``filter.prod`` if needed.
TEXT. -/

-- QUOTE:
#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) : 
  tendsto f at_top (𝓝 (x₀, y₀)) ↔ 
  tendsto (prod.fst ∘ f) at_top (𝓝 x₀) ∧ tendsto (prod.snd ∘ f) at_top (𝓝 y₀) :=
sorry
-- QUOTE.

-- SOLUTIONS:

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) : 
  tendsto f at_top (𝓝 (x₀, y₀)) ↔ 
  tendsto (prod.fst ∘ f) at_top (𝓝 x₀) ∧ tendsto (prod.snd ∘ f) at_top (𝓝 y₀) :=
calc
tendsto f at_top (𝓝 (x₀, y₀)) ↔ map f at_top ≤ 𝓝 (x₀, y₀) : iff.rfl
... ↔ map f at_top ≤ 𝓝 x₀ ×ᶠ 𝓝 y₀ : by rw nhds_prod_eq
... ↔ map f at_top ≤ (comap prod.fst (𝓝 x₀) ⊓ comap prod.snd (𝓝 y₀)) : iff.rfl
... ↔ map f at_top ≤ comap prod.fst (𝓝 x₀) ∧ map f at_top ≤ (comap prod.snd (𝓝 y₀)) : le_inf_iff
... ↔ map prod.fst (map f at_top) ≤ 𝓝 x₀ ∧ map prod.snd (map f at_top) ≤ 𝓝 y₀ : 
        by rw [← map_le_iff_le_comap, ← map_le_iff_le_comap]
... ↔ map (prod.fst ∘ f) at_top ≤ 𝓝 x₀ ∧ map (prod.snd ∘ f) at_top ≤ 𝓝 y₀ : by rw [map_map, map_map]
/- begin
  rw nhds_prod_eq,
  unfold tendsto filter.prod,
  rw [le_inf_iff, ← map_le_iff_le_comap, map_map, ← map_le_iff_le_comap, map_map]
end -/

/- TEXT:
The ordered type ``filter X`` is actually a *complete* lattice: there is a bottom element and a top element and
any set of filters on ``X`` have an ``Inf`` and a ``Sup``.

Note that in the definition of filters, given the second property
(if ``U`` belongs to ``F`` then anything larger also belongs), the first property 
(the set of all inhabitants of ``X`` belongs to ``F``) is
equivalent to asking that ``F`` is not the empty collection of sets.
This shouldn't be confused with a more subtle question. The 
definition does not prohibit ``∅ ∈ F``. If ``∅ ∈ F`` then
``∀ U : set X, U ∈ F``, hence ``F`` is a
rather trivial filter. This trivial filter is precisely the bottom element of the complete
lattice ``filter X``.
This contrasts with the definition of filters in
Bourbaki who doesn't allow filters containing the empty set. 
Because of this choice, we need an
extra assumption of non-triviality in some lemmas, but gain
nicer global formal properties for the theory. We've seen already that it gives us a
bottom element. It also allowed us to define ``principal : set X → filter X`` without
precondition (this map sends ``∅`` to ``⊥``). 
And it allowed to get the pull-back operation without precondition.
Indeed it can happen that ``comap f F = ⊥`` although ``F ≠ ⊥``. For instance,
given ``x₀ : ℝ`` and ``s : set ℝ``, the pull-back of ``𝓝 x₀`` under the coercion
from the subtype corresponding to ``s`` is non-trivial if and only if ``x₀`` belongs to the
closure of ``s``.

In order to easily manage lemmas that do need to assume some filter is non-trivial, there is
a type class ``filter.ne_bot``, so you sometimes see lemmas assuming 
``(F : filter X) [F.ne_bot]``. The instance database knows for instance that ``(at_top : filter ℕ).ne_bot``
and knows that pushing forward a non-trivial filter gives a non-trivial filter, so a lemma
assuming ``[F.ne_bot]`` will automatically apply to ``map u at_top`` for any sequence ``u``.

Our tour of algebraic properties of filters and their relation to limits is essentially done,
but careful readers may have noticed that our claim that we get back the usual notions
of limits is not so clear. Superficially, it may look like ``tendsto u at_top (𝓝 x₀)``
is stronger than the usual condition because we ask that *every* neighborhood of ``x₀`` 
has a preimage belonging to ``at_top`` whereas the usual definition only asks
this for the standard neighborhoods ``Ioo (x₀ - ε) (x₀ + ε)``. 
The key is that, by definition, every neighborhood contains such a standard one.
This idea leads to the notion of a filter basis. Given ``F : filter X``,
a family of sets `s : ι → set X` is a basis for ``F`` if 
``∀ U : set X, U ∈ F ↔ ∃ i, s i ⊆ U``. Actually it is more flexible to also consider
a predicate on ``ι`` to select only some values ``i``. In the case of
``𝓝 x₀``, we want ``ι`` to be ``ℝ``, ``i = ε`` and the predicate should select
positive ``ε``. So the actual basis statement is:
TEXT. -/

-- QUOTE:
example (x₀ : ℝ) : has_basis (𝓝 x₀) (λ ε : ℝ, 0 < ε) (λ ε, Ioo  (x₀ - ε) (x₀ + ε)) :=
nhds_basis_Ioo_pos x₀
-- QUOTE.

/- TEXT:
Of course we also have a nice basis for ``at_top``, and the lemma ``filter.has_basis.tendsto_iff`` allows
us to reformulate a ``tendsto f F G`` given bases for ``F`` and ``G``.
TEXT. -/

-- QUOTE:
example (u : ℕ → ℝ) (x₀ : ℝ) : 
  tendsto u at_top (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo  (x₀ - ε) (x₀ + ε) :=
begin
  have : at_top.has_basis (λ n : ℕ, true) Ici := at_top_basis,
  rw this.tendsto_iff (nhds_basis_Ioo_pos x₀),
  simp
end
-- QUOTE.

/- TEXT:
We now turn to the way filters allow to efficiently handle properties that hold for sufficiently large numbers
or sufficiently close to a given point. If you did the exercises in :numref:`sequences_and_convergence`,
you have very often been in the situation where some property ``P n`` holds for sufficiently large ``n`` and some
other property ``Q n`` holds for sufficiently large ``n``. After two ```cases`` this gave you
``N_P`` and ``N_Q`` such that ``∀ n ≥ N_P, P n`` and ``∀ n ≥ N_Q, Q n``. Then you ``set N := max N_P N_Q`` and
patiently proved that ``∀ n ≥ N, P n ∧ Q n``. After doing this a couple of time this feels very tiresome. 

The way to solve this issue is to note that "``P n`` and ``Q n`` hold for large enough ``n``" means 
``{n | P n} ∈ at_top`` and ``{n | Q n} ∈ at_top``.
Then the fact that ``at_top`` is a filter means in particular that the intersection of two elements of ``at_top`` 
is again in ``at_top``, so ``{n | P n ∧ Q n} ∈ at_top``. However writing ``{n | P n} ∈ at_top`` is not very nice.
In this situation, we use the more suggestive notation ``∀ᶠ n in at_top, P n``. 
Note the superscript ``f`` which stands for filter. 
The notation reads: for all ``n`` in "the set of very large numbers", ``P n`` holds. Technically, this notation 
stands for ``filter.eventually``, and the lemma ``filter.eventually.and`` uses the intersection property of filters to do
what we described above:

TEXT. -/

-- QUOTE:
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in at_top, P n) (hQ : ∀ᶠ n in at_top, Q n) : 
  ∀ᶠ n in at_top, P n ∧ Q n := hP.and hQ
-- QUOTE.

/- TEXT:
This notation is so convenient and intuitive to use that we also have specializations 
when ``P`` is an equality or inequality statement. For instance, let ``u`` and ``v`` be
two sequences of real numbers. Let us state that if
``u n`` and ``v n`` coincide for large enough ``n`` then ``u`` tends to ``x₀`` if and only
if ``v`` tends to ``x₀``. First we'll use the generic ``eventually`` and then the one 
specialized for the equality predicate, ``eventually_eq`` . Note that both statements are
definitionaly equivalent so the same proof will be used.

TEXT. -/

-- QUOTE:
example (u v : ℕ → ℝ) (h : ∀ᶠ n in at_top, u n = v n) (x₀ : ℝ) : 
  tendsto u at_top (𝓝 x₀) ↔ tendsto v at_top (𝓝 x₀) :=
tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[at_top] v) (x₀ : ℝ) : 
  tendsto u at_top (𝓝 x₀) ↔ tendsto v at_top (𝓝 x₀) :=
tendsto_congr' h

-- QUOTE.

/- TEXT:

It instructive to review the definition of filters in terms of this use with ``eventually``.
Given ``F : filter X``, for any predicates ``P`` and ``Q`` on ``X``,

* the condition ``univ ∈ F`` ensures that ``(∀ x, P x) → ∀ᶠ x in F, P x``.
* the condition ``U ∈ F → U ⊆ V → V ∈ F`` ensures that ``(∀ᶠ x in F, P x) → (∀ x, P x → Q x) → ∀ᶠ x in F, Q x``
* the condition ``U ∈ F → V ∈ F → U ∩ V ∈ F`` ensures that ``(∀ᶠ x in F, P x) → (∀ᶠ x in F, Q x) → ∀ᶠ x in F, P x ∧ Q x``, as we already discussed.

TEXT. -/

-- QUOTE:
#check @eventually_of_forall
#check @eventually.mono
#check @eventually.and
-- QUOTE.

/- TEXT:
The item above, corresponding to ``eventually.mono`` is also a very nice use of filters, especially combined
with ``eventually.and``. The ``filter_upwards`` tactic allows us to nicely combine them. 
Compare:

TEXT. -/

-- QUOTE:

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in at_top, P n) (hQ : ∀ᶠ n in at_top, Q n) 
  (hR : ∀ᶠ n in at_top, P n ∧ Q n → R n) : 
  ∀ᶠ n in at_top, R n := 
begin
  apply (hP.and (hQ.and hR)).mono,
  rintros n ⟨h, h', h''⟩,
  exact h'' ⟨h, h'⟩
end

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in at_top, P n) (hQ : ∀ᶠ n in at_top, Q n) 
  (hR : ∀ᶠ n in at_top, P n ∧ Q n → R n) : 
  ∀ᶠ n in at_top, R n := 
begin
  filter_upwards [hP, hQ, hR],
  intros n h h' h'',
  exact h'' ⟨h, h'⟩
end

-- QUOTE.

/- TEXT:

Readers who know about measure theory will note that the filter ``μ.ae`` of sets whose complement has measure zero
(aka "the set of almost every point") is not very useful as the source or target of ``tendsto`` but very often
used with ``eventually``, when saying a property holds for almost every point.

There is a dual version of ``∀ᶠ x in F, P x`` which is much less useful, but still exists: ``∃ᶠ x in F, P x`` means
``{x | ¬P x} ∉ f``. For instance ``∃ᶠ n in at_top, P n`` means there are arbitrarily large ``n`` such that ``P n``.
This notation stands for ``filter.frequently``.


As a more sophisticated example, the statement: "if a sequence ``u`` converges to
some ``x`` and ``u n`` belongs to a set ``M`` for ``n`` large enough then ``x`` is in the closure of
``M``" is formalized as: ``tendsto u at_top (𝓝 x) → (∀ᶠ n in at_top, u n ∈ M) → x ∈ closure M``,
which is a special case of ``mem_closure_of_tendsto`` from the topology library.
See if you can prove it using the quoted lemmas, knowing that ``cluster_pt x F`` means ``(𝓝 x ⊓ F).ne_bot``.

TEXT. -/
-- QUOTE:
#check mem_closure_iff_cluster_pt
#check le_principal_iff
#check ne_bot_of_le

example (u : ℕ → ℝ) (M : set ℝ) (x : ℝ) 
  (hux : tendsto u at_top (𝓝 x)) (huM : ∀ᶠ n in at_top, u n ∈ M) : x ∈ closure M :=
sorry
-- QUOTE.

-- SOLUTIONS:
example (u : ℕ → ℝ) (M : set ℝ) (x : ℝ) 
  (hux : tendsto u at_top (𝓝 x)) (huM : ∀ᶠ n in at_top, u n ∈ M) : x ∈ closure M :=
mem_closure_iff_cluster_pt.mpr (ne_bot_of_le $ le_inf hux $ le_principal_iff.mpr huM)
