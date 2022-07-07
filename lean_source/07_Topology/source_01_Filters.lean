import topology.instances.real

open set filter
open_locale topological_space filter

/- TEXT:
.. index:: filter

.. _filters:

Filters
-------

A *filter* on a type ``X`` is a collection of sets of ``X`` that satisfies three
conditions that we will spell out below. The notion
supports two related ideas:

* *limits*, including all the kinds of limits discussed above: finite and infinite limits of sequences, finite and infinite limits of functions at a point or at infinity, and so on.

* *things happening eventually*, including things happening for large enough ``n : ℕ``, or sufficiently near a point ``x``, or for sufficiently close pairs of points, or almost everywhere in the sense of measure theory. Dually, filters can also express the idea of *things happening often*: for arbitrarily large ``n``, at a point in any neighborhood of given a point, etc.

The filters that correspond to these descriptions will be defined later in this section, but we can already name them:

* ``(at_top : filter ℕ)``, made of sets of ``ℕ`` containing ``{n | n ≥ N}`` for some ``N``
* ``𝓝 x``, made of neighborhoods of ``x`` in a topological space
* ``𝓤 X``, made of entourages of a uniform space (uniform spaces generalize metric spaces and topological groups)
* ``μ.a_e`` , made of sets whose complement has zero measure with respect to a measure ``μ``.

The general definition is as follows: a filter ``F : filter X`` is a
collection of sets ``F.sets : set (set X)`` satisfying the following:

* ``F.univ_sets : univ ∈ F.sets``
* ``F.sets_of_superset : ∀ {U V}, U ∈ F.sets → U ⊆ V → V ∈ F.sets``
* ``F.inter_sets : ∀ {U V}, U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets``.

The first condition says that the set of all elements of ``X`` belongs to ``F.sets``.
The second condition says that if ``U`` belongs to ``F.sets`` then anything
containing ``U`` also belongs to ``F.sets``.
The third condition says that ``F.sets`` is closed under finite intersections.
In mathlib, a filter ``F`` is defined to be a structure bundling ``F.sets`` and its
three properties, but the properties carry no additional data,
and it is convenient to blur the distinction between ``F`` and ``F.sets``. We
therefore define ``U ∈ F`` to mean ``U ∈ F.sets``.
This explains why the word ``sets`` appears in the names of some lemmas that
that mention ``U ∈ F``.

It may help to think of a filter as defining a notion of a "sufficiently large" set. The first
condition then says that ``univ`` is sufficiently large, the second one says that a set containing a sufficiently
large set is sufficiently large and the third one says that the intersection of two sufficiently large sets
is sufficiently large.

It may be even  more useful to think of a filter on a type ``X``
as a generalized element of ``set X``. For instance, ``at_top`` is the
"set of very large numbers" and ``𝓝 x₀`` is the "set of points very close to ``x₀``."
One manifestation of this view is that we can associate to any ``s : set X`` the so-called *principal filter*
consisting of all sets that contain ``s``.
This definition is already in mathlib and has a notation ``𝓟`` (localized in the ``filter`` namespace).
For the purpose of demonstration, we ask you to take this opportunity to work out the definition here.
EXAMPLES: -/
-- QUOTE:
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
For our second example, we ask you to define the filter ``at_top : filter ℕ``.
(We could use any type with a preorder instead of ``ℕ``.)
EXAMPLES: -/
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
In the real numbers, a neighborhood of ``x`` is a set containing an open interval
:math:`(x_0 - \varepsilon, x_0 + \varepsilon)`,
defined in mathlib as ``Ioo (x₀ - ε) (x₀ + ε)``.
(This is notion of a neighborhood is only a special case of a more general construction in mathlib.)

With these examples, we can already define what is means for a function ``f : X → Y``
to converge to some ``G : filter Y`` along some ``F : filter X``,
as follows:
BOTH: -/
-- QUOTE:
def tendsto₁ {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) :=
∀ V ∈ G, f ⁻¹' V ∈ F
-- QUOTE.

/- TEXT:
When ``X`` is ``ℕ`` and ``Y`` is ``ℝ``, ``tendsto₁ u at_top (𝓝 x)`` is equivalent to saying that the sequence ``u : ℕ → ℝ``
converges to the real number ``x``. When both ``X`` and ``Y`` are ``ℝ``, ``tendsto f (𝓝 x₀) (𝓝 y₀)``
is equivalent to the familiar notion :math:`\lim_{x \to x₀} f(x) = y₀`.
All of the other kinds of limits mentioned in the introduction are
also equivalent to instances of ``tendsto₁`` for suitable choices of filters on the source and target.

The notion ``tendsto₁`` above is definitionally equivalent to the notion ``tendsto`` that is defined in mathlib,
but the latter is defined more abstractly.
The problem with the definition of ``tendsto₁`` is that it exposes a quantifier and elements of ``G``,
and it hides the intuition that we get by viewing filters as generalized sets. We can
hide the quantifier ``∀ V`` and make the intuition more salient by using more algebraic and set-theoretic machinery.
The first ingredient is the *pushforward* operation :math:`f_*` associated to any map ``f : X → Y``,
denoted ``filter.map f`` in mathlib. Given a filter ``F`` on ``X``, ``filter.map f F : filter Y`` is defined so that
``V ∈ filter.map f F ↔ f ⁻¹' V ∈ F`` holds definitionally.
In this examples file we've opened the ``filter`` namespace so that
``filter.map`` can be written as ``map``. This means that we can rewrite the definition of ``tendsto`` using
the order relation on ``filter Y``, which is reversed inclusion of the set of members.
In other words, given ``G H : filter Y``, we have ``G ≤ H ↔ ∀ V : set Y, V ∈ H → V ∈ G``.
EXAMPLES: -/
-- QUOTE:
def tendsto₂ {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) :=
map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) :
  tendsto₂ f F G ↔ tendsto₁ f F G := iff.rfl
-- QUOTE.

/- TEXT:
It may seem that the order relation on filters is backward. But recall that we can view filters on ``X`` as
generalized elements of ``set X``, via the inclusion of ``𝓟 : set X → filter X`` which maps any set ``s`` to the corresponding principal filter.
This inclusion is order preserving, so the order relation on ``filter`` can indeed be seen as the natural inclusion relation
between generalized sets. In this analogy, pushforward is analogous to the direct image.
And, indeed, ``map f (𝓟 s) = 𝓟 (f '' s)``.

We can now understand intuitively why a sequence ``u : ℕ → ℝ`` converges to
a point ``x₀`` if and only if we have ``map u at_top ≤ 𝓝 x₀``.
The inequality means the "direct image under ``u``" of
"the set of very big natural numbers" is "included" in "the set of points very close to ``x₀``."

As promised, the definition of ``tendsto₂`` does not exhibit any quantifiers or sets.
It also leverages the algebraic properties of the pushforward operation.
First, each ``filter.map f`` is monotone. And, second, ``filter.map`` is compatible with
composition.
EXAMPLES: -/
-- QUOTE:
#check (@filter.map_mono : ∀ {α β} {m : α → β}, monotone (map m))
#check (@filter.map_map : ∀ {α β γ} {f : filter α} {m : α → β} {m' : β → γ},
                            map m' (map m f) = map (m' ∘ m) f)
-- QUOTE.

/- TEXT:
Together these two properties allow us to prove that limits compose, yielding in one shot all 256 variants
of the composition lemma described in the introduction, and lots more.
You can practice proving the following statement using either the definition
of ``tendsto₁`` in terms of the
universal quantifier or the algebraic definition,
together with the two lemmas above.
EXAMPLES: -/
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
The pushforward construction uses a map to push filters from the map source to the map target.
There also a *pullback* operation, ``filter.comap``, going in the other direction.
This generalizes the
preimage operation on sets. For any map ``f``,
``filter.map f`` and ``filter.comap f`` form what is known as a *Galois connection*,
which is to say, they satisfy

  ``filter.map_le_iff_le_comap : filter.map f F ≤ G ↔ F ≤ filter.comap f G``

for every ``F`` and ``G``.
This operation could be used to provided another formulation of ``tendsto`` that would be provably
(but not definitionaly) equivalent to the one in mathlib.

The ``comap`` operation can be used to restrict filters to a subtype. For instance, suppose we have ``f : ℝ → ℝ``,
``x₀ : ℝ`` and ``y₀ : ℝ``, and suppose we want to state that ``f x`` approaches ``y₀`` when ``x`` approaches ``x₀`` within the rational numbers.
We can pull the filter ``𝓝 x₀`` back to ``ℚ`` using the coercion map
``coe : ℚ → ℝ`` and state ``tendsto (f ∘ coe : ℚ → ℝ) (comap coe (𝓝 x₀)) (𝓝 y₀)``.
EXAMPLES: -/
-- QUOTE:
variables (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap (coe : ℚ → ℝ) (𝓝 x₀)
#check tendsto (f ∘ coe) (comap (coe : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)
-- QUOTE.

/- TEXT:
The pullback operation is also compatible with composition, but it *contravariant*,
which is to say, it reverses the order of the arguments.
EXAMPLES: -/
-- QUOTE:
section
variables {α β γ : Type*} (F : filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)
end
-- QUOTE.

/- TEXT:
Let's now shift attention to the plane ``ℝ × ℝ`` and try to understand how the neighborhoods of a point
``(x₀, y₀)`` are related to ``𝓝 x₀`` and ``𝓝 y₀``. There is a product operation
``filter.prod : filter X → filter Y → filter (X × Y)``, denoted by ``×ᶠ``, which answers this question:
EXAMPLES: -/
-- QUOTE:
example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ᶠ 𝓝 y₀ := nhds_prod_eq
-- QUOTE.

/- TEXT:
The product operation is defined in terms of the pullback operation and the ``inf`` operation:

  ``F ×ᶠ G = (comap prod.fst F) ⊓ (comap prod.snd G)``.

Here the ``inf`` operation refers to the lattice structure on ``filter X`` for any type ``X``, whereby
``F ⊓ G`` is the greatest filter that is smaller than both ``F`` and ``G``.
Thus the ``inf`` operation generalizes the notion of the intersection of sets.

A lot of proofs in mathlib use all of the aforementioned structure (``map``, ``comap``, ``inf``, ``sup``, and ``prod``)
to give algebraic proofs about convergence without ever referring to members of filters.
You can practice doing this in a proof of the following lemma, unfolding the definition of ``tendsto``
and ``filter.prod`` if needed.
EXAMPLES: -/
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

-- an alterantive solution
example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
  tendsto f at_top (𝓝 (x₀, y₀)) ↔
  tendsto (prod.fst ∘ f) at_top (𝓝 x₀) ∧ tendsto (prod.snd ∘ f) at_top (𝓝 y₀) :=
begin
  rw nhds_prod_eq,
  unfold tendsto filter.prod,
  rw [le_inf_iff, ← map_le_iff_le_comap, map_map, ← map_le_iff_le_comap, map_map]
end

/- TEXT:
The ordered type ``filter X`` is actually a *complete* lattice,
which is to say, there is a bottom element, there is a top element, and
every set of filters on ``X`` has an ``Inf`` and a ``Sup``.

Note that given the second property in the definition of a filter
(if ``U`` belongs to ``F`` then anything larger than ``U`` also belongs to ``F``),
the first property
(the set of all inhabitants of ``X`` belongs to ``F``) is
equivalent to the property that ``F`` is not the empty collection of sets.
This shouldn't be confused with the more subtle question as to whether
the empty set is an *element* of ``F``. The
definition of a filter does not prohibit ``∅ ∈ F``,
but if the empty set is in ``F`` then
every set is in ``F``, which is to say, ``∀ U : set X, U ∈ F``.
In this case, ``F`` is a rather trivial filter, which is precisely the
bottom element of the complete lattice ``filter X``.
This contrasts with the definition of filters in
Bourbaki, which doesn't allow filters containing the empty set.

Because we include the trivial filter in our definition, we sometimes need to explicitly assume
nontriviality in some lemmas.
In return, however, the theory has nicer global properties.
We have already seen that including the trivial filter gives us a
bottom element. It also allows us to define ``principal : set X → filter X``,
which maps  ``∅`` to ``⊥``, without additing a precondition to rule out the empty set.
And it allows us to define the pullback operation without a precondition as well.
Indeed, it can happen that ``comap f F = ⊥`` although ``F ≠ ⊥``. For instance,
given ``x₀ : ℝ`` and ``s : set ℝ``, the pullback of ``𝓝 x₀`` under the coercion
from the subtype corresponding to ``s`` is nontrivial if and only if ``x₀`` belongs to the
closure of ``s``.

In order to manage lemmas that do need to assume some filter is nontrivial, mathlib has
a type class ``filter.ne_bot``, and the library has lemmas that assume
``(F : filter X) [F.ne_bot]``. The instance database knows, for example, that ``(at_top : filter ℕ).ne_bot``,
and it knows that pushing forward a nontrivial filter gives a nontrivial filter.
As a result, a lemma assuming ``[F.ne_bot]`` will automatically apply to ``map u at_top`` for any sequence ``u``.

Our tour of the algebraic properties of filters and their relation to limits is essentially done,
but we have not yet justified our claim to have recaptured the usual limit notions.
Superficially, it may seem that ``tendsto u at_top (𝓝 x₀)``
is stronger than the notion of convergence defined in :numref:`sequences_and_convergence` because we ask that *every* neighborhood of ``x₀``
has a preimage belonging to ``at_top``, whereas the usual definition only requires
this for the standard neighborhoods ``Ioo (x₀ - ε) (x₀ + ε)``.
The key is that, by definition, every neighborhood contains such a standard one.
This observation leads to the notion of a *filter basis*.

Given ``F : filter X``,
a family of sets `s : ι → set X` is a basis for ``F`` if for every set ``U``,
we have ``U ∈ F`` if and only if it contains some ``s i``. In other words, formally speaking,
``s`` is a basis if it satisfies
``∀ U : set X, U ∈ F ↔ ∃ i, s i ⊆ U``. It is even more flexible to consider
a predicate on ``ι`` that selects only some of the values ``i`` in the indexing type.
In the case of ``𝓝 x₀``, we want ``ι`` to be ``ℝ``, we write ``ε`` for ``i``, and the predicate should select the positive values of ``ε``.
So the fact that the sets ``Ioo  (x₀ - ε) (x₀ + ε)`` form a basis for the
neighborhood topology on ``ℝ`` is stated as follows:
EXAMPLES: -/
-- QUOTE:
example (x₀ : ℝ) : has_basis (𝓝 x₀) (λ ε : ℝ, 0 < ε) (λ ε, Ioo (x₀ - ε) (x₀ + ε)) :=
nhds_basis_Ioo_pos x₀
-- QUOTE.

/- TEXT:
There is also a nice basis for the filter ``at_top``. The lemma
``filter.has_basis.tendsto_iff`` allows
us to reformulate a statement of the form ``tendsto f F G``
given bases for ``F`` and ``G``.
Putting these pieces together gives us essentially the notion of convergence
that we used in :numref:`sequences_and_convergence`.
EXAMPLES: -/
-- QUOTE:
example (u : ℕ → ℝ) (x₀ : ℝ) :
  tendsto u at_top (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) :=
begin
  have : at_top.has_basis (λ n : ℕ, true) Ici := at_top_basis,
  rw this.tendsto_iff (nhds_basis_Ioo_pos x₀),
  simp
end
-- QUOTE.

/- TEXT:
We now show how filters facilitate working with properties that hold for sufficiently large numbers
or for points that are sufficiently close to a given point. In :numref:`sequences_and_convergence`, we were often faced with the situation where
we knew that some property ``P n`` holds for sufficiently large ``n`` and that some
other property ``Q n`` holds for sufficiently large ``n``.
Using ``cases`` twice gave us ``N_P`` and ``N_Q`` satisfying
``∀ n ≥ N_P, P n`` and ``∀ n ≥ N_Q, Q n``. Using ``set N := max N_P N_Q``, we could
eventually prove ``∀ n ≥ N, P n ∧ Q n``.
Doing this repeatedly becomes tiresome.

We can do better by noting that the statement "``P n`` and ``Q n`` hold for large enough ``n``" means
that we have ``{n | P n} ∈ at_top`` and ``{n | Q n} ∈ at_top``.
The fact that ``at_top`` is a filter implies that the intersection of two elements of ``at_top``
is again in ``at_top``, so we have ``{n | P n ∧ Q n} ∈ at_top``.
Writing ``{n | P n} ∈ at_top`` is unpleasant,
but we can use the more suggestive notation ``∀ᶠ n in at_top, P n``.
Here the superscripted ``f`` stands for "filter."
You can think of the notation as saying that for all ``n`` in the "set of very large numbers," ``P n`` holds. The ``∀ᶠ``
notation stands for ``filter.eventually``, and the lemma ``filter.eventually.and`` uses the intersection property of filters to do what we just described:
EXAMPLES: -/
-- QUOTE:
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in at_top, P n) (hQ : ∀ᶠ n in at_top, Q n) :
  ∀ᶠ n in at_top, P n ∧ Q n := hP.and hQ
-- QUOTE.

/- TEXT:
This notation is so convenient and intuitive that we also have specializations
when ``P`` is an equality or inequality statement. For example, let ``u`` and ``v`` be
two sequences of real numbers, and let us show that if
``u n`` and ``v n`` coincide for sufficiently large ``n`` then
``u`` tends to ``x₀`` if and only if ``v`` tends to ``x₀``.
First we'll use the generic ``eventually`` and then the one
specialized for the equality predicate, ``eventually_eq``. The two statements are
definitionaly equivalent so the same proof work in both cases.
EXAMPLES: -/
-- QUOTE:
example (u v : ℕ → ℝ) (h : ∀ᶠ n in at_top, u n = v n) (x₀ : ℝ) :
  tendsto u at_top (𝓝 x₀) ↔ tendsto v at_top (𝓝 x₀) :=
tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[at_top] v) (x₀ : ℝ) :
  tendsto u at_top (𝓝 x₀) ↔ tendsto v at_top (𝓝 x₀) :=
tendsto_congr' h
-- QUOTE.

/- TEXT:
It is instructive to review the definition of filters in terms of ``eventually``.
Given ``F : filter X``, for any predicates ``P`` and ``Q`` on ``X``,

* the condition ``univ ∈ F`` ensures ``(∀ x, P x) → ∀ᶠ x in F, P x``,
* the condition ``U ∈ F → U ⊆ V → V ∈ F`` ensures ``(∀ᶠ x in F, P x) → (∀ x, P x → Q x) → ∀ᶠ x in F, Q x``, and
* the condition ``U ∈ F → V ∈ F → U ∩ V ∈ F`` ensures ``(∀ᶠ x in F, P x) → (∀ᶠ x in F, Q x) → ∀ᶠ x in F, P x ∧ Q x``.
EXAMPLES: -/
-- QUOTE:
#check @eventually_of_forall
#check @eventually.mono
#check @eventually.and
-- QUOTE.

/- TEXT:
The second item, corresponding to ``eventually.mono``, supports nice ways
of using filters, especially when combined
with ``eventually.and``. The ``filter_upwards`` tactic allows us to combine them.
Compare:
EXAMPLES: -/
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
(aka "the set consisting of almost every point") is not very useful as the source or target of ``tendsto``, but it can be conveniently
used with ``eventually`` to say that a property holds for almost every point.

There is a dual version of ``∀ᶠ x in F, P x``, which is occasionally useful:
``∃ᶠ x in F, P x`` means
``{x | ¬P x} ∉ F``. For example, ``∃ᶠ n in at_top, P n`` means there are arbitrarily large ``n`` such that ``P n`` holds.
The ``∃ᶠ`` notation stands for ``filter.frequently``.

For a more sophisticated example, consider the following statement about a sequence
``u``, a set ``M``, and a value ``x``:

  If ``u`` converges to ``x`` and ``u n`` belongs to ``M`` for
  sufficiently large ``n`` then ``x`` is in the closure of ``M``.

This can be formalized as follows:

  ``tendsto u at_top (𝓝 x) → (∀ᶠ n in at_top, u n ∈ M) → x ∈ closure M``.

This is a special case of the theorem ``mem_closure_of_tendsto`` from the
topology library.
See if you can prove it using the quoted lemmas,
using the fact that ``cluster_pt x F`` means ``(𝓝 x ⊓ F).ne_bot``.

EXAMPLES: -/
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
