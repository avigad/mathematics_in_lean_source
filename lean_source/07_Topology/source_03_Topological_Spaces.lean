import topology.instances.real
import analysis.normed_space.banach_steinhaus

open set filter
open_locale topological_space filter

/- TEXT:
.. index:: topological space

.. _topological_spaces:

Topological spaces
------------------

Fundamentals
^^^^^^^^^^^^

We now go up in generality and introduce topological spaces. We will review the two main ways to define
topological spaces and then explain how the category of topological spaces is much better behaved than
the category of metric spaces. Note that we won't be using mathlib category theory here, only having 
a somewhat categorical point of view.

The first way to think about the transition from metric spaces to topological spaces is that we only
remember the notion of open sets (or equivalently the notion of closed sets). From this point of view,
a topological space is a type equipped with a collection of sets that are called open sets. This collection
has to satisfy a number of axioms presented below (this collection is slightly redundant but we will ignore that).

BOTH: -/

-- QUOTE:
section

variables {X : Type*} [topological_space X]

example : is_open (univ : set X) := is_open_univ

example : is_open (∅ : set X) := is_open_empty

example {ι : Type*} {s : ι → set X} (hs : ∀ i, is_open $ s i) : 
  is_open (⋃ i, s i) := 
is_open_Union hs

example {ι : Type*} [fintype ι] {s : ι → set X} (hs : ∀ i, is_open $ s i) : 
  is_open (⋂ i, s i) := 
is_open_Inter hs


-- QUOTE.

/- TEXT:

Closed sets are then defined as sets whose complement  is open. A function between topological spaces
is (globally) continuous if all preimages of open sets are open. 
BOTH: -/

-- QUOTE:
variables {Y : Type*} [topological_space Y]

example {f : X → Y} : continuous f ↔ ∀ s, is_open s → is_open (f ⁻¹' s) :=
continuous_def

-- QUOTE.

/- TEXT:
With this definition we already see that, compared to metric spaces, topological spaces only remember
enough information to talk about continuous functions: two topological structures on a type are
the same if and only if they have the same continuous functions (indeed the identity function will
be continuous in both direction if and only if the two structures have the same open sets).

However as soon as we move on to continuity at a point we see the limitations of the approach based 
on open sets. In mathlib it is much more frequent to think of topological spaces as types equipped
with a neighborhood filter ``𝓝 x`` attached to each point ``x`` (the corresponding function
``X → filter X`` satisfies certain conditions explained further down). Remember from the filters section that
these gadget play two related roles. First ``𝓝 x`` is seen as the generalized set of points of ``X``
that are close to ``x``. And then it is seen as giving a way to say, for any predicate ``P : X → Prop``,
that this predicates holds for points that are close enough to ``x``. Let us state
that ``f : X → Y`` is continuous at ``x``. The purely filtery way is to say that the direct image under
``f`` of the generalized set of points that are close to ``x`` is contained in the generalized set of 
points that are close to ``f x``. Recall this spelled either ``map f (𝓝 x) ≤ 𝓝 (f x)``
or ``tendsto f (𝓝 x) (𝓝 (f x))``. 

BOTH: -/

-- QUOTE:

example {f : X → Y} {x : X} : continuous_at f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) :=
iff.rfl

-- QUOTE.

/- TEXT:
One can also spell it using both neighborhoods seen as ordinary sets and a neighborhood filter 
seen as a generalized set: "for any neighborhood ``U`` of ``f x``, all points close to ``x`` 
are sent to ``U``". Note that the proof is again ``iff.rfl``, this point of view is definitionally 
equivalent to the previous one.

BOTH: -/

-- QUOTE:
example {f : X → Y} {x : X} : continuous_at f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U :=
iff.rfl
-- QUOTE.

/- TEXT:
We now explain how to go from one point of view to the other. In terms of open sets, we can
simply define members of ``𝓝 x`` as sets that contain an open set containing ``x``.


BOTH: -/

-- QUOTE:
example {x : X} {s : set X} : s ∈ 𝓝 x ↔ ∃ t ⊆ s, is_open t ∧ x ∈ t :=
mem_nhds_iff
-- QUOTE.

/- TEXT:
To go in the other direction we need to discuss the condition that ``𝓝 : X → filter X`` must satisfy
in order to be the neighborhood function of a topology. 

The first constraint is that ``𝓝 x``, seen as a generalized set, contains the set ``{x}`` seen as the generalized set
``pure x`` (explaining this weird name would be too much of a digression, so we simply accept it for now). 
Another way to say it is that if a predicate holds for points close to ``x`` then it holds at ``x``.

BOTH: -/

-- QUOTE:
example (x : X) : pure x ≤ 𝓝 x := pure_le_nhds x

example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x := 
pure_le_nhds x h
-- QUOTE.

/- TEXT:
Then a more subtle requirement is that, for any predicate ``P : X → Prop`` and any ``x``, if ``P y`` holds for ``y`` close
to ``x`` then for ``y`` close to ``x`` and ``z`` close to ``y``, ``P z`` holds. More precisely we have:
BOTH: -/

-- QUOTE:

example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
eventually_eventually_nhds.mpr h

-- QUOTE.

/- TEXT:
Those two results characterize the functions ``X → filter X`` that are neighborhood functions for a topological space
structure on ``X``. There is a still a function ``topological_space.mk_of_nhds : (X → filter X) → topological_space X``
but it will give back its input as a neighborhood function only if it satisfies the above two constraints.
More precisely we have a lemma ``topological_space.nhds_mk_of_nhds`` saying that in a different way and our
next exercise deduces this different way from how we stated it above. 
BOTH: -/

#check topological_space.mk_of_nhds
#check topological_space.nhds_mk_of_nhds.

-- QUOTE:

example {α : Type*} (n : α → filter α) (H₀ : ∀ a, pure a ≤ n a) 
  (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → (∀ᶠ y in n a, ∀ᶠ x in n y, p x)) :
  ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' :=
sorry

-- QUOTE.

-- SOLUTIONS:
example {α : Type*} (n : α → filter α) (H₀ : ∀ a, pure a ≤ n a) 
  (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → (∀ᶠ y in n a, ∀ᶠ x in n y, p x)) :
  ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' :=
begin
  intros a s s_in,
  refine ⟨{y | s ∈ n y}, H a (λ x, x ∈ s) s_in, _, by tauto⟩,
  rintros y (hy : s ∈ n y),
  exact H₀ y hy
end
-- BOTH:
end
-- BOTH.
/- TEXT:
Note that ``topological_space.mk_of_nhds`` is not so frequently used, but it still good to know in what
precise sense the neighborhood filters is all there is in a topological space structure.

The next thing to know in order to efficiently use topological spaces in mathlib is that we use a lot
of formal properties of ``topological_space : Type u → Type u``. From a purely mathematical point of view,
those formal properties are a very clean way to explain how topological spaces solve issues that metric spaces 
have. From this point of view, the issues solved by topological spaces is that metric spaces enjoy very 
little fonctoriality, and have very bad categorical properties in general. This comes on top of the fact 
already discussed that metric spaces contain a lot of geometrical information that is not topologically relevant. 

Let us focus on fonctoriality first. A metric space structure can be induced on a subset or,
equivalently, it can be pulled back by an injective map. But that's pretty much everything.
They cannot be pulled back by general map or pushed forward, even by surjective maps.

In particular there is no sensible distance to put on a quotient of a metric space or on an uncountable
products of metric spaces. Consider for instance the type ``ℝ → ℝ``, seen as
a product of copies of ``ℝ`` indexed by ``ℝ``. We would like to say that pointwise convergence of
sequences of functions is a respectable notion of convergence. But there is no distance on
``ℝ → ℝ`` that gives this notion of convergence. Relatedly, there is no distance ensuring that
a map ``f : X → (ℝ → ℝ)`` is continuous if and only ``λ x, f x t`` is continuous for every ``t : ℝ``.

We now review the data used to solve all those issues. First we can use any map ``f : X → Y`` to
push or pull topologies from one side to the other. Those two operations form a Galois connection.

BOTH: -/

-- QUOTE:
variables {X Y : Type*}

example (f : X → Y) : topological_space X → topological_space Y :=
topological_space.coinduced f

example (f : X → Y) : topological_space Y → topological_space X :=
topological_space.induced f

example (f : X → Y) (T_X : topological_space X) (T_Y : topological_space Y) :
  topological_space.coinduced f T_X ≤ T_Y ↔ T_X ≤ topological_space.induced f T_Y :=
coinduced_le_iff_le_induced

-- QUOTE.

/- TEXT:
Those operations are compactible with composition of functions. 
As usual, pushing forward is covariant and pulling back is contravariant, see ``coinduced_compose`` and ``induced_compose``.
On paper we will use notations :math:`f_*T` for ``topological_space.coinduced f T`` and
:math:`f^*T` for ``topological_space.induced f T``.
BOTH: -/

#check coinduced_compose
#check induced_compose.

/- TEXT:

Then the next big piece is a complete lattice structure on ``topological_structure X`` 
for any given structure. If you think of topologies are being primarily the data of open sets then you expect
the order relation on ``topological_structure X`` to come from ``set (set X)``, ie you expect ``t ≤ t'``
if a set ``u`` is open for ``t'`` as soon as it is open for ``t``. However we already know that mathlib focuses
on neighborhoods more than open sets so, for any ``x : X`` we want ``λ T : topological_space X, @nhds X T x``
to be order preserving. And we know the order relation on ``filter X`` is designed to ensure an order
preserving ``principal : set X → filter X``, allowing to see filters as generalized sets.
So the order relation we do use on  ``topological_structure X`` is opposite to the one coming from ``set (set X)``.

BOTH: -/

-- QUOTE:
example {T T' : topological_space X} :
  T ≤ T' ↔ ∀ s, T'.is_open s → T.is_open s  :=
iff.rfl

-- QUOTE.

/- TEXT:

Now we can recover continuity by combining the push-foward (or pull-back) operation with the order relation.

BOTH: -/

-- QUOTE:
example (T_X : topological_space X) (T_Y : topological_space Y) (f : X → Y) :
  continuous f ↔ topological_space.coinduced f T_X ≤ T_Y :=
continuous_iff_coinduced_le

-- QUOTE.

/- TEXT:
With this definition and the compatibility of push-forward and composition, we 
get for free the universal property that, for any topological space :math:`Z`,
a function :math:`g : Y → Z` is continuous for the topology :math:`f_*T_X` if and only if
:math:`g ∘ f` is continuous.

.. math::
  g \text{ continuous } &⇔ g_*(f_*T_X) ≤ T_Z \\
  &⇔ (g ∘ f)_* T_X ≤ T_Z \\
  &⇔ g ∘ f \text{ continuous}


BOTH: -/

-- QUOTE:

example {Z : Type*} (f : X → Y) 
  (T_X : topological_space X) (T_Z : topological_space Z) (g : Y → Z) :
  @continuous Y Z (topological_space.coinduced f T_X) T_Z g ↔ @continuous X Z T_X T_Z (g ∘ f) :=
by rw [continuous_iff_coinduced_le, coinduced_compose, continuous_iff_coinduced_le]

-- QUOTE.

/- TEXT:

So we already get quotient topologies (using the projection map as ``f``). This wasn't using that 
``topological_space X`` is a complete lattice for all ``X``. Let's now see how all this structure
proves the existence of the product topology by abstract non-sense.
We considered the case of ``ℝ → ℝ`` above, but let's now consider the general case of ``Π i, X i`` for
some ``ι : Type*`` and ``X : ι → Type*``. We want, for any topological space ``Z`` and any function
``f : Z → Π i, X i``, that ``f`` is continuous if and only if ``(λ x, x i) ∘ f`` is continuous.
Let us explore that constraint "on papar" using notation :math:`p_i` for the projection 
``(λ (x : Π i, X i), x i)``:

.. math::
  (∀ i, p_i ∘ f \text{ continuous}) &⇔ ∀ i, (p_i ∘ f)_* T_Z ≤ T_{X_i} \\
  &⇔ ∀ i, (p_i)_* f_* T_Z ≤ T_{X_i}\\
  &⇔ ∀ i, f_* T_Z ≤ (p_i)^*T_{X_i}\\ 
  &⇔  f_* T_Z ≤ \inf \left[(p_i)^*T_{X_i}\right]

So we see that what is the topology we want on ``Π i, X i``:
BOTH: -/

-- QUOTE:
example (ι : Type*) (X : ι → Type*) (T_X : Π i, topological_space $ X i) :
  (Pi.topological_space : topological_space (Π i, X i)) = ⨅ i, topological_space.induced (λ x, x i) (T_X i) :=
rfl

-- QUOTE.

/- TEXT:

This ends our tour of how mathlib thinks that topological spaces fix defects of the theory of metric spaces
by being a more functorial theory and having a complete lattice structure for any fixed type.

Separation and countability
^^^^^^^^^^^^^^^^^^^^^^^^^^^

We saw that the category of topological spaces have very nice properties. The price to pay for
this is existence of rather pathological topological spaces. 
There are a number of assumptions you can make on a topological space to ensure its behavior
is closer to what metric spaces do. The most important is ``t2_space``, also called "Hausdorff", 
that will ensure that limits are unique.
A stronger separation property is regularity that ensure that each point has a basis of closed
neighborhood. 

BOTH: -/

-- QUOTE:

example [topological_space X] [t2_space X] {u : ℕ → X} {a b : X} 
  (ha : tendsto u at_top (𝓝 a)) (hb : tendsto u at_top (𝓝 b)) : a = b :=
tendsto_nhds_unique ha hb

example [topological_space X] [regular_space X] (a : X) :
    (𝓝 a).has_basis (λ (s : set X), s ∈ 𝓝 a ∧ is_closed s) id :=
closed_nhds_basis a
-- QUOTE.

/- TEXT:
Note that, in every topological space, each point has a basis of open neighborhood, by definition.

BOTH: -/

-- QUOTE:
example [topological_space X] {x : X} : (𝓝 x).has_basis (λ t : set X, t ∈ 𝓝 x ∧ is_open t) id :=
nhds_basis_opens' x
-- QUOTE.

/- TEXT:
Our main goal is now to prove the basic theorem which allows extension by continuity.
From Bourbaki's general topology book, I.8.5, Theorem 1 (taking only the non-trivial implication):

Let :math:`X` be a topological space, :math:`A` a dense subset of :math:`X`, :math:`f : A → Y`  
a continuous mapping of :math:`A` into a regular space :math:`Y`. If, for each :math:`x` in :math:`X`, 
:math:`f(y)` tends to a limit in :math:`Y` when :math:`y` tends to :math:`x`
while remaining in :math:`A` then there exists a continuous extension :math:`φ` of :math:`f` to 
:math:`X`.

Actually ``mathlib`` contains a more general version of the above lemma, ``dense_inducing.continuous_at_extend``,
but we'll stick to Bourbaki's version here.

Remember that, given ``A : set X``, ``↥A`` is the subtype associated to ``A``, and Lean will automatically
insert that funny up arrow when needed. And the (inclusion) coercion map is ``coe : A → X``.
The assumption "tends to :math:`x` while remaining in :math:`A`" corresponds to the pull-back filter
``comap coe (𝓝 x)``.

Let's prove first an auxiliary lemma, extracted to simplify the context
(in particular we don't need Y to be a topological space here).

BOTH: -/

-- QUOTE:
lemma aux {X Y A : Type*} [topological_space X] {c : A → X} {f : A → Y} {x : X} {F : filter Y}
  (h : tendsto f (comap c (𝓝 x)) F) {V' : set Y} (V'_in : V' ∈ F) :
  ∃ V ∈ 𝓝 x, is_open V ∧ c ⁻¹' V ⊆ f ⁻¹' V' :=
sorry

-- QUOTE.

-- SOLUTIONS:
example {X Y A : Type*} [topological_space X] {c : A → X} {f : A → Y} {x : X} {F : filter Y}
  (h : tendsto f (comap c (𝓝 x)) F) {V' : set Y} (V'_in : V' ∈ F) :
  ∃ V ∈ 𝓝 x, is_open V ∧ c ⁻¹' V ⊆ f ⁻¹' V' :=
begin
  simpa [and_assoc] using ((nhds_basis_opens' x).comap c).tendsto_left_iff.mp h V' V'_in
end

/- TEXT:
Let's now turn to the main proof of the extension by continuity theorem.

When Lean needs a topology on ``↥A`` it will use the induced topology, thanks to the instance
``subtype.topological_space``.
This all happens automatically. The only relevant lemma is
``nhds_induced coe : ∀ a : ↥A, 𝓝 a = comap coe (𝓝 ↑a)``
(this is actually a general lemma about induced topologies).

The proof outline is:

The main assumption and the axiom of choice give a function ``φ`` such that
``∀ x, tendsto f (comap coe $ 𝓝 x) (𝓝 (φ x))``
(because ``Y`` is Hausdorff, ``φ`` is entirely determined, but we won't need that until we try to
prove that ``φ`` indeed extends ``f``).

Let's first prove ``φ`` is continuous. Fix any ``x : X``.
Since ``Y`` is regular, it suffices to check that for every *closed* neighborhood
``V'`` of ``φ x``, ``φ ⁻¹' V' ∈ 𝓝 x``.
The limit assumption gives (through the auxiliary lemma above)
some ``V ∈ 𝓝 x`` such ``is_open V ∧ coe ⁻¹' V ⊆ f ⁻¹' V'``.
Since ``V ∈ 𝓝 x``, it suffices to prove ``V ⊆ φ ⁻¹' V'``, ie  ``∀ y ∈ V, φ y ∈ V'``.
Let's fix ``y`` in ``V``. Because ``V`` is *open*, it is a neighborhood of ``y``.
In particular ``coe ⁻¹' V ∈ comap coe (𝓝 y)`` and a fortiori ``f ⁻¹' V' ∈ comap coe (𝓝 y)``.
In addition ``comap coe $ 𝓝 y ≠ ⊥`` because ``A`` is dense.
Because we know ``tendsto f (comap coe $ 𝓝 y) (𝓝 (φ y))`` this implies
``φ y ∈ closure V'`` and, since ``V'`` is closed, we have proved ``φ y ∈ V'``.

It remains to prove that ``φ`` extends ``f``. This is were continuity of ``f`` enters the discussion,
together with the fact that ``Y`` is Hausdorff.
BOTH: -/

-- QUOTE:

example [topological_space X] [topological_space Y] [regular_space Y] 
  {A : set X} (hA : ∀ x, x ∈ closure A)
  {f : A → Y} (f_cont : continuous f)
  (hf : ∀ x : X, ∃ c : Y, tendsto f (comap coe $ 𝓝 x) $ 𝓝 c) :
  ∃ φ : X → Y, continuous φ ∧ ∀ a : A, φ a = f a :=
sorry
-- QUOTE.

-- SOLUTIONS:

example [topological_space X] [topological_space Y] [regular_space Y] {A : set X} (hA : ∀ x, x ∈ closure A)
  {f : A → Y} (f_cont : continuous f)
  (hf : ∀ x : X, ∃ c : Y, tendsto f (comap coe $ 𝓝 x) $ 𝓝 c) :
  ∃ φ : X → Y, continuous φ ∧ ∀ a : A, φ a = f a :=
begin
  choose φ hφ using hf,
  use φ,
  split,
  { rw continuous_iff_continuous_at,
    intros x,
    suffices : ∀ V' ∈ 𝓝 (φ x), is_closed V' → φ ⁻¹' V' ∈ 𝓝 x,
      by simpa [continuous_at, (closed_nhds_basis _).tendsto_right_iff],
    intros V' V'_in V'_closed,
    obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, is_open V ∧ coe ⁻¹' V ⊆ f ⁻¹' V',
    { exact aux (hφ x) V'_in },
    suffices : ∀ y ∈ V, φ y ∈ V',
      from mem_of_superset V_in this,
    intros y y_in,
    have hVx : V ∈ 𝓝 y := V_op.mem_nhds y_in,
    haveI : (comap (coe : A → X) (𝓝 y)).ne_bot := by simpa [mem_closure_iff_comap_ne_bot] using hA y,
    apply V'_closed.mem_of_tendsto (hφ y),
    exact mem_of_superset (preimage_mem_comap hVx) hV },
  { intros a,
    have lim : tendsto f (𝓝 a) (𝓝 $ φ a),
      by simpa [nhds_induced] using hφ a,
    exact tendsto_nhds_unique lim f_cont.continuous_at },
end


/- TEXT:
In addition to separation property, the main kind of assumption you can make on a topological
space to bring it closer to metric spaces is countability assumption. The main one is first countability
asking that every point has a countable neighborhood basic. In particular this ensures that closure
of sets can be understood using sequences.

BOTH: -/

-- QUOTE:

example [topological_space X] [topological_space.first_countable_topology X] {s : set X} {a : X} :
  a ∈ closure s ↔ ∃ (u : ℕ → X), (∀ n, u n ∈ s) ∧ tendsto u at_top (𝓝 a) :=
mem_closure_iff_seq_limit

-- QUOTE.

/- TEXT:
Compactness
^^^^^^^^^^^

Let us now discuss how compactness is defined for topological spaces. As usual there are several ways
to think about it and mathlib goes for the filter version.

We first need to define cluster points of filters. Given a filter ``F`` on a topological space ``X``,
a point ``x : X`` is a cluster point of ``F`` if ``F``, seen as a generalized set, has non-empty intersection
with the generalized set of points that are close to ``x``.

Then we can say that a set ``s`` is compact if every nonempty generalized set ``F`` contained in ``s``,
ie such that ``F ≤ 𝓟 s``, has a cluster point in ``s``. 

BOTH: -/

-- QUOTE:
variables [topological_space X]

example {F : filter X} {x : X} : cluster_pt x F ↔ ne_bot (𝓝 x ⊓ F) :=
iff.rfl

example {s : set X} : 
  is_compact s ↔ ∀ (F : filter X) [ne_bot F], F ≤ 𝓟 s → ∃ a ∈ s, cluster_pt a F :=
iff.rfl
-- QUOTE.

/- TEXT:
For instance if ``F`` is ``map u at_top``, the image under ``u : ℕ → X`` of ``at_top``, the generalized set 
of very large natural numbers, then the assumption ``F ≤ 𝓟 s`` means that ``u n`` belongs to ``s`` for ``n``
large enough. Saying that ``x`` is a cluster point of ``map u at_top`` says the image of very large numbers
intersects the set of points that are close to ``x``. In case ``𝓝 x`` has a countable basis, we can
interpret this as saying that ``u`` has a subsequence converging to ``x``, and we get back what compactness
looks like in metric spaces.
BOTH: -/

-- QUOTE:
example [topological_space.first_countable_topology X] 
  {s : set X} {u : ℕ → X} (hs : is_compact s) (hu : ∀ n, u n ∈ s) :
  ∃ (a ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 a) :=
hs.tendsto_subseq hu
-- QUOTE.

/- TEXT:
Cluster points behave nicely with continuous functions.

BOTH: -/

-- QUOTE:

variables [topological_space Y]

example {x : X} {F : filter X} {G : filter Y} (H : cluster_pt x F)
  {f : X → Y} (hfx : continuous_at f x) (hf : tendsto f F G) :
  cluster_pt (f x) G :=
cluster_pt.map H hfx hf
-- QUOTE.

/- TEXT:
As an exercise, we will prove that the image of a compact set under a continuous map is
compact. In addition to what we saw already, you should use ``filter.push_pull`` and
``ne_bot.of_map``.
BOTH: -/

-- QUOTE:
example [topological_space Y] {f : X  → Y} (hf : continuous f) 
  {s : set X} (hs : is_compact s) : is_compact (f '' s) :=
begin
  intros F F_ne F_le,
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F,
  { sorry },
  haveI Hne : (𝓟 s ⊓ comap f F).ne_bot,
  { sorry },
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s, from inf_le_left,
  sorry
end
-- QUOTE.

-- SOLUTIONS:
example [topological_space Y] {f : X  → Y} (hf : continuous f) 
  {s : set X} (hs : is_compact s) : is_compact (f '' s) :=
begin
  intros F F_ne F_le,
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F,
  { rw [filter.push_pull, map_principal] },
  haveI Hne : (𝓟 s ⊓ comap f F).ne_bot,
  { apply ne_bot.of_map,
    rwa [map_eq, inf_of_le_right F_le] },
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s, from inf_le_left,
  rcases hs Hle with ⟨x, x_in, hx⟩,
  refine ⟨f x, mem_image_of_mem f x_in, _⟩,
  apply hx.map hf.continuous_at,
  rw [tendsto, map_eq],
  exact inf_le_right
end

/- TEXT:


One can also express compactness in terms of open covers: ``s`` is compact if every family of open sets that
cover ``s`` has a finite covering sub-family.

BOTH: -/

-- QUOTE:
example {ι : Type*} {s : set X} (hs : is_compact s)
  (U : ι → set X) (hUo : ∀ i, is_open (U i)) (hsU : s ⊆ ⋃ i, U i) :
  ∃ t : finset ι, s ⊆ ⋃ i ∈ t, U i :=
hs.elim_finite_subcover U hUo hsU

-- QUOTE.

/- TEXT:
A topological space ``X`` is compact if ``(univ : set X)`` is compact.
BOTH: -/

-- QUOTE:
example [compact_space X] : is_compact (univ : set X) :=
compact_univ
-- QUOTE.
