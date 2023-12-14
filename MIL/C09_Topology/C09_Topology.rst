.. _topology:

.. index:: topology

Topology
========

Calculus is based on the concept of a function, which is used to model
quantities that depend on one another.
For example, it is common to study quantities that change over time.
The notion of a *limit* is also fundamental.
We may say that the limit of a function :math:`f(x)` is a value :math:`b`
as :math:`x` approaches a value :math:`a`,
or that :math:`f(x)` *converges to* :math:`b` as :math:`x` approaches :math:`a`.
Equivalently, we may say that a :math:`f(x)` approaches :math:`b` as :math:`x`
approaches a value :math:`a`, or that it *tends to* :math:`b`
as :math:`x` tends to :math:`a`.
We have already begun to consider such notions in :numref:`sequences_and_convergence`.

*Topology* is the abstract study of limits and continuity.
Having covered the essentials of formalization in Chapters :numref:`%s <basics>`
to :numref:`%s <structures>`,
in this chapter, we will explain how topological notions are formalized in Mathlib.
Not only do topological abstractions apply in much greater generality,
but that also, somewhat paradoxically, make it easier to reason about limits
and continuity in concrete instances.

Topological notions build on quite a few layers of mathematical structure.
The first layer is naive set theory,
as described in :numref:`Chapter %s <sets_and_functions>`.
The next layer is the theory of *filters*, which we will describe in :numref:`filters`.
On top of that, we layer
the theories of *topological spaces*, *metric spaces*, and a slightly more exotic
intermediate notion called a *uniform space*.

Whereas previous chapters relied on mathematical notions that were likely
familiar to you,
the notion of a filter less well known,
even to many working mathematicians.
The notion is essential, however, for formalizing mathematics effectively.
Let us explain why.
Let ``f : ℝ → ℝ`` be any function. We can consider
the limit of ``f x`` as ``x`` approaches some value ``x₀``,
but we can also consider the limit of ``f x`` as ``x`` approaches infinity
or negative infinity.
We can moreover consider the limit of ``f x`` as ``x`` approaches ``x₀`` from
the right, conventionally written ``x₀⁺``, or from the left,
written  ``x₀⁻``. There are variations where ``x`` approaches ``x₀`` or ``x₀⁺``
or ``x₀⁻`` but
is not allowed to take on the value ``x₀`` itself.
This results in at least eight ways that ``x`` can approach something.
We can also restrict to rational values of ``x``
or place other constraints on the domain, but let's stick to those 8 cases.

We have a similar variety of options on the codomain:
we can specify that ``f x`` approaches a value from the left or right,
or that it approaches positive or negative infinity, and so on.
For example, we may wish to say that ``f x`` tends to ``+∞``
when ``x`` tends to ``x₀`` from the right without
being equal to ``x₀``.
This results in 64 different kinds of limit statements,
and we haven't even begun to deal with limits of sequences,
as we did in :numref:`sequences_and_convergence`.

The problem is compounded even further when it comes to the supporting lemmas.
For instance, limits compose: if
``f x`` tends to ``y₀`` when ``x`` tends to ``x₀`` and
``g y`` tends to ``z₀`` when ``y`` tends to ``y₀`` then
``g ∘ f x`` tends to ``z₀`` when ``x`` tends to ``x₀``.
There are three notions of "tends to" at play here,
each of which can be instantiated in any of the eight ways described
in the previous paragraph.
This results in 512 lemmas, a lot to have to add to a library!
Informally, mathematicians generally prove two or three of these
and simply note that the rest can be proved "in the same way."
Formalizing mathematics requires making the relevant notion of "sameness"
fully explicit, and that is exactly what Bourbaki's theory of filters
manages to do.
