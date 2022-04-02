.. _topology:

.. index:: topology

Topology
========

In this chapter, we will see how topology, the study of limits and continuity,
is formalized in mathlib. This topic is rather well developed and involves
quite a few layers of mathematical structure.
The first layer is naive set theory already covered in :numref:`Chapter %s <sets_and_functions>`.
The next one is the theory of filters, which then allows us to develop
topological spaces, metric spaces and a slightly more exotic
intermediate notion called a uniform space.

This chapter will contain quite a bit more mathematical explanation
than the previous ones since filters in particular are not
systematically taught in universities, even to future mathematicians,
and are crucial in formalizations of topology in all major libraries of
formalized mathematics.

This discrepancy is easy to explain. Consider limits of a function
``f : ℝ → ℝ``. We can consider
the limit of ``f x`` when ``x`` goes to some ``x₀`` or ``±∞``, or
``x₀⁺`` or ``x₀⁻``, as well as variations where ``x`` is not allowed to be
``x₀``. We could also ask that only rational values of ``x`` are
considered, or other constraints, but let's stick to these 13 cases.
Then the behavior of ``f x`` could also be anyone of these 13
possibilities. So we get 13 × 13 = 169 definitions, including
"``f x`` tends to ``+∞`` when ``x`` tends to ``x₀`` from the right without
being equal to ``x₀``" etc. That's already a lot of definitions, and they
don't even include limits of sequences for instance.

Then come the lemmas. For instance you can compose limits. If
``f x`` tends to ``y₀`` when ``x`` tends to ``x₀`` and
``g y`` tends to ``z₀`` when ``y`` tends to ``y₀`` then
``g ∘ f x`` tends to ``z₀`` when ``x`` tends to ``x₀``.
It is important to keep track of eack kind of limit here. For instance,
if the second assumption is only a pointed limit (ie.
``g y`` tends to ``z₀`` when ``y`` tends to ``y₀`` and ``y ≠ y₀``)
then the conclusion may not hold.
So we now need 13 × 13 × 13 = 2197 lemmas.

In informal maths this is not a big issue, we can prove two or three of
those 2197 lemmas and leave the others as exercises for the reader.
This trick is not available in formalized mathematics, hence we will
need a bit more mathematics: Bourbaki's theory of filters.


.. include:: 07_Topology/01_Filters.inc
