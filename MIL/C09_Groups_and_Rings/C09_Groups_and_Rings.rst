.. _groups_and_ring:

Groups and Rings
================

We saw in :numref:`proving_identities_in_algebraic_structures` how to reason about
operations in groups and rings. Later, in :numref:`section_algebraic_structures`, we saw how
to define abstract algebraic structures, such as group structures, as well as concrete instances
such as the ring structure on the Gaussian integers. :numref:`Chapter %s <hierarchies>` explained how
hierarchies of abstract structures are handled in Mathlib.

In this chapter we work with groups and rings in more detail. We won't be able to
cover every aspect of the treatment of these topics in Mathlib, especially since Mathlib is constantly growing.
But we will provide entry points to the library and show how the essential concepts are used.
There is some overlap with the discussion of
:numref:`Chapter %s <hierarchies>`, but here we will focus on how to use Mathlib instead of the design
decisions behind the way the topics are treated.
So making sense of some of the examples may require reviewing the background from
:numref:`Chapter %s <hierarchies>`.
