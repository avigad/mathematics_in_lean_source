.. _logic:

Logic
=====

Propositional Logic
-------------------

Quantifiers
-----------

Classical Logic
---------------

decidability, computability

proof by cases, proof by contradiction

``open_local_classical``

Equality
--------

Describe rewrite, simp, calc

Do some calculations with integers and reals.

Do some examples of identities in groups, with inverses and conjugates, inverses unique, etc.

Do some examples of proving identities in lattices, with meets and joins.

Do some trig identities.

A nice example, illustrating the ``ring`` tactic:

.. code-block:: lean

    import algebra.group_power tactic.ring

    variables {α : Type*} [comm_ring α]

    def sos (x : α) := ∃ a b, x = a^2 + b^2

    theorem sos_mul {x y : α} (sosx : sos x) (sosy : sos y) : sos (x * y) :=
    begin
      rcases sosx with ⟨a, b, xeq⟩,
      rcases sosy with ⟨c, d, yeq⟩,
      use [(a*c - b*d), (a*d + b*c)],
      rw [xeq, yeq], ring
    end

Add exercises for all of these.

Inequalities
------------



AM-GM inequality.

Identities in lattices.

complete lattices have lubs.