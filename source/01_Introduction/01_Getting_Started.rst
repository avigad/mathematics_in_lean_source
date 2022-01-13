Getting Started
---------------

The goal of this book is to teach you to formalize mathematics using the
Lean 3 interactive proof assistant.
It presupposes that you know some mathematics, but not much.
Although we will cover examples ranging from number theory
to measure theory and analysis,
we will focus on elementary aspects of those fields,
in the hopes that if they are not familiar to you,
you can pick it up as you go.
We also don't presuppose any background in formalization.
Formalization can be seen as a kind of computer programming:
we will write mathematical definitions, theorems, and proofs in
a regimented language, like a programming language,
that Lean can understand.
In return, Lean provides feedback and information,
interprets expressions and guarantees that they are well-formed,
and ultimately certifies the correctness of our proofs.

You can learn more about Lean from the
`Lean project page <https://leanprover.github.io>`_
and the
`Lean community web pages <https://leanprover-community.github.io/>`_.
This tutorial is based on Lean's large and ever-growing library, *mathlib*.
We also strongly recommend taking a look at the
`Lean Zulip online chat group <https://leanprover.zulipchat.com/>`_
if you haven't already.
You'll find a lively and welcoming community of Lean enthusiasts there,
happy to answer questions and offer moral support.

Although you can read a pdf or html version of this book online,
it designed to be read interactively,
running Lean from inside the VS Code editor.
To get started:

#. Install Lean, VS Code, and mathlib following the instructions
   on the `community web site <https://leanprover-community.github.io/>`_.

#. In a terminal, type ``leanproject get mathematics_in_lean``
   to set up a working directory for this tutorial.

#. Type ``code mathematics_in_lean`` to open that directory in
   ``VS Code``.

Opening the file ``welcome.lean`` will simultaneously open this
book in a VS Code window. You can update to a newer version by tying
``git pull`` followed by ``leanproject get-mathlib-cache`` inside
the ``mathematics_in_lean`` folder.

Alternatively, you can run Lean and VS Code in the cloud,
using `Gitpod <https://gitpod.io/>`.
You can find instructions as to how to do that on the Mathematics in Lean
`project page <https://github.com/leanprover-community/mathematics_in_lean>`_
on Github.

Each section in this book has an associated Lean file with examples
and exercises. You can find them in the folder `lean_files`,
organized by chapter. We recommend making a copy of that folder
so that you can experiment with the files as you go,
while leaving the originals intact.
The text will often include examples, like this one:

.. code-block:: lean

  #eval "Hello, World!"

You should be able to find the corresponding example in the associated
Lean file.
If you click on the line, VS Code will show you Lean's feedback in
the ``Lean Goal`` window, and if you hover
your cursor over the ``#eval`` command VS Code will show you Lean's response
to this command in a pop-up window.
You are encouraged to edit the file and try examples of your own.

This book moreover provides lots of challenging exercises for you to try.
Don't rush past these!
Lean is about *doing* mathematics interactively, not just reading about it.
Working through the exercises is central to the experience.
You can always compare your solutions to the ones in the ``solutions``
folder associated with each section.
