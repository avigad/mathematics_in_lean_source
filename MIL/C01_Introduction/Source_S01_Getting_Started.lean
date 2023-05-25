/- TEXT:
Getting Started
---------------

The goal of this book is to teach you to formalize mathematics using the
Lean 4 interactive proof assistant.
It assumes that you know some mathematics, but it does not require much.
Although we will cover examples ranging from number theory
to measure theory and analysis,
we will focus on elementary aspects of those fields,
in the hopes that if they are not familiar to you,
you can pick them up as you go.
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

#. Install Lean 4 and VS Code following
   these `instructions <https://github.com/leanprover/lean4/blob/master/doc/quickstart.md>_`.

#. In a terminal, navigate to the folder where you want to put a copy of the
   repository, and type ``git clone git@github.com:leanprover-community/mathematics_in_lean.git``
   to fetch it from github.

#. Navigate to ``mathematics_in_lean``, and execute ``lake exe cache get`` to fetch a compiled
   version of the library, ``mathlib``.

#. Type ``code .`` to open the folder in ``VS Code``. Alternatively, you can run ``VS Code`` and
   choose ``Open Folder`` from the ``File`` menu. Be sure to open the folder ``mathematics_in_lean``,
   not any other folder.

Opening any Lean file will simultaneously open this
book in a VS Code window. You can update to a newer version by tying
``git pull`` followed by ``lake exe cache get`` inside
the ``mathematics_in_lean`` folder.

Alternatively, you can run Lean and VS Code in the cloud,
using `Gitpod <https://gitpod.io/>`_.
You can find instructions as to how to do that on the Mathematics in Lean
`project page <https://github.com/leanprover-community/mathematics_in_lean>`_
on Github.

Each section in this book has an associated Lean file with examples
and exercises. You can find them in the folder `src`,
organized by chapter. We recommend making a copy of that folder
so that you can experiment with the files as you go,
while leaving the originals intact.
The text will often include examples, like this one:
TEXT. -/
-- QUOTE:
#eval "Hello, World!"

-- QUOTE.
/- TEXT:
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
TEXT. -/
