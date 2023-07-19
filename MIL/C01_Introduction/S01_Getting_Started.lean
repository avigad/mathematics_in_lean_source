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
We also don't presuppose any background with formal methods.
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
We also strongly recommend joining the
`Lean Zulip online chat group <https://leanprover.zulipchat.com/>`_
if you haven't already.
You'll find a lively and welcoming community of Lean enthusiasts there,
happy to answer questions and offer moral support.

Although you can read a pdf or html version of this book online,
it designed to be read interactively,
running Lean from inside the VS Code editor.
To get started:

1. Install Lean 4 and VS Code following
   these `instructions <https://leanprover-community.github.io/get_started.html>`_.

2. Make sure you have `git <https://git-scm.com/>`_ installed.

3. Follow these `instructions <https://leanprover-community.github.io/install/project.html#working-on-an-existing-project`_
   to fetch the ``mathematics_in_lean`` repository and open it up in VS Code.

4. Each section in this book has an associated Lean file with examples and exercises.
   You can find them in the folder ``MIL``, organized by chapter.
   We strongly recommend making a copy of that folder and experimenting and doing the
   exercises in that copy.
   This leaves the originals intact, and it also makes it easier to update the repository as it changes (see below).
   You can call the copy ``my_files`` or whatever you want and use it to create
   your own Lean files as well.

At that point, you can open the textbook in a side panel in VS Code as follows:

1. Type ``ctrl-shift-P`` (``command-shift-P`` in macOS).

2. Type ``Lean 4: Open Documentation View`` in the bar that appears, and then
   press return. (You can press return to select it as soon as it is highlighted
   in the menu.)

3. In the window that opens, click on ``Open documentation of current project``.

Alternatively, you can run Lean and VS Code in the cloud,
using `Gitpod <https://gitpod.io/>`_.
You can find instructions as to how to do that on the Mathematics in Lean
`project page <https://github.com/leanprover-community/mathematics_in_lean>`_
on Github. We still recommend working in a copy of the `MIL` folder,
as described above.

This textbook and the associated repository are still a work in progress.
You can update the repository by typing ``git pull``
followed by ``lake exe cache get`` inside the ``mathematics_in_lean`` folder.
(This assumes that you have not changed the contents of the ``MIL`` folder,
which is why we suggested making a copy.)

We intend for you to work on the exercises in the ``MIL`` folder while reading the
textbook, which contains explanations, instructions, and hints.
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
You don't have to do all of them; when you feel comfortable that you have mastered
the relevant skills, feel free to move on.
You can always compare your solutions to the ones in the ``solutions``
folder associated with each section.
TEXT. -/
