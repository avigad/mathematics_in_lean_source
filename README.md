
Mathematics in Lean Source
==========================

This repository is used to generate the textbook and user repository for
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/).

Our build process applies a rudimentary Python script to marked up Lean files to generate
- source files for the textbook,
- Lean exercise files, and
- Lean solution files,

and put them all in the right places.

We use [Sphinx](https://www.sphinx-doc.org/en/master/)
 and the [Read the Docs theme](https://sphinx-rtd-theme.readthedocs.io/en/stable/) to generate
 the HTML and PDF versions of the textbook.

Finally, we use another Python script to deploy the contents to the
[user repository](https://github.com/leanprover-community/mathematics_in_lean).


Setup
-----

To edit the Lean files, you need to have Lean, github, and friends installed.
See the instructions on the [Lean community web pages](https://leanprover-community.github.io/) .
In particular, don't forget to use
```
lake exe cache get
```
after fetching this repository to get the compiled version of Mathlib.

To build the textbook, you need to have
[Sphinx and ReadTheDocs](https://sphinx-rtd-tutorial.readthedocs.io/en/latest/install.html)
installed, as well as the Python `regex` package.
Ideally, `pip install sphinx sphinx-rtd-theme regex` should suffice.


Overview
--------

The Lean source files are in the `MIL` directory. There is a folder for each chapter, the
name of which begins with the letter `C` and the chapter number.
The scripts sort the chapters and ignore folders that do not begin with `C`.

Each folder should contain an `.rst` file with the same name, which has the chapter header
for Sphinx. Each folder also has a Lean source file for each section,
the name of which begins with `S` and the section number.
The scripts ignore Lean files that do not begin with `S`.
The markup that is used to generate the content is described below.

The folder `sphinx_source` contains files that are automatically added to a generated folder
called `source`, which is used by Sphinx.
It includes, in particular, a folder for any figures you want to use in the textbook.

The folder `user_repo_source` contains files that are automatically added to a generated
folder called `user_repo`, which is used to build the user repository.
It includes, in particular, the `README` file for that repository.


Build
-----

Running `scripts/mkall.py` does the following:
- It initializes and creates a `source` directory, for use by Sphinx.
- It initializes and creates a `user_repo` directory with files that will be
  deployed to the user repository.
- It updates the file `MIL.lean` to match the contents of the `MIL` folder.

With the `source` directory in place, you can use `make html` and `make latexpdf` to
call Sphinx to build the HTML and PDF versions of the book, respectively.
Sphinx puts these in a generated `build` directory.

Running `scripts/deploy.sh leanprover-community mathematics_in_lean` calls all three of the
previous scripts, copies the HTML and PDF versions of the book to `user_repo`,
and deploys the user repository to the github repository `leanprover-community/mathematics_in_lean`.
You can deploy to another destination for testing.

Running `scripts/clean.py` deletes the `source`, `user_repo`, and `build` directories.


Markup
------

The Lean files in the `MIL` folder generate three types of files:
- Source files for the Sphinx textbook.
- Files with examples (and exercises) for the user repository.
- Files with solutions for the user repository.
A line of text from the Lean file may go to any combination of these destinations simultaneously,
or nowhere at all, as determined by simple markup directives in the file.

When `scripts/mkall.py` starts processing a file,
it sends output to both the associated examples file and the associated solutions file by default.
This makes sense, for example, for the import lines.

The following markup specifies material for the textbook:
```
/- TEXT:
Stuff for the textbook goes here.
TEXT. -/
```
The lines between the comments are sent only to the associated Sphinx source file.

After the line `TEXT. -/`, by default, lines of text are only to the
examples file.
You can replace the last line with `EXAMPLES: -/`, which has the same effect,
`SOLUTIONS: -/` to send the lines to the solutions file,
`BOTH: -/` to send the lines to the both files,
or `OMIT: -/` to send the lines to neither.

You can subsequently modify the behavior with the additional comment lines
`-- EXAMPLES:`, `-- SOLUTIONS:`, `-- BOTH:`, and `-- OMIT:`.
The behavior stays in effect until another directive changes it.

While the script is processing lines of Lean code, you can specify that a sequence of lines
should be added to the textbook as a block quote by enclosing it as follows:
```
-- QUOTE:
example : 1 + 1 = 2 := by rfl
-- QUOTE.
```
Note the use of the period to mark the end of the quote.

In such a quote block, any lines that are designated to go only to the solutions file are not
included in the quote. Thus you can only quote lines that are sent to the examples file,
sent to both the examples and solutions files, or omitted from both.
The behavior of the `QUOTE` directives is otherwise independent of the behavior of the
`EXAMPLES`, `SOLUTIONS`, `BOTH`, and `OMIT` directives.
For example, you can switch output from the examples file to both the examples and solutions
file in the middle of a quote.
It doesn't make a difference whether one of the latter directives occurs just before or
just after a `QUOTE` directive.

You can also use `/- EXAMPLES:`, `/- SOLUTIONS:`, `/- BOTH:`, and `/- OMIT:` to put text
in a block comment that is sent to one of the files accordingly.
This provides a handy way to specify a `sorry` in an examples file
that is replaced by a solution in the solution file.
Here's an example of how these are used:
```
/- TEXT:
Here is an example of the way that ``rintro`` is used:
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩
-- QUOTE.

/- TEXT:
As an exercise, try proving the other inclusion:
BOTH: -/
-- QUOTE:
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  . use xs; right; exact xu
-- QUOTE.

```
The second text block represents a common idiom for presenting exercises:
after the textbook prose, a `theorem` or `example` line is sent to both the examples
and the solutions file.
The examples file contains only a `sorry`, whereas the solutions file contains the full solution.
The solution is checked by Lean in the source file, but it is not included in the quote.

Note also the useful convention that if a blank line is needed in the examples or
solutions file, it is specified *after* the relevant segment, so that the next
time output is enabled no blank line is needed.
So, in the example above, there is no blank line before or after `-- QUOTE:`
because we assume that prior input has already inserted a blank line,
but there is a blank line after `--QUOTE.`

It is common to use sections to declare and scope variables in the examples and solutions
files, but to omit the section commands from quote.
Thus an example above could have begun as follows:
```
/- TEXT:
Here is an example of the way that ``rintro`` is used:
BOTH: -/
section
variable (s t u : Set α)

-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩
-- QUOTE.

```
Just make sure that the matching `end` and a blank line after are sent to both outputs.

The weird pair of characters `αα` in a Lean input file is simply deleted from any
output produced by the script.
This is a little hack that allows you to produce the same identifier in the examples
and solutions files. For example, the exercise above could have been written
as follows:
```
/- TEXT:
As an exercise, try proving the other inclusion:
EXAMPLES: -/
-- QUOTE:
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry

-- QUOTE.
-- SOLUTIONS:
theorem fooαα : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  . use xs; right; exact xu

```
The theorem is named `foo` in both the examples and the solutions.

Finally, there is a mechanism that allows you to quote any part of the file
in the textbook, before or after it appears in the Lean source file.
This can be used, for example, to present a long proof, and then refer back to parts of it.
Encode the lines you are interested in quoting with a pair of tags:
```
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
-- TAG: my_tag
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  . use xs; right; exact xu
-- TAG: end
```
The first tag can have any label you want in place of `my_tag`, whereas the second should
be exactly as shown. Adding the line
```
-- LITERALINCLUDE: my_tag
```
in the middle of a text block anywhere in the file will insert the tagged text as a
block quote in the textbook,
using a Sphinx directive that is designed for exactly that purpose.


Processing one section
----------------------

Instead of building everything, you can test build a single section with `scripts/mksection.py`.
For example,
```
  scripts/mksection.py C03_Logic S02_The_Existential_Quantifier
```
creates the examples file, the solutions file, and the Sphinx restructured text file
for the section indicated.


How to contribute
-----------------

The textbook is still a work in progress, but feedback and corrections are welcome.
You can open a pull request,
find us on the [Lean Zulip channel](https://leanprover.zulipchat.com/),
or contact us by email.
