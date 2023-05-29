
Mathematics in Lean 3 Source
============================

This is the source code for
[Mathematics in Lean 3](https://leanprover-community.github.io/mathematics_in_lean3/).

Our build process is rudimentary and not ready for prime time, but it is fairly
convenient to use. Most of the source is written directly in the `.lean` files
in `lean_source` using some simple markup. The Python script
`lean_source/mkall.sh` then generates the `.rst` source for the textbook and
an exercise file and a solution file for each section.

To build the textbook, you need to have
[Sphinx and ReadTheDocs installed](https://sphinx-rtd-tutorial.readthedocs.io/en/latest/install.html).
The following files are maintained by hand:
- The file `source/index.rst` should have an entry for each chapter.
- For each chapter, there should be a `.rst` file in `source`. It should include
  each of the sections.
- For each section, there should be a `.lean` file in the appropriate place
  in `lean_source`.
- Each section should have a corresponding line in `lean_source/mkall.sh`.

Is everything is set up right, the command
```
lean_source/mkall.sh
```
from the top level should build the restructured text files, the exercise files,
and the solutions. The command
```
make html
```
builds the html textbook and puts it in the `build` folder. The command
```
make latexpdf
```
builds the pdf textbook instead.

The script `deploy.sh` is used to deploy everything (the textbook and the
user's version of the example and solution files) to an arbitrary repository, set up to use the `gh-pages` branch
to display the html. Specifically, we use the following:
```
./deploy.sh leanprover-community mathematics_in_lean3
```

## How to contribute

The textbook is still a work in progress, but feedback and corrections are welcome.
You can open a pull request, find us on the [Lean Zulip channel](https://leanprover.zulipchat.com/), or contact any of us by email.
