
Mathematics in Lean
-------------------

Built using Sphinx and restructured text.

# How to build

The project requires a Lean installation to test the snippets. Install the project with
```
leanproject new mathematics_in_lean
```
and use
```
leanproject up
```
to update.

The build requires python 3 (install `python3-venv` on ubuntu).

```
make install-deps
make html
make latexpdf
```

The call to `make install-deps` is only required the first time, and only if you want to use the bundled version of Sphinx and Pygments with improved syntax highlighting for Lean.

# How to test the Lean code snippets

```
make leantest
```

# How to deploy

```
./deploy.sh leanprover-community mathematics_in_lean
```

# How to contribute

We are just getting started with this, so extensive feedback is premature. Feel free to contact any of the authors by email or though the [Lean Zulip channel](https://leanprover.zulipchat.com/).
