# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    =
SPHINXBUILD   = python -msphinx  # was: sphinx-build
SPHINXPROJ    = mathematics_in_lean
SOURCEDIR     = source
BUILDDIR      = build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help Makefile

# Setup from Gabriel Ebner
VENVDIR := .venv
export PATH := $(VENVDIR)/bin:$(PATH)

install-deps:
	test -f $(VENVDIR)/bin/pip || python3 -m venv $(VENVDIR)
	pip install pip install git+https://github.com/fact-project/smart_fact_crawler.git@master#egg=Pygments
	pip install 'wheel>=0.29' # needed for old ubuntu versions, https://github.com/pallets/markupsafe/issues/59
	pip install sphinx
.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
