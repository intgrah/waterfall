# Release preparation

The selected version is **waterfall 0.1**, `0.1.0` in Lake. The source is public at
[samth/waterfall](https://github.com/samth/waterfall), with documentation on
[GitHub Pages](https://samth.github.io/waterfall/). Lake can install the package
from Git using the coordinate in the [README](../README.md).
There is no version tag or Reservoir listing yet; `reservoir = false` keeps
registry indexing disabled pending the tagged release.

The package targets Lean 4.33.1 and also tests compatibility with Lean 4.30.0.
It has no external Lean library dependencies and contains Apache-2.0 licensing,
Lake metadata, a compiled tutorial, regression tests, a Markdown website, and an
independent consumer fixture. Library source is separated from optional
observation and replay. Research corpora and lemma-discovery experiments are
excluded.

The [CI workflow](../.github/workflows/ci.yml) builds and tests both Lean versions,
compiles the literal README and website examples, checks proofs with leanchecker,
and builds the independent consumer. A separate job builds and checks the static
site. After all checks pass on main, the workflow deploys the site through
GitHub Pages. Pull requests run the checks without deployment.
[Website editing instructions](../site/README.md) describe the Markdown sources.

The three defects identified by the
[adversarial review](reviews/2026-09-11/README.md) have been corrected separately
from the readability refactor. [Fix details and regression tests](reviews/2026-09-11/FIXES.md)
cover cancellation accounting, committed sibling scanning, and extension progress.

Remaining work for the tagged release:

1. Validate the selected commit from a clean clone, including Git-based installation.
2. Enable Reservoir indexing and create the `v0.1.0` version tag.
3. Confirm the package's Reservoir entry and test its registry coordinate before
   documenting registry installation as available.

Reservoir requirements should be checked when preparing that submission:
[Lake distribution documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

[0.1 changes and validation evidence](releases/0.1/README.md) record the
Lean compatibility work, Software Foundations examples and complete checks.
