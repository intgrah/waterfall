# Release preparation

The selected release is **Waterfall 0.1**, version `0.1.0` in Lake. It remains
a private candidate, hosted at
[samth/Waterfall](https://github.com/samth/Waterfall). There is no release tag,
public website or registry submission. `reservoir = false` keeps indexing disabled
pending public release approval.

The package targets Lean 4.33.1 and also tests compatibility with Lean 4.30.0.
It has no external library dependencies and contains
Apache-2.0 licensing, Lake metadata, a compiled tutorial, regression tests, a
static website, and an independent consumer fixture. Library source is separated
from optional observation and replay. Research corpora and lemma-discovery
experiments are excluded.

The three defects identified by the
[adversarial review](reviews/2026-09-11/README.md) have been corrected separately
from the readability refactor. [Fix details and regression tests](reviews/2026-09-11/FIXES.md)
cover cancellation accounting, committed sibling scanning, and extension progress.

Before publication, after maintainer approval:

1. Approve public visibility for the existing repository and add the chosen Git
   installation coordinate to the examples and package metadata. Do not guess
   a registry scope.
2. Keep the selected `0.1.0` version and enable Reservoir indexing.
3. Run the documented checks from a clean clone, including `consumer/`.
4. Create the corresponding version tag and publish it with the source.
5. Run `python3 scripts/build_site.py` and host `dist/site/`; add the resulting URL as `homepage`.
6. Verify Git-based installation, then confirm the package's Reservoir entry
   and test the registry coordinate before documenting it as available.

Lake can install a package from a local path or Git without registry membership.
Reservoir uses package metadata such as version, license and README. Its current
indexing requirements and behavior should be checked again at publication time:
[Lake distribution documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

No automatic deployment workflow or release-upload script is enabled. The
`ci.yml` workflow builds and checks source on pushes and pull requests.

[0.1 changes and validation evidence](releases/0.1/README.md) record the
Lean compatibility work, Software Foundations examples and complete checks.
