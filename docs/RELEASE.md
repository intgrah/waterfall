# Release preparation

This is a private candidate, version `0.1.0-rc.1`, hosted at
[samth/Waterfall](https://github.com/samth/Waterfall). There is no release tag,
public website or registry submission. `reservoir = false` keeps indexing disabled
pending public release approval.

The package uses Lean 4.30.0, has no external library dependencies, and contains
Apache-2.0 licensing, Lake metadata, a compiled tutorial, regression tests, a
static website, and an independent consumer fixture. Library source is separated
from optional observation and replay. Research corpora and lemma-discovery
experiments are excluded.

The [adversarial review](reviews/2026-09-11/README.md) identified three existing
defects. Repair cancelled-worker heartbeat accounting and the committed sibling
scan before public release; resolve or explicitly document the progress-check
restriction on extensions. Keep their behavioral changes separate from the
validated readability refactor.

Before publication, after maintainer approval:

1. Approve public visibility for the existing repository and add the chosen Git
   installation coordinate to the examples and package metadata. Do not guess
   a registry scope.
2. Change the version to the approved release and enable Reservoir indexing.
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
