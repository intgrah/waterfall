# Documentation tooling

This is an independent Lake project. It uses
[lean-markdown](https://github.com/paulbutcher/lean-markdown), pinned by Git commit,
at release v0.3.0, with its dependencies locked in `lake-manifest.json`. This
release targets stable Lean; later library releases require a Lean release
candidate. The tactic package has no Markdown, HTML or documentation-tool
dependency. All three projects pin Lean 4.33.1.

From the repository root:

```sh
lake -d docbuild build
lake -d docbuild test
lake -d docbuild exe site build
lake -d docbuild exe site check
lake -d docbuild exe site check-docs
```

`build` renders the Markdown sources and copies downloadable source artifacts.
`check` also checks generated links, HTML anchors and duplicate IDs.
`check-docs` adds source-document link checks, excerpt consistency and compilation
of every complete README/website Lean example. It invokes the root package's
pinned Lean toolchain, clearing inherited Lake search paths; this also supports
CI checking older waterfall toolchains with the same documentation executable.

The executable finds the repository from its current directory or an optional
second argument. Generated output is restricted to `dist/site/`; temporary proof
files are removed even if a check fails.

- [Build.lean](DocSite/Build.lean): rendering, templates and output files.
- [Html.lean](DocSite/Html.lean): metadata from HTML start tags and URL decoding.
- [Check.lean](DocSite/Check.lean): links, excerpts and proof compilation.
- [Tests.lean](Tests.lean): rendering and failure-detection regressions.

Page editing instructions are in [site/README.md](../site/README.md).
