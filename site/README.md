# Editing the website

The page text, code examples and tables live in Markdown:

- [index.md](index.md): main page, usage, options, results and installation.
- [examples.md](examples.md): Software Foundations examples and complete proofs.
- [footer.md](footer.md): shared footer.

Fenced `lean` blocks contain the displayed proof code. Complete examples start
with `import Waterfall`; the Lean documentation tool compiles them directly from
the Markdown. Short theorem excerpts must occur in one of those checked examples.
The standalone tactic invocations on the main page are checked against its
traversal theorem. Ordinary Markdown tables work without HTML table markup.

The few `<section>`, `<details>` and `<nav>` tags preserve anchors and collapsible
proofs. Blank lines inside these elements allow their contents to remain Markdown.
The page frame is [_template.html](_template.html); styling is in [style.css](style.css).
Generated HTML lives only in `dist/site/`, which Git ignores.

From the repository root:

```sh
lake -d docbuild build
lake -d docbuild test
lake -d docbuild exe site check
```

The generated `dist/site/index.html` can be opened in a browser. After building
Waterfall with `lake build`, the proof examples are checked with:

```sh
lake -d docbuild exe site check-docs
```

The [separate documentation package](../docbuild/README.md) uses pinned Lean
Markdown and HTML libraries. The root Waterfall package does not depend on it.
No Python installation is needed for these tools.

On pushes to `main`, GitHub Actions builds the site and publishes it to
[GitHub Pages](https://samth.github.io/Waterfall/) after the Lean checks pass.
Pull requests build and check the site without deploying it.
