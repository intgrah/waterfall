# Editing the website

The page text, code examples and tables live in Markdown:

- [index.md](index.md): main page, usage, options, results and installation.
- [examples.md](examples.md): Software Foundations examples and complete proofs.
- [footer.md](footer.md): shared footer.

Fenced `lean` blocks contain the displayed proof code. Complete examples start
with `import Waterfall`; `scripts/check_docs.py` compiles them directly from the
Markdown. Short theorem excerpts must occur in one of those checked examples.
The standalone tactic invocations on the main page are checked against its
traversal theorem. Ordinary Markdown tables work without any HTML table markup.

The few `<section>`, `<details>` and `<nav>` tags preserve anchors and collapsible
proofs. Blank lines inside these elements allow their contents to remain Markdown.
The page frame is [_template.html](_template.html); styling is in [style.css](style.css).
Generated HTML lives only in `dist/site/`, which Git ignores.

From the repository root:

```sh
python3 -m venv /tmp/waterfall-site-venv
. /tmp/waterfall-site-venv/bin/activate
python3 -m pip install -r site/requirements.txt
python3 scripts/check_site.py
python3 -m http.server 8000 --directory dist/site
```

The local preview is at <http://localhost:8000/>. With the Lean package built,
`python3 scripts/check_docs.py` also checks the proof examples.

On pushes to `main`, GitHub Actions builds the site and publishes it to
[GitHub Pages](https://samth.github.io/Waterfall/) after the Lean checks pass.
Pull requests build and check the site without deploying it.
