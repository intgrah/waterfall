# Waterfall contributor guide

This package contains the small proof engine, its public configured tactic,
search policies, and optional observation/replay. It depends only on Lean.

- Keep inference behavior general; never special-case theorem or corpus names.
- Keep policy, middleware and frontend changes separate from proof operations.
- Preserve compatible checkpoints, sibling obligations and effort accounting.
- Add focused regressions for semantic changes; run `lake build` and `lake test`.
- Compile documentation with `python3 scripts/check_docs.py` and report the
  complete import sizes with `python3 scripts/size.py`.
- Website text and examples live in `site/*.md`; do not edit generated HTML.
  Install `site/requirements.txt` before running the Python documentation checks.
  Build the website with `python3 scripts/build_site.py`; `scripts/check_site.py`
  also checks its links. See `site/README.md` for the editing workflow.
- Check the independent `consumer/` package for public-interface changes.
- No `unsafe`, admitted test proofs, legacy engine, or private benchmark corpus.
- Commit completed stages. Publish, push, tag or deploy only when authorized.

The repository is public at samth/Waterfall. GitHub Actions deploys the Markdown
website to https://samth.github.io/Waterfall/ after checks on main pass.
Version tags and Reservoir registration remain pending.
