# Waterfall contributor guide

This package contains the small proof engine, its public configured tactic,
search policies, and optional observation/replay. It depends only on Lean.

- Keep inference behavior general; never special-case theorem or corpus names.
- Keep policy, middleware and frontend changes separate from proof operations.
- Preserve compatible checkpoints, sibling obligations and effort accounting.
- Add focused regressions for semantic changes; run `lake build` and `lake test`.
- Compile documentation with `python3 scripts/check_docs.py` and report the
  complete import sizes with `python3 scripts/size.py`.
- Build the standalone website with `python3 scripts/build_site.py`.
- Check the independent `consumer/` package for public-interface changes.
- No `unsafe`, admitted test proofs, legacy engine, or private benchmark corpus.
- Commit completed stages. Publish, push, tag or deploy only when authorized.

The current checkout is a local release candidate; publication is pending.
