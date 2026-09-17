# Contributing

The package contains the proof engine, configured tactics, search policies,
tests, tutorial, and website sources. Inference operations should remain
general: corpus-specific theorem names and special cases belong in experiments,
not in the package.

Run the package checks after source changes:

```sh
lake build
lake test
```

Changes to the public interface should also be checked against the independent
`consumer/` package. Website text and examples live in `site/*.md`; generated
HTML is not committed. The documentation project validates the site and its
Lean examples:

```sh
lake -d docbuild test
lake -d docbuild exe site check-docs
```

Keep proof operations separate from scheduling policy, observation middleware,
and tactic syntax. Search transitions must preserve compatible Lean checkpoints,
pending sibling obligations, and effort accounting. New semantic behavior needs
focused regression tests as well as the full package checks above.
