#!/usr/bin/env python3
"""Check documentation links and compile the literal README/website examples."""
from pathlib import Path
import re
import subprocess
import tempfile

from build_site import MARKDOWN, PAGES, ROOT, SITE
from check_site import check as check_site


def check_link(source, target):
    if not target or target.startswith(("#", "https://", "http://", "mailto:")):
        return
    path = source.parent / target.split("#", 1)[0]
    assert path.exists(), f"Broken link: {source.relative_to(ROOT)} -> {target}"


check_site()
for path in [ROOT / "README.md", *(ROOT / "docs").glob("*.md"), SITE / "README.md"]:
    for target in re.findall(r"\]\(([^)]+)\)", path.read_text()):
        check_link(path, target)

sources = [ROOT / "README.md", *(SITE / f"{name}.md" for name in PAGES)]
blocks = [(path, token.content) for path in sources
          for token in MARKDOWN.parse(path.read_text())
          if token.type == "fence" and token.info.strip() == "lean"]
complete = [(path, block) for path, block in blocks if block.startswith("import ")]
assert complete, "Documentation has no complete Lean examples"
examples = list(complete)
traversal = next(block for path, block in complete if path == SITE / "index.md")
for path, block in blocks:
    if block.startswith("import "):
        continue
    if block.startswith("waterfall "):
        # The options examples are invocations on the main traversal theorem.
        prefix = traversal[:traversal.rindex("  waterfall")]
        examples.append((path, prefix + "\n".join("  " + line for line in block.splitlines()) + "\n"))
    else:
        # Short theorem excerpts must agree with a checked complete example.
        assert any(block.strip() in full for _, full in complete), \
            f"Excerpt differs from the complete examples in {path}:\n{block}"

with tempfile.TemporaryDirectory(prefix="waterfall-docs-") as directory:
    for i, (source, block) in enumerate(examples):
        path = Path(directory) / f"Example{i}.lean"
        path.write_text(block)
        print(f"Checking example {i + 1} from {source.relative_to(ROOT)}", flush=True)
        subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, check=True)
print(f"Documentation links and {len(examples)} README/website examples pass.")
