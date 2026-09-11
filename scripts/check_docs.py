#!/usr/bin/env python3
"""Check local documentation links and compile the actual README Lean examples."""
from html.parser import HTMLParser
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def check_link(source, target):
    if not target or target.startswith(("#", "https://", "http://", "mailto:")):
        return
    path = source.parent / target.split("#", 1)[0]
    assert path.exists(), f"Broken link: {source.relative_to(ROOT)} -> {target}"


class Links(HTMLParser):
    def __init__(self, source):
        super().__init__()
        self.source = source

    def handle_starttag(self, tag, attrs):
        for key, value in attrs:
            if key in {"href", "src"}:
                check_link(self.source, value)


for path in [ROOT / "README.md", *(ROOT / "docs").glob("*.md")]:
    for target in re.findall(r"\]\(([^)]+)\)", path.read_text()):
        check_link(path, target)
for path in (ROOT / "site").glob("*.html"):
    Links(path).feed(path.read_text())

blocks = re.findall(r"```lean\n(.*?)```", (ROOT / "README.md").read_text(), re.S)
assert blocks, "README has no checked Lean examples"
with tempfile.TemporaryDirectory(prefix="waterfall-docs-") as directory:
    # Each fence is independently usable, including its own imports.
    for i, block in enumerate(blocks):
        path = Path(directory) / f"Readme{i}.lean"
        path.write_text(block)
        subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, check=True)
print(f"Documentation links and {len(blocks)} README examples pass.")
