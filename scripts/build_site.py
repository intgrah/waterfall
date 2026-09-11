#!/usr/bin/env python3
"""Build a self-contained static site for local review or later static hosting."""
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'dist/site'
OUT.mkdir(parents=True, exist_ok=True)
for p in (ROOT / 'site').iterdir():
    if not p.is_file():
        continue
    if p.suffix == '.html':
        (OUT / p.name).write_text(p.read_text().replace('href="../', 'href="source/'))
    else:
        shutil.copyfile(p, OUT / p.name)
for folder in ['Docs', 'Waterfall', 'Tests', 'docs']:
    for p in (ROOT / folder).rglob('*'):
        if p.is_file():
            target = OUT / 'source' / p.relative_to(ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, target)
shutil.copyfile(ROOT / 'LICENSE', OUT / 'source/LICENSE')
print(OUT / 'index.html')
