#!/usr/bin/env python3
"""Render the editable Markdown pages into dist/site for any static web server."""
from html import escape
from pathlib import Path
from string import Template
import shutil

from markdown_it import MarkdownIt

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "site"
OUT = ROOT / "dist/site"
PAGES = {"index": "Induction proofs in Lean", "examples": "Examples"}
MARKDOWN = MarkdownIt("commonmark").enable("table")


def render(source):
    """Keep source links relative in Markdown and adapt them for the built site."""
    html = MARKDOWN.render(source)
    html = html.replace('href="../', 'href="source/')
    for name in PAGES:
        target = "./" if name == "index" else name + ".html"
        html = html.replace(f'href="{name}.md"', f'href="{target}"')
        html = html.replace(f'href="{name}.md#', f'href="{target}#')
    return html


def build():
    # Only this generated directory is replaced; source Markdown stays in site/.
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True)
    template = Template((SITE / "_template.html").read_text())
    footer = render((SITE / "footer.md").read_text())
    for name, title in PAGES.items():
        page = template.substitute(
            title=escape(title), body=render((SITE / f"{name}.md").read_text()),
            overview_current=' aria-current="page"' if name == "index" else "",
            examples_current=' aria-current="page"' if name == "examples" else "",
            footer=footer,
        )
        (OUT / f"{name}.html").write_text(page)
    # Copy only assets and legacy redirects, never old generated page files.
    for name in ["style.css", "guide.html", "reference.html"]:
        shutil.copyfile(SITE / name, OUT / name)
    for folder in ["Docs", "Waterfall", "Tests", "docs"]:
        shutil.copytree(ROOT / folder, OUT / "source" / folder,
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    shutil.copyfile(ROOT / "LICENSE", OUT / "source/LICENSE")
    return OUT


if __name__ == "__main__":
    print(build() / "index.html")
