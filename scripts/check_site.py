#!/usr/bin/env python3
"""Build the website and check local links and HTML fragment targets."""
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit

from build_site import OUT, build


class Page(HTMLParser):
    def __init__(self, path):
        super().__init__()
        self.links = []
        self.ids = set()
        self.feed(path.read_text())

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            assert attrs["id"] not in self.ids, f"Duplicate anchor: {attrs['id']}"
            self.ids.add(attrs["id"])
        for key in ["href", "src"]:
            if key in attrs:
                self.links.append(attrs[key])


def check():
    build()
    count = 0
    for source in OUT.glob("*.html"):
        for link in Page(source).links:
            parts = urlsplit(link)
            if parts.scheme or parts.netloc:
                continue
            target = source.parent / unquote(parts.path) if parts.path else source
            if target.is_dir():
                target = target / "index.html"
            assert target.exists(), f"Broken link: {source.name} -> {link}"
            if parts.fragment and target.suffix == ".html":
                assert unquote(parts.fragment) in Page(target).ids, \
                    f"Broken anchor: {source.name} -> {link}"
            count += 1
    print(f"Website build and {count} local links/anchors pass.")


if __name__ == "__main__":
    check()
