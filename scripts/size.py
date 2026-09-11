#!/usr/bin/env python3
"""Report noncomment implementation sizes, including every transitive local helper.

Comments may be expanded for review without consuming the implementation budget.
Keep the physical count visible as well; the limit is not a formatting target.
"""
from pathlib import Path


def code_lines(source: str) -> int:
    """Count nonempty lines after removing Lean line and nested block comments.

    String contents and quoted identifiers are code, including comment-looking
    text inside them. Ordinary apostrophes are valid Lean identifier characters.
    """
    depth, quoted, escaped, count = 0, None, False, 0
    for line in source.splitlines():
        has_code, i = False, 0
        while i < len(line):
            c, pair = line[i], line[i:i + 2]
            if depth:
                if pair == "/-":
                    depth += 1
                    i += 2
                elif pair == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            elif quoted:
                has_code = True
                if escaped:
                    escaped = False
                elif c == "\\" and quoted == '"':
                    escaped = True
                elif c == quoted:
                    quoted = None
                i += 1
            elif pair == "--":
                break
            elif pair == "/-":
                depth = 1
                i += 2
            else:
                has_code |= not c.isspace()
                if c in ('"', '«'):
                    quoted = '»' if c == '«' else c
                i += 1
        count += has_code
    assert depth == 0 and quoted is None, "Unterminated comment/string/quoted identifier"
    return count


root = Path(__file__).resolve().parent.parent

def closure(start):
    pending, counted = [start], {}
    while pending:
        module = pending.pop()
        if module in counted or module == "Lean" or module.startswith("Lean."):
            continue
        path = root / (module.replace(".", "/") + ".lean")
        source = path.read_text()
        counted[module] = (code_lines(source), len(source.splitlines()))
        for line in source.splitlines():
            if line.startswith("import "):
                pending.extend(line.split("--", 1)[0].split()[1:])
    return counted

for entry in ["Waterfall.Core", "Waterfall", "Waterfall.Observe"]:
    counted = closure(entry)
    print(f"{entry}: {sum(n for n, _ in counted.values())} noncomment / "
          f"{sum(n for _, n in counted.values())} physical lines")
    for name, (n, physical) in sorted(counted.items()):
        print(f"  {name}: {n} / {physical}")
