#!/usr/bin/env python3
"""Write the generated parts of REVIEW.md.

Usage: python3 scripts/gen_review.py [--check]

Two parts of REVIEW.md come from Halfagg/Summary.lean, each between two marker
comments:

- the table of the main results with what a reader of each has to read, from
  the guarded outputs of `#reading`,
- the list of the definitions behind all results, from the guarded output of
  `#surface`.

With `--check` the script changes nothing and fails if REVIEW.md is out of
date.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

MAIN = ("<!-- main:begin -->", "<!-- main:end -->")
DEFINITIONS = ("<!-- definitions:begin -->", "<!-- definitions:end -->")

# The first component of a module name, and the library it belongs to.
LIBRARIES = [("Halfagg", "This project"), ("Taproot", "taproot-lean"),
             ("AlgebraicGroupModel", "agm-lean"), ("VCVio", "VCVio"), ("ToMathlib", "VCVio"),
             ("PolyFun", "PolyFun"), ("ToCslib", "PolyFun"), ("Cslib", "cslib")]

TEXT = (
    "The definitions that the statements of the results in `Halfagg/Summary.lean` depend on, "
    "directly or through other definitions: {own} of this project and {other} of the libraries it "
    "is built on. `#surface` in `Halfagg/Audit.lean` computes the list from the compiled project, "
    "`Halfagg/Summary.lean` guards it, and the build fails if it changes. Proofs are not followed, "
    "since what a proof uses does not change what a statement says. The list stops at Lean's core "
    "library and at Mathlib. Whoever agrees with these definitions knows what the results say. "
    "The ones that are not printed above have to be read in the sources, for the libraries at the "
    "commits in `lake-manifest.json`. `scripts/check.sh` fails if the list has a module under "
    "`Halfagg/Proofs/`.")

READING = re.compile(
    r"/-! ### ([^\n]*) -/\n\n/--\ninfo: (.*?)\n-/\n#guard_msgs in\n#reading ([^\n]*)\n", re.S)
COUNT = re.compile(r"(\w+): (\d+) definitions, (\d+) lines")


def short(name):
    return name.removeprefix("Halfagg.")


def modules(lines):
    """Lines `module: name, name, …` as bullet points."""
    out = []
    for line in lines:
        module, names = line.split(": ", 1)
        shown = ", ".join(f"`{short(n)}`" for n in names.split(", "))
        out.append(f"- `{module.replace('.', '/')}.lean`: {shown}")
    return out


def render_main():
    summary = (ROOT / "Halfagg/Summary.lean").read_text()
    results = READING.findall(summary)
    if not results:
        sys.exit("Halfagg/Summary.lean has no guarded #reading")
    table = ["| Main result | Theorem | Definitions here | Lines | Definitions in the libraries "
             "| Lines |", "|---|---|---|---|---|---|"]
    lists = []
    for title, info, names in results:
        counts = [COUNT.fullmatch(l) for l in info.split("\n")]
        own = [m for m in counts if m and m.group(1) == "Halfagg"]
        other = [m for m in counts if m and m.group(1) != "Halfagg"]
        if len(own) != 1:
            sys.exit(f"unexpected #reading output for {title}")
        theorems = ", ".join(f"`{n.split('.')[-1]}`" for n in names.split())
        if title == "All main results":
            title, theorems = "All of them", ""
        else:
            lists += [f"**{title}**", ""]
            lists += modules(l for l, m in zip(info.split("\n"), counts) if not m) + [""]
        table.append(f"| {title} | {theorems} | {own[0].group(2)} | {own[0].group(3)} "
                     f"| {sum(int(m.group(2)) for m in other)} "
                     f"| {sum(int(m.group(3)) for m in other)} |")
    return "\n".join([MAIN[0], ""] + table + ["", "The definitions of this project behind each "
                     "main result, by file:", ""] + lists + [MAIN[1]])


def surface():
    """The guarded output of `#surface`: (module, names) pairs."""
    summary = (ROOT / "Halfagg/Summary.lean").read_text()
    end = summary.find("\n-/\n#guard_msgs in\n#surface ")
    start = summary.rfind("/--\ninfo: ", 0, end)
    if end < 0 or start < 0:
        sys.exit("Halfagg/Summary.lean has no guarded #surface")
    out = []
    for line in summary[start + len("/--\ninfo: "):end].split("\n"):
        module, names = line.split(": ", 1)
        out.append((module, names.split(", ")))
    return out


def render_definitions():
    mods = surface()
    known = dict(LIBRARIES)
    for module, _ in mods:
        if module.split(".")[0] not in known:
            sys.exit(f"module of an unknown library: {module}")
    own = sum(len(names) for module, names in mods if module.split(".")[0] == "Halfagg")
    other = sum(len(names) for _, names in mods) - own
    out = [DEFINITIONS[0], "", "## Every definition behind the results", "",
           TEXT.format(own=own, other=other), ""]
    for title in dict.fromkeys(title for _, title in LIBRARIES):
        lines = []
        for module, names in mods:
            if known[module.split(".")[0]] == title:
                shown = ", ".join(f"`{short(n)}`" for n in names)
                lines.append(f"- `{module.replace('.', '/')}.lean`: {shown}")
        if lines:
            out += [f"**{title}**", ""] + lines + [""]
    out.append(DEFINITIONS[1])
    return "\n".join(out)


def main():
    review = (ROOT / "REVIEW.md").read_text()
    new = review
    for (begin, end), text in ((MAIN, render_main()), (DEFINITIONS, render_definitions())):
        i, j = new.index(begin), new.index(end) + len(end)
        new = new[:i] + text + new[j:]
    if "--check" in sys.argv:
        if new != review:
            sys.exit("REVIEW.md is out of date: run scripts/gen_review.py")
    else:
        (ROOT / "REVIEW.md").write_text(new)


if __name__ == "__main__":
    main()
