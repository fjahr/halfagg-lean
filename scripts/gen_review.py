#!/usr/bin/env python3
"""Write the list of the definitions behind the results into REVIEW.md.

Usage: python3 scripts/gen_review.py [--check]

The list is the guarded output of `#surface` in Halfagg/Summary.lean. It goes
between two marker comments at the end of REVIEW.md. With `--check` the script
changes nothing and fails if REVIEW.md is out of date.
"""

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

BEGIN = "<!-- definitions:begin -->"
END = "<!-- definitions:end -->"

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


def render():
    modules = surface()
    known = dict(LIBRARIES)
    for module, _ in modules:
        if module.split(".")[0] not in known:
            sys.exit(f"module of an unknown library: {module}")
    own = sum(len(names) for module, names in modules if module.split(".")[0] == "Halfagg")
    other = sum(len(names) for _, names in modules) - own
    out = [BEGIN, "", "### Every definition behind the results", "",
           TEXT.format(own=own, other=other), ""]
    for title in dict.fromkeys(title for _, title in LIBRARIES):
        lines = []
        for module, names in modules:
            if known[module.split(".")[0]] == title:
                shown = ", ".join(f"`{n.removeprefix('Halfagg.')}`" for n in names)
                lines.append(f"- `{module.replace('.', '/')}.lean`: {shown}")
        if lines:
            out += [f"**{title}**", ""] + lines + [""]
    out.append(END)
    return "\n".join(out)


def main():
    review = (ROOT / "REVIEW.md").read_text()
    i, j = review.index(BEGIN), review.index(END) + len(END)
    new = review[:i] + render() + review[j:]
    if "--check" in sys.argv:
        if new != review:
            sys.exit("REVIEW.md is out of date: run scripts/gen_review.py")
    else:
        (ROOT / "REVIEW.md").write_text(new)


if __name__ == "__main__":
    main()
