#!/usr/bin/env python3
"""
Mutation test of the Lean model.

Usage: python3 scripts/mutate_model.py [--only NAME,NAME,...] [--in-place]

Copies the project into a temporary directory, with the build outputs, and for
each named mutant of a definition runs `lake build Halfagg` there. Prints the
declarations that no longer compile. A mutant that builds is a survivor: the
theorems do not depend on what it changes. The script fails if there is one,
and if a build fails without an error in a file of the project.

The copy uses `cp -c` (copy-on-write on APFS) when it can, so it needs little
disk space on macOS. Elsewhere it copies the dependencies' build outputs too.

With `--in-place` the script mutates this checkout instead of a copy. It puts
the sources back, but the build outputs are then those of the last mutant.
This is for CI, where the checkout is thrown away.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

Z_QUERY = "  if i = 0 then pure 1 else red <$> HasQuery.query (spec := RandSpec H X M) (its.take (i + 1))\n"
Z_TABLE = "    if i = 0 then pure 1 else red <$> tableRO (items.take (i + 1))\n"
Z_ANN = ("  if i = 0 then pure 1\n"
         "  else red <$> liftM ((unifSpec + AnnSpec n H X M).query (.inr (items.take (i + 1))))\n")
Z_OF = "  if i = 0 then 1 else g (t.take (i + 1))\n"


def everywhere(change):
    """The same change to the four definitions of the verifier's randomizers."""
    return [("Halfagg/Security.lean", Z_QUERY, change(Z_QUERY)),
            ("Halfagg/Security.lean", Z_TABLE, change(Z_TABLE)),
            ("Halfagg/Proofs/Annotated.lean", Z_ANN, change(Z_ANN)),
            ("Halfagg/Proofs/Annotated.lean", Z_OF, change(Z_OF))]


# (name, description, [(file, old, new)]); old must occur exactly once.
MUTANTS = [
    ("ones", "every randomizer is 1",
     everywhere(lambda s: s.replace("if i = 0 then", "if i = i then"))),
    ("prefix", "the randomizer z_i does not cover item i",
     everywhere(lambda s: s.replace("take (i + 1)", "take i"))),
    ("signed", "a win needs no unsigned message",
     [("Halfagg/Security.lean", "    its.any fun it => it.2.1 == pk && !signed it.2.2\n",
       "    its.any fun it => it.2.1 == pk\n")]),
    ("target", "a win needs no item under the target key",
     [("Halfagg/Security.lean", "    its.any fun it => it.2.1 == pk && !signed it.2.2\n",
       "    its.any fun it => !signed it.2.2\n")]),
    ("rawtail", "the raw tail of a randomizer request is always used",
     [("Halfagg/Security.lean", "  | it :: rest => if lifts C it then [] else it :: rest\n",
       "  | it :: rest => if lifts C it then it :: rest else it :: rest\n")]),
    ("lift", "VerifyAggregate does not check that the nonces and the public keys lift",
     [("Halfagg/Basic.lean", "  decide (agg.rs.length = pm.length) && its.all (lifts C) &&\n"
       "    decide (C.mulG agg.s = isum (fun i it => (zf i).val • term C challenge it) 0 its)\n",
       "  decide (agg.rs.length = pm.length) &&\n"
       "    decide (C.mulG agg.s = isum (fun i it => (zf i).val • term C challenge it) 0 its)\n")]),
    ("count", "randomizer requests are not counted",
     [("Halfagg/Security.lean", "  | .rand _ _ => true\n", "  | .rand _ _ => false\n")]),
    ("signcount", "signing requests are not counted",
     [("Halfagg/Security.lean", "  | .sign m => p m\n", "  | .sign _ => false\n")]),
    ("red", "every reduction of a hash output counts as nearly uniform",
     [("Halfagg/Security.lean", "  ∀ c : ZMod n, Pr{let h ← $ᵗ H}[red h = c] ≤ μ\n",
       "  ∀ c : ZMod n, Pr{let h ← $ᵗ H}[red h = c] ≤ μ + 1\n")]),
    ("zero", "every 256-bit hash output reduces to the scalar 0",
     [("Halfagg/Hash256.lean", "def redMod (n N : ℕ) : Fin N → ZMod n := fun h => (h.val : ZMod n)\n",
       "def redMod (n N : ℕ) : Fin N → ZMod n := fun _ => 0\n")]),
    ("verifies", "the verification game of the knowledge theorem accepts every aggregate",
     [("Halfagg/SecurityKnowledge.lean",
       "def aggVerifies (its : List (Item X M)) (s : ZMod n) (zs : List (ZMod n)) : Bool :=\n"
       "  verifyWith C challenge (fun i => zs.getD i 0) ⟨its.map (·.1), s⟩ (its.map (·.2))\n",
       "def aggVerifies (its : List (Item X M)) (s : ZMod n) (zs : List (ZMod n)) : Bool :=\n"
       "  verifyWith C challenge (fun i => zs.getD i 0) ⟨its.map (·.1), s⟩ (its.map (·.2)) || true\n")]),
    ("romhash", "the game with a challenge oracle verifies with the challenges 0",
     [("Halfagg/SecurityROM.lean",
       "(aggExperiment C (hOf g) red (erase C (F.at g)))).run' ∅\n",
       "(aggExperiment C (hOf fun _ => 0) red (erase C (F.at g)))).run' ∅\n")]),
    ("chalcount", "challenge-hash queries are not counted",
     [("Halfagg/SecurityROM.lean", "  | .inl _ => true\n", "  | .inl _ => false\n")]),
    ("explains", "every forger counts as explaining its nonces",
     [("Halfagg/SecurityTight.lean", "      | .inl key, next => key.2.1 ∈ seen ∧ ∀ e, next e seen\n",
       "      | .inl _, next => ∀ e, next e seen\n")]),
    ("bind", "the binding adversary wins with the same list twice",
     [("Halfagg/SecurityBinding.lean",
       "  decide (pm ≠ pm') && verifyWith C challenge (fun i => zs.getD i 0) agg pm &&\n",
       "  verifyWith C challenge (fun i => zs.getD i 0) agg pm &&\n")]),
    ("range", "VerifyAggregate on bytes accepts an s that is not below n",
     [("Halfagg/Vectors.lean",
       "    decide (s < n) &&\n    verifyAggregate secp256k1F challenge randomizerF",
       "    decide (s < 2 ^ 256) &&\n    verifyAggregate secp256k1F challenge randomizerF"),
      ("Halfagg/Vectors.lean", "    decide (s < n) &&\n    verifyAggregateFast ⟨",
       "    decide (s < 2 ^ 256) &&\n    verifyAggregateFast ⟨"),
      ("Halfagg/Encoding.lean", "      decide (s < n) then\n", "      decide (s < 2 ^ 256) then\n")]),
    ("input", "the randomizer hash does not cover the messages",
     [("Halfagg/Vectors.lean", "(its.flatMap fun it => it.1 ++ it.2.1 ++ it.2.2)) :\n",
       "(its.flatMap fun it => it.1 ++ it.2.1)) :\n"),
      ("Halfagg/Encoding.lean", "  its.flatMap fun it => it.1 ++ it.2.1 ++ it.2.2\n",
       "  its.flatMap fun it => it.1 ++ it.2.1\n")]),
]

DECL = re.compile(r"^(?:noncomputable |private |protected )*(?:def|theorem|lemma|abbrev|instance)\s+(\S+)")


def copy_project(dst):
    """The project with its build outputs, copy-on-write if the file system can."""
    for flags in (["-c", "-R"], ["-R"]):
        if subprocess.run(["cp", *flags, str(ROOT) + "/.", str(dst)],
                          capture_output=True).returncode == 0:
            return
        shutil.rmtree(dst, ignore_errors=True)
        dst.mkdir()
    sys.exit("could not copy the project")


def failures(tree, out):
    """The declarations around the errors of a build log, in the log's order.
    Lake does not build what depends on a module that failed, so these are the
    declarations nearest to the mutated definition."""
    found = []
    for m in re.finditer(r"^error: (Halfagg/\S+\.lean):(\d+):\d+: ", out, re.M):
        path, line = m.group(1), int(m.group(2))
        lines = (tree / path).read_text().split("\n")
        where = f"{path}:{line}"
        at = min(line, len(lines)) - 1
        # Lean reports some errors at the docstring of the declaration.
        up = not lines[at].startswith("/--")
        for i in (range(at, -1, -1) if up else range(at, len(lines))):
            d = DECL.match(lines[i])
            if d:
                where = f"{d.group(1)} ({path})"
                break
        if where not in found:
            found.append(where)
    return found


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", help="comma-separated mutant names")
    ap.add_argument("--in-place", action="store_true",
                    help="mutate this checkout instead of a copy")
    args = ap.parse_args()
    wanted = set(args.only.split(",")) if args.only else None
    if args.in_place:
        sys.exit(run(ROOT, wanted))
    with tempfile.TemporaryDirectory() as tmp:
        tree = Path(tmp) / "project"
        tree.mkdir()
        copy_project(tree)
        sys.exit(run(tree, wanted))


def run(tree, wanted):
    """Build every wanted mutant in `tree`. Returns 1 if one of them builds."""
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ["PATH"])
    build = ["lake", "build", "Halfagg"]
    if subprocess.run(build, cwd=tree, env=env, capture_output=True).returncode != 0:
        sys.exit("the unmutated project does not build")
    survivors = []
    unknown = []
    for name, description, edits in MUTANTS:
        if wanted is not None and name not in wanted:
            continue
        saved = {}
        try:
            for path, old, new in edits:
                src = (tree / path).read_text()
                saved.setdefault(path, src)
                if src.count(old) != 1:
                    sys.exit(f"{name}: expected one occurrence in {path}, found {src.count(old)}")
                (tree / path).write_text(src.replace(old, new))
            r = subprocess.run(build, cwd=tree, env=env, capture_output=True, text=True)
        finally:
            for path, src in saved.items():
                (tree / path).write_text(src)
        if r.returncode == 0:
            print(f"{name}: {description}\n    builds", flush=True)
            survivors.append(name)
        else:
            where = failures(tree, r.stdout + r.stderr)
            if not where:
                unknown.append(name)
            print(f"{name}: {description}\n    fails in {', '.join(where) or 'an unknown place'}",
                  flush=True)
    print(f"survivors: {', '.join(survivors) or 'none'}")
    if unknown:
        print(f"no error in a project file: {', '.join(unknown)}")
    return 1 if survivors or unknown else 0


if __name__ == "__main__":
    main()
