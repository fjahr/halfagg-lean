#!/usr/bin/env python3
"""Generate Halfagg/Summary.lean from the axioms Lean reports for the results.

Usage: python3 scripts/gen_summary.py > Halfagg/Summary.lean  (after `lake build`)

Run it when a result is added or a definition behind a result changes. The
generated file then fails the build if the axioms of a result, the axioms of
the project, the list of definitions behind the results or the reading list of
a main result change.
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

SECTIONS = [
    ("Correctness, for every choice of the hash functions",
     ["Halfagg.verifyAggregate_aggregate", "Halfagg.verifyAggregate_incAggregate",
      "Halfagg.verifyAggregate_single", "Halfagg.incAggregate_append",
      "Halfagg.aggregate_append", "Halfagg.aggregate_accepts_invalid",
      "Halfagg.verifyMulti_eq"]),
    ("The order of secp256k1 and of its generator, checked by the kernel",
     ["Halfagg.OrderG.n_smul_G", "Halfagg.secp256k1F", "Halfagg.secp256k1_primeOrder",
      "Halfagg.secp256k1_verifyMulti_eq"]),
    ("Forgeries against weakened verifiers",
     ["Halfagg.forgeOnes_verifies", "Halfagg.forgeLate_verifies", "Halfagg.rogue_neg",
      "Halfagg.card_rogue"]),
    ("Test vectors (compiled evaluation)",
     ["Halfagg.Vectors.aggregate_vectors", "Halfagg.Vectors.incAggregate_vectors",
      "Halfagg.Vectors.verifyAggregate_vectors"]),
    ("Byte encodings",
     ["Halfagg.Vectors.randomizerInput_injective", "Halfagg.Vectors.randomizerF_input_injective",
      "Halfagg.Vectors.verifyAggregateBytes_eq", "Halfagg.Vectors.decodeVerify_randomizer",
      "Halfagg.Vectors.decodeVerify_pm_injective",
      "Halfagg.Vectors.verifyAggregateBytes_incAggregateBytes",
      "Halfagg.Vectors.verifyAggregateBytes_aggregateBytes",
      "Halfagg.Vectors.incAggregateBytes_isSome", "Halfagg.Vectors.aggregateBytes_isSome",
      "Halfagg.Vectors.verifyAggregateBytes_unique"]),
    ("Security for 32-byte nonces, public keys and messages",
     ["Halfagg.Security.secp256k1X", "Halfagg.Security.length_sha256",
      "Halfagg.Security.randomizerX_eq_red256", "Halfagg.Security.randHash256_input_injective",
      "Halfagg.Security.bytes_halfagg_unforgeable", "Halfagg.Security.bytes_halfagg_knowledge",
      "Halfagg.Security.bytes_halfagg_dlog_tight", "Halfagg.Security.bytes_halfagg_binding",
      "Halfagg.Security.bytes_halfagg_dlog_tight_256",
      "Halfagg.Security.bytes_halfagg_binding_256",
      "Halfagg.verifyWith_map", "Halfagg.Security.verifyAggregateBytes_eq_X",
      "Halfagg.Security.decodeX_bytes", "Halfagg.Security.bytes_game_verifier"]),
    ("The game with the forgery as bytes",
     ["Halfagg.Security.aggExperimentB_eq", "Halfagg.Security.aggAdvantageB_eq",
      "Halfagg.Security.parseOut_serOut", "Halfagg.Security.toStruct_serB",
      "Halfagg.Security.bytesGame_halfagg_unforgeable",
      "Halfagg.Security.bytesGame_serB_unforgeable", "Halfagg.Security.bytesGame_winnable"]),
    ("Unforgeability",
     ["Halfagg.Security.halfagg_unforgeable", "Halfagg.Security.redMod_bound",
      "Halfagg.Security.secp256k1_redBound", "Halfagg.Security.reduction_sign_queries",
      "Halfagg.Security.aggWins_lifts", "Halfagg.Security.game_verifier",
      "Halfagg.Security.secp256k1_halfagg_unforgeable"]),
    ("Knowledge of the individual signatures",
     ["Halfagg.Security.halfagg_knowledge", "Halfagg.Security.extractor_sign_queries",
      "Halfagg.Security.secp256k1_halfagg_knowledge"]),
    ("The loss is tight",
     ["Halfagg.Security.grinder_advantage", "Halfagg.Security.grinder_sandwich",
      "Halfagg.Security.grinder_reduction_no_sign"]),
    ("The games can be won",
     ["Halfagg.Security.bettor_advantage_pos", "Halfagg.Security.bettor_queries",
      "Halfagg.Security.bettor_bound", "Halfagg.Security.bettor_verify_pos",
      "Halfagg.Security.bettorRom_advantage_pos", "Halfagg.Security.bettorRom_explains",
      "Halfagg.Security.bettorRom_bound", "Halfagg.Security.bettorRomH_advantage_pos",
      "Halfagg.Security.bettorRomH_explains", "Halfagg.Security.bettorRomH_bound"]),
    ("The challenge hash as a random oracle",
     ["Halfagg.Security.halfagg_unforgeable_rom", "Halfagg.Security.halfagg_dlog",
      "Halfagg.Security.reductionROM_bound", "Halfagg.LoggedRun.rom_eq_table",
      "Halfagg.Security.secp256k1_halfagg_dlog"]),
    ("A reduction to discrete log without forking",
     ["Halfagg.Security.halfagg_key_or_signature", "Halfagg.Security.halfagg_dlog_tight",
      "Halfagg.Security.secp256k1_halfagg_dlog_tight"]),
    ("Binding",
     ["Halfagg.Security.halfagg_binding", "Halfagg.Security.secp256k1_halfagg_binding"]),
    ("The challenge hash as BIP 340 computes it: hash outputs reduced modulo n",
     ["Halfagg.Security.repMod_bound", "Halfagg.Security.secp256k1_repBound",
      "Halfagg.Security.halfagg_hashed_le", "Halfagg.Security.halfagg_unforgeable_rom_hashed",
      "Halfagg.Security.halfagg_dlog_hashed", "Halfagg.Security.halfagg_dlog_tight_hashed",
      "Halfagg.Security.secp256k1_halfagg_dlog_256",
      "Halfagg.Security.secp256k1_halfagg_dlog_tight_256",
      "Halfagg.Security.halfagg_binding_hashed_le", "Halfagg.Security.halfagg_binding_hashed",
      "Halfagg.Security.secp256k1_halfagg_binding_256"]),
]

# The main results: one theorem for every property, in its general form. The
# other results are forms of these for other models of the hash functions, for
# secp256k1 and for bytes, and facts that support them. REVIEW.md prints the
# statements of the main results and what a reader of each has to read.
MAIN = [
    ("Correctness",
     ["Halfagg.verifyAggregate_aggregate", "Halfagg.verifyAggregate_incAggregate"]),
    ("Unforgeability", ["Halfagg.Security.halfagg_unforgeable"]),
    ("Knowledge of the individual signatures", ["Halfagg.Security.halfagg_knowledge"]),
    ("A reduction to discrete log", ["Halfagg.Security.halfagg_dlog_tight"]),
    ("Binding", ["Halfagg.Security.halfagg_binding"]),
]

HEADER = '''
/-!
# The results and their axioms

Each check below fails the build if the axioms of a result change. The
theorems must depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); a `sorry` would show up as `sorryAx`. This
includes the results about secp256k1: the order of its generator is checked by
the kernel (`Halfagg.OrderG`). Only the test vector checks use compiled
evaluation, with one `native_decide` axiom each.

Generated by `scripts/gen_summary.py`.
-/

set_option linter.style.longLine false
'''

INVENTORY = '''
/-! ## The axioms of the whole project

The checks above are about single results. This one is about every
declaration of the project: the axioms that its modules declare, and the
axioms that its declarations depend on. The only axioms of the project are
the ones of the test vector checks. -/
'''

SURFACE = '''
/-! ## The definitions behind the results

The definitions that the statements of the results above depend on, directly
or through other definitions, by module: the ones of this project, and the
ones of taproot-lean, VCVio, agm-lean and the libraries these are built on.
Proofs are not followed. `REVIEW.md` lists the same definitions. -/
'''

READING = '''
/-! ## What to read for each main result

For every main result, the definitions behind its statement: how many there
are and how many source lines they have, for this project and for every
library, and the ones of this project by module. The last check is for all
main results together. `REVIEW.md` shows these lists. -/
'''


def lean(imports, body):
    """The output of Lean on a file with the given imports and commands."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write("\n".join(imports) + "\n" + body)
        path = f.name
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ["PATH"])
    out = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True,
                         cwd=ROOT, env=env).stdout
    os.unlink(path)
    return out


SEPARATOR = "-- next command --"


def guards(imports, commands, start):
    """Guarded commands with the messages they print, each of which must begin
    with one of the strings in `start`. One run of Lean for all of them."""
    out = lean(imports, f'\n#eval IO.println "{SEPARATOR}"\n'.join(commands) + "\n")
    msgs = [m.strip() for m in out.split(SEPARATOR)]
    if len(msgs) != len(commands):
        sys.exit(f"expected {len(commands)} messages, got {len(msgs)}:\n{out}")
    for command, msg in zip(commands, msgs):
        if not msg.startswith(start):
            sys.exit(f"unexpected output of {command.split()[0]}:\n{msg}")
    return [f"\n/--\ninfo: {msg}\n-/\n#guard_msgs in\n{command}\n"
            for command, msg in zip(commands, msgs)]


def main():
    imports = [l for l in (ROOT / "Halfagg.lean").read_text().splitlines()
               if l.strip() and l.strip() != "import Halfagg.Summary"]
    names = [n for _, l in SECTIONS for n in l]
    out = lean(imports, "".join(f"#print axioms {n}\n" for n in names))
    msgs, cur = [], None
    for line in out.split("\n"):
        if line.startswith("'"):
            if cur is not None:
                msgs.append(cur)
            cur = line
        elif cur is not None and line.strip():
            cur += "\n" + line
    if cur is not None:
        msgs.append(cur)
    if len(msgs) != len(names):
        sys.exit(f"expected {len(names)} axiom reports, got {len(msgs)}:\n{out}")
    doc = "\n".join(imports) + "\n" + HEADER
    it = iter(msgs)
    for title, l in SECTIONS:
        doc += f"\n/-! ## {title} -/\n"
        for name in l:
            m = next(it)
            assert m.startswith(f"'{name}'"), (m, name)
            if "\n" in m:
                doc += f"\n/--\ninfo: {m}\n-/\n#guard_msgs in\n#print axioms {name}\n"
            else:
                doc += f"\n/-- info: {m} -/\n#guard_msgs in\n#print axioms {name}\n"
    main_names = [n for _, l in MAIN for n in l]
    if not set(main_names) <= set(names):
        sys.exit("a main result is not in SECTIONS")
    reading = MAIN + [("All main results", main_names)]
    libraries = ("AlgebraicGroupModel: ", "Cslib: ", "Halfagg: ")
    inventory, surface, *lists = guards(
        imports,
        ["#project_axioms", "#surface " + " ".join(names)]
        + ["#reading " + " ".join(l) for _, l in reading],
        ("axioms declared in the project", "AlgebraicGroupModel.") + libraries)
    doc += INVENTORY + inventory + SURFACE + surface + READING
    for (title, _), text in zip(reading, lists):
        doc += f"\n/-! ### {title} -/\n" + text
    sys.stdout.write(doc)


if __name__ == "__main__":
    main()
