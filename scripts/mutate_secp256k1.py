#!/usr/bin/env python3
"""
Mutation test of libsecp256k1's schnorrsig_halfagg module.

Usage:
    python3 scripts/mutate_secp256k1.py path/to/secp256k1 path/to/bips/bip-0458
        [--cases N] [--seed S] [--no-exhaustive] [--only NAME,NAME,...]

Exports HEAD of the secp256k1 checkout into a temporary directory, applies
patches/secp256k1-halfagg-exhaustive-tests.patch and builds there, so the
checkout is not touched. For each one-line mutant of
src/modules/schnorrsig_halfagg/main_impl.h it rebuilds and runs three sets of
tests:

  tests       the module's unit tests, one by one,
  cases       the cases of scripts/fuzz.py through the driver built from
              scripts/fuzz_secp256k1.c, compared with BIP 458's Python reference,
  exhaustive  the exhaustive tests on the group of order 13, with the patch.

A mutant that none of them notices is a survivor.

On secp256k1 nobody can produce an input for V6: accepting an r >= p needs a
nonce point whose x-coordinate is below 2^256 - p. The test curve has a point of
order 3 with the x-coordinate 0, which r = p reduces to, and the exhaustive
tests try all values of s for that r.
"""

import argparse
import random
import subprocess
import sys
import tempfile
from pathlib import Path

import fuzz

MODULE = "src/modules/schnorrsig_halfagg/main_impl.h"
CMAKE = ["-DBUILD_SHARED_LIBS=OFF", "-DSECP256K1_EXPERIMENTAL=ON",
         "-DSECP256K1_ENABLE_MODULE_SCHNORRSIG_HALFAGG=ON", "-DSECP256K1_BUILD_BENCHMARK=OFF",
         "-DSECP256K1_BUILD_EXHAUSTIVE_TESTS=OFF", "-DSECP256K1_BUILD_CTIME_TESTS=OFF",
         "-DSECP256K1_BUILD_EXAMPLES=OFF"]

W_R = "        secp256k1_sha256_write(hash_ctx, &hash, &aggsig[i*32], 32);\n"
W_PK = "        secp256k1_sha256_write(hash_ctx, &hash, pk_ser, 32);\n"
W_M = "        secp256k1_sha256_write(hash_ctx, &hash, &all_msgs32[i*32], 32);\n"
W_NEW_R = "        secp256k1_sha256_write(hash_ctx, &hash, &new_sigs64[(i-n_before)*64], 32);\n"
W_VER_M = "        secp256k1_sha256_write(hash_ctx, &hash, &msgs32[i*32], 32);\n"
PREFIX_PK_M = "        /* write pk_i */\n" + W_PK + "        /* write m_i*/\n" + W_M
PREFIX_R_PK = "        /* write r_i */\n" + W_R + "        /* write pk_i */\n" + W_PK
NEW_M = W_M + "        /* 1.b) Copy the hash */\n"
FIN = "        secp256k1_sha256_finalize(hash_ctx, &hashcopy, hashoutput);\n"
FIN_AGG = FIN + "        /* Note: No need to check overflow, comes from hash */\n"
FIN_VER = FIN + "        secp256k1_scalar_set_b32(&zi, hashoutput, NULL);\n\n        /* Step 2"
FAIL4 = "    if (overflow) {\n        return 0;\n    }\n"
FAIL8 = "        if (overflow) {\n            return 0;\n        }\n"
OLD_S = "        secp256k1_scalar_set_b32(&s, &aggsig[n_before*32], &overflow);\n"
NEW_S = "        secp256k1_scalar_set_b32(&si, &new_sigs64[(i-n_before)*64+32], &overflow);\n"
VER_S = "    secp256k1_scalar_set_b32(&s, &aggsig[n*32], &overflow);\n"
Z0_AGG = "        if (i != 0) secp256k1_scalar_mul(&si, &si, &zi);\n"
Z0_VER = "        if (i != 0) secp256k1_ecmult(&ti, &ti, &zi, NULL);\n"
R_LIMIT = ("        if (!secp256k1_fe_set_b32_limit(&rx, &aggsig[i*32])) {\n"
           "            return 0;\n        }\n")

# An edit is (old, new, occurrence): the occurrence index, or None if old is unique.
E_Z0_AGG = (Z0_AGG, "        secp256k1_scalar_mul(&si, &si, &zi);\n", None)
E_Z0_VER = (Z0_VER, "        secp256k1_ecmult(&ti, &ti, &zi, NULL);\n", None)
E_NEW_PK_R = (W_NEW_R + W_PK, W_PK + W_NEW_R, None)
E_FIN_AGG = (FIN_AGG, FIN_AGG.replace("&hashcopy", "&hash"), None)
E_FIN_VER = (FIN_VER, FIN_VER.replace("&hashcopy", "&hash"), None)

MUTANTS = [
    ("A1", "aggregate: capacity check removed",
     [("    if ((*aggsig_len / 32) <= 0 || ((*aggsig_len / 32) - 1) < n) {", "    if (0) {", None)]),
    ("A2", "aggregate: capacity must exceed 32*(n+1)",
     [("((*aggsig_len / 32) - 1) < n)", "((*aggsig_len / 32) - 1) <= n)", None)]),
    ("A3", "inc_aggregate: prefix hash leaves out r_i", [(W_R, "", 0)]),
    ("A4", "inc_aggregate: prefix hash writes m_i before pk_i", [(PREFIX_PK_M, W_M + W_PK, None)]),
    ("A5", "inc_aggregate: s of the input aggregate ignored",
     [("    if (has_input_aggsig) {", "    if (0) {", None)]),
    ("A6", "inc_aggregate: input s >= n not rejected", [(OLD_S + FAIL8, OLD_S, None)]),
    ("A7", "aggregate: hash writes pk_i before r_i", [E_NEW_PK_R]),
    ("A8", "inc_aggregate: new signatures hash message i - n_before",
     [(NEW_M, NEW_M.replace("[i*32]", "[(i-n_before)*32]"), None)]),
    ("A9", "aggregate: running hash finalized instead of a copy", [E_FIN_AGG]),
    ("A10", "aggregate: signature s >= n not rejected", [(NEW_S + FAIL8, NEW_S, None)]),
    ("A11", "aggregate: z_0 hashed instead of 1", [E_Z0_AGG]),
    ("A12", "inc_aggregate: z = 1 for the first new signature",
     [(Z0_AGG, Z0_AGG.replace("i != 0", "i != n_before"), None)]),
    ("V1", "aggverify: length need not be a multiple of 32",
     [(" || (aggsig_len % 32) != 0) {", ") {", None)]),
    ("V2", "aggverify: longer aggregate accepted",
     [("((aggsig_len / 32)-1) != n", "((aggsig_len / 32)-1) < n", None)]),
    ("V3", "aggverify: s >= n not rejected", [(VER_S + FAIL4, VER_S, None)]),
    ("V4", "aggverify: z_0 hashed instead of 1", [E_Z0_VER]),
    ("V5", "aggverify: running hash finalized instead of a copy", [E_FIN_VER]),
    ("V6", "aggverify: r >= p reduced mod p instead of rejected",
     [(R_LIMIT, "        secp256k1_fe_set_b32_mod(&rx, &aggsig[i*32]);\n", None)]),
    ("C1", "both: z_0 hashed instead of 1", [E_Z0_AGG, E_Z0_VER]),
    ("C2", "both: hash writes pk_i before r_i",
     [(PREFIX_R_PK, "        /* write r_i */\n" + W_PK + W_R, None), E_NEW_PK_R,
      (W_R + W_PK + W_VER_M, W_PK + W_R + W_VER_M, None)]),
    ("C3", "both: running hash finalized instead of a copy", [E_FIN_AGG, E_FIN_VER]),
]


def mutate(src, edits):
    for old, new, occurrence in edits:
        count = src.count(old)
        if occurrence is None:
            if count != 1:
                sys.exit(f"expected one occurrence, found {count}:\n{old}")
            src = src.replace(old, new)
        else:
            if count <= occurrence:
                sys.exit(f"expected more than {occurrence} occurrences, found {count}:\n{old}")
            parts = src.split(old)
            src = old.join(parts[:occurrence + 1]) + new + old.join(parts[occurrence + 1:])
    return src


def run(cmd, cwd, stdin=None, timeout=900):
    try:
        r = subprocess.run(cmd, cwd=cwd, input=stdin, capture_output=True, text=True,
                           timeout=timeout)
        return r.returncode, r.stdout
    except subprocess.TimeoutExpired:
        return -1, ""


def unit_tests(tree):
    out = run(["./build/bin/tests", "--list_tests"], tree)[1].split("\n")
    start = next(i for i, l in enumerate(out) if "Module: schnorrsig_halfagg" in l)
    names = []
    for l in out[start + 1:]:
        if "]" not in l:
            break
        names.append(l.split("]")[1].strip())
    return names


def evaluate(tree, tests, driver_src, lines, expected, exhaustive):
    """(failed unit tests, cases that differ, exhaustive tests failed); None if it does not
    build."""
    if run(["cmake", "--build", "build", "-j4"], tree)[0] != 0:
        return None
    failed = [t for t in tests if run(["./build/bin/tests", f"--target={t}"], tree)[0] != 0]
    if run(["cc", "-O2", "-Iinclude", str(driver_src), "build/lib/libsecp256k1.a", "-o",
            "build/driver"], tree)[0] != 0:
        sys.exit("the driver does not compile")
    code, out = run(["./build/driver"], tree, "\n".join(lines) + "\n")
    got = out.split("\n")[:-1]
    if code != 0 or len(got) != len(lines):
        differ = len(lines)
    else:
        differ = sum(g != "SKIP" and e != g for e, g in zip(expected, got))
    ex = exhaustive and run(["./build/bin/exhaustive_tests", "1"], tree)[0] != 0
    return failed, differ, ex


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("secp256k1", help="path to a secp256k1 checkout with the halfagg module")
    ap.add_argument("bip_dir", help="path to bips/bip-0458")
    ap.add_argument("--cases", type=int, default=3000)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--no-exhaustive", action="store_true",
                    help="do not apply the patch and do not run the exhaustive tests")
    ap.add_argument("--only", help="comma-separated mutant names")
    args = ap.parse_args()

    root = Path(__file__).resolve().parent.parent
    bip_dir = Path(args.bip_dir).resolve()
    sys.path.insert(0, str(bip_dir))
    sys.path.insert(0, str(bip_dir / "secp256k1lab/src"))
    import halfagg as ref
    from secp256k1lab import bip340

    gen = fuzz.Gen(random.Random(args.seed), ref, bip340)
    makers = [gen.case_aggregate, gen.case_inc, gen.case_verify, gen.case_verify]
    cases = [makers[i % len(makers)]() for i in range(args.cases)]
    expected = [fuzz.reference(ref, c) for c in cases]
    lines = [fuzz.encode(c) for c in cases]
    driver_src = root / "scripts" / "fuzz_secp256k1.c"
    exhaustive = not args.no_exhaustive
    wanted = set(args.only.split(",")) if args.only else None

    with tempfile.TemporaryDirectory() as tmp:
        tree = Path(tmp)
        archive = subprocess.run(["git", "-C", args.secp256k1, "archive", "HEAD"],
                                 capture_output=True, check=True).stdout
        subprocess.run(["tar", "-x", "-C", tmp], input=archive, check=True)
        cmake = [c for c in CMAKE if "EXHAUSTIVE" not in c]
        if exhaustive:
            patch = (root / "patches" / "secp256k1-halfagg-exhaustive-tests.patch").read_bytes()
            subprocess.run(["patch", "-p1", "-s"], cwd=tmp, input=patch, check=True)
            cmake.append("-DSECP256K1_BUILD_EXHAUSTIVE_TESTS=ON")
        else:
            cmake.append("-DSECP256K1_BUILD_EXHAUSTIVE_TESTS=OFF")
        if run(["cmake", "-S", ".", "-B", "build"] + cmake, tree)[0] != 0:
            sys.exit("cmake failed")
        original = (tree / MODULE).read_text()
        if evaluate(tree, [], driver_src, lines, expected, False) is None:
            sys.exit("the unmutated module does not build")
        tests = unit_tests(tree)
        base = evaluate(tree, tests, driver_src, lines, expected, exhaustive)
        if base != ([], 0, False):
            sys.exit(f"the unmutated module fails: {base}")
        print(f"{len(tests)} unit tests, {len(lines)} cases"
              f"{', exhaustive tests' if exhaustive else ''}", flush=True)
        survivors, only_ex, total = [], [], 0
        for name, description, edits in MUTANTS:
            if wanted is not None and name not in wanted:
                continue
            total += 1
            (tree / MODULE).write_text(mutate(original, edits))
            result = evaluate(tree, tests, driver_src, lines, expected, exhaustive)
            if result is None:
                print(f"{name:4}{description}: does not compile")
                continue
            failed, differ, ex = result
            short = ", ".join(t.replace("test_schnorrsig_", "") for t in failed) or "none"
            print(f"{name:4}{description}\n      tests: {short}\n      cases: {differ}"
                  + (f"\n      exhaustive: {'fails' if ex else 'passes'}" if exhaustive else ""),
                  flush=True)
            if not failed and not differ:
                (only_ex if ex else survivors).append(name)
        print(f"only the exhaustive tests catch: {', '.join(only_ex) or 'none'}")
        print(f"{total - len(survivors)} of {total} mutants caught, survivors: "
              f"{', '.join(survivors) or 'none'}")


if __name__ == "__main__":
    main()
