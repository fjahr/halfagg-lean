#!/usr/bin/env python3
"""
Differential test of the Lean byte-level model against BIP 458's Python reference.

Usage:
    python3 scripts/fuzz.py path/to/bips/bip-0458 [--cases N] [--seed S]
        [--secp256k1 path/to/fuzz_secp256k1] [--no-lean]

Generates random valid and malformed inputs for Aggregate, IncAggregate and
VerifyAggregate, runs them through halfagg.py and through the Lean model
(scripts/Fuzz.lean), and reports every case where the two disagree.

With --secp256k1, the same cases also run through libsecp256k1's
schnorrsig_halfagg module, using the driver built from
scripts/fuzz_secp256k1.c. The C API cannot express every malformed input; the
driver skips those cases.
"""

import argparse
import os
import random
import subprocess
import sys
from pathlib import Path

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
EDGES = [0, 1, 2, 5, P - 1, P, P + 1, N - 1, N, N + 1, 2**255, 2**256 - 1]


def b32(x):
    return x.to_bytes(32, "big")


class Gen:
    def __init__(self, rng, ref, bip340):
        self.rng, self.ref, self.bip340 = rng, ref, bip340
        # a small key pool, so that repeated keys and messages occur
        self.keys = [b32(rng.randrange(1, N)) for _ in range(4)]
        self.msgs = [rng.randbytes(32) for _ in range(4)]

    def rbytes(self, n):
        return self.rng.randbytes(n)

    def odd_len(self, good):
        return self.rbytes(self.rng.choice([0, 1, good - 1, good + 1, 2 * good]))

    def edge(self):
        return b32(self.rng.choice(EDGES))

    def triple(self):
        sk = self.rng.choice(self.keys)
        m = self.rng.choice(self.msgs) if self.rng.random() < 0.5 else self.rbytes(32)
        sig = self.bip340.schnorr_sign(m, sk, self.rbytes(32))
        return (self.bip340.pubkey_gen(sk), m, sig)

    def bad_triple(self):
        pk, m, sig = self.triple()
        k = self.rng.randrange(9)
        if k == 0: sig = sig[:32] + self.edge()
        elif k == 1: sig = self.edge() + sig[32:]
        elif k == 2: sig = self.odd_len(64)
        elif k == 3: pk = self.odd_len(32)
        elif k == 4: m = self.odd_len(32)
        elif k == 5: pk = self.edge()
        elif k == 6: sig = self.rbytes(64)
        elif k == 7: sig = sig[:32] + b32((int.from_bytes(sig[32:], "big") + 1) % N)
        else: pk = self.rbytes(32)
        return (pk, m, sig)

    def triples(self, lo=0, hi=5, bad=0.25):
        out = []
        for _ in range(self.rng.randint(lo, hi)):
            out.append(self.bad_triple() if self.rng.random() < bad else self.triple())
        return out

    def aggregate_of(self, pms):
        try:
            return self.ref.Aggregate(pms)
        except ValueError:
            return None

    def mutate_agg(self, agg, u):
        k = self.rng.randrange(8)
        a = bytearray(agg)
        if k == 0 and a:
            i = self.rng.randrange(len(a)); a[i] ^= 1 << self.rng.randrange(8)
        elif k == 1: a = a[:-32] + self.edge()
        elif k == 2 and u: 
            i = self.rng.randrange(u); a[32 * i:32 * i + 32] = self.edge()
        elif k == 3: a = a[:-1]
        elif k == 4: a = a + b"\x00"
        elif k == 5: a = a + self.rbytes(32)
        elif k == 6: a = a[32:]
        else: a = bytearray(self.rbytes(len(a)))
        return bytes(a)

    def case_aggregate(self):
        return ("A", self.triples())

    def case_inc(self):
        base = self.triples(0, 3, bad=0.0)
        agg = self.aggregate_of(base)
        pm = [(pk, m) for pk, m, _ in base]
        r = self.rng.random()
        if r < 0.25: agg = self.mutate_agg(agg, len(pm))
        elif r < 0.35 and pm: pm[self.rng.randrange(len(pm))] = (self.odd_len(32), self.rbytes(32))
        elif r < 0.40: pm.append((self.rbytes(32), self.rbytes(32)))
        return ("I", agg, pm, self.triples(0, 3))

    def case_verify(self):
        if self.rng.random() < 0.02:
            # The empty aggregate with s = n. A verifier without the check
            # s < n reduces it to the valid s = 0 and accepts. For any other
            # s >= n it rejects anyway, because the reduced s fails the equation.
            return ("V", b32(N), [])
        pms = self.triples(0, 4, bad=0.0)
        r = self.rng.random()
        if r < 0.10 and len(pms) >= 2:
            # shift s between the first two signatures: both become invalid,
            # the aggregate stays valid
            z1 = int(self.ref.hashHalfAgg_randomizer(
                [(pk, m, sig[:32]) for pk, m, sig in pms[:2]]))
            d = self.rng.randrange(1, N)
            s0 = (int.from_bytes(pms[0][2][32:], "big") + d * z1) % N
            s1 = (int.from_bytes(pms[1][2][32:], "big") - d) % N
            pms[0] = (pms[0][0], pms[0][1], pms[0][2][:32] + b32(s0))
            pms[1] = (pms[1][0], pms[1][1], pms[1][2][:32] + b32(s1))
        agg = self.aggregate_of(pms)
        pm = [(pk, m) for pk, m, _ in pms]
        if 0.10 <= r < 0.45: agg = self.mutate_agg(agg, len(pm))
        elif r < 0.55 and pm:
            i = self.rng.randrange(len(pm))
            k = self.rng.randrange(5)
            if k == 0: pm[i] = (self.edge(), pm[i][1])
            elif k == 1: pm[i] = (pm[i][0], self.rbytes(32))
            elif k == 2: pm[i] = (self.odd_len(32), pm[i][1])
            elif k == 3: pm[i] = (pm[i][0], self.odd_len(32))
            else: pm[i] = (self.rbytes(32), pm[i][1])
        elif r < 0.62 and len(pm) >= 2:
            self.rng.shuffle(pm)
        elif r < 0.67 and pm: pm.pop()
        elif r < 0.72: pm.append((self.rbytes(32), self.rbytes(32)))
        return ("V", agg, pm)


def hx(b):
    return b.hex() if b else "_"


def items(l):
    return ",".join(":".join(hx(x) for x in it) for it in l) if l else "-"


def encode(case):
    if case[0] == "A": return "A " + items(case[1])
    if case[0] == "I": return f"I {hx(case[1])} {items(case[2])} {items(case[3])}"
    return f"V {hx(case[1])} {items(case[2])}"


def reference(ref, case):
    try:
        if case[0] == "A": return ref.Aggregate(case[1]).hex()
        if case[0] == "I": return ref.IncAggregate(case[1], case[2], case[3]).hex()
        return "true" if ref.VerifyAggregate(case[1], case[2]) else "false"
    except ValueError:
        return "FAIL" if case[0] != "V" else "false"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("bip_dir", help="path to bips/bip-0458")
    ap.add_argument("--cases", type=int, default=600)
    ap.add_argument("--seed", type=int, default=458)
    ap.add_argument("--secp256k1", help="path to the driver built from scripts/fuzz_secp256k1.c")
    ap.add_argument("--no-lean", action="store_true", help="skip the Lean model")
    args = ap.parse_args()

    bip_dir = Path(args.bip_dir).resolve()
    sys.path.insert(0, str(bip_dir))
    sys.path.insert(0, str(bip_dir / "secp256k1lab/src"))
    import halfagg as ref
    from secp256k1lab import bip340

    gen = Gen(random.Random(args.seed), ref, bip340)
    makers = [gen.case_aggregate, gen.case_inc, gen.case_verify, gen.case_verify]
    cases = [makers[i % len(makers)]() for i in range(args.cases)]
    expected = [reference(ref, c) for c in cases]
    lines = [encode(c) for c in cases]

    kinds = {}
    for c, e in zip(cases, expected):
        key = (c[0], "accept" if e not in ("FAIL", "false") else "reject")
        kinds[key] = kinds.get(key, 0) + 1
    for key in sorted(kinds):
        print(f"{key[0]} {key[1]}: {kinds[key]}")

    root = Path(__file__).resolve().parent.parent
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ["PATH"])
    targets = []
    if not args.no_lean:
        targets.append(("lean", ["lake", "env", "lean", "--run", "scripts/Fuzz.lean"]))
    if args.secp256k1:
        targets.append(("secp256k1", [str(Path(args.secp256k1).resolve())]))

    failed = False
    for name, cmd in targets:
        out = subprocess.run(cmd, cwd=root, env=env, input="\n".join(lines) + "\n",
                             capture_output=True, text=True)
        got = out.stdout.split("\n")[:-1]
        if out.returncode != 0 or len(got) != len(cases):
            sys.exit(f"{name} driver failed ({len(got)} of {len(cases)} results):\n{out.stderr}")
        skipped = sum(g == "SKIP" for g in got)
        bad = [(l, e, g) for l, e, g in zip(lines, expected, got) if g != "SKIP" and e != g]
        for l, e, g in bad:
            print(f"MISMATCH\n  case:   {l}\n  python: {e}\n  {name}: {g}")
        print(f"{name}: {len(cases) - skipped} cases compared, {skipped} skipped, "
              f"{len(bad)} mismatches")
        failed = failed or bool(bad)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
