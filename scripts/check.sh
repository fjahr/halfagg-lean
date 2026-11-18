#!/bin/sh
# Source checks that complement the axiom checks in Halfagg/Summary.lean:
# no `sorry`, no new axioms or unsafe code, compiled evaluation
# (`native_decide`, `decide +native`) only in the test vector checks, and the
# statements printed in REVIEW.md match the sources.
set -eu
cd "$(dirname "$0")/.."
fail=0
if grep -rnwE 'sorry|admit' Halfagg --include='*.lean' | grep -v '^Halfagg/Summary.lean:'; then
  echo 'error: sorry or admit found'; fail=1
fi
if grep -rnwE 'axiom|unsafe|implemented_by|extern|skipKernelTC' Halfagg --include='*.lean' |
    grep -v '^Halfagg/Summary.lean:'; then
  echo 'error: axiom, unsafe code or kernel bypass found'; fail=1
fi
if grep -rlE 'native|ofReduceBool|reduceBool|trustCompiler' Halfagg --include='*.lean' |
    grep -vE '^Halfagg/(Vectors|Summary)\.lean$'; then
  echo 'error: compiled evaluation outside the test vector checks'; fail=1
fi
# Every Lean code block in REVIEW.md must be in the sources word for word.
python3 - <<'EOF' || fail=1
import pathlib, re, sys
sources = [p.read_text() for p in pathlib.Path('Halfagg').rglob('*.lean')]
bad = 0
for block in re.findall(r'```lean\n(.*?)\n```', pathlib.Path('REVIEW.md').read_text(), re.S):
    if not any(block in s for s in sources):
        print('error: REVIEW.md block not found in the sources:\n' + block)
        bad = 1
sys.exit(bad)
EOF
exit $fail
