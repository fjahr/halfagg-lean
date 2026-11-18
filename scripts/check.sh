#!/bin/sh
# Source checks that complement the axiom checks in Halfagg/Summary.lean:
# no `sorry`, no new axioms or unsafe code, and compiled evaluation
# (`native_decide`, `decide +native`) only in the test vector checks.
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
exit $fail
