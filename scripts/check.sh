#!/bin/sh
# Source checks that complement the checks in Halfagg/Summary.lean. They read
# every Lean file of the repository:
# - no `sorry`, no new axioms, no unsafe code and no kernel bypass,
# - compiled evaluation (`native_decide`, `decide +native`) only in the test
#   vector checks,
# - the root module has nothing but imports, and the generated summary has
#   nothing but imports and guarded commands,
# - the statements printed in REVIEW.md match the sources, and
#   Halfagg/Summary.lean checks the axioms of every result that REVIEW.md
#   prints or the README lists.
# scripts/check_selftest.sh checks that these checks fail when they should.
set -eu
cd "$(dirname "$0")/.."
fail=0
files=$(find . -name '*.lean' -not -path './.lake/*' | sed 's|^\./||' | sort)
# Halfagg/Summary.lean is generated and quotes axiom names: it is checked line
# by line below instead.
scanned=$(echo "$files" | grep -v '^Halfagg/Summary\.lean$')
if grep -nwE 'sorry|admit' $scanned; then
  echo 'error: sorry or admit found'; fail=1
fi
if grep -nwE 'axiom|unsafe|implemented_by|extern|skipKernelTC' $scanned; then
  echo 'error: axiom, unsafe code or kernel bypass found'; fail=1
fi
if grep -lE 'native|ofReduceBool|reduceBool|trustCompiler' $scanned |
    grep -vE '^Halfagg/Vectors\.lean$'; then
  echo 'error: compiled evaluation outside the test vector checks'; fail=1
fi
python3 - <<'EOF' || fail=1
import pathlib, re, sys
bad = 0
# The root module: imports only.
for line in pathlib.Path('Halfagg.lean').read_text().split('\n'):
    if line and not re.fullmatch(r'import Halfagg(\.[A-Za-z0-9_]+)+', line):
        print('error: Halfagg.lean has a line that is not an import: ' + line)
        bad = 1
# The generated summary: outside of comments only imports and guarded commands.
allowed = re.compile(r"import Halfagg(\.[A-Za-z0-9_]+)+|set_option linter\.style\.longLine false|"
                     r"#guard_msgs in|#print axioms [A-Za-z0-9_.']+")
summary = re.sub(r'/-.*?-/', '', pathlib.Path('Halfagg/Summary.lean').read_text(), flags=re.S)
for line in summary.split('\n'):
    if line.strip() and not allowed.fullmatch(line):
        print('error: Halfagg/Summary.lean has an unexpected line: ' + line)
        bad = 1
lines = [l for l in summary.split('\n') if l.strip()]
for prev, line in zip([''] + lines, lines):
    if line.startswith('#') and line != '#guard_msgs in' and prev != '#guard_msgs in':
        print('error: Halfagg/Summary.lean has a command without a guard: ' + line[:60])
        bad = 1
# Every Lean code block in REVIEW.md must be in the sources word for word.
sources = [p.read_text() for p in pathlib.Path('Halfagg').rglob('*.lean')]
for block in re.findall(r'```lean\n(.*?)\n```', pathlib.Path('REVIEW.md').read_text(), re.S):
    if not any(block in s for s in sources):
        print('error: REVIEW.md block not found in the sources:\n' + block)
        bad = 1
sys.exit(bad)
EOF
# Halfagg/Summary.lean must check the axioms of every theorem printed in
# REVIEW.md and of every result in the README's tables.
python3 - <<'EOF' || fail=1
import pathlib, re, sys
summary = pathlib.Path('Halfagg/Summary.lean').read_text()
checked = {m.split('.')[-1] for m in re.findall(r'^#print axioms (\S+)', summary, re.M)}
names = []
for block in re.findall(r'```lean\n(.*?)\n```', pathlib.Path('REVIEW.md').read_text(), re.S):
    names += re.findall(r'^(?:theorem|lemma)\s+(\S+)', block, re.M)
table = pathlib.Path('README.md').read_text().split('## Results')[1].split('\n## ')[0]
for line in table.split('\n'):
    if line.startswith('| `'):
        names += re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", line.split('|')[1])
missing = sorted({x for x in names if x.split('.')[-1] not in checked})
if missing:
    print('error: Halfagg/Summary.lean does not check the axioms of: ' + ', '.join(missing))
sys.exit(bool(missing))
EOF
exit $fail
