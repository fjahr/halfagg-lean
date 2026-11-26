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
#   prints or the README lists,
# - the list of definitions in REVIEW.md is the one that Halfagg/Summary.lean
#   guards, and it has no module under Halfagg/Proofs/,
# - the table of the main results in REVIEW.md is the one that
#   Halfagg/Summary.lean guards, and REVIEW.md prints the statement of every
#   main result.
# scripts/check_selftest.sh checks that these checks fail when they should.
set -eu
cd "$(dirname "$0")/.."
fail=0
files=$(find . -name '*.lean' -not -path './.lake/*' | sed 's|^\./||' | sort)
# The file names are passed to grep as words, so a path with a space or another
# unusual character would not be read.
if echo "$files" | grep -vE '^[A-Za-z0-9_./-]+$'; then
  echo 'error: a Lean file with an unexpected character in its path'; fail=1
fi
# Halfagg/Summary.lean is generated and quotes axiom names: it is checked line
# by line below instead.
scanned=$(echo "$files" | grep -v '^Halfagg/Summary\.lean$')
# `forbid MESSAGE ARGS`: fail if grep with ARGS finds a match in the scanned
# files, or if it cannot read one of them.
forbid() {
  message=$1
  shift
  status=0
  grep "$@" $scanned || status=$?
  if [ "$status" -eq 0 ]; then
    echo "error: $message"; fail=1
  elif [ "$status" -gt 1 ]; then
    echo 'error: grep could not read a file'; fail=1
  fi
}
forbid 'sorry or admit found' -nwE 'sorry|admit'
forbid 'axiom, unsafe code or kernel bypass found' -nwE 'axiom|unsafe|implemented_by|extern|skipKernelTC'
scanned=$(echo "$scanned" | grep -v '^Halfagg/Vectors\.lean$')
forbid 'compiled evaluation outside the test vector checks' -lE 'native|ofReduceBool|reduceBool|trustCompiler'
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
                     r"#guard_msgs in|#print axioms [A-Za-z0-9_.']+|#project_axioms|"
                     r"#(surface|reading)( [A-Za-z0-9_.']+)+")
raw = pathlib.Path('Halfagg/Summary.lean').read_text()
summary = re.sub(r'/-.*?-/', '', raw, flags=re.S)
for line in summary.split('\n'):
    if line.strip() and not allowed.fullmatch(line):
        print('error: Halfagg/Summary.lean has an unexpected line: ' + line)
        bad = 1
for command in ('#project_axioms', '#surface ', '#reading '):
    if ('#guard_msgs in\n' + command) not in summary:
        print('error: Halfagg/Summary.lean does not guard ' + command.strip())
        bad = 1
# No definition behind the results is under Halfagg/Proofs/, so the proofs can
# stay unread.
end = raw.find('\n-/\n#guard_msgs in\n#surface ')
start = raw.rfind('/--\ninfo: ', 0, end)
for line in raw[start:end].split('\n'):
    if line.startswith('Halfagg.Proofs.'):
        print('error: a definition behind the results is under Halfagg/Proofs/: ' + line[:100])
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
# The table of the main results and the list of definitions in REVIEW.md must
# be the ones in Halfagg/Summary.lean.
python3 scripts/gen_review.py --check || fail=1
# Halfagg/Summary.lean must check the axioms of every theorem printed in
# REVIEW.md and of every result in the README's tables. A result is found by
# its full name: a declaration with the same last name in another namespace
# does not count.
python3 - <<'EOF' || fail=1
import pathlib, re, sys
DECL = re.compile(r"(?:@\[[^\]]*\]\s*)?(?:noncomputable |private |protected )*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([^\s:({\[]+)")


def declarations(text):
    """The full name and the position of every declaration that starts a line."""
    stack, out, pos = [], [], 0
    for line in text.split('\n'):
        m = re.fullmatch(r'namespace\s+(\S+)\s*', line)
        if m:
            stack.append(m.group(1))
        elif re.fullmatch(r'section(\s+\S+)?\s*', line):
            stack.append(None)
        elif re.fullmatch(r'end(\s+\S+)?\s*', line) and stack:
            stack.pop()
        else:
            m = DECL.match(line)
            if m:
                out.append(('.'.join([n for n in stack if n] + [m.group(1)]), pos))
        pos += len(line) + 1
    return out


sources = {p: p.read_text() for p in pathlib.Path('Halfagg').rglob('*.lean')
           if p.name != 'Summary.lean'}
decls = {p: declarations(s) for p, s in sources.items()}
names = [full for l in decls.values() for full, _ in l]
checked = set(re.findall(r'^#print axioms (\S+)', pathlib.Path('Halfagg/Summary.lean').read_text(),
                         re.M))
bad = 0
printed = set()
# The theorems that REVIEW.md prints, with the namespace they have in the sources.
for block in re.findall(r'```lean\n(.*?)\n```', pathlib.Path('REVIEW.md').read_text(), re.S):
    for m in re.finditer(r'^(?:theorem|lemma)\s+', block, re.M):
        homes = [(p, s.find(block)) for p, s in sources.items() if block in s]
        if not homes:
            continue    # reported above
        if len(homes) > 1:
            print('error: REVIEW.md block is in more than one source file:\n' + block)
            bad = 1
            continue
        p, at = homes[0]
        full = [f for f, pos in decls[p] if pos == at + m.start()]
        if len(full) != 1 or full[0] not in checked:
            print('error: Halfagg/Summary.lean does not check the axioms of the printed theorem at: '
                  + block[m.start():].split('\n')[0][:80])
            bad = 1
        printed.update(full)
# REVIEW.md prints the statement of every main result.
main = re.findall(r'^#reading (.*)$', pathlib.Path('Halfagg/Summary.lean').read_text(), re.M)
for name in sorted({name for line in main for name in line.split()} - printed):
    print('error: REVIEW.md does not print the statement of the main result ' + name)
    bad = 1
# The results in the README's tables: each names exactly one declaration.
table = pathlib.Path('README.md').read_text().split('## Results')[1].split('\n## ')[0]
for line in table.split('\n'):
    if line.startswith('| `'):
        for short in re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", line.split('|')[1]):
            full = [f for f in names if f == short or f.endswith('.' + short)]
            if len(full) != 1:
                print(f'error: the README names {short}, which is {len(full)} declarations')
                bad = 1
            elif full[0] not in checked:
                print('error: Halfagg/Summary.lean does not check the axioms of ' + full[0])
                bad = 1
sys.exit(bad)
EOF
exit $fail
