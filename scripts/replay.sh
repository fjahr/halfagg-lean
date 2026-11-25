#!/bin/sh
# Replay modules in the kernel, without the elaborator.
#
#   scripts/replay.sh         every project module and every module of
#                             taproot-lean and agm-lean that the project imports
#   scripts/replay.sh --deps  every module of VCVio, PolyFun and cslib that the
#                             project imports, directly or through other modules
#
# With `--list` as the last argument the script prints the modules and replays
# nothing. Mathlib and the libraries it is built on are not replayed here.
#
# `lake env leanchecker Halfagg` replays all modules in parallel, and each one
# loads Mathlib (about 5 GB). This script runs one process per module instead.
# The root module `Halfagg` only has imports, and its name is a prefix of every
# other module, so it is skipped.
set -eu
cd "$(dirname "$0")/.."
packages="TaprootLean agm-lean"
project=1
if [ "${1:-}" = "--deps" ]; then
  packages="VCVio PolyFun cslib"
  project=0
  shift
fi
# The modules of the given packages in the import closure of the project.
closure() {
  python3 - "$@" <<'EOF'
import pathlib, re, sys
wanted = sys.argv[1:]
packages = pathlib.Path('.lake/packages')
base = {'mathlib', 'batteries', 'aesop', 'Qq', 'proofwidgets', 'plausible', 'importGraph',
        'LeanSearchClient', 'Cli'}
roots = [(None, pathlib.Path('.'))] + [(p.name, p) for p in sorted(packages.iterdir())
                                       if p.name not in base]
imp = re.compile(r'^(?:public |private |meta )*import (?:all )?([A-Za-z0-9_.]+)', re.M)
todo = imp.findall(pathlib.Path('Halfagg.lean').read_text())
seen = {}
while todo:
    m = todo.pop()
    if m in seen:
        continue
    seen[m] = None
    for name, root in roots:
        f = root / (m.replace('.', '/') + '.lean')
        if f.exists():
            seen[m] = name
            todo += imp.findall(f.read_text())
            break
print('\n'.join(sorted(m for m, name in seen.items() if name in wanted)))
EOF
}
mods=$(closure $packages)
if [ "$project" = 1 ]; then
  mods="$mods $(find Halfagg -name '*.lean' | sort | sed 's/\.lean$//' | tr / .)"
fi
if [ "${1:-}" = "--list" ]; then
  echo "$mods" | tr ' ' '\n'
  exit 0
fi
for mod in $mods; do
  echo "replay $mod"
  lake env leanchecker "$mod"
done
