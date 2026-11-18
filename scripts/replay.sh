#!/bin/sh
# Replay every project module in the kernel, without the elaborator.
#
# `lake env leanchecker Halfagg` replays all modules in parallel, and each one
# loads Mathlib (about 5 GB). This script runs one process per module instead.
# The root module `Halfagg` only has imports, and its name is a prefix of every
# other module, so it is skipped.
set -eu
cd "$(dirname "$0")/.."
for f in $(find Halfagg -name '*.lean' | sort); do
  mod=$(echo "${f%.lean}" | tr / .)
  echo "replay $mod"
  lake env leanchecker "$mod"
done
