#!/bin/sh
# Check that scripts/check.sh fails when it should. Each case changes a copy of
# the sources in one way that the checks are there to catch.
set -eu
cd "$(dirname "$0")/.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fresh() {
  rm -rf "$tmp/work"
  mkdir "$tmp/work"
  cp -R Halfagg.lean Halfagg scripts README.md REVIEW.md "$tmp/work/"
}
fail=0
expect_fail() {
  if "$tmp/work/scripts/check.sh" > "$tmp/out" 2>&1; then
    echo "error: scripts/check.sh passes with $1"; fail=1
  else
    echo "caught: $1"
  fi
}
fresh
"$tmp/work/scripts/check.sh" || { echo 'error: scripts/check.sh fails on the unchanged sources'; exit 1; }

fresh
echo 'axiom audit_backdoor : False' >> "$tmp/work/Halfagg.lean"
expect_fail 'an axiom in the root module'

fresh
echo 'axiom audit_backdoor : False' >> "$tmp/work/Halfagg/Summary.lean"
expect_fail 'an axiom in the generated summary'

fresh
echo 'axiom audit_backdoor : False' >> "$tmp/work/scripts/Fuzz.lean"
expect_fail 'an axiom in a script'

fresh
echo 'theorem audit_backdoor : False := by sorry' >> "$tmp/work/Halfagg/Basic.lean"
expect_fail 'a sorry'

fresh
echo 'theorem audit_backdoor : 1 = 1 := by native_decide' >> "$tmp/work/Halfagg/Basic.lean"
expect_fail 'compiled evaluation outside the test vector checks'

fresh
echo '#print axioms Nat.add_comm' >> "$tmp/work/Halfagg/Summary.lean"
expect_fail 'a command without a guard in the generated summary'

fresh
sed 's/^theorem halfagg_unforgeable /theorem halfagg_unforgeable_changed /' "$tmp/work/REVIEW.md" > "$tmp/review"
cp "$tmp/review" "$tmp/work/REVIEW.md"
expect_fail 'a printed statement that is not in the sources'

fresh
grep -v '^#print axioms Halfagg.Security.halfagg_unforgeable$' "$tmp/work/Halfagg/Summary.lean" > "$tmp/summary"
cp "$tmp/summary" "$tmp/work/Halfagg/Summary.lean"
expect_fail 'a printed theorem whose axioms the summary does not check'

fresh
printf '\nnamespace Other\ntheorem halfagg_unforgeable : True := trivial\nend Other\n' >> "$tmp/work/Halfagg/Tightness.lean"
sed 's/^#print axioms Halfagg.Security.halfagg_unforgeable$/#print axioms Other.halfagg_unforgeable/' "$tmp/work/Halfagg/Summary.lean" > "$tmp/summary"
cp "$tmp/summary" "$tmp/work/Halfagg/Summary.lean"
expect_fail 'a summary that checks another theorem with the same last name'

fresh
echo 'theorem audit_backdoor : False := by sorry' > "$tmp/work/Halfagg/Back door.lean"
expect_fail 'a sorry in a file with a space in its name'

exit $fail
