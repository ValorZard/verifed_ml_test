#!/usr/bin/env bash
# CI checks.  Runs inside the CI toolchain image (docker/Dockerfile, stage ci).
#
#   ci/check.sh [SOURCE_DIR]     (default: current directory)
#
# 1. Re-checks every proof (HOL4 + CakeML theories in hol/ and hol/pancake/).
# 2. Fails if any theorem depends on a cheat or other oracle.
# 3. Compiles the generated CakeML program and the Pancake program with the
#    verified CakeML compiler binary, links them, and tests the executables.
#
# Outputs (assembly + binaries) go to $OUT (default: SOURCE_DIR/ci-out).
set -euo pipefail

SRC="$(cd "${1:-.}" && pwd)"
OUT="${OUT:-$SRC/ci-out}"
JOBS="${JOBS:-$(nproc)}"
# A private copy inside the CakeML tree, so Holmake resolves CakeML theories.
WORK="$CAKEMLDIR/examples/vqs_ci"

step() { printf '\n==== %s\n' "$*"; }
fail() { echo "FAIL: $*" >&2; exit 1; }

step "Copying sources to $WORK"
rm -rf "$WORK"
mkdir -p "$WORK" "$OUT"
cp -r "$SRC/hol/." "$WORK/"
rm -rf "$WORK/build" "$WORK/pancake/build" "$WORK/pancake/dev" "$WORK/qsort.sexp"
find "$WORK" -name .hol -type d -prune -exec rm -rf {} +

step "Checking the quicksort proofs and generating the CakeML program"
cd "$WORK"
Holmake -j"$JOBS" qsortTheory qsortProgTheory
test -s qsort.sexp || fail "qsort.sexp was not generated"

step "Checking the Pancake program logic and contract proofs"
cd "$WORK/pancake"
Holmake -j"$JOBS" panQsortProofTheory

step "Checking that no theorem depends on a cheat or oracle"
cd "$WORK"
hol --holstate="$CAKEMLDIR/basis/basis-heap" < "$SRC/ci/no_cheats.sml" \
  > "$OUT/no_cheats.log" 2>&1 || true
grep -E "no-cheats|depends on oracle" "$OUT/no_cheats.log" || true
grep -q "no-cheats: OK" "$OUT/no_cheats.log" || fail "oracle check (see no_cheats.log)"

step "Compiling the CakeML program with the verified compiler"
cake --sexp=true < "$WORK/qsort.sexp" > "$OUT/qsort.S"
gcc -O2 -o "$OUT/qsort" "$OUT/qsort.S" /opt/cake/cake-x64-64/basis_ffi.c -lm

step "Testing the CakeML binary (numbers as command-line arguments)"
expected=$'-17\n-1\n0\n3\n3\n5\n9\n42\n100'
[ "$("$OUT/qsort" 5 3 9 -1 0 42 3 -17 100)" = "$expected" ] || fail "small example"
[ -z "$("$OUT/qsort")" ] || fail "no arguments should print nothing"
[ -z "$("$OUT/qsort" 3 abc 1 2>/dev/null)" ] || fail "bad argument should print nothing on stdout"
"$OUT/qsort" 3 abc 1 2>&1 >/dev/null | grep -q usage || fail "bad argument should print usage on stderr"
[ "$("$OUT/qsort" 123456789012345678901234567890 7 +7 ~4)" = $'-4\n7\n7\n123456789012345678901234567890' ] \
  || fail "bignums and signs"
nums=$(shuf -i 1-100000 -n 2000 | tr '\n' ' ')
diff <(printf '%s\n' $nums | sort -n) <("$OUT/qsort" $nums) || fail "2000 random numbers"

step "Compiling the Pancake program with the verified compiler"
cake --pancake < "$WORK/pancake/qsort.pnk" > "$OUT/qsort_pan.S"
gcc -O2 -o "$OUT/qsort_pan" "$OUT/qsort_pan.S" "$WORK/pancake/qsort_ffi.c"

step "Testing the Pancake binary (numbers on stdin)"
[ "$(echo '5 3 9 -1 0 42 3 -17 100' | "$OUT/qsort_pan")" = "$expected" ] || fail "small example"
[ -z "$(printf '' | "$OUT/qsort_pan")" ] || fail "empty input should print nothing"
[ "$(echo '9223372036854775807 -9223372036854775808 0' | "$OUT/qsort_pan")" = \
  $'-9223372036854775808\n0\n9223372036854775807' ] || fail "64-bit extremes"
shuf -i 1-1000000 -n 200000 > "$OUT/random.txt"
diff <(sort -n "$OUT/random.txt") <("$OUT/qsort_pan" < "$OUT/random.txt") || fail "200000 random numbers"
rm -f "$OUT/random.txt"

step "All checks passed"
ls -l "$OUT"
