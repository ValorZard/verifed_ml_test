#!/usr/bin/env bash
# Build the verified quicksort from scratch.
#
#   ./build.sh          Tier 1: proofs + generated CakeML program + binary
#                       (compiled with CakeML's verified bootstrapped compiler)
#   ./build.sh tier2    Tier 2: additionally compile inside HOL4 and prove the
#                       end-to-end theorem about the x64 machine code
#                       (builds CakeML's compiler proofs: several hours)
#
# Everything runs in Docker; the hol/ directory is mounted into the
# container at /opt/cakeml/examples/verified_qsort.
set -euo pipefail
cd "$(dirname "$0")"
export MSYS_NO_PATHCONV=1          # Git Bash on Windows: don't mangle paths

IMAGE=vqs-toolchain:base
NAME=vqs-dev
HOLDIR_IN=/opt/cakeml/examples/verified_qsort

docker image inspect "$IMAGE" >/dev/null 2>&1 || docker build -t "$IMAGE" docker

if ! docker container inspect "$NAME" >/dev/null 2>&1; then
  docker run -d --name "$NAME" -v "$(pwd -W 2>/dev/null || pwd)/hol:$HOLDIR_IN" "$IMAGE" sleep infinity
fi
docker start "$NAME" >/dev/null

run() { docker exec "$NAME" bash -lc "cd $HOLDIR_IN && $*"; }

# 1. Check all proofs and generate the CakeML program (writes hol/qsort.sexp)
run "Holmake -j8"

# 2. Compile with the verified CakeML compiler binary and link with the FFI
run "mkdir -p build && cake --sexp=true < qsort.sexp > build/qsort.S && \
     gcc -O2 -o build/qsort build/qsort.S /opt/cake/cake-x64-64/basis_ffi.c -lm"

if [ "${1:-}" = "tier2" ]; then
  # 3. Compile inside the logic (writes hol/compile/qsort.S) and prove the
  #    machine-code theorem qsort_compiled_thm.
  run "cd compile && Holmake -j6 qsortProofTheory"
  run "gcc -O2 -o build/qsort_inlogic compile/qsort.S /opt/cake/cake-x64-64/basis_ffi.c -lm"
fi

echo
echo "Done.  Try:  MSYS_NO_PATHCONV=1 docker exec $NAME $HOLDIR_IN/build/qsort 5 3 -1 42 0"
echo "       (MSYS_NO_PATHCONV=1 is only needed in Git Bash on Windows)"
