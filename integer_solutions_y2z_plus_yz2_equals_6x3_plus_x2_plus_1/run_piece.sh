#!/usr/bin/env bash
# Run piece WID of NW of the exhaustive search  y^2 z + y z^2 = 6x^3 + x^2 + 1,  UMIN <= |x| <= UMAX.
# usage: bash run_piece.sh UMIN UMAX WID NW [THREADS]
set -euo pipefail
UMIN=$1; UMAX=$2; WID=$3; NW=$4
THREADS=${5:-$( (nproc 2>/dev/null) || sysctl -n hw.ncpu )}
HERE="$(cd "$(dirname "$0")" && pwd)"
CC=${CC:-$(command -v gcc || command -v clang)}
[ -x ./ysearch5 ] || $CC -O3 -march=native -o ysearch5 "$HERE/src/ysearch5.c" -lpthread -lm 2>/dev/null \
                  || $CC -O3 -o ysearch5 "$HERE/src/ysearch5.c" -lpthread -lm
./ysearch5 1 "$UMIN" "$UMAX" "$THREADS" 2048 "$WID" "$NW" > "sols_${WID}_of_${NW}.txt" 2> "log_${WID}_of_${NW}.txt"
cat "sols_${WID}_of_${NW}.txt"
