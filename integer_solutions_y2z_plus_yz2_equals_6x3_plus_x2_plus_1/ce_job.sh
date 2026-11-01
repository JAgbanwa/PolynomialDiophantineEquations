#!/usr/bin/env bash
# Self-contained Charity Engine / generic cloud job.
# usage: bash ce_job.sh UMIN UMAX WID NW
# Downloads the C source from GitHub, compiles it, runs piece WID of NW on all cores,
# and prints a one-line verdict:  PIECE WID/NW UMIN..UMAX : DONE ... sols=0   (sols>0 => SOL lines above it)
set -euo pipefail
UMIN=$1; UMAX=$2; WID=$3; NW=$4
SRC_URL="https://raw.githubusercontent.com/JAgbanwa/PolynomialDiophantineEquations/main/integer_solutions_y2z_plus_yz2_equals_6x3_plus_x2_plus_1/src/ysearch5.c"
mkdir -p out
(curl -fsSL "$SRC_URL" -o ysearch5.c) || (wget -qO ysearch5.c "$SRC_URL")
gcc -O3 -march=native -o ysearch5 ysearch5.c -lpthread -lm 2>/dev/null || gcc -O3 -o ysearch5 ysearch5.c -lpthread -lm
T=$(nproc)
START=$(date +%s)
./ysearch5 1 "$UMIN" "$UMAX" "$T" 2048 "$WID" "$NW" > out/sols_${WID}.txt 2> out/log_${WID}.txt
END=$(date +%s)
grep '^SOL' out/sols_${WID}.txt || true
echo "PIECE $WID/$NW $UMIN..$UMAX threads=$T seconds=$((END-START)) : $(grep '^DONE' out/sols_${WID}.txt)"
cp out/sols_${WID}.txt "result_${WID}_of_${NW}.txt" 2>/dev/null || true
