#!/usr/bin/env bash
# Validates the sieve against brute force on y z (y+z) = 6x^3 + x^2 + K for several K (these DO have solutions).
# Needs: gcc or clang, python3 with sympy.
set -euo pipefail
cd "$(dirname "$0")"
CC=${CC:-$(command -v gcc || command -v clang)}
$CC -O3 -o ysearch5 ../src/ysearch5.c -lpthread -lm
for K in 2 3 5 7 18 25; do
  ./ysearch5 $K 4 3000 4 > c_$K.txt 2>/dev/null
  python3 ref.py $K 4 3000 > r_$K.txt
  python3 cmp.py c_$K.txt r_$K.txt $K
done
# work-splitting check: 3 pieces together must equal the full run
for w in 0 1 2; do ./ysearch5 5 4 3000 2 2048 $w 3 > s_$w.txt 2>/dev/null; done
cat s_0.txt s_1.txt s_2.txt > s_all.txt; python3 cmp.py s_all.txt r_5.txt 5
