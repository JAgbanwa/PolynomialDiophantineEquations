#!/bin/bash
# Regression tests for src/k7.c. Usage: bash tools/validate.sh [--full]     (from the folder root)
# Quick (~1 min): K=41 known solution found 3 times under two different work splits, and an exact K=7 candidate count.
# --full (~2-3 min more): exact candidate counts reproduced by earlier, independently written programs.
cd "$(dirname "$0")/.." || exit 1
CC=${CC:-cc}; J=${J:-$(nproc 2>/dev/null || sysctl -n hw.ncpu)}
D=$(mktemp -d); trap 'rm -rf "$D"' EXIT
$CC -O3 -o $D/k7 src/k7.c -lm -lpthread && $CC -O3 -DK=41 -o $D/k41 src/k7.c -lm -lpthread || { echo "compile failed"; exit 1; }
fail=0
check(){ # name expected_candidates expected_solutions command...
  local name=$1 ec=$2 es=$3; shift 3
  "$@" -p $D/p -s $D/s -l $D/l > $D/o 2>&1; rm -f $D/p
  local c=$(grep -o "candidates=[0-9]*" $D/o | head -1 | cut -d= -f2) s=$(grep -c SOLUTION $D/s 2>/dev/null); rm -f $D/s
  if [ "$c" = "$ec" ] && [ "$s" = "$es" ]; then echo "PASS $name (candidates=$c solutions=$s)"; else echo "FAIL $name: candidates=$c (expect $ec) solutions=$s (expect $es)"; fail=1; fi
}
check "K=41, sieve T=997 + large primes"   310109   3 $D/k41 -j $J -T 997 -R 8 -a -40001 40000 -b 997 925000 0 400002
check "K=41, sieve only (T=2e6)"           310109   3 $D/k41 -j $J -T 2000000 -R 8 -a -40001 40000
check "K=7, large primes, |d| to 1e13"     24517097 0 $D/k7  -j $J -T 2300001000 -b 2300001000 2300201000 1000000000000 9999999999999 -ub 18
if [ "${1:-}" = "--full" ]; then
check "K=7, all |d| < 1e8 (sieve)"         132688589 0 $D/k7 -j $J -T 231000000 -a -10000000 10000000
check "K=7, large primes, |d| to 1e12"     99760564 0 $D/k7  -j $J -T 2300001000 -b 2300001000 2310001000 10000000000 999999999999
fi
[ $fail = 0 ] && echo "ALL PASSED" || { echo "SOME TESTS FAILED"; exit 1; }
