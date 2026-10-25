#!/bin/bash
# Checks the freshly built searcher against counts computed independently (Python/sympy re-implementation).
cd "$(dirname "$0")" || exit 1
fail=0; : > selftest.log
t() { out=$(NBAD=nbad.txt ./search_mac $1 $2 $3 524288 2>&1 >/dev/null | grep -o 'kept=[0-9]* cand=[0-9]* alive=[0-9]* sqrt=[0-9]*')
      echo "$1 $2 $3 -> $out (expected $4)" >> selftest.log
      [ "$out" = "$4" ] || { echo "MISMATCH: $1 $2 $3 -> $out, expected $4"; fail=1; }; }
t  1 0 3000                        "kept=201 cand=281 alive=146 sqrt=1"
t -1 0 3000                        "kept=173 cand=242 alive=115 sqrt=4"
t  1 1000000 1003000               "kept=138 cand=246 alive=119 sqrt=4"
t -1 1000000000 1006000000         "kept=148729 cand=315864 alive=157988 sqrt=4210"
t -1 297777777777 297777799777     "kept=440 cand=1079 alive=522 sqrt=19"
t  1 27777777777777 27777777797777 "kept=452 cand=1168 alive=592 sqrt=21"
[ $fail = 0 ] && echo "Self-test passed." || echo "Self-test FAILED."
exit $fail
