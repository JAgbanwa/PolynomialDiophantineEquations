#!/bin/bash
cd "$(dirname "$0")" || exit 1
. ./config.sh
n=$(ls done 2>/dev/null | wc -l | tr -d ' ')
c=0; while :; do if [ $((c % RES)) -ne 0 ] && [ ! -f "done/$c" ]; then break; fi; c=$((c+1)); done
echo "Mac chunks done: $n.  Every Mac chunk below index $c is finished, i.e. this Mac has covered its share of |a| < $((BASE + c*WIDTH))  (|x| < $((2*(BASE + c*WIDTH))))."
echo "Workers running: $(pgrep -f x2y_search_worker | wc -l | tr -d ' ')"
[ -s logs/errors.log ] && { echo "Errors:"; tail -3 logs/errors.log; }
if grep -h SOLUTION logs/sol_*.log 2>/dev/null; then echo "*** SOLUTION FOUND (see above) ***"; else echo "No solution yet."; fi
