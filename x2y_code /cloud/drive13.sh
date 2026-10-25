#!/bin/bash
# Resumable driver: searches |a| in [state, END) in chunks (both signs).
# state11.txt holds the next |a| to search; it is advanced only after a chunk completes for BOTH signs.
# The binary is read from bin.txt (if present) at the start of every chunk, so it can be swapped safely.
# usage: ./drive13.sh END [BUDGET_SECONDS] [CHUNK]
cd "$(dirname "$0")"
END=$1; BUDGET=${2:-6600}; CH=${3:-200000000000}
STATE=state11.txt; t0=$(date +%s)
while true; do
  BIN=./search13; [ -s bin.txt ] && BIN=$(head -1 bin.txt)
  A=$(cat $STATE)
  if [ "$A" -ge "$END" ]; then echo "REACHED_END $A $(date)" >> prog11.log; break; fi
  B=$((A + CH)); [ $B -gt $END ] && B=$END
  for r in 3 33; do
    if [ $r = 3 ]; then s=1; else s=-1; fi
    lo=$(( (A - r + 35) / 36 )); hi=$(( (B - r + 35) / 36 )); [ $lo -lt 0 ] && lo=0
    if ! NBAD=${NBAD:-nbad.txt} $BIN $s $lo $hi ${SEG:-} >> sol11.log 2>> prog11.log; then echo "ERROR in chunk A=$A s=$s bin=$BIN $(date)" >> prog11.log; exit 1; fi
  done
  echo $B > $STATE.tmp && mv $STATE.tmp $STATE
  if grep -q SOLUTION sol11.log; then echo "SOLUTION_FOUND $(date)" >> prog11.log; break; fi
  if [ $(( $(date +%s) - t0 )) -ge $BUDGET ]; then echo "BUDGET_STOP next=$B $(date)" >> prog11.log; break; fi
done
