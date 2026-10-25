#!/bin/bash
# One worker: repeatedly claims the next free chunk (atomic mkdir), searches both signs of a, marks it done.
cd "$(dirname "$0")" || exit 1
W=$1
. ./config.sh
c=0
while [ ! -f STOP ]; do
  if [ $((c % RES)) -eq 0 ] || [ -f "done/$c" ]; then c=$((c+1)); continue; fi
  if ! mkdir "claims/$c" 2>/dev/null; then c=$((c+1)); continue; fi
  A=$((BASE + c*WIDTH)); B=$((A + WIDTH)); ok=1
  for r in 3 33; do
    if [ $r = 3 ]; then s=1; else s=-1; fi
    lo=$(( (A - r + 35) / 36 )); hi=$(( (B - r + 35) / 36 ))
    if ! NBAD=nbad.txt ./search_mac $s $lo $hi 524288 >> "logs/sol_$W.log" 2>> "logs/prog_$W.log"; then
      ok=0; echo "ERROR chunk=$c s=$s worker=$W $(date)" >> logs/errors.log
    fi
  done
  if [ $ok = 1 ]; then echo "$A $B $(date +%s)" > "done/$c"; else rmdir "claims/$c"; sleep 10; fi
  if grep -q SOLUTION logs/sol_*.log 2>/dev/null; then touch STOP; fi
  c=$((c+1))
done
