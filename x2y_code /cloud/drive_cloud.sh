#!/bin/bash
# Cloud share of the interleaved layout shared with the Mac (see x2y_search/config.sh on the Mac):
# chunk c covers |a| in [BASE + c*WIDTH, BASE + (c+1)*WIDTH), both signs; the cloud does c % RES == 0.
# cloud_k.txt holds the next k (chunk c = RES*k). usage: ./drive_cloud.sh [BUDGET_SECONDS]
cd "$(dirname "$0")"
BASE=20000000000000; WIDTH=200000000000; RES=${RES:-6}
BUDGET=${1:-7000}; t0=$(date +%s)
[ -f cloud_k.txt ] || echo 0 > cloud_k.txt
while true; do
  BIN=./search14; [ -s bin.txt ] && BIN=$(head -1 bin.txt)
  k=$(cat cloud_k.txt); c=$((RES*k)); A=$((BASE + c*WIDTH)); B=$((A + WIDTH))
  for r in 3 33; do
    if [ $r = 3 ]; then s=1; else s=-1; fi
    lo=$(( (A - r + 35) / 36 )); hi=$(( (B - r + 35) / 36 ))
    if ! NBAD=nbad.txt $BIN $s $lo $hi >> sol11.log 2>> prog11.log; then echo "ERROR cloud chunk c=$c s=$s $(date)" >> prog11.log; exit 1; fi
  done
  echo "CLOUD_CHUNK_DONE c=$c |a| in [$A,$B) $(date)" >> prog11.log
  echo $((k+1)) > cloud_k.txt.tmp && mv cloud_k.txt.tmp cloud_k.txt
  if grep -q SOLUTION sol11.log; then echo "SOLUTION_FOUND $(date)" >> prog11.log; break; fi
  if [ $(( $(date +%s) - t0 )) -ge $BUDGET ]; then echo "BUDGET_STOP cloud next_k=$((k+1)) $(date)" >> prog11.log; break; fi
done
