#!/bin/bash
# One-command launcher:   cd ~/output/x2y_search && bash run.sh        (optional argument: number of workers, default 8)
# Builds the searcher, runs a self-test against known counts, then starts the workers in the background
# (they keep running after you close Terminal; caffeinate keeps the Mac from idle-sleeping while they run).
cd "$(dirname "$0")" || exit 1
chmod +x *.sh 2>/dev/null
NW=${1:-8}
if [ ! -x ./search_mac ] || [ search_mac.c -nt search_mac ]; then
  echo "Compiling search_mac ..."
  clang -O3 -mcpu=apple-m1 -Wno-unknown-pragmas -o search_mac search_mac.c -lm 2> build.log \
   || clang -O3 -Wno-unknown-pragmas -o search_mac search_mac.c -lm 2>> build.log \
   || cc -O3 -o search_mac search_mac.c -lm 2>> build.log \
   || { echo "Compilation failed, see build.log"; exit 1; }
fi
bash selftest.sh || { echo "SELF-TEST FAILED -- not starting (see selftest.log)"; exit 1; }
if pgrep -f "x2y_search_worker" >/dev/null 2>&1; then echo "Workers already running (bash status.sh to see progress)."; exit 0; fi
rm -f STOP
mkdir -p claims done logs
# drop claims of chunks that were interrupted before finishing (no workers are running now)
for d in claims/*; do [ -e "$d" ] || continue; n=$(basename "$d"); [ -f "done/$n" ] || rmdir "$d"; done
nohup caffeinate -i bash workers.sh "$NW" > logs/workers.out 2>&1 &
echo "Started $NW workers in the background.   Progress: bash status.sh    Stop: bash stop.sh"
