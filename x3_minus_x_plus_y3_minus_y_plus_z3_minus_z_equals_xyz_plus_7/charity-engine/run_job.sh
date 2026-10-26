#!/bin/bash
# Charity Engine job for the complete search of  x^3 - x + y^3 - y + z^3 - z = xyz + 7.
#
# Which work units (WUs, see workunits.txt) a job runs -- first match wins:
#   run_job.sh 17 18 19             explicit WU ids (plain numbers or the 5-digit ids)
#   run_job.sh --range 100 8        8 consecutive WUs starting at 100
#   run_job.sh --list ids.txt       ids listed in a file (e.g. the "missing" list printed by merge_results.py)
#   run_job.sh                      job index from $JOB_INDEX (or $WU, $CE_JOB_INDEX, $SLURM_ARRAY_TASK_ID,
#                                   $AWS_BATCH_JOB_ARRAY_INDEX): runs WUs index*WU_PER_JOB ... +WU_PER_JOB-1
# Environment:
#   THREADS     threads per WU (default: all CPUs visible to the container)
#   WU_PER_JOB  WUs per job index in the no-argument mode (default 1)
#   MAX_HOURS   wall-clock budget; no new WU is started once it is nearly used up (default 7.5)
#   OUT         where result_*.txt / checkpoints go (default /data if writable, else the current directory)
#   K7DIR       where the binaries and workunits.txt live (default /opt/k7)
# Output, per WU: OUT/result_<id>.txt, and the same summary on stdout as lines starting with "K7RESULT".
# Exit code: 0 all requested WUs complete, 1 some incomplete (budget or error), 2 bad arguments, 3 self-test failed.
K7DIR=${K7DIR:-/opt/k7}
THREADS=${THREADS:-$(nproc 2>/dev/null || echo 1)}
MAX_HOURS=${MAX_HOURS:-7.5}
WU_PER_JOB=${WU_PER_JOB:-1}
if [ -z "${OUT:-}" ]; then if [ -d /data ] && [ -w /data ]; then OUT=/data; else OUT=$PWD; fi; fi
mkdir -p "$OUT" && cd "$OUT" || { echo "cannot use output directory $OUT" >&2; exit 2; }
WUFILE=$K7DIR/workunits.txt
T0=$(date +%s)

ids=()
if [ "${1:-}" = "--range" ]; then
  for ((i=$2; i<$2+$3; i++)); do ids+=("$i"); done
elif [ "${1:-}" = "--list" ]; then
  while read -r a _; do [ -n "$a" ] && [ "${a:0:1}" != "#" ] && ids+=("$a"); done < "$2"
elif [ $# -ge 1 ]; then
  ids=("$@")
else
  IDX=${JOB_INDEX:-${WU:-${CE_JOB_INDEX:-${SLURM_ARRAY_TASK_ID:-${AWS_BATCH_JOB_ARRAY_INDEX:-}}}}}
  [ -n "$IDX" ] || { echo "no work unit given: pass ids, --range, --list, or set JOB_INDEX" >&2; exit 2; }
  for ((i=IDX*WU_PER_JOB; i<(IDX+1)*WU_PER_JOB; i++)); do ids+=("$i"); done
fi

V=generic; grep -qw avx512ifma /proc/cpuinfo 2>/dev/null && [ -x "$K7DIR/k7_ifma" ] && V=ifma
BIN=$K7DIR/k7_$V; BIN41=$K7DIR/k7_41_$V

# Self-test (once per container, ~20 s): the known solution (-297301,-89201,329339) of the K=41 equation must be
# found 3 times, and a fixed K=7 slice must give an exact candidate count. Otherwise refuse to run.
if [ ! -f /tmp/k7_selftest_ok_$V ]; then
  D=$(mktemp -d)
  "$BIN41" -j "$THREADS" -T 997 -R 8 -a -40001 40000 -b 997 925000 0 400002 -p $D/p1 -s $D/s1 -l $D/l1 > $D/o1 2>&1
  "$BIN" -j "$THREADS" -T 2300001000 -b 2300001000 2300201000 1000000000000 9999999999999 -ub 18 -p $D/p2 -s $D/s2 -l $D/l2 > $D/o2 2>&1
  S1=$(grep -c SOLUTION $D/s1 2>/dev/null); C1=$(grep -o "candidates=[0-9]*" $D/o1 | head -1); C2=$(grep -o "candidates=[0-9]*" $D/o2 | head -1)
  rm -rf "$D"
  if [ "$S1" != 3 ] || [ "$C1" != candidates=310109 ] || [ "$C2" != candidates=24517097 ]; then
    echo "K7RESULT SELFTEST_FAILED build=$V sols=$S1 $C1 $C2"; exit 3; fi
  touch /tmp/k7_selftest_ok_$V
  echo "K7RESULT SELFTEST_OK build=$V threads=$THREADS"
fi

rc=0; last=0
for raw in "${ids[@]}"; do
  ID=$(printf "%05d" "$((10#$raw))" 2>/dev/null) || { echo "bad work unit id $raw" >&2; rc=1; continue; }
  ARGS=$(awk -v id="$ID" '$1==id{$1="";$2="";$3="";sub(/^ +/,"");print}' "$WUFILE")
  [ -n "$ARGS" ] || { echo "K7RESULT $ID STATUS UNKNOWN_WU"; rc=1; continue; }
  # stop starting new work units when the remaining budget is less than ~1.5x the last one
  el=$(( $(date +%s) - T0 ))
  if awk -v e="$el" -v l="$last" -v m="$MAX_HOURS" 'BEGIN{exit !(e + 1.5*l > m*3600)}'; then
    echo "K7RESULT $ID STATUS NOT_STARTED (time budget)"; rc=1; continue; fi
  s=$(date +%s)
  "$BIN" -j "$THREADS" -T 2300001000 $ARGS -p progress_$ID.txt -s solutions_$ID.txt -l log_$ID.txt > stdout_$ID.txt 2>&1
  RC=$?
  last=$(( $(date +%s) - s ))
  NU=$(grep -o "units=[0-9]*" log_$ID.txt | tail -1 | cut -d= -f2)
  TOT=$(awk '{k=$1" "$2" "$3" "$4" "$5; if(k in seen) next; seen[k]=1; n++;
         for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="cand")c+=a[2]; if(a[1]=="passed")p+=a[2]; if(a[1]=="passed2")p2+=a[2];
           if(a[1]=="sols")s+=a[2]; if(a[1]=="primes")q+=a[2]; if(a[1]=="ovf")o+=a[2]} }
         END{printf "units=%d candidates=%d passed=%d passed2=%d primes=%d overflow=%d solutions=%d", n,c,p,p2,q,o,s}' progress_$ID.txt 2>/dev/null)
  DONE=$(echo "$TOT" | grep -o "units=[0-9]*" | cut -d= -f2)
  ST=INCOMPLETE; [ "$RC" = 0 ] && [ -n "$NU" ] && [ "$DONE" = "$NU" ] && ST=COMPLETE
  [ "$ST" = COMPLETE ] || rc=1
  { echo "WU $ID"; echo "ARGS $ARGS"; echo "BUILD $V"; echo "STATUS $ST"; echo "TOTALS $TOT"; echo "SECONDS $last"
    grep -h "SOLUTION\|BUG" log_$ID.txt solutions_$ID.txt 2>/dev/null | sort -u; } > result_$ID.txt
  sed "s/^/K7RESULT $ID /" result_$ID.txt | grep -v "K7RESULT $ID WU "
done
exit $rc
