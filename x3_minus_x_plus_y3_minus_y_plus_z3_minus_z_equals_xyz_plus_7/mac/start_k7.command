#!/bin/bash
# macOS launcher (double-click): compiles ../src/k7.c, self-tests, then searches |x+y| in [1e11, 1e13) on all cores.
# Survives closing the window, keeps the Mac awake (caffeinate), resumes from progress.txt. Stop with stop_k7.command.
cd "$(dirname "$0")" || exit 1
NCPU=$(sysctl -n hw.ncpu)
echo "== k7 search ==  CPU: $(sysctl -n machdep.cpu.brand_string)  cores: $NCPU"
if pgrep -x k7 >/dev/null; then echo "k7 is already running (see log.txt)."; exit 0; fi
( clang -O3 -mcpu=native -o k7 ../src/k7.c -lm -lpthread 2>build.log || clang -O3 -o k7 ../src/k7.c -lm -lpthread 2>>build.log ) || { echo "COMPILE FAILED"; cat build.log; exit 1; }
clang -O3 -DK=41 -o /tmp/k7_41_selftest ../src/k7.c -lm -lpthread 2>>build.log || { echo "COMPILE FAILED (selftest)"; exit 1; }
rm -f /tmp/k7st_*.txt
/tmp/k7_41_selftest -j "$NCPU" -T 997 -R 8 -a -40001 40000 -b 997 925000 0 400002 -p /tmp/k7st_p.txt -s /tmp/k7st_s.txt -l /tmp/k7st_l.txt > /tmp/k7st_o.txt 2>&1
./k7 -j "$NCPU" -T 2300001000 -b 2300001000 2300201000 1000000000000 9999999999999 -ub 18 -p /tmp/k7st_p2.txt -s /tmp/k7st_s2.txt -l /tmp/k7st_l2.txt > /tmp/k7st_o2.txt 2>&1
S1=$(grep -c SOLUTION /tmp/k7st_s.txt); C1=$(grep -o "candidates=[0-9]*" /tmp/k7st_o.txt | head -1); C2=$(grep -o "candidates=[0-9]*" /tmp/k7st_o2.txt | head -1)
echo "self-test: K=41 solutions=$S1 $C1 (expect 3, 310109) | K=7 slice $C2 (expect 24517097)" | tee selftest_result.txt
[ "$S1" = 3 ] && [ "$C1" = candidates=310109 ] && [ "$C2" = candidates=24517097 ] || { echo "SELF-TEST FAILED - not starting"; exit 1; }
nohup caffeinate -is ./k7 -j "$NCPU" -T 2300001000 \
  -a 10000000000 1000000000000 -a -1000000000000 -10000000000 \
  -b 230000000100 23000000000100 100000000000 9999999999999 \
  -bu 24 -b 2300001000 230000000100 1000000000000 1999999999999 \
         -b 2300001000 230000000100 2000000000000 4999999999999 \
         -b 2300001000 230000000100 5000000000000 9999999999999 \
  -p progress.txt -s solutions.txt -l log.txt > stdout.txt 2>&1 &
disown; sleep 5
pgrep -x k7 >/dev/null && echo "RUNNING. Progress: mac/log.txt  Solutions: mac/solutions.txt  (you can close this window)" || { echo "did not start:"; cat stdout.txt; }
