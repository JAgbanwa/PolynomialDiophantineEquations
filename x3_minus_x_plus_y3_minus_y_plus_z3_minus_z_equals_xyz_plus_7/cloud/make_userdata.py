import gzip, base64, sys, re
# Generates k7_userdata.sh (EC2 user data) and cloud_startup.sh (generic VM startup script) from ../src/k7.c.
# Usage: python3 make_userdata.py [time_cap_minutes]
import os, re
here=os.path.dirname(os.path.abspath(__file__))
full=open(os.path.join(here,'..','src','k7.c')).read()
_m=re.sub(r'/\*.*?\*/', '', full, flags=re.S)
src='\n'.join(l.strip() for l in _m.split('\n') if l.strip())+'\n'      # comment-stripped copy (fits EC2's 16 KB user-data limit gzipped)
assert 'EOF_K7_SOURCE' not in src
JOB = ("-a 10000000000 1000000000000 -a -1000000000000 -10000000000 "
       "-b 230000000100 23000000000100 100000000000 9999999999999 "
       "-bu 24 -b 2300001000 230000000100 1000000000000 1999999999999 "
       "-b 2300001000 230000000100 2000000000000 4999999999999 "
       "-b 2300001000 230000000100 5000000000000 9999999999999")
def build(maxmin, job=JOB, dry=False):
    script = r'''#!/bin/bash
# k7 search worker: x^3-x+y^3-y+z^3-z = xyz+7, |x+y| in [1e11,1e13). Stops itself when done or at the time cap.
DRY=__DRY__
W=/opt/k7; [ "$DRY" = 1 ] && W=$PWD/k7run
mkdir -p $W && cd $W
say(){ local m="K7 $(date -u +%Y-%m-%dT%H:%M:%SZ) $*"; echo "$m" >> $W/console.log; [ "$DRY" = 1 ] && echo "$m" || { echo "$m" > /dev/ttyS0 2>/dev/null || echo "$m" > /dev/console; }; }
[ "$DRY" = 1 ] || shutdown -h +__MAXMIN__ "k7 time cap" >/dev/null 2>&1
say "boot cores=$(nproc) mem=$(free -g | awk '/Mem/{print $2}')G cap=__MAXMIN__min"
[ "$DRY" = 1 ] || { dnf install -y gcc >/dev/null 2>&1 || yum install -y gcc >/dev/null 2>&1; }
cat > k7.c << 'EOF_K7_SOURCE'
__SOURCE__EOF_K7_SOURCE
gcc -O3 -march=native -o k7 k7.c -lm -lpthread 2>build.log && gcc -O3 -march=native -DK=41 -o k7_41 k7.c -lm -lpthread 2>>build.log || { say "COMPILE FAILED: $(head -c 300 build.log)"; [ "$DRY" = 1 ] || shutdown -h now; exit 1; }
say "compiled: $(grep -o avx512ifma /proc/cpuinfo | head -1 || echo scalar)"
N=$(nproc)
./k7_41 -j $N -T 997 -R 8 -a -40001 40000 -b 997 925000 0 400002 -p st1_p.txt -s st1_s.txt -l st1_l.txt > st1.txt 2>&1
S1=$(grep -c SOLUTION st1_s.txt); C1=$(grep -o "candidates=[0-9]*" st1.txt | head -1)
./k7 -j $N -T 2300001000 -b 2300001000 2300201000 1000000000000 9999999999999 -ub 18 -p st2_p.txt -s st2_s.txt -l st2_l.txt > st2.txt 2>&1
C2=$(grep -o "candidates=[0-9]*" st2.txt | head -1)
say "selftest sols=$S1 $C1 | $C2 (expect 3 candidates=310109 | candidates=24517097)"
if [ "$S1" != 3 ] || [ "$C1" != candidates=310109 ] || [ "$C2" != candidates=24517097 ]; then say "SELFTEST FAILED"; [ "$DRY" = 1 ] || shutdown -h now; exit 1; fi
FROM=$(cat from.txt 2>/dev/null)
./k7 -j $N -T 2300001000 __JOB__ ${FROM:+-from $FROM} -p progress.txt -s solutions.txt -l log.txt > stdout.txt 2>&1 &
P=$!; say "search started pid=$P threads=$N"
seen=0
while kill -0 $P 2>/dev/null; do
  sleep __PERIOD__
  say "STATUS $(grep -E 'units done|root table' log.txt | tail -1)"
  n=$(grep -hc "SOLUTION\|BUG" log.txt 2>/dev/null); n=${n:-0}
  if [ "$n" -gt "$seen" ]; then grep -h "SOLUTION\|BUG" log.txt | tail -n +$((seen+1)) | while read l; do say "$l"; done; seen=$n; fi
done
say "FINAL $(grep -E 'ALL|units done' log.txt | tail -1)"
grep -h "SOLUTION\|BUG" log.txt solutions.txt 2>/dev/null | sort -u | while read l; do say "$l"; done
ns=$(grep -c SOLUTION solutions.txt 2>/dev/null); say "K7DONE solutions=${ns:-0}"
[ "$DRY" = 1 ] || { sleep 20; shutdown -h now; }
'''
    script = (script.replace('__SOURCE__', src).replace('__MAXMIN__', str(maxmin)).replace('__JOB__', job)
                    .replace('__DRY__', '1' if dry else '0').replace('__PERIOD__', '5' if dry else '300'))
    return script
if __name__=='__main__':
    maxmin=int(sys.argv[1]) if len(sys.argv)>1 else 480
    os.chdir(here)
    s=build(maxmin); open('k7_userdata.sh','w').write(s)                       # EC2 user data (launch_k7.sh gzips it)
    gz=gzip.compress(s.encode(),9)
    print("k7_userdata.sh:", len(s), "bytes;", len(gz), "gzipped (EC2 limit 16384)")
    g=s.replace(src, full)                                                     # same script with the commented source
    g=g.replace('{ dnf install -y gcc >/dev/null 2>&1 || yum install -y gcc >/dev/null 2>&1; }',
                '{ if command -v apt-get >/dev/null; then apt-get update -qq >/dev/null 2>&1; DEBIAN_FRONTEND=noninteractive apt-get install -y -qq gcc >/dev/null 2>&1; else dnf install -y gcc >/dev/null 2>&1 || yum install -y gcc >/dev/null 2>&1; fi; }')
    open('cloud_startup.sh','w').write(g)                                      # startup script for any Linux VM (GCE, Azure, EC2)
    print("cloud_startup.sh:", len(g), "bytes")
