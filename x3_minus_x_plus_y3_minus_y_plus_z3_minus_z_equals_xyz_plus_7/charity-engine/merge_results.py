#!/usr/bin/env python3
"""Check the results of the k7 work units: all complete, replicas agree, collect solutions.

Usage:  python3 merge_results.py workunits.txt RESULTS_DIR [--missing missing.txt]

Reads result_<id>.txt files and/or any job logs (*.txt, *.log, *.out) containing "K7RESULT" lines.
With --missing, writes the ids still to be run (feed it to:  run_job.sh --list missing.txt).
"""
import sys, os, re, collections
wufile, rdir = sys.argv[1], sys.argv[2]
missing_out = sys.argv[sys.argv.index('--missing') + 1] if '--missing' in sys.argv else None
wus = {}
for l in open(wufile):
    if l.startswith('#') or not l.strip(): continue
    p = l.split(None, 3); wus[p[0]] = p[3].strip()
records = collections.defaultdict(dict)       # (file, wu) -> fields
sols, bugs = set(), set()
for fn in sorted(os.listdir(rdir)):
    path = os.path.join(rdir, fn)
    if not os.path.isfile(path): continue
    if fn.startswith('result_'):
        cur = None
        for l in open(path, errors='replace'):
            k, _, v = l.rstrip('\n').partition(' ')
            if k == 'WU': cur = v
            elif cur and k in ('ARGS', 'BUILD', 'STATUS', 'TOTALS'): records[(fn, cur)][k] = v
            if 'SOLUTION' in l: sols.add(l.strip())
            if l.startswith('BUG'): bugs.add(l.strip())
    elif fn.endswith(('.txt', '.log', '.out')):
        for l in open(path, errors='replace'):
            m = re.match(r'.*?K7RESULT (\d{5}) (\w+) ?(.*)$', l.rstrip('\n'))
            if not m: continue
            wu, k, v = m.groups()
            if k in ('ARGS', 'BUILD', 'STATUS', 'TOTALS'): records[(fn, wu)][k] = v
            if 'SOLUTION' in l: sols.add(l.strip())
            if ' BUG ' in l: bugs.add(l.strip())
byw = collections.defaultdict(list)
for (fn, wu), d in records.items(): byw[wu].append(d)
complete = {w for w, rs in byw.items() if any(r.get('STATUS') == 'COMPLETE' and r.get('ARGS') == wus.get(w) for r in rs)}
missing = sorted(set(wus) - complete)
mismatch = [w for w, rs in byw.items() if len({r.get('TOTALS') for r in rs if r.get('STATUS') == 'COMPLETE'}) > 1]
tot = collections.Counter()
for w in complete:
    r = next(r for r in byw[w] if r.get('STATUS') == 'COMPLETE' and r.get('ARGS') == wus.get(w))
    for k, v in re.findall(r'(\w+)=(\d+)', r['TOTALS']): tot[k] += int(v)
print(f"work units: {len(wus)}   complete: {len(complete)}   missing/incomplete: {len(missing)}   replica mismatches: {len(mismatch)}")
print("totals over complete units:", dict(tot))
if mismatch: print("REPLICA MISMATCH (rerun these):", mismatch[:50])
if missing:
    print("missing (first 30):", missing[:30])
    if missing_out:
        open(missing_out, 'w').write('\n'.join(missing) + '\n'); print("wrote", missing_out)
print("BUG lines:", len(bugs)); [print("  ", b) for b in sorted(bugs)]
print("SOLUTIONS:", len(sols)); [print("  ", s) for s in sorted(sols)]
