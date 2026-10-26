#!/usr/bin/env python3
"""Exact check of SOLUTION lines (from any log/result file) with Python integers.
Usage: python3 verify_solution.py FILE...      or      python3 verify_solution.py x y z"""
import sys, re
def ok(x, y, z): return x**3 - x + y**3 - y + z**3 - z == x*y*z + 7
if len(sys.argv) == 4 and all(re.fullmatch(r'-?\d+', a) for a in sys.argv[1:]):
    x, y, z = map(int, sys.argv[1:]); print(x, y, z, "VALID" if ok(x, y, z) else "NOT a solution"); sys.exit(0)
n = 0
for fn in sys.argv[1:]:
    for l in open(fn, errors='replace'):
        m = re.search(r'x=(-?\d+) y=(-?\d+) z=(-?\d+)', l)
        if m and 'SOLUTION' in l:
            x, y, z = map(int, m.groups()); n += 1
            print(x, y, z, "VALID" if ok(x, y, z) else "NOT a solution (K differs or error)")
print(n, "SOLUTION line(s) checked")
