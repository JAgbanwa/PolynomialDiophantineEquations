# Exact verification of reported solutions:  x^2 y + x y^2 + x z^2 + 2 x^2 - z^2 + 3 = 0
import re, sys
fn = sys.argv[1] if len(sys.argv) > 1 else 'sol10.log'
for line in open(fn):
    mm = re.search(r'SOLUTION x=(-?\d+) y=(-?\d+) z=(-?\d+)', line)
    if not mm: continue
    x, y, z = map(int, mm.groups())
    v = x*x*y + x*y*y + x*z*z + 2*x*x - z*z + 3
    print(f"x={x} y={y} z={z}  value={v}  {'VALID' if v == 0 else 'INVALID'}")
