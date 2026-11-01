# Compare C output (SOL lines) with the brute-force reference; every C solution is re-verified exactly.
import sys, re
K = int(sys.argv[3])
C = set()
for l in open(sys.argv[1]):
    m = re.match(r"SOL x=(-?\d+) y=(-?\d+) z=(-?\d+)", l)
    if m:
        x, y, z = map(int, m.groups())
        assert y * z * (y + z) == 6 * x**3 + x * x + K, l
        C.add((x,) + tuple(sorted([y, z, -(y + z)])))
R = set(tuple(map(int, l.split())) for l in open(sys.argv[2]))
ok = C == R
print(f"K={K}: C={len(C)} ref={len(R)} missing={sorted(R - C)[:3]} extra={sorted(C - R)[:3]} -> {'OK' if ok else 'MISMATCH'}")
sys.exit(0 if ok else 1)
