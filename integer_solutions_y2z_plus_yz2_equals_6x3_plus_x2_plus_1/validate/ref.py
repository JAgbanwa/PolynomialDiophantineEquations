# Brute-force reference: all (x,y,z) with lo<=|x|<=hi and y z (y+z) = 6x^3 + x^2 + K,
# via the divisor reduction s=y+z | N, s^2 - 4N/s = (y-z)^2.  Prints orbits (x, sorted(y,z,-(y+z))).
import sys
from math import isqrt
from sympy import divisors
K, lo, hi = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
orbs = set()
for u in range(lo, hi + 1):
    for x in (u, -u):
        N = 6 * x**3 + x * x + K
        if N == 0:
            continue
        for d in divisors(abs(N)):
            for s in (d, -d):
                D = s * s - 4 * (N // s)
                if D >= 0:
                    q = isqrt(D)
                    if q * q == D and (s + q) % 2 == 0:
                        y, z = (s + q) // 2, (s - q) // 2
                        orbs.add((x,) + tuple(sorted([y, z, -(y + z)])))
for o in sorted(orbs):
    print(*o)
