# Independent re-implementation (Python/sympy) of the search pipeline, for validating search10.
# usage: python3 check.py s J0 J1    -> prints counts and the list of (m,z) reaching the exact-sqrt stage
import sys, math
from sympy import factorint, primerange
from sympy.ntheory import sqrt_mod
s = int(sys.argv[1]); J0 = int(sys.argv[2]); J1 = int(sys.argv[3])
r = 3 if s == 1 else 33
import os
PR = list(primerange(5, int(os.environ.get("NPMAX","1500000"))))
QR19 = {(i*i) % 19 for i in range(1, 19)}
SQA = {(i*i) % 45045 for i in range(45045)}; SQB = {(i*i) % 7429 for i in range(7429)}
def leg(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1
kept = cand = alive = nsq = 0; out = []
for j in range(J0, J1):
    m = r + 36*j; a = s*m
    f = factorint(m//3)
    if any(not (p % 12 in (1, 11)) for p in f): continue
    t = abs(2*a - 1); ft = factorint(t)
    ok = True
    for p, e in ft.items():
        if p == 19:
            if e > 1: ok = False
        elif (p % 19) not in QR19: ok = False
    if not ok: continue
    N = 2*a**3 - 8*a**2 - 3
    D = -2*a*(2*a - 1)
    bad = False
    for p in PR:
        if N % p: continue
        if D % p == 0: continue
        if N % (p*p) == 0: continue
        if leg(D, p) == -1: bad = True; break
    if bad: continue
    kept += 1
    roots = sqrt_mod(3, 2*m, all_roots=True) or []
    for z in sorted(set(roots)):
        if z > m + 5: continue
        assert (z*z - 3) % (2*a) == 0
        k = (z*z - 3)//(2*a)
        B2 = (a - 2)**2 - (2*a - 1)*k - 7
        if B2 <= 0: continue
        cand += 1
        if B2 % 8 != 1: continue
        alive += 1
        if (B2 % 45045) not in SQA or (B2 % 7429) not in SQB: continue
        nsq += 1; out.append((m, z))
        b = math.isqrt(B2)
        if b*b == B2: print("SOLUTION", 2*a, b - a, z)
print(f"check s={s} j in [{J0},{J1}): kept={kept} cand={cand} alive={alive} sqrt={nsq}")
for m, z in out: print("CAND", s, m, z)
