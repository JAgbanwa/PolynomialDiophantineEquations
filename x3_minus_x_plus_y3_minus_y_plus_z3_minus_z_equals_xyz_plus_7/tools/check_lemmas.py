#!/usr/bin/env python3
"""Checks the two facts the search relies on, plus a small brute-force box.
1. Every solution modulo 20 has a pair (x,y), (y,z) or (x,z) with sum = 2 (mod 10).
2. With c = d/2, e = kc: a solution needs c^2 f(k) + 1 - 4/k + 7/(kc) >= 0, f(k) = 208/k - (k-9)^2 - 26.
   f < -0.142 for all k >= 4.6, so |e| <= 2.3|d| whenever |d| >= 8 (both signs); d = 2 is checked directly.
3. No solution with max(|x|,|y|,|z|) <= 60."""
K = 7
ok = all(any((a + b) % 10 == 2 for a, b in ((x, y), (y, z), (x, z)))
         for x in range(20) for y in range(20) for z in range(20)
         if (x**3 - x + y**3 - y + z**3 - z - x*y*z - K) % 20 == 0)
print("1. mod-20 pair lemma:", ok)
mx = max(208/k - (k - 9)**2 - 26 for k in [4.6 + i*1e-4 for i in range(3_000_000)])
print("2. max f(k) on [4.6, 304.6]:", round(mx, 4), "(f -> -infinity beyond)")
# d = 2: N(2) = 211 is prime, so e in {1, 211}; e = 211 gives a^2 = 1 - 202^2 - 25 < 0.
print("   d=2: N(2) =", 26*8 - 4 + 7, "-> only e = 1, 211; e = 211 impossible since a^2 =", 211//211 - (211 - 9)**2 - 26 + 1)
R = range(-60, 61)
sols = [(x, y, z) for x in R for y in R for z in R if x**3 - x + y**3 - y + z**3 - z - x*y*z == K]
print("3. solutions with max |coordinate| <= 60:", sols)
