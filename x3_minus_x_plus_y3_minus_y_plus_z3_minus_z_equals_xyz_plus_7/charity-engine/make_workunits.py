# Work units for |d| = |x+y| in [1e11, 1e13) (d == 2 mod 10). Target ~1 core-hour each on a typical x86 core.
import math
T = 2300001000
WU = []
# A: small-divisor sieve, t-ranges of 2^33 (d = 10t+2), sub-units of 2^22 for checkpoints. ~1-1.5 h + ~2 min table build. RAM ~1.5-2 GB.
step = 1 << 33
for lo, hi in [(10**10, 10**12), (-10**12, -10**10)]:
    t = lo
    while t < hi:
        t1 = min(t + step, hi); WU.append(("A", f"-a {t} {t1} -ua 22", 1.2)); t = t1
# B1: large primes q in (2.3e11, 2.3e13] for 1e11 <= |d| < 1e13; q-ranges of 2^36 (~0.8-1.8 h), sub-units 2^28. RAM < 50 MB.
q, qend, w = 230000000100, 23000000000100, 1 << 36
while q < qend:
    q1 = min(q + w, qend); est = (q1 - q) / math.log((q + q1) / 2) * 1.3e-6 / 3600
    WU.append(("B", f"-b {q} {q1} 100000000000 9999999999999 -ub 28", est)); q = q1
# B2: large primes q in (2.3e9, 2.3e11] for |d| in [1e12, 1e13), three d-bands; cost per prime ~0.6 ms*(2.3e9/q)*band_fraction.
for (D0, D1, frac) in [(10**12, 2*10**12 - 1, 1/9), (2*10**12, 5*10**12 - 1, 3/9), (5*10**12, 10**13 - 1, 5/9)]:
    q = 2300001000; qend = 230000000100
    while q < qend:
        # choose width so that estimated cost ~ 1 core-hour
        per_prime = 0.6e-3 * (2.3e9 / q) * frac + 1.3e-6
        dens = 1 / math.log(q)
        w = int(3600 / (per_prime * dens)); w = max(1 << 22, min(w, 1 << 36))
        w = (w >> 22) << 22
        q1 = min(q + w, qend); est = (q1 - q) * dens * per_prime / 3600
        WU.append(("B", f"-bu 22 -b {q} {q1} {D0} {D1}", est)); q = q1
with open("workunits.txt", "w") as f:
    f.write("# id type est_core_hours k7_arguments   (all with -T 2300001000; see run_wu.sh)\n")
    for i, (ty, args, est) in enumerate(WU):
        f.write(f"{i:05d} {ty} {est:.2f} {args}\n")
tot = sum(e for _, _, e in WU)
print(len(WU), "work units;", sum(1 for t,_,_ in WU if t=="A"), "A,", sum(1 for t,_,_ in WU if t=="B"), "B; est total core-hours ~", round(tot))
print("max est per WU:", round(max(e for _,_,e in WU),2), " min:", round(min(e for _,_,e in WU),3))
