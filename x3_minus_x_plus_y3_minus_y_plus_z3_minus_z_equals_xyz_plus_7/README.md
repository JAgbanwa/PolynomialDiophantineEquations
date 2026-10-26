# Searching for integer solutions of  x³ − x + y³ − y + z³ − z = xyz + 7

**Status:** no integer solutions with |x + y| < 10¹¹ for the distinguished pair below, so in particular none with
max(|x|, |y|, |z|) < 5·10¹⁰. The range 10¹¹ ≤ |x + y| < 10¹³ is split into work units for distributed runs
(Charity Engine, a Mac, or a cloud VM). See [`results/COVERAGE.md`](results/COVERAGE.md) for exactly what has been covered.

## The reduction

1. **A distinguished pair.** Every solution modulo 20 has a pair among (x, y), (y, z), (x, z) whose sum is ≡ 2 (mod 10).
   Relabel so that d = x + y ≡ 2 (mod 10). Only these d are searched (a factor 10 saving).
2. **A divisor condition.** Put e = z + 3d. Then e divides N(d) = 26d³ − 2d + 7, and
   xy = e² − 9ed + 27d² − 1 − N(d)/e, so d² − 4xy = (x − y)² must be a perfect square.
   Equivalently, with x = a + c, y = c − a, z = b + 3c:  (b + 9c)(a² + b² + 26c² − 1) = 208c³ − 4c + 7.
3. **A size bound.** sign(e) = sign(d) and |e| ≤ 2.3|d| (+50 slack in the code). Writing c = d/2 and e = kc, a solution needs
   c²·f(k) + 1 − 4/k + 7/(kc) ≥ 0 with f(k) = 208/k − (k − 9)² − 26, and f(k) < −0.142 for every k ≥ 4.6.
   That rules out |e| > 2.3|d| for all |d| ≥ 8; the only smaller d ≡ 2 (mod 10) is d = 2, where N(2) = 211 is prime and
   e = 211 is impossible. `tools/check_lemmas.py` checks all of this.

So for each d the search enumerates the divisors e of N(d) with 0 < |e| ≤ 2.3|d| and the right sign, and tests one square.
Note that this covers solutions where x and y are much larger than d (small e makes |x − y| ≈ 2√(N/e)).

The equation is solvable modulo every prime power tested, so no congruence rules solutions out. Nearby constants behave
similarly: with 13, 23, 31, 33, 35, 47 or 53 in place of 7 there is no solution with |x + y| ≤ 10⁷ either, while 41 and 55
have solutions with coordinates of size about 3·10⁵ and 4·10⁴.

## The algorithm (`src/k7.c`, one C file, no dependencies)

* **A units: small-divisor sieve.** For every prime p ≤ T = 2.3·10⁹ the roots of N mod p are tabulated (112,173,086
  prime–root pairs, ≈ 0.9 GB). A segmented sieve over t (d = 10t + 2) collects, for each d, its prime factors up to T,
  and all divisors e ≤ 2.3|d| built from them are tested.
* **B units: large primes.** For primes q > T, the roots of N mod q are found with a Cantor–Zassenhaus root finder in
  Montgomery arithmetic (8 primes at a time with AVX-512 IFMA on x86, 4-way interleaved scalar code elsewhere). Then every
  d ≡ root (mod q) in range gives divisors e = m·q with small m (m ≤ 2.3|d|/q ≤ 10⁴). Since T² > 2.3|d|, no divisor has
  two prime factors above T.
* **Testing a candidate (d, e).** A 2-adic test and quadratic-character tests modulo all primes up to 67 discard almost
  every candidate cheaply. The rare survivors are tested exactly in 192-bit arithmetic (valid for |d| < 1.7·10¹³), and any
  solution is re-verified via the original equation modulo 2¹²⁸ before it is printed as a `SOLUTION` line.
* **Work units and checkpoints.** The job is cut into units, scheduled dynamically over threads in order of the smallest
  |d| they touch. Every finished unit is appended to `progress.txt` and skipped on restart, and the log reports
  "job complete for |d| < X".

## Validation

* Roots of N mod p agree with PARI/GP, including primes above 2³².
* With 7 replaced by 41 (`-DK=41`), the program finds the known solution (x, y, z) = (−297301, −89201, 329339) from all
  three of its pair sums, whether the work is split at T = 997 (sieve + large primes) or done by the sieve alone.
* Candidate counts are identical to those of earlier, independently written programs: 132,688,589 for |d| < 10⁸, and
  99,760,564 for one large-prime slice. At |d| ≈ 5·10¹² they also match an exact trial-division count in Python.
* The 192-bit exact test agrees with Python big integers on random cases with |d| up to 1.7·10¹³.
* Results are deterministic: a unit's totals are identical on every machine and build, so replicated runs check each other.

Run `bash tools/validate.sh` (about 1 minute), or `bash tools/validate.sh --full`.

## Running it

| where | how |
|---|---|
| **Charity Engine** | see [`charity-engine/README.md`](charity-engine/README.md): Docker image, `run_job.sh`, 656 work units, `merge_results.py` |
| **macOS** | double-click `mac/start_k7.command` (all cores, resumable); `mac/stop_k7.command` stops it |
| **AWS EC2** | in AWS CloudShell: upload `cloud/launch_k7.sh` + `cloud/k7_userdata.sh`, run `bash launch_k7.sh` (shows the plan and cost, asks before launching, the instance stops itself) |
| **Any Linux VM** (Google Cloud, Azure, …) | paste `cloud/cloud_startup.sh` as the VM's startup script; progress goes to the serial console |
| **By hand** | `cc -O3 -march=native -o k7 src/k7.c -lm -lpthread`, then e.g. `./k7 -j 8 -T 2300001000 -a 10000000000 10100000000` |

Command-line summary of `k7`: `-j threads`, `-T table bound`, `-a t0 t1` (sieve units for d = 10t + 2, t in [t0, t1)),
`-b q0 q1 D0 D1` (large primes q in (q0, q1] for D0 ≤ |d| ≤ D1), `-ua`/`-ub`/`-bu` (log₂ unit sizes), `-p/-s/-l`
(progress, solutions, log files), `-from X` (treat all units below |d| = X as done).

**Avoid running the same range in two places.** The Mac launcher and `cloud/` cover all of 10¹¹ ≤ |d| < 10¹³, and so do
the 656 Charity Engine work units. Pick one per range, or split, e.g. Charity Engine runs the B units and a Mac or a VM
runs the A units.

## Files

| path | what |
|---|---|
| `src/k7.c` | the search program |
| `charity-engine/` | `Dockerfile`, `run_job.sh`, `workunits.txt` (+ `make_workunits.py`), `merge_results.py`, README |
| `mac/` | `start_k7.command`, `stop_k7.command` |
| `cloud/` | `launch_k7.sh` (EC2 from CloudShell), `k7_userdata.sh`, `cloud_startup.sh`, `make_userdata.py` (regenerates both from `src/k7.c`) |
| `tools/` | `validate.sh`, `check_lemmas.py`, `verify_solution.py` (exact check of any `SOLUTION` line) |
| `results/COVERAGE.md` | completed ranges with candidate counts |
