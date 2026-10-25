# Search code for  x²y + xy² + xz² + 2x² − z² + 3 = 0

This is the code that found the solution

    x = −2450412151997178,  y = 2357619934960084 (or −x−y = 92792217037094),  z = ±467727250324161

It was found on 25 Oct 2026 at 10:03 CET by worker 2 of `mac/`, running on an Apple M1 Pro, in the
chunk |a| ∈ [1.2252·10¹⁵, 1.2254·10¹⁵) with a = x/2 < 0. The math and the algorithm are explained
in `x2y_solution.pdf`.

## Layout

| path | what it is |
|---|---|
| `mac/search_mac.c` | **The program that found the solution.** Portable C (no OpenMP or AVX2 needed) and single-threaded. Usage: `NBAD=nbad.txt ./search_mac s J0 J1 [S]`. It searches a = s·m, m = r + 36j, j ∈ [J0, J1), with r = 3 for s = +1 and r = 33 for s = −1. Any solution is printed as `SOLUTION x=… y=… z=…`. |
| `mac/run.sh` | One-command launcher: `bash run.sh [workers]`. It compiles with clang, runs the self-test, then starts N background workers under `caffeinate`. |
| `mac/worker.sh`, `mac/workers.sh` | Workers claim chunks of 2·10¹¹ in \|a\| (both signs) with an atomic `mkdir`. Progress is recorded per chunk in `done/`. A worker that finds a solution creates `STOP`. |
| `mac/config.sh` | Chunk layout: BASE = 2·10¹³, WIDTH = 2·10¹¹, RES = 6. Chunks with c % 6 == 0 were left to the cloud machine. |
| `mac/selftest.sh` | Compares the build against counts computed independently by `check.py`. |
| `mac/status.sh`, `mac/stop.sh` | Progress report, and a graceful stop. |
| `cloud/search14.c` | The same algorithm for x86 Linux, using OpenMP and AVX2 (`gcc -O3 -march=native -fopenmp search14.c -lm`). It covered \|a\| < 2·10¹³ and every sixth chunk above that. |
| `cloud/drive13.sh`, `cloud/drive_cloud.sh` | Sequential and interleaved drivers for the cloud machine. |
| `tools/make_nbad.py` | Builds `mac/nbad.txt` with PARI/GP (cypari2). Each line holds a prime p < 1.5·10⁶, a simple root θ of N(a) = 2a³ − 8a² − 3 mod p with (−2θ(2θ−1)/p) = −1, and its Hensel lift mod p². |
| `tools/check.py` | Independent Python/SymPy re-implementation of the whole pipeline, used for validation: `python3 check.py s J0 J1`. |
| `tools/verify.py` | Exact check of `SOLUTION` lines in a log file. |

## Reproducing the discovery directly

The solution has a = −1225206075998589, so m = 1225206075998589 = 33 + 36·34033502111071. Run:

    clang -O3 -o search_mac mac/search_mac.c -lm        # or gcc
    NBAD=mac/nbad.txt ./search_mac -1 34033502111000 34033502112000

It prints, within a second:

    SOLUTION x=-2450412151997178 y=2357619934960084 z=467727250324161 (a=-1225206075998589 b=1132413858961495) check(mod 2^128)=OK

## Proven restrictions the search relies on

With x = 2a and y = b − a, the equation becomes 2a·b² + (2a−1)·z² = 2a³ − 8a² − 3. Then:

- **mod 36:** a ≡ 3 (mod 36). This comes from a mod-8 argument combined with Hilbert reciprocity for the quaternion algebra (x, 3).
- **primes of a/3:** each is ≡ ±1 (mod 12).
- **primes of |2a−1|:** each is 19 (at most once) or a square mod 19.
- **z:** z² ≡ 3 (mod 2a).
- **b:** b is odd.
- **primes of N(a):** if p ∥ N(a) and (−2a(2a−1)/p) = −1, there is no solution.
