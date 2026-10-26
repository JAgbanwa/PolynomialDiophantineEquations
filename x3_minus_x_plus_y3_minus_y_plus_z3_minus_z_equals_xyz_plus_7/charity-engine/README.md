# Running the search on Charity Engine

The range 10¹¹ ≤ |x + y| < 10¹³ is cut into **656 independent work units** (`workunits.txt`), about 650 core-hours in
total on ordinary x86 cores. AVX-512 hosts are about 1.6× faster on the B units.

| type | count | memory | time on 1 core | what it does |
|---|---|---|---|---|
| A | 232 | ≈ 1.0 GB with 2 threads | ~1–1.5 h + ~2 min setup | sieve over a slice of d, with a 112M-entry prime/root table |
| B | 424 | < 50 MB | ~0.2–1.2 h | large primes q > 2.3·10⁹ for a slice of q |

All units fit the smallest instance type (2 vCPU, 2 GiB). With 2 threads each unit takes roughly half the times above,
so one job can run several units within the 8-hour job limit.

## 1. Build the image

From the folder above this one:

    docker build -f charity-engine/Dockerfile -t k7search .
    docker tag k7search <your-dockerhub-user>/k7search:1 && docker push <your-dockerhub-user>/k7search:1

The image compiles two builds: a generic x86-64-v2 one and an AVX-512 IFMA one. `run_job.sh` picks the right one on
each host.

## 2. Tell each job which work units to run

`run_job.sh` (the image's entry point) accepts, first match wins:

| arguments | runs |
|---|---|
| `17 18 19` | those work units |
| `--range 100 8` | 8 consecutive units starting at 100 |
| `--list ids.txt` | the ids in a file, e.g. the "missing" list from `merge_results.py` |
| *(none)* | `$JOB_INDEX` (or `$WU`, `$CE_JOB_INDEX`): units `JOB_INDEX·WU_PER_JOB … +WU_PER_JOB−1` |

Sensible job sizes, with an 8-hour limit and 2 vCPUs per job: **`--range N 8`** (8 units ≈ 4 h), i.e. 82 jobs
`--range 0 8`, `--range 8 8`, …, `--range 648 8`. If the platform provides a job index, use `WU_PER_JOB=8` and
indices 0–81 instead.

Environment knobs: `THREADS` (default: all CPUs of the container), `MAX_HOURS` (default 7.5; no new unit is started
when the budget is nearly used), `OUT` (default `/data`).

## 3. What a job does

1. **Self-test (~20 s).** It must find the known solution (−297301, −89201, 329339) of the K = 41 equation 3 times and
   reproduce an exact candidate count for a K = 7 slice. Otherwise it prints `K7RESULT SELFTEST_FAILED` and exits 3.
2. **Work units.** For each unit it writes `result_<id>.txt` with `STATUS COMPLETE` and a deterministic `TOTALS` line,
   and prints the same lines to stdout prefixed `K7RESULT <id>`. A found solution appears as a `SOLUTION x=… y=… z=…` line.
3. **Checkpoints.** `progress_<id>.txt` is updated every few minutes. Rerunning a unit in the same directory resumes it.

Exit code: 0 all units complete, 1 something incomplete (time budget or error), 3 self-test failed.

## 4. Collect and check

Put the returned files in one directory. `result_*.txt` files or plain job logs with `K7RESULT` lines both work. Then:

    python3 merge_results.py workunits.txt results/ --missing missing.txt

This reports complete/missing units, any disagreement between replicas of the same unit (totals are identical across
hosts), BUG lines, and solutions. Rerun what is missing with `run_job.sh --list missing.txt`.
Check any solution exactly with `python3 ../tools/verify_solution.py results/*`.

Replicating a sample of units, or all with quorum 2, verifies the volunteer hosts exactly, because the totals are
deterministic.
