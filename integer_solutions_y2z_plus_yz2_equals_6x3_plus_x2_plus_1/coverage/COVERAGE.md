# Search coverage for  y^2 z + y z^2 = 6x^3 + x^2 + 1

| range of \|x\| | method | status |
|---|---|---|
| 0 … 1e8 | independent check: factor N(x) with PARI, test every divisor s=y+z (s^2-4N/s square) | done, no solution |
| 4 … 1e9 | `ysearch` (single run, 8 threads, Apple M-series) | done, sols=0 |
| 1e9 … 1e11 | `ysearch` (single run, 2621 s, 8 threads) | done, sols=0 |
| 1e11 … 1e12 | `ysearch4` (single run, 16189 s, 8 threads) | done, sols=0 |
| 1e12 … 1e13 | `ysearch5`, 24 pieces (Modal 64-CPU containers + local Mac) | 19/24 pieces done, all sols=0; pending: [14, 15, 16, 17, 18] |
| 1e13 … 1e14 | `ysearch5`, 48 pieces — Charity Engine | to do |

Each run/piece ends with a line `DONE K=1 UMIN=… UMAX=… sols=0`; a solution would be printed as `SOL x=… y=… z=…`.

## 1e12 … 1e13, piece log (`DONE` lines)
| piece | where | DONE line |
|---|---|---|
| 0/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=1018.9` |
| 1/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=731.0` |
| 2/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=768.8` |
| 3/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=738.6` |
| 4/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=746.3` |
| 5/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=758.8` |
| 6/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=750.5` |
| 7/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=765.9` |
| 8/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=756.4` |
| 9/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=767.1` |
| 10/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=734.8` |
| 11/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=739.7` |
| 12/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=752.3` |
| 13/24 | Modal 64-CPU | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=746.9` |
| 14/24 | — | pending |
| 15/24 | — | pending |
| 16/24 | — | pending |
| 17/24 | — | pending |
| 18/24 | — | pending |
| 19/24 | local Mac 8 threads | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=6478.9` |
| 20/24 | local Mac 8 threads | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=6369.6` |
| 21/24 | local Mac 8 threads | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=6015.8` |
| 22/24 | local Mac 8 threads | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=6039.1` |
| 23/24 | local Mac 8 threads | `DONE K=1 UMIN=1000000000000 UMAX=10000000000000 sols=0 time=6005.6` |
