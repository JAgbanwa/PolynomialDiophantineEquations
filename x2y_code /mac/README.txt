Search for integer solutions of   x^2*y + x*y^2 + x*z^2 + 2*x^2 - z^2 + 3 = 0
=========================================================================

START (one command, in Terminal):
    cd ~/output/x2y_search && bash run.sh
It compiles search_mac.c with clang, runs a self-test against independently computed counts,
and starts 8 background workers (they keep running if you close Terminal; caffeinate prevents
idle sleep while they run -- keep the Mac plugged in, it will run warm).

    bash status.sh     progress, and any SOLUTION found
    bash stop.sh       graceful stop (current chunks finish, at most a few minutes); restart with bash run.sh
    bash run.sh 6      run with 6 workers instead of 8 (e.g. to keep the machine responsive)

Progress is saved per chunk (done/), so stopping, rebooting or sleeping only loses the chunks in flight.

What is searched
----------------
x must be even; with x = 2a, y = b - a the equation becomes  2a*b^2 + (2a-1)*z^2 = 2a^3 - 8a^2 - 3.
Proven necessary conditions used: a = 3 (mod 36) (mod-8 argument plus Hilbert reciprocity for (x,3)),
every prime of a/3 is +-1 (mod 12), every prime of |2a-1| is 19 (once) or a square mod 19,
z^2 = 3 (mod 2a), b odd, and the N-sieve (p || N(a) with (-2a(2a-1)/p) = -1 is impossible).
For each admissible a all z in [0,|a|+5] with z^2 = 3 (mod 2a) are generated (sieve factorisation +
square roots + CRT) and b^2 = ((a-2)^2 - (2a-1)k - 7), k = (z^2-3)/(2a), is tested for squareness.

Layout: chunk c covers |a| in [BASE + c*WIDTH, BASE + (c+1)*WIDTH) for both signs (see config.sh).
|a| < 2e13 and the chunks with c % 6 == 0 are being done on the cloud machine; this Mac does the rest.

A solution line in logs/sol_*.log looks like:  SOLUTION x=... y=... z=... (a=... b=...)
(other solutions follow by y -> -x-y and z -> -z).  check.py is the independent Python re-implementation
used for validation:  python3 check.py s J0 J1   (needs sympy).
