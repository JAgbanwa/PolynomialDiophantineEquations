# Integer solutions of  $y^2 z + y z^2 = 6x^3 + x^2 + 1$

**Question.** Does $yz(y+z) = 6x^3 + x^2 + 1$ have an integer solution?

**Status:** no solution with $|x| \le 10^{12}$ (complete); $10^{12} < |x| \le 10^{13}$ finishing (see `coverage/COVERAGE.md`).
The range $10^{13} < |x| \le 10^{14}$ is prepared for distributed volunteers (Charity Engine), see below.

## Proven facts (elementary)
* $x$ is odd: $yz(y+z)$ is always even, while $N(x)=6x^3+x^2+1 \equiv x^2+1 \pmod 2$.
* $3 \nmid x$: $N \equiv x^2+1 \not\equiv 0 \pmod 3$, so $3\nmid y,z,y+z$, hence $y\equiv z \pmod 3$ and $yz(y+z)\equiv 2z^3\equiv \pm2 \pmod 9$; $3\mid x$ gives $N\equiv 1 \pmod 9$.
* $x \bmod 7 \in\{0,1,4,5\}$: modulo 7, $yz(y+z)$ only takes the values $0,\pm1,\pm2$.
* The equation is solvable modulo every integer, so congruences alone cannot rule out solutions.
* `analysis/`: the projective cubic surface has 27 lines over a degree-36 field (Galois orbits 3,3,3,18); $H^1(G,\mathrm{Pic}\,\bar X)=H^1(G,\mathrm{Pic}\,\bar U)=0$, and the boundary curve $yz(y+z)=6x^3\cong Y^2=X^3+576$ has a single rational 3-isogeny, so there is no Brauer–Manin obstruction to integral points. Heuristically about $0.035\ln X$ solution orbits are expected with $|x|\le X$, so solutions may be very large.

## Search algorithm (Booker-style sieve, `src/ysearch5.c`)
Put $w=-(y+z)$, so $y+z+w=0$, $yzw=-N(x)$, and the equation is symmetric in $(y,z,w)$.
Choose $w$ of least absolute value and let $d=|w|$. Then
1. $2d^3\le |N(x)|$, hence $d \le 1.44225\,|x|$ and $|x| \ge 0.69\,d$;
2. $\operatorname{sign}(w)=\operatorname{sign}(N(x))=\operatorname{sign}(x)$;
3. $d \mid N(x)$, i.e. $x$ is congruent to a root of $N$ modulo $d$;
4. $\Delta = d^2 + 4|N(x)|/d = (y-z)^2$ is a perfect square with $y-z\equiv d \pmod 2$.

Conversely every such triple gives a solution. The program enumerates all $d\le 1.44225\,X$ with the roots of $N$ mod $d$
(smooth $d$ by depth-first search; $d=P\cdot m$ with a large prime $P$ via a Cardano + Lucas-sequence root finder),
walks the progressions $x\equiv r \pmod d$, removes candidates by necessary congruences (bitmask sieves mod 64, 27, 7, 5, ..., 53),
and tests survivors exactly in 256-bit arithmetic. Solutions are printed as `SOL x=... y=... z=...`; a finished piece prints `DONE ... sols=<count>`.

Usage: `ysearch5 K UMIN UMAX THREADS [LTH=2048] [WID NW]` searches $yz(y+z)=6x^3+x^2+K$ for $UMIN\le|x|\le UMAX$ ($UMIN\ge 4$), piece `WID` of `NW`.
The `NW` pieces are disjoint and together cover the whole range.

## Validation
`bash validate/validate.sh` compares the sieve with brute force on $yz(y+z)=6x^3+x^2+K$ for $K\in\{2,3,5,7,18,25\}$ and $4\le|x|\le 3000$
(equations that do have solutions: 1, 5, 37, 2, 23, 30 orbits), plus a 3-way work-splitting check. All match exactly.
The 256-bit exact test was checked against Python big integers for $|x|$ up to $2\cdot10^{16}$.

## Run one piece yourself
```bash
bash run_piece.sh 10000000000000 100000000000000 7 48     # piece 7 of 48 of 1e13 < |x| <= 1e14
```

## Charity Engine: range $10^{13} < |x| \le 10^{14}$
Total work is about 3,400 core-hours, split into 48 pieces (about 70 core-hours each). One job = one piece.
* App: `docker:gcc`
* Command line for piece W of 48:
  `bash -c "curl -fsSL https://raw.githubusercontent.com/JAgbanwa/PolynomialDiophantineEquations/main/integer_solutions_y2z_plus_yz2_equals_6x3_plus_x2_plus_1/ce_job.sh -o ce_job.sh && bash ce_job.sh 10000000000000 100000000000000 W 48"`
  All 48 lines: `charity_engine/commands_1e13_1e14_48pieces.txt` (a 480-piece variant is also provided).
* Each job ends with one line `PIECE W/48 ... : DONE ... sols=0`. Any `SOL x=... y=... z=...` line is a solution.
* Memory about 1 GB; the job uses all cores of the instance.

A range is solution-free only after all of its pieces report `DONE`.
