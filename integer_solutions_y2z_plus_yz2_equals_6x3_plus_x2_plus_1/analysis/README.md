# Brauer–Manin analysis (why congruence/reciprocity arguments cannot work)

* `lines27.gp` (PARI/GP 2.17): computes the 27 lines of $X: y^2z+yz^2=6x^3+x^2w+w^3$ over their splitting field
  (degree 36), the intersection matrix, and generators of the Galois action on the lines. Run: `gp -q < lines27.gp > lines27.log`.
* `h1_pic.py` (Python + sympy): from that output, computes $H^1(G,\mathrm{Pic}\,\bar X)$ and $H^1(G,\mathrm{Pic}\,\bar U)$ for $U = X\setminus\{w=0\}$.
  Both are trivial, so $\mathrm{Br}_1(U)=\mathrm{Br}_0(U)$.
* The boundary curve $D:\ yz(y+z)=6x^3$ is isomorphic to $Y^2=X^3+576$ (rank 1, torsion $\mathbb Z/3$) with a single rational
  3-isogeny (PARI `ellisomat`), so $\mathrm{Hom}_G(D[n],\mathbb Z/n)=0$ for all $n$, giving $\mathrm{Br}(\bar U)^G=0$.
* Hence there is no Brauer–Manin obstruction to integral points; together with solvability modulo every integer, no
  local or reciprocity argument can prove that no solution exists.
