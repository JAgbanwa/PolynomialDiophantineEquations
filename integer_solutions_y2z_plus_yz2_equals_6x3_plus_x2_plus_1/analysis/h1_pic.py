# Compute H^1(G, Pic Xbar) and H^1(G, Pic Ubar) for the cubic surface
#   X : y^2 z + y z^2 = 6x^3 + x^2 w + w^3,   U = X minus {w = 0}
# Input: run  `gp -q < lines27.gp > lines27.log`  first (writes lines_out.txt = [intersection matrix, Galois generators]).
import re, sympy as sp
from sympy.matrices.normalforms import hermite_normal_form, smith_normal_form
txt = open('lines27.log').read()
pm = re.search(r'perms (\[\[.*\]\])', txt).group(1)
gens = [tuple(int(t) - 1 for t in re.findall(r'\d+', g)) for g in re.findall(r'\[([\d, ]+)\]', pm)]
raw = open('lines_out.txt').read()
M = sp.Matrix([[int(t) for t in row.split(',')] for row in raw[2:raw.index(']')].split(';')])
B = hermite_normal_form(M.T)                     # basis of Pic Xbar inside Z^27 (columns), rank 7
BtBi = (B.T * B).inv()
def act(g):
    P = sp.zeros(27, 27)
    for i in range(27): P[g[i], i] = 1
    A = BtBi * B.T * P * B
    assert P * B == B * A
    return A
As = [act(g) for g in gens]
def H1(As, dim, n=36):   # |G| = 36 kills H^1;  H^1 = (M/n)^G / (M^G/n)
    K = sp.Matrix.vstack(*[A - sp.eye(dim) for A in As])
    D = smith_normal_form(K, domain=sp.ZZ)
    return [sp.gcd(D[i, i], n) for i in range(min(D.shape)) if D[i, i] != 0 and sp.gcd(D[i, i], n) != 1]
print('H^1(G, Pic Xbar) invariants:', H1(As, 7) or 'trivial')
h = BtBi * B.T * (M[:, 0] + M[:, 1] + M[:, 2])   # hyperplane class (tritangent plane x = theta w)
Q = sp.eye(7); Q[:, 0] = h; Qi = Q.inv()
Aq = [(Qi * A * Q)[1:, 1:] for A in As]
print('H^1(G, Pic Ubar) invariants:', H1(Aq, 6) or 'trivial')
