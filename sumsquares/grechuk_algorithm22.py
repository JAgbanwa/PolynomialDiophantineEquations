#!/usr/bin/env python3
# grechuk_search_fixed.py
#
# Pure Python implementation of the tangent/Pell construction used in the
# sums-of-two-squares paper.  This version avoids modern syntax such as
# dataclasses, builtin generic type hints, and future annotations, and it has
# a fallback for math.isqrt.  It should run on ordinary Python 3 installations.

from __future__ import print_function

import argparse
import sys
from collections import namedtuple

# Python 3.11+ limits conversion of very large integers to strings.
# Pell-generated solutions can be huge, so disable that limit when available.
try:
    sys.set_int_max_str_digits(0)
except AttributeError:
    pass

try:
    from math import isqrt as int_sqrt
except ImportError:  # Python < 3.8 fallback
    def int_sqrt(n):
        if n < 0:
            raise ValueError("square root not defined for negative integers")
        if n < 2:
            return n
        x = 1 << ((n.bit_length() + 1) // 2)
        while True:
            y = (x + n // x) // 2
            if y >= x:
                while (x + 1) * (x + 1) <= n:
                    x += 1
                while x * x > n:
                    x -= 1
                return x
            x = y


# ---------------------------------------------------------------------
# Basic arithmetic
# ---------------------------------------------------------------------

def is_square(n):
    """Return True iff n is a non-negative perfect square."""
    if n < 0:
        return False
    r = int_sqrt(n)
    return r * r == n


def signed_ordered_sumsq_reps(n):
    """
    Return all signed ordered pairs (p,q) with p^2 + q^2 = n.
    This is a direct search, fine for the u-values used in the paper.
    """
    if n < 0:
        return []
    out = set()
    limit = int_sqrt(n)
    for a in range(limit + 1):
        b2 = n - a * a
        b = int_sqrt(b2)
        if b * b == b2:
            for p0, q0 in ((a, b), (b, a)):
                ps = [0] if p0 == 0 else [p0, -p0]
                qs = [0] if q0 == 0 else [q0, -q0]
                for p in ps:
                    for q in qs:
                        out.add((p, q))
    return sorted(out)


def fundamental_pell_unit(D):
    """
    Fundamental positive solution (U,W) of U^2 - D W^2 = 1.
    Uses the continued-fraction algorithm.
    """
    if D <= 0:
        raise ValueError("D must be positive")
    a0 = int_sqrt(D)
    if a0 * a0 == D:
        raise ValueError("D must be nonsquare")

    m = 0
    d = 1
    a = a0
    p_nm2, p_nm1 = 0, 1
    q_nm2, q_nm1 = 1, 0

    while True:
        p = a * p_nm1 + p_nm2
        q = a * q_nm1 + q_nm2
        if p * p - D * q * q == 1:
            return p, q

        p_nm2, p_nm1 = p_nm1, p
        q_nm2, q_nm1 = q_nm1, q
        m = d * a - m
        d = (D - m * m) // d
        a = (a0 + m) // d


def pell_orbit(D, N, v0, x0, count):
    """
    Generate count solutions (X,V) of V^2 - D X^2 = N from one seed
    (x0,v0), by multiplying V + X*sqrt(D) by powers of the fundamental unit.

    The seed is yielded before computing the fundamental unit.  So --count 1
    is fast even when the fundamental unit is large.
    """
    if v0 * v0 - D * x0 * x0 != N:
        raise ValueError("Seed does not satisfy V^2 - D X^2 = N")

    if count <= 0:
        return

    V, X = v0, x0
    yield X, V

    if count == 1:
        return

    U, W = fundamental_pell_unit(D)  # U^2 - D W^2 = 1
    for _ in range(count - 1):
        V, X = V * U + D * X * W, V * W + X * U
        yield X, V


# ---------------------------------------------------------------------
# Special case R(t)=t^3+f, Q(X)=X^2
# ---------------------------------------------------------------------

def auxiliary_D_N_for_x6_plus_f(f, u):
    """
    For R(t)=t^3+f and Q(X)=X^2, the auxiliary equation is

        V^2 - D X^2 = N,

    with D = 4(u^3+f), N = -u(u^3-8f), and m = u^3+f.
    """
    m = u ** 3 + f
    D = 4 * m
    N = -u * (u ** 3 - 8 * f)
    return D, N, m


def tangent_representation_x6_plus_f(f, u, X, V_section):
    """
    Given a solution of the auxiliary equation, return A,B with

        A^2 + B^2 = X^6 + f.

    In the paper's sums-of-two-squares section, the auxiliary v is scaled by
    2 compared with the general quadratic-form formula, so we use
    v_general = V_section/2 here.
    """
    D, N, m = auxiliary_D_N_for_x6_plus_f(f, u)
    if V_section * V_section - D * X * X != N:
        raise ValueError("Not a solution of the auxiliary equation")
    if V_section % 2 != 0:
        raise ValueError("V_section must be even for this explicit formula")

    r = 3 * u * u
    den = 2 * m
    s = X * X - u

    reps = signed_ordered_sumsq_reps(m)
    for p, q in reps:
        for sign in (1, -1):
            v = sign * (V_section // 2)
            lam_num = r * p + v * (2 * q)
            mu_num = r * q - v * (2 * p)
            if lam_num % den == 0 and mu_num % den == 0:
                lam = lam_num // den
                mu = mu_num // den
                A = p + s * lam
                B = q + s * mu
                if A * A + B * B == X ** 6 + f:
                    return A, B

    raise ValueError("No representation of R(u) satisfied the congruences")


def convert_representation_to_original(e, f, X, A, B):
    """
    Convert A^2+B^2=X^6+f into a solution of

        y^2 + X^3*y + z^2 + e*z + (e^2-f)/4 = 0

    by matching A = X^3 + 2y and B = 2z + e, after possible sign changes
    and swapping A,B.
    """
    if (e * e - f) % 4 != 0:
        raise ValueError("The constant (e^2-f)/4 is not integral")

    tried = set()
    candidates = (
        (A, B), (A, -B), (-A, B), (-A, -B),
        (B, A), (B, -A), (-B, A), (-B, -A),
    )
    for C, D in candidates:
        if (C, D) in tried:
            continue
        tried.add((C, D))

        if (C - X ** 3) % 2 == 0 and (D - e) % 2 == 0:
            y = (C - X ** 3) // 2
            z = (D - e) // 2
            constant = (e * e - f) // 4
            if y * y + X ** 3 * y + z * z + e * z + constant == 0:
                return y, z, C, D

    raise ValueError("Could not match signs/parity to the target equation")


CubicShiftTarget = namedtuple(
    "CubicShiftTarget",
    "key equation f e u x0 v0",
)

TARGETS = {
    # Equation (2): y^2 + X^3*y + z^2 + 1 = 0.
    "eq2": CubicShiftTarget(
        "eq2",
        "y^2 + X^3*y + z^2 + 1 = 0",
        -4,
        0,
        162,
        22108343594783571,
        91171377945572295096,
    ),
    # Equation (14): y^2 + X^3*y + z^2 - 2 = 0.
    "eq14": CubicShiftTarget(
        "eq14",
        "y^2 + X^3*y + z^2 - 2 = 0",
        8,
        0,
        8,
        12,
        544,
    ),
    # Equation (15): y^2 + X^3*y + z^2 + z - 1 = 0.
    "eq15": CubicShiftTarget(
        "eq15",
        "y^2 + X^3*y + z^2 + z - 1 = 0",
        5,
        1,
        2,
        6,
        44,
    ),
    # Equation (16): y^2 + X^3*y + z^2 + z + 1 = 0.
    "eq16": CubicShiftTarget(
        "eq16",
        "y^2 + X^3*y + z^2 + z + 1 = 0",
        -3,
        1,
        2,
        2,
        4,
    ),
}


def solutions_for_cubic_shift_target(target, count):
    """Generate integer solutions for one of the TARGETS."""
    D, N, _m = auxiliary_D_N_for_x6_plus_f(target.f, target.u)

    for X, V in pell_orbit(D, N, target.v0, target.x0, count):
        A, B = tangent_representation_x6_plus_f(target.f, target.u, X, V)
        y, z, A_used, B_used = convert_representation_to_original(
            target.e, target.f, X, A, B
        )
        constant = (target.e * target.e - target.f) // 4
        check_value = y * y + X ** 3 * y + z * z + target.e * z + constant
        if check_value != 0:
            raise AssertionError("Internal verification failed")

        yield {
            "X": X,
            "y": y,
            "z": z,
            "A": A_used,
            "B": B_used,
            "aux_v": V,
            "check_value": check_value,
        }


def search_small_seeds(f, max_u, max_X, required_X_parity=None):
    """
    Search for small (u,X,V) satisfying the auxiliary equation and tangent
    congruences.  Useful for rediscovering the f=8,5,-3 examples.
    """
    hits = []
    for u in range(-max_u, max_u + 1):
        D, N, m = auxiliary_D_N_for_x6_plus_f(f, u)
        if m <= 0:
            continue
        if not signed_ordered_sumsq_reps(m):
            continue
        if D <= 0 or is_square(D) or N == 0:
            continue

        for X in range(max_X + 1):
            if required_X_parity is not None and X % 2 != required_X_parity:
                continue
            V2 = D * X * X + N
            if not is_square(V2):
                continue
            V = int_sqrt(V2)
            try:
                tangent_representation_x6_plus_f(f, u, X, V)
            except ValueError:
                continue
            hits.append((u, X, V))
            break
    return hits


# ---------------------------------------------------------------------
# General tangent formula, for Algorithm 4.3-style examples
# ---------------------------------------------------------------------

def tangent_solution_general_form(
    Acoef,
    Bcoef,
    Ccoef,
    R,
    Rprime,
    Du,
    Q,
    u,
    p,
    q,
    x,
    v,
):
    """
    Proposition 4.1 formula for F(y,z)=A*y^2+B*y*z+C*z^2.
    The caller supplies a pair (x,v) satisfying the auxiliary equation and
    congruences.
    """
    Delta = Bcoef * Bcoef - 4 * Acoef * Ccoef
    if Delta == 0:
        raise ValueError("The form is degenerate")

    m = R(u)
    r = Rprime(u)
    if m != Acoef * p * p + Bcoef * p * q + Ccoef * q * q or m == 0:
        raise ValueError("Need m=R(u)=F(p,q) nonzero")

    T = Q(x)
    if 4 * m * Du(T) - r * r != -Delta * v * v:
        raise ValueError("The auxiliary equation is not satisfied")

    den = 2 * m
    lam_num = r * p + v * (Bcoef * p + 2 * Ccoef * q)
    mu_num = r * q - v * (2 * Acoef * p + Bcoef * q)

    if lam_num % den != 0 or mu_num % den != 0:
        raise ValueError("The congruences are not satisfied")

    lam = lam_num // den
    mu = mu_num // den
    s = T - u
    y = p + s * lam
    z = q + s * mu

    if Acoef * y * y + Bcoef * y * z + Ccoef * z * z != R(Q(x)):
        raise AssertionError("Internal verification failed")
    return y, z


def prop44_plus_solution(n):
    """Solution to 2y^2 + yz + 2z^2 = x^3 + 1."""
    v = 1 + 4 * n
    x = (15 * v * v - 7) // 8
    y, z = tangent_solution_general_form(
        2,
        1,
        2,
        R=lambda t: t ** 3 + 1,
        Rprime=lambda t: 3 * t * t,
        Du=lambda t: t + 2,
        Q=lambda t: t,
        u=1,
        p=1,
        q=0,
        x=x,
        v=v,
    )
    return x, y, z


def prop44_minus_solution(n):
    """Solution to 2y^2 + yz + 2z^2 = x^3 - 1."""
    v = 45 + 228 * n
    x = (5 * v * v + 819) // 456
    y, z = tangent_solution_general_form(
        2,
        1,
        2,
        R=lambda t: t ** 3 - 1,
        Rprime=lambda t: 3 * t * t,
        Du=lambda t: t + 14,
        Q=lambda t: t,
        u=7,
        p=3,
        q=12,
        x=x,
        v=v,
    )
    return x, y, z


def print_cubic_shift_solutions(target, count):
    print(target.equation)
    i = 0
    for sol in solutions_for_cubic_shift_target(target, count):
        i += 1
        print("\nsolution {0}".format(i))
        print("X = {0}".format(sol["X"]))
        print("y = {0}".format(sol["y"]))
        print("z = {0}".format(sol["z"]))
        print("check_value = {0}".format(sol["check_value"]))


def self_test():
    for key in ("eq14", "eq15", "eq16", "eq2"):
        target = TARGETS[key]
        sol = next(solutions_for_cubic_shift_target(target, 1))
        if sol["check_value"] != 0:
            raise AssertionError("self-test failed for {0}".format(key))
    for n in (0, 1):
        x, y, z = prop44_plus_solution(n)
        if 2 * y * y + y * z + 2 * z * z != x ** 3 + 1:
            raise AssertionError("self-test failed for prop44_plus")
        x, y, z = prop44_minus_solution(n)
        if 2 * y * y + y * z + 2 * z * z != x ** 3 - 1:
            raise AssertionError("self-test failed for prop44_minus")
    print("self-test passed")


# ---------------------------------------------------------------------
# Command-line interface
# ---------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Generate solutions from Grechuk-style tangent/Pell examples."
    )
    choices = sorted(TARGETS.keys()) + ["prop44_plus", "prop44_minus"]
    parser.add_argument("--target", choices=choices, default="eq2")
    parser.add_argument("--count", type=int, default=1)
    parser.add_argument("--search-f", type=int, default=None)
    parser.add_argument("--max-u", type=int, default=200)
    parser.add_argument("--max-X", type=int, default=10000)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        return

    if args.search_f is not None:
        print("Small seeds for f={0}:".format(args.search_f))
        print(search_small_seeds(args.search_f, args.max_u, args.max_X))
        return

    if args.target == "prop44_plus":
        for n in range(args.count):
            x, y, z = prop44_plus_solution(n)
            print("n={0}: x={1}, y={2}, z={3}".format(n, x, y, z))
        return

    if args.target == "prop44_minus":
        for n in range(args.count):
            x, y, z = prop44_minus_solution(n)
            print("n={0}: x={1}, y={2}, z={3}".format(n, x, y, z))
        return

    print_cubic_shift_solutions(TARGETS[args.target], args.count)


if __name__ == "__main__":
    main()
