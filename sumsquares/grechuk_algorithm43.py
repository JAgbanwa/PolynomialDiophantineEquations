#!/usr/bin/env python3
"""
grechuk_algorithm43.py

Pure-Python implementation of Algorithm 4.3 from Grechuk--Agbanwa,
"On the polynomial values represented by quadratic forms".

The algorithm tries to prove and exhibit infinitely many integer solutions of

    F(y,z) = R(Q(x)),

where

    F(y,z) = A*y^2 + B*y*z + C*z^2

is a non-degenerate integral binary quadratic form, and R,Q are univariate
integer polynomials with degree pairs (3,1), (4,1), or (3,2).

The code implements:
  * the Taylor quotient D_u(t), defined by
        R(t) = R(u) + R'(u)(t-u) + (t-u)^2 D_u(t);
  * the auxiliary equation
        4*m*D_u(Q(x)) - r^2 = -Delta*v^2,
    where m=R(u)=F(p,q), r=R'(u), Delta=B^2-4AC;
  * the congruences
        r*p + v*(B*p+2*C*q)       == 0 mod 2|m|,
        r*q - v*(2*A*p+B*q)       == 0 mod 2|m|;
  * the construction
        y = p + (Q(x)-u)*(r*p + v*(B*p+2*C*q))/(2m),
        z = q + (Q(x)-u)*(r*q - v*(2*A*p+B*q))/(2m).

Usage examples:

    # With no arguments the script now runs both Proposition 4.4 examples.
    python3 grechuk_algorithm43_v2.py

    python3 grechuk_algorithm43_v2.py --example prop44_plus --count 5
    python3 grechuk_algorithm43_v2.py --example prop44_minus --count 5
    python3 grechuk_algorithm43_v2.py --demo
    python3 grechuk_algorithm43_v2.py --self-test

Custom example, using coefficient lists from low degree to high degree:

    # R(t)=t^3+1, Q(x)=x, F=2y^2+yz+2z^2
    python3 grechuk_algorithm43_v2.py --A 2 --B 1 --C 2 --R 1,0,0,1 --Q 0,1 --count 5

Manual seed:

    python3 grechuk_algorithm43_v2.py --A 2 --B 1 --C 2 --R 1,0,0,1 --Q 0,1 \
        --u 1 --p 1 --q 0 --count 5

This script is deliberately dependency-free: it uses only the Python standard
library.
"""

from __future__ import print_function

import argparse
import math
import sys

# Python 3.11+ limits conversion of huge integers to strings by default.
# Algorithm 4.3 can generate very large Pell-type solutions, so disable the
# safety limit for this mathematical script. Printed output is still abbreviated
# by --max-print-digits unless set to 0.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


# ---------------------------------------------------------------------------
# Basic integer helpers
# ---------------------------------------------------------------------------

try:
    _isqrt = math.isqrt
except AttributeError:  # Python < 3.8 fallback
    def _isqrt(n):
        if n < 0:
            raise ValueError("isqrt() argument must be nonnegative")
        x = int(math.sqrt(n))
        while (x + 1) * (x + 1) <= n:
            x += 1
        while x * x > n:
            x -= 1
        return x


def is_square(n):
    """Return True iff n is a nonnegative perfect square."""
    if n < 0:
        return False
    r = _isqrt(n)
    return r * r == n


def sqrt_if_square(n):
    """Return sqrt(n) if n is a square, otherwise None."""
    if n < 0:
        return None
    r = _isqrt(n)
    if r * r == n:
        return r
    return None


def gcd(a, b):
    return math.gcd(int(a), int(b))


def lcm(a, b):
    a = abs(int(a))
    b = abs(int(b))
    if a == 0 or b == 0:
        return 0
    return a // gcd(a, b) * b


def ordered_range(bound):
    """Yield 0, 1, -1, 2, -2, ..., bound, -bound."""
    yield 0
    for n in range(1, bound + 1):
        yield n
        yield -n


def divisible(num, den):
    if den == 0:
        return False
    return num % den == 0


# ---------------------------------------------------------------------------
# Polynomial arithmetic, coefficients in increasing degree order.
# Example: 1 + 0*t + 0*t^2 + t^3 is [1,0,0,1].
# ---------------------------------------------------------------------------


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    if not p:
        return [0]
    return p


def poly_degree(p):
    p = trim(p)
    if len(p) == 1 and p[0] == 0:
        return -1
    return len(p) - 1


def poly_add(p, q):
    n = max(len(p), len(q))
    out = []
    for i in range(n):
        out.append((p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0))
    return trim(out)


def poly_sub(p, q):
    n = max(len(p), len(q))
    out = []
    for i in range(n):
        out.append((p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0))
    return trim(out)


def poly_scalar_mul(k, p):
    return trim([k * c for c in p])


def poly_mul(p, q):
    if p == [0] or q == [0]:
        return [0]
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(out)


def poly_pow(p, n):
    if n < 0:
        raise ValueError("negative polynomial power")
    out = [1]
    base = trim(p)
    while n:
        if n & 1:
            out = poly_mul(out, base)
        base = poly_mul(base, base)
        n >>= 1
    return out


def poly_eval(p, x):
    val = 0
    for c in reversed(p):
        val = val * x + c
    return val


def poly_derivative(p):
    if len(p) <= 1:
        return [0]
    return trim([i * p[i] for i in range(1, len(p))])


def poly_compose(p, q):
    """Return p(q(x))."""
    out = [0]
    power = [1]
    for coeff in p:
        out = poly_add(out, poly_scalar_mul(coeff, power))
        power = poly_mul(power, q)
    return trim(out)


def poly_div_exact_by_monic(p, q):
    """Exact division p/q, where q is monic. Raises ValueError if not exact."""
    p = trim(p)
    q = trim(q)
    if q == [0]:
        raise ZeroDivisionError("polynomial division by zero")
    if q[-1] != 1:
        raise ValueError("divisor must be monic")
    if poly_degree(p) < poly_degree(q):
        if p == [0]:
            return [0]
        raise ValueError("division is not exact: degree smaller than divisor")

    rem = list(p)
    out = [0] * (poly_degree(p) - poly_degree(q) + 1)
    dq = poly_degree(q)
    while poly_degree(rem) >= dq and rem != [0]:
        coeff = rem[-1]  # q is monic
        shift = poly_degree(rem) - dq
        out[shift] += coeff
        subtract = [0] * shift + [coeff * c for c in q]
        rem = poly_sub(rem, subtract)
    if rem != [0]:
        raise ValueError("division is not exact; remainder = %s" % rem)
    return trim(out)


def poly_to_string(p, var):
    p = trim(p)
    if p == [0]:
        return "0"
    terms = []
    for i, c in enumerate(p):
        if c == 0:
            continue
        sign = "-" if c < 0 else "+"
        a = abs(c)
        if i == 0:
            body = str(a)
        elif i == 1:
            body = var if a == 1 else "%s*%s" % (a, var)
        else:
            body = "%s^%d" % (var, i) if a == 1 else "%s*%s^%d" % (a, var, i)
        terms.append((sign, body))
    first_sign, first_body = terms[0]
    s = ("-" if first_sign == "-" else "") + first_body
    for sign, body in terms[1:]:
        s += " %s %s" % (sign, body)
    return s


def parse_poly(text):
    """Parse comma-separated integer coefficients in increasing degree order."""
    try:
        coeffs = [int(part.strip()) for part in text.split(",") if part.strip() != ""]
    except Exception:
        raise argparse.ArgumentTypeError("polynomial must be comma-separated integers, e.g. 1,0,0,1")
    if not coeffs:
        raise argparse.ArgumentTypeError("empty polynomial")
    return trim(coeffs)


# ---------------------------------------------------------------------------
# Algorithm 4.3 context and formulas
# ---------------------------------------------------------------------------


class Context(object):
    pass


def F_value(A, B, C, y, z):
    return A * y * y + B * y * z + C * z * z


def D_u_polynomial(R, u):
    """Compute D_u(t) from R(t)=R(u)+R'(u)(t-u)+(t-u)^2 D_u(t)."""
    Ru = poly_eval(R, u)
    Rprime = poly_derivative(R)
    r = poly_eval(Rprime, u)
    t_minus_u = [-u, 1]
    numerator = poly_sub(poly_sub(R, [Ru]), poly_scalar_mul(r, t_minus_u))
    denominator = poly_mul(t_minus_u, t_minus_u)  # monic
    return poly_div_exact_by_monic(numerator, denominator)


def build_context(A, B, C, R, Q, u, p, q):
    Delta = B * B - 4 * A * C
    if Delta == 0:
        raise ValueError("F is degenerate: Delta = B^2 - 4AC = 0")

    m = poly_eval(R, u)
    if m == 0:
        raise ValueError("R(u) must be nonzero")
    fpq = F_value(A, B, C, p, q)
    if fpq != m:
        raise ValueError("seed mismatch: R(u)=%s but F(p,q)=%s" % (m, fpq))

    Rprime = poly_derivative(R)
    r = poly_eval(Rprime, u)
    Du = D_u_polynomial(R, u)
    DuQ = poly_compose(Du, Q)
    left_poly = poly_sub(poly_scalar_mul(4 * m, DuQ), [r * r])
    left_poly = trim(left_poly)
    if poly_degree(left_poly) > 2:
        raise ValueError("auxiliary left side has degree %d, expected at most 2" % poly_degree(left_poly))

    c = left_poly[0] if len(left_poly) > 0 else 0
    b = left_poly[1] if len(left_poly) > 1 else 0
    a = left_poly[2] if len(left_poly) > 2 else 0
    D = -Delta

    ctx = Context()
    ctx.A = A
    ctx.B = B
    ctx.C = C
    ctx.Delta = Delta
    ctx.D = D
    ctx.R = trim(R)
    ctx.Q = trim(Q)
    ctx.u = u
    ctx.p = p
    ctx.q = q
    ctx.m = m
    ctx.r = r
    ctx.Du = Du
    ctx.DuQ = DuQ
    ctx.left_poly = left_poly
    ctx.a = a
    ctx.b = b
    ctx.c = c
    ctx.seed = None
    return ctx


def congruence_values(ctx, v):
    A, B, C = ctx.A, ctx.B, ctx.C
    p, q, r = ctx.p, ctx.q, ctx.r
    first = r * p + v * (B * p + 2 * C * q)
    second = r * q - v * (2 * A * p + B * q)
    return first, second


def congruences_ok(ctx, v):
    mod = 2 * abs(ctx.m)
    first, second = congruence_values(ctx, v)
    return first % mod == 0 and second % mod == 0


def aux_lhs(ctx, x):
    return ctx.a * x * x + ctx.b * x + ctx.c


def aux_ok(ctx, x, v):
    return aux_lhs(ctx, x) == ctx.D * v * v and congruences_ok(ctx, v)


def proposition_42_conditions_without_seed(ctx):
    a, b, c, D = ctx.a, ctx.b, ctx.c, ctx.D
    cond_a = (a == 0) or (a * D > 0 and not is_square(a * D))
    cond_b = (b * b - 4 * a * c != 0)
    return cond_a, cond_b


def proposition_42_conditions(ctx):
    cond_a, cond_b = proposition_42_conditions_without_seed(ctx)
    cond_c = ctx.seed is not None and aux_ok(ctx, ctx.seed[0], ctx.seed[1])
    return cond_a, cond_b, cond_c


def find_aux_seed(ctx, bound):
    """
    Brute-force search for one integer solution (x0,v0) of
        a*x^2+b*x+c = D*v^2
    satisfying the congruences.

    For a=0, scan v and solve the resulting linear equation for x.
    For a!=0, scan v and solve the resulting quadratic equation for x.
    """
    a, b, c, D = ctx.a, ctx.b, ctx.c, ctx.D

    if D == 0:
        return None

    if a == 0:
        if b == 0:
            return None
        for v in ordered_range(bound):
            if not congruences_ok(ctx, v):
                continue
            numerator = D * v * v - c
            if numerator % b == 0:
                x = numerator // b
                if aux_ok(ctx, x, v):
                    return (x, v)
        return None

    den = 2 * a
    for v in ordered_range(bound):
        if not congruences_ok(ctx, v):
            continue
        disc = b * b - 4 * a * (c - D * v * v)
        s = sqrt_if_square(disc)
        if s is None:
            continue
        for num in (-b + s, -b - s):
            if num % den == 0:
                x = num // den
                if aux_ok(ctx, x, v):
                    return (x, v)
    return None


def representation_search(A, B, C, m, pq_bound):
    """Yield integer pairs (p,q) with |p|,|q|<=pq_bound and F(p,q)=m."""
    for p in ordered_range(pq_bound):
        for q in ordered_range(pq_bound):
            if F_value(A, B, C, p, q) == m:
                yield (p, q)


def algorithm43_search(A, B, C, R, Q, u_bound, pq_bound, seed_bound):
    """
    Search for u,p,q and a seed (x0,v0) satisfying Algorithm 4.3 and Proposition 4.2.
    Return a Context, or None.
    """
    Delta = B * B - 4 * A * C
    if Delta == 0:
        raise ValueError("F is degenerate: Delta = 0")

    for u in ordered_range(u_bound):
        m = poly_eval(R, u)
        if m == 0:
            continue
        for p, q in representation_search(A, B, C, m, pq_bound):
            try:
                ctx = build_context(A, B, C, R, Q, u, p, q)
            except ValueError:
                continue
            cond_a, cond_b = proposition_42_conditions_without_seed(ctx)
            if not (cond_a and cond_b):
                continue
            seed = find_aux_seed(ctx, seed_bound)
            if seed is None:
                continue
            ctx.seed = seed
            if all(proposition_42_conditions(ctx)):
                return ctx
    return None


# ---------------------------------------------------------------------------
# Generating solutions after a successful Algorithm 4.3 certificate
# ---------------------------------------------------------------------------


def solution_from_aux(ctx, x, v):
    """Construct (x,y,z,v) using formula (29)."""
    s = poly_eval(ctx.Q, x) - ctx.u
    denom = 2 * ctx.m
    lam_num = ctx.r * ctx.p + v * (ctx.B * ctx.p + 2 * ctx.C * ctx.q)
    mu_num = ctx.r * ctx.q - v * (2 * ctx.A * ctx.p + ctx.B * ctx.q)
    if lam_num % denom != 0 or mu_num % denom != 0:
        raise ArithmeticError("congruences failed: lambda or mu is not integral")
    lam = lam_num // denom
    mu = mu_num // denom
    y = ctx.p + s * lam
    z = ctx.q + s * mu
    if F_value(ctx.A, ctx.B, ctx.C, y, z) != poly_eval(ctx.R, poly_eval(ctx.Q, x)):
        raise ArithmeticError("constructed solution failed verification")
    return (x, y, z, v)


def valid_linear_period(ctx, v0, L):
    """Check that v=v0+nL preserves congruences and x-integrality for all n, in the a=0 case."""
    if L <= 0 or ctx.a != 0 or ctx.b == 0:
        return False
    mod = 2 * abs(ctx.m)
    coeff1 = ctx.B * ctx.p + 2 * ctx.C * ctx.q
    coeff2 = -(2 * ctx.A * ctx.p + ctx.B * ctx.q)
    if (coeff1 * L) % mod != 0:
        return False
    if (coeff2 * L) % mod != 0:
        return False
    b_abs = abs(ctx.b)
    # Need b | D*((v0+nL)^2-v0^2) for every integer n.
    # It is enough to require b | D*L^2 and b | 2*D*v0*L.
    if (ctx.D * L * L) % b_abs != 0:
        return False
    if (2 * ctx.D * v0 * L) % b_abs != 0:
        return False
    return True


def find_linear_period(ctx, v0, max_scan):
    for L in range(1, max_scan + 1):
        if valid_linear_period(ctx, v0, L):
            return L
    # Safe but sometimes non-minimal fallback.
    return lcm(2 * abs(ctx.m), abs(ctx.b))


def generate_linear_aux_pairs(ctx, count, max_period_scan):
    """Generate aux pairs in the a=0 case."""
    if ctx.seed is None:
        raise ValueError("no seed stored in context")
    x0, v0 = ctx.seed
    if ctx.a != 0:
        raise ValueError("linear generator called with a != 0")
    if ctx.b == 0:
        raise ValueError("cannot generate: a=b=0")

    L = find_linear_period(ctx, v0, max_period_scan)
    emitted = 0
    for n in ordered_range(max(count * 3, count + 10)):
        v = v0 + L * n
        numerator = ctx.D * v * v - ctx.c
        if numerator % ctx.b != 0:
            continue
        x = numerator // ctx.b
        if aux_ok(ctx, x, v):
            yield (x, v)
            emitted += 1
            if emitted >= count:
                return

    # Fallback: continue one-sided if the symmetric small range was somehow too short.
    n = count * 3 + 11
    while emitted < count:
        v = v0 + L * n
        numerator = ctx.D * v * v - ctx.c
        if numerator % ctx.b == 0:
            x = numerator // ctx.b
            if aux_ok(ctx, x, v):
                yield (x, v)
                emitted += 1
        n += 1


def pell_fundamental_solution(N):
    """Return the minimal positive solution (U,W) to U^2 - N W^2 = 1."""
    if N <= 0 or is_square(N):
        raise ValueError("N must be positive nonsquare")

    a0 = _isqrt(N)
    m = 0
    d = 1
    a = a0

    num_m2 = 0
    num_m1 = 1
    den_m2 = 1
    den_m1 = 0

    # The loop is guaranteed to terminate for nonsquare positive N.
    while True:
        num = a * num_m1 + num_m2
        den = a * den_m1 + den_m2
        if num * num - N * den * den == 1:
            return num, den
        num_m2, num_m1 = num_m1, num
        den_m2, den_m1 = den_m1, den
        m = d * a - m
        d = (N - m * m) // d
        a = (a0 + m) // d


def multiply_quadratic_pair(pair1, pair2, N):
    """Multiply (x1+y1 sqrt(N))*(x2+y2 sqrt(N))."""
    x1, y1 = pair1
    x2, y2 = pair2
    return (x1 * x2 + N * y1 * y2, x1 * y2 + x2 * y1)


def multiply_quadratic_pair_mod(pair1, pair2, N, M):
    x, y = multiply_quadratic_pair(pair1, pair2, N)
    return (x % M, y % M)


def find_unit_identity_power_mod(U, W, N, M, max_power):
    """Find T such that (U+W sqrt(N))^T == 1 mod M in Z[sqrt(N)]."""
    if M <= 1:
        return (U, W, 1)
    cur = (1 % M, 0)
    base = (U % M, W % M)
    full = (1, 0)
    unit = (U, W)
    for T in range(1, max_power + 1):
        cur = multiply_quadratic_pair_mod(cur, base, N, M)
        full = multiply_quadratic_pair(full, unit, N)
        if cur == (1 % M, 0):
            return (full[0], full[1], T)
    return None


def generate_pell_aux_pairs(ctx, count, max_unit_power):
    """Generate aux pairs in the a != 0 case via Pell multiplication."""
    if ctx.seed is None:
        raise ValueError("no seed stored in context")
    a, b, c, D = ctx.a, ctx.b, ctx.c, ctx.D
    if a == 0:
        raise ValueError("Pell generator called with a=0")
    N = 4 * a * D
    if N <= 0 or is_square(N):
        raise ValueError("Pell generator requires N=4*a*D positive nonsquare")

    x0, v0 = ctx.seed
    X0 = 2 * a * x0 + b
    Y0 = v0
    K = b * b - 4 * a * c
    if X0 * X0 - N * Y0 * Y0 != K:
        raise ArithmeticError("Pell transform seed check failed")

    U, W = pell_fundamental_solution(N)
    M = lcm(abs(2 * a), 2 * abs(ctx.m))
    unit_power = find_unit_identity_power_mod(U, W, N, M, max_unit_power)
    if unit_power is None:
        # Fallback: use the fundamental unit and filter. This may skip many terms.
        step = (U, W)
    else:
        step = (unit_power[0], unit_power[1])

    emitted = 0
    X, Y = X0, Y0
    for n in range(count * 10 + 10):
        if (X - b) % (2 * a) == 0:
            x = (X - b) // (2 * a)
            v = Y
            if aux_ok(ctx, x, v):
                yield (x, v)
                emitted += 1
                if emitted >= count:
                    return
        X, Y = multiply_quadratic_pair((X, Y), step, N)

    # If the filtered fundamental-unit fallback did not produce enough terms, continue longer.
    hard_limit = max(count * 1000, 1000)
    for n in range(count * 10 + 10, hard_limit):
        if (X - b) % (2 * a) == 0:
            x = (X - b) // (2 * a)
            v = Y
            if aux_ok(ctx, x, v):
                yield (x, v)
                emitted += 1
                if emitted >= count:
                    return
        X, Y = multiply_quadratic_pair((X, Y), step, N)

    raise RuntimeError("Pell generator did not find enough congruent terms; increase --max-unit-power")


def generate_aux_pairs(ctx, count, max_period_scan, max_unit_power):
    if ctx.a == 0:
        for pair in generate_linear_aux_pairs(ctx, count, max_period_scan):
            yield pair
    else:
        for pair in generate_pell_aux_pairs(ctx, count, max_unit_power):
            yield pair


# ---------------------------------------------------------------------------
# Examples from Proposition 4.4
# ---------------------------------------------------------------------------


def example_context(name):
    if name == "prop44_plus":
        # 2y^2 + yz + 2z^2 = x^3 + 1
        # Paper seed: u=1, (p,q)=(1,0), x0=1, v0=1.
        ctx = build_context(2, 1, 2, [1, 0, 0, 1], [0, 1], 1, 1, 0)
        ctx.seed = (1, 1)
        return ctx
    if name == "prop44_minus":
        # 2y^2 + yz + 2z^2 = x^3 - 1
        # Paper seed: u=7, (p,q)=(3,12), x0=24, v0=45.
        ctx = build_context(2, 1, 2, [-1, 0, 0, 1], [0, 1], 7, 3, 12)
        ctx.seed = (24, 45)
        return ctx
    raise ValueError("unknown example: %s" % name)


# ---------------------------------------------------------------------------
# Printing / CLI
# ---------------------------------------------------------------------------



def format_int(n, max_digits):
    """Format an integer, abbreviating very large outputs unless max_digits=0."""
    s = str(n)
    if max_digits is None or max_digits == 0 or len(s) <= max_digits:
        return s
    if max_digits < 40:
        max_digits = 40
    left = max_digits // 2
    right = max_digits - left
    return s[:left] + "...<%d digits>..." % len(s) + s[-right:]

def describe_context(ctx):
    print("Quadratic form F(y,z) = %s*y^2 + %s*y*z + %s*z^2" % (ctx.A, ctx.B, ctx.C))
    print("Delta = B^2 - 4AC = %s;  D = -Delta = %s" % (ctx.Delta, ctx.D))
    print("R(t) = %s" % poly_to_string(ctx.R, "t"))
    print("Q(x) = %s" % poly_to_string(ctx.Q, "x"))
    print("u = %s,  (p,q) = (%s,%s)" % (ctx.u, ctx.p, ctx.q))
    print("m = R(u) = F(p,q) = %s" % ctx.m)
    print("r = R'(u) = %s" % ctx.r)
    print("D_u(t) = %s" % poly_to_string(ctx.Du, "t"))
    print("D_u(Q(x)) = %s" % poly_to_string(ctx.DuQ, "x"))
    print("Auxiliary equation:")
    print("    %s = %s*v^2" % (poly_to_string(ctx.left_poly, "x"), ctx.D))
    print("Equivalently:")
    print("    (%s)*x^2 + (%s)*x + (%s) = %s*v^2" % (ctx.a, ctx.b, ctx.c, ctx.D))
    first_const = ctx.r * ctx.p
    first_coeff = ctx.B * ctx.p + 2 * ctx.C * ctx.q
    second_const = ctx.r * ctx.q
    second_coeff = -(2 * ctx.A * ctx.p + ctx.B * ctx.q)
    print("Congruences modulo 2|m| = %s:" % (2 * abs(ctx.m)))
    print("    %s + (%s)*v == 0" % (first_const, first_coeff))
    print("    %s + (%s)*v == 0" % (second_const, second_coeff))
    conds = proposition_42_conditions(ctx)
    print("Proposition 4.2 conditions: (a)=%s, (b)=%s, (c)=%s" % conds)
    if ctx.seed is not None:
        print("Auxiliary seed: x0 = %s, v0 = %s" % (ctx.seed[0], ctx.seed[1]))
    print("")


def print_solutions(ctx, count, max_period_scan, max_unit_power, max_print_digits):
    print("Solutions produced by formula (29):")
    print("    index | x | y | z | v | verification")
    print("    " + "-" * 72)
    i = 0
    for x, v in generate_aux_pairs(ctx, count, max_period_scan, max_unit_power):
        sol = solution_from_aux(ctx, x, v)
        x, y, z, v = sol
        lhs = F_value(ctx.A, ctx.B, ctx.C, y, z)
        rhs = poly_eval(ctx.R, poly_eval(ctx.Q, x))
        ok = "OK" if lhs == rhs else "FAIL"
        print("    %5d | %s | %s | %s | %s | F=%s, R(Q)=%s [%s]" % (
            i,
            format_int(x, max_print_digits),
            format_int(y, max_print_digits),
            format_int(z, max_print_digits),
            format_int(v, max_print_digits),
            format_int(lhs, max_print_digits),
            format_int(rhs, max_print_digits),
            ok))
        i += 1




def context_to_solutions(ctx, count, max_period_scan, max_unit_power):
    """Return a list of constructed (x,y,z,v) solutions for testing."""
    out = []
    for x, v in generate_aux_pairs(ctx, count, max_period_scan, max_unit_power):
        out.append(solution_from_aux(ctx, x, v))
    return out


def run_self_test():
    """Fast internal checks for the two Proposition 4.4 examples."""
    for name in ("prop44_plus", "prop44_minus"):
        ctx = example_context(name)
        if not all(proposition_42_conditions(ctx)):
            raise AssertionError("Proposition 4.2 conditions failed for %s" % name)
        sols = context_to_solutions(ctx, 3, 100000, 100000)
        if len(sols) != 3:
            raise AssertionError("expected 3 solutions for %s" % name)
        for x, y, z, v in sols:
            lhs = F_value(ctx.A, ctx.B, ctx.C, y, z)
            rhs = poly_eval(ctx.R, poly_eval(ctx.Q, x))
            if lhs != rhs:
                raise AssertionError("verification failed for %s" % name)
    print("Self-test passed: prop44_plus and prop44_minus both generate verified solutions.")


def run_demo(count, max_period_scan, max_unit_power, max_print_digits):
    """Run both examples from Proposition 4.4."""
    for name in ("prop44_plus", "prop44_minus"):
        print("=" * 80)
        print("Example:", name)
        print("=" * 80)
        ctx = example_context(name)
        describe_context(ctx)
        print_solutions(ctx, count, max_period_scan, max_unit_power, max_print_digits)
        print("")

def main(argv):
    # Friendly behavior for IDEs / online runners: running the file with no
    # arguments now runs both built-in Proposition 4.4 examples instead of
    # throwing an argparse usage error.
    if not argv:
        argv = ["--demo"]

    parser = argparse.ArgumentParser(
        description="Implementation of Grechuk--Agbanwa Algorithm 4.3"
    )
    parser.add_argument("--example", choices=["prop44_plus", "prop44_minus", "plus", "minus"],
                        help="run one example from Proposition 4.4")
    parser.add_argument("--demo", action="store_true",
                        help="run both Proposition 4.4 examples; this is the default with no arguments")
    parser.add_argument("--self-test", action="store_true",
                        help="run fast internal verification tests and exit")
    parser.add_argument("--list-examples", action="store_true",
                        help="list available named examples and exit")
    parser.add_argument("--A", type=int, help="coefficient A in F=Ay^2+Byz+Cz^2")
    parser.add_argument("--B", type=int, help="coefficient B in F=Ay^2+Byz+Cz^2")
    parser.add_argument("--C", type=int, help="coefficient C in F=Ay^2+Byz+Cz^2")
    parser.add_argument("--R", type=parse_poly,
                        help="R coefficients, low degree first, e.g. 1,0,0,1 for t^3+1")
    parser.add_argument("--Q", type=parse_poly,
                        help="Q coefficients, low degree first, e.g. 0,1 for x")
    parser.add_argument("--u", type=int, help="manual seed u")
    parser.add_argument("--p", type=int, help="manual seed p")
    parser.add_argument("--q", type=int, help="manual seed q")
    parser.add_argument("--seed-x", type=int, help="manual auxiliary seed x0")
    parser.add_argument("--seed-v", type=int, help="manual auxiliary seed v0")
    parser.add_argument("--u-bound", type=int, default=20,
                        help="search bound for u if no manual seed is supplied")
    parser.add_argument("--pq-bound", type=int, default=30, help="search bound for p,q")
    parser.add_argument("--seed-bound", type=int, default=5000,
                        help="search bound for auxiliary seed v")
    parser.add_argument("--count", type=int, default=5, help="number of solutions to print")
    parser.add_argument("--max-period-scan", type=int, default=100000,
                        help="max scan for linear v-period")
    parser.add_argument("--max-unit-power", type=int, default=100000,
                        help="max scan for Pell unit power modulo congruence modulus")
    parser.add_argument("--max-print-digits", type=int, default=240,
                        help="abbreviate printed integers longer than this; use 0 for full integers")

    args = parser.parse_args(argv)

    if args.list_examples:
        print("Available examples:")
        print("  prop44_plus   : 2y^2 + yz + 2z^2 = x^3 + 1")
        print("  prop44_minus  : 2y^2 + yz + 2z^2 = x^3 - 1")
        print("Aliases: plus, minus")
        return

    if args.self_test:
        run_self_test()
        return

    custom_fields = [args.A, args.B, args.C, args.R, args.Q]

    # If the user only changes display parameters such as --count, run demo.
    # But if they supplied part of a custom problem, require the full custom input.
    if args.demo or (not args.example and all(v is None for v in custom_fields)):
        run_demo(args.count, args.max_period_scan, args.max_unit_power, args.max_print_digits)
        return

    if args.example:
        ex = args.example
        if ex == "plus":
            ex = "prop44_plus"
        elif ex == "minus":
            ex = "prop44_minus"
        ctx = example_context(ex)
    else:
        if any(v is None for v in custom_fields):
            parser.error("either use --example/--demo, or supply all of --A --B --C --R --Q")

        if args.u is not None or args.p is not None or args.q is not None:
            if args.u is None or args.p is None or args.q is None:
                parser.error("manual seed requires all of --u --p --q")
            ctx = build_context(args.A, args.B, args.C, args.R, args.Q, args.u, args.p, args.q)
            if args.seed_x is not None or args.seed_v is not None:
                if args.seed_x is None or args.seed_v is None:
                    parser.error("manual auxiliary seed requires both --seed-x and --seed-v")
                ctx.seed = (args.seed_x, args.seed_v)
                if not aux_ok(ctx, ctx.seed[0], ctx.seed[1]):
                    parser.error("manual auxiliary seed does not satisfy equation plus congruences")
            else:
                seed = find_aux_seed(ctx, args.seed_bound)
                if seed is None:
                    parser.error("could not find auxiliary seed; increase --seed-bound or choose different u,p,q")
                ctx.seed = seed
        else:
            ctx = algorithm43_search(args.A, args.B, args.C, args.R, args.Q,
                                     args.u_bound, args.pq_bound, args.seed_bound)
            if ctx is None:
                parser.error("Algorithm 4.3 search failed within bounds; increase --u-bound, --pq-bound, or --seed-bound")

    conds = proposition_42_conditions(ctx)
    if not all(conds):
        describe_context(ctx)
        parser.error("Proposition 4.2 conditions are not all satisfied")

    describe_context(ctx)
    print_solutions(ctx, args.count, args.max_period_scan, args.max_unit_power, args.max_print_digits)


if __name__ == "__main__":
    main(sys.argv[1:])
