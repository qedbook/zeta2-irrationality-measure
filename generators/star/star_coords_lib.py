#!/usr/bin/env python3
"""Parsing + exact Q[n] algebra for the SYMBOLIC (star) coordinates.

The single source of truth for the data is the LANDED ENGINE:

    build/mb_pipeline starcoords <rec-t1|rec-t2|cand-t1|cand-t2>

which prints the whole solve as a function of `n`: the five affine-factor
multisets with their `n`-slopes UNSPECIALIZED (`lead*t + a*n + b`), and every
coordinate as a reduced pair (A_k, B_k) of polynomials in `n` with value A/B --
`k = 0..dx` the certificate x's coefficients, `k = dx+1..dx+1+J` the alpha_j.
Nothing here is transcribed from a document.

WHY THIS EXISTS.  zeta2-star-b1.md Sec15.5: `Zeta2StarB1.star_forall_of_grid`
consumes a residual POLYNOMIAL `F` in `n` plus a degree bound, and a per-point
receipt supplies neither -- 552 shards buy `forall w in sample`, not `forall n`.
`F` is the CLEARED residual

    F(n)(t) = a(n,t) * X(n,t+1) - b(n,t-1) * X(n,t)
              - c(n,t) * SUM_j Atilde_j(n) * Pa_j(n,t)

where `L` is a common denominator of every B_k, `X_k = A_k * (L / B_k)` and
`Atilde_j = A_{dx+1+j} * (L / B_{dx+1+j})`.  Multiplying (star) by `L` clears
every coordinate at once because x and the alpha_j each occur LINEARLY -- one
factor of `L`, not one per coefficient, which is what keeps the degree at ~551
instead of ~22000.

THE ALGEBRA BELOW IS A DELIBERATE SECOND IMPLEMENTATION, NOT A COPY, for the same
reason `star_lib`'s is (LEAN.md Sec6 layer 2): it re-derives in exact `Fraction`
arithmetic what the engine does over its own bignums, so the emitted `F` can be
CHECKED rather than trusted.  Do not consolidate it with the engine, and do not
call the engine from here.
"""

import sys
from fractions import Fraction

sys.set_int_max_str_digits(20000000)


# ───────────────────────────── the coords format ─────────────────────────────


class StarCoords:
    """One `mb_pipeline starcoords` record."""

    def __init__(self):
        self.header = {}
        self.fac = {}      # name -> list of (lead, a, b, mult), meaning lead*t + a*n + b
        self.coords = []   # list of dicts: role, idx, A (list[Fraction]), B (list[Fraction])

    @property
    def J(self):
        return int(self.header["J"])

    @property
    def dx(self):
        return int(self.header["dx"])

    @property
    def side(self):
        return self.header["side"]


def parse_coords(path):
    c = StarCoords()
    cur_fac = None
    cur_coord = None
    cur_part = None
    want = 0
    with open(path) as f:
        for raw in f:
            line = raw.rstrip("\n")
            if line.startswith("STARCOORDS "):
                for kv in line.split()[1:]:
                    k, _, v = kv.partition("=")
                    c.header[k] = v
                continue
            if line.startswith("FACSYM "):
                _, name, _count = line.split()
                cur_fac, cur_coord, cur_part = name, None, None
                c.fac[name] = []
                continue
            if line.startswith("COORD "):
                parts = line.split()
                cur_coord = {
                    "k": int(parts[1]),
                    "role": parts[2].split("=")[1],
                    "idx": int(parts[3].split("=")[1]),
                    "A": None,
                    "B": None,
                }
                c.coords.append(cur_coord)
                cur_fac, cur_part = None, None
                continue
            if line.startswith("  A ") or line.startswith("  B "):
                cur_part = line.strip().split()[0]
                want = int(line.strip().split()[1])
                cur_coord[cur_part] = []
                continue
            if line.startswith("    "):
                idx, val = line.split()
                num, den = val.split("/")
                lst = cur_coord[cur_part]
                if int(idx) != len(lst):
                    raise ValueError("%s: coefficient out of order in COORD %d %s"
                                     % (path, cur_coord["k"], cur_part))
                lst.append(Fraction(int(num), int(den)))
                if len(lst) == want:
                    cur_part = None
                continue
            if line.startswith("  ") and cur_fac is not None:
                lead, a, b, mult = line.split()
                c.fac[cur_fac].append((int(lead), int(a), int(b), int(mult)))
                continue
            if line == "END":
                continue
    # CONTAINMENT, at the reader.  A per-coordinate check establishes nothing
    # about the ENUMERATION being complete: the file must carry exactly
    # dx + 1 certificate coefficients and J + 1 recurrence coefficients, in
    # order, none missing and none duplicated.  (The engine checks the same
    # invariant at the emit; this is the independent restatement, and the two
    # are what make a missing coordinate impossible to miss.)
    nx = c.dx + 1
    want_n = nx + c.J + 1
    if len(c.coords) != want_n:
        raise ValueError("%s: CONTAINMENT — %d coordinates for dx=%d, J=%d (expected %d)"
                         % (path, len(c.coords), c.dx, c.J, want_n))
    for k, co in enumerate(c.coords):
        if co["k"] != k:
            raise ValueError("%s: CONTAINMENT — coordinate %d is labelled %d" % (path, k, co["k"]))
        exp_role, exp_idx = ("x", k) if k < nx else ("alpha", k - nx)
        if co["role"] != exp_role or co["idx"] != exp_idx:
            raise ValueError("%s: CONTAINMENT — coordinate %d is %s[%d], expected %s[%d]"
                             % (path, k, co["role"], co["idx"], exp_role, exp_idx))
        if not co["A"] or not co["B"]:
            raise ValueError("%s: CONTAINMENT — coordinate %d is missing A or B" % (path, k))
    missing = [k for k in ("a", "b", "c", "D") if k not in c.fac]
    if missing:
        raise ValueError("%s: missing factor blocks %s" % (path, missing))
    for j in range(c.J + 1):
        if ("Pa%d" % j) not in c.fac:
            raise ValueError("%s: missing factor block Pa%d" % (path, j))
    return c


# ───────────────────────── exact Q[n] polynomial algebra ─────────────────────
# Dense coefficient lists, low degree first.


def ptrim(p):
    q = list(p)
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    return q


def pdeg(p):
    q = ptrim(p)
    return -1 if (len(q) == 1 and q[0] == 0) else len(q) - 1


def pis_zero(p):
    return all(cf == 0 for cf in p)


def padd(a, b):
    n = max(len(a), len(b))
    out = [Fraction(0)] * n
    for i, v in enumerate(a):
        out[i] += v
    for i, v in enumerate(b):
        out[i] += v
    return ptrim(out)


def psub(a, b):
    n = max(len(a), len(b))
    out = [Fraction(0)] * n
    for i, v in enumerate(a):
        out[i] += v
    for i, v in enumerate(b):
        out[i] -= v
    return ptrim(out)


def pmul(a, b):
    if pis_zero(a) or pis_zero(b):
        return [Fraction(0)]
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        if u == 0:
            continue
        for j, v in enumerate(b):
            if v != 0:
                out[i + j] += u * v
    return ptrim(out)


def pdivmod(a, b):
    """Exact division with remainder over Q[n]."""
    a, b = ptrim(a), ptrim(b)
    if pis_zero(b):
        raise ZeroDivisionError("pdivmod by the zero polynomial")
    db = pdeg(b)
    lead = b[db]
    r = list(a)
    q = [Fraction(0)] * max(1, len(a) - db)
    for k in range(pdeg(r) - db, -1, -1):
        if len(r) <= k + db or r[k + db] == 0:
            continue
        f = r[k + db] / lead
        q[k] = f
        for i, v in enumerate(b):
            r[k + i] -= f * v
    return ptrim(q), ptrim(r)


def pdiv_exact(a, b):
    q, r = pdivmod(a, b)
    if not pis_zero(r):
        raise ValueError("pdiv_exact: %s does not divide" % b[:3])
    return q


def pmonic(p):
    p = ptrim(p)
    d = pdeg(p)
    if d < 0:
        return p
    lead = p[d]
    return [v / lead for v in p]


def pgcd(a, b):
    a, b = ptrim(a), ptrim(b)
    while not pis_zero(b):
        _, r = pdivmod(a, b)
        a, b = b, ptrim(r)
    return pmonic(a)


def peval(p, v):
    """Horner, high -> low."""
    acc = Fraction(0)
    for cf in reversed(p):
        acc = acc * v + cf
    return acc


def common_denominator(bs):
    """A polynomial every `B_k` divides.

    FAST PATH FIRST, and it is not an optimisation but a numerical one: an
    Euclidean gcd over Q[n] on degree-155 polynomials with 271-digit coefficients
    grows its intermediates without bound, while an exact-division TEST is
    stable.  The solve's coordinates are individually reduced fractions of one
    common denominator, so the widest `B` normally IS the lcm; the gcd path
    stays as the honest fallback and reports itself.
    """
    cand = max(bs, key=pdeg)
    used_gcd = 0
    for b in bs:
        _, r = pdivmod(cand, b)
        if not pis_zero(r):
            used_gcd += 1
            cand = pmul(pdiv_exact(cand, pgcd(cand, b)), b)
    return pmonic(cand), used_gcd


# ───────────────────── the cleared residual, per `n` (Q[t]) ──────────────────


def facs_at_n(facs, n):
    """`lead*t + a*n + b` at a fixed integer `n`, as star_lib's (lead, off, mult)."""
    return [(lead, a * n + b, mult) for (lead, a, b, mult) in facs]


def structural_degree_bound(c, xnum, atil):
    """The `n`-degree bound `hdeg` must prove, computed the way LEAN will.

    Not the true degree: the bound Lean's structural arithmetic
    (`natDegree_add_le` / `natDegree_mul_le`, one affine factor = 1) will
    actually reach.  Emitting a bound Lean cannot reproduce is the one way this
    number could be wrong in the direction that matters, so it is derived from
    the SAME rules rather than from `pdeg(F)`.
    """
    def tdeg_count(name):
        return sum(mult for (_l, _a, _b, mult) in c.fac[name])

    xmax = max(len(p) - 1 for p in xnum)
    lhs_a = tdeg_count("a") + xmax
    lhs_b = tdeg_count("b") + xmax
    rhs = tdeg_count("c") + max(
        (len(atil[j]) - 1) + tdeg_count("Pa%d" % j) for j in range(c.J + 1)
    )
    return max(lhs_a, lhs_b, rhs)
