#!/usr/bin/env python3
"""Shared parsing + exact arithmetic for the B1 (star) data pipeline.

The single source of truth for the data is the LANDED ENGINE:

    build/mb_pipeline stardump <rec-t1|rec-t2> <n>

which prints, for one integer `n`, the five polynomial data of the (star)
identity as integer affine-factor multisets (`a`, `b`, `c`, `D`, `Pa j`) plus the
solution (`AJ j` = alpha_j(n), `X k` = the certificate's coefficients).  Nothing
here is transcribed from a document.

(star), verbatim from `cas::zeilqn::star_check_core`:

    a(t) * x(t+1)  -  b(t-1) * x(t)  -  c(t) * SUM_j alpha_j * Pa_j(t)  ==  0

as an identity of polynomials in t.

THE POLYNOMIAL ALGEBRA BELOW IS A DELIBERATE SECOND IMPLEMENTATION, NOT A COPY.
`factors_to_coeffs` / `poly_shift` / `poly_mul` re-derive in exact `Fraction`
arithmetic what `zp_conv` / `zp_shift1` / `expand_at_n` do over the engine's own
bignums, so that `star_residual` can CHECK the engine's identity rather than
restate its verdict.  A cross-check that reuses the checked code checks nothing
(LEAN.md Sec6 layer 2); the duplication is the instrument.  Do not "consolidate"
it with the engine, and do not call the engine from here.
"""

import sys
from fractions import Fraction

sys.set_int_max_str_digits(2000000)


# ───────────────────────────── the dump format ──────────────────────────────


class StarDump:
    """One `mb_pipeline stardump` record."""

    def __init__(self):
        self.header = {}
        self.fac = {}  # name -> list of (lead, off, mult)
        self.aj = []  # Fraction
        self.x = []  # Fraction, index = t-degree

    @property
    def J(self):
        return int(self.header["J"])

    @property
    def dx(self):
        return int(self.header["dx"])

    @property
    def n(self):
        return int(self.header["n"])

    @property
    def side(self):
        return self.header["side"]


def parse_dump(path):
    d = StarDump()
    cur = None
    with open(path) as f:
        for raw in f:
            line = raw.rstrip("\n")
            if line.startswith("STARDUMP "):
                for kv in line.split()[1:]:
                    k, _, v = kv.partition("=")
                    d.header[k] = v
                continue
            if line.startswith("FAC "):
                _, name, _count = line.split()
                cur = name
                d.fac[cur] = []
                continue
            if line.startswith("  "):
                lead, off, mult = line.split()
                d.fac[cur].append((int(lead), int(off), int(mult)))
                continue
            if line.startswith("AJ "):
                _, idx, val = line.split()
                num, den = val.split("/")
                assert int(idx) == len(d.aj), "AJ out of order"
                d.aj.append(Fraction(int(num), int(den)))
                continue
            if line.startswith("X "):
                _, idx, val = line.split()
                num, den = val.split("/")
                assert int(idx) == len(d.x), "X out of order"
                d.x.append(Fraction(int(num), int(den)))
                continue
            if line == "END":
                cur = None
                continue
    missing = [k for k in ("a", "b", "c", "D") if k not in d.fac]
    if missing:
        raise ValueError("dump %s is missing factor blocks %s" % (path, missing))
    if len(d.aj) != d.J + 1:
        raise ValueError("dump %s: %d alphas for J=%d" % (path, len(d.aj), d.J))
    if len(d.x) != d.dx + 1:
        raise ValueError("dump %s: %d x-coeffs for dx=%d" % (path, len(d.x), d.dx))
    return d


# ────────────────────────── exact polynomial algebra ─────────────────────────


def factors_to_coeffs(facs):
    """Product of (lead*t + off)^mult, as a dense low->high coefficient list."""
    out = [Fraction(1)]
    for lead, off, mult in facs:
        for _ in range(mult):
            nxt = [Fraction(0)] * (len(out) + 1)
            for i, cf in enumerate(out):
                nxt[i] += cf * off
                nxt[i + 1] += cf * lead
            out = nxt
    return out


def poly_shift(coeffs, h):
    """p(t + h), exact."""
    n = len(coeffs)
    out = [Fraction(0)] * n
    for i, cf in enumerate(coeffs):
        if cf == 0:
            continue
        binom = 1
        for k in range(i, -1, -1):
            out[k] += cf * binom * Fraction(h) ** (i - k)
            binom = binom * k // (i - k + 1)
    return out


def poly_mul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, xv in enumerate(a):
        if xv == 0:
            continue
        for j, yv in enumerate(b):
            out[i + j] += xv * yv
    return out


def poly_lin(terms):
    """Sum of (scalar, poly)."""
    n = max((len(p) for _, p in terms), default=1)
    out = [Fraction(0)] * n
    for s, p in terms:
        for i, cf in enumerate(p):
            out[i] += s * cf
    return out


def poly_sub(a, b):
    n = max(len(a), len(b))
    out = [Fraction(0)] * n
    for i, xv in enumerate(a):
        out[i] += xv
    for i, yv in enumerate(b):
        out[i] -= yv
    return out


def star_residual(d):
    """The (star) residual polynomial, computed independently of the engine.

    Zero iff (star) holds at this n.  This is the pipeline's ALGEBRAIC
    cross-check: it re-does the identity from the dumped data rather than
    trusting the engine's own verdict line.
    """
    ac = factors_to_coeffs(d.fac["a"])
    bc = factors_to_coeffs(d.fac["b"])
    cc = factors_to_coeffs(d.fac["c"])
    lhs = poly_sub(poly_mul(ac, poly_shift(d.x, 1)), poly_mul(poly_shift(bc, -1), d.x))
    pasum = poly_lin(
        [(d.aj[j], factors_to_coeffs(d.fac["Pa%d" % j])) for j in range(d.J + 1)]
    )
    return poly_sub(lhs, poly_mul(cc, pasum))


def is_zero(poly):
    return all(cf == 0 for cf in poly)


# ───────────────────────────── Lean rendering ────────────────────────────────


def lean_rat(fr):
    """A rational literal.  Integers print bare so `ring` sees no division."""
    if fr.denominator == 1:
        return "(%d : ℚ)" % fr.numerator
    return "((%d : ℚ) / %d)" % (fr.numerator, fr.denominator)


def lean_horner(coeffs, var):
    coeffs = list(coeffs)
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    out = lean_rat(coeffs[-1])
    for i in range(len(coeffs) - 2, -1, -1):
        out = "(%s * %s + %s)" % (out, var, lean_rat(coeffs[i]))
    return out


def lean_factor_product(facs, var):
    parts = []
    for lead, off, mult in facs:
        term = var if lead == 1 else "((%d : ℚ) * %s)" % (lead, var)
        for _ in range(mult):
            parts.append("(%s + (%d : ℚ))" % (term, off))
    return " * ".join(parts) if parts else "(1 : ℚ)"


# ───────────────── mirror of the Lean kernel ops (StarKernelBridge.lean) ─────────────────
# Dense `List ℤ`, low degree first, over Python ints.  These are the SECOND implementation of
# the operations `StarKernelBridge.lean` defines (`zadd`/`zscale`/`zmul`/`zprod`/`zshift1`/
# `zsub`/`ztrim`) and the kernel runs under `decide +kernel`; a generator re-verifies the
# ℤ-cleared (★) identity with them before it writes a kernel shard (LEAN.md §6 layer 2), and
# `gen_star_kernel_probe.py` measured them.  Structurally recursive like the Lean side on
# purpose — `poly_mul`/`poly_shift` above are the OTHER second implementation, over Fractions.


def zp_add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def zp_scale(c, p):
    return [c * v for v in p]


def zp_mul(p, q):
    if not p:
        return []
    return zp_add(zp_scale(p[0], q), [0] + zp_mul(p[1:], q))


def zp_prod(facs):
    out = [1]
    for lead, off in facs:
        out = zp_mul([off, lead], out)
    return out


def zp_shift1(p):
    acc = []
    for c in reversed(p):
        acc = zp_add([c], zp_mul([1, 1], acc))
    return acc


def zp_trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def zp_sub(p, q):
    return zp_add(p, zp_scale(-1, q))


def zp_star_sides(L, M, fa, fb1, fc, xL, aM, fpa):
    """The two sides of the ℤ-cleared (★) at one point, exactly as the kernel shard states them:
    `M·[a·(Lx)(t+1) − b(t−1)·(Lx)]` and `L·c·Σⱼ (Mαⱼ)·Paⱼ`, with the Σ nested
    `(0 + 1) + (2 + 3)` — the nesting `StarKernel.h0_of_kernel` expects (J = 3)."""
    if len(aM) != 4 or len(fpa) != 4:
        raise ValueError("zp_star_sides: written for J = 3 (four recurrence coefficients)")
    lhs = zp_scale(M, zp_sub(zp_mul(zp_prod(fa), zp_shift1(xL)), zp_mul(zp_prod(fb1), xL)))
    s01 = zp_add(zp_scale(aM[0], zp_prod(fpa[0])), zp_scale(aM[1], zp_prod(fpa[1])))
    s23 = zp_add(zp_scale(aM[2], zp_prod(fpa[2])), zp_scale(aM[3], zp_prod(fpa[3])))
    rhs = zp_scale(L, zp_mul(zp_prod(fc), zp_add(s01, s23)))
    return lhs, rhs
