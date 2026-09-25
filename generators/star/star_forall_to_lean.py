#!/usr/bin/env python3
"""Encode the engine's SYMBOLIC coordinates as `star_forall_of_grid`'s `F` and `hdeg`.

    star_forall_to_lean.py --coords build/starcoords_rec-t1.txt --out F.lean
                           [--points 0,1,2 | --points all] [--verify-points N]

LAYER 1 of the LEAN.md Sec6 discipline, for the `forall n` half of B1: GENERATE,
never retype.  The only input is `mb_pipeline starcoords`; the encoder refuses to
emit unless it has independently re-verified, in exact rational arithmetic, that
the cleared residual it is about to write down actually VANISHES -- at more
integer `n` than its own structural degree bound, which is not a sample but a
proof over Q[n].

WHAT IS BUILT, and why it is the object Sec15.5 says nobody was producing.
`Zeta2StarB1.star_forall_of_grid` consumes

    (F : R[X]) (D : Nat) (hdeg : F.natDegree <= D)
    (s : Finset R) (hs : D < s.card) (h0 : forall v in s, F.eval v = 0)

A shard supplies none of `F`, `D`, `hdeg`: it proves `StarIdentity` about six
concrete `Q -> Q` functions at ONE `n`.  Here `R = Q` with the contour variable
`t` a PARAMETER, so `F t : Q[X]` is a polynomial in `n` alone and the conclusion
`forall t v, (F t).eval v = 0` is (star) at every `n` and every `t`.

`F` is CLEARED and UNEXPANDED.  Cleared: `L` is a common denominator of every
`B_k`, and `X_k = A_k * (L / B_k)`, so one factor of `L` clears the whole
identity (x and the alpha_j each occur linearly).  Unexpanded: `F` is a product /
sum expression, never a monomial list -- Route B's ~329 GB was a `ring` over the
EXPANDED bivariate residual (Sec12), and nothing here ever forms that object.

`hdeg` is PROVED, structurally, from the same arithmetic the generator uses to
choose `D` (`star_coords_lib.structural_degree_bound`).  Sec15.5's warning that
"whoever builds `hdeg` must derive it, not quote it" is why the bound 551 is
never read from a document here.

LEAN IS NOT RUN HERE.  This script only WRITES a file; elaborate it with
`run_eval_probe.sh`, which ships to the buildbox (owner rule: no Mathlib on the
laptop, ever).
"""

import argparse
import hashlib
import os
import sys
from math import lcm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import star_coords_lib as scl  # noqa: E402
import star_lib  # noqa: E402   the t-side algebra, a THIRD implementation

# simp's default budget is 100 000 and it COUNTS CONGRUENCES, so every `simp` in
# a generated file whose goal mentions the data has a step count that grows with
# the data.  One budget, used everywhere, so the next scale-up fails in one place
# or in none.
SIMP_STEPS = 20000000

PRELUDE = r'''
namespace @NS@

open Polynomial

/-! ## The encoding primitives

`polB` is Horner from a dense coefficient list; `polB2` is Horner in the CONTOUR
variable of a list of such lists (the certificate `x(n, s) = ∑ₖ Xₖ(n)·sᵏ`);
`afProd` is a factor multiset `∏ (lead·t + a·n + b)`, flattened by multiplicity.

Each carries ONE degree lemma and ONE evaluation lemma.  That is the whole reason
they exist: the naive encoding writes the Horner chain inline, and then `hdeg`
costs one `natDegree_add_le`/`natDegree_mul_le` step per LITERAL (≈ 22 000 at
candidate scale) instead of one per POLYNOMIAL (146). -/

/-- Horner from a dense coefficient list, low degree first. -/
noncomputable def polB : List ℚ → ℚ[X]
  | [] => 0
  | c :: l => C c + X * polB l

theorem polB_natDegree_le : ∀ (l : List ℚ) (d : ℕ), l.length ≤ d + 1 → (polB l).natDegree ≤ d := by
  intro l
  induction l with
  | nil => intro d _; simp [polB]
  | cons c l ih =>
    intro d h
    have hl : l.length ≤ d := by simpa using h
    cases d with
    | zero =>
      have hnil : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      subst hnil
      simp [polB]
    | succ d' =>
      have hih : (polB l).natDegree ≤ d' := ih d' hl
      have h1 : (X * polB l).natDegree ≤ d' + 1 := by
        have hm := natDegree_mul_le (p := (X : ℚ[X])) (q := polB l)
        rw [natDegree_X] at hm
        omega
      have h2 : ((C c : ℚ[X])).natDegree ≤ d' + 1 := by simp
      show (C c + X * polB l).natDegree ≤ d' + 1
      exact le_trans (natDegree_add_le _ _) (max_le h2 h1)

theorem polB_eval : ∀ (l : List ℚ) (v : ℚ),
    (polB l).eval v = l.foldr (fun c acc => c + v * acc) 0 := by
  intro l
  induction l with
  | nil => intro v; simp [polB]
  | cons c l ih => intro v; simp [polB, ih v]

/-- Horner in the contour variable over a list of coefficient lists. -/
noncomputable def polB2 : List (List ℚ) → ℚ → ℚ[X]
  | [], _ => 0
  | l :: ls, s => polB l + C s * polB2 ls s

theorem polB2_natDegree_le : ∀ (ls : List (List ℚ)) (s : ℚ) (d : ℕ),
    (∀ l ∈ ls, l.length ≤ d + 1) → (polB2 ls s).natDegree ≤ d := by
  intro ls
  induction ls with
  | nil => intro s d _; simp [polB2]
  | cons l ls ih =>
    intro s d h
    have hl : l.length ≤ d + 1 := h l (List.mem_cons_self)
    have hrest : ∀ m ∈ ls, m.length ≤ d + 1 := fun m hm => h m (List.mem_cons_of_mem l hm)
    have h1 : (polB l).natDegree ≤ d := polB_natDegree_le l d hl
    have h2 : (C s * polB2 ls s).natDegree ≤ d := by
      have hm := natDegree_mul_le (p := (C s : ℚ[X])) (q := polB2 ls s)
      have := ih s d hrest
      simp only [natDegree_C] at hm
      omega
    show (polB l + C s * polB2 ls s).natDegree ≤ d
    exact le_trans (natDegree_add_le _ _) (max_le h1 h2)

theorem polB2_eval : ∀ (ls : List (List ℚ)) (s v : ℚ),
    (polB2 ls s).eval v = ls.foldr (fun l acc => (polB l).eval v + s * acc) 0 := by
  intro ls
  induction ls with
  | nil => intro s v; simp [polB2]
  | cons l ls ih => intro s v; simp [polB2, ih s v]

/-- One integer affine factor `lead·t + a·n + b`, as a polynomial in `n`. -/
noncomputable def af (t lead a b : ℚ) : ℚ[X] := C (lead * t + b) + C a * X

theorem af_natDegree_le (t lead a b : ℚ) : (af t lead a b).natDegree ≤ 1 := by
  have h2 : ((C a : ℚ[X]) * X).natDegree ≤ 1 := by
    have hm := natDegree_mul_le (p := (C a : ℚ[X])) (q := (X : ℚ[X]))
    simp only [natDegree_C, natDegree_X] at hm
    omega
  have h3 : ((C (lead * t + b) : ℚ[X])).natDegree ≤ 1 := by
    simp only [natDegree_C]; omega
  show ((C (lead * t + b) : ℚ[X]) + C a * X).natDegree ≤ 1
  exact le_trans (natDegree_add_le _ _) (max_le h3 h2)

theorem af_eval (t lead a b v : ℚ) : (af t lead a b).eval v = lead * t + b + a * v := by
  simp [af]

/-- A factor multiset `∏ (lead·t + a·n + b)`, flattened by multiplicity. -/
noncomputable def afProd : List (ℚ × ℚ × ℚ) → ℚ → ℚ[X]
  | [], _ => 1
  | f :: fs, t => af t f.1 f.2.1 f.2.2 * afProd fs t

theorem afProd_natDegree_le : ∀ (fs : List (ℚ × ℚ × ℚ)) (t : ℚ),
    (afProd fs t).natDegree ≤ fs.length := by
  intro fs
  induction fs with
  | nil => intro t; simp [afProd]
  | cons f fs ih =>
    intro t
    have h1 := af_natDegree_le t f.1 f.2.1 f.2.2
    have h2 := ih t
    have hm := natDegree_mul_le (p := af t f.1 f.2.1 f.2.2) (q := afProd fs t)
    show (af t f.1 f.2.1 f.2.2 * afProd fs t).natDegree ≤ (f :: fs).length
    simp only [List.length_cons]
    omega

theorem afProd_eval : ∀ (fs : List (ℚ × ℚ × ℚ)) (t v : ℚ),
    (afProd fs t).eval v = fs.foldr (fun f acc => (f.1 * t + f.2.2 + f.2.1 * v) * acc) 1 := by
  intro fs
  induction fs with
  | nil => intro t v; simp [afProd]
  | cons f fs ih => intro t v; simp [afProd, af_eval, ih t v]

/-- Degree bookkeeping, as four one-liners, so the generated `hdeg` is a tree of
applications rather than a tactic block whose size grows with the data. -/
theorem nd_mul {p q : ℚ[X]} {m n : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).natDegree ≤ m + n := le_trans natDegree_mul_le (Nat.add_le_add hp hq)

theorem nd_add {p q : ℚ[X]} {m : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m) :
    (p + q).natDegree ≤ m := le_trans (natDegree_add_le _ _) (max_le hp hq)

theorem nd_sub {p q : ℚ[X]} {m : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m) :
    (p - q).natDegree ≤ m := le_trans (natDegree_sub_le _ _) (max_le hp hq)

theorem nd_le {p : ℚ[X]} {m n : ℕ} (hp : p.natDegree ≤ m) (h : m ≤ n) : p.natDegree ≤ n :=
  le_trans hp h

/-! ## The grid principle

`star_forall_of_grid`, reproduced VERBATIM from
`external_tests/zeta2_star_b1/Zeta2StarB1.lean` (proved there 2026-09-08,
axiom-clean).  There is no Lean package for this corpus, so it is copied rather
than imported, and the copy is marked so a future edit of the original is known
to require regenerating this file. -/

theorem star_forall_of_grid {R : Type*} [CommRing R] [IsDomain R]
    (F : R[X]) (D : ℕ) (hdeg : F.natDegree ≤ D) (s : Finset R) (hs : D < s.card)
    (h0 : ∀ v ∈ s, F.eval v = 0) : ∀ v : R, F.eval v = 0 := by
  classical
  have hF : F = 0 := by
    by_contra hne
    have hroots : s ⊆ F.roots.toFinset := by
      intro v hv
      simp only [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
      exact h0 v hv
    have : s.card ≤ F.natDegree :=
      le_trans (Finset.card_le_card hroots)
        (le_trans (Multiset.toFinset_card_le _) (F.card_roots' ))
    omega
  simp [hF]
'''


def rat_lit(fr):
    if fr.denominator == 1:
        return "(%d : ℚ)" % fr.numerator
    return "((%d : ℚ) / %d)" % (fr.numerator, fr.denominator)


def list_lit(coeffs):
    return "[" + ", ".join(rat_lit(c) for c in coeffs) + "]"


def _clear_list(coeffs):
    """A ℚ coefficient list as (integer numerators, ONE common denominator) -- row PAIR-K2.

    `d = lcm(den cᵢ)` and `zᵢ = cᵢ·d`, so `cᵢ = zᵢ/d` EXACTLY and the base module can carry
    the list as `List ℤ` without changing a single value.  Measured basis for doing it per
    LIST and not once per grid: the hat grid's per-list denominators are 173-207 digits and
    their lcm over all 121 lists is 207 digits (`sizes.py`, 2026-09-11), so a single global
    denominator would buy nothing and a per-list one keeps the integers in the identity's own
    size class.
    """
    d = 1
    for c in coeffs:
        d = lcm(d, c.denominator)
    return [int(c * d) for c in coeffs], d


def facs_lit(facs):
    """A factor multiset flattened by multiplicity, as `List (ℚ × ℚ × ℚ)`."""
    out = []
    for lead, a, b, mult in facs:
        for _ in range(mult):
            out.append("((%d : ℚ), (%d : ℚ), (%d : ℚ))" % (lead, a, b))
    return "[" + ", ".join(out) + "]"


def facs_count(facs):
    return sum(mult for (_l, _a, _b, mult) in facs)


def build(coords_path):
    """Parse, clear, and return everything the emitter and the gate both need."""
    c = scl.parse_coords(coords_path)
    nx = c.dx + 1
    bs = [co["B"] for co in c.coords]
    L, gcd_used = scl.common_denominator(bs)
    xnum = [scl.pmul(c.coords[k]["A"], scl.pdiv_exact(L, c.coords[k]["B"])) for k in range(nx)]
    atil = [scl.pmul(c.coords[nx + j]["A"], scl.pdiv_exact(L, c.coords[nx + j]["B"]))
            for j in range(c.J + 1)]
    D = scl.structural_degree_bound(c, xnum, atil)
    return c, L, xnum, atil, D, gcd_used


def residual_at(c, xnum, atil, n):
    """The cleared residual at one integer `n`, as an exact ℚ[t] coefficient list.

    A THIRD implementation of the t-side algebra: `star_lib`'s
    `factors_to_coeffs` / `poly_shift` / `poly_mul` (themselves a deliberate
    second implementation of the engine's `zp_conv` / `zp_shift1`).  This
    function's only new content is the CLEARING -- substituting `Xₖ(n)` and
    `Ãⱼ(n)` where `star_lib.star_residual` substitutes the engine's already
    divided `x` and `αⱼ`.  So a bug in the clearing shows up here and a bug in
    the t-algebra shows up in both, which is why the per-point receipts are
    checked by the OTHER path (`check_star_encoding.py`) and not by this one.
    """
    ac = star_lib.factors_to_coeffs(scl.facs_at_n(c.fac["a"], n))
    bc = star_lib.factors_to_coeffs(scl.facs_at_n(c.fac["b"], n))
    cc = star_lib.factors_to_coeffs(scl.facs_at_n(c.fac["c"], n))
    xv = [scl.peval(p, n) for p in xnum]
    lhs = star_lib.poly_sub(star_lib.poly_mul(ac, star_lib.poly_shift(xv, 1)),
                            star_lib.poly_mul(star_lib.poly_shift(bc, -1), xv))
    pasum = star_lib.poly_lin([
        (scl.peval(atil[j], n),
         star_lib.factors_to_coeffs(scl.facs_at_n(c.fac["Pa%d" % j], n)))
        for j in range(c.J + 1)
    ])
    return star_lib.poly_sub(lhs, star_lib.poly_mul(cc, pasum))


def namespace_of(c):
    return "StarForall" + c.side.replace("-", "").replace("_", "").title()


# ─────────────────────────── the file SECTIONS ───────────────────────────────
# Factored out of `emit` so that `emit_modules` can compose the SAME bytes into a
# different file layout.  There is deliberately no second copy of any of these:
# zeta2-star-b1.md Sec15.3 measured the consolidated single-file form at +1.43 GB
# per witness, so the modular layout is not an alternative rendering but the only
# one that scales -- and two emitters that could drift would put the scaling
# route on unchecked bytes.  `check_star_coords.py`'s byte-identity arm over the
# committed single-file record artifact is what pins that they have not drifted.


def _write_prelude(f, c, coords_name, gcd_used, xdeg, D, L, ns):
    f.write("import Mathlib.Analysis.Polynomial.Basic\n")
    f.write("import Mathlib.Tactic\n\n")
    f.write(
            "/-!\n"
            "# (★) for EVERY `n`, from the engine's symbolic coordinates — %s\n\n"
            "GENERATED by `external_tests/zeta2_star_b1/star_forall_to_lean.py` from\n"
            "`%s`, itself the output of\n\n"
            "    build/mb_pipeline starcoords %s\n\n"
            "Do not edit by hand: re-run the generator.  It re-verifies the cleared residual\n"
            "in exact rational arithmetic at more integer `n` than the degree bound below\n"
            "before emitting, and REFUSES on a nonzero one.\n\n"
            "## What is here\n\n"
            "`F t : ℚ[X]` is the CLEARED (★) residual as a polynomial in `n`, with the\n"
            "contour variable `t` a parameter.  It is UNEXPANDED — a product/sum expression,\n"
            "never a monomial list.  `dx = %d`, `J = %d`, %d coordinates, common denominator\n"
            "of `n`-degree %d (%s), certificate `n`-degree ≤ %d.\n\n"
            "`hdeg : (F t).natDegree ≤ %d` is PROVED structurally, by the same arithmetic the\n"
            "generator used to choose the bound — not quoted from a document.\n\n"
            "Lines exceed 100 columns: a single coefficient does.\n-/\n\n"
            % (c.side, coords_name, c.side, c.dx, c.J, len(c.coords), scl.pdeg(L),
               "widest B_k, verified to be a common multiple" if gcd_used == 0
               else "lcm, %d gcd step(s)" % gcd_used,
               xdeg, D)
    )
    f.write(PRELUDE.replace("@NS@", ns))
    f.write("\nset_option maxRecDepth 8000000\n")
    f.write("set_option maxHeartbeats 0\n\n")


def _write_data(f, c, xnum, atil, literal=False):
    f.write("/-! ## The engine's data -/\n\n")
    for name in ("a", "b", "c"):
        f.write("noncomputable def %sFacs : List (ℚ × ℚ × ℚ) := %s\n\n"
                % (name, facs_lit(c.fac[name])))
    for j in range(c.J + 1):
        f.write("noncomputable def pa%dFacs : List (ℚ × ℚ × ℚ) := %s\n\n"
                % (j, facs_lit(c.fac["Pa%d" % j])))
    f.write("/-- The certificate's CLEARED coefficients `Xₖ(n) = Aₖ(n)·(L/Bₖ)(n)`,\n"
            "`k = 0..%d`, each a dense coefficient list in `n`. -/\n" % c.dx)
    if literal:
        # LEVER (a) of zeta2-star-b1.md Sec17.6: each coefficient list gets a NAME, so that a
        # shard can state `(polB xcK).eval n = <literal>` as its own lemma and `ring` never
        # sees a Horner chain.  `xCoeffs` is then a list of names, not of literals; nothing
        # downstream changes shape.
        #
        # ROW PAIR-K2: the NAME's body is an INTEGER list over one denominator, not a list of
        # ℚ literals.  `xcₖ` is still a `List ℚ` of exactly the same values, so `xCoeffs`,
        # `F`, `F_def`, `hdeg`'s statement, `grid`, `hs` and `star_forall_of_h0` are unchanged
        # to the character; what changes is that a kernel shard can evaluate the list over ℤ
        # (`StarKernel.qeval_map_of_kernel`) instead of over ℚ -- MEASURED-buildbox 2026-09-11
        # at ~10x per kernel op, and that one data fact was 110 s of a 125 s point.
        for k, p in enumerate(xnum):
            zs, d = _clear_list(p)
            f.write("def xz%d : List ℤ := %s\n\n" % (k, _zints(zs)))
            f.write("def xd%d : ℤ := %d\n\n" % (k, d))
            # `hdeg`'s length fact reaches the list through `List.length_map`, and it must NOT
            # reach the ENTRIES: with `xz%d` itself in that simp set, `List.map_cons` unfolds the
            # mapped list before `List.length_map` can fire and simp then walks 273 rational
            # divisions per list to count them.  MEASURED-buildbox 2026-09-12: that spelling put
            # the candidate-scale base past 11 min against its 5:22 under the ℚ encoding.  This
            # lemma is the length by itself -- `rfl` reads the SPINE, never a coefficient.
            f.write("theorem xzl%d : xz%d.length = %d := rfl\n\n" % (k, k, len(zs)))
            # Proved ONCE in the base, not per point: `qeval_map_of_kernel` needs it for every
            # shard, and it is a property of the base's own data.
            f.write("theorem xdne%d : ((xd%d : ℤ) : ℚ) ≠ 0 := by decide +kernel\n\n" % (k, k))
            f.write("noncomputable def xc%d : List ℚ :=\n"
                    "  xz%d.map (fun c : ℤ => (c : ℚ) / (xd%d : ℚ))\n\n" % (k, k, k))
        f.write("noncomputable def xCoeffs : List (List ℚ) :=\n  [%s]\n\n"
                % ", ".join("xc%d" % k for k in range(len(xnum))))
    else:
        f.write("noncomputable def xCoeffs : List (List ℚ) :=\n  [%s]\n\n"
                % ",\n   ".join(list_lit(p) for p in xnum))
    for j in range(c.J + 1):
        f.write("/-- The cleared recurrence coefficient `Ã%d(n) = A(n)·(L/B)(n)`. -/\n" % j)
        f.write("noncomputable def al%d : List ℚ := %s\n\n" % (j, list_lit(atil[j])))


def _write_f_hdeg(f, c, xnum, atil, D, xdeg, literal=False):
    # Under the LITERAL encoding `xCoeffs` is a list of NAMES, so the length fact behind `hx`
    # needs the names unfolded too; the default encoding's simp set is unchanged byte for byte.
    # Row PAIR-K2 adds one link to that chain and NOTHING else in the file: `xcₖ` is now
    # `xzₖ.map _`, so the length goes through `List.length_map` (already `@[simp]`; naming it
    # here draws an `unusedSimpArgs` warning, MEASURED 2026-09-12) to `xzₖ.length`, and stops
    # there at the one-line `xzlₖ`.  The `xzₖ` NAMES are deliberately ABSENT: with them present
    # simp unfolds the mapped list and counts 273 rational divisions per list instead of reading
    # a spine, which measured 11+ min of base against 5:22.  `hdeg`'s STATEMENT is untouched --
    # this is its simp set, which is part of the encoding.
    xc_simp = ("xCoeffs, "
               + ", ".join("xc%d" % k for k in range(len(xnum)))
               + ", " + ", ".join("xzl%d" % k for k in range(len(xnum)))) if literal else "xCoeffs"
    f.write("/-! ## `F` and its degree bound -/\n\n")
    f.write("/-- The CLEARED (★) residual, as a polynomial in `n` with `t` a parameter.\n"
            "UNEXPANDED: every product stays a product. -/\n")
    rhs_sum = "\n        + ".join("polB al%d * afProd pa%dFacs t" % (j, j)
                                  for j in range(c.J + 1))
    f.write("noncomputable def F (t : ℚ) : ℚ[X] :=\n"
            "  afProd aFacs t * polB2 xCoeffs (t + 1)\n"
            "    - afProd bFacs (t - 1) * polB2 xCoeffs t\n"
            "    - afProd cFacs t * (%s)\n\n" % rhs_sum)
    # `F`'s unfolding as an ORDINARY theorem, not as simp's on-demand equation
    # lemma.  MEASURED-buildbox 2026-09-09, and it is what makes the MODULAR
    # layout possible at all: across a module import, `simp only [F]` hits
    # `maximum recursion depth has been reached` in ~3 s at BOTH record and
    # candidate scale -- localized to `F` alone, since `simp only [xCoeffs]` and
    # `simp only [afProd_eval, polB2_eval, polB_eval]` are each GREEN across the
    # same import.  `rfl` goes through defeq instead and is green, so a shard
    # never unfolds `F`; it rewrites with a theorem ABOUT `F`.  The single-file
    # layout uses the same route, so the two layouts cannot diverge in the one
    # place that was measured to matter.
    f.write("/-- `F`'s unfolding, stated as a theorem so that a module which IMPORTS this\n"
            "one can rewrite with it.  `simp only [F]` across an import exhausts the\n"
            "recursion budget; `rfl` does not. -/\n")
    f.write("theorem F_def (t : ℚ) : F t =\n"
            "    afProd aFacs t * polB2 xCoeffs (t + 1)\n"
            "      - afProd bFacs (t - 1) * polB2 xCoeffs t\n"
            "      - afProd cFacs t * (%s) := rfl\n\n" % rhs_sum)
    # THE STEP BUDGET IS PART OF THE ENCODING, NOT A SAFETY MARGIN.  Each of the
    # `simp`s below proves a LENGTH fact about a literal list, so its step count
    # scales with the DATA: `xCoeffs` is 76 lists of <=125 entries at record scale
    # and 142 of <=273 at candidate scale.  MEASURED-buildbox 2026-09-09: the bare
    # `simp [xCoeffs]` that closes it at record scale dies at candidate scale with
    # `maximum number of steps exceeded` at 3:24 into the base module -- and the
    # file still ends by REPORTING `hdeg` as depending on `sorryAx`, because a
    # failed tactic leaves a sorry behind and `#print axioms` faithfully says so.
    # That is why the axiom receipt is read and not just emitted.
    f.write("theorem hdeg (t : ℚ) : (F t).natDegree ≤ %d := by\n" % D)
    f.write("  have hx : ∀ s : ℚ, (polB2 xCoeffs s).natDegree ≤ %d :=\n"
            "    fun s => polB2_natDegree_le xCoeffs s %d (by simp (maxSteps := %d) [%s])\n"
            % (xdeg, xdeg, SIMP_STEPS, xc_simp))
    for name in ("a", "b", "c"):
        f.write("  have h%s : ∀ t : ℚ, (afProd %sFacs t).natDegree ≤ %d :=\n"
                "    fun t => nd_le (afProd_natDegree_le %sFacs t) "
                "(by simp (maxSteps := %d) [%sFacs])\n"
                % (name, name, facs_count(c.fac[name]), name, SIMP_STEPS, name))
    for j in range(c.J + 1):
        f.write("  have hp%d : (afProd pa%dFacs t).natDegree ≤ %d :=\n"
                "    nd_le (afProd_natDegree_le pa%dFacs t) "
                "(by simp (maxSteps := %d) [pa%dFacs])\n"
                % (j, j, facs_count(c.fac["Pa%d" % j]), j, SIMP_STEPS, j))
        f.write("  have hal%d : (polB al%d).natDegree ≤ %d :=\n"
                "    polB_natDegree_le al%d %d (by simp (maxSteps := %d) [al%d])\n"
                % (j, j, len(atil[j]) - 1, j, len(atil[j]) - 1, SIMP_STEPS, j))
    rhs_bound = max((len(atil[j]) - 1) + facs_count(c.fac["Pa%d" % j])
                    for j in range(c.J + 1))
    for j in range(c.J + 1):
        f.write("  have hm%d : (polB al%d * afProd pa%dFacs t).natDegree ≤ %d :=\n"
                "    nd_le (nd_mul hal%d hp%d) (by norm_num)\n"
                % (j, j, j, rhs_bound, j, j))
    # `nd_add` is binary and the sum is left-nested, so the application has to
    # be nested the same way: `nd_add (nd_add (nd_add hm0 hm1) hm2) hm3`.
    acc = "hm0"
    for j in range(1, c.J + 1):
        acc = "nd_add (%s) hm%d" % (acc, j) if j > 1 else "nd_add %s hm%d" % (acc, j)
    f.write("  have hsum : (%s).natDegree ≤ %d :=\n    %s\n"
            % ("\n        + ".join("polB al%d * afProd pa%dFacs t" % (j, j)
                                   for j in range(c.J + 1)),
               rhs_bound, acc))
    f.write("  show (afProd aFacs t * polB2 xCoeffs (t + 1)\n"
            "    - afProd bFacs (t - 1) * polB2 xCoeffs t\n"
            "    - afProd cFacs t * (%s)).natDegree ≤ %d\n"
            % ("\n        + ".join("polB al%d * afProd pa%dFacs t" % (j, j)
                                   for j in range(c.J + 1)), D))
    f.write("  exact nd_sub (nd_sub (nd_le (nd_mul (ha t) (hx (t + 1))) (by norm_num))\n"
            "      (nd_le (nd_mul (hb (t - 1)) (hx t)) (by norm_num)))\n"
            "    (nd_le (nd_mul (hc t) hsum) (by norm_num))\n\n")


def _write_grid(f, D):
    f.write("/-! ## The grid -/\n\n")
    f.write("/-- The first %d natural numbers, as a `Finset ℚ`. -/\n" % (D + 1))
    f.write("noncomputable def grid : Finset ℚ :=\n"
            "  (Finset.range %d).image (fun k : ℕ => (k : ℚ))\n\n" % (D + 1))
    f.write("theorem hcard : grid.card = %d := by\n"
            "  rw [grid, Finset.card_image_of_injective _ (Nat.cast_injective (R := ℚ)),"
            " Finset.card_range]\n\n" % (D + 1))
    f.write("theorem hs : %d < grid.card := by rw [hcard]; omega\n\n" % D)


def unfold_set(c):
    """The `simp only` set `h0` is closed with.

    The eval LEMMAS, not the definitions: `afProd_eval` / `polB2_eval` /
    `polB_eval` turn each object into ONE `List.foldr` instead of unfolding a
    Horner chain through `eval_add`/`eval_mul`/`eval_C` per literal.  The step
    budget is raised because the identity has ~10⁴–10⁵ literals and simp's
    default 100 000 counts congruences too.

    `F_def` and not `F`, for the reason recorded beside its emission: unfolding
    the DEFINITION across a module import exhausts the recursion budget, while
    rewriting with a theorem about it does not.
    """
    return ("F_def, eval_sub, eval_add, eval_mul, afProd_eval, polB2_eval, polB_eval,\n"
            "    aFacs, bFacs, cFacs, %s, xCoeffs, %s,\n"
            "    List.foldr_cons, List.foldr_nil"
            % (", ".join("pa%dFacs" % j for j in range(c.J + 1)),
               ", ".join("al%d" % j for j in range(c.J + 1))))


def _write_h0(f, c, points):
    f.write("/-! ## The per-point vanishing -/\n\n")
    unfold = unfold_set(c)
    for n in points:
        f.write("theorem h0_%d (t : ℚ) : (F t).eval (%d : ℚ) = 0 := by\n"
                "  simp (maxSteps := %d) only [%s]\n"
                "  ring\n\n" % (n, n, SIMP_STEPS, unfold))


def emit(c, L, xnum, atil, D, points, out, coords_name, gcd_used, unconditional):
    ns = namespace_of(c)
    xdeg = max(len(p) - 1 for p in xnum)
    with open(out, "w") as f:
        _write_prelude(f, c, coords_name, gcd_used, xdeg, D, L, ns)
        _write_data(f, c, xnum, atil)
        _write_f_hdeg(f, c, xnum, atil, D, xdeg)
        _write_grid(f, D)
        _write_h0(f, c, points)
        if unconditional:
            f.write("theorem h0_all (t : ℚ) : ∀ v ∈ grid, (F t).eval v = 0 := by\n"
                    "  intro v hv\n"
                    "  simp only [grid, Finset.mem_image, Finset.mem_range] at hv\n"
                    "  obtain ⟨k, hk, rfl⟩ := hv\n"
                    "  interval_cases k\n")
            for n in points:
                f.write("  · simpa using h0_%d t\n" % n)
            f.write("\n/-- **(★) at EVERY `n` and every `t`, at %s scale.**  The grid principle,\n"
                    "applied to a residual polynomial the engine's own symbolic coordinates\n"
                    "produced. -/\n" % c.side)
            f.write("theorem star_forall (t : ℚ) : ∀ v : ℚ, (F t).eval v = 0 :=\n"
                    "  star_forall_of_grid (F t) %d (hdeg t) grid hs (h0_all t)\n\n" % D)
        else:
            f.write("/-- The `∀ n` step, with the per-point vanishing as its ONE remaining\n"
                    "hypothesis.  Stated as typed Lean rather than as a sentence: everything\n"
                    "`star_forall_of_grid` needs except `h0` is discharged above. -/\n")
            f.write("theorem star_forall_of_h0 (t : ℚ) (h0 : ∀ v ∈ grid, (F t).eval v = 0) :\n"
                    "    ∀ v : ℚ, (F t).eval v = 0 :=\n"
                    "  star_forall_of_grid (F t) %d (hdeg t) grid hs h0\n\n" % D)
        f.write("end %s\n\n" % ns)
        f.write("#print axioms %s.hdeg\n" % ns)
        f.write("#print axioms %s.hs\n" % ns)
        for n in points[:2]:
            f.write("#print axioms %s.h0_%d\n" % (ns, n))
        if points[2:]:
            f.write("#print axioms %s.h0_%d\n" % (ns, points[-1]))
        if unconditional:
            f.write("#print axioms %s.star_forall\n" % ns)
        else:
            f.write("#print axioms %s.star_forall_of_h0\n" % ns)
    return ns


# ───────────────────────────── the MODULAR layout ────────────────────────────


def _write_h0_literal(f, c, xnum, atil, n):
    """LEVER (a), zeta2-star-b1.md Sec17.6: the per-point proof with every `Xₖ(n)` and
    `Ãⱼ(n)` EVALUATED TO A LITERAL in its own lemma, by `norm_num` over the named list, so
    the closing `ring` sees a polynomial identity in `t` with literal coefficients and never a
    Horner chain in `n`.  The literals are computed here in exact rational arithmetic
    (`scl.peval`), which is the same arithmetic the residual gate verified the data with, and
    Lean re-derives each one from the list — a wrong literal is a RED lemma, not a wrong proof.

    `polB_eval` is deliberately ABSENT from the closing simp set: with it present simp could
    unfold `(polB xcK).eval n` into the chain before the literal lemma fires, and the lever
    would be silently undone.

    ROW PAIR-K2: `xcK` is now `xzK.map (fun c : ℤ => (c : ℚ) / (xdK : ℚ))`, so `xv_k`'s simp
    set gains what it takes to reach the entries: `xzK`, `xdK` and `List.map_cons`/`_nil`.
    The entries themselves are the same rationals -- `rat_lit` already wrote every one of them
    as a division -- so the `norm_num` that closes the lemma sees the same arithmetic."""
    lits_x = [scl.peval(p, n) for p in xnum]
    lits_a = [scl.peval(atil[j], n) for j in range(c.J + 1)]
    for k, v in enumerate(lits_x):
        f.write("theorem xv_%d : (polB xc%d).eval (%d : ℚ) = %s := by\n"
                "  rw [polB_eval]\n"
                "  simp (maxSteps := %d) only [xc%d, xz%d, xd%d, List.map_cons, List.map_nil,\n"
                "    List.foldr_cons, List.foldr_nil]\n"
                "  all_goals norm_num\n\n"
                % (k, k, n, rat_lit(v), SIMP_STEPS, k, k, k))
    for j, v in enumerate(lits_a):
        f.write("theorem av_%d : (polB al%d).eval (%d : ℚ) = %s := by\n"
                "  rw [polB_eval]\n"
                "  simp (maxSteps := %d) only [al%d, List.foldr_cons, List.foldr_nil]\n"
                "  all_goals norm_num\n\n" % (j, j, n, rat_lit(v), SIMP_STEPS, j))
    closing = ("F_def, eval_sub, eval_add, eval_mul, afProd_eval, polB2_eval,\n"
               "    aFacs, bFacs, cFacs, %s, xCoeffs,\n"
               "    List.foldr_cons, List.foldr_nil,\n"
               "    %s,\n    %s"
               % (", ".join("pa%dFacs" % j for j in range(c.J + 1)),
                  ", ".join("xv_%d" % k for k in range(len(xnum))),
                  ", ".join("av_%d" % j for j in range(c.J + 1))))
    f.write("theorem h0_%d (t : ℚ) : (F t).eval (%d : ℚ) = 0 := by\n"
            "  simp (maxSteps := %d) only [%s]\n"
            "  ring\n\n" % (n, n, SIMP_STEPS, closing))


def kernel_point(c, xnum, atil, n):
    """The ℤ-cleared (★) data at integer `n`, FROM THE COORDS — the literals of a kernel shard.

    `L := lcm(den Xₖ(n))`, `M := lcm(den Ãⱼ(n))`, `xL := L·X(n)`, `mⱼ := M·Ãⱼ(n)`, and the
    factor multisets at `n` flattened by multiplicity with `off := a·n + b` (`off − lead` for
    `b(t − 1)`).  The same `Xₖ`/`Ãⱼ` the base module's `xCoeffs`/`alⱼ` carry, evaluated at
    `n` — so the shard's data facts (`xCoeffs.map (qeval n) = xL.map (zdiv L)`, …) are
    identities the kernel decides, and the archived per-point dumps are NOT an input here
    (they cross-check the coords through `check_star_encoding.py`, a different arm).

    REFUSES on a nonzero ℤ residual — computed with `star_lib.zp_*`, the mirror of the Lean
    kernel ops (LEAN.md §6 layer 2), which is a different implementation from the
    `residual_at` gate's Fraction algebra above.
    """
    def flat(name, shift=0):
        out = []
        for lead, off, mult in scl.facs_at_n(c.fac[name], n):
            out.extend([(lead, off + shift * lead)] * mult)
        return out
    fa, fb1, fc = flat("a"), flat("b", -1), flat("c")
    fpa = [flat("Pa%d" % j) for j in range(c.J + 1)]
    xv = [scl.peval(p, n) for p in xnum]
    av = [scl.peval(atil[j], n) for j in range(c.J + 1)]
    L = 1
    for v in xv:
        L = lcm(L, v.denominator)
    M = 1
    for v in av:
        M = lcm(M, v.denominator)
    xL = [int(v * L) for v in xv]
    aM = [int(v * M) for v in av]
    lhs, rhs = star_lib.zp_star_sides(L, M, fa, fb1, fc, xL, aM, fpa)
    if star_lib.zp_trim(star_lib.zp_sub(lhs, rhs)):
        raise SystemExit("star_forall_to_lean: REFUSING TO EMIT — the ℤ-cleared (★) residual at "
                         "n=%d is NONZERO under the kernel-op mirror" % n)
    # ROW PAIR-K2.  The per-list ℤ clearing the BASE carries (`xzₖ`, `xdₖ`) has to reproduce
    # this point's `xLₖ` through the kernel's own Horner: `hornerZ xzₖ n · L = xLₖ · xdₖ`.
    # That is the statement each shard hands to `decide +kernel`, so it is re-derived here in
    # Python and REFUSED if it fails — a wrong clearing must not become a Lean goal nobody
    # can close, and must never become one that is false and closes anyway.
    for k, (zs, d) in enumerate(_clear_list(p) for p in xnum):
        hz = 0
        for cf in reversed(zs):
            hz = cf + n * hz
        if hz * L != xL[k] * d:
            raise SystemExit("star_forall_to_lean: REFUSING TO EMIT — the integer coefficient "
                             "list xz%d does not reproduce xL[%d] at n=%d" % (k, k, n))
    digits = max(len(str(abs(v))) for v in lhs) if lhs else 0
    return dict(L=L, M=M, fa=fa, fb1=fb1, fc=fc, fpa=fpa, xL=xL, aM=aM, digits=digits)


def _zpairs(facs):
    return "[" + ", ".join("(%d, %d)" % (l, o) for l, o in facs) + "]"


def _zints(vals):
    return "[" + ", ".join(str(v) for v in vals) + "]"


def _write_h0_kernel(f, c, xnum, atil, n):
    """PAIR-K's encoding: the point's (★) identity, cleared to ℤ, decided by the KERNEL over
    `StarKernel.ZP` (`decide +kernel`), plus the ℚ↔ℤ data facts (also kernel-decided) and ONE
    application of `StarKernel.h0_of_kernel` — the generic bridge in `StarKernelBridge.lean`,
    which the shard imports beside the base.  No `ring`, no `norm_num` on the data.

    Every name carries `_n`, so all D+1 shards can be imported into ONE module (the literal
    encoding's `xv_k`/`av_j` collide across shards — measured 2026-09-11, see the row).

    ROW PAIR-K2.  The one expensive data fact, `khX_n`, no longer goes to the kernel over ℚ: the
    base carries each coefficient list as `xzₖ : List ℤ` over `xdₖ : ℤ`, so this writes one ℤ
    kernel fact per list (`kzx<k>_n`), lifts each with the bridge's generic
    `qeval_map_of_kernel`, and assembles the SAME `khX_n` statement by `simp only`.  Nothing
    `h0_of_kernel` sees changes; what changes is which ring the kernel computes in.
    """
    k = kernel_point(c, xnum, atil, n)
    assert c.J == 3, "the kernel shard's identity is written for J = 3 (StarKernel.h0_of_kernel)"
    f.write("/-! ## The point's data, cleared to ℤ\n\n`L = lcm(den Xₖ(%d))` (%d digits), "
            "`M = lcm(den Ãⱼ(%d))` (%d digits); largest coefficient of the cleared identity "
            "%d digits. -/\n\n" % (n, len(str(k["L"])), n, len(str(k["M"])), k["digits"]))
    f.write("def kL_%d : ℤ := %d\ndef kM_%d : ℤ := %d\n\n" % (n, k["L"], n, k["M"]))
    f.write("def kaF_%d : List (ℤ × ℤ) := %s\n\n" % (n, _zpairs(k["fa"])))
    f.write("def kbF_%d : List (ℤ × ℤ) := %s\n\n" % (n, _zpairs(k["fb1"])))
    f.write("def kcF_%d : List (ℤ × ℤ) := %s\n\n" % (n, _zpairs(k["fc"])))
    for j in range(c.J + 1):
        f.write("def kp%dF_%d : List (ℤ × ℤ) := %s\n\n" % (j, n, _zpairs(k["fpa"][j])))
    # ROW PAIR-K2: each cleared coefficient gets its own NAME, so `kzx<k>` (the ℤ Horner fact)
    # and `kxL` (the identity's list) quote ONE literal, never two copies that could drift.
    for kk, v in enumerate(k["xL"]):
        f.write("def kx%d_%d : ℤ := %d\n" % (kk, n, v))
    f.write("\ndef kxL_%d : List ℤ :=\n  [%s]\n\n"
            % (n, ", ".join("kx%d_%d" % (kk, n) for kk in range(len(k["xL"])))))
    for j in range(c.J + 1):
        f.write("def km%d_%d : ℤ := %d\n" % (j, n, k["aM"][j]))
    f.write("\n/-! ## The kernel identity -/\n\n")
    f.write("theorem kker_%d : StarKernel.ztrim (StarKernel.zsub\n"
            "    (StarKernel.zscale kM_%d (StarKernel.zsub\n"
            "      (StarKernel.zmul (StarKernel.zprod kaF_%d) (StarKernel.zshift1 kxL_%d))\n"
            "      (StarKernel.zmul (StarKernel.zprod kbF_%d) kxL_%d)))\n"
            "    (StarKernel.zscale kL_%d (StarKernel.zmul (StarKernel.zprod kcF_%d)\n"
            "      (StarKernel.zadd\n"
            "        (StarKernel.zadd (StarKernel.zscale km0_%d (StarKernel.zprod kp0F_%d))\n"
            "                         (StarKernel.zscale km1_%d (StarKernel.zprod kp1F_%d)))\n"
            "        (StarKernel.zadd (StarKernel.zscale km2_%d (StarKernel.zprod kp2F_%d))\n"
            "                         (StarKernel.zscale km3_%d (StarKernel.zprod kp3F_%d))))))) "
            "= [] := by\n  decide +kernel\n\n"
            % (n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n))
    f.write("/-! ## The data facts: the base module's ℚ lists at `n = %d` ARE the ℤ literals -/\n\n"
            % n)
    f.write("theorem khA_%d : aFacs.map (StarKernel.qfac %d) = kaF_%d.map StarKernel.zfac := by\n"
            "  decide +kernel\n" % (n, n, n))
    f.write("theorem khB_%d : bFacs.map (StarKernel.qfacs %d) = kbF_%d.map StarKernel.zfac := by\n"
            "  decide +kernel\n" % (n, n, n))
    f.write("theorem khC_%d : cFacs.map (StarKernel.qfac %d) = kcF_%d.map StarKernel.zfac := by\n"
            "  decide +kernel\n" % (n, n, n))
    for j in range(c.J + 1):
        f.write("theorem khP%d_%d : pa%dFacs.map (StarKernel.qfac %d) = kp%dF_%d.map StarKernel.zfac "
                ":= by\n  decide +kernel\n" % (j, n, j, n, j, n))
    # The two clearing denominators are nonzero BEFORE the coefficient facts, because row
    # PAIR-K2's `khx<k>` consume `khL_<n>` (a Lean file is read top-down).
    f.write("theorem khL_%d : (kL_%d : ℚ) ≠ 0 := by decide +kernel\n" % (n, n))
    f.write("theorem khM_%d : (kM_%d : ℚ) ≠ 0 := by decide +kernel\n\n" % (n, n))
    # ROW PAIR-K2.  `khX` was ONE `decide +kernel` over ℚ and was 110 s of a 125 s point: 121
    # Horner chains of ~270 rationals whose entries carry 173-207-digit denominators, and a
    # kernel `Rat` op is ~10x a kernel `Int` op.  It is now 121 kernel facts over **ℤ**
    # (`kzx<k>`), each lifted to its ℚ form by the generic `StarKernel.qeval_map_of_kernel`
    # (one list induction, proved once in the bridge), and assembled into the SAME statement
    # `h0_of_kernel` consumes — the theorem's type is unchanged to the character.
    f.write("theorem khn_%d : (((%d : ℤ)) : ℚ) = (%d : ℚ) := by norm_num\n\n" % (n, n, n))
    for kk in range(len(k["xL"])):
        f.write("theorem kzx%d_%d : StarKernel.hornerZ xz%d (%d : ℤ) * kL_%d = kx%d_%d * xd%d "
                ":= by\n  decide +kernel\n" % (kk, n, kk, n, n, kk, n, kk))
    f.write("\n")
    for kk in range(len(k["xL"])):
        f.write("theorem khx%d_%d : StarKernel.qeval (%d : ℚ) xc%d "
                "= StarKernel.zdiv kL_%d kx%d_%d :=\n"
                "  StarKernel.qeval_map_of_kernel xz%d xd%d kL_%d kx%d_%d %d (%d : ℚ) "
                "khn_%d xdne%d khL_%d kzx%d_%d\n"
                % (kk, n, n, kk, n, kk, n, kk, kk, n, kk, n, n, n, n, kk, n, kk, n))
    f.write("\ntheorem khX_%d : xCoeffs.map (StarKernel.qeval %d) = kxL_%d.map (StarKernel.zdiv kL_%d) "
            ":= by\n  simp (maxSteps := %d) only [xCoeffs, kxL_%d, List.map_cons, List.map_nil,\n"
            "    %s]\n"
            % (n, n, n, n, SIMP_STEPS, n,
               ", ".join("khx%d_%d" % (kk, n) for kk in range(len(k["xL"])))))
    for j in range(c.J + 1):
        f.write("theorem kha%d_%d : StarKernel.qeval %d al%d = StarKernel.zdiv kM_%d km%d_%d := by\n"
                "  decide +kernel\n" % (j, n, n, j, n, j, n))
    f.write("\n/-! ## The point -/\n\n")
    f.write("theorem h0_%d (t : ℚ) : (F t).eval (%d : ℚ) = 0 := by\n"
            "  simp only [F_def, eval_sub, eval_mul, eval_add, afProd_eval, polB2_eval, polB_eval]\n"
            "  exact StarKernel.h0_of_kernel khL_%d khM_%d khA_%d khB_%d khC_%d khP0_%d khP1_%d "
            "khP2_%d khP3_%d\n    khX_%d kha0_%d kha1_%d kha2_%d kha3_%d kker_%d\n\n"
            % ((n, n) + (n,) * 15))


# Shard file-name letter per encoding: the kernel shards are a DIFFERENT file family from
# the `ring`/`literal` ones (same theorem `h0_n`, different proof, different imports), so
# they never overwrite a committed `P<n>` shard and a manifest names which family it holds.
SHARD_LETTER = {"ring": "P", "literal": "P", "kernel": "K"}


def emit_modules(c, L, xnum, atil, D, points, outdir, coords_name, gcd_used, base_mod,
                 encoding="ring"):
    """One BASE module carrying `F`/`hdeg`/`grid`/`hs`, one module per grid point.

    WHY THIS EXISTS AND THE SINGLE FILE DOES NOT SCALE.  zeta2-star-b1.md Sec15.3
    measured the consolidated single-file form at **+1.43 GB per witness, flat**
    (24.51 GB at 12, 41.62 GB at 24), against a modular layout that is **flat at
    3.18 GB**; Sec16.4 reproduced the same slope in the `h0` layer itself
    (+1.375 GB per point at RECORD scale).  277 points in one file is therefore
    not a large elaboration, it is an impossible one -- and no amount of
    `maxHeartbeats` fixes a memory law.

    The split is exactly where the cost is: everything that is elaborated ONCE
    (the ~16 MB of engine data, `F`, the structural `hdeg`, the grid, and the
    `star_forall_of_grid` application modulo `h0`) goes in the base and becomes
    one `.olean`; each point's `simp`+`ring` -- the only per-point work -- gets
    its own module and its own process, so peak memory is per-shard and the run
    is embarrassingly parallel.

    A shard IMPORTS the base rather than re-stating it, so the two can never
    disagree about what `F` is; and it inherits `import Mathlib.Tactic` through
    that import, which Sec15.7 measured at +29% peak over a bare shard.  That is
    the reason the recommended concurrency width is 6-7 and not 9.
    """
    ns = namespace_of(c)
    xdeg = max(len(p) - 1 for p in xnum)
    # The KERNEL encoding keeps the base module BYTE-IDENTICAL to the literal one (named
    # `xc<k>` lists, same `F`/`hdeg`): a kernel grid re-uses the base olean the literal grid
    # compiled, and one manifest line pins both families to the same base.
    literal = encoding in ("literal", "kernel")
    kernel = encoding == "kernel"
    written = []
    base_path = os.path.join(outdir, base_mod + ".lean")
    with open(base_path, "w") as f:
        _write_prelude(f, c, coords_name, gcd_used, xdeg, D, L, ns)
        _write_data(f, c, xnum, atil, literal=literal)
        _write_f_hdeg(f, c, xnum, atil, D, xdeg, literal=literal)
        _write_grid(f, D)
        f.write("/-- The `∀ n` step, with the per-point vanishing as its ONE remaining\n"
                "hypothesis.  Each `h0` point is proved in its OWN module against this one. -/\n")
        f.write("theorem star_forall_of_h0 (t : ℚ) (h0 : ∀ v ∈ grid, (F t).eval v = 0) :\n"
                "    ∀ v : ℚ, (F t).eval v = 0 :=\n"
                "  star_forall_of_grid (F t) %d (hdeg t) grid hs h0\n\n" % D)
        f.write("end %s\n\n" % ns)
        f.write("#print axioms %s.hdeg\n" % ns)
        f.write("#print axioms %s.hcard\n" % ns)
        f.write("#print axioms %s.hs\n" % ns)
        f.write("#print axioms %s.star_forall_of_h0\n" % ns)
    written.append(base_path)

    unfold = unfold_set(c)
    for n in points:
        mod = "%s%s%d" % (base_mod[:-4] if base_mod.endswith("Base") else base_mod,
                          SHARD_LETTER[encoding], n)
        p = os.path.join(outdir, mod + ".lean")
        with open(p, "w") as f:
            f.write("import %s\n" % base_mod)
            if kernel:
                f.write("import StarKernelBridge\n")
            f.write("\n/-!\n# (★) vanishes at `n = %d` — one %sSHARD of the %s grid\n\n"
                    "GENERATED by `external_tests/zeta2_star_b1/star_forall_to_lean.py`%s.\n"
                    "One of the %d modules `star_forall_of_h0` needs; every other input it\n"
                    "takes (`F`, `hdeg`, `grid`, `hs`) is proved once in `%s`.%s\n-/\n\n"
                    % (n, "KERNEL " if kernel else "", c.side,
                       " --h0-encoding kernel" if kernel else "", D + 1, base_mod,
                       "\nThe identity is decided by the KERNEL over `List ℤ` (row PAIR-K) and\n"
                       "bridged to `(F t).eval n = 0` by `StarKernel.h0_of_kernel`\n"
                       "(`StarKernelBridge.lean`, imported)." if kernel else ""))
            f.write("open Polynomial\n\n")
            f.write("set_option maxRecDepth 8000000\n")
            f.write("set_option maxHeartbeats 0\n\n")
            f.write("namespace %s\n\n" % ns)
            if kernel:
                _write_h0_kernel(f, c, xnum, atil, n)
            elif literal:
                _write_h0_literal(f, c, xnum, atil, n)
            else:
                f.write("theorem h0_%d (t : ℚ) : (F t).eval (%d : ℚ) = 0 := by\n"
                        "  simp (maxSteps := %d) only [%s]\n"
                        "  ring\n\n" % (n, n, SIMP_STEPS, unfold))
            f.write("end %s\n\n" % ns)
            f.write("#print axioms %s.h0_%d\n" % (ns, n))
        written.append(p)
    return ns, written


def emit_assembly(outdir, ns, D, points, base_mod, encoding, side):
    """The module that JOINS the shards: `h0_all` over the whole grid, then `star_forall`.

    WHY THIS EXISTS, and it is the row's own finding rather than a feature request.  Until
    2026-09-14 the modular layout emitted the base and the shards and nothing else, so a
    completed grid discharged `star_forall_of_h0`'s HYPOTHESES and produced no object.  278
    shards elaborate in 278 separate processes, hence 278 separate contexts; `#print axioms
    h0_277` is clean and says nothing whatever about `star_forall`, which had no referent.
    That is LEAN.md §1's "an axiom check on the WRONG theorem attests nothing" and §3's
    composition rule one level up: the pieces were proved with their neighbours absent.

    The single-file `emit()` has written both declarations since the beginning, behind
    `--unconditional`.  This is that code MOVED, not a new design -- the tactic skeleton
    below is the same one, and it has to be, or the two layouts would prove different
    theorems from the same coordinates.

    `star_forall` is built through the base's OWN `star_forall_of_h0` rather than by
    re-applying `star_forall_of_grid` here, so the grid principle is applied exactly once in
    the whole corpus and the assembly cannot disagree with the base about `hdeg`/`hs`.

    REFUSES ON A PARTIAL GRID.  `h0_all` quantifies over `grid`, whose card is `D+1`; a
    subset of points cannot prove it.  Emitting anyway would produce a file that fails to
    elaborate with an `interval_cases` goal nobody can read as "you asked for 24 of 278
    points", so the refusal is the error message.
    """
    if points != list(range(D + 1)):
        raise SystemExit(
            "star_forall_to_lean: REFUSING TO ASSEMBLE — `h0_all` quantifies over the whole "
            "grid (%d points) and only %d were emitted.  Re-run with `--points all`; a "
            "partial grid can discharge no `∀ v ∈ grid` statement." % (D + 1, len(points)))
    stem = base_mod[:-4] if base_mod.endswith("Base") else base_mod
    mod = stem + "Assemble"
    path = os.path.join(outdir, mod + ".lean")
    with open(path, "w") as f:
        f.write("import %s\n" % base_mod)
        for n in points:
            f.write("import %s%s%d\n" % (stem, SHARD_LETTER[encoding], n))
        f.write("\n/-!\n# (★) at EVERY `n` and every `t`, at %s scale — THE ASSEMBLY\n\n"
                "GENERATED by `external_tests/zeta2_star_b1/star_forall_to_lean.py "
                "--assemble`.\n\n"
                "The %d shard modules each prove `h0_n` in their own process and their own\n"
                "context.  This module is the only place they are in scope together, and so\n"
                "the only place `h0_all` — and therefore `star_forall` — can be stated at\n"
                "all.  A green grid is this module's HYPOTHESES; it is not this module.\n\n"
                "`star_forall` goes through `%s`'s own `star_forall_of_h0`, so\n"
                "`star_forall_of_grid` is applied ONCE in the corpus and this file cannot\n"
                "disagree with the base about `hdeg`, `grid` or `hs`.\n-/\n\n"
                % (side, D + 1, base_mod))
        f.write("open Polynomial\n\n")
        f.write("set_option maxRecDepth 8000000\n")
        f.write("set_option maxHeartbeats 0\n\n")
        f.write("namespace %s\n\n" % ns)
        f.write("/-- Every grid point vanishes — the %d shard results, joined. -/\n" % (D + 1))
        f.write("theorem h0_all (t : ℚ) : ∀ v ∈ grid, (F t).eval v = 0 := by\n"
                "  intro v hv\n"
                "  simp only [grid, Finset.mem_image, Finset.mem_range] at hv\n"
                "  obtain ⟨k, hk, rfl⟩ := hv\n"
                "  interval_cases k\n")
        for n in points:
            f.write("  · simpa using h0_%d t\n" % n)
        f.write("\n/-- **(★) at EVERY `n` and every `t`, at %s scale.**  The grid principle,\n"
                "applied to a residual polynomial the engine's own symbolic coordinates\n"
                "produced. -/\n" % side)
        f.write("theorem star_forall (t : ℚ) : ∀ v : ℚ, (F t).eval v = 0 :=\n"
                "  star_forall_of_h0 t (h0_all t)\n\n")
        f.write("end %s\n\n" % ns)
        f.write("#print axioms %s.h0_all\n" % ns)
        f.write("#print axioms %s.star_forall\n" % ns)
    return path


def write_manifest(paths, out, points_spec, encoding="literal", assemble=False):
    """A SHA-256 line per emitted module, sorted by name, under a `# points` line.

    THE POINT SPEC IS IN THE FILE, not in the caller's memory.  A manifest is only
    checkable by REGENERATING, and a regeneration at different `--points` produces
    a different module set -- so a checker told the wrong spec reports a red that
    means nothing, and a falsifier told the wrong spec passes every arm and fails
    its own restore control.  `falsify_star_coords.sh` carries a five-line comment
    warning about exactly that for the single-file layout; here the file answers
    the question instead of the comment asking the reader to.

    WHY A MANIFEST AND NOT THE FILE.  The base module is ~16 MB of engine data
    at candidate scale and is EXACTLY regenerable from the committed coords by
    this committed generator in ~90 s; zeta2-star-b1.md Sec12.7 rules that
    derived Lean of that size does not ship, and Sec13.6 already applies the same
    rule to the 71.8 MB of grid receipts with the same instrument -- a manifest
    is what makes a regeneration CHECKABLE rather than merely repeatable.  A
    hash arm is not weaker than a byte arm: it compares the same bytes.
    """
    lines = []
    for p in sorted(paths, key=os.path.basename):
        h = hashlib.sha256()
        with open(p, "rb") as f:
            for chunk in iter(lambda: f.read(1 << 20), b""):
                h.update(chunk)
        lines.append("%s  %s  %d\n" % (h.hexdigest(), os.path.basename(p), os.path.getsize(p)))
    with open(out, "w") as f:
        f.write("# points %s\n" % points_spec)
        # The ENCODING is in the file for the same reason the points are: a kernel manifest
        # regenerated at the literal encoding names `P<n>` shards it never listed.  Absent
        # line = `literal`, so every manifest written before 2026-09-11 reads as it did.
        if encoding != "literal":
            f.write("# encoding %s\n" % encoding)
        # And the ASSEMBLY, for the third time the same reason (2026-09-14): a manifest that
        # LISTS `<stem>Assemble.lean` but is regenerated without `--assemble` fails its own
        # byte-identity arm with a missing file, and the red means nothing about the bytes.
        # Absent line = not assembled, so every manifest written before today reads as it did.
        if assemble:
            f.write("# assemble 1\n")
        f.writelines(lines)
    return lines


def manifest_points(path):
    """The `--points` spec a manifest was written at, or None."""
    return _manifest_field(path, "points")


def manifest_encoding(path):
    """The `--h0-encoding` a manifest was written at; `literal` when the line is absent."""
    return _manifest_field(path, "encoding") or "literal"


def manifest_assemble(path):
    """Whether the manifest was written WITH `--assemble`; False when the line is absent."""
    return _manifest_field(path, "assemble") == "1"


def _manifest_field(path, key):
    with open(path) as f:
        for line in f:
            if line.startswith("# %s " % key):
                return line[len("# %s " % key):].strip()
            if not line.startswith("#"):
                return None
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--coords", required=True)
    ap.add_argument("--out", help="single-file layout: the .lean to write")
    ap.add_argument("--emit-modules", metavar="DIR",
                    help="MODULAR layout: write <DIR>/<base>.lean plus one <base-stem>P<n>.lean "
                         "per point.  This is the layout that scales (Sec15.3/Sec16.4: the "
                         "single file is +1.4 GB per witness, the modular one is flat).")
    ap.add_argument("--base-module", default=None,
                    help="module name for the base, default StarForall<Side>Base")
    ap.add_argument("--manifest", default=None,
                    help="where to write the SHA-256 manifest of the emitted modules; default "
                         "<DIR>/MANIFEST-<side>.sha256")
    ap.add_argument("--points", default="0,1,2",
                    help="grid points to prove h0 at; `all` = 0..D, which is what makes the "
                         "`∀ n` conclusion unconditional")
    ap.add_argument("--verify-points", type=int, default=-1,
                    help="how many integer n to re-verify the cleared residual at; the default "
                         "(-1) is D+1, which is a PROOF over ℚ[n] and not a sample")
    ap.add_argument("--from-index", type=int, default=0,
                    help="resume the verification loop at this index (it streams and checkpoints)")
    ap.add_argument("--assemble", action="store_true",
                    help="MODULAR layout only: also emit `<stem>Assemble.lean`, which imports "
                         "the base and every shard and states `h0_all` + `star_forall`. Without "
                         "it a completed grid discharges `star_forall_of_h0`'s HYPOTHESES and "
                         "produces no object — the shards elaborate as separate processes, so "
                         "nothing is ever in scope with anything else and `star_forall` has no "
                         "referent (row PAIR-2, 2026-09-14). Requires `--points all`: `h0_all` "
                         "quantifies over the whole grid and a subset cannot prove it.")
    ap.add_argument("--emit-only", action="store_true",
                    help="skip the residual gate. ONLY for `check_star_coords.py`'s "
                         "byte-identity arm, which is checking the BYTES and whose arm A has "
                         "already re-verified the mathematics from the same dump. Never use it "
                         "to produce a committed artifact.")
    ap.add_argument("--h0-encoding", choices=("ring", "literal", "kernel"), default=None,
                    help="MODULAR layout only; default `literal`. `literal` is Sec17.6's lever (a), "
                         "adopted Sec17.7: every X_k(n) and A~_j(n) is evaluated to a literal in its "
                         "own `norm_num` lemma, so `ring` sees only literal coefficients — MEASURED "
                         "2026-09-10 at 207 s / 8.09 GB (n=0), 362 s / 7.77 GB (n=138), 265 s / "
                         "8.02 GB (n=276). `ring` is the Sec17 encoding it replaced: each shard "
                         "unfolds every list and hands `ring` the whole residual, 449 s / 16.29 GB at "
                         "the CHEAPEST point and unfinished at 35 min on the interior; kept so the "
                         "comparison can be re-run. The single-file layout always uses `ring`, so "
                         "check_star_coords.py's byte-identity arm keeps its pin. "
                         "`kernel` (2026-09-11, row PAIR-K) writes `K<n>` shards that decide the "
                         "point's ℤ-cleared identity by `decide +kernel` and bridge it with "
                         "`StarKernel.h0_of_kernel` (StarKernelBridge.lean, shipped beside the base); "
                         "the base module is byte-identical to the literal one. Cost: see the row.")
    args = ap.parse_args()
    if bool(args.out) == bool(args.emit_modules):
        print("star_forall_to_lean: give exactly one of --out (single file) or --emit-modules DIR",
              file=sys.stderr)
        return 2
    if args.h0_encoding is not None and not args.emit_modules:
        print("star_forall_to_lean: --h0-encoding is a MODULAR-layout knob; the single file keeps "
              "the Sec17 encoding so check_star_coords.py's byte-identity arm keeps its pin",
              file=sys.stderr)
        return 2
    if args.h0_encoding is None:
        args.h0_encoding = "literal"

    c, L, xnum, atil, D, gcd_used = build(args.coords)
    print("side=%s dx=%d J=%d coords=%d  L.deg=%d (gcd steps %d)  x.deg<=%d  D=%d"
          % (c.side, c.dx, c.J, len(c.coords), scl.pdeg(L), gcd_used,
             max(len(p) - 1 for p in xnum), D), flush=True)

    nver = 0 if args.emit_only else (D + 1 if args.verify_points < 0 else args.verify_points)
    bad = 0
    for i in range(args.from_index, nver):
        r = residual_at(c, xnum, atil, i)
        ok = star_lib.is_zero(r)
        if not ok:
            bad += 1
            deg = max(k for k, cf in enumerate(r) if cf != 0)
            print("RESIDUAL NONZERO at n=%d (t-degree %d)" % (i, deg), file=sys.stderr,
                  flush=True)
        if i % 10 == 0 or not ok:
            print("verify n=%d ok=%d" % (i, 1 if ok else 0), flush=True)
    if bad:
        print("star_forall_to_lean: REFUSING TO EMIT — the cleared residual is nonzero at "
              "%d point(s).  Fix the data, not this script." % bad, file=sys.stderr)
        return 1
    if nver <= D and not args.emit_only:
        print("star_forall_to_lean: REFUSING TO EMIT — %d verification points do NOT exceed the "
              "degree bound %d, so the residual is not PROVED zero over ℚ[n].  Re-run with "
              "--verify-points %d or more." % (nver, D, D + 1), file=sys.stderr)
        return 1

    if args.points == "all":
        points = list(range(D + 1))
        unconditional = True
    else:
        points = [int(s) for s in args.points.split(",") if s.strip()]
        unconditional = False
    if args.emit_modules:
        base = args.base_module or (namespace_of(c) + "Base")
        os.makedirs(args.emit_modules, exist_ok=True)
        ns, written = emit_modules(c, L, xnum, atil, D, points, args.emit_modules,
                                   os.path.basename(args.coords), gcd_used, base,
                                   encoding=args.h0_encoding)
        if args.assemble:
            written.append(emit_assembly(args.emit_modules, ns, D, points, base,
                                         args.h0_encoding, c.side))
        for p in written:
            print("wrote %s (%d bytes)" % (p, os.path.getsize(p)), flush=True)
        man = args.manifest or os.path.join(
            args.emit_modules, "MANIFEST-%s%s.sha256"
            % (c.side, "-kernel" if args.h0_encoding == "kernel" else ""))
        write_manifest(written, man, args.points, args.h0_encoding, assemble=args.assemble)
        print("wrote %s (%d line(s))" % (man, len(written)), flush=True)
        print("MODULAR: namespace %s, base %s, D=%d, %d of %d grid point(s) emitted"
              % (ns, base, D, len(points), D + 1))
        return 0
    ns = emit(c, L, xnum, atil, D, points, args.out, os.path.basename(args.coords), gcd_used,
              unconditional)
    print("wrote %s (%d bytes, namespace %s, D=%d, %d h0 point(s), %s)"
          % (args.out, os.path.getsize(args.out), ns, D, len(points),
             "UNCONDITIONAL ∀ n" if unconditional else "∀ n modulo h0"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
