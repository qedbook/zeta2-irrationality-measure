/-
# Row PHI-BDY — the tale-1 boundary law, as a shift law on `Rep`

`docs/future/zeta2-lean-chain.md` row PHI-BDY.

**What the row owed, and what its cell said.**  PHI-BDY was the ONLY row of the 42-row chain
whose size cell read `UNSIZED`, and it carried the scope audit's "row I understand least" (§9.4).
Its two branches were *"[E] if `ΔS ∈ Rep` and the shift identities are exact on `Rep`, it is ~100
lines of `Finset` bookkeeping; if the census's strip statement has to be re-derived as a residue
statement, ~500+"*.  **This file is the cheap branch, EXECUTED**: ~110 lines, one elaboration, and
no residue argument anywhere.

`Φ` is an algebraic functional on `Rep = Polynomial ℚ × (ℕ →₀ ℚ)` whose only dependence on the
cell is through the harmonic index `k − m − 1`.  So raising every key by one — which is what
`t ↦ t + 1` does to a partial-fraction family — moves `Φ` by the two landed halves of B2 and by
nothing else:

    Zeta2Moments.Lpoly_shift    ℒ(ρ(·+1)) − ℒ(ρ) = ρ′(M+1)        on the polynomial part
    Zeta2Moments.harm_succ_sub  H⁽²⁾_{j+1} − H⁽²⁾_j = 1/(j+1)²    on the pole basis

giving, for an ARBITRARY `Rep` supported above `m`,

    **Φ m (repDelta r) = ( 0 , P′(−m) − Σ_k c_k/(k−m)² )**                    `Phi_repDelta`

This is the exact twin of `Zeta2HatShift.Phihat_repDelta`, one kernel down, and the difference
between the two IS the transfer question: `π/sin 2πt` has two SIMPLE poles per cell, so `Φ̂`'s
boundary term is the representation SAMPLED at two points (`beltPt N 0`, `beltPt N 1`); tale-1's
`(π/sin πt)²` has ONE DOUBLE pole per cell, at the integer `M + 1 = −β₃n`, so the boundary term is
the representation's DERIVATIVE there.  Unconditional coordinates drop from two to one, and
`Lpoly_shift` — the polynomial half, which `Rep̂` has no counterpart for at all, since `Rep̂` has no
polynomial part — becomes load-bearing here (`t1_bdy_probe.py`'s `phi-no-poly` and
`shift-keys-only` arms are the measurement that it is).

**SO THIS IS NOT A CENSUS ROW, AND B3/B4 ARE NOT INPUTS TO IT.**  `Φ m (repDelta r) = 0` is ONE
number, `S′(−β₃n)`, and `Zeta2Census`'s 118 theorems and `Zeta2ContourD7`'s 402 — both
`omega`-class affine sign facts — are not consumed in reaching it.  The only thing this row needs
from that direction is the support floor `β₃ ≤ α₄`, which is already a field of
`Zeta2Defs.Member.WF` (`b3_le`).  *Scoped claim*: whatever else B3/B4 serve upstream,
`Φ (repDelta r) = 0` does not consume them.

**The one hypothesis, and it is load-bearing rather than decorative.**  `Member.harmIndex` is ℕ
subtraction, so `harm 2 (k + 1 − m − 1) − harm 2 (k − m − 1) = 1/(k−m)²` needs `m + 1 ≤ k`; at
`k = m` both sides truncate to `0` and the law is FALSE.  §6 exhibits that break INSIDE Lean —
`Phi_repDelta_needs_support` proves that a version stated without `hsupp` would prove
`(0,0) = (0,−1)` — and `../zeta2_star_b1/t1_bdy_probe.py` §B measures the same break off-Lean at
four cells.

**`m` is `β₃n`**, so the cell is `M = −m−1` (`Zeta2Defs.Member.cell`) and the harmonic index is
`k − m − 1` (`Zeta2Defs.Member.harmIndex`), both spelled here exactly as those definitions do.

**WHAT THIS FILE DOES NOT DO, and the row is NOT closed by it.**  It does not exhibit
`repS n : Rep`, and it does not prove `evalRep (repS n) t = S t` off the poles.  Everything here is
about `Φ`; nothing here is about `S`, the member, or the census.  What is MEASURED about `S` — in
exact rationals, on BOTH landed tale-1 coordinate files, by `../zeta2_star_b1/t1_bdy_probe.py`
(153 checks / 0 failed, eight falsifier arms RED):

  * `S`'s poles are ALL SIMPLE at every `n ≥ 1` of a seven-point ladder, up to 177 of them — which
    is the whole reason `Rep` needs no order-2 family and B2 owes no `Wtwo_shift`.  A single
    order-2 pole would have been the row's `~500+` branch.
  * `ord` of `S` at the strip integer `−β₃n` is **2 for every `n ≥ 3`, and 1 at `n = 0, 1, 2`**, at
    BOTH members — so the threshold is **SHARP at 3**, not a margin (the `n = 1, 2` case is checked
    to have `G(t₀) ≠ 0`), and it equals the predicted `⌈L/(β₃−β₂)⌉` computed from the coords file.
    The row's own `N₀ = 6` clears it by 3.
  * `deg num − deg den = 16n + 48` (candidate) / `9n + 27` (record): `S` is VERY improper, and the
    hat's `C₀` trap is ABSORBED rather than repeated.  `Ŝ` was improper by exactly ZERO, so
    `Ŝ(∞) = C₀ ≠ 0` and no `Rep̂` represented it at all; tale-1's `Rep` HAS a polynomial part, so a
    degree-`16n+48` improper part is carried rather than subtracted, and the probe's §F measures
    `evalRep (repS n) t = S t` with NO correction constant.
  * **At `n = 0` the row's statement is FALSE**: `ord = 1` at both members, and `S` has an order-3
    pole at `k = 1`, so it is not in `Rep` at all.  The row's ORIGINALLY named probe was that
    instance; run as written it reds on a true theorem's false instance, which is why the row
    strikes it rather than superseding it.

**How to elaborate it** (LEAN.md §0 — Lean never runs on the laptop):

    sh external_tests/zeta2_arith/run_probe.sh Zeta2T1Shift.lean

which ships this file and `Zeta2Moments.lean` from `../zeta2_small_rows/` to the buildbox, oleans
the dependency, and reads the eleven `#print axioms` lines through the repo's one receipt
predicate.  Falsifier: `sh external_tests/zeta2_arith/falsify_t1shift.sh` (four arms, GREEN control
at both ends).  Archived output: `out_axioms_t1shift.txt`, `out_t1shift_falsify.txt`.
-/
import Mathlib.Data.Finsupp.Basic
import Zeta2Moments

namespace Zeta2T1Shift

open Zeta2Moments Finset Polynomial

/-! ## §1 — tale-1's `Rep`, `evalRep` and `Φ`, as the PHI-REP row states them -/

/-- **`Rep`** — tale-1's partial-fraction data: a POLYNOMIAL part and the ORDER-1 pole
coefficients at `t = −k`.  No order-2 family: `R_n`'s poles are simple
(`Zeta2Defs.Member.window`), and `t1_bdy_probe.py` §D measures that `S`'s are too, at every
`n ≥ 1` of a seven-point ladder at both landed members.  That is the whole reason B2's
`Wone_shift` suffices and no `Wtwo_shift` is owed. -/
abbrev Rep := Polynomial ℚ × (ℕ →₀ ℚ)

/-- The evaluation map.  A pair `(P, c)` REPRESENTS a function `f` when this agrees with `f`
off the poles — the EVALUATION direction, which is the corpus's convention
(`Zeta2HatRep`'s header, PHI-REP's own `rep_injective`). -/
noncomputable def evalRep (r : Rep) (t : ℚ) : ℚ :=
  r.1.eval t + r.2.sum (fun k c => c / (t + (k : ℚ)))

/-- **`Φ`** at the cell `M = −m−1`, ℚ×ℚ-valued: `(ζ(2) coefficient, rational part)`.  This is
the PHI-REP row's definition with `m := β₃n`, so `harm 2 (k + M) = harm 2 (k − m − 1)` is
`Zeta2Defs.Member.harmIndex` on the nose. -/
noncomputable def Phi (m : ℕ) (r : Rep) : ℚ × ℚ :=
  (r.2.sum (fun _ c => c),
   Lpoly (-(m : ℤ) - 1) r.1 - r.2.sum (fun k c => c * harm 2 (k - m - 1)))

/-- **`shiftRep r`** — translate the argument by one: the polynomial part is composed with
`X + 1` and every pole index is raised by one. -/
noncomputable def shiftRep (r : Rep) : Rep :=
  (r.1.comp (X + 1), r.2.mapDomain (· + 1))

/-- **`repDelta r`** — the representation of `t ↦ f(t+1) − f(t)` when `r` represents `f`. -/
noncomputable def repDelta (r : Rep) : Rep := shiftRep r - r

/-! ## §2 — `shiftRep` IS translation by one -/

theorem succ_inj : Function.Injective (fun k : ℕ => k + 1) := fun _ _ h => by simpa using h

theorem evalRep_shiftRep (r : Rep) (t : ℚ) : evalRep (shiftRep r) t = evalRep r (t + 1) := by
  have hp : (r.1.comp (X + 1)).eval t = r.1.eval (t + 1) := by
    rw [eval_comp]; simp
  have hs : (Finsupp.mapDomain (fun k : ℕ => k + 1) r.2).sum (fun k c => c / (t + (k : ℚ)))
      = r.2.sum (fun k c => c / (t + 1 + (k : ℚ))) := by
    rw [Finsupp.sum_mapDomain_index_inj succ_inj]
    refine Finsupp.sum_congr fun k _ => ?_
    have hk : t + ((k + 1 : ℕ) : ℚ) = t + 1 + (k : ℚ) := by push_cast; ring
    rw [hk]
  show (r.1.comp (X + 1)).eval t
      + (Finsupp.mapDomain (fun k : ℕ => k + 1) r.2).sum (fun k c => c / (t + (k : ℚ)))
      = r.1.eval (t + 1) + r.2.sum (fun k c => c / (t + 1 + (k : ℚ)))
  rw [hp, hs]

/-! ## §3 — `Φ` is additive, so the Δ splits -/

theorem Lpoly_sub (M : ℤ) (p q : Polynomial ℚ) : Lpoly M (p - q) = Lpoly M p - Lpoly M q := by
  have h : Lpoly M (p - q) + Lpoly M q = Lpoly M p := by
    rw [← Lpoly_add]; ring_nf
  linarith

theorem Phi_sub (m : ℕ) (r s : Rep) : Phi m (r - s) = Phi m r - Phi m s := by
  unfold Phi
  have h1 : (r - s).2.sum (fun _ c => c) = r.2.sum (fun _ c => c) - s.2.sum (fun _ c => c) :=
    Finsupp.sum_sub_index (fun _ _ _ => rfl)
  have h2 : (r - s).2.sum (fun k c => c * harm 2 (k - m - 1))
      = r.2.sum (fun k c => c * harm 2 (k - m - 1))
        - s.2.sum (fun k c => c * harm 2 (k - m - 1)) :=
    Finsupp.sum_sub_index (fun _ _ _ => by ring)
  have h3 : (r - s).1 = r.1 - s.1 := rfl
  rw [h3, Lpoly_sub, h1, h2, Prod.mk_sub_mk, Prod.mk.injEq]
  exact ⟨rfl, by ring⟩

/-! ## §4 — the two coordinates under the argument shift -/

/-- **The ζ(2) coordinate does not move at all** — a key shift is an injective reindexing.
This is the twin of `Zeta2HatShift.Phihat_zeta2_argshift`, and like it, it needs NO hypothesis:
no support condition, no cell condition, nothing. -/
theorem Phi_zeta2_argshift (m : ℕ) (r : Rep) : (Phi m (shiftRep r)).1 = (Phi m r).1 := by
  show (r.2.mapDomain (fun k => k + 1)).sum (fun _ c => c) = r.2.sum (fun _ c => c)
  rw [Finsupp.sum_mapDomain_index_inj succ_inj]

/-- **The rational coordinate moves by the strip residue** — B2, both halves, composed.  The
polynomial part contributes `P′(M+1)` (`Lpoly_shift`) and each simple pole contributes
`−c_k/(k−m)²` (`harm_succ_sub`), which is `(d/dt)[c_k/(t+k)]` at `t = M+1 = −m`. -/
theorem Phi_rat_argshift (m : ℕ) (r : Rep) (hsupp : ∀ k ∈ r.2.support, m + 1 ≤ k) :
    (Phi m (shiftRep r)).2
      = (Phi m r).2 + ((derivative r.1).eval (-(m : ℚ))
          - r.2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2)) := by
  show Lpoly (-(m : ℤ) - 1) (r.1.comp (X + 1))
      - (r.2.mapDomain (fun k => k + 1)).sum (fun k c => c * harm 2 (k - m - 1)) = _
  have hL : Lpoly (-(m : ℤ) - 1) (r.1.comp (X + 1)) - Lpoly (-(m : ℤ) - 1) r.1
      = (derivative r.1).eval (-(m : ℚ)) := by
    have h := Lpoly_shift (-(m : ℤ) - 1) r.1
    have hc : ((-(m : ℤ) - 1 : ℤ) : ℚ) + 1 = -(m : ℚ) := by push_cast; ring
    rw [h, hc]
  have hM : (r.2.mapDomain (fun k => k + 1)).sum (fun k c => c * harm 2 (k - m - 1))
      = r.2.sum (fun k c => c * harm 2 (k + 1 - m - 1)) := by
    rw [Finsupp.sum_mapDomain_index_inj succ_inj]
  have hH : r.2.sum (fun k c => c * harm 2 (k + 1 - m - 1))
      - r.2.sum (fun k c => c * harm 2 (k - m - 1))
      = r.2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2) := by
    rw [Finsupp.sum, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : m + 1 ≤ k := hsupp k hk
    have he : k + 1 - m - 1 = (k - m - 1) + 1 := by omega
    have hcast : ((k - m - 1 : ℕ) : ℚ) + 1 = (k : ℚ) - (m : ℚ) := by
      have h0 : (k - m - 1 : ℕ) + m + 1 = k := by omega
      have h2 : (((k - m - 1 : ℕ) + m + 1 : ℕ) : ℚ) = (k : ℚ) := by rw [h0]
      push_cast at h2
      linarith
    rw [he, ← mul_sub, harm_succ_sub 2 (k - m - 1), hcast]
    ring
  rw [hM]
  have : Lpoly (-(m : ℤ) - 1) (r.1.comp (X + 1))
      = Lpoly (-(m : ℤ) - 1) r.1 + (derivative r.1).eval (-(m : ℚ)) := by linarith [hL]
  rw [this]
  show _ = Lpoly (-(m : ℤ) - 1) r.1 - r.2.sum (fun k c => c * harm 2 (k - m - 1))
      + ((derivative r.1).eval (-(m : ℚ)) - r.2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2))
  rw [← hH]
  ring

/-! ## §5 — THE ROW'S LAW -/

/-- **`Φ (repDelta r)` is the strip residue, for an ARBITRARY `Rep` supported above `m`.**

The tale-1 twin of `Zeta2HatShift.Phihat_repDelta`.  Nothing here is about `S`, the census, or
the member: it is about `Φ` being an algebraic functional whose only cell-dependence is the
harmonic index.  B3's 118 and B4's 402 affine sign facts are NOT an input to it. -/
theorem Phi_repDelta (m : ℕ) (r : Rep) (hsupp : ∀ k ∈ r.2.support, m + 1 ≤ k) :
    Phi m (repDelta r)
      = (0, (derivative r.1).eval (-(m : ℚ))
              - r.2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2)) := by
  rw [repDelta, Phi_sub]
  rw [Prod.ext_iff]
  constructor
  · show (Phi m (shiftRep r)).1 - (Phi m r).1 = 0
    rw [Phi_zeta2_argshift]; ring
  · show (Phi m (shiftRep r)).2 - (Phi m r).2 = _
    rw [Phi_rat_argshift m r hsupp]; ring

/-- **The row, in the form L1-ASM consumes it.**  `hz` says the representation's derivative at
the strip integer vanishes — which `t1_bdy_probe.py` §C measures to hold for the candidate's
and the record's `S` at every `n ≥ 3`, because `S` has a DOUBLE ZERO at `t = −β₃n` there. -/
theorem hbdy (m : ℕ) (r : Rep) (hsupp : ∀ k ∈ r.2.support, m + 1 ≤ k)
    (hz : (derivative r.1).eval (-(m : ℚ))
            = r.2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2)) :
    Phi m (repDelta r) = 0 := by
  rw [Phi_repDelta m r hsupp, hz]
  simp

/-! ## §6 — rung-0: the hypothesis is load-bearing, and the law is not vacuous

`LEAN.md` §5 — a lemma stated without the hypothesis would elaborate green and mean nothing.
These are the Lean twins of `t1_bdy_probe.py` §B, which measures the same break off-Lean. -/

/-- The bad instance's Φ side: at `m = 1` with a single pole at `k = 0` — one BELOW the support
floor `m + 1 = 2` — the ℕ subtraction `k − m − 1` truncates at BOTH `k = 0` and `k = 1`, so the
harmonic difference is `0`. -/
theorem Phi_repDelta_at_bad_key :
    Phi 1 (repDelta ((0 : Polynomial ℚ), Finsupp.single 0 (1 : ℚ))) = (0, 0) := by
  have hp : (repDelta ((0 : Polynomial ℚ), Finsupp.single 0 (1 : ℚ))).1 = 0 := by
    simp [repDelta, shiftRep]
  have hd : (repDelta ((0 : Polynomial ℚ), Finsupp.single 0 (1 : ℚ))).2
      = Finsupp.single 1 (1 : ℚ) - Finsupp.single 0 (1 : ℚ) := by
    simp [repDelta, shiftRep, Finsupp.mapDomain_single]
  have e1 : (Finsupp.single 1 (1 : ℚ) - Finsupp.single 0 (1 : ℚ)).sum (fun _ c => c) = 0 := by
    rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)]
    simp
  have e2 : (Finsupp.single 1 (1 : ℚ) - Finsupp.single 0 (1 : ℚ)).sum
      (fun k c => c * harm 2 (k - 1 - 1)) = 0 := by
    rw [Finsupp.sum_sub_index (fun _ _ _ => by ring)]
    simp [harm]
  rw [Phi, hp, hd, e1, e2, Lpoly_zero]
  simp

/-- The bad instance's STRIP-RESIDUE side: `−1`, not `0`. -/
theorem strip_residue_at_bad_key :
    (derivative (0 : Polynomial ℚ)).eval (-(1 : ℚ))
        - (Finsupp.single 0 (1 : ℚ)).sum (fun k c => c / ((k : ℚ) - (1 : ℚ)) ^ 2) = -1 := by
  rw [Finsupp.sum_single_index] <;> simp

/-- **Falsifier.**  So `Phi_repDelta`'s conclusion is FALSE at a key below the support floor —
a version of it stated without `hsupp` would prove `(0,0) = (0,−1)`.  The off-Lean twin is
`t1_bdy_probe.py` §B, which measures the same break at four cells. -/
theorem Phi_repDelta_needs_support :
    Phi 1 (repDelta ((0 : Polynomial ℚ), Finsupp.single 0 (1 : ℚ)))
      ≠ (0, (derivative (0 : Polynomial ℚ)).eval (-(1 : ℚ))
              - (Finsupp.single 0 (1 : ℚ)).sum
                  (fun k c => c / ((k : ℚ) - (1 : ℚ)) ^ 2)) := by
  rw [Phi_repDelta_at_bad_key, strip_residue_at_bad_key]
  simp

/-- **Control.**  The ζ(2) coordinate really is zero on a NONZERO `repDelta`, so
`Phi_repDelta`'s first component is not zero by the object being trivial. -/
theorem repDelta_nontrivial : repDelta ((0 : Polynomial ℚ), Finsupp.single 3 (1 : ℚ)) ≠ 0 := by
  intro h
  have := congrArg (fun z => (Prod.snd z) 4) h
  simp [repDelta, shiftRep, Finsupp.mapDomain_single] at this

/-! ## §7 — receipts (`LEAN.md` §1 — exit 0 is not an attestation) -/

#print axioms Zeta2T1Shift.evalRep_shiftRep
#print axioms Zeta2T1Shift.Lpoly_sub
#print axioms Zeta2T1Shift.Phi_sub
#print axioms Zeta2T1Shift.Phi_zeta2_argshift
#print axioms Zeta2T1Shift.Phi_rat_argshift
#print axioms Zeta2T1Shift.Phi_repDelta
#print axioms Zeta2T1Shift.hbdy
#print axioms Zeta2T1Shift.Phi_repDelta_at_bad_key
#print axioms Zeta2T1Shift.strip_residue_at_bad_key
#print axioms Zeta2T1Shift.Phi_repDelta_needs_support
#print axioms Zeta2T1Shift.repDelta_nontrivial

end Zeta2T1Shift
