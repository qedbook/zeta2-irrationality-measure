/-
# PT-QB clump 1b — PAIR EXECUTED: the hat's carries are the chain's `qₙ`'s carries

Row PT-QB of `docs/future/zeta2-lean-chain.md` (registry `2B0.AW`).  `Zeta2HatCarry.lean` proves
things about `hatQ`.  Nothing about `hatQ` is about the chain's `qₙ` until PAIR is applied, and
LEAN.md §3 is explicit that proving a piece with its neighbour as a hypothesis is not composing.
So this module does the application and nothing else — it is PT-QB's IDENTIFICATION half, run.

`Zeta2Pair8Close.pairing_q : ∀ n, hatQ n = qnInt n` is UNCONDITIONAL (re-verified here rather
than taken from the cell: its olean was rebuilt 2026-09-19 and its receipt reread — `pairing_q`
depends on `[propext, Classical.choice, Quot.sound]`, and its statement in
`Zeta2Pair8Close.lean` carries no hypothesis and no `n`-threshold).

## What this module banks

1. **`qnInt_ne_zero : ∀ n, qnInt n ≠ 0`, unconditionally.**  `Zeta2CarryFold.lean`'s own header
   records that PT-QA's `padicValInt` form "carries a hidden hypothesis" `hq : qnInt n ≠ 0` and
   that "no `∀ n, qnInt n ≠ 0` is landed anywhere in the corpus — the chain's `hrow` is
   `∃ k, m₀ ≤ k ∧ qn k ≠ 0`, one index".  It is landed now, and cheaply: `hatQ` is a NEGATED sum
   of positive binomial products, so `hatQ n < 0` at every `n`, and PAIR carries that across.
   `padicValInt_qnInt_ge_phiSingle` below is PT-QA's cell statement with no hypothesis left.
2. **`pow_dvd_qnInt_of_hat_bits`** — the hat's four-bit carry bound, stated about `qnInt`.  This
   is the shape PT-QB's five gap-interval lemmas will feed.
3. **The cell `(12, 103)` at the chain's own `q₁₂`**, and — the point of the row — the GAP it
   sits in, proved in Lean rather than read off a probe: `phiSingle (12/103) = 1` while
   `phiT (12/103) = 2`.  The tale-1 profile PT-QA delivers is strictly short there, so
   `103² ∣ q₁₂` is a fact PT-QA cannot produce and the hat can.

## What this module does NOT claim

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  `PhiT_dvd_qnInt` is NOT
here: the hat bound is proved at ONE cell by kernel evaluation, not on the five gap intervals,
and the five interval lemmas plus the profile dispatch are PT-QB's remaining work
(`ptqb_gap_probe.out`, `ptqb_cover_probe.out`).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Pair8Close
import Zeta2CarryFold
import Zeta2PhiT
import Zeta2HatCarry

namespace Zeta2HatQnInt

-- `qnInt` lives in `Zeta2Arith`, not `Zeta2Defs`: without it on this line `autoImplicit`
-- silently binds `qnInt` as a variable and every theorem below elaborates to `sorryAx`
-- while `#print axioms` still prints (LEAN.md §1 — measured here 2026-09-19).
open Zeta2Defs Zeta2Arith Zeta2Hat

/-! ## PAIR applied -/

/-- **`qnInt n ≠ 0` at every `n`.**  `Zeta2HatCarry.hatQ_ne_zero` through
`Zeta2Pair8Close.pairing_q`.  This is the hypothesis PT-QA's `padicValInt_qnInt_ge_phi` takes
and that its own header records as landed nowhere. -/
theorem qnInt_ne_zero (n : ℕ) : qnInt n ≠ 0 := by
  rw [← Zeta2Pair8Close.pairing_q n]
  exact Zeta2HatCarry.hatQ_ne_zero n

/-- **PT-QA's cell statement, UNCONDITIONAL.**  `Zeta2Arith.padicValInt_qnInt_ge_phi` with its
`hq` discharged — the `φ` (single-representation) profile bounds `ord_p qₙ` at every prime above
the Legendre line, with no side condition. -/
theorem padicValInt_qnInt_ge_phiSingle (n p : ℕ) [Fact p.Prime] (hp2 : 26 * n + 1 < p ^ 2) :
    Zeta2Arith.phiSingle (Int.fract ((n : ℚ) / p)) ≤ padicValInt p (qnInt n) :=
  Zeta2Arith.padicValInt_qnInt_ge_phi n p hp2 (qnInt_ne_zero n)

/-- **The hat's four one-term carry bits, about the chain's `qₙ`.**  The shape PT-QB's five
gap-interval lemmas produce; the transport is `pairing_q` and nothing else. -/
theorem pow_dvd_qnInt_of_hat_bits (n p v : ℕ) [Fact p.Prime]
    (h : ∀ j, j ≤ 8 * n →
      v ≤ (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0)
        + (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0)
        + (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0)
        + (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0)) :
    (p : ℤ) ^ v ∣ qnInt n := by
  rw [← Zeta2Pair8Close.pairing_q n]
  exact Zeta2HatCarry.pow_dvd_hatQ_of_bits n p v h

/-! ## The cell `(12, 103)`, and the gap it sits in -/

/-- The row's named probe, at the chain's own `q₁₂`. -/
theorem sq_103_dvd_qnInt_twelve : (103 : ℤ) ^ 2 ∣ qnInt 12 := by
  rw [← Zeta2Pair8Close.pairing_q 12]
  exact Zeta2HatCarry.sq_103_dvd_hatQ_twelve

/-- `2 ≤ ord₁₀₃ q₁₂` — the cell's statement verbatim, with the nonvanishing proved above. -/
theorem two_le_padicValInt_103_qnInt_twelve : 2 ≤ padicValInt 103 (qnInt 12) := by
  have : Fact (Nat.Prime 103) := ⟨by norm_num⟩
  exact ((padicValInt_dvd_iff 2 (qnInt 12)).1 sq_103_dvd_qnInt_twelve).resolve_left
    (qnInt_ne_zero 12)

/-- `{12/103} = 12/103` — the residue is below 1, so the fractional part is the fraction. -/
theorem fract_twelve_103 : Int.fract (((12 : ℕ) : ℚ) / ((103 : ℕ) : ℚ)) = 12 / 103 := by
  rw [Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]
  norm_num

/-- **PT-QA's profile is strictly SHORT at this residue.**  `12/103 ∈ [1/9, 2/17)`, where the
single-representation profile is `1`. -/
theorem phiSingle_twelve_103 : Zeta2Arith.phiSingle (12 / 103) = 1 := by
  norm_num [Zeta2Arith.phiSingle, Zeta2Arith.phiTable, List.find?]

/-- **`φ̃` is `2` there** — `12/103 ∈ [1/11, 2/17)` in `candidateProfile`.  With the line above,
this is the GAP `φ̃ > φ` that row PT-QB exists to close, exhibited in Lean at one cell: the
tale-1 half CANNOT give `103² ∣ q₁₂`, and `sq_103_dvd_qnInt_twelve` (which came through the hat)
does. -/
theorem phiT_twelve_103 : Zeta2PhiT.phiT (12 / 103) = 2 := by decide +kernel

/-- The gap, as one statement. -/
theorem phiSingle_lt_phiT_twelve_103 :
    Zeta2Arith.phiSingle (12 / 103) < Zeta2PhiT.phiT (12 / 103) := by
  rw [phiSingle_twelve_103, phiT_twelve_103]
  norm_num

end Zeta2HatQnInt

#print axioms Zeta2HatQnInt.qnInt_ne_zero
#print axioms Zeta2HatQnInt.padicValInt_qnInt_ge_phiSingle
#print axioms Zeta2HatQnInt.pow_dvd_qnInt_of_hat_bits
#print axioms Zeta2HatQnInt.sq_103_dvd_qnInt_twelve
#print axioms Zeta2HatQnInt.two_le_padicValInt_103_qnInt_twelve
#print axioms Zeta2HatQnInt.fract_twelve_103
#print axioms Zeta2HatQnInt.phiSingle_twelve_103
#print axioms Zeta2HatQnInt.phiT_twelve_103
#print axioms Zeta2HatQnInt.phiSingle_lt_phiT_twelve_103
