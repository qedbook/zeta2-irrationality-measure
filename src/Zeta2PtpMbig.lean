/-
# Row PT-P, part (b) — the polar run-strata rows at `m ≥ p²`: `RestAboveOpen` NAMED, and
# `Zeta2PtpRunS7.ResidualRunRestOpen` SPLIT into its `m < p²` and `m ≥ p²` halves

`Zeta2PtpRunS7.ResidualRunRestOpen` is the polar rows (`p ∣ r+1`) with `n % p` on one of the five
run strata, except the ones `coeff_runLow_S7` closes.  It has two halves by `m := 11n + 1 + r`:

* `m < p²` — `Zeta2PtpRunS2.RestBelowOpen`, the sibling unit's (the four φ̃ = 2 strata below `p²`),
  PROVED there hypothesis-free as `Zeta2PtpRunS2.restBelowOpen`.
* `m ≥ p²` — **`RestAboveOpen`**, this file's, and OPEN.

`residualRunRestOpen_of_split : RestBelowOpen → RestAboveOpen → ResidualRunRestOpen` and, with the
sibling's theorem spent, **`polyHalfOpen_of_above : RestAboveOpen → PolyHalfOpen`** — the
polynomial half of PT-P on ONE binder, carried in the TYPE (`#print axioms` cannot see it, LEAN.md §1).

THE ROWS (`ptp_mbig_probe.py` / `.out`, arm R).  Window primes have `p² > 26n + 1` and `m ≤ 27n`,
so `m ≥ p²` forces `26n + 1 < p² ≤ 27n` and `m = p² + μ`, `0 ≤ μ < n` — `m` has THREE base-`p`
digits with top digit `1`.  The family is infinite and sparse at small `n`: the first row is
`(n, p, r) = (64, 41, 983)` (`row_64_41`), the first φ̃ = 1 row is `(717, 137, 10959)`
(`row_717_137`); none at `n ≤ 60` (the `n = 11, p = 17, r = 169` cell is polar but OFF the run
strata — `11/17` — and `Zeta2PtpResPair.coeff_bound_sq_offrun` already closes it).

WHAT THE PROBE FOUND (not proved here).  Not termwise: every row has a term two places short.
The mechanism is two-level — the fold `F(i) = T(i) + T(p² + i)` gains one place by a
SECOND-ORDER pair law, `F(j) ≡ −p·λ(j)·T(j) (mod p^{v(T(j))+2})`, and the folded `p`-blocks
gain the other by the SAME block lemma as below `p²` (`Zeta2PtpRunBlock.lo_block_dvd`, which takes
no `m < p²`).  See the probe's header and the chain doc for the measured numbers.

Probe: `ptp_mbig_probe.py` / `.out`.  Falsifier: `falsify_ptpmbig.sh` / `out_ptpmbig_falsify.txt`.
Runner: `run_resid.sh`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2PtpRunS2

namespace Zeta2PtpMbig

/-! ## 1. The `m ≥ p²` half -/

/-- **THE `m ≥ p²` HALF — OPEN.**  The coefficient bound at every polar row on the five run
strata with `p² ≤ m = 11n + 1 + r`.  (No `¬ S7` clause: `coeff_runLow_S7` needs `m < p²`, so every
row here, the φ̃ = 1 stratum's included, is owed.) -/
def RestAboveOpen : Prop :=
  ∀ n p r : ℕ, p ∈ Zeta2PhiT.phiWindow n → r < 16 * n → p ∣ r + 1 →
    Zeta2PtpKumRows.RunStrata p (n % p) →
    p ^ 2 ≤ 11 * n + 1 + r →
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ)

/-! ## 2. The split -/

/-- **THE SPLIT**: the two halves give `ResidualRunRestOpen`. -/
theorem residualRunRestOpen_of_split (hb : Zeta2PtpRunS2.RestBelowOpen) (ha : RestAboveOpen) :
    Zeta2PtpRunS7.ResidualRunRestOpen := by
  intro n p r hp hr hpol hrun hns7
  by_cases hm : 11 * n + 1 + r < p ^ 2
  · exact hb n p r hp hr hpol hrun hns7 hm
  · exact ha n p r hp hr hpol hrun (by omega)

/-- **THE POLYNOMIAL HALF OF PT-P ON ONE BINDER**: the sibling's `restBelowOpen` spent. -/
theorem polyHalfOpen_of_above (ha : RestAboveOpen) : Zeta2PtpPolar.PolyHalfOpen :=
  Zeta2PtpRunS7.polyHalfOpen_of_rest (residualRunRestOpen_of_split Zeta2PtpRunS2.restBelowOpen ha)

/-! ## 3. Pins: `RestAboveOpen` is not vacuous -/

/-- The family's FIRST row: `n = 64, p = 41, r = 983` (`s = 23`, stratum `[5/9, 9/16)`, φ̃ = 2),
`m = 1688 = 41² + 7`. -/
theorem row_64_41 : 41 ∈ Zeta2PhiT.phiWindow 64 ∧ 983 < 16 * 64 ∧ 41 ∣ 983 + 1
    ∧ Zeta2PtpKumRows.RunStrata 41 (64 % 41) ∧ 41 ^ 2 ≤ 11 * 64 + 1 + 983 := by
  refine ⟨Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by norm_num, by norm_num⟩, by norm_num⟩,
    by norm_num, by norm_num, ?_, by norm_num⟩
  unfold Zeta2PtpKumRows.RunStrata
  norm_num

/-- The first φ̃ = 1 row: `n = 717, p = 137, r = 10959` (`s = 32`, stratum `[3/13, 4/17)`),
`m = 18847 = 137² + 78` — the stratum `coeff_runLow_S7` closes only below `p²`. -/
theorem row_717_137 : 137 ∈ Zeta2PhiT.phiWindow 717 ∧ 10959 < 16 * 717 ∧ 137 ∣ 10959 + 1
    ∧ (3 * 137 ≤ 13 * (717 % 137) ∧ 17 * (717 % 137) < 4 * 137)
    ∧ 137 ^ 2 ≤ 11 * 717 + 1 + 10959 := by
  refine ⟨Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by norm_num, by norm_num⟩, by norm_num⟩,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

end Zeta2PtpMbig

#print axioms Zeta2PtpMbig.residualRunRestOpen_of_split
#check @Zeta2PtpMbig.residualRunRestOpen_of_split
#print axioms Zeta2PtpMbig.polyHalfOpen_of_above
#check @Zeta2PtpMbig.polyHalfOpen_of_above
#print Zeta2PtpMbig.RestAboveOpen
#print axioms Zeta2PtpMbig.row_64_41
#check @Zeta2PtpMbig.row_64_41
#print axioms Zeta2PtpMbig.row_717_137
#check @Zeta2PtpMbig.row_717_137
