/-
# HC2 composed — `hc2` discharged inside `Zeta2L12.candidate_target_of_certified_constants`

LEAN.md §3: a row is closed when its statement is APPLIED where the chain consumes it, not when
a theorem of the right shape exists somewhere.  `Zeta2DPhi.hc2_of_dphi` delivers
`31 − d_φ̃ + ε' ≤ 15.01912095` for `ε' ≤ 1e-8`; this file feeds it to L12's headline at
`c2 := 31 − d_φ̃ + ε'`, so the 18-binder theorem becomes a 17-binder one plus `hε'`, and the
kernel — not a docstring — confirms that the re-cut literal in `Zeta2L12` and the literal
`Zeta2DPhi` proves are the SAME number.  `hmu` stays `Zeta2L12.L12_rational_gap`, unchanged in
form (`1 + vRate / uRate < 5.0495243`), re-`norm_num`'d at the re-cut rates.

The remaining binders are other rows' — DRATE produces the `c2`-shaped `hdecay`/`hgrowth`
inputs at exactly this `c2` (`c2 = 31 − d_φ̃ + ε'` is DRATE's own definition in the chain doc),
RDECAY/QGROW the rate bounds, L1-ASM the recurrences, PT-\* the clearing.

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox; Lean
never runs on the laptop (owner ruling 2026-09-07).
-/
import Zeta2DPhi
import Zeta2L12

namespace Zeta2Hc2

open Zeta2Defs

/-- **L12's headline with `hc2` DISCHARGED by row HC2.**  Seventeen of the eighteen binders
survive, plus `hε' : ε' ≤ 1e-8` for DRATE's slack; `c2` is `31 − d_φ̃ + ε'` throughout, in
`hdecay`'s `exp(−(c0 − c2 − δ))` and `hgrowth`'s `exp(c1 + c2)` alike — ONE `c2` serves both. -/
theorem candidate_target_of_hc2
    (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    {N₀ n₁ m₀ Nr Nq : ℕ} {Cr Cq c0 c1 δ ε' : ℝ}
    (hc0 : (29.10787127 : ℝ) ≤ c0) (hc1 : c1 ≤ (42.03361581 : ℝ))
    (hε' : ε' ≤ 1 / 10 ^ 8) (hδ : δ ≤ 1 / 10 ^ 16)
    (hrecq : ∀ n, N₀ ≤ n →
      α₀ n * ((candidateM.qn n : ℚ) : ℝ) + α₁ n * ((candidateM.qn (n + 1) : ℚ) : ℝ)
        + α₂ n * ((candidateM.qn (n + 2) : ℚ) : ℝ)
        + α₃ n * ((candidateM.qn (n + 3) : ℚ) : ℝ) = 0)
    (hrecp : ∀ n, N₀ ≤ n →
      α₀ n * ((candidateM.pn n : ℚ) : ℝ) + α₁ n * ((candidateM.pn (n + 1) : ℚ) : ℝ)
        + α₂ n * ((candidateM.pn (n + 2) : ℚ) : ℝ)
        + α₃ n * ((candidateM.pn (n + 3) : ℚ) : ℝ) = 0)
    (hΔne : ∀ n, Δ n ≠ 0)
    (hQ : ∀ n, (Q n : ℝ) = Δ n * ((candidateM.qn n : ℚ) : ℝ))
    (hP : ∀ n, (P n : ℝ) = Δ n * ((candidateM.pn n : ℚ) : ℝ))
    (hN₁ : N₀ ≤ n₁) (hM₀ : N₀ ≤ m₀)
    (hα₃ : ∀ n, n₁ ≤ n → α₃ n ≠ 0) (hα₀ : ∀ n, m₀ ≤ n → α₀ n ≠ 0)
    (hrow : ∃ k, m₀ ≤ k ∧ candidateM.qn k ≠ 0)
    (hCr : 0 < Cr)
    (hdecay : ∀ n, Nr ≤ n →
      |Δ n * candidateM.rn n| ≤ Cr * Real.exp (-(c0 - (31 - Zeta2DPhi.dPhi + ε') - δ)) ^ n)
    (hCq : 0 < Cq)
    (hgrowth : ∀ n, Nq ≤ n →
      |(Q n : ℝ)| ≤ Cq * Real.exp (c1 + (31 - Zeta2DPhi.dPhi + ε')) ^ n) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2L12.candidate_target_of_certified_constants Q P Δ α₀ α₁ α₂ α₃ hc0 hc1
    (Zeta2DPhi.hc2_of_dphi ε' hε') hδ hrecq hrecp hΔne hQ hP hN₁ hM₀ hα₃ hα₀ hrow hCr hdecay
    hCq hgrowth

/-- The literal HC2 proves and the literal L12 consumes are the same number: this is
`Zeta2L12.uRate_le_certified` and `certified_le_vRate` applied to HC2's output, with nothing
in between.  A drift on either side is an elaboration error here. -/
theorem rates_bracket_dphi (ε' : ℝ) (hε' : ε' ≤ 1 / 10 ^ 8) {c0 c1 δ : ℝ}
    (hc0 : (29.10787127 : ℝ) ≤ c0) (hc1 : c1 ≤ (42.03361581 : ℝ)) (hδ : δ ≤ 1 / 10 ^ 16) :
    Zeta2L12.uRate ≤ c0 - (31 - Zeta2DPhi.dPhi + ε') - δ
      ∧ c1 + (31 - Zeta2DPhi.dPhi + ε') ≤ Zeta2L12.vRate :=
  ⟨Zeta2L12.uRate_le_certified hc0 (Zeta2DPhi.hc2_of_dphi ε' hε') hδ,
    Zeta2L12.certified_le_vRate hc1 (Zeta2DPhi.hc2_of_dphi ε' hε')⟩

#print axioms candidate_target_of_hc2
#print axioms rates_bracket_dphi
#print axioms Zeta2L12.L12_rational_gap

end Zeta2Hc2
