/-
# HC1 — `hc1 : Real.log Zeta2XL1.rhoChar ≤ 42.03361581`, and its composition into L12

The row's whole content is one `exp` LOWER bound at a rational, and the row is small only on ONE
route.  `hc1_margin.py` (`external_tests/zeta2_arith/`, re-run and re-derived in exact rationals
2026-09-19) measures the room the 8-decimal literal leaves and what each Mathlib route delivers:

| route | lower bound on `exp 42.03361581` vs `rhoChar` |
|---|---|
| `Real.add_one_le_exp` (the scope audit's named lemma) | `1 + 42.03…` — hopeless at 42 |
| `Real.exp_one_gt_d9 ^ 42` × `quadratic_le_exp_of_nonneg` | SHORT by **6.174e-6** relative |
| `Real.exp_one_gt_d9 ^ 42` × a 7-term Taylor sum | still SHORT by **4.25e-10** relative |
| `Real.exp_one_near_20 ^ 42` × a 7-term Taylor sum | CLEARS, residual **2.0324e-9** relative |

The margin itself is **2.0324e-9** relative (`exp 42.03361581 / rhoChar − 1`), so the audit's route
fails by three orders of magnitude and it fails LATE, after the composition is written.  The third
row is the sharper statement and it is this file's own finding: `exp_one_gt_d9` is 2.46e-9 relative
below `e^42` all by itself, so NO improvement to the fractional-part bound rescues that route — the
constant, not the truncation, is what is insufficient.

`taylor_sum_eq` is the §6 cross-check on the one hand-entered literal in this file: the 50-digit
numerator is asserted EQUAL to `∑ i ∈ Finset.range 7, 0.03361581^i / i!`, so a mistyped digit is an
elaboration error rather than a silently weaker bound.

`candidate_target_of_rhoChar_growth` is the row's delivery to QGROW, stated with the hypothesis
QGROW actually PRODUCES (LEAN.md §3's corollary): `|Q n| ≤ Cq * (rhoChar * exp c2) ^ n`, the shape
L5-at-`qₙ` hands over, rather than L12's `exp (c1 + c2) ^ n`.  The bridge between them is
`Real.exp_log` at `c1 := Real.log rhoChar`, discharged here once.

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox; Lean never
runs on the laptop (owner ruling 2026-09-07).  Names verified at that pin 2026-09-19:
`Real.exp_one_near_20`, `Real.sum_le_exp_of_nonneg` and `Real.exp_nat_mul` are all present in the
cited spellings; `pow_le_pow_left` is NOT — it is `pow_le_pow_left₀` here (LEAN.md §8).
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Zeta2XL1
import Zeta2Hc2

namespace Zeta2Hc1

open Zeta2Defs

/-! ## The two certified lower bounds -/

/-- Mathlib's 20-place enclosure of `e`, read as a lower bound. -/
theorem e_lower : (363916618873 / 133877442384 - 1 / 10 ^ 20 : ℝ) ≤ Real.exp 1 := by
  have h := Real.exp_one_near_20
  rw [abs_le] at h
  linarith [h.1]

theorem e_lower_nonneg : (0 : ℝ) ≤ 363916618873 / 133877442384 - 1 / 10 ^ 20 := by norm_num

theorem exp_42 : Real.exp 42 = Real.exp 1 ^ 42 :=
  calc Real.exp 42 = Real.exp (((42 : ℕ) : ℝ) * 1) := by norm_num
    _ = Real.exp 1 ^ 42 := Real.exp_nat_mul 1 42

/-- The integer part: `e`'s certified lower end, to the 42nd power. -/
theorem pow_lower : (363916618873 / 133877442384 - 1 / 10 ^ 20 : ℝ) ^ 42 ≤ Real.exp 42 := by
  rw [exp_42]
  exact pow_le_pow_left₀ e_lower_nonneg e_lower 42

/-- The 7-term Taylor partial sum at the fractional part, EVALUATED.  This equation is the §6
cross-check on the only hand-entered literal in the file. -/
theorem taylor_sum_eq :
    (∑ i ∈ Finset.range 7, (0.03361581 : ℝ) ^ i / (Nat.factorial i : ℝ))
      = 82734976480930246345784026795152318369527627450609
        / 80000000000000000000000000000000000000000000000000 := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The fractional part: every term of the partial sum is positive, so it is a lower bound. -/
theorem frac_lower :
    (82734976480930246345784026795152318369527627450609
      / 80000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.exp 0.03361581 := by
  rw [← taylor_sum_eq]
  exact Real.sum_le_exp_of_nonneg (by norm_num) 7

theorem exp_split : Real.exp (42.03361581 : ℝ) = Real.exp 42 * Real.exp 0.03361581 := by
  rw [← Real.exp_add]; norm_num

/-! ## The arithmetic core -/

theorem cden_posR : (0 : ℝ) < (Zeta2XL1Data.cden : ℝ) := by
  have := Zeta2XL1Data.cden_pos
  exact_mod_cast this

/-- **THE arithmetic fact of row HC1**: the characteristic root's exact rational value against the
product of the two certified lower bounds.  Everything else in the file is plumbing. -/
theorem rho_le_prod :
    (Zeta2XL1Data.rhoNum : ℝ) / (Zeta2XL1Data.cden : ℝ)
      ≤ (363916618873 / 133877442384 - 1 / 10 ^ 20 : ℝ) ^ 42
        * (82734976480930246345784026795152318369527627450609
            / 80000000000000000000000000000000000000000000000000) := by
  rw [div_le_iff₀ cden_posR]
  norm_num [Zeta2XL1Data.rhoNum, Zeta2XL1Data.cden]

/-! ## The row's statements, in the target vocabulary -/

/-- **HC1, in `exp` form.**  `Zeta2XL1.rhoChar` is `rhoNum / cden` by definition. -/
theorem rhoChar_le_exp : Zeta2XL1.rhoChar ≤ Real.exp (42.03361581 : ℝ) := by
  rw [Zeta2XL1.rhoChar]
  refine rho_le_prod.trans ?_
  rw [exp_split]
  exact mul_le_mul pow_lower frac_lower (by norm_num) (Real.exp_nonneg _)

/-- **HC1, in the binder shape `Zeta2L12` consumes**: `hc1 : c1 ≤ 42.03361581` at
`c1 := Real.log Zeta2XL1.rhoChar`. -/
theorem hc1 : Real.log Zeta2XL1.rhoChar ≤ (42.03361581 : ℝ) :=
  (Real.log_le_iff_le_exp Zeta2XL1.rho_pos).mpr rhoChar_le_exp

/-- **QGROW's step, as ONE application** at `c1 := Real.log rhoChar`: `rhoChar ^ n ≤ exp c1 ^ n`.
At this `c1` it is an equality, which is the point — the loss lives entirely in `hc1`. -/
theorem rhoChar_pow_le_exp_c1 (n : ℕ) :
    Zeta2XL1.rhoChar ^ n ≤ Real.exp (Real.log Zeta2XL1.rhoChar) ^ n := by
  rw [Real.exp_log Zeta2XL1.rho_pos]

/-- The same step at the LITERAL, for a consumer that would rather fix `c1 := 42.03361581`. -/
theorem rhoChar_pow_le_exp_lit (n : ℕ) :
    Zeta2XL1.rhoChar ^ n ≤ Real.exp (42.03361581 : ℝ) ^ n :=
  pow_le_pow_left₀ Zeta2XL1.rho_pos.le rhoChar_le_exp n

/-! ## Composition — the row applied where the chain consumes it (LEAN.md §3) -/

/-- **HC1 AND HC2 discharged inside L12's headline.**  Sixteen of `candidate_target_of_hc2`'s
seventeen binders survive; `c1` is pinned to `Real.log Zeta2XL1.rhoChar` throughout. -/
theorem candidate_target_of_hc1_hc2
    (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    {N₀ n₁ m₀ Nr Nq : ℕ} {Cr Cq c0 δ ε' : ℝ}
    (hc0 : (29.10787127 : ℝ) ≤ c0)
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
      |(Q n : ℝ)| ≤ Cq
        * Real.exp (Real.log Zeta2XL1.rhoChar + (31 - Zeta2DPhi.dPhi + ε')) ^ n) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2Hc2.candidate_target_of_hc2 Q P Δ α₀ α₁ α₂ α₃ hc0 hc1 hε' hδ hrecq hrecp hΔne hQ hP
    hN₁ hM₀ hα₃ hα₀ hrow hCr hdecay hCq hgrowth

/-- **The same, with the growth hypothesis in the shape QGROW PRODUCES.**  L5-at-`qₙ` delivers
`|qₙ| ≤ C · rhoChar ^ n`, so after the clearing the natural statement is
`|Q n| ≤ Cq · (rhoChar · exp c2) ^ n` — no `Real.log` anywhere in the hypothesis.  This theorem is
the whole of HC1's contribution to QGROW: the caller never has to see `exp (log rhoChar)`. -/
theorem candidate_target_of_rhoChar_growth
    (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    {N₀ n₁ m₀ Nr Nq : ℕ} {Cr Cq c0 δ ε' : ℝ}
    (hc0 : (29.10787127 : ℝ) ≤ c0)
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
      |(Q n : ℝ)| ≤ Cq
        * (Zeta2XL1.rhoChar * Real.exp (31 - Zeta2DPhi.dPhi + ε')) ^ n) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 := by
  -- `Nq` is implicit in the callee and appears only in the hypothesis being deferred, so it has
  -- to be pinned by name; without it the `?_` leaves `Nq` unsolvable (LEAN.md §3: composition
  -- fails on exactly this, and only the real application shows it).
  refine candidate_target_of_hc1_hc2 (Nq := Nq) Q P Δ α₀ α₁ α₂ α₃ hc0 hε' hδ hrecq hrecp hΔne hQ hP
    hN₁ hM₀ hα₃ hα₀ hrow hCr hdecay hCq ?_
  intro n hn
  rw [Real.exp_add, Real.exp_log Zeta2XL1.rho_pos]
  exact hgrowth n hn

#print axioms taylor_sum_eq
#print axioms rho_le_prod
#print axioms rhoChar_le_exp
#print axioms hc1
#print axioms rhoChar_pow_le_exp_c1
#print axioms rhoChar_pow_le_exp_lit
#print axioms candidate_target_of_hc1_hc2
#print axioms candidate_target_of_rhoChar_growth

end Zeta2Hc1
