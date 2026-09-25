/-
# D3 at the REAL objects — L9/L11 applied to `Zeta2Defs.Member.rn` / `.qn` / `.pn`

`Zeta2Instantiate.lean` (row 2B0.V) did this for the GROWTH side: it handed the landed
`star_growth_bound_eventual` the real `rn` and read off what came out.  This file does it for
the two links D3 owns, and takes the composition one step further — the conclusion here is not
another rate bound, it is the headline's own predicate `¬ LiouvilleWith p₀ zeta2` at the
candidate's `zeta2`, `qn`, `pn`, `rn`.

**What this buys.**  The composition, EXECUTED rather than asserted (`LEAN.md` §3).  Every
hypothesis of `not_liouvilleWith_of_chain` was stated in the vocabulary the chain's rows
produce, and this file is the test of that claim: it goes through with no re-statement, no cast
repair and no index shift, which is the thing that failed both times it was tried earlier in
this program.

**What it does NOT buy.**  Nothing here is unconditional.  Five inputs remain open and are
named as hypotheses: `hrecq`/`hrecp` (L1, rows B1–B5), `hα₃`/`hα₀` and `hrow` (L4 + the exact
`m₀ = 1120` / `q_1127 ≠ 0` residue, row D4-L4 — **that data is not in the repo**), `hdecay`
(L7 + L8, the blocker), `hgrowth` (L5 + L10), and `hgap` (L12's certified arithmetic).  The
honest position of this row is: the interface is fitted, the inputs are named, and the inputs
are the work.

**CORRECTED 2026-09-09 — "that data is not in the repo" is spent, and the replacement is a
DIFFERENT obligation, not the same one.**  It was true when this file was written (2026-09-08).
Hours later `533c3b114` landed `external_tests/chain_close_design/results/solution_a.txt` plus
`l4_data.py`, which rebuilds all four degree-510 `cleared_j` from it in ~0.4 s, and
`external_tests/zeta2_small_rows/Zeta2L4.lean` proves `c0_ne_zero`, `c3_ne_zero` and
`q1127_ne_zero` axiom-clean.  `hα₃`/`hα₀`/`hrow` are still hypotheses below, but the reason has
changed: `Zeta2L4` speaks about `List ℤ` through `Zeta2L4.hornerZ`, this file wants `ℕ → ℝ`,
and `Zeta2XL1.lean` records that **no `List ℤ → ℝ[X]` bridge exists anywhere in this corpus**.
`zeta2-l9-l11.md` §5's *"landing D4-L4 discharges `hα₀`, `hα₃`, `hrow` and `hM₀`/`hN₁`
verbatim, with no restatement"* is therefore NOT established — the same over-claim
`Zeta2XL1B` §3 found in A5's `hL` sentence, and it is corrected there too.

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox; Lean
never runs on the laptop (owner ruling 2026-09-07).
-/
import Zeta2L9L11
import Zeta2Defs

namespace Zeta2L9L11Instantiate

open Zeta2Defs

/-- The cleared linear form IS the clearing factor times `r_n`: `Q_n ζ − P_n = Δ_n · r_n`.

This one identity is the whole reason L11's decay hypothesis can be fed from L7/L8 (a bound on
`r_n`) and L10 (a bound on `Δ_n`) separately — see `Zeta2L9L11.clearing_rate`. -/
theorem cleared_linear_form (m : Member) (Q P : ℕ → ℤ) (Δ : ℕ → ℝ)
    (hQ : ∀ n, (Q n : ℝ) = Δ n * ((m.qn n : ℚ) : ℝ))
    (hP : ∀ n, (P n : ℝ) = Δ n * ((m.pn n : ℚ) : ℝ)) (n : ℕ) :
    (Q n : ℝ) * zeta2 - (P n : ℝ) = Δ n * m.rn n := by
  rw [hQ n, hP n]
  simp only [Member.rn]
  ring

/-- **D3 at the candidate.**  `¬ LiouvilleWith p₀ ζ(2)` for the member the μ ≤ 5.0495243 bound
is about, from the chain's own inputs at `candidateM.qn` / `.pn` / `.rn`.

Hypothesis census — every one of these is a NAMED row of `zeta2-integral-free.md` §5.3:

| hypothesis | row | status in the repo |
|---|---|---|
| `hrecq`, `hrecp` | B1–B5 (L1) | open |
| `hΔne`, `hQ`, `hP` | A1–A4 / L10 clearing | open (definitional once the certificate tier lands) |
| `hα₃`, `hα₀`, `hrow` | D4 (L4) — `m₀ = 1120`, `q_1127 ≠ 0` | **in the repo and PROVED** since `533c3b114` (`Zeta2L4.c0_ne_zero` / `c3_ne_zero` / `q1127_ne_zero`); open here only for want of a `List ℤ → ℝ[X]` bridge — CORRECTED 2026-09-09, this cell read "computed, **not in the repo**" |
| `hdecay` | C1–C7 (L7) + L8 + L10 | the blocker |
| `hgrowth` | D1 (L5) + L10 | L5 closed abstractly; not yet at `qn` |
| `hgap` | L12 | certified numerically |

The decay hypothesis is deliberately stated on `Δ n * candidateM.rn n` rather than on
`Q n · ζ − P n`: those are equal (`cleared_linear_form`), but only the first is in the
vocabulary L7/L8/L10 speak. -/
theorem candidate_not_liouvilleWith
    (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    {N₀ n₁ m₀ Nr Nq : ℕ} {p₀ Cr ρr Cq ρq : ℝ}
    (hp₀ : 1 < p₀)
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
    (hCr : 0 < Cr) (hρr0 : 0 < ρr) (hρr1 : ρr < 1)
    (hdecay : ∀ n, Nr ≤ n → |Δ n * candidateM.rn n| ≤ Cr * ρr ^ n)
    (hCq : 0 < Cq) (hρq : 1 ≤ ρq)
    (hgrowth : ∀ n, Nq ≤ n → |(Q n : ℝ)| ≤ Cq * ρq ^ n)
    (hgap : ρq * ρr ^ (p₀ - 1) < 1) :
    ¬ LiouvilleWith p₀ zeta2 := by
  refine Zeta2L9L11.not_liouvilleWith_of_chain (Nr := Nr)
    (fun n => ((candidateM.qn n : ℚ) : ℝ)) (fun n => ((candidateM.pn n : ℚ) : ℝ))
    Q P Δ α₀ α₁ α₂ α₃ hp₀ hrecq hrecp hΔne hQ hP hN₁ hM₀ hα₃ hα₀ ?_ hCr hρr0 hρr1 ?_
    hCq hρq hgrowth hgap
  · obtain ⟨k, hk, hqk⟩ := hrow
    exact ⟨k, hk, by exact_mod_cast hqk⟩
  · intro n hn
    rw [cleared_linear_form candidateM Q P Δ hQ hP n]
    exact hdecay n hn

/-- **The literal §5.1 target, conditional on the named rows.**  With the rates written the way
the chain writes them — `ρr = e^(−u)`, `ρq = e^v` — and L12's certified `1 + v/u < 5.0495243`,
this is `Zeta2Target.zeta2_not_liouvilleWith` with its `sorry` replaced by an explicit list of
what is still owed.

`5.0495243` is the constant of `zeta2-integral-free.md` §5.1: strictly above the certified
`1 + v/(u−δ) = 5.049524290530377` and strictly below the record's certified `5.095411785826`. -/
theorem candidate_target_of_rates
    (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    {N₀ n₁ m₀ Nr Nq : ℕ} {Cr Cq u v : ℝ}
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
    (hCr : 0 < Cr) (hu : 0 < u) (hv : 0 ≤ v)
    (hdecay : ∀ n, Nr ≤ n → |Δ n * candidateM.rn n| ≤ Cr * Real.exp (-u) ^ n)
    (hCq : 0 < Cq)
    (hgrowth : ∀ n, Nq ≤ n → |(Q n : ℝ)| ≤ Cq * Real.exp v ^ n)
    (hmu : 1 + v / u < 5.0495243) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 := by
  have hρr0 : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
  have hρr1 : Real.exp (-u) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hρq : (1:ℝ) ≤ Real.exp v := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hv
  exact candidate_not_liouvilleWith Q P Δ α₀ α₁ α₂ α₃ (by norm_num) hrecq hrecp hΔne hQ hP
    hN₁ hM₀ hα₃ hα₀ hrow hCr hρr0 hρr1 hdecay hCq hρq hgrowth
    (Zeta2L9L11.gap_of_rate_bound hu hmu)

/-- The headline as an irrationality-measure bound, exactly as `Zeta2Target` derives it — but
here from the conditional statement above rather than from a `sorry`. -/
theorem candidate_measure_le (h : ¬ LiouvilleWith (5.0495243 : ℝ) zeta2) :
    ∀ p : ℝ, (5.0495243 : ℝ) ≤ p → ¬ LiouvilleWith p zeta2 :=
  Zeta2L9L11.measure_le_of_not_liouvilleWith h

/-! ## Receipts

Every line must read `[propext, Classical.choice, Quot.sound]`.  `Zeta2Target.lean`'s deliberate
`sorry` is NOT in this file's dependency graph: nothing here imports it. -/

#print axioms cleared_linear_form
#print axioms candidate_not_liouvilleWith
#print axioms candidate_target_of_rates
#print axioms candidate_measure_le

end Zeta2L9L11Instantiate
