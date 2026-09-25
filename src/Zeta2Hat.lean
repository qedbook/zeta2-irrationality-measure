/-
# Row PAIR-0 — the hat member's coordinates, as finite sums, agreeing with `qₙ` at the start

`docs/future/zeta2-lean-chain.md` row PAIR-0.  The candidate's Whipple hat
`(â; b̂) = (20n+2; 5n+1, 7n+1, 9n+1 / 3n+2; 1, 18n+2, 20n+2)` with kernel `π/sin 2πt`
(promotion doc F1) has, at integer `n`, the rational part

    R̂ₙ/Π̂ = ∏_{l=3n+2}^{20n+1} (2t+l) · ∏_{l=1}^{5n} (t+l) / [∏_{l=7n+1}^{18n+1} (t+l) · ∏_{l=9n+1}^{20n+1} (t+l)]

whose DOUBLE poles sit at `t = −k`, `k ∈ [10n+1, 18n+1]` (the two denominator blocks' overlap,
beyond the reach of the `(2t+l)` zeros).  The kernel's Laurent series at an even lattice point
has NO constant term (`1/(2u) + (π²/3)u + …`), so the ζ(2)-coordinate of the hat form is the
sum of the ORDER-2 partial-fraction coefficients alone, and `Π̂·A_k` regroups into four
binomials (`j = k − 10n − 1`):

    Π̂·A_k = C(17n+2j, 2j) · C(11n, 3n+j) · C(11n, n+j) · C(10n+j, 5n)  =: hatA n j.

The rational coordinate needs the order-1 coefficients too — `B_k = A_k·Λ_k` at the double
poles (a log-derivative, harmonic numbers) and the residues at the two runs of simple poles —
paired with the alternating sums `A(L, s) = Σ_{d=1}^{L} (−1)^d/d^s` the left-closing evaluator
produces at the pairing contour `Ĉ(n) = −4n − 3/4` (`L_k = 2k − 8n − 2`).

The derivation, and every number, are in `gen_hat_lean.py` beside this file: it equates this
closed form with the engine's partial fractions per coefficient, with the independent
half-lattice evaluator `mb2`, with the tale-1 engine (the PAIRING, n = 0..6) and with the
archived K7 literals, and carries falsifier arms.  This file is a TRANSCRIPTION of that
generator's `hatQ`/`hatP`, and `Zeta2HatCheck.lean` (generated) `#eval`s the two against the
engine literals.

Kernel-checked here: `hatQ n = qnInt n` for `n < 3` (the row's statement), lifted to
`(hatQ n : ℚ) = candidateM.qn n` through `qnInt_cast`; `hatP 0 = 0 = candidateM.pn 0`.
`hatP n = candidateM.pn n` at `n ≥ 1` is NOT stated: `candidateM.pn` goes through
`Polynomial ℚ` division (`pnPoly`), which is noncomputable and has no kernel evaluation in the
corpus until row RESID/PHI-EVAL — the engine literal for `hatP 1`, `hatP 2` is pinned instead.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2QnInt

namespace Zeta2Hat

open Zeta2Defs Zeta2Arith Nat Finset

/-! ## The ζ(2)-coordinate `hatQ` -/

/-- `Π̂·A_k` at the double pole `k = 10n+1+j`, `j ∈ [0, 8n]`: four binomial coefficients.
Kept in `Nat.choose` form because row PT-QB's Kummer/Legendre atom (`padicValNat_choose'`) is
stated on binomials; the small-`n` proofs below rewrite it to `descFactorial / factorial` first
(kernel `Nat.choose` recursion is exponential). -/
def hatA (n j : ℕ) : ℕ :=
  (17 * n + 2 * j).choose (2 * j) * (11 * n).choose (3 * n + j) * (11 * n).choose (n + j)
    * (10 * n + j).choose (5 * n)

/-- **`hatQ`** — the hat's ζ(2)-coordinate: `−Σ_{j ≤ 8n} hatA n j`.  The `−` is the tale-1 sign
`(−1)^d`, `d = 16n − 1` odd (`Zeta2Defs.Member.sgn` at the candidate). -/
def hatQ (n : ℕ) : ℤ := -∑ j ∈ range (8 * n + 1), (hatA n j : ℤ)

/-! ## The rational coordinate `hatP` -/

/-- `Π̂(n) = (11n)!² / ((17n)!(5n)!)` (`z2a.Pi_hat` at the candidate, promotion doc F3). -/
def hatPi (n : ℕ) : ℚ :=
  (((11 * n)! * (11 * n)! : ℕ) : ℚ) / (((17 * n)! * (5 * n)! : ℕ) : ℚ)

/-- `A(L, s) = Σ_{d=1}^{L} (−1)^d / d^s`, the alternating truncated sum (`mb2.Aalt`). -/
def altH (s L : ℕ) : ℚ := ∑ d ∈ range L, (-1) ^ (d + 1) / ((d : ℚ) + 1) ^ s

/-- `Λ_k = B_k / A_k` at the double pole `k = 10n+1+j`: the log-derivative of `(t+k)²·R̂/Π̂`,
written in harmonic numbers `harm 1 m = H_m`. -/
def hatLam (n j : ℕ) : ℚ :=
  -2 * (harm 1 (17 * n + 2 * j) - harm 1 (2 * j)) - (harm 1 (10 * n + j) - harm 1 (5 * n + j))
    + (harm 1 (3 * n + j) - harm 1 (8 * n - j)) + (harm 1 (n + j) - harm 1 (10 * n - j))

/-- `Π̂·B_k` at the "lo" simple pole `k = 9n+1+i`, `i ∈ [0, n−1]` (one `(2t+2k)` zero against
both denominator blocks). -/
def hatBlo (n i : ℕ) : ℚ :=
  hatPi n * ((2 * (15 * n + 2 * i)! * (2 * n - 1 - 2 * i)! * (9 * n + i)! : ℕ) : ℚ)
    / (((4 * n + i)! * (2 * n + i)! * (9 * n - i)! * i ! * (11 * n - i)! : ℕ) : ℚ)

/-- `Π̂·B_k` at the "hi" simple pole `k = 18n+2+i`, `i ∈ [0, 2n−1]` (second denominator block
only); sign `(−1)^i`. -/
def hatBhi (n i : ℕ) : ℚ :=
  (-1) ^ i * hatPi n
    * (((33 * n + 2 + 2 * i)! * (18 * n + 1 + i)! * i ! : ℕ) : ℚ)
    / (((16 * n + 2 + 2 * i)! * (13 * n + 1 + i)! * (11 * n + 1 + i)! * (9 * n + 1 + i)!
        * (2 * n - 1 - i)! : ℕ) : ℚ)

/-- **`hatP`** — the hat's rational coordinate at the pairing contour `Ĉ(n) = −4n − 3/4`:
`Σ_k [B_k·A(L_k,1) + 2·A_k·A(L_k,2)]`, `L_k = 2k − 8n − 2`, over the double poles
(`L = 12n+2j`), the lo simple poles (`L = 10n+2i`) and the hi simple poles (`L = 28n+2+2i`). -/
def hatP (n : ℕ) : ℚ :=
  (∑ j ∈ range (8 * n + 1),
      (hatA n j : ℚ) * (hatLam n j * altH 1 (12 * n + 2 * j) + 2 * altH 2 (12 * n + 2 * j)))
    + (∑ i ∈ range n, hatBlo n i * altH 1 (10 * n + 2 * i))
    + (∑ i ∈ range (2 * n), hatBhi n i * altH 1 (28 * n + 2 + 2 * i))

/-! ## The small instances, kernel-checked -/

theorem hatQ_zero : hatQ 0 = -1 := by decide

/-- `n = 0`: one double pole, `A_1 = 1`, `q₀ = −1` (`Zeta2Defs.Member.qn_zero`). -/
theorem hatQ_eq_qnInt_zero : hatQ 0 = qnInt 0 := by decide

/-- `n = 1`: 9 double poles, the largest binomial `C(33, 16)`; `Nat.choose` rewritten to
`descFactorial / factorial` so the kernel evaluates in polynomial time. -/
theorem hatQ_eq_qnInt_one : hatQ 1 = qnInt 1 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- `n = 2`: 17 double poles, the largest binomial `C(66, 32)`. -/
theorem hatQ_eq_qnInt_two : hatQ 2 = qnInt 2 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- **The row's statement**: `hatQ n = qnInt n` for `n < 3`. -/
theorem hatQ_eq_qnInt_small : ∀ n < 3, hatQ n = qnInt n := by
  intro n hn
  interval_cases n
  · exact hatQ_eq_qnInt_zero
  · exact hatQ_eq_qnInt_one
  · exact hatQ_eq_qnInt_two

/-- The same, at the chain's own object `candidateM.qn` (through `qnInt_cast`). -/
theorem hatQ_cast_eq_qn_small : ∀ n < 3, (hatQ n : ℚ) = candidateM.qn n := by
  intro n hn
  rw [hatQ_eq_qnInt_small n hn, qnInt_cast]

/-- `p̂₀ = 0`: the single double pole's alternating sums are empty (`L = 0`). -/
theorem hatP_zero : hatP 0 = 0 := by
  simp [hatP, altH]

/-- `p₀ = 0` on the chain's side: `Ppol 0 = 1 /ₘ (X + 1) = 0` and the harmonic half is
`harm 2 0 = 0`. -/
theorem candidate_pn_zero : candidateM.pn 0 = 0 := by
  have hnum : candidateM.numPoly 0 = 1 := by
    simp [Member.numPoly, block, candidateM]
  have hden : candidateM.denPoly 0 = Polynomial.X + Polynomial.C (1 : ℚ) := by
    simp [Member.denPoly, block, candidateM]
  have hPpol : candidateM.Ppol 0 = 0 := by
    rw [Member.Ppol, hnum, hden, Polynomial.divByMonic_eq_zero_iff (Polynomial.monic_X_add_C _)]
    rw [Polynomial.degree_one, Polynomial.degree_X_add_C]
    exact zero_lt_one
  have hpoly : candidateM.pnPoly 0 = 0 := by
    simp [Member.pnPoly, hPpol]
  have hharm : candidateM.pnHarm 0 = 0 := by
    simp [Member.pnHarm, Member.window_zero, Member.harmIndex, harm]
  rw [Member.pn, hpoly, hharm]
  simp

theorem hatP_eq_pn_zero : hatP 0 = candidateM.pn 0 := by
  rw [hatP_zero, candidate_pn_zero]

end Zeta2Hat

#print axioms Zeta2Hat.hatQ_eq_qnInt_zero
#print axioms Zeta2Hat.hatQ_eq_qnInt_one
#print axioms Zeta2Hat.hatQ_eq_qnInt_two
#print axioms Zeta2Hat.hatQ_eq_qnInt_small
#print axioms Zeta2Hat.hatQ_cast_eq_qn_small
#print axioms Zeta2Hat.hatP_zero
#print axioms Zeta2Hat.candidate_pn_zero
#print axioms Zeta2Hat.hatP_eq_pn_zero
