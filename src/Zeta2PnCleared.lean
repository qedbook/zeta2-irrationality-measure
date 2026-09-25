/-
# `Zeta2PnCleared.lean` — row PNCLR of `docs/future/zeta2-lean-chain.md`, two increments

**HEADLINE: `PnCleared` is NOT proved here, at either pair of constants.**  This file lands the
row's two SEPARABLE increments and says exactly what each is:

  * **The twin at the row's own constants.**  `PnClearedAt c₁ c₂` restates
    `Zeta2Arith.PnCleared` with the clearing pair as a PARAMETER; `pnClearedAt_1316` is the
    `Iff.rfl` back to the landed `(13,16)` statement, `pnClearedAt_of_dvd` transfers a clearing
    along `Δ ∣ Δ`, `Δ_1316_dvd_1615` is the instance the row names (`D(13n) ∣ D(15n)`), and
    `binders_of_pn_cleared_1615` is `Zeta2ArithAssemble.binders_of_pn_cleared` at `Δ 16 15` —
    the pair the headline μ needs (`Δ̃ₙ = Δ 16 15 n / Φ̃ₙ`), not the pair the naive integrality
    pin was measured at.  So a proof of `PnCleared` at `(13,16)` DELIVERS the `(16,15)` binders,
    and nothing in the chain has to be re-proved at the second pair.

  * **The von Staudt–Clausen step, the row's named unknown, discharged as a LEMMA.**
    `D_mul_momI_int : j + 1 ≤ m → ∃ z : ℤ, (D m : ℚ) * momI M j = z`.  Every Bernoulli moment
    `momI (cell n) j = B_j(−4n)` occurring in `pnPoly` (`j ≤ 16n − 1`, `Ppol_natDegree`) is
    therefore cleared by the single factor `D (16n)` of `Δ 16 15 n` — `D_mul_momI_pnPoly_range`.
    The Mathlib API is `Bernoulli.vonStaudt_clausen` (`Mathlib/NumberTheory/Bernoulli.lean`,
    current Mathlib): `B_{2k} + Σ_{p prime, (p−1) ∣ 2k, p < 2k+2} 1/p ∈ ℤ`.

**WHAT THIS DOES NOT PROVE, and the measurement that says so.**  `Δ · pₙ ∈ ℤ` does NOT follow
from the moments' denominators.  `pnPoly n = Σ_j (Ppol n).coeff j · momI (cell n) j` is
multiplied by `Π(n) = (11n)!/((13n)!(9n)!(5n)!)`, whose `p`-adic valuations are NEGATIVE, and
`Π · (Ppol n).coeff j ∉ ℤ` at EVERY `j` (measured, n ≤ 5: 16/16, 32/32, 48/48, 64/64, 80/80).
The polynomial half's integrality is therefore a statement about the SUM over `j`, and the
moments' von Staudt denominators are one bounded ingredient of it, not the obstruction.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2ArithBridge
import Zeta2ArithAssemble

namespace Zeta2PnCleared

open Zeta2Defs Zeta2Arith Finset

/-! ## 1. The clearing statement with the constants as parameters -/

/-- **`PnClearedAt c₁ c₂`** — `Δ c₁ c₂ n · pₙ ∈ ℤ` for every `n`.  `Zeta2Arith.PnCleared` is
this at `(13,16)`; the chain's headline needs it at `(16,15)`. -/
def PnClearedAt (c₁ c₂ : ℕ) : Prop :=
  ∃ P : ℕ → ℤ, ∀ n, (P n : ℚ) = ((Δ c₁ c₂ n : ℕ) : ℚ) * candidateM.pn n

/-- The landed statement is this one at the pinned naive constants — definitionally. -/
theorem pnClearedAt_1316 : PnClearedAt 13 16 ↔ Zeta2Arith.PnCleared := Iff.rfl

/-- **A clearing transfers along divisibility of the clearing factors.**  The witness is
`(Δ₂ / Δ₁) · P`, an integer because the quotient is one. -/
theorem pnClearedAt_of_dvd {c₁ c₂ c₃ c₄ : ℕ} (hdvd : ∀ n, Δ c₁ c₂ n ∣ Δ c₃ c₄ n)
    (h : PnClearedAt c₁ c₂) : PnClearedAt c₃ c₄ := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun n => ((Δ c₃ c₄ n / Δ c₁ c₂ n : ℕ) : ℤ) * P n, fun n => ?_⟩
  have hne : ((Δ c₁ c₂ n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Δ_ne_zero c₁ c₂ n
  have hq : ((Δ c₃ c₄ n / Δ c₁ c₂ n : ℕ) : ℚ)
      = ((Δ c₃ c₄ n : ℕ) : ℚ) / ((Δ c₁ c₂ n : ℕ) : ℚ) := Nat.cast_div (hdvd n) hne
  have hPn := hP n
  rw [Int.cast_mul, Int.cast_natCast, hq, hPn]
  field_simp

/-- `Δ 13 16 n ∣ Δ 16 15 n`, because `D(13n) ∣ D(15n)` (`D_dvd_D`). -/
theorem Δ_1316_dvd_1615 (n : ℕ) : Δ 13 16 n ∣ Δ 16 15 n := by
  have h : D (13 * n) ∣ D (15 * n) := D_dvd_D (by omega)
  have h2 := mul_dvd_mul h (dvd_refl (D (16 * n)))
  unfold Δ
  rw [mul_comm (D (16 * n)) (D (15 * n))]
  exact h2

/-- The naive pinned clearing implies the clearing at the pair the headline μ is built on. -/
theorem pnClearedAt_1615_of_1316 (h : Zeta2Arith.PnCleared) : PnClearedAt 16 15 :=
  pnClearedAt_of_dvd Δ_1316_dvd_1615 (pnClearedAt_1316.mpr h)

/-! ## 2. The chain's three arithmetic binders at `Δ 16 15` -/

/-- **`Zeta2ArithAssemble.binders_of_pn_cleared` at `(16,15)`.**  `hΔne` and `hQ` carry no
hypothesis (increments 1–3); `hP` is the witness of `PnClearedAt 16 15`.  Every bridge lemma is
`Δ`-generic, so this is the same composition at the other pair, not a second proof. -/
theorem binders_of_pn_cleared_1615 (hp : PnClearedAt 16 15) :
    ∃ (Q P : ℕ → ℤ),
      (∀ n, ((Δ 16 15 n : ℕ) : ℝ) ≠ 0) ∧
      (∀ n, (Q n : ℝ) = ((Δ 16 15 n : ℕ) : ℝ) * ((candidateM.qn n : ℚ) : ℝ)) ∧
      (∀ n, (P n : ℝ) = ((Δ 16 15 n : ℕ) : ℝ) * ((candidateM.pn n : ℚ) : ℝ)) := by
  obtain ⟨P, hP⟩ := hp
  refine ⟨fun n => ((Δ 16 15 n : ℕ) : ℤ) * qnInt n, P, hΔne_of_Δ 16 15, fun n => ?_,
    hP_of_cleared P 16 15 hP⟩
  exact_mod_cast hQ_of_qn_int qnInt qnInt_cast 16 15 n

/-- The composition executed (LEAN.md §3): the LANDED `(13,16)` hypothesis delivers the
`(16,15)` binders, with no second clearing proof. -/
theorem binders_1615_of_PnCleared (h : Zeta2Arith.PnCleared) :
    ∃ (Q P : ℕ → ℤ),
      (∀ n, ((Δ 16 15 n : ℕ) : ℝ) ≠ 0) ∧
      (∀ n, (Q n : ℝ) = ((Δ 16 15 n : ℕ) : ℝ) * ((candidateM.qn n : ℚ) : ℝ)) ∧
      (∀ n, (P n : ℝ) = ((Δ 16 15 n : ℕ) : ℝ) * ((candidateM.pn n : ℚ) : ℝ)) :=
  binders_of_pn_cleared_1615 (pnClearedAt_1615_of_1316 h)

/-! ## 3. von Staudt–Clausen: the moments' denominators divide `D m`

**WHICH `momI` — read this before reusing anything below.**  The corpus has TWO constants called
`momI` and they are NOT the same: `Zeta2Defs.momI M j = (Polynomial.bernoulli j).eval (M+1)`,
which everything here is about and which `Member.pnPoly` sums, and `Zeta2Moments.momI`, the §5.2
four-line recursion, which `Φ` is built on.  **No `rfl` bridges them** — the bridge is the theorem
`Zeta2T1Eval.momI_agree` (through `Zeta2Moments.momI_eq_bernoulli`), and row PHI-EVAL hit this
independently on 2026-09-14 while this row hit it on 2026-09-15.  Two units, one duplication, so
the note is left HERE, where the next reader meets the object: if you want `D m · momI M j ∈ ℤ`
for the §5.2 recursion's `momI`, rewrite with `momI_agree` FIRST and then apply
`D_mul_momI_int`.  (The sibling duplication `harm` IS `rfl`, which is why these two had to be
measured rather than assumed alike.)
-/

/-- **At an integer argument a Bernoulli POLYNOMIAL value is its Bernoulli NUMBER plus an
integer.**  `Polynomial.bernoulli_eval_one_add` stepped both ways from
`Polynomial.bernoulli_eval_zero`.  This is what makes the von Staudt bound about `momI`, whose
argument is `cell n + 1 = −4n`, rather than only about `B_j`. -/
theorem bernoulli_eval_intCast (j : ℕ) (x : ℤ) :
    ∃ z : ℤ, (Polynomial.bernoulli j).eval ((x : ℚ)) = _root_.bernoulli j + (z : ℚ) := by
  induction x using Int.induction_on with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z + (j : ℤ) * (k : ℤ) ^ (j - 1), ?_⟩
      have hstep := Polynomial.bernoulli_eval_one_add j (k : ℚ)
      have hx : (((k : ℤ) + 1 : ℤ) : ℚ) = 1 + (k : ℚ) := by push_cast; ring
      rw [hx, hstep]
      push_cast at hz ⊢
      rw [hz]
      ring
  | pred k ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z - (j : ℤ) * (-(k : ℤ) - 1) ^ (j - 1), ?_⟩
      have hstep := Polynomial.bernoulli_eval_one_add j (-(k : ℚ) - 1)
      have hx : (1 : ℚ) + (-(k : ℚ) - 1) = ((-(k : ℤ) : ℤ) : ℚ) := by push_cast; ring
      rw [hx] at hstep
      have hy : ((-(k : ℤ) - 1 : ℤ) : ℚ) = -(k : ℚ) - 1 := by push_cast; ring
      rw [hy]
      push_cast at hz hstep ⊢
      linarith [hz, hstep]

/-- **von Staudt–Clausen, consumed.**  `D m` clears `B_j` as soon as `j + 1 ≤ m`: every prime in
`B_j`'s denominator satisfies `p − 1 ∣ j` and `p < j + 2`, hence `p ≤ m`, hence `p ∣ D m`
(`dvd_D`), and each occurs to the first power because the correction sum is `Σ 1/p`. -/
theorem D_mul_bernoulli_int (j m : ℕ) (h : j + 1 ≤ m) :
    ∃ z : ℤ, ((D m : ℕ) : ℚ) * _root_.bernoulli j = (z : ℚ) := by
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨k, hk⟩ := he
    have hj : j = 2 * k := by omega
    subst hj
    rcases Nat.eq_zero_or_pos k with rfl | _hkpos
    · exact ⟨(D m : ℤ), by norm_num⟩
    · obtain ⟨z₀, hz₀⟩ := Bernoulli.vonStaudt_clausen k
      set S : Finset ℕ := {p ∈ range (2 * k + 2) | p.Prime ∧ (p - 1) ∣ 2 * k} with hS
      refine ⟨(D m : ℤ) * z₀ - ∑ p ∈ S, ((D m / p : ℕ) : ℤ), ?_⟩
      have hb : _root_.bernoulli (2 * k) = (z₀ : ℚ) - ∑ p ∈ S, (1 : ℚ) / p := by
        rw [hz₀]
        ring
      have hterm : ∀ p ∈ S, ((D m : ℕ) : ℚ) * ((1 : ℚ) / p) = (((D m / p : ℕ) : ℤ) : ℚ) := by
        intro p hp
        have hmem := Finset.mem_filter.mp hp
        have hprime : p.Prime := hmem.2.1
        have hlt : p < 2 * k + 2 := Finset.mem_range.mp hmem.1
        have hple : p ≤ m := by omega
        have hdvd : p ∣ D m := dvd_D hprime.pos hple
        have hpne : ((p : ℕ) : ℚ) ≠ 0 := by
          exact_mod_cast hprime.ne_zero
        rw [mul_one_div, ← Nat.cast_div hdvd hpne, Int.cast_natCast]
      rw [hb, mul_sub, Finset.mul_sum, Finset.sum_congr rfl hterm]
      push_cast
      ring
  · rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr ho.pos.ne') with h1 | h1
    · -- `j = 1`: `B₁ = −1/2`, and `2 ≤ m` from `j + 1 ≤ m`
      have hj : j = 1 := h1.symm
      subst hj
      have h2 : (2 : ℕ) ∣ D m := dvd_D (by omega) (by omega)
      have hne : ((2 : ℕ) : ℚ) ≠ 0 := by norm_num
      have hdiv : ((D m / 2 : ℕ) : ℚ) = ((D m : ℕ) : ℚ) / ((2 : ℕ) : ℚ) := Nat.cast_div h2 hne
      refine ⟨-((D m / 2 : ℕ) : ℤ), ?_⟩
      rw [_root_.bernoulli_one, Int.cast_neg, Int.cast_natCast, hdiv]
      push_cast
      ring
    · exact ⟨0, by rw [_root_.bernoulli_eq_zero_of_odd ho h1]; ring⟩

/-- **The row's von Staudt step, at the row's own object.**  `momI M j = B_j(M+1)` is cleared by
`D m` whenever `j + 1 ≤ m` — for ANY integer cell `M`. -/
theorem D_mul_momI_int (M : ℤ) (j m : ℕ) (h : j + 1 ≤ m) :
    ∃ z : ℤ, ((D m : ℕ) : ℚ) * momI M j = (z : ℚ) := by
  obtain ⟨z₁, h₁⟩ := bernoulli_eval_intCast j (M + 1)
  obtain ⟨z₂, h₂⟩ := D_mul_bernoulli_int j m h
  refine ⟨z₂ + (D m : ℤ) * z₁, ?_⟩
  have hcast : (((M + 1 : ℤ)) : ℚ) = (M : ℚ) + 1 := by push_cast; ring
  rw [hcast] at h₁
  have hmom : momI M j = (Polynomial.bernoulli j).eval ((M : ℚ) + 1) := rfl
  rw [hmom, h₁, mul_add, h₂]
  push_cast
  ring

/-- **The consumer's shape**: every moment index `pnPoly n` sums over is `j ≤ 16n − 1`
(`candidate_Ppol_natDegree`), so the single factor `D (16n)` of `Δ 16 15 n` clears it.  This is
the whole von Staudt contribution to PNCLR — the row's remaining content is the `Π(n)` factor,
which this says nothing about (file header). -/
theorem D_mul_momI_pnPoly_range (n j : ℕ) (hn : 1 ≤ n) (hj : j ≤ 16 * n - 1) :
    ∃ z : ℤ, ((D (16 * n) : ℕ) : ℚ) * momI (candidateM.cell n) j = (z : ℚ) :=
  D_mul_momI_int _ j _ (by omega)

end Zeta2PnCleared

#print axioms Zeta2PnCleared.pnClearedAt_1316
#print axioms Zeta2PnCleared.pnClearedAt_of_dvd
#print axioms Zeta2PnCleared.Δ_1316_dvd_1615
#print axioms Zeta2PnCleared.pnClearedAt_1615_of_1316
#print axioms Zeta2PnCleared.binders_of_pn_cleared_1615
#print axioms Zeta2PnCleared.binders_1615_of_PnCleared
#print axioms Zeta2PnCleared.bernoulli_eval_intCast
#print axioms Zeta2PnCleared.D_mul_bernoulli_int
#print axioms Zeta2PnCleared.D_mul_momI_int
#print axioms Zeta2PnCleared.D_mul_momI_pnPoly_range
