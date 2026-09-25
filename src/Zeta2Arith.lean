/-
# The arithmetic clearing, layer 0 — `D k = lcm(1..k)` as a Lean object

The chain (`Zeta2L9L11Instantiate.candidate_not_liouvilleWith`) binds `Δ : ℕ → ℝ` and
`hQ : ∀ n, (Q n : ℝ) = Δ n * qn n` as HYPOTHESES. The scope audit graded this the program's
largest unscoped row: no Lean object for `Δ` existed anywhere. This file is the first
bankable increment — the denominator-clearing object every later statement is built from,
with the two facts every use of it needs, typechecked against current Mathlib.

Increment 1 of N. Nothing here is candidate-specific. `Δ n = D (16 n) * D (15 n)` (the
naive form) is increment 2; the `Φ̃`-divisibility refinement that makes the number work is
later and is the part that carries mathematical content.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Basic.Real.Basic

namespace Zeta2Arith

/-- `D k = lcm(1, …, k)` — the classical denominator of the harmonic-type sums this chain
clears. `Finset.Icc 1 k` rather than `range` so that `0` is never a member (lcm with `0` is `0`). -/
def D (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

/-- `D k` is never zero: every member of `Icc 1 k` is positive. -/
theorem D_ne_zero (k : ℕ) : D k ≠ 0 := by
  unfold D
  rw [Finset.lcm_ne_zero_iff]
  intro x hx
  simp only [Finset.mem_Icc, id] at hx ⊢
  omega

/-- Every `m` in `1..k` divides `D k` — the property that makes it a common denominator. -/
theorem dvd_D {m k : ℕ} (h1 : 1 ≤ m) (hk : m ≤ k) : m ∣ D k :=
  Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨h1, hk⟩)

/-- `D` is monotone under divisibility: a larger range has a larger lcm. -/
theorem D_dvd_D {j k : ℕ} (h : j ≤ k) : D j ∣ D k :=
  Finset.lcm_mono (Finset.Icc_subset_Icc_right h)

/-- `D 1 = 1`, the base of the tower. -/
theorem D_one : D 1 = 1 := by
  unfold D
  simp

/-- `D k` is positive — the form `Nat.cast` lemmas want. -/
theorem D_pos (k : ℕ) : 0 < D k := Nat.pos_of_ne_zero (D_ne_zero k)

/-! ## The naive clearing factor, parametrised by the member's constants

`zeta2-arith-layer.md` derives, per member, two constants `c₁ c₂` from `(a, b)` such that
`D (c₁ n) * D (c₂ n) * pₙ ∈ ℤ` (tale-1: `(9, 8)`, measured at every `n ≤ 10`; R3: `(7, 7)`).
`qₙ ∈ ℤ` needs no clearing at all. The constants are NOT fixed here: they are pinned when the
integrality proof is attempted, because the doc's own transcription of them wobbled once
(`9n` vs `9n+1`, resolved only by the constant term of `d`). -/

/-- The naive clearing factor. The `Φ̃`-divisibility refinement that recovers the RATE is not
this object; `zeta2-scope-audit.md` records that with this `Δ` alone `u = C0 − 31 < 0`. -/
def Δ (c₁ c₂ n : ℕ) : ℕ := D (c₁ * n) * D (c₂ * n)

theorem Δ_ne_zero (c₁ c₂ n : ℕ) : Δ c₁ c₂ n ≠ 0 :=
  Nat.mul_ne_zero (D_ne_zero _) (D_ne_zero _)

theorem Δ_pos (c₁ c₂ n : ℕ) : 0 < Δ c₁ c₂ n := Nat.pos_of_ne_zero (Δ_ne_zero c₁ c₂ n)

/-- Cast to `ℝ`, `Δ` is nonzero — the exact shape of the chain's `hΔne`. -/
theorem Δ_cast_ne_zero (c₁ c₂ n : ℕ) : (Δ c₁ c₂ n : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Δ_ne_zero c₁ c₂ n)

end Zeta2Arith

#print axioms Zeta2Arith.D_ne_zero
#print axioms Zeta2Arith.dvd_D
#print axioms Zeta2Arith.D_dvd_D
#print axioms Zeta2Arith.D_one
#print axioms Zeta2Arith.D_pos
#print axioms Zeta2Arith.Δ_ne_zero
#print axioms Zeta2Arith.Δ_pos
#print axioms Zeta2Arith.Δ_cast_ne_zero
