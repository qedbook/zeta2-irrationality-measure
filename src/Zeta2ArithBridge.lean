/-
# The arithmetic clearing, layer 1 — the chain's `hQ`/`hP` binders, from integrality

`Zeta2L9L11Instantiate.candidate_not_liouvilleWith` binds

    (Q P : ℕ → ℤ) (Δ : ℕ → ℝ)
    (hΔne : ∀ n, Δ n ≠ 0)
    (hQ : ∀ n, (Q n : ℝ) = Δ n * ((candidateM.qn n : ℚ) : ℝ))
    (hP : ∀ n, (P n : ℝ) = Δ n * ((candidateM.pn n : ℚ) : ℝ))

This file proves that those three binders FOLLOW from two integrality facts —
`qₙ ∈ ℤ` (no clearing; `zeta2-arith-layer.md` measures it three times) and
`Δ c₁ c₂ n * pₙ ∈ ℤ` — by cast arithmetic alone. No `sorry` anywhere: the integrality facts
are HYPOTHESES here (LEAN.md §7, the hypothesis form), and proving them is the next
increment. What this file attests is that the OBJECTS COMPOSE: `Zeta2Arith.Δ`'s type,
`Zeta2Defs.candidateM.qn`'s type and the `ℕ → ℤ → ℚ → ℝ` cast chain meet at the chain's
exact binder shapes. That is the check every previous "scoped" row failed at composition
time (LEAN.md §3), executed on the smallest instance that can fail.

Increment 2 of the arithmetic clearing. ~seconds.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith

namespace Zeta2Arith

open Zeta2Defs

/-- The chain's `hΔne`, discharged: `Δ` cast to `ℝ` is nonzero. -/
theorem hΔne_of_Δ (c₁ c₂ : ℕ) : ∀ n, ((Δ c₁ c₂ n : ℕ) : ℝ) ≠ 0 :=
  fun n => Δ_cast_ne_zero c₁ c₂ n

/-- **The chain's `hQ`, from `qₙ ∈ ℤ`.**  `qₙ` needs no clearing, so `Q n = Δ n * q n` with
`q n : ℤ` the integer `qₙ` is; the binder wants it stated through `ℝ`. -/
theorem hQ_of_qn_int (q : ℕ → ℤ) (hq : ∀ n, (q n : ℚ) = candidateM.qn n) (c₁ c₂ : ℕ) :
    ∀ n, (((Δ c₁ c₂ n : ℕ) : ℤ) * q n : ℝ) = ((Δ c₁ c₂ n : ℕ) : ℝ) * ((candidateM.qn n : ℚ) : ℝ) := by
  intro n
  rw [← hq n]
  push_cast
  ring

/-- **The chain's `hP`, from `Δ · pₙ ∈ ℤ`.**  Here the clearing is the whole content: `P n` is
the integer that `Δ c₁ c₂ n * pₙ` equals. -/
theorem hP_of_cleared (P : ℕ → ℤ) (c₁ c₂ : ℕ)
    (hP : ∀ n, (P n : ℚ) = ((Δ c₁ c₂ n : ℕ) : ℚ) * candidateM.pn n) :
    ∀ n, (P n : ℝ) = ((Δ c₁ c₂ n : ℕ) : ℝ) * ((candidateM.pn n : ℚ) : ℝ) := by
  intro n
  have h := hP n
  have h' : ((P n : ℚ) : ℝ) = (((Δ c₁ c₂ n : ℕ) : ℚ) * candidateM.pn n : ℚ) := by rw [h]
  push_cast at h' ⊢
  exact h'

end Zeta2Arith

#print axioms Zeta2Arith.hΔne_of_Δ
#print axioms Zeta2Arith.hQ_of_qn_int
#print axioms Zeta2Arith.hP_of_cleared
