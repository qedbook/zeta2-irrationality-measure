/-
# The irrationality measure of ζ(2) is at most 5.0495243

    theorem zeta2_not_liouvilleWith : ¬ LiouvilleWith (5.0495243 : ℝ) zeta2

Here `zeta2` is `Zeta2Defs.zeta2 := π²/6`, and `Zeta2Final.zeta2_eq_riemannZeta_two` proves that
it equals Mathlib's `riemannZeta 2`.  Mathlib's `LiouvilleWith p x` says that for some `C`, for
infinitely many `n` there is an `m` with `x ≠ m/n` and `|x − m/n| < C/n^p`.  The theorem is the
negation: for every `C` and every large enough `n`, `|ζ(2) − m/n| ≥ C/n^5.0495243` for every
integer `m` with `m/n ≠ ζ(2)`.  That is the bound `μ(ζ(2)) ≤ 5.0495243` on the irrationality
measure.  No hypothesis is taken; `zeta2_irrationality_measure_le` gives every `p ≥ 5.0495243`.

**Reading the receipt.**  The commands at the bottom of this file print, for both theorems, the
axioms the proof depends on and the statement's type.  The axioms are Lean's standard three,
`[propext, Classical.choice, Quot.sound]`; each type is the statement written below, nothing more.
Both are needed: `#print axioms` omits hypotheses, so a conditional theorem prints the same axioms.

**Why the constant is 5.0495243.**  The proof uses three exponential rates: the decay of
`qₙζ(2) − pₙ`, the growth of `qₙ`, and the growth of `Δ̃ₙ` (`Zeta2PhiT.ΔT`), the factor that makes
`Δ̃ₙqₙ` and `Δ̃ₙpₙ` integers.  It proves eight-decimal bounds on them, at least 29.10787127 for the
decay and at most 42.03361581 and 15.01912095 for the growths, and `Zeta2L12.L12_rational_gap` gives
`1 + (42.03361581 + 15.01912095)/(29.10787127 − 15.01912095 − 10⁻¹⁶) < 5.0495243`, the last term
being a slack in the decay rate.  At the rates' archived values, with slack `9.94·10⁻¹⁷`, the
exponent is `5.04952429053…`, so 5.0495243, which is 5.04952430, is the smallest bound with eight
decimal places that the proof gives (`Zeta2TWire.certified_value_is_strictly_between_the_two_literals`).

**What this file does not claim.**  The theorem is an upper bound for the irrationality measure
and asserts nothing below 5.0495243.  `Zeta2Defs` describes the construction and cites its paper.
Toolchain `leanprover/lean4:v4.34.0-rc2`; Mathlib at commit `5aedf732`.
-/
import Zeta2Unconditional
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

namespace Zeta2Target

open Zeta2Defs

/-- **The theorem.**  `¬ LiouvilleWith 5.0495243 ζ(2)`: the irrationality measure of
`ζ(2)` is at most `5.0495243`.  No hypothesis. -/
theorem zeta2_not_liouvilleWith : ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2Unconditional.zeta2_not_liouvilleWith

/-- The headline as an irrationality-measure bound, by `LiouvilleWith.mono`.

A Liouville property at an exponent implies it at every smaller exponent, so the statement at
`5.0495243` gives the bound at every larger exponent: one statement suffices. -/
theorem zeta2_irrationality_measure_le :
    ∀ p : ℝ, (5.0495243 : ℝ) ≤ p → ¬ LiouvilleWith p zeta2 := by
  intro p hp h
  exact zeta2_not_liouvilleWith (h.mono hp)

/-! ## Receipts — BOTH channels: the axioms AND the printed type, the statement and nothing more -/

#print axioms zeta2_not_liouvilleWith
#check @zeta2_not_liouvilleWith
#print axioms zeta2_irrationality_measure_le
#check @zeta2_irrationality_measure_le

end Zeta2Target
