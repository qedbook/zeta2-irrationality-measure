/-
# THE HEADLINE, UNCONDITIONAL — `μ(ζ(2)) ≤ 5.0495243`, with no binder

`Zeta2Final.zeta2_not_liouvilleWith_of_psi` proves the headline conditional on ONE hypothesis,
`hψ : Zeta2LegA.psiErrorBoundStatement`. `Zeta2Hpsi.hψ` proves that hypothesis from PNT+'s
`MediumPNT`, which is vendored at `external_tests/pnt_port/` and elaborated in this same kernel. This file
applies the one to the other. There are three forms, and none of them has a binder:

| theorem | statement |
|---|---|
| `zeta2_not_liouvilleWith` | `¬ LiouvilleWith 5.0495243 ζ(2)` |
| `zeta2_irrationality_measure_le` | `∀ p ≥ 5.0495243, ¬ LiouvilleWith p ζ(2)` |
| `zeta2_rational_approximation` | `∀ C, ∀ᶠ n, ∀ m, ζ(2) ≠ m/n → C / n ^ 5.0495243 ≤ |ζ(2) − m/n|` |

**The receipt is half the acceptance; the `#check @` type is the other half** (LEAN.md §1). A binder is
not an axiom, so the axioms list alone cannot tell this file from the conditional one. The
printed types below must name NO hypothesis. `falsify_unconditional.sh` arm U-D shows that the
type check is what discriminates.

**WHAT THIS FILE DOES NOT CLAIM.**
* It does not reach `5.04952429`. That numeral is the sweep's `μ̃` score, strictly stronger than
  the certified value; the chain proves `5.0495243` (`Zeta2Final.the_literal_is_the_chains`).
* It does not touch `Zeta2Target.lean` or its deliberate `sorry`. Whether that file changes is the
  owner's call.
* `Zeta2Defs.zeta2` is Mathlib's `riemannZeta 2` as a real
  (`Zeta2Final.zeta2_eq_riemannZeta_two`), and `LiouvilleWith` is Mathlib's.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox, clean store.
Runner `clean_close/run_clean_final.sh Zeta2Unconditional.lean`; falsifier `falsify_unconditional.sh`.
-/
import Zeta2Final
import Zeta2Hpsi

namespace Zeta2Unconditional

/-- **THE HEADLINE.** `ζ(2)` is not Liouville with exponent `5.0495243`, so its irrationality
measure is at most `5.0495243`. -/
theorem zeta2_not_liouvilleWith : ¬ LiouvilleWith (5.0495243 : ℝ) Zeta2Defs.zeta2 :=
  Zeta2Final.zeta2_not_liouvilleWith_of_psi Zeta2Hpsi.hψ

/-- **The measure form**: no exponent `p ≥ 5.0495243` makes `ζ(2)` Liouville-with-`p`. -/
theorem zeta2_irrationality_measure_le :
    ∀ p : ℝ, (5.0495243 : ℝ) ≤ p → ¬ LiouvilleWith p Zeta2Defs.zeta2 :=
  Zeta2Final.zeta2_irrationality_measure_le_of_psi Zeta2Hpsi.hψ

/-- **The rational-approximation form**, which is Mathlib's `LiouvilleWith` unfolded. For every constant `C`,
every large enough denominator `n`, and every integer `m` with `m / n ≠ ζ(2)`,
`|ζ(2) − m/n| ≥ C / n ^ 5.0495243`. -/
theorem zeta2_rational_approximation :
    ∀ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℤ,
      Zeta2Defs.zeta2 ≠ m / n → C / (n : ℝ) ^ (5.0495243 : ℝ) ≤ |Zeta2Defs.zeta2 - m / n| :=
  Zeta2Final.zeta2_rational_approximation_of_psi Zeta2Hpsi.hψ

end Zeta2Unconditional

/-! ## RECEIPTS — LEAN.md §1, BOTH channels, the type beside every receipt.

Acceptance: every receipt reads `[propext, Classical.choice, Quot.sound]`, AND the three printed
types name no hypothesis. `Zeta2Hpsi.hψ` and `MediumPNT` are printed too: the headline's
footprint is theirs plus the chain's. -/

#print axioms Zeta2Unconditional.zeta2_not_liouvilleWith
#check @Zeta2Unconditional.zeta2_not_liouvilleWith
#print axioms Zeta2Unconditional.zeta2_irrationality_measure_le
#check @Zeta2Unconditional.zeta2_irrationality_measure_le
#print axioms Zeta2Unconditional.zeta2_rational_approximation
#check @Zeta2Unconditional.zeta2_rational_approximation
#print axioms Zeta2Hpsi.hψ
#check @Zeta2Hpsi.hψ
#print axioms MediumPNT
#print axioms Zeta2Final.zeta2_eq_riemannZeta_two
#check @Zeta2Final.zeta2_eq_riemannZeta_two
