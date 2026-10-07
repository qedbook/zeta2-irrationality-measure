/-
# The headline theorem in three forms, with no hypothesis

`Zeta2Final.zeta2_not_liouvilleWith_of_psi` proves the headline from one hypothesis,
`hψ : Zeta2LegA.psiErrorBoundStatement`, an error bound for Chebyshev's function `ψ`.
`Zeta2Hpsi.hψ` proves that hypothesis from `MediumPNT`, the prime number theorem with error term
`O(x·exp(−c·(log x)^{1/10}))` from the PrimeNumberTheoremAnd project, which is vendored with this
development (see `PROVENANCE.md`) and checked by the same kernel.  This file applies the one to
the other.  There are three forms, and none of them has a hypothesis:

| theorem | statement |
|---|---|
| `zeta2_not_liouvilleWith` | `¬ LiouvilleWith 5.0495243 ζ(2)` |
| `zeta2_irrationality_measure_le` | `∀ p ≥ 5.0495243, ¬ LiouvilleWith p ζ(2)` |
| `zeta2_rational_approximation` | `∀ C, ∀ᶠ n, ∀ m, ζ(2) ≠ m/n → C / n ^ 5.0495243 ≤ |ζ(2) − m/n|` |

**Reading the receipt.**  The commands at the bottom of this file print each theorem's axioms and
its type.  Every axiom list must read `[propext, Classical.choice, Quot.sound]`, and each printed
type must be the statement written below, nothing more.  Both checks are needed: `#print axioms`
does not list hypotheses, so the conditional theorem in `Zeta2Final` prints the same three axioms,
and only the types tell the two apart.

**What this file does not claim.**  It claims the bound at `5.0495243` and at every larger
exponent, and nothing below `5.0495243`; `Zeta2Target` explains the constant.  `Zeta2Defs.zeta2`
is `π²/6`, which `Zeta2Final.zeta2_eq_riemannZeta_two` identifies with Mathlib's
`riemannZeta 2`, and `LiouvilleWith` is Mathlib's definition.


Toolchain `leanprover/lean4:v4.34.0-rc2`; Mathlib at commit `5aedf732`.
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

/-! ## Receipts: the axioms and the type of each theorem

Acceptance: every receipt reads `[propext, Classical.choice, Quot.sound]`, AND each of the three
printed types is the statement written above, nothing more. `Zeta2Hpsi.hψ` and `MediumPNT` are
printed too: the headline's footprint is theirs plus the chain's. -/

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
