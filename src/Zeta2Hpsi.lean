/-
# `hψ`: the error bound for Chebyshev's `ψ`, proved from `MediumPNT`

`Zeta2LegA.psiErrorBoundStatement` is the prime-number-theorem input of the ζ(2) proof: for some
`c > 0` and `C`, eventually `|ψ(x) − x| ≤ C·exp(−c·(log x)^{1/10})·x`, where `ψ` is Chebyshev's
function.  This file proves that `Prop`, imported from `Zeta2LegA` rather than restated here,
from `PrimeNumberTheoremAnd.MediumPNT`, which is vendored with two one-line patches (see
`PROVENANCE.md`):

```
MediumPNT : ∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * exp (-c * (log x) ^ (1 / 10))
```

The proof unpacks the `IsBigO` into the pointwise, eventual form of
`Zeta2LegA.psiErrorBoundStatement`.

**What this file does not claim.**  It does not reprove `MediumPNT`, which is the
PrimeNumberTheoremAnd project's theorem; its `#print axioms` below shows that the vendored files
prove it from Lean's three standard axioms, with no `sorryAx`.  This development's part is the
two patches, which repair tactic behaviour on this toolchain, and this unpacking.


Toolchain `leanprover/lean4:v4.34.0-rc2`; Mathlib at commit `5aedf732`.
-/
import PrimeNumberTheoremAnd.MediumPNT
import Zeta2LegA

open Filter Asymptotics
open scoped Topology

namespace Zeta2Hpsi

/-- **hψ, discharged.** The chain's `Zeta2LegA.psiErrorBoundStatement`, from `MediumPNT`:
`|ψ x − x| ≤ C · exp(−c·(log x)^{1/10}) · x` eventually. -/
theorem hψ : Zeta2LegA.psiErrorBoundStatement := by
  show ∃ c > 0, ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
    |Chebyshev.psi x - x| ≤ C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x
  obtain ⟨c, hc, hO⟩ := MediumPNT
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  refine ⟨c, hc, C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hx
  have hnn : (0 : ℝ) ≤ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by positivity
  rw [abs_of_nonneg hnn] at hx
  calc |Chebyshev.psi x - x|
      ≤ C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := hx
    _ = C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x := by ring

end Zeta2Hpsi

/-! ## Receipts: axioms and types

`sorryAx` in `MediumPNT`'s footprint would mean the vendored files do not prove it on this pin;
its absence covers every declaration `MediumPNT`'s proof uses, 324 of the vendored cone's 750
and none from LeanArchitect (`PROVENANCE.md`).  `Zeta2Hpsi.hψ` must print the same three axioms,
and `#check @` must print `Zeta2Hpsi.hψ : Zeta2LegA.psiErrorBoundStatement`.  The `#print`s show
the target `Prop` and its `ψ`, Mathlib's `Chebyshev.psi`, which no vendored definition shadows. -/

#print axioms MediumPNT
#check @MediumPNT
#print axioms Zeta2Hpsi.hψ
#check @Zeta2Hpsi.hψ
#print Zeta2LegA.psiErrorBoundStatement
#print Chebyshev.psi
