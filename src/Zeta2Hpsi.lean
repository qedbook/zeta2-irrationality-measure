/-
# Row hψ — `Zeta2LegA.psiErrorBoundStatement`, DISCHARGED in our kernel from `MediumPNT`

The ζ(2) chain carries one standing hypothesis, `hψ : Zeta2LegA.psiErrorBoundStatement`, which is
`MediumPNT`'s rate on Chebyshev's `ψ`. This file proves that very `Prop` (THE CHAIN'S DEFINITION,
imported from `Zeta2LegA`, not a local restatement of it) from
`PrimeNumberTheoremAnd.MediumPNT`, which is vendored with two one-line patches at
`external_tests/pnt_port/` (PNT+ `a5154676`, ported to our pin: see its PROVENANCE.md).

```
MediumPNT : ∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * exp (-c * (log x) ^ (1 / 10))
```

The proof is `PsiErrorBound.psi_error_bound`
(`external_tests/zeta2_binet_design/PsiErrorBound.lean`), which was attested on PNT+'s own toolchain.
Here the only change to that proof is the target: the `IsBigO` is unpacked into the pointwise-eventual form.

**What this file does NOT claim.** It does not reprove PNT+. `MediumPNT` is PNT+'s theorem, and
its `#print axioms` below is the attestation that the vendored cone proves it with no `sorryAx`
on our pin. Our part is the two patches, which are tactic-behaviour repairs, and this unpacking.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox, clean store.
Runner `clean_close/run_clean_final.sh Zeta2Hpsi.lean`; falsifier `falsify_unconditional.sh`.
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

/-! ## RECEIPTS — LEAN.md §1, both channels.

`sorryAx` in `MediumPNT`'s footprint would mean the vendored cone does not prove it on our pin.
Its absence covers all 23 vendored files transitively. `Zeta2Hpsi.hψ` must print the allowlist,
and `#check @` must print `Zeta2Hpsi.hψ : Zeta2LegA.psiErrorBoundStatement`, with no binder. The
`#print`s show the target `Prop` and the `ψ` it is about. `Chebyshev.psi` is Mathlib's, with no PNT+
definition shadowing it, and the census receipt of 2026-09-24 printed this same body. -/

#print axioms MediumPNT
#check @MediumPNT
#print axioms Zeta2Hpsi.hψ
#check @Zeta2Hpsi.hψ
#print Zeta2LegA.psiErrorBoundStatement
#print Chebyshev.psi
