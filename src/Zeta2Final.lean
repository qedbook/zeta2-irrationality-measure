/-
# The final assembly: the headline from `hψ`, every other input supplied

**What this file proves.**  The headline with two hypotheses,

```
Zeta2Final.zeta2_not_liouvilleWith_of_psi_of_poly :
    Zeta2LegA.psiErrorBoundStatement → Zeta2PtpPolar.PolyHalfOpen →
      ¬ LiouvilleWith 5.0495243 Zeta2Defs.zeta2
```

and then, at the foot of the file, with one: `Zeta2PtpMbigS2.polyHalfOpen` proves `PolyHalfOpen`,
so `zeta2_not_liouvilleWith_of_psi` takes only `hψ : Zeta2LegA.psiErrorBoundStatement`, the
error bound for Chebyshev's `ψ` that `Zeta2Hpsi.hψ` proves.  `Zeta2Unconditional` applies the
one to the other.

Beside them, `l1asm_binders_of_poly` exports five hypotheses of
`Zeta2L12.candidate_target_of_certified_constants`, `hrecq hrecp hΔne hQ hP`, together at the
chain's `Δ̃ = Zeta2PhiT.ΔT`, and `target_of_poly_and_rates` feeds them to that theorem, so the
composition is checked by Lean rather than asserted.  `hrecq` and `hrecp` say that `qₙ` and `pₙ`
satisfy the same four-term recurrence from `N₀` on; `hΔne`, `hQ` and `hP` say that `Δ̃ₙ ≠ 0` and
that `Δ̃ₙ·qₙ` and `Δ̃ₙ·pₙ` are integers.

**Where each binder comes from — a proved theorem, applied by name.**

| binder | supplied by |
|---|---|
| `hrecq` `hrecp` | `Zeta2L1Asm.hrecq` / `hrecp` at `αⱼ := Zeta2L1Asm.αR j`, `N₀ := Zeta2L1Asm.N0 = 4` |
| `hΔne` | `Zeta2PhiT.ΔT_ne_zero` |
| `hQ` | `Zeta2HatAssemble.hQ_at_ΔT`, at `Q := Zeta2HatAssemble.QT` |
| `hP` | `ptpOpen_of_poly` ← `Zeta2PtpAHalf.hP_at_ΔT_of_poly`, whose harmonic half `aHalfOpen` is proved |

`Zeta2TWire.PT_P_open` is, by its definition, exactly the `∃ P, ∀ n, ↑(P n) = ΔT n * ↑(pₙ)` that
`hP_at_ΔT_of_poly` concludes, so `ptpOpen_of_poly` is the identity up to `δ`-unfolding; it is a
theorem here so that the typechecker, not this comment, rules the two statements are one.

**Reading the receipts.**  The commands at the bottom print, for each theorem, the axioms it
depends on and its type.  The axioms are `[propext, Classical.choice, Quot.sound]` throughout,
for the conditional theorems too: `#print axioms` does not list hypotheses, so it is the printed
type that says which hypotheses a theorem takes.  `zeta2_not_liouvilleWith_of_psi_of_poly`
names `hψ` and `PolyHalfOpen`; `zeta2_not_liouvilleWith_of_psi` names `hψ` alone.

**What this file does not claim.**  None of its theorems is the unconditional statement; that is
`Zeta2Unconditional`'s.  It does not reach `5.04952429`: the proved bound is `5.0495243`, which
is `5.04952430`, the smallest number with eight decimal places above the certified exponent
`5.04952429053…` (`Zeta2TWire.certified_value_is_strictly_between_the_two_literals`).

**The falsifier run** (`out_final_falsify.txt`).  Seven planted defects each make Lean reject this
file, among them the bound at `5.04952429` and the harmonic half fed where `PolyHalfOpen` is
asked; an eighth, an extra hypothesis, is accepted with the same axiom list and is caught by the
printed type alone.


Toolchain `leanprover/lean4:v4.34.0-rc2`; Mathlib at commit `5aedf732`.
-/
import Zeta2Capstone
import Zeta2PtpAHalf
import Zeta2PtpMbigS2
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

namespace Zeta2Final

open Zeta2Defs

/-! ## 1. The p-half of the clearing, in the shape the capstone asks for -/

/-- **The p-half, conditional on the polynomial half alone.**  `Zeta2PtpAHalf.hP_at_ΔT_of_poly` is
`Zeta2TWire.PT_P_open`'s body verbatim; the harmonic half (`Zeta2PtpAHalf.aHalfOpen`) is already
discharged inside it. -/
theorem ptpOpen_of_poly (hpoly : Zeta2PtpPolar.PolyHalfOpen) : Zeta2TWire.PT_P_open :=
  Zeta2PtpAHalf.hP_at_ΔT_of_poly hpoly

/-! ## 2. The recurrence and clearing binders, exported together at `Δ̃` -/

/-- **The five arithmetic binders at the chain's `Δ̃`** — `hrecq hrecp hΔne hQ hP` of
`Zeta2L12.candidate_target_of_certified_constants`, in its EXACT binder types, at
`αⱼ := Zeta2L1Asm.αR j`, `N₀ := Zeta2L1Asm.N0`, `Q := Zeta2HatAssemble.QT`,
`Δ := Zeta2PhiT.ΔT`.  The `binders_of_pn_cleared` shape, moved from the stand-in `Δ 16 15`
to the object that carries the headline rate.  Conditional on `PolyHalfOpen` ONLY: the
recurrence half, `hΔne` and `hQ` carry no hypothesis. -/
theorem l1asm_binders_of_poly (hpoly : Zeta2PtpPolar.PolyHalfOpen) :
    ∃ P : ℕ → ℤ,
      (∀ n, Zeta2L1Asm.N0 ≤ n →
        Zeta2L1Asm.αR 0 n * ((candidateM.qn n : ℚ) : ℝ)
          + Zeta2L1Asm.αR 1 n * ((candidateM.qn (n + 1) : ℚ) : ℝ)
          + Zeta2L1Asm.αR 2 n * ((candidateM.qn (n + 2) : ℚ) : ℝ)
          + Zeta2L1Asm.αR 3 n * ((candidateM.qn (n + 3) : ℚ) : ℝ) = 0) ∧
      (∀ n, Zeta2L1Asm.N0 ≤ n →
        Zeta2L1Asm.αR 0 n * ((candidateM.pn n : ℚ) : ℝ)
          + Zeta2L1Asm.αR 1 n * ((candidateM.pn (n + 1) : ℚ) : ℝ)
          + Zeta2L1Asm.αR 2 n * ((candidateM.pn (n + 2) : ℚ) : ℝ)
          + Zeta2L1Asm.αR 3 n * ((candidateM.pn (n + 3) : ℚ) : ℝ) = 0) ∧
      (∀ n, Zeta2PhiT.ΔT n ≠ 0) ∧
      (∀ n, ((Zeta2HatAssemble.QT n : ℤ) : ℝ) = Zeta2PhiT.ΔT n * ((candidateM.qn n : ℚ) : ℝ)) ∧
      (∀ n, ((P n : ℤ) : ℝ) = Zeta2PhiT.ΔT n * ((candidateM.pn n : ℚ) : ℝ)) := by
  obtain ⟨P, hP⟩ := ptpOpen_of_poly hpoly
  exact ⟨P, Zeta2L1Asm.hrecq, Zeta2L1Asm.hrecp, Zeta2PhiT.ΔT_ne_zero,
    Zeta2HatAssemble.hQ_at_ΔT, hP⟩

/-- **The export CONSUMED, not just stated.**  `candidate_target_of_certified_constants` applied
with ALL FIVE of `l1asm_binders_of_poly`'s binders (not with `Zeta2L1Asm.hrecq` directly), the
guards from `Zeta2L4Br`, and the rate block left as hypotheses.  Not the headline (section 3), but
the check that the export's five types are the five the capstone asks for, at one shared `Δ`. -/
theorem target_of_poly_and_rates (hpoly : Zeta2PtpPolar.PolyHalfOpen)
    {Nr Nq : ℕ} {Cr Cq c0 c1 c2 δ : ℝ}
    (hc0 : (29.10787127 : ℝ) ≤ c0) (hc1 : c1 ≤ (42.03361581 : ℝ))
    (hc2 : c2 ≤ (15.01912095 : ℝ)) (hδ : δ ≤ 1 / 10 ^ 16)
    (hCr : 0 < Cr)
    (hdecay : ∀ n, Nr ≤ n →
      |Zeta2PhiT.ΔT n * candidateM.rn n| ≤ Cr * Real.exp (-(c0 - c2 - δ)) ^ n)
    (hCq : 0 < Cq)
    (hgrowth : ∀ n, Nq ≤ n →
      |((Zeta2HatAssemble.QT n : ℤ) : ℝ)| ≤ Cq * Real.exp (c1 + c2) ^ n) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 := by
  obtain ⟨P, hrecq, hrecp, hΔne, hQ, hP⟩ := l1asm_binders_of_poly hpoly
  exact Zeta2L12.candidate_target_of_certified_constants Zeta2HatAssemble.QT P Zeta2PhiT.ΔT
    (Zeta2L1Asm.αR 0) (Zeta2L1Asm.αR 1) (Zeta2L1Asm.αR 2) (Zeta2L1Asm.αR 3)
    hc0 hc1 hc2 hδ hrecq hrecp hΔne hQ hP
    Zeta2L4Br.hN₁ Zeta2L4Br.hM₀ Zeta2L4Br.hα₃ Zeta2L4Br.hα₀ Zeta2L4Br.hrow
    hCr hdecay hCq hgrowth

/-! ## 3. The headline, conditional on `hψ` and `PolyHalfOpen` -/

/-- **The headline from `hψ` and `PolyHalfOpen`.**  Executed through
`Zeta2Capstone.target_of_psi_and_ptp`, which supplies every other input of the chain; this
theorem supplies the p-half of the clearing from `PolyHalfOpen`.  Read the `#check @` at the
bottom: the type names `hψ` and `PolyHalfOpen` and nothing else. -/
theorem zeta2_not_liouvilleWith_of_psi_of_poly (hψ : Zeta2LegA.psiErrorBoundStatement)
    (hpoly : Zeta2PtpPolar.PolyHalfOpen) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2Capstone.target_of_psi_and_ptp hψ (ptpOpen_of_poly hpoly)

/-- The same as an irrationality-measure bound: every `p ≥ 5.0495243`, by `LiouvilleWith.mono`
inside `Zeta2Capstone.zeta2_irrationality_measure_le_of_psi_of_ptp`. -/
theorem zeta2_irrationality_measure_le_of_psi_of_poly
    (hψ : Zeta2LegA.psiErrorBoundStatement) (hpoly : Zeta2PtpPolar.PolyHalfOpen) :
    ∀ p : ℝ, (5.0495243 : ℝ) ≤ p → ¬ LiouvilleWith p zeta2 :=
  Zeta2Capstone.zeta2_irrationality_measure_le_of_psi_of_ptp hψ (ptpOpen_of_poly hpoly)

/-! ## 4. Checks that are not steps of the chain -/

/-- **THE HARMONIC HALF IS NOT THE POLYNOMIAL HALF.**  `aHalfOpen` is proved hypothesis-free, and
a composition that fed it where `PolyHalfOpen` is asked would discharge the wrong statement;
the falsifier run plants exactly that substitution, and Lean rejects it.  Stated here so
the two `Prop`s are visibly distinct constants in this environment. -/
theorem harmonic_half_is_proved : Zeta2PtpPolar.AHalfOpen := Zeta2PtpAHalf.aHalfOpen

/-- **THE `Δ` IS THE CHAIN'S.**  `Δ̃ₙ > 0` at every `n`, so `hQ`/`hP` above are statements about
nonzero multiples of `qₙ`/`pₙ`, not about the zero sequence. -/
theorem delta_is_nonzero : ∀ n, Zeta2PhiT.ΔT n ≠ 0 := Zeta2PhiT.ΔT_ne_zero

/-- **The proved constant is `5.0495243`, strictly above `5.04952429`.** -/
theorem the_literal_is_the_chains : (5.04952429 : ℝ) < 5.0495243 := by norm_num

end Zeta2Final

/-! ## Receipts: the axioms and the type of each theorem

The acceptance is that `Zeta2Final.zeta2_not_liouvilleWith_of_psi_of_poly` and
`Zeta2Final.zeta2_irrationality_measure_le_of_psi_of_poly` print
`[propext, Classical.choice, Quot.sound]` AND a type naming exactly
`Zeta2LegA.psiErrorBoundStatement` and `Zeta2PtpPolar.PolyHalfOpen` and no other hypothesis, and
that `Zeta2Final.l1asm_binders_of_poly` names `Zeta2PtpPolar.PolyHalfOpen` and nothing else. -/

#print axioms Zeta2Final.ptpOpen_of_poly
#check @Zeta2Final.ptpOpen_of_poly
#print axioms Zeta2Final.l1asm_binders_of_poly
#check @Zeta2Final.l1asm_binders_of_poly
#print axioms Zeta2Final.target_of_poly_and_rates
#check @Zeta2Final.target_of_poly_and_rates
#print axioms Zeta2Final.zeta2_not_liouvilleWith_of_psi_of_poly
#check @Zeta2Final.zeta2_not_liouvilleWith_of_psi_of_poly
#print axioms Zeta2Final.zeta2_irrationality_measure_le_of_psi_of_poly
#check @Zeta2Final.zeta2_irrationality_measure_le_of_psi_of_poly
#print axioms Zeta2Final.harmonic_half_is_proved
#check @Zeta2Final.harmonic_half_is_proved
#print axioms Zeta2Final.delta_is_nonzero
#check @Zeta2Final.delta_is_nonzero
#print axioms Zeta2Final.the_literal_is_the_chains
#check @Zeta2Final.the_literal_is_the_chains

/-! The polynomial half and the p-half of the clearing, printed as the `Prop`s they are. -/
#print Zeta2PtpPolar.PolyHalfOpen
#print Zeta2TWire.PT_P_open

/-! ## The closing step: the headline, conditional on `hψ` alone.

`Zeta2PtpMbigS2.polyHalfOpen : Zeta2PtpPolar.PolyHalfOpen` is proved with no hypothesis, so the
headline here takes one hypothesis, and its type names `Zeta2LegA.psiErrorBoundStatement` and
nothing else.  `Zeta2Unconditional` discharges that hypothesis with `Zeta2Hpsi.hψ`, and
`Zeta2Target` states the result.
-/

namespace Zeta2Final

theorem zeta2_not_liouvilleWith_of_psi (hψ : Zeta2LegA.psiErrorBoundStatement) :
    ¬ LiouvilleWith (5.0495243 : ℝ) Zeta2Defs.zeta2 :=
  Zeta2Final.zeta2_not_liouvilleWith_of_psi_of_poly hψ Zeta2PtpMbigS2.polyHalfOpen

theorem zeta2_irrationality_measure_le_of_psi (hψ : Zeta2LegA.psiErrorBoundStatement) :
    ∀ p : ℝ, (5.0495243 : ℝ) ≤ p → ¬ LiouvilleWith p Zeta2Defs.zeta2 :=
  Zeta2Final.zeta2_irrationality_measure_le_of_psi_of_poly hψ Zeta2PtpMbigS2.polyHalfOpen

theorem l1asm_binders : ∃ P : ℕ → ℤ,
      (∀ n, Zeta2L1Asm.N0 ≤ n →
        Zeta2L1Asm.αR 0 n * ((Zeta2Defs.candidateM.qn n : ℚ) : ℝ)
          + Zeta2L1Asm.αR 1 n * ((Zeta2Defs.candidateM.qn (n + 1) : ℚ) : ℝ)
          + Zeta2L1Asm.αR 2 n * ((Zeta2Defs.candidateM.qn (n + 2) : ℚ) : ℝ)
          + Zeta2L1Asm.αR 3 n * ((Zeta2Defs.candidateM.qn (n + 3) : ℚ) : ℝ) = 0) ∧
      (∀ n, Zeta2L1Asm.N0 ≤ n →
        Zeta2L1Asm.αR 0 n * ((Zeta2Defs.candidateM.pn n : ℚ) : ℝ)
          + Zeta2L1Asm.αR 1 n * ((Zeta2Defs.candidateM.pn (n + 1) : ℚ) : ℝ)
          + Zeta2L1Asm.αR 2 n * ((Zeta2Defs.candidateM.pn (n + 2) : ℚ) : ℝ)
          + Zeta2L1Asm.αR 3 n * ((Zeta2Defs.candidateM.pn (n + 3) : ℚ) : ℝ) = 0) ∧
      (∀ n, Zeta2PhiT.ΔT n ≠ 0) ∧
      (∀ n, ((Zeta2HatAssemble.QT n : ℤ) : ℝ) =
        Zeta2PhiT.ΔT n * ((Zeta2Defs.candidateM.qn n : ℚ) : ℝ)) ∧
      (∀ n, ((P n : ℤ) : ℝ) = Zeta2PhiT.ΔT n * ((Zeta2Defs.candidateM.pn n : ℚ) : ℝ)) :=
  Zeta2Final.l1asm_binders_of_poly Zeta2PtpMbigS2.polyHalfOpen

/-! ## WHAT THE HEADLINE'S WORDS MEAN — so a reader need not trust three names.

`Zeta2Defs.zeta2` is defined as `π²/6`; below it is proved equal to Mathlib's `riemannZeta 2` and
to the series `∑_{n ≥ 1} 1/n²`, with no `1/0` convention involved.  `LiouvilleWith` is Mathlib's
(`#print` below), and the headline is restated in its unfolded form. -/

/-- `ζ(2)` here equals Mathlib's Riemann zeta function at `2`. -/
theorem zeta2_eq_riemannZeta_two : ((Zeta2Defs.zeta2 : ℝ) : ℂ) = riemannZeta 2 := by
  rw [riemannZeta_two, Zeta2Defs.zeta2]
  push_cast
  ring

/-- `ζ(2)` here is the series from `1`, so the `1/0 = 0` convention plays no part. -/
theorem zeta2_eq_tsum_from_one :
    Zeta2Defs.zeta2 = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
  have h := (hasSum_nat_add_iff' 1).mpr Zeta2Defs.hasSum_zeta2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  norm_num at h
  simpa only [one_div] using h.tsum_eq.symm

/-- Mathlib's `LiouvilleWith`, unfolded: its negation says that for every constant `C`, all
large enough denominators `n` admit no `m / n ≠ x` closer to `x` than `C / n ^ p`. -/
theorem not_liouvilleWith_iff (p x : ℝ) :
    ¬ LiouvilleWith p x ↔
      ∀ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℤ, x ≠ m / n → C / (n : ℝ) ^ p ≤ |x - m / n| := by
  simp only [LiouvilleWith, not_exists, Filter.not_frequently, not_and, not_lt]

/-- **THE HEADLINE, UNFOLDED.**  Given `hψ`: for every constant `C`, every large enough
denominator `n`, and every integer `m` with `m / n ≠ ζ(2)`, `|ζ(2) − m/n| ≥ C / n ^ 5.0495243`. -/
theorem zeta2_rational_approximation_of_psi (hψ : Zeta2LegA.psiErrorBoundStatement) :
    ∀ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℤ,
      Zeta2Defs.zeta2 ≠ m / n → C / (n : ℝ) ^ (5.0495243 : ℝ) ≤ |Zeta2Defs.zeta2 - m / n| :=
  (not_liouvilleWith_iff _ _).mp (zeta2_not_liouvilleWith_of_psi hψ)

end Zeta2Final

/-- **The headline from `hψ`, in the `Zeta2Target` namespace**: the statement of
`Zeta2Target.zeta2_not_liouvilleWith` with `hψ` as its one hypothesis.  `Zeta2Unconditional`
discharges `hψ`. -/
theorem Zeta2Target.zeta2_not_liouvilleWith_of_psi (hψ : Zeta2LegA.psiErrorBoundStatement) :
    ¬ LiouvilleWith (5.0495243 : ℝ) Zeta2Defs.zeta2 :=
  Zeta2Final.zeta2_not_liouvilleWith_of_psi hψ

#print axioms Zeta2Final.zeta2_not_liouvilleWith_of_psi
#check @Zeta2Final.zeta2_not_liouvilleWith_of_psi
#print axioms Zeta2Final.zeta2_irrationality_measure_le_of_psi
#check @Zeta2Final.zeta2_irrationality_measure_le_of_psi
#print axioms Zeta2Final.l1asm_binders
#check @Zeta2Final.l1asm_binders
#print axioms Zeta2PtpMbigS2.polyHalfOpen
#check @Zeta2PtpMbigS2.polyHalfOpen
#print axioms Zeta2Final.zeta2_eq_riemannZeta_two
#check @Zeta2Final.zeta2_eq_riemannZeta_two
#print axioms Zeta2Final.zeta2_eq_tsum_from_one
#check @Zeta2Final.zeta2_eq_tsum_from_one
#print axioms Zeta2Final.not_liouvilleWith_iff
#check @Zeta2Final.not_liouvilleWith_iff
#print axioms Zeta2Final.zeta2_rational_approximation_of_psi
#check @Zeta2Final.zeta2_rational_approximation_of_psi
#print axioms Zeta2Target.zeta2_not_liouvilleWith_of_psi
#check @Zeta2Target.zeta2_not_liouvilleWith_of_psi
#print LiouvilleWith
#print Zeta2Defs.zeta2
