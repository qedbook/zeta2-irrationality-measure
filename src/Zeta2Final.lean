/-
# THE FINAL ASSEMBLY — rows L1-ASM (arithmetic half) and T-WIRE, conditional on `PolyHalfOpen`

**What this file proves.**  The μ(ζ(2)) chain with row PT-P reduced to the ONE statement it still
owes, `Zeta2PtpPolar.PolyHalfOpen`:

```
Zeta2Final.zeta2_not_liouvilleWith_of_psi_of_poly :
    Zeta2LegA.psiErrorBoundStatement → Zeta2PtpPolar.PolyHalfOpen →
      ¬ LiouvilleWith 5.0495243 Zeta2Defs.zeta2
```

and, beside it, row L1-ASM's five binders of `Zeta2L12.candidate_target_of_certified_constants`
— `hrecq hrecp hΔne hQ hP` — exported TOGETHER at the chain's `Δ̃ = Zeta2PhiT.ΔT`, conditional on
`PolyHalfOpen` alone (`l1asm_binders_of_poly`), and consumed by that capstone in
`target_of_poly_and_rates` so the export is an executed interface, not a claimed one.

**Where each piece comes from — every one a landed theorem, applied by name (LEAN.md §3).**

| binder | supplied by | row |
|---|---|---|
| `hrecq` `hrecp` | `Zeta2L1Asm.hrecq` / `hrecp` at `αⱼ := Zeta2L1Asm.αR j`, `N₀ := Zeta2L1Asm.N0 = 4` | L1-ASM, recurrence half |
| `hΔne` | `Zeta2PhiT.ΔT_ne_zero` | PT-DEF |
| `hQ` | `Zeta2HatAssemble.hQ_at_ΔT`, at `Q := Zeta2HatAssemble.QT` | PT-QB |
| `hP` | `ptpOpen_of_poly` ← `Zeta2PtpAHalf.hP_at_ΔT_of_poly` (harmonic half `aHalfOpen` proved) | PT-P |

`Zeta2TWire.PT_P_open` is, by its definition, exactly the `∃ P, ∀ n, ↑(P n) = ΔT n * ↑(pₙ)` that
`hP_at_ΔT_of_poly` concludes, so `ptpOpen_of_poly` is the identity up to `δ`-unfolding; it is a
theorem here so that the typechecker, not this comment, rules the two statements are one.

**WHAT THIS FILE DOES NOT CLAIM.**

* It does **not** prove `μ(ζ(2)) ≤ 5.0495243` unconditionally.  ONE hypothesis remains and it is
  not an axiom, so `#print axioms` below reads `[propext, Classical.choice, Quot.sound]` —
  byte-identical to what an unconditional proof would print (LEAN.md §1: a binder is not an
  axiom).  **The receipt is HALF the acceptance; the `#check @` type printed beside it is the
  other half.**
  - `hψ : Zeta2LegA.psiErrorBoundStatement` — MediumPNT's rate on Chebyshev's `ψ`; the ACCEPTED
    standing binder (owner fork answered A, 2026-09-20).  It stays in the headline.
  - `hpoly : Zeta2PtpPolar.PolyHalfOpen` — the POLYNOMIAL half of row PT-P — is DISCHARGED by
    `Zeta2PtpMbigS2.polyHalfOpen` in the closing step at the foot of this file.  The
    `_of_poly` theorems keep it as a binder so the two halves stay separately inspectable.
* It does **not** reach `5.04952429`.  That numeral is the sweep's `μ̃` SCORE, strictly stronger
  than the certified `V = 5.04952429053…` (`Zeta2TWire.certified_value_is_strictly_between_the_two_literals`);
  the bound this chain proves is `5.0495243`.
* It does **not** touch `Zeta2Target.zeta2_not_liouvilleWith`, whose `sorry` is deliberate and
  stays confined to `Zeta2Target.lean`; no theorem is added to that file.

**THE CLOSING STEP** is at the foot of this file: `zeta2_not_liouvilleWith_of_psi`, the headline
conditional on `hψ` ALONE, is one application of `Zeta2PtpMbigS2.polyHalfOpen`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
Runner `run_probe.sh Zeta2Final.lean` (olean store `probes/final`), falsifier `falsify_final.sh`,
receipts `out_axioms_final.txt` and `out_final_falsify.txt`.
-/
import Zeta2Capstone
import Zeta2PtpAHalf
import Zeta2PtpMbigS2
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

namespace Zeta2Final

open Zeta2Defs

/-! ## §1. Row PT-P's output, in the shape the capstone asks for -/

/-- **PT-P, conditional on the polynomial half alone.**  `Zeta2PtpAHalf.hP_at_ΔT_of_poly` is
`Zeta2TWire.PT_P_open`'s body verbatim; the harmonic half (`Zeta2PtpAHalf.aHalfOpen`) is already
discharged inside it. -/
theorem ptpOpen_of_poly (hpoly : Zeta2PtpPolar.PolyHalfOpen) : Zeta2TWire.PT_P_open :=
  Zeta2PtpAHalf.hP_at_ΔT_of_poly hpoly

/-! ## §2. Row L1-ASM's binders, exported together at `Δ̃` -/

/-- **L1-ASM, both halves, at the chain's `Δ̃`** — the five binders `hrecq hrecp hΔne hQ hP` of
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
guards from `Zeta2L4Br`, and the rate block left as hypotheses.  Not the headline — §3 is — but
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

/-! ## §3. T-WIRE — THE HEADLINE, CONDITIONAL ON `hψ` AND `PolyHalfOpen` -/

/-- **T-WIRE.**  Executed through `Zeta2Capstone.target_of_psi_and_ptp`, which already carries
every closed row (L1's recurrence, L4-BR's guards, HC1, HC2, RDECAY, QGROW, L7ID, PT-DEF, PT-QB);
this theorem supplies PT-P from `PolyHalfOpen`.  Read the `#check @` at the bottom: the type names
`hψ` and `PolyHalfOpen` and nothing else. -/
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

/-! ## §4. Rung 0 (LEAN.md §5) — none of these is a step of the chain -/

/-- **THE HARMONIC HALF IS NOT THE POLYNOMIAL HALF.**  `aHalfOpen` is proved hypothesis-free, and
a composition that had fed it where `PolyHalfOpen` is asked would be a silent discharge of the
open row; `falsify_final.sh` arm F1 makes exactly that substitution and must red.  Stated here so
the two `Prop`s are visibly distinct constants in this environment. -/
theorem harmonic_half_is_proved : Zeta2PtpPolar.AHalfOpen := Zeta2PtpAHalf.aHalfOpen

/-- **THE `Δ` IS THE CHAIN'S.**  `Δ̃ₙ > 0` at every `n`, so `hQ`/`hP` above are statements about
nonzero multiples of `qₙ`/`pₙ`, not about the zero sequence. -/
theorem delta_is_nonzero : ∀ n, Zeta2PhiT.ΔT n ≠ 0 := Zeta2PhiT.ΔT_ne_zero

/-- **THE CONSTANT IS THE CHAIN'S, NOT THE SWEEP SCORE.** -/
theorem the_literal_is_the_chains : (5.04952429 : ℝ) < 5.0495243 := by norm_num

end Zeta2Final

/-! ## RECEIPTS — LEAN.md §1, BOTH channels, the type beside every receipt.

The acceptance for this landing is that `Zeta2Final.zeta2_not_liouvilleWith_of_psi_of_poly` and
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

/-! The one open statement, printed as the `Prop` it is. -/
#print Zeta2PtpPolar.PolyHalfOpen
#print Zeta2TWire.PT_P_open

/-! ## THE CLOSING STEP — the headline, conditional on `hψ` ALONE.

`Zeta2PtpMbigS2.polyHalfOpen : Zeta2PtpPolar.PolyHalfOpen` is proved with no binder, so the
T-WIRE headline takes one hypothesis.  The acceptance is a type naming
`Zeta2LegA.psiErrorBoundStatement` and NOTHING else, the owner-accepted conditional headline
(decision A, 2026-09-20).  It lives HERE, never in `Zeta2Target.lean`, whose `sorry` block stays
as it is. -/

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

`Zeta2Defs.zeta2` is Mathlib's `riemannZeta 2`, and the series `∑_{n ≥ 1} 1/n²` with no `1/0`
convention involved; `LiouvilleWith` is Mathlib's (`#print` below), and the headline is restated
in its unfolded form. -/

/-- `ζ(2)` here is Mathlib's Riemann zeta function at `2`. -/
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

/-- **THE DELIVERABLE, UNDER THE NAME THE OWNER RULING GIVES IT** (owner-rulings.md, 2026-09-20,
clause 2): `Zeta2Target.zeta2_not_liouvilleWith_of_psi`.  Declared HERE, in the `Zeta2Target`
namespace, so `Zeta2Target.lean` itself — and its deliberate `sorry` — is not touched. -/
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
