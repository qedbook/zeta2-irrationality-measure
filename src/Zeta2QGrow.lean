/-
# ROW QGROW — `hCq` and `hgrowth` at the real `Q`, **CONDITIONAL on `hψ`**

**HEADLINE: `Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.**  Nothing here
discharges it.  What this file closes is ONE of the chain's three remaining open rows, and it
closes it in the shape the chain can actually deliver:

```
Zeta2QGrow.qgrow_of_psi
    (hψ : Zeta2LegA.psiErrorBoundStatement) {ε' : ℝ} (hε' : 0 < ε') : Zeta2TWire.QGROW_open ε'
```

**THE SHAPE CORRECTION, AND IT IS THE ROW'S MAIN FINDING.**  `Zeta2TWire.QGROW_open` is stated
hypothesis-free, and the scaffold's `QGROW_sorried : QGROW_open ε'` (removed 2026-09-24) read as a
promise that some file would discharge it outright; none then could.  `QT n` is `Δ̃ₙ · qₙ`
(`Zeta2HatAssemble.hQ_at_ΔT`), so a bound on `|QT n|` needs a bound on `Δ̃ₙ`, and EVERY landed
theorem that rates `Δ̃` takes `hψ` as its first explicit argument — `Zeta2DRate.tendsto_log_ΔT_div`,
`ΔT_growth`, `ΔT_growth_hc2`, `ΔT_clearing_rate`, `ΔT_clearing_rate_hc2`, `ΔT_rate_ne_31`, all six.
`hψ` is `Zeta2LegA.psiErrorBoundStatement`, MediumPNT's error rate on Chebyshev's ψ, proved
sorry-free in `PrimeNumberTheoremAnd` at ITS toolchain and undischarged at this pin; the owner's
2026-09-20 ruling (fork answered **A**) makes it an accepted STANDING BINDER of the headline.  So
the row's deliverable is `hψ → QGROW_open ε'` and the chain doc's QGROW cell already says so
("SO THIS ROW DELIVERS `hψ → hgrowth`, NOT `hgrowth`, corrected 2026-09-20"); this file is the
first place the correction is carried into Lean rather than into prose.  `RDECAY_open` has the
identical shape and the identical reason — it routes through `ΔT_clearing_rate_hc2` too — and its
own blocker (L7ID's `candidateM.rn` identification) is unchanged by anything here.

**AND `#print axioms` CANNOT SEE ANY OF THIS** (LEAN.md §1, the trap added 2026-09-20): a binder is
not an axiom, so `qgrow_of_psi` prints a footprint byte-identical to an unconditional theorem's.
The receipts at the bottom of this file are therefore emitted WITH `#check @` on every theorem
claimed, and the acceptance test for this row is both channels, never the receipt alone.

## The route, in three legs, each at the constant its certifying row PINS

1. **L5/Poincaré at `qₙ`** — `Zeta2StarB1.star_growth_bound_eventual` with `y := qₙ` and
   `hL := Zeta2L1Asm.hrecq` (the SAME binder L1-ASM exports; no restatement), giving
   `∃ C N, ∀ n ≥ N, |qₙ| ≤ C · rhoChar ^ n`.  The cell predicted the `B := P₃` trick here; the
   file uses `B := 1` instead, which is simpler and costs nothing — see §3.
2. **The clearing** — `Zeta2DRate.ΔT_clearing_rate hψ hε' hy` at `y := qₙ`, giving
   `|Δ̃ₙ · qₙ| ≤ C · 1 · (rhoChar · exp c2) ^ n` with `c2 = 31 − d_φ̃ + ε'` (HC2's own constant).
3. **HC1** — `exp (log rhoChar + c2) = rhoChar · exp c2` by `Real.exp_add` and
   `Real.exp_log Zeta2XL1.rho_pos`.  At `c1 := Real.log rhoChar` this is an EQUALITY, which is the
   point: the loss lives entirely in `Zeta2Hc1.hc1`, and the row never constructs a re-derived
   literal.  Writing the rate at a literal instead would need a bridge nobody has built.

`Zeta2L12.growth_relax` is NOT used: leg 3 is an equality, so there is no exponent to relax.  The
only slack introduced anywhere is `Cq := C + 1`, because `star_growth_bound_eventual` returns
`0 ≤ C` and the capstone's `hCq` wants `0 < Cq`.

## §2's census, measured on the committed sources before a line of Lean was written

`qgrow_lead_census.py` (this directory, output `qgrow_lead_census.out`): all four cleared
coefficient lists have **511 entries** and
their leading entries are **exactly** `Zeta2XL1Data.lead0 … lead3` — `c0lead = lead0`,
`Zeta2StarIdIIJ1.c1.getLast = lead1`, `Zeta2StarIdIIJ2.c2.getLast = lead2`, `c3lead = lead3`, all
four ratios `= 1`.  That is what makes §4 a kernel check rather than a re-derivation.

**THE SIGN, and it is where an `hk : Pⱼ.coeff 510 = leadⱼ` hypothesis would have been FALSE.**
L1-ASM's `hrecq` is at the `'alt'` convention `αⱼ = (−1)^j cⱼ`, so the polynomial realising `α₁`
and `α₃` is `−ofList cⱼ`, whose coefficient at 510 is `−leadⱼ`.  `Zeta2XL1`'s own composed
theorem `candidate_rn_growth_of_recurrence` asks for the UNSIGNED shape and cannot be used here;
this file goes one level lower, to `Zeta2XL1.degree_lead_of_coeff` and `Zeta2StarB1`'s capstone,
and carries the sign explicitly.  The `A`-constants are unaffected — `|a / −b| = |a / b|` — which
is measured by the theorems of §5 and not assumed.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2TWire

-- FILE-LEVEL on purpose, and copied from `Zeta2L4Br` for the same measured reason: placed
-- between a docstring and its theorem a `set_option` is a parse error Lean silently RECOVERS
-- from (LEAN.md §1, the `ParseRecovery` case — receipts print anyway and only `rc` dissents).
-- It is load-bearing here: the four cleared coefficient lists are 511 entries long, so every
-- `rfl`/`rw` that has to unfold one of them overruns the default `maxRecDepth` of 512.  Measured
-- 2026-09-20: without these two lines this file reports eight `maximum recursion depth` errors,
-- EIGHTEEN of its thirty-three receipts silently carry `sorryAx`, and the other fifteen print
-- clean — the exact shape LEAN.md §1 warns about, and the reason `rc` is read in its own
-- channel.  Falsifier arm A9 (`falsify_qgrow.sh`) removes the line and requires that red.
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Zeta2QGrow

open Zeta2Defs Polynomial

/-! ## §1. The two `hornerZ` ties this file needs

`Zeta2StarIdIIJ1` and `Zeta2StarIdIIJ2` each restate `hornerZ`; `Zeta2L4Br` already tied `J0`
and `J3` (`hornerZ_j0`, `hornerZ_j3`) because those are the guard sides.  `j = 1, 2` were never
needed before, and they are needed here because this row is the first consumer of ALL FOUR
cleared polynomials at once.  Same structural induction, no new content. -/

theorem hornerZ_j1 : ∀ (L : List ℤ) (x : ℤ), Zeta2StarIdIIJ1.hornerZ L x = Zeta2L4.hornerZ L x
  | [], _ => rfl
  | c :: cs, x => by rw [Zeta2StarIdIIJ1.hornerZ, Zeta2L4.hornerZ, hornerZ_j1 cs x]

theorem hornerZ_j2 : ∀ (L : List ℤ) (x : ℤ), Zeta2StarIdIIJ2.hornerZ L x = Zeta2L4.hornerZ L x
  | [], _ => rfl
  | c :: cs, x => by rw [Zeta2StarIdIIJ2.hornerZ, Zeta2L4.hornerZ, hornerZ_j2 cs x]

/-! ## §2. The four polynomials that realise L1-ASM's `αⱼ`, SIGNED

`Zeta2L4Br.P0`/`P3` are the unsigned `ofList Zeta2L4.c0`/`c3`; the `'alt'` convention puts a minus
on the odd `j`. -/

/-- `α₀`'s polynomial: `(−1)⁰ = 1`, so this is `Zeta2L4Br.P0` unchanged. -/
noncomputable def Q0 : ℝ[X] := Zeta2L4Br.P0

/-- `α₁`'s polynomial: `(−1)¹ = −1`. -/
noncomputable def Q1 : ℝ[X] := -(Zeta2L4Br.ofList Zeta2StarIdIIJ1.c1)

/-- `α₂`'s polynomial: `(−1)² = 1`. -/
noncomputable def Q2 : ℝ[X] := Zeta2L4Br.ofList Zeta2StarIdIIJ2.c2

/-- `α₃`'s polynomial: `(−1)³ = −1`, so this is `−Zeta2L4Br.P3`. -/
noncomputable def Q3 : ℝ[X] := -Zeta2L4Br.P3

/-! ## §3. `Qⱼ(n) = αⱼ(n)` — the clearing identity at `B := 1`

`star_growth_bound_eventual`'s `hⱼ : Pⱼ.eval n = B.eval n * αⱼ n` exists so that a caller whose
`αⱼ` are RATIONAL functions can clear them by one common `B`.  L1-ASM's `'alt'` `αⱼ` are already
polynomial in `n` (the `'alt'` route performs no division at all — that is what the 2026-09-18
landing bought), so the clearing polynomial is `1` and `hⱼ` collapses to an identification.

`Zeta2L4Br.αR0_eq`/`αR3_eq` are the `j = 0, 3` halves, landed.  `j = 1, 2` are proved here by the
same three-line script. -/

theorem αR1_eq (n : ℕ) :
    Zeta2L1Asm.αR 1 n = -((Zeta2L4Br.ofList Zeta2StarIdIIJ1.c1).eval (n : ℝ)) := by
  show ((((-1 : ℚ) ^ 1
      * ((Zeta2StarIdIIJ1.hornerZ Zeta2StarIdIIJ1.c1 (n : ℤ) : ℤ) : ℚ)) : ℚ) : ℝ)
    = -((Zeta2L4Br.ofList Zeta2StarIdIIJ1.c1).eval (n : ℝ))
  rw [Zeta2L4Br.eval_ofList, hornerZ_j1]
  push_cast
  ring

theorem αR2_eq (n : ℕ) :
    Zeta2L1Asm.αR 2 n = (Zeta2L4Br.ofList Zeta2StarIdIIJ2.c2).eval (n : ℝ) := by
  show ((((-1 : ℚ) ^ 2
      * ((Zeta2StarIdIIJ2.hornerZ Zeta2StarIdIIJ2.c2 (n : ℤ) : ℤ) : ℚ)) : ℚ) : ℝ)
    = (Zeta2L4Br.ofList Zeta2StarIdIIJ2.c2).eval (n : ℝ)
  rw [Zeta2L4Br.eval_ofList, hornerZ_j2]
  push_cast
  ring

theorem h0 : ∀ n : ℕ, Zeta2L1Asm.N0 ≤ n →
    Q0.eval (n : ℝ) = (1 : ℝ[X]).eval (n : ℝ) * Zeta2L1Asm.αR 0 n := by
  intro n _
  rw [eval_one, one_mul, Q0, Zeta2L4Br.αR0_eq]

theorem h1 : ∀ n : ℕ, Zeta2L1Asm.N0 ≤ n →
    Q1.eval (n : ℝ) = (1 : ℝ[X]).eval (n : ℝ) * Zeta2L1Asm.αR 1 n := by
  intro n _
  rw [eval_one, one_mul, Q1, eval_neg, αR1_eq]

theorem h2 : ∀ n : ℕ, Zeta2L1Asm.N0 ≤ n →
    Q2.eval (n : ℝ) = (1 : ℝ[X]).eval (n : ℝ) * Zeta2L1Asm.αR 2 n := by
  intro n _
  rw [eval_one, one_mul, Q2, αR2_eq]

theorem h3 : ∀ n : ℕ, Zeta2L1Asm.N0 ≤ n →
    Q3.eval (n : ℝ) = (1 : ℝ[X]).eval (n : ℝ) * Zeta2L1Asm.αR 3 n := by
  intro n _
  rw [eval_one, one_mul, Q3, eval_neg, Zeta2L4Br.αR3_eq]

/-! ## §4. The shape facts — `natDegree ≤ 510` and `coeff 510 = ±leadⱼ`

The two ties `c0lead = lead0` / `c3lead = lead3` are the "twin literals" `Zeta2L4Br`'s docstring
names; they had never been checked.  `j = 1, 2` read their leading entry straight off the list. -/

theorem c0lead_tie : Zeta2L4.c0lead = Zeta2XL1Data.lead0 := by decide +kernel

theorem c3lead_tie : Zeta2L4.c3lead = Zeta2XL1Data.lead3 := by decide +kernel

theorem c1_length : Zeta2StarIdIIJ1.c1.length = 511 := by rfl

theorem c2_length : Zeta2StarIdIIJ2.c2.length = 511 := by rfl

theorem c1_lead : Zeta2StarIdIIJ1.c1.getD 510 0 = Zeta2XL1Data.lead1 := by decide +kernel

theorem c2_lead : Zeta2StarIdIIJ2.c2.getD 510 0 = Zeta2XL1Data.lead2 := by decide +kernel

theorem Q0_natDegree_le : Q0.natDegree ≤ 510 := Zeta2L4Br.P0_natDegree_le

theorem Q0_coeff : Q0.coeff 510 = ((Zeta2XL1Data.lead0 : ℤ) : ℝ) := by
  rw [Q0, Zeta2L4Br.P0_coeff_510, c0lead_tie]

theorem Q1_natDegree_le : Q1.natDegree ≤ 510 := by
  rw [Q1, natDegree_neg]
  have h := Zeta2L4Br.natDegree_ofList_le Zeta2StarIdIIJ1.c1
  rwa [c1_length] at h

theorem Q1_coeff : Q1.coeff 510 = -((Zeta2XL1Data.lead1 : ℤ) : ℝ) := by
  rw [Q1, coeff_neg, Zeta2L4Br.coeff_ofList, c1_lead]

theorem Q2_natDegree_le : Q2.natDegree ≤ 510 := by
  rw [Q2]
  have h := Zeta2L4Br.natDegree_ofList_le Zeta2StarIdIIJ2.c2
  rwa [c2_length] at h

theorem Q2_coeff : Q2.coeff 510 = ((Zeta2XL1Data.lead2 : ℤ) : ℝ) := by
  rw [Q2, Zeta2L4Br.coeff_ofList, c2_lead]

theorem Q3_natDegree_le : Q3.natDegree ≤ 510 := by
  rw [Q3, natDegree_neg]
  exact Zeta2L4Br.P3_natDegree_le

theorem Q3_coeff : Q3.coeff 510 = -((Zeta2XL1Data.lead3 : ℤ) : ℝ) := by
  rw [Q3, coeff_neg, Zeta2L4Br.P3_coeff_510, c3lead_tie]

/-! ## §5. Degrees and the majorant constants, WITH the sign carried

`Zeta2XL1.degree_lead_of_coeff` turns `natDegree ≤ d` + a nonzero `coeff d` into
`P ≠ 0 ∧ P.degree = d ∧ P.leadingCoeff = that coefficient`.  The `A`-constants then come from
`Zeta2XL1.hA0`–`hA2` after `|a / −b| = |a / b|`, which is the theorem rather than the remark. -/

theorem Q0_shape : Q0 ≠ 0 ∧ Q0.degree = ((510 : ℕ) : WithBot ℕ)
    ∧ Q0.leadingCoeff = ((Zeta2XL1Data.lead0 : ℤ) : ℝ) :=
  Zeta2XL1.degree_lead_of_coeff Q0_natDegree_le Q0_coeff Zeta2XL1.lead0_neR

theorem Q1_shape : Q1 ≠ 0 ∧ Q1.degree = ((510 : ℕ) : WithBot ℕ)
    ∧ Q1.leadingCoeff = -((Zeta2XL1Data.lead1 : ℤ) : ℝ) :=
  Zeta2XL1.degree_lead_of_coeff Q1_natDegree_le Q1_coeff (neg_ne_zero.mpr Zeta2XL1.lead1_neR)

theorem Q2_shape : Q2 ≠ 0 ∧ Q2.degree = ((510 : ℕ) : WithBot ℕ)
    ∧ Q2.leadingCoeff = ((Zeta2XL1Data.lead2 : ℤ) : ℝ) :=
  Zeta2XL1.degree_lead_of_coeff Q2_natDegree_le Q2_coeff Zeta2XL1.lead2_neR

theorem Q3_shape : Q3 ≠ 0 ∧ Q3.degree = ((510 : ℕ) : WithBot ℕ)
    ∧ Q3.leadingCoeff = -((Zeta2XL1Data.lead3 : ℤ) : ℝ) :=
  Zeta2XL1.degree_lead_of_coeff Q3_natDegree_le Q3_coeff (neg_ne_zero.mpr Zeta2XL1.lead3_neR)

/-- `|a / −b| = |a / b|` and `|−a / −b| = |a / b|`, from core lemmas only (LEAN.md §8: a
remembered composite name is a guess; these three are not). -/
theorem abs_div_neg (a b : ℝ) : |a / -b| = |a / b| := by rw [div_neg, abs_neg]

theorem abs_neg_div_neg (a b : ℝ) : |(-a) / -b| = |a / b| := by
  rw [div_neg, neg_div, neg_neg]

/-- **The sign is invisible to the majorant** — `|ℓ₀ / −ℓ₃| = |ℓ₀ / ℓ₃|`, so `Zeta2XL1.hA0`
transfers with no new arithmetic. -/
theorem hA0' : |Q0.leadingCoeff / Q3.leadingCoeff| < Zeta2XL1.Aco0 := by
  rw [Q0_shape.2.2, Q3_shape.2.2, abs_div_neg]
  exact Zeta2XL1.hA0

/-- At `j = 1` BOTH signs are negative and cancel outright. -/
theorem hA1' : |Q1.leadingCoeff / Q3.leadingCoeff| < Zeta2XL1.Aco1 := by
  rw [Q1_shape.2.2, Q3_shape.2.2, abs_neg_div_neg]
  exact Zeta2XL1.hA1

theorem hA2' : |Q2.leadingCoeff / Q3.leadingCoeff| < Zeta2XL1.Aco2 := by
  rw [Q2_shape.2.2, Q3_shape.2.2, abs_div_neg]
  exact Zeta2XL1.hA2

/-! ## §6. LEG (i) — L5/Poincaré at `qₙ`, EXECUTED

`hL` is `Zeta2L1Asm.hrecq` itself, at `y := fun n => ((candidateM.qn n : ℚ) : ℝ)`.  Nothing is
restated: if L1-ASM's binder had the wrong `N₀`, the wrong index or the wrong cast, this
application is where it would be a type error. -/

theorem qn_growth : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ n, N ≤ n → |((candidateM.qn n : ℚ) : ℝ)| ≤ C * Zeta2XL1.rhoChar ^ n :=
  Zeta2StarB1.star_growth_bound_eventual
    (fun n => ((candidateM.qn n : ℚ) : ℝ))
    (Zeta2L1Asm.αR 0) (Zeta2L1Asm.αR 1) (Zeta2L1Asm.αR 2) (Zeta2L1Asm.αR 3)
    Q0 Q1 Q2 Q3 1 Zeta2L1Asm.N0
    Zeta2L1Asm.hrecq h0 h1 h2 h3
    Q3_shape.1
    (Q0_shape.2.1.trans Q3_shape.2.1.symm)
    (Q1_shape.2.1.trans Q3_shape.2.1.symm)
    (Q2_shape.2.1.trans Q3_shape.2.1.symm)
    hA0' hA1' hA2' Zeta2XL1.rho_pos Zeta2XL1.char_real

/-! ## §7. THE ROW — legs (ii) and (iii), and the conditional shape

The conclusion is `Zeta2TWire.QGROW_open ε'` **verbatim**, not a twin: the scaffold's `Prop` is
what the capstone consumes, so a consumer built to a guessed shape is impossible here. -/

/--
**QGROW, CLOSED CONDITIONALLY ON `hψ`.**

`hψ : Zeta2LegA.psiErrorBoundStatement` is INHERITED, NOT DISCHARGED — it enters through
`Zeta2DRate.ΔT_clearing_rate`, whose first explicit argument it is, and it is the standing binder
the owner's 2026-09-20 ruling accepts.  `#print axioms` on this theorem reads
`[propext, Classical.choice, Quot.sound]` and says NOTHING about that; read `#check @qgrow_of_psi`
beside it.

`0 < ε'` is load-bearing exactly where DRATE's is: the `Tendsto → ∀ n ≥ N` conversion needs the
limit strictly below the rate.
-/
theorem qgrow_of_psi (hψ : Zeta2LegA.psiErrorBoundStatement) {ε' : ℝ} (hε' : 0 < ε') :
    Zeta2TWire.QGROW_open ε' := by
  obtain ⟨C, N, hC, hy⟩ := qn_growth
  obtain ⟨M, hM⟩ :=
    Zeta2DRate.ΔT_clearing_rate hψ hε' (y := fun n => ((candidateM.qn n : ℚ) : ℝ))
      (Cy := C) (ρy := Zeta2XL1.rhoChar) (Ny := N) hy
  refine ⟨C + 1, M, by linarith, fun n hn => ?_⟩
  have hbase : (0 : ℝ) ≤ (Zeta2XL1.rhoChar * Real.exp (31 - Zeta2DPhi.dPhi + ε')) ^ n :=
    pow_nonneg (mul_nonneg Zeta2XL1.rho_pos.le (Real.exp_nonneg _)) n
  rw [Zeta2HatAssemble.hQ_at_ΔT n, Real.exp_add, Real.exp_log Zeta2XL1.rho_pos]
  refine (hM n hn).trans ?_
  rw [mul_one]
  exact mul_le_mul_of_nonneg_right (by linarith) hbase

/-- **The row against the scaffold's own corrected interface.**  `Zeta2TWire.QGROW_deliverable`
is `hψ → QGROW_open ε'`, added by this row's landing; inhabiting it is what makes "QGROW is
closed" a statement the typechecker can check rather than one the doc asserts. -/
theorem qgrow {ε' : ℝ} (hε' : 0 < ε') : Zeta2TWire.QGROW_deliverable ε' :=
  fun hψ => qgrow_of_psi hψ hε'

/-- **`hCq` and `hgrowth` unpacked**, for a reader who wants the binder types rather than the
packed `∃`.  Same content, same `hψ`. -/
theorem hgrowth_of_psi (hψ : Zeta2LegA.psiErrorBoundStatement) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ (Cq : ℝ) (Nq : ℕ), 0 < Cq ∧
      ∀ n, Nq ≤ n → |((Zeta2HatAssemble.QT n : ℤ) : ℝ)|
        ≤ Cq * Real.exp (Real.log Zeta2XL1.rhoChar + (31 - Zeta2DPhi.dPhi + ε')) ^ n :=
  qgrow_of_psi hψ hε'

/-! ## §8. THE COMPOSITION, EXECUTED — T-WIRE with QGROW no longer a hypothesis

`Zeta2TWire.target_of_open_rows` binds the three open rows.  This is the same application with
QGROW supplied from §7, so the chain's remaining obligations are exactly PT-P, RDECAY and `hψ`.
It is the LEAN.md §3 acceptance for this row: the theorem produced is the theorem consumed. -/

theorem target_of_two_open_rows (hψ : Zeta2LegA.psiErrorBoundStatement)
    {ε' : ℝ} (hε'0 : 0 < ε') (hε' : ε' ≤ 1 / 10 ^ 8)
    (hPT_P : Zeta2TWire.PT_P_open) (hRDECAY : Zeta2TWire.RDECAY_deliverable ε') :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2TWire.target_of_deliverable_rows hψ hε' hPT_P hRDECAY (qgrow hε'0)

/-! ## §9. Rung 0 — the checks that stop a green meaning nothing (LEAN.md §5)

None of these is a step of the chain. -/

/-- **THE HC1 LEG IS NOT SILENTLY ZERO.**  `c1 = Real.log rhoChar > 0` (because `1 < rhoChar`,
`Zeta2XL1.one_lt_rhoChar`), so the row's exponent `c1 + c2` is STRICTLY above DRATE's `c2`.  A
`c1` that had come out `≤ 0` would mean the `qₙ` leg contributed nothing and the bound was
DRATE's alone wearing HC1's name — the cheapest way this row could be green and vacuous. -/
theorem c1_is_positive : 0 < Real.log Zeta2XL1.rhoChar :=
  Real.log_pos Zeta2XL1.one_lt_rhoChar

theorem growth_base_above_drate {ε' : ℝ} :
    Real.exp (31 - Zeta2DPhi.dPhi + ε')
      < Real.exp (Real.log Zeta2XL1.rhoChar + (31 - Zeta2DPhi.dPhi + ε')) :=
  Real.exp_lt_exp.mpr (by linarith [c1_is_positive])

/-- **THE `B := 1` CLEARING IS NOT VACUOUS.**  `star_growth_bound_eventual` would accept `B := 0`
with `Pⱼ := 0` and prove nothing about `qₙ` at all — the `hⱼ` would hold and `hP₃ : P₃ ≠ 0` would
fail, which is the hypothesis that stops it.  Recorded as a theorem because the `B` this file
picks is the degenerate-looking one. -/
theorem clearing_B_is_a_unit : (1 : ℝ[X]).eval (0 : ℝ) = 1 := by simp

/-- **The four `Qⱼ` are pairwise the SAME degree and none is zero** — the hypothesis bundle
`star_growth_bound_eventual` uses to read a characteristic root off the leading coefficients.
A `Qⱼ` of lower degree would make `hdⱼ` false, not merely weak. -/
theorem all_four_are_degree_510 :
    Q0.degree = ((510 : ℕ) : WithBot ℕ) ∧ Q1.degree = ((510 : ℕ) : WithBot ℕ)
      ∧ Q2.degree = ((510 : ℕ) : WithBot ℕ) ∧ Q3.degree = ((510 : ℕ) : WithBot ℕ) :=
  ⟨Q0_shape.2.1, Q1_shape.2.1, Q2_shape.2.1, Q3_shape.2.1⟩

/-- **The signed `Q₁` really is signed.**  `Q₁.coeff 510 = −lead1` and `lead1 > 0`, so an
instantiation that had used the UNSIGNED `ofList c1` would have supplied a `Pⱼ` whose evaluation
is `−α₁(n)`, and `h₁` would be false.  This is the cell's own warning, in the kernel. -/
theorem unsigned_P1_would_be_wrong : Q1.coeff 510 ≠ ((Zeta2XL1Data.lead1 : ℤ) : ℝ) := by
  rw [Q1_coeff]
  have h : (0 : ℝ) < ((Zeta2XL1Data.lead1 : ℤ) : ℝ) := by
    exact_mod_cast Zeta2XL1Data.lead1_pos
  intro hEq
  linarith

end Zeta2QGrow

/-! ## Receipts — BOTH channels, and the type beside every one (LEAN.md §1, 2026-09-20)

`#print axioms` is blind to `hψ`.  Every theorem below that carries it is printed with
`#check @` as well, and the acceptance for this row is the PAIR: the footprint inside
`{propext, Classical.choice, Quot.sound}`, and a type naming `Zeta2LegA.psiErrorBoundStatement`
and no other undischarged hypothesis.  Read `lean`'s exit code in its own channel too — neither
channel is sufficient alone. -/

#print axioms Zeta2QGrow.hornerZ_j1
#print axioms Zeta2QGrow.hornerZ_j2
#print axioms Zeta2QGrow.αR1_eq
#print axioms Zeta2QGrow.αR2_eq
#print axioms Zeta2QGrow.h0
#print axioms Zeta2QGrow.h1
#print axioms Zeta2QGrow.h2
#print axioms Zeta2QGrow.h3
#print axioms Zeta2QGrow.c0lead_tie
#print axioms Zeta2QGrow.c3lead_tie
#print axioms Zeta2QGrow.c1_length
#print axioms Zeta2QGrow.c2_length
#print axioms Zeta2QGrow.c1_lead
#print axioms Zeta2QGrow.c2_lead
#print axioms Zeta2QGrow.Q0_coeff
#print axioms Zeta2QGrow.Q1_coeff
#print axioms Zeta2QGrow.Q2_coeff
#print axioms Zeta2QGrow.Q3_coeff
#print axioms Zeta2QGrow.Q0_shape
#print axioms Zeta2QGrow.Q1_shape
#print axioms Zeta2QGrow.Q2_shape
#print axioms Zeta2QGrow.Q3_shape
#print axioms Zeta2QGrow.hA0'
#print axioms Zeta2QGrow.hA1'
#print axioms Zeta2QGrow.hA2'
#print axioms Zeta2QGrow.qn_growth
#print axioms Zeta2QGrow.qgrow_of_psi
#print axioms Zeta2QGrow.qgrow
#print axioms Zeta2QGrow.hgrowth_of_psi
#print axioms Zeta2QGrow.target_of_two_open_rows
#print axioms Zeta2QGrow.c1_is_positive
#print axioms Zeta2QGrow.growth_base_above_drate
#print axioms Zeta2QGrow.all_four_are_degree_510
#print axioms Zeta2QGrow.unsigned_P1_would_be_wrong

#check @Zeta2QGrow.qn_growth
#check @Zeta2QGrow.qgrow_of_psi
#check @Zeta2QGrow.qgrow
#check @Zeta2QGrow.hgrowth_of_psi
#check @Zeta2QGrow.target_of_two_open_rows
#check @Zeta2TWire.QGROW_open
#check @Zeta2TWire.RDECAY_open
#check @Zeta2DRate.ΔT_clearing_rate
#check @Zeta2DRate.ΔT_growth
