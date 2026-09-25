/-
# Row L7ID — `PpolMomentValue` PROVED, and `rₙ = −rLine n` becomes UNCONDITIONAL

`Zeta2L7IdSum` reduced row L7ID's target to one named `Prop`:

    rn_eq_neg_rLine_iff (hn : 1 ≤ n) : candidateM.rn n = -L7MidM5.rLine n ↔ PpolMomentValue n

and TOOK that `Prop` rather than proving it.  This file proves it, at EVERY `n` (the `1 ≤ n`
is the consumer's, not this statement's), so

    rn_eq_neg_rLine (hn : 1 ≤ n) : candidateM.rn n = -L7MidM5.rLine n

carries no hypothesis beyond `1 ≤ n`.  Read the `#check` receipts: `ppolMomentValue` takes
`(n : ℕ)` and nothing else, and `rn_eq_neg_rLine_uncond` takes `(hn : 1 ≤ n)` and nothing else.

## The route, and what it is NOT

The `Ppol` arm's integrand on the route-A line is `Π(n)·Ppol_n(t)·(π/sin πt)²` at
`t = lineA n s = C + i s`, `C = −4n − ½`; `Zeta2L7IdMoment.kernel_lineA` collapses the kernel to
the REAL `π² sech²(π s)`, so the whole arm is `Π(n)` times a polynomial against a real weight.
`Polynomial.aeval_eq_sum_range` expands the polynomial over `range (natDegree + 1)` — the SAME
index set `Zeta2Defs.Member.pnPoly` sums over, which is why the two match term by term — and
`Zeta2MomentLaw.integral_line_pow` evaluates each monomial's integral as `2π·B_j(C + ½)`.  The
last step is arithmetic and is the reason the arm was ever stateable: `C + ½ = −4n`, and
`Zeta2L7IdMoment.momI_cell_eq` says `momI (cell n) j = B_j(−4n)`.  So the `j`-th term is
`2π·momI (cell n) j` and the sum is `2π·pnPoly n`, by the DEFINITION of `pnPoly` and not by a
second construction of it.

NOTHING here is an estimate.  Obligation 2 of row L7ID — the decay RATE on `rₙ` — is untouched
by this file and by everything it imports; this is a VALUE identity.
-/
import Mathlib
import Zeta2L7IdSum
import Zeta2MomentLaw

namespace Zeta2PpolMoment

open MeasureTheory Complex Zeta2Defs

/-! ## §1. The arm on the line, in the moment law's vocabulary -/

/-- `Zeta2L7IdMoment.kernel_lineA`'s real value IS `Zeta2SechMoment.sechKer` — the two spellings
tied once, here, so neither file carries a copy of the other's (LEAN.md §6). -/
theorem kernel_eq_sechKer (s : ℝ) :
    ((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ) = Zeta2SechMoment.sechKer s := by
  rw [Zeta2SechMoment.sechKer, div_pow]

/-- The route-A line IS the moment law's `C + i s`, at `C = −4n − ½`.  Definitional; stated so
the instantiation below is a `rw` and not a `show`. -/
theorem lineA_eq (n : ℕ) (s : ℝ) :
    Zeta2L7IdMoment.lineA n s = ((-4 * (n : ℝ) - 1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I := rfl

/-- The `Ppol` arm on the route-A line: `Π(n)` times the polynomial times the REAL kernel. -/
theorem PpolArm_lineA (n : ℕ) (s : ℝ) :
    Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s)
      = ((candidateM.Pin n : ℚ) : ℂ)
          * Polynomial.aeval (Zeta2L7IdMoment.lineA n s) (candidateM.Ppol n)
          * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ) := by
  rw [Zeta2L7IdSplit.PpolArm, Zeta2L7IdMoment.kernel_lineA, kernel_eq_sechKer]

/-! ## §2. The Bernoulli value at the cell, transported ℚ → ℝ -/

/-- `aeval` at a cast rational IS the cast of `eval` at the rational.  The general twin of
`Zeta2SechMoment.eval_bernoulli_half_real`, which is that statement at `q = ½`. -/
theorem aeval_real_of_rat (j : ℕ) (q : ℚ) :
    Polynomial.aeval ((q : ℚ) : ℝ) (Polynomial.bernoulli j)
      = (((Polynomial.bernoulli j).eval q : ℚ) : ℝ) := by
  rw [Polynomial.aeval_def, ← eq_ratCast (algebraMap ℚ ℝ) q, Polynomial.eval₂_at_apply,
    eq_ratCast]

/-- **`C + ½ = −4n`, and that number is the cell's.**  The whole arithmetic content of the arm's
identification, and the reason `momI` is the right object to land on (`Zeta2L7IdMoment`'s §3). -/
theorem aeval_shift_eq_momI (n j : ℕ) :
    Polynomial.aeval ((1 / 2 : ℝ) + (-4 * (n : ℝ) - 1 / 2 : ℝ)) (Polynomial.bernoulli j)
      = ((Zeta2Defs.momI (candidateM.cell n) j : ℚ) : ℝ) := by
  have harg : (1 / 2 : ℝ) + (-4 * (n : ℝ) - 1 / 2 : ℝ) = ((-(4 * n : ℚ) : ℚ) : ℝ) := by
    push_cast
    ring
  rw [harg, aeval_real_of_rat, Zeta2L7IdMoment.momI_cell_eq]

/-! ## §3. THE ARM'S INTEGRAL, evaluated -/

/-- Each monomial of `Ppol` contributes `2π · momI (cell n) j`. -/
theorem integral_lineA_pow (n j : ℕ) :
    (∫ s : ℝ, (Zeta2L7IdMoment.lineA n s) ^ j * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ))
      = ((2 * Real.pi * ((Zeta2Defs.momI (candidateM.cell n) j : ℚ) : ℝ) : ℝ) : ℂ) := by
  simp only [lineA_eq]
  rw [Zeta2MomentLaw.integral_line_pow (-4 * (n : ℝ) - 1 / 2 : ℝ) j, aeval_shift_eq_momI n j]

theorem integrable_lineA_pow (n j : ℕ) :
    Integrable (fun s : ℝ =>
      (Zeta2L7IdMoment.lineA n s) ^ j * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ)) volume := by
  simp only [lineA_eq]
  exact Zeta2MomentLaw.integrable_line_pow (-4 * (n : ℝ) - 1 / 2 : ℝ) j

/-- **THE ARM'S INTEGRAL.**  `∫ PpolArm∘lineA = 2π · Π(n) · pnPoly n`, REAL, at every `n`.  The
index set is `(Ppol n).natDegree + 1` on both sides — `Polynomial.aeval_eq_sum_range`'s and
`Member.pnPoly`'s — so the sums match term by term and no degree bound is needed anywhere. -/
theorem integral_PpolArm_lineA (n : ℕ) :
    (∫ s : ℝ, Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s))
      = ((2 * Real.pi * ((candidateM.Pin n * candidateM.pnPoly n : ℚ) : ℝ) : ℝ) : ℂ) := by
  have hexp : ∀ s : ℝ, Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s)
      = ∑ j ∈ Finset.range ((candidateM.Ppol n).natDegree + 1),
          (((candidateM.Pin n * (candidateM.Ppol n).coeff j : ℚ)) : ℂ)
            * ((Zeta2L7IdMoment.lineA n s) ^ j * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ)) := by
    intro s
    rw [PpolArm_lineA, Polynomial.aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Rat.smul_def]
    push_cast
    ring
  have hint : ∀ j ∈ Finset.range ((candidateM.Ppol n).natDegree + 1), Integrable
      (fun s : ℝ => (((candidateM.Pin n * (candidateM.Ppol n).coeff j : ℚ)) : ℂ)
        * ((Zeta2L7IdMoment.lineA n s) ^ j * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ))) volume :=
    fun j _ => (integrable_lineA_pow n j).const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_finsetSum _ hint]
  have hsum : ∀ j ∈ Finset.range ((candidateM.Ppol n).natDegree + 1),
      (∫ s : ℝ, (((candidateM.Pin n * (candidateM.Ppol n).coeff j : ℚ)) : ℂ)
        * ((Zeta2L7IdMoment.lineA n s) ^ j * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ)))
      = (((candidateM.Pin n * (candidateM.Ppol n).coeff j : ℚ)) : ℂ)
          * ((2 * Real.pi * ((Zeta2Defs.momI (candidateM.cell n) j : ℚ) : ℝ) : ℝ) : ℂ) := by
    intro j _
    rw [integral_const_mul, integral_lineA_pow n j]
  rw [Finset.sum_congr rfl hsum, Member.pnPoly, Finset.mul_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-! ## §4. THE ROW'S VALUE OBLIGATION, DISCHARGED -/

/-- **`Zeta2L7IdSum.PpolMomentValue n`, PROVED at every `n`.**  This is the `Prop` that file
TOOK; it is a theorem now, and it takes no hypothesis at all — not even `1 ≤ n`. -/
theorem ppolMomentValue (n : ℕ) : Zeta2L7IdSum.PpolMomentValue n := by
  have hpi := Real.pi_pos
  rw [Zeta2L7IdSum.PpolMomentValue, integral_PpolArm_lineA n, Complex.ofReal_re]
  field_simp

/-- **ROW L7ID'S TARGET, UNCONDITIONAL.**  `rₙ = −rLine n` for every `n ≥ 1`, with the
`PpolMomentValue` binder DISCHARGED rather than carried.  Compare `Zeta2L7IdSum.rn_eq_neg_rLine`,
whose type names `hP` — `#print axioms` cannot tell the two apart (LEAN.md §1), so read the
`#check` receipts below, where this one's binder list is `{n : ℕ}` and `1 ≤ n` and nothing else. -/
theorem rn_eq_neg_rLine_uncond {n : ℕ} (hn : 1 ≤ n) :
    candidateM.rn n = -L7MidM5.rLine n :=
  Zeta2L7IdSum.rn_eq_neg_rLine hn (ppolMomentValue n)

/-- The same statement against the EQUIVALENCE rather than the conditional form, so the two
spellings `Zeta2L7IdSum` exports cannot drift apart from this one. -/
theorem rn_eq_neg_rLine_iff_true {n : ℕ} (hn : 1 ≤ n) :
    candidateM.rn n = -L7MidM5.rLine n :=
  (Zeta2L7IdSum.rn_eq_neg_rLine_iff hn).mpr (ppolMomentValue n)

/-! ## §5. EDGES (LEAN.md §5), asked of the real data

At `n = 0` the arm is empty on BOTH sides — `Ppol 0 = 0` and `pnPoly 0 = 0` — so
`ppolMomentValue 0` is the identity `0 = 0` and is not evidence about any `n ≥ 1`.  It is
recorded because a reader who saw `∀ n` might otherwise take `n = 0` as the smallest instance,
which is exactly the mistake L7ID-0's cell warns about: `n = 0` is NOT a template for this arm. -/

theorem integral_PpolArm_lineA_zero :
    (∫ s : ℝ, Zeta2L7IdSplit.PpolArm 0 (Zeta2L7IdMoment.lineA 0 s)) = 0 := by
  rw [integral_PpolArm_lineA 0, Zeta2L7IdSum.pnPoly_zero]
  push_cast
  ring

end Zeta2PpolMoment

/-! ## RECEIPTS — the footprint AND the type, for every theorem (LEAN.md §1).

The two that matter are the last two before the edge: `ppolMomentValue` takes `(n : ℕ)` and NO
hypothesis, and `rn_eq_neg_rLine_uncond` takes `{n : ℕ}` and `1 ≤ n` and no other binder.  That
is the whole difference between this file and `Zeta2L7IdSum.rn_eq_neg_rLine`, whose footprint is
byte-identical and whose type is not. -/

#print axioms Zeta2PpolMoment.kernel_eq_sechKer
#check @Zeta2PpolMoment.kernel_eq_sechKer
#print axioms Zeta2PpolMoment.lineA_eq
#check @Zeta2PpolMoment.lineA_eq
#print axioms Zeta2PpolMoment.PpolArm_lineA
#check @Zeta2PpolMoment.PpolArm_lineA
#print axioms Zeta2PpolMoment.aeval_real_of_rat
#check @Zeta2PpolMoment.aeval_real_of_rat
#print axioms Zeta2PpolMoment.aeval_shift_eq_momI
#check @Zeta2PpolMoment.aeval_shift_eq_momI
#print axioms Zeta2PpolMoment.integral_lineA_pow
#check @Zeta2PpolMoment.integral_lineA_pow
#print axioms Zeta2PpolMoment.integrable_lineA_pow
#check @Zeta2PpolMoment.integrable_lineA_pow
#print axioms Zeta2PpolMoment.integral_PpolArm_lineA
#check @Zeta2PpolMoment.integral_PpolArm_lineA
#print axioms Zeta2PpolMoment.ppolMomentValue
#check @Zeta2PpolMoment.ppolMomentValue
#print axioms Zeta2PpolMoment.rn_eq_neg_rLine_uncond
#check @Zeta2PpolMoment.rn_eq_neg_rLine_uncond
#print axioms Zeta2PpolMoment.rn_eq_neg_rLine_iff_true
#check @Zeta2PpolMoment.rn_eq_neg_rLine_iff_true
#print axioms Zeta2PpolMoment.integral_PpolArm_lineA_zero
#check @Zeta2PpolMoment.integral_PpolArm_lineA_zero
