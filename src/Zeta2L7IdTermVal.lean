/-
Row L7ID: the RESID arm's PER-`m` LINE INTEGRALS, EVALUATED — `docs/future/zeta2-lean-chain.md`.

WHAT THIS FILE PROVES.  `Zeta2L7IdResid.integral_ResidArm_lineA` turned the RESID arm's line
integral into `∑'_m ∫ F n m`; it did not say what any of those integrals IS.  This file does,
in closed form, at every `n` and every `m`:

    integral_F_eq_zero (n) (hm : 4 * n < m) : ∫ s, F n m s = 0
    integral_F_eq      (n) (hm : m ≤ 4 * n) :
      ∫ s, F n m s = ∑ k ∈ window n, ↑(Pin n * ck n k) * ↑(2π / ((k : ℝ) - m) ^ 2)

so the family is supported on `m ≤ 4n` — the half-plane on the CELL side — and each surviving
term is an elementary `2π/(k − m)²`.

WHY THE ANSWER IS THIS CLEAN, and it is a property of the CELL contour rather than of the
integrand.  On `Re t = −4n − ½` the two shifts are `b_k = k − 4n − ½` and `a_m = m − 4n − ½`.
Every window pole has `k ≥ 15n + 1`, so `b_k ≥ 11n + ½ > 0` — ALL the window poles are on one
side.  `Zeta2L7LineInt.integral_line_two_pole` then gives `π(sgn b − sgn a)/(a − b)²`, which is

  * `0` whenever `a_m > 0`, i.e. `m ≥ 4n + 1`: the double pole joins the window poles on the same
    side and the term contributes nothing;
  * `2π/(a_m − b_k)² = 2π/(m − k)²` whenever `a_m < 0`, i.e. `m ≤ 4n`.

The `a = b` case is not an oversight and it is not vacuous: `m = k` DOES occur, for the `11n + 1`
values of `m` inside the window, and there the integrand is a TRIPLE pole `(lin a s)⁻³` whose
integral is `Zeta2L7Id0Val.integral_inv_lin_cube`'s `0`.  It lands in the vanishing branch, so the
statement above needs no third case — but the proof does, and a file that had only two branches
would be wrong exactly on the window.

WHAT THIS SETS UP, and what it deliberately does NOT do.  Summing the closed form over `m ≤ 4n`
with `j = k − m ≥ k − 4n ≥ 11n + 1` gives `∑_k c_k · 2π · (ζ(2) − harm 2 (k − 4n − 1))`, and
`Zeta2Defs.Member.harmIndex n k = k − b₃n − 1 = k − 4n − 1` at the candidate — the chain's own
index, not a lookalike.  That summation is NOT performed here: it needs the `m`/`k` sum
interchange and `Zeta2Defs.hasSum_zeta2`, and it is its own step.  Nothing here mentions
`candidateM.rn`, so RDECAY gains nothing; obligation 2's estimate is untouched; the `Ppol` arm
still rests on `Zeta2L7IdMoment.SechMomentTable`.

ACCEPTANCE (LEAN.md §1, as sharpened 2026-09-20): the receipt AND the printed type.  Every
theorem prints both.

Elaborate: sh external_tests/zeta2_arith/run_probe.sh Zeta2L7IdTermVal.lean
Falsifier:  bash external_tests/zeta2_arith/falsify_l7idtermval.sh

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2
         mathlib   5aedf732b6987e8c26ab3c9ebc855314f82b045f
-/
import Mathlib
import Zeta2L7IdResid

namespace Zeta2L7IdTermVal

open MeasureTheory Complex
open Zeta2Defs Zeta2L7LineInt Zeta2L7IdResid

/-! ## §1. Which side of the contour each pole is on

This is the whole file's content in one place: `b_k > 0` for every window pole, and `a_m` changes
sign exactly at `m = 4n`, which is the cell. -/

/-- **Every window pole is strictly to the LEFT of the cell contour**, so its shift is positive.
`k ≥ 15n + 1` and the abscissa is `4n + ½`, so `b_k ≥ 11n + ½`. -/
theorem offN_pos {n k : ℕ} (hk : k ∈ candidateM.window n) : 0 < offN n k := by
  rw [Member.window, Finset.mem_Icc] at hk
  have hk1 : 15 * n + 1 ≤ k := by simpa [candidateM] using hk.1
  have hkR : (15 * (n : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [offN]
  linarith

theorem offN_ne_zero {n k : ℕ} (hk : k ∈ candidateM.window n) : offN n k ≠ 0 :=
  ne_of_gt (offN_pos hk)

/-- Above the cell the double pole joins them. -/
theorem offZ_pos {n : ℕ} {m : ℤ} (hm : 4 * (n : ℤ) < m) : 0 < offZ n m := by
  have h : 4 * (n : ℤ) + 1 ≤ m := by omega
  have hR : 4 * (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
  rw [offZ]
  linarith

/-- At or below the cell it is on the other side. -/
theorem offZ_neg {n : ℕ} {m : ℤ} (hm : m ≤ 4 * (n : ℤ)) : offZ n m < 0 := by
  have hR : (m : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast hm
  rw [offZ]
  linarith

theorem offZ_ne_zero (n : ℕ) (m : ℤ) : offZ n m ≠ 0 := by
  rcases le_or_gt m (4 * (n : ℤ)) with h | h
  · exact ne_of_lt (offZ_neg h)
  · exact ne_of_gt (offZ_pos h)

theorem offZ_sub_offN (n : ℕ) (m : ℤ) (k : ℕ) : offZ n m - offN n k = (m : ℝ) - (k : ℝ) := by
  rw [offZ, offN]
  ring

/-! ## §2. One term, evaluated -/

/-- The `(k, m)` term of `F`, in `Zeta2L7LineInt`'s own product order. -/
theorem term_eq (n : ℕ) (m : ℤ) (k : ℕ) (s : ℝ) :
    (Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ))
        * (Zeta2L7IdMoment.lineA n s + (m : ℂ)) ^ 2
      = (lin (offZ n m) s) ^ 2 * lin (offN n k) s := by
  rw [lineA_add_natCast, lineA_add_intCast]
  ring

/-- **ABOVE THE CELL every term vanishes**, and the proof needs the `m = k` branch: inside the
window the two shifts COINCIDE and the integrand is a triple pole, not a two-pole product. -/
theorem integral_term_eq_zero {n : ℕ} {m : ℤ} (hm : 4 * (n : ℤ) < m) {k : ℕ}
    (hk : k ∈ candidateM.window n) :
    ∫ s : ℝ, ((lin (offZ n m) s) ^ 2 * lin (offN n k) s)⁻¹ = 0 := by
  rcases eq_or_ne (offZ n m) (offN n k) with heq | hne
  · -- the TRIPLE pole: `m = k`, which happens for every `m` in the window
    rw [heq]
    have hcube : ∀ s : ℝ,
        ((lin (offN n k) s) ^ 2 * lin (offN n k) s)⁻¹ = ((lin (offN n k) s) ^ 3)⁻¹ := by
      intro s
      rw [← pow_succ]
    rw [integral_congr_ae (Filter.Eventually.of_forall hcube)]
    exact Zeta2L7Id0Val.integral_inv_lin_cube (offN_ne_zero hk)
  · have hb := offN_pos hk
    have ha := offZ_pos hm
    rw [Zeta2L7LineInt.integral_line_two_pole (ne_of_gt ha) (ne_of_gt hb) hne,
      abs_of_pos ha, abs_of_pos hb, div_self (ne_of_gt ha), div_self (ne_of_gt hb)]
    norm_num

/-- **AT OR BELOW THE CELL** the term is the elementary `2π/(k − m)²`. -/
theorem integral_term_eq {n : ℕ} {m : ℤ} (hm : m ≤ 4 * (n : ℤ)) {k : ℕ}
    (hk : k ∈ candidateM.window n) :
    ∫ s : ℝ, ((lin (offZ n m) s) ^ 2 * lin (offN n k) s)⁻¹
      = ((2 * Real.pi / ((k : ℝ) - (m : ℝ)) ^ 2 : ℝ) : ℂ) := by
  have hb := offN_pos hk
  have ha := offZ_neg hm
  have hne : offZ n m ≠ offN n k := by
    intro h
    rw [h] at ha
    linarith
  rw [Zeta2L7LineInt.integral_line_two_pole (ne_of_lt ha) (ne_of_gt hb) hne,
    abs_of_neg ha, abs_of_pos hb, div_self (ne_of_gt hb), offZ_sub_offN]
  have hdiv : offZ n m / -offZ n m = -1 := by
    rw [div_neg, div_self (ne_of_lt ha)]
  rw [hdiv]
  congr 1
  have hsq : ((m : ℝ) - (k : ℝ)) ^ 2 = ((k : ℝ) - (m : ℝ)) ^ 2 := by ring
  rw [hsq]
  ring

/-! ## §3. The finite `k`-sum, and the per-`m` value

`integral_finset_sum` wants each summand integrable, which is the per-term half of
`Zeta2L7IdResid.integrable_F`; the constant comes out by `integral_const_mul`, which is
unconditional. -/

theorem integrable_single (n : ℕ) (m : ℤ) (k : ℕ) :
    Integrable (fun s : ℝ =>
      ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
        / ((Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ))
            * (Zeta2L7IdMoment.lineA n s + (m : ℂ)) ^ 2)) := by
  have hA := A_pos n m
  have hcont : Continuous (fun s : ℝ =>
      ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
        / ((Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ))
            * (Zeta2L7IdMoment.lineA n s + (m : ℂ)) ^ 2)) := by
    refine Continuous.div continuous_const ?_ (fun s => ?_)
    · exact ((Zeta2L7IdContour.continuous_lineA n).add continuous_const).mul
        (((Zeta2L7IdContour.continuous_lineA n).add continuous_const).pow 2)
    · rw [lineA_add_natCast, lineA_add_intCast]
      refine mul_ne_zero (lin_ne_zero ?_ s) (pow_ne_zero 2 (lin_ne_zero (offZ_ne_zero n m) s))
      intro h
      have := half_le_abs_offN n k
      rw [h, abs_zero] at this
      linarith
  refine ((integrable_maj hA 1).const_mul
    ‖((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)‖).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with s
  have hy2 : ‖Zeta2L7IdMoment.lineA n s + (m : ℂ)‖ ^ 2 = s ^ 2 + A n m ^ 2 :=
    norm_sq_lineA_add_intCast n m s
  have hxge : Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2)
      ≤ ‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖ := sqrt_le_norm_lineA_add_natCast n k s
  have hroot : (0 : ℝ) < Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  have hden : (0 : ℝ) < (s ^ 2 + A n m ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) := by
    have : (0 : ℝ) < s ^ 2 + A n m ^ 2 := by positivity
    exact mul_pos this hroot
  have hprod : (s ^ 2 + A n m ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2)
      ≤ ‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖
        * ‖Zeta2L7IdMoment.lineA n s + (m : ℂ)‖ ^ 2 := by
    rw [hy2]
    calc (s ^ 2 + A n m ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2)
        = Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) * (s ^ 2 + A n m ^ 2) := by ring
      _ ≤ ‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖ * (s ^ 2 + A n m ^ 2) := by
          refine mul_le_mul_of_nonneg_right hxge ?_
          positivity
  calc ‖((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
          / ((Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ))
              * (Zeta2L7IdMoment.lineA n s + (m : ℂ)) ^ 2)‖
      = ‖((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)‖
          * (‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖
              * ‖Zeta2L7IdMoment.lineA n s + (m : ℂ)‖ ^ 2)⁻¹ := by
        rw [norm_div, norm_mul, norm_pow, div_eq_mul_inv]
    _ ≤ ‖((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)‖
          * ((s ^ 2 + A n m ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_left (Zeta2L7Id0Val.inv_le_inv_of_le' hden hprod) (norm_nonneg _)
    _ ≤ ‖((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)‖
          * (1 / 2 * (A n m ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹
              + (1 : ℝ)⁻¹ / 2 * (s ^ 2 + A n m ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (inv_prod_le hA one_pos s) (norm_nonneg _)

theorem integral_F_split (n : ℕ) (m : ℤ) :
    (∫ s : ℝ, F n m s)
      = ∑ k ∈ candidateM.window n,
          ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
            * ∫ s : ℝ, ((lin (offZ n m) s) ^ 2 * lin (offN n k) s)⁻¹ := by
  -- `simp only`, not `rw`: `F n m s` sits under the integral's lambda binder and `rw` does not
  -- rewrite under binders ("Failed to rewrite using equation theorems for `F`", measured on this
  -- file's first elaboration).
  simp only [Zeta2L7IdResid.F]
  -- `integral_finset_sum` is DEPRECATED at this pin; `integral_finsetSum` is the name.
  rw [integral_finsetSum _ (fun k _ => integrable_single n m k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  -- `simp only`, not `rw`: `integral_congr_ae` leaves the two sides as UNREDUCED applications
  -- `(fun a => …) s`, and `rw` does not beta-reduce (measured on this file's first elaboration).
  simp only [term_eq n m k s, div_eq_mul_inv]

/-- **ABOVE THE CELL the whole `m`-th integral vanishes.** -/
theorem integral_F_eq_zero (n : ℕ) {m : ℤ} (hm : 4 * (n : ℤ) < m) :
    (∫ s : ℝ, F n m s) = 0 := by
  rw [integral_F_split]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [integral_term_eq_zero hm hk, mul_zero]

/-- **AT OR BELOW THE CELL**, the closed form: an elementary sum over the pole window. -/
theorem integral_F_eq (n : ℕ) {m : ℤ} (hm : m ≤ 4 * (n : ℤ)) :
    (∫ s : ℝ, F n m s)
      = ∑ k ∈ candidateM.window n,
          ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
            * ((2 * Real.pi / ((k : ℝ) - (m : ℝ)) ^ 2 : ℝ) : ℂ) := by
  rw [integral_F_split]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_term_eq hm hk]

/-! ## §4. The index the chain already has, and the edge

`Member.harmIndex n k = k − b₃n − 1`, and `b₃ = 4` at the candidate — so the `j = k − m` the
summation below `m ≤ 4n` runs over starts at exactly `harmIndex n k + 1`.  Recorded as a theorem
because the next step's whole identification rests on it being the CHAIN's index and not a
lookalike (LEAN.md §6). -/

/-- `harmIndex n k = k − 4n − 1` at the candidate. -/
theorem harmIndex_eq (n k : ℕ) : candidateM.harmIndex n k = k - 4 * n - 1 := by
  rw [Member.harmIndex]
  simp [candidateM]

/-- **The EDGE that decides the support**: at `n = 0` the cell is `m ≤ 0`, which is exactly
L7ID-0's own support (`Zeta2L7LineInt.integral_term_ge_two`/`_le_zero` vanish for `m ≥ 2` and are
`2π/(m−1)²` for `m ≤ 0`, with the `m = 1` triple pole between them).  Here `window 0 = {1}`, so
the single `k` is `1` and the closed form at `m ≤ 0` reads `2π/(1−m)²` — the SAME family, derived
from the general statement rather than resembling it. -/
theorem integral_F_zero_eq (m : ℤ) (hm : m ≤ 0) :
    (∫ s : ℝ, F 0 m s)
      = ((2 * Real.pi / ((1 : ℝ) - (m : ℝ)) ^ 2 : ℝ) : ℂ) := by
  have h := integral_F_eq 0 (by simpa using hm)
  rw [h, candidateM.window_zero, Finset.sum_singleton, candidateM.Pin_zero,
    candidateM.ck_zero]
  norm_num

end Zeta2L7IdTermVal

/-! ## RECEIPTS — the footprint AND the type, for every theorem (LEAN.md §1). -/

#print axioms Zeta2L7IdTermVal.offN_pos
#check @Zeta2L7IdTermVal.offN_pos
#print axioms Zeta2L7IdTermVal.offZ_pos
#check @Zeta2L7IdTermVal.offZ_pos
#print axioms Zeta2L7IdTermVal.offZ_neg
#check @Zeta2L7IdTermVal.offZ_neg
#print axioms Zeta2L7IdTermVal.offZ_ne_zero
#check @Zeta2L7IdTermVal.offZ_ne_zero
#print axioms Zeta2L7IdTermVal.offZ_sub_offN
#check @Zeta2L7IdTermVal.offZ_sub_offN
#print axioms Zeta2L7IdTermVal.term_eq
#check @Zeta2L7IdTermVal.term_eq
#print axioms Zeta2L7IdTermVal.integral_term_eq_zero
#check @Zeta2L7IdTermVal.integral_term_eq_zero
#print axioms Zeta2L7IdTermVal.integral_term_eq
#check @Zeta2L7IdTermVal.integral_term_eq
#print axioms Zeta2L7IdTermVal.integrable_single
#check @Zeta2L7IdTermVal.integrable_single
#print axioms Zeta2L7IdTermVal.integral_F_split
#check @Zeta2L7IdTermVal.integral_F_split
#print axioms Zeta2L7IdTermVal.integral_F_eq_zero
#check @Zeta2L7IdTermVal.integral_F_eq_zero
#print axioms Zeta2L7IdTermVal.integral_F_eq
#check @Zeta2L7IdTermVal.integral_F_eq
#print axioms Zeta2L7IdTermVal.harmIndex_eq
#check @Zeta2L7IdTermVal.harmIndex_eq
#print axioms Zeta2L7IdTermVal.integral_F_zero_eq
#check @Zeta2L7IdTermVal.integral_F_zero_eq
