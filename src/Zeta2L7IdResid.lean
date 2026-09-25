/-
Row L7ID, OBLIGATION 3 of 5: the `∫Σ` interchange on the RESID arm — `docs/future/zeta2-lean-chain.md`.

WHAT THIS FILE PROVES.

    Zeta2L7IdResid.integral_ResidArm_lineA (n : ℕ) :
      ∫ s, Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s) = ∑' m : ℤ, ∫ s, F n m s

at EVERY `n`, on the CELL contour `Re t = −4n − ½`, where `F n m s` is the `m`-th summand of
`Zeta2L7IdContour.ResidArm_lineA_eq_tsum` — the finite `k`-sum over the pole window.  The two
hypotheses `MeasureTheory.integral_tsum_of_summable_integral_norm` asks for are discharged:
`integrable_F` (every term integrable on the line) and `summable_integral_norm` (hypothesis (b),
`Σ_m ∫‖F_m‖ < ∞`), which is the one the row's cell called "the work".

WHY IT IS AVAILABLE HERE AND NOWHERE EARLIER.  The UNSPLIT family cannot take this step at any
`n ≥ 1`: `R_n` has degree `16n − 1`, so the hinge's `m`-th terms grow like `|s|^{16n−3}` and
hypothesis (a) is false (`l7id_ratfun_check.py` ARM 4).  The `Ppol`/residue split
(`Zeta2L7IdSplit`) is what produces a family that decays like `|t|^{−3}`, and obligation 5
(`Zeta2L7IdContour`) is what puts that family on the contour the rest of the row uses.  This file
is the third of those three and it consumes both for real rather than restating them.

THE ESTIMATE, and where each factor's decay comes from.  On the cell contour

    ‖lineA n s + k‖² = s² + (k − 4n − ½)²   and   ‖lineA n s + m‖² = s² + (m − 4n − ½)²,

and `k − 4n − ½` is a half-odd-integer for EVERY natural `k`, so `‖lineA n s + k‖ ≥ √(s² + ¼)`
with no fact about the window at all.  That is the whole reason hypothesis (b) holds: the
`k`-factor is NOT bounded below by a constant in the way that would matter — keeping its `s`
decay is what turns `∫‖F_m‖ ≲ 1/|m|` (not summable) into `∫‖F_m‖ ≲ |m|^{−3/2}` (summable).  The
free `k` of `Zeta2L7Id0Val.amgm_inv_sqrt` is spent at `k = √A`, exactly as at `n = 0`; the true
size is `log|m|/m²` and the `3/2` is a deliberate under-estimate, since summable is all the
interchange wants.  **The `|m|^{−2}` sharpening is measured FALSE from `m = 5` on** (row L7ID-0's
cell), so the `3/2` is carrying weight and is not a convenience.

WHAT IS REUSED RATHER THAN RESPELLED (LEAN.md §3/§6).  `A n m = |m − 4n − ½|` is literally
`Zeta2L7Id0Val.A (m − 4n)` — the `n = 0` file's own distance function at a SHIFTED index — so
`A_pos`, `w_mono`, `maj_le`, `summable_w` and `summable_w_shift` are applied here, not copied.
What is genuinely new is (i) the scale-`a` generalisation of that file's pointwise majorant,
which at `n = 0` was stated only at `a = A m`, (ii) the finite `k`-sum, which `n = 0` did not
have (its window is the single pole `k = 1`), and (iii) the `m ↦ m − 4n` reindexing of the
summable majorant.

WHAT IS NOT PROVED, so the ROW still does not close:
  * obligation 2, the ESTIMATE, is untouched — this file bounds `∫‖F_m‖` well enough to
    interchange, which is a far weaker statement than the row's rate needs.
  * the per-`m` integrals `∫ F n m` are not EVALUATED here.  At `n = 0` they are
    `0 / 0 / 2π(m−1)⁻²` (`Zeta2L7LineInt.integral_term_ge_two`/`_le_zero`); at general `n` the
    `k`-sum and the window make that a separate obligation.
  * the `Ppol` arm's value still rests on `Zeta2L7IdMoment.SechMomentTable`, a `Prop`.
  * NOTHING here mentions `candidateM.rn`, so RDECAY gains nothing.

ACCEPTANCE (LEAN.md §1, as sharpened 2026-09-20): the receipt AND the printed type.  Every
theorem below prints both; the only binders are `n : ℕ`, `m : ℤ`, `k : ℝ`, `s : ℝ`, `a : ℝ` and
positivity side conditions on the last two.  No hypothesis from anywhere else in the chain.

Elaborate: sh external_tests/zeta2_arith/run_probe.sh Zeta2L7IdResid.lean
Falsifier:  bash external_tests/zeta2_arith/falsify_l7idresid.sh

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2
         mathlib   5aedf732b6987e8c26ab3c9ebc855314f82b045f
-/
import Mathlib
import Zeta2L7Id0Val
import Zeta2L7IdContour

namespace Zeta2L7IdResid

open MeasureTheory Complex Filter Topology
open Zeta2Defs Zeta2L7LineInt

/-! ## §1. The cell contour in `lin`'s vocabulary

`Zeta2L7LineInt` is stated for `lin a s = a + i s` at arbitrary real `a`.  The cell contour's
shifts are `k − 4n − ½` and `m − 4n − ½`, so the whole of that file becomes available once these
two rewrites are in place. -/

/-- The shift of the `k`-th window pole, as a real abscissa. -/
noncomputable def offN (n : ℕ) (k : ℕ) : ℝ := (k : ℝ) - 4 * (n : ℝ) - 1 / 2

/-- The shift of the `m`-th kernel pole, as a real abscissa. -/
noncomputable def offZ (n : ℕ) (m : ℤ) : ℝ := (m : ℝ) - 4 * (n : ℝ) - 1 / 2

theorem lineA_add_natCast (n k : ℕ) (s : ℝ) :
    Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ) = lin (offN n k) s := by
  rw [Zeta2L7IdMoment.lineA, lin, offN]
  push_cast
  ring

theorem lineA_add_intCast (n : ℕ) (m : ℤ) (s : ℝ) :
    Zeta2L7IdMoment.lineA n s + (m : ℂ) = lin (offZ n m) s := by
  rw [Zeta2L7IdMoment.lineA, lin, offZ]
  push_cast
  ring

/-- **Every shift is a half-odd-integer, so every one of them is at least `½` away from `0`.**
This is the file's one arithmetic input and it says nothing about the window: it is true for
EVERY natural `k` and every integer `m`, which is why no window fact is ever needed below. -/
theorem half_le_abs_sub_half (j : ℤ) : (1 : ℝ) / 2 ≤ |(j : ℝ) - 1 / 2| := by
  rcases le_or_gt j 0 with h | h
  · have hj : (j : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h1 : (1 : ℤ) ≤ j := h
    have hj : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h1
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem half_le_abs_offN (n k : ℕ) : (1 : ℝ) / 2 ≤ |offN n k| := by
  have h := half_le_abs_sub_half ((k : ℤ) - 4 * (n : ℤ))
  refine le_of_le_of_eq h ?_
  congr 1
  rw [offN]
  push_cast
  ring

/-- `A n m`, the distance from the `m`-th double pole to the cell contour, IS the `n = 0` file's
own `A` at the shifted index `m − 4n`.  Defined that way rather than restated, so every lemma
proved about it there applies here (LEAN.md §6). -/
noncomputable def A (n : ℕ) (m : ℤ) : ℝ := Zeta2L7Id0Val.A (m - 4 * (n : ℤ))

theorem A_eq_abs_offZ (n : ℕ) (m : ℤ) : A n m = |offZ n m| := by
  rw [A, Zeta2L7Id0Val.A, offZ]
  congr 1
  push_cast
  ring

theorem A_pos (n : ℕ) (m : ℤ) : 0 < A n m := Zeta2L7Id0Val.A_pos _

theorem norm_sq_lineA_add_intCast (n : ℕ) (m : ℤ) (s : ℝ) :
    ‖Zeta2L7IdMoment.lineA n s + (m : ℂ)‖ ^ 2 = s ^ 2 + A n m ^ 2 := by
  rw [lineA_add_intCast, norm_sq_lin, A_eq_abs_offZ, sq_abs]

theorem sqrt_le_norm_lineA_add_natCast (n k : ℕ) (s : ℝ) :
    Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) ≤ ‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖ := by
  have hsq : ‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖ ^ 2 = s ^ 2 + |offN n k| ^ 2 := by
    rw [lineA_add_natCast, norm_sq_lin, sq_abs]
  have hle : s ^ 2 + (1 / 2 : ℝ) ^ 2 ≤ ‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖ ^ 2 := by
    rw [hsq]
    have h := half_le_abs_offN n k
    nlinarith [abs_nonneg (offN n k)]
  calc Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2)
      ≤ Real.sqrt (‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = ‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## §2. The family, and the constant the finite `k`-sum contributes -/

/-- The `m`-th summand of `Zeta2L7IdContour.ResidArm_lineA_eq_tsum`, spelled character for
character so that no second copy of the family exists. -/
noncomputable def F (n : ℕ) (m : ℤ) (s : ℝ) : ℂ :=
  ∑ k ∈ candidateM.window n,
    ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
      / ((Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ))
          * (Zeta2L7IdMoment.lineA n s + (m : ℂ)) ^ 2)

/-- The residue mass of the window — the only way the window enters this file at all. -/
noncomputable def C (n : ℕ) : ℝ :=
  ∑ k ∈ candidateM.window n, ‖((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)‖

theorem C_nonneg (n : ℕ) : 0 ≤ C n :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **The pointwise majorant.**  `|t|^{−3}`, with the `k`-factor's `s`-decay KEPT — dropping it
would give `1/|m|` and the summability below would be false. -/
theorem norm_F_le (n : ℕ) (m : ℤ) (s : ℝ) :
    ‖F n m s‖
      ≤ C n * ((s ^ 2 + A n m ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2))⁻¹ := by
  have hA := A_pos n m
  have hroot : (0 : ℝ) < Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  have hden : (0 : ℝ) < (s ^ 2 + A n m ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) := by
    have : (0 : ℝ) < s ^ 2 + A n m ^ 2 := by positivity
    exact mul_pos this hroot
  refine (norm_sum_le _ _).trans ?_
  rw [C, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  set x : ℂ := Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ) with hxdef
  set y : ℂ := Zeta2L7IdMoment.lineA n s + (m : ℂ) with hydef
  have hy2 : ‖y‖ ^ 2 = s ^ 2 + A n m ^ 2 := norm_sq_lineA_add_intCast n m s
  have hxge : Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) ≤ ‖x‖ :=
    sqrt_le_norm_lineA_add_natCast n k s
  have hprod : (s ^ 2 + A n m ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) ≤ ‖x‖ * ‖y‖ ^ 2 := by
    rw [hy2]
    calc (s ^ 2 + A n m ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2)
        = Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) * (s ^ 2 + A n m ^ 2) := by ring
      _ ≤ ‖x‖ * (s ^ 2 + A n m ^ 2) := by
          refine mul_le_mul_of_nonneg_right hxge ?_
          positivity
  have hnorm : ‖((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ) / (x * y ^ 2)‖
      = ‖((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)‖ / (‖x‖ * ‖y‖ ^ 2) := by
    rw [norm_div, norm_mul, norm_pow]
  rw [hnorm]
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Zeta2L7Id0Val.inv_le_inv_of_le' hden hprod

/-! ## §3. The scale-`a` majorant — `Zeta2L7Id0Val`'s estimate, freed of its `A`

At `n = 0` the pointwise majorant was stated only at `a = A m`.  Everything it proves is true at
any positive scale, and this file needs it at `a = A n m` for a DIFFERENT `A`, so the statement
is generalised once here rather than instantiated twice. -/

/-- `1/((s²+a²)√(s²+¼)) ≤ (k/2)(a²)⁻¹(s²+¼)⁻¹ + (k⁻¹/2)(s²+a²)⁻¹` — AM-GM on the square root,
then `s² + ¼ ≥ ¼` is NOT used: what is used is `s² + a² ≥ a²`. -/
theorem inv_prod_le {a : ℝ} (ha : 0 < a) {k : ℝ} (hk : 0 < k) (s : ℝ) :
    ((s ^ 2 + a ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2))⁻¹
      ≤ k / 2 * (a ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ + k⁻¹ / 2 * (s ^ 2 + a ^ 2)⁻¹ := by
  have hX : (0 : ℝ) < s ^ 2 + (1 / 2 : ℝ) ^ 2 := by positivity
  have hYa : a ^ 2 ≤ s ^ 2 + a ^ 2 := by nlinarith [sq_nonneg s]
  rw [mul_inv]
  calc (s ^ 2 + a ^ 2)⁻¹ * (Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2))⁻¹
      ≤ (s ^ 2 + a ^ 2)⁻¹ * (k / 2 * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ + k⁻¹ / 2) :=
        mul_le_mul_of_nonneg_left (Zeta2L7Id0Val.amgm_inv_sqrt hX hk) (by positivity)
    _ = k / 2 * ((s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ * (s ^ 2 + a ^ 2)⁻¹)
        + k⁻¹ / 2 * (s ^ 2 + a ^ 2)⁻¹ := by ring
    _ ≤ k / 2 * ((a ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹)
        + k⁻¹ / 2 * (s ^ 2 + a ^ 2)⁻¹ := by
        have hinner : (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ * (s ^ 2 + a ^ 2)⁻¹
            ≤ (a ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ :=
          calc (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ * (s ^ 2 + a ^ 2)⁻¹
              ≤ (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ * (a ^ 2)⁻¹ :=
                mul_le_mul_of_nonneg_left
                  (Zeta2L7Id0Val.inv_le_inv_of_le' (by positivity) hYa) (by positivity)
            _ = (a ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ := mul_comm _ _
        exact add_le_add (mul_le_mul_of_nonneg_left hinner (by positivity)) le_rfl
    _ = k / 2 * (a ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹
        + k⁻¹ / 2 * (s ^ 2 + a ^ 2)⁻¹ := by ring

theorem integrable_maj {a : ℝ} (ha : 0 < a) (k : ℝ) :
    Integrable (fun s : ℝ => k / 2 * (a ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹
      + k⁻¹ / 2 * (s ^ 2 + a ^ 2)⁻¹) :=
  ((integrable_inv_sq_add_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _).add
    ((integrable_inv_sq_add_sq ha).const_mul _)

theorem integral_maj {a : ℝ} (ha : 0 < a) (k : ℝ) :
    ∫ s : ℝ, (k / 2 * (a ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹
      + k⁻¹ / 2 * (s ^ 2 + a ^ 2)⁻¹)
      = k / 2 * (a ^ 2)⁻¹ * (Real.pi / (1 / 2)) + k⁻¹ / 2 * (Real.pi / a) := by
  rw [integral_add ((integrable_inv_sq_add_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _)
      ((integrable_inv_sq_add_sq ha).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_inv_sq_add_sq (by norm_num : (0 : ℝ) < 1 / 2), integral_inv_sq_add_sq ha]

/-- The majorant's integral AT the balancing `k = √a` is exactly `3π/2 · a^{−3/2}` — an
EQUALITY, isolated so that both consumers below use the same arithmetic. -/
theorem maj_value_at_sqrt {a : ℝ} (ha : 0 < a) :
    Real.sqrt a / 2 * (a ^ 2)⁻¹ * (Real.pi / (1 / 2)) + (Real.sqrt a)⁻¹ / 2 * (Real.pi / a)
      = 3 * Real.pi / 2 / (a * Real.sqrt a) := by
  -- `set` FIRST: without it, `rw [← ht2]` rewrites the `a` INSIDE `Real.sqrt a` too and leaves
  -- `√(√a ^ 2)`, which `ring` cannot close.  (Measured on this file's first elaboration.)
  set t : ℝ := Real.sqrt a with htdef
  have ht : 0 < t := Real.sqrt_pos.mpr ha
  have ht2 : t ^ 2 = a := Real.sq_sqrt ha.le
  rw [← ht2]
  field_simp
  ring

/-- **The `a^{−3/2}` bound at the balancing `k = √a`.** -/
theorem integral_inv_prod_le {a : ℝ} (ha : 0 < a) :
    ∫ s : ℝ, ((s ^ 2 + a ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2))⁻¹
      ≤ 3 * Real.pi / 2 / (a * Real.sqrt a) := by
  have ht : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hb := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun s : ℝ => by positivity :
      ∀ s : ℝ, (0 : ℝ) ≤ ((s ^ 2 + a ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2))⁻¹))
    (integrable_maj ha (Real.sqrt a))
    (Filter.Eventually.of_forall (fun s => inv_prod_le ha ht s))
  rw [integral_maj ha (Real.sqrt a)] at hb
  exact hb.trans (le_of_eq (maj_value_at_sqrt ha))

/-! ## §4. Hypothesis (a): every `F n m` is integrable on the line -/

theorem continuous_F (n : ℕ) (m : ℤ) : Continuous (F n m) := by
  -- `continuous_finset_sum` is DEPRECATED at this pin; `continuous_finsetSum` is the name.
  refine continuous_finsetSum _ fun k _ => ?_
  refine Continuous.div continuous_const ?_ (fun s => ?_)
  · exact ((Zeta2L7IdContour.continuous_lineA n).add continuous_const).mul
      (((Zeta2L7IdContour.continuous_lineA n).add continuous_const).pow 2)
  · rw [lineA_add_natCast, lineA_add_intCast]
    refine mul_ne_zero (lin_ne_zero ?_ s) (pow_ne_zero 2 (lin_ne_zero ?_ s))
    · intro h
      have := half_le_abs_offN n k
      rw [h, abs_zero] at this
      linarith
    · have hA := A_pos n m
      rw [A_eq_abs_offZ] at hA
      exact fun h => by simp [h] at hA

theorem integrable_maj_scaled (n : ℕ) (m : ℤ) (k : ℝ) :
    Integrable (fun s : ℝ => C n * (k / 2 * (A n m ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹
      + k⁻¹ / 2 * (s ^ 2 + A n m ^ 2)⁻¹)) :=
  (integrable_maj (A_pos n m) k).const_mul _

/-- **HYPOTHESIS (a).**  Each `F n m` is integrable — dominated by the `k = 1` majorant. -/
theorem integrable_F (n : ℕ) (m : ℤ) : Integrable (F n m) := by
  refine (integrable_maj_scaled n m 1).mono' (continuous_F n m).aestronglyMeasurable ?_
  filter_upwards with s
  refine (norm_F_le n m s).trans ?_
  exact mul_le_mul_of_nonneg_left (inv_prod_le (A_pos n m) one_pos s) (C_nonneg n)

/-! ## §5. Hypothesis (b): `Σ_m ∫‖F_m‖ < ∞` — the obligation the row's cell called "the work" -/

theorem integral_norm_F_le (n : ℕ) (m : ℤ) :
    ∫ s : ℝ, ‖F n m s‖ ≤ C n * (3 * Real.pi / 2 / (A n m * Real.sqrt (A n m))) := by
  have hA := A_pos n m
  have hstep := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun s => norm_nonneg (F n m s)))
    (((integrable_maj hA (Real.sqrt (A n m))).const_mul (C n)))
    (Filter.Eventually.of_forall (fun s =>
      (norm_F_le n m s).trans
        (mul_le_mul_of_nonneg_left
          (inv_prod_le hA (Real.sqrt_pos.mpr hA) s) (C_nonneg n))))
  refine hstep.trans ?_
  rw [integral_const_mul, integral_maj hA (Real.sqrt (A n m))]
  exact mul_le_mul_of_nonneg_left (le_of_eq (maj_value_at_sqrt hA)) (C_nonneg n)

/-- The summable majorant, reindexed: `A n m` is `Zeta2L7Id0Val.A (m − 4n)`, so the `n = 0`
file's two shifted `|·|^{−3/2}` families are pulled back along `m ↦ m − 4n`, which is injective.
-/
theorem summable_shifted (n : ℕ) :
    Summable (fun m : ℤ => 1 / (|((m - 4 * (n : ℤ) : ℤ) : ℝ)| *
        Real.sqrt |((m - 4 * (n : ℤ) : ℤ) : ℝ)|)
      + 1 / (|((m - 4 * (n : ℤ) : ℤ) : ℝ) - 1| *
          Real.sqrt |((m - 4 * (n : ℤ) : ℤ) : ℝ) - 1|)) := by
  have hinj : Function.Injective (fun m : ℤ => m - 4 * (n : ℤ)) := by
    intro a b hab
    simp only at hab
    omega
  exact (Zeta2L7Id0Val.summable_w.add Zeta2L7Id0Val.summable_w_shift).comp_injective hinj

/-- **HYPOTHESIS (b).**  `Σ_m ∫‖F n m‖ < ∞`. -/
theorem summable_integral_norm (n : ℕ) :
    Summable (fun m : ℤ => ∫ s : ℝ, ‖F n m s‖) := by
  refine Summable.of_nonneg_of_le
    (fun m => integral_nonneg (fun s => norm_nonneg (F n m s)))
    (fun m => (integral_norm_F_le n m).trans ?_)
    (((summable_shifted n).mul_left (6 * Real.pi)).mul_left (C n))
  refine mul_le_mul_of_nonneg_left ?_ (C_nonneg n)
  exact (Zeta2L7Id0Val.maj_le (m - 4 * (n : ℤ)))

/-! ## §6. THE INTERCHANGE, executed -/

/-- **ROW L7ID'S THIRD OBLIGATION, DISCHARGED AT EVERY `n`.**  The RESID arm's line integral over
the cell contour IS the sum of its terms' line integrals. -/
theorem integral_ResidArm_lineA (n : ℕ) :
    (∫ s : ℝ, Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s))
      = ∑' m : ℤ, ∫ s : ℝ, F n m s := by
  have hae : (fun s : ℝ => Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s))
      =ᵐ[volume] (fun s : ℝ => ∑' m : ℤ, F n m s) := by
    filter_upwards [Zeta2L7IdHinge.ae_ne_zero] with s hs
    rw [Zeta2L7IdContour.ResidArm_lineA_eq_tsum n hs]
    rfl
  rw [integral_congr_ae hae]
  exact (integral_tsum_of_summable_integral_norm (integrable_F n)
    (summable_integral_norm n)).symm

end Zeta2L7IdResid

/-! ## RECEIPTS — the footprint AND the type, for every theorem (LEAN.md §1). -/

#print axioms Zeta2L7IdResid.lineA_add_natCast
#check @Zeta2L7IdResid.lineA_add_natCast
#print axioms Zeta2L7IdResid.lineA_add_intCast
#check @Zeta2L7IdResid.lineA_add_intCast
#print axioms Zeta2L7IdResid.half_le_abs_sub_half
#check @Zeta2L7IdResid.half_le_abs_sub_half
#print axioms Zeta2L7IdResid.half_le_abs_offN
#check @Zeta2L7IdResid.half_le_abs_offN
#print axioms Zeta2L7IdResid.A_eq_abs_offZ
#check @Zeta2L7IdResid.A_eq_abs_offZ
#print axioms Zeta2L7IdResid.A_pos
#check @Zeta2L7IdResid.A_pos
#print axioms Zeta2L7IdResid.norm_sq_lineA_add_intCast
#check @Zeta2L7IdResid.norm_sq_lineA_add_intCast
#print axioms Zeta2L7IdResid.sqrt_le_norm_lineA_add_natCast
#check @Zeta2L7IdResid.sqrt_le_norm_lineA_add_natCast
#print axioms Zeta2L7IdResid.C_nonneg
#check @Zeta2L7IdResid.C_nonneg
#print axioms Zeta2L7IdResid.norm_F_le
#check @Zeta2L7IdResid.norm_F_le
#print axioms Zeta2L7IdResid.inv_prod_le
#check @Zeta2L7IdResid.inv_prod_le
#print axioms Zeta2L7IdResid.integrable_maj
#check @Zeta2L7IdResid.integrable_maj
#print axioms Zeta2L7IdResid.integral_maj
#check @Zeta2L7IdResid.integral_maj
#print axioms Zeta2L7IdResid.integral_inv_prod_le
#check @Zeta2L7IdResid.integral_inv_prod_le
#print axioms Zeta2L7IdResid.continuous_F
#check @Zeta2L7IdResid.continuous_F
#print axioms Zeta2L7IdResid.integrable_F
#check @Zeta2L7IdResid.integrable_F
#print axioms Zeta2L7IdResid.integral_norm_F_le
#check @Zeta2L7IdResid.integral_norm_F_le
#print axioms Zeta2L7IdResid.summable_shifted
#check @Zeta2L7IdResid.summable_shifted
#print axioms Zeta2L7IdResid.summable_integral_norm
#check @Zeta2L7IdResid.summable_integral_norm
#print axioms Zeta2L7IdResid.integral_ResidArm_lineA
#check @Zeta2L7IdResid.integral_ResidArm_lineA
