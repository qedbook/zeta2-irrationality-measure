/-
# Row L7ID-0, the VALUE half — pieces (b), (c), (d), (e), and the row's target

`docs/future/zeta2-lean-chain.md` row **L7ID-0**.  The SHAPE half is `Zeta2L7Id0.lean` (the
contour at `n = 0`, the kernel collapse, `rn 0 = −ζ(2)`, and `row_target_is_false`); piece (a)
of the VALUE half is `Zeta2L7LineInt.lean` (the per-`m` line integral and its sign).  THIS file
is the rest of the value half and the row's target theorem:

    theorem rn_eq_neg_rLine_zero : candidateM.rn 0 = -L7MidM5.rLine 0

**Headline: `Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.**  This file
closes ONE row of the chain and moves no other row's grade.

The four pieces the cell named, and what each turned out to be:

* **(b) the hinge off `ℍₒ`.**  `Zeta2MB.pi_sq_div_sin_sq_eq_tsum` needs `z ∈ ℍₒ`, while the
  contour `−½ + is` has `Im = s` and runs over ALL of `ℝ`.  The cell priced a CONJUGATION
  extension (`Complex.sin_conj`, `integral_conj`, …).  **That is not the cheapest route and one
  of its four named lemmas does not exist**: `MeasureTheory.integral_conj` is an unknown
  identifier at this pin (measured, this file's `Names` section records the two that do exist).
  What replaces it is a REINDEXING symmetry, `§1`: both sides of the hinge are EVEN in `s` on
  this contour — the left because `sin(π(−½+is)) = −cosh(πs)` (`Zeta2L7Id0.sin_pi_lineB_zero`)
  and `cosh` is even, the right because `m ↦ 1 − m` is an involution of `ℤ` carrying the `s`
  term to the `−s` term EXACTLY (`lineB 0 (−s) + (1−m) = −(lineB 0 s + m)`, and the square kills
  the sign).  So `s < 0` follows from `s > 0` with no conjugation and no `starRingEnd`.
* **(c) the summability.**  `∑_m ∫‖·‖` really is the row's analytic price.  `§4`.
* **(d) integrability at `n = 0` from scratch.**  Every M4/M5 support lemma is gated `1 ≤ n`, so
  none applies.  It is NOT, however, integrability of `H₀ ∘ lineB 0` that this route needs:
  `integral_tsum_of_summable_integral_norm` asks for integrability of each TERM, and the value
  comes out as a complex equation, so the `Complex.re`-through-an-integral step the cell priced
  (and `Zeta2L7Id0.rLine_zero_nonneg` paid for) is never taken here.  `§3`.
* **(e) the `m = 1` triple pole.**  `a = b = ½`, outside `integral_line_two_pole`'s shape.  It
  is `(½+is)⁻³` and it integrates to `0`, by piece (a)'s antiderivative pattern one power up.
  `§2`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib
import Zeta2Defs
import Zeta2Hat
import L7MidM5
import Zeta2SinSqSeries
import Zeta2L7LineInt
import Zeta2L7Id0

open MeasureTheory Complex Filter Topology

set_option maxHeartbeats 1000000

namespace Zeta2L7Id0Val

open Zeta2L7LineInt

/-! ## §0. The contour at `n = 0`, in `Zeta2L7LineInt`'s vocabulary

`lineB 0 s = −½ + is`, so `lineB 0 s + m = lin (m − ½) s` and `lineB 0 s + 1 = lin ½ s`.  These
two rewrites are what let piece (a)'s per-`m` integrals be consumed verbatim. -/

theorem lineB_add_intCast (m : ℤ) (s : ℝ) :
    L7MidM5.lineB 0 s + (m : ℂ) = lin ((m : ℝ) - 1 / 2) s := by
  rw [Zeta2L7Id0.lineB_zero, lin]
  push_cast
  ring

theorem lineB_add_one (s : ℝ) : L7MidM5.lineB 0 s + 1 = lin (1 / 2) s := by
  rw [Zeta2L7Id0.lineB_zero, lin]
  push_cast
  ring

theorem lineB_neg_add (m : ℤ) (s : ℝ) :
    L7MidM5.lineB 0 (-s) + ((1 - m : ℤ) : ℂ) = -(L7MidM5.lineB 0 s + (m : ℂ)) := by
  rw [Zeta2L7Id0.lineB_zero, Zeta2L7Id0.lineB_zero]
  push_cast
  ring

/-- The hinge's `m`-th term on this row's contour: `a = m − ½` against `b = ½`. -/
noncomputable def term (m : ℤ) (s : ℝ) : ℂ :=
  ((lin ((m : ℝ) - 1 / 2) s) ^ 2 * lin (1 / 2) s)⁻¹

/-- `m − ½` is never `0`: `m` is an integer.  (LEAN.md §5 — the edge the whole family rests on,
recorded as a theorem rather than as a remark.) -/
theorem half_ne (m : ℤ) : ((m : ℝ) - 1 / 2) ≠ 0 := by
  intro h
  have h2 : (2 * m : ℤ) = 1 := by
    have hr : (2 : ℝ) * (m : ℝ) = 1 := by linarith
    exact_mod_cast hr
  omega

/-- `A m = |m − ½|`, the distance from the `m`-th pole to the contour. -/
noncomputable def A (m : ℤ) : ℝ := |(m : ℝ) - 1 / 2|

theorem A_pos (m : ℤ) : 0 < A m := abs_pos.mpr (half_ne m)

/-! ## §1. PIECE (b) — the hinge, off the upper half-plane

`Zeta2MB.pi_sq_div_sin_sq_eq_tsum` is stated on `ℍₒ`.  The contour meets `ℍₒ` only for `s > 0`.
Both sides are even in `s`, so `s < 0` is free; `s = 0` is a single point and every consumer
below is `ae`. -/

/-- The kernel's series side, as a function of the ordinate. -/
noncomputable def kern (s : ℝ) : ℂ := ∑' m : ℤ, 1 / (L7MidM5.lineB 0 s + (m : ℂ)) ^ 2

/-- **The reindexing symmetry.**  `m ↦ 1 − m` is an involution of `ℤ` and it carries the `−s`
term to the `s` term exactly: `lineB 0 (−s) + (1 − m) = −(lineB 0 s + m)`, whose square is the
same.  This is what replaces the cell's conjugation route. -/
theorem kern_neg (s : ℝ) : kern (-s) = kern s := by
  have h := (Equiv.subLeft (1 : ℤ)).tsum_eq
    (fun m : ℤ => 1 / (L7MidM5.lineB 0 (-s) + (m : ℂ)) ^ 2)
  rw [kern, kern, ← h]
  refine tsum_congr (fun m => ?_)
  have : L7MidM5.lineB 0 (-s) + (((Equiv.subLeft (1 : ℤ)) m : ℤ) : ℂ)
      = -(L7MidM5.lineB 0 s + (m : ℂ)) := by
    simpa using lineB_neg_add m s
  rw [this, neg_pow]
  norm_num

/-- The hinge's LEFT side is even in `s`, because `sin(π(−½+is)) = −cosh(πs)` and `cosh` is
even.  (The minus is squared away here — but it is the same minus `Zeta2L7Id0` measures.) -/
theorem sin_sq_lineB_neg (s : ℝ) :
    Complex.sin ((Real.pi : ℂ) * L7MidM5.lineB 0 (-s)) ^ 2
      = Complex.sin ((Real.pi : ℂ) * L7MidM5.lineB 0 s) ^ 2 := by
  rw [Zeta2L7Id0.sin_pi_lineB_zero, Zeta2L7Id0.sin_pi_lineB_zero,
    show Real.pi * (-s) = -(Real.pi * s) by ring, Real.cosh_neg]

/-- **PIECE (b).**  The hinge on the WHOLE contour off the real axis — `s > 0` from Mathlib,
`s < 0` from the two evenness lemmas above, and `s = 0` excluded (it is the one point of the
contour on the real axis, and it is `volume`-null). -/
theorem hinge_on_lineB {s : ℝ} (hs : s ≠ 0) :
    ((Real.pi : ℂ)) ^ 2 / Complex.sin ((Real.pi : ℂ) * L7MidM5.lineB 0 s) ^ 2 = kern s := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have hup : L7MidM5.lineB 0 (-s) ∈ UpperHalfPlane.upperHalfPlaneSet := by
      show 0 < (L7MidM5.lineB 0 (-s)).im
      rw [Zeta2L7Id0.lineB_zero]
      simpa using (neg_pos.mpr hneg)
    have h := Zeta2MB.pi_sq_div_sin_sq_eq_tsum hup
    rw [← sin_sq_lineB_neg s, h, ← kern, kern_neg]
  · have hup : L7MidM5.lineB 0 s ∈ UpperHalfPlane.upperHalfPlaneSet := by
      show 0 < (L7MidM5.lineB 0 s).im
      rw [Zeta2L7Id0.lineB_zero]
      simpa using hpos
    exact Zeta2MB.pi_sq_div_sin_sq_eq_tsum hup

/-! ## §2. PIECE (e) — the `m = 1` triple pole

The hinge's `m`-th term on this contour has `a = m − ½` against `b = ½`, so `m = 1` is the one
index with `a = b`: the term is `(½+is)⁻³`, outside `integral_line_two_pole`'s shape.  It
integrates to `0` on the same antiderivative pattern piece (a) used for the double pole, one
power up: `i(a+is)⁻²/2`. -/

theorem norm_lin_ge (a s : ℝ) : |a| ≤ ‖lin a s‖ := by
  have h := Complex.abs_re_le_norm (lin a s)
  rwa [lin_re] at h

theorem integrable_inv_lin_cube {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun s : ℝ => ((lin a s) ^ 3)⁻¹) := by
  have habs : (0 : ℝ) < |a| := abs_pos.mpr ha
  have hcont : Continuous (fun s : ℝ => ((lin a s) ^ 3)⁻¹) :=
    Continuous.inv₀ ((continuous_lin a).pow 3) (fun s => pow_ne_zero 3 (lin_ne_zero ha s))
  refine ((integrable_inv_sq_add_sq habs).const_mul (1 / |a|)).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with s
  have hge := norm_lin_ge a s
  have hn : (0 : ℝ) < ‖lin a s‖ := lt_of_lt_of_le habs hge
  have hsq : ‖lin a s‖ ^ 2 = s ^ 2 + |a| ^ 2 := by rw [norm_sq_lin, sq_abs]
  have hprod : |a| * ‖lin a s‖ ^ 2 ≤ ‖lin a s‖ ^ 3 :=
    calc |a| * ‖lin a s‖ ^ 2 ≤ ‖lin a s‖ * ‖lin a s‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hge (sq_nonneg _)
      _ = ‖lin a s‖ ^ 3 := by ring
  calc ‖((lin a s) ^ 3)⁻¹‖ = 1 / ‖lin a s‖ ^ 3 := by rw [norm_inv, norm_pow, one_div]
    _ ≤ 1 / (|a| * ‖lin a s‖ ^ 2) := one_div_le_one_div_of_le (by positivity) hprod
    _ = 1 / |a| * (s ^ 2 + |a| ^ 2)⁻¹ := by
        rw [hsq]
        field_simp

theorem tendsto_inv_lin_sq (a : ℝ) (l : Filter ℝ)
    (hl : Tendsto (fun s : ℝ => ‖lin a s‖) l atTop) :
    Tendsto (fun s : ℝ => (Complex.I / 2) * ((lin a s) ^ 2)⁻¹) l (nhds 0) := by
  have h0 : Tendsto (fun s : ℝ => (Complex.I * (lin a s)⁻¹) ^ 2) l (nhds 0) := by
    simpa using (tendsto_inv_lin a l hl).pow 2
  have h1 := h0.const_mul (-(Complex.I / 2))
  rw [mul_zero] at h1
  refine h1.congr (fun s => ?_)
  rw [mul_pow, Complex.I_sq, inv_pow]
  ring

/-- **PIECE (e).**  `∫_ℝ (a+is)⁻³ ds = 0` for every `a ≠ 0` — exact antiderivative
`i(a+is)⁻²/2`, vanishing at both ends. -/
theorem integral_inv_lin_cube {a : ℝ} (ha : a ≠ 0) :
    ∫ s : ℝ, ((lin a s) ^ 3)⁻¹ = 0 := by
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => (Complex.I / 2) * ((lin a s) ^ 2)⁻¹) (((lin a s) ^ 3)⁻¹) s := by
    intro s
    have hne : (lin a s) ^ 2 ≠ 0 := pow_ne_zero 2 (lin_ne_zero ha s)
    have hp : HasDerivAt (fun s : ℝ => (lin a s) ^ 2)
        (2 * (lin a s) ^ 1 * Complex.I) s := (hasDerivAt_lin a s).pow 2
    have h := (hp.inv hne).const_mul (Complex.I / 2)
    have hcoef : (Complex.I / 2) * (-(2 * (lin a s) ^ 1 * Complex.I) / ((lin a s) ^ 2) ^ 2)
        = ((lin a s) ^ 3)⁻¹ := by
      have hl : lin a s ≠ 0 := lin_ne_zero ha s
      rw [show ((lin a s) ^ 2) ^ 2 = (lin a s) ^ 4 from by ring]
      rw [show (Complex.I / 2) * (-(2 * (lin a s) ^ 1 * Complex.I) / (lin a s) ^ 4)
            = (-(Complex.I ^ 2)) * (lin a s / (lin a s) ^ 4) from by ring,
        Complex.I_sq, neg_neg, one_mul]
      field_simp
    rwa [hcoef] at h
  have h := integral_of_hasDerivAt_of_tendsto hderiv (integrable_inv_lin_cube ha)
    (tendsto_inv_lin_sq a atBot (tendsto_norm_lin_atBot a))
    (tendsto_inv_lin_sq a atTop (tendsto_norm_lin_atTop a))
  simpa using h

/-- The hinge's `m = 1` term on this row's own contour: `a = b = ½`, the triple pole, `0`. -/
theorem integral_term_one : ∫ s : ℝ, term 1 s = 0 := by
  have hcube : ∀ s : ℝ, term 1 s = ((lin (1 / 2 : ℝ) s) ^ 3)⁻¹ := by
    intro s
    rw [term, show (((1 : ℤ) : ℝ) - 1 / 2) = 1 / 2 from by norm_num, ← pow_succ]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcube)]
  exact integral_inv_lin_cube (by norm_num)

/-! ## §3. PIECE (d) — the family, its norm, and integrability at `n = 0` from scratch

Nothing in M4/M5 is available here: `L7MidM5.integrable_Hn_lineB`, `norm_Hn_lineB_le`,
`norm_rIntC_le` and `lineB_eq_contourB` are all gated `1 ≤ n`.  What the route actually needs,
though, is NOT integrability of `H₀ ∘ lineB 0` — `integral_tsum_of_summable_integral_norm` asks
for integrability of each TERM, and the value it produces is a complex equation, so the
`Complex.re`-through-an-integral step (no named Mathlib lemma; three lines and an `Integrable`
hypothesis) is never taken.  That is the cell's piece (d), and it is cheaper than the cell
priced it BECAUSE the route changed, not because the estimate was wrong. -/

theorem norm_term (m : ℤ) (s : ℝ) :
    ‖term m s‖ = ((s ^ 2 + A m ^ 2) * Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2))⁻¹ := by
  have hb : ‖lin (1 / 2 : ℝ) s‖ = Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) := by
    rw [← norm_sq_lin (1 / 2 : ℝ) s, Real.sqrt_sq (norm_nonneg _)]
  rw [term, norm_inv, norm_mul, norm_pow, norm_sq_lin, hb, A, sq_abs]

/-- `1/√X ≤ k/(2X) + 1/(2k)` — AM-GM on `√(1/X) = √((k/X)·(1/k))`, the one inequality that
turns the `|t+1|⁻¹` factor's square root into two Cauchy kernels.  The free `k` is what buys the
`|m|^{−3/2}` decay: at `k = √|a|` the two halves balance. -/
theorem amgm_inv_sqrt {X k : ℝ} (hX : 0 < X) (hk : 0 < k) :
    (Real.sqrt X)⁻¹ ≤ k / 2 * X⁻¹ + k⁻¹ / 2 := by
  obtain ⟨r, hr0, rfl⟩ : ∃ r : ℝ, 0 < r ∧ X = r ^ 2 :=
    ⟨Real.sqrt X, Real.sqrt_pos.mpr hX, (Real.sq_sqrt hX.le).symm⟩
  rw [Real.sqrt_sq hr0.le, ← sub_nonneg]
  have hid : k / 2 * (r ^ 2)⁻¹ + k⁻¹ / 2 - r⁻¹ = (k - r) ^ 2 / (2 * k * r ^ 2) := by
    field_simp
    ring
  rw [hid]
  positivity

theorem inv_le_inv_of_le' {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : y⁻¹ ≤ x⁻¹ := by
  rw [← one_div, ← one_div]
  exact one_div_le_one_div_of_le hx hxy

/-- The pointwise majorant: two Cauchy kernels, one at scale `½` and one at scale `|m − ½|`. -/
theorem norm_term_le (m : ℤ) {k : ℝ} (hk : 0 < k) (s : ℝ) :
    ‖term m s‖ ≤ k / 2 * (A m ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹
      + k⁻¹ / 2 * (s ^ 2 + A m ^ 2)⁻¹ := by
  have hA := A_pos m
  have hX : (0 : ℝ) < s ^ 2 + (1 / 2 : ℝ) ^ 2 := by positivity
  have hYa : A m ^ 2 ≤ s ^ 2 + A m ^ 2 := by nlinarith [sq_nonneg s]
  rw [norm_term, mul_inv]
  calc (s ^ 2 + A m ^ 2)⁻¹ * (Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2))⁻¹
      ≤ (s ^ 2 + A m ^ 2)⁻¹ * (k / 2 * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ + k⁻¹ / 2) :=
        mul_le_mul_of_nonneg_left (amgm_inv_sqrt hX hk) (by positivity)
    _ = k / 2 * ((s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ * (s ^ 2 + A m ^ 2)⁻¹)
        + k⁻¹ / 2 * (s ^ 2 + A m ^ 2)⁻¹ := by ring
    _ ≤ k / 2 * ((A m ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹)
        + k⁻¹ / 2 * (s ^ 2 + A m ^ 2)⁻¹ := by
        have hinner : (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ * (s ^ 2 + A m ^ 2)⁻¹
            ≤ (A m ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ :=
          calc (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ * (s ^ 2 + A m ^ 2)⁻¹
              ≤ (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ * (A m ^ 2)⁻¹ :=
                mul_le_mul_of_nonneg_left (inv_le_inv_of_le' (by positivity) hYa)
                  (by positivity)
            _ = (A m ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹ := mul_comm _ _
        have hk2 : (0 : ℝ) ≤ k / 2 := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hinner hk2) le_rfl
    _ = k / 2 * (A m ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹
        + k⁻¹ / 2 * (s ^ 2 + A m ^ 2)⁻¹ := by ring

theorem integrable_majorant (m : ℤ) (k : ℝ) :
    Integrable (fun s : ℝ => k / 2 * (A m ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹
      + k⁻¹ / 2 * (s ^ 2 + A m ^ 2)⁻¹) :=
  ((integrable_inv_sq_add_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _).add
    ((integrable_inv_sq_add_sq (A_pos m)).const_mul _)

theorem continuous_term (m : ℤ) : Continuous (term m) := by
  refine Continuous.inv₀ (((continuous_lin _).pow 2).mul (continuous_lin _)) (fun s => ?_)
  exact mul_ne_zero (pow_ne_zero 2 (lin_ne_zero (half_ne m) s))
    (lin_ne_zero (by norm_num) s)

/-- **PIECE (d).**  Each term is integrable — dominated by the `k = 1` majorant. -/
theorem integrable_term (m : ℤ) : Integrable (term m) := by
  refine (integrable_majorant m 1).mono' (continuous_term m).aestronglyMeasurable ?_
  filter_upwards with s
  exact norm_term_le m one_pos s

/-! ## §4. PIECE (c) — the summability

`∫‖term m‖ ≲ |m|^{−3/2}`, which is where the free `k` of `amgm_inv_sqrt` is spent: `k = √|a|`
balances `πk/a²` against `π/(2k|a|)`.  The true size is `log|a|/a²` and `3/2` is a deliberate
under-estimate — it is summable, which is all `integral_tsum_of_summable_integral_norm` wants,
and it costs no logarithm. -/

theorem integral_majorant (m : ℤ) (k : ℝ) :
    ∫ s : ℝ, (k / 2 * (A m ^ 2)⁻¹ * (s ^ 2 + (1 / 2 : ℝ) ^ 2)⁻¹
      + k⁻¹ / 2 * (s ^ 2 + A m ^ 2)⁻¹)
      = k / 2 * (A m ^ 2)⁻¹ * (Real.pi / (1 / 2)) + k⁻¹ / 2 * (Real.pi / A m) := by
  rw [integral_add ((integrable_inv_sq_add_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _)
      ((integrable_inv_sq_add_sq (A_pos m)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_inv_sq_add_sq (by norm_num : (0 : ℝ) < 1 / 2), integral_inv_sq_add_sq (A_pos m)]

/-- **The `|m|^{−3/2}` bound**, at the balancing `k = √|m − ½|`. -/
theorem integral_norm_term_le (m : ℤ) :
    ∫ s : ℝ, ‖term m s‖ ≤ 3 * Real.pi / 2 / (A m * Real.sqrt (A m)) := by
  have hA := A_pos m
  set t : ℝ := Real.sqrt (A m) with htdef
  have ht : 0 < t := Real.sqrt_pos.mpr hA
  have ht2 : t ^ 2 = A m := Real.sq_sqrt hA.le
  have hb := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun s => norm_nonneg (term m s)))
    (integrable_majorant m t) (Filter.Eventually.of_forall (norm_term_le m ht))
  rw [integral_majorant m t] at hb
  refine hb.trans (le_of_eq ?_)
  rw [← ht2]
  field_simp
  ring

/-- `x ≥ u/2 > 0 ⟹ 1/(x√x) ≤ 4/(u√u)`.  The `4` is slack (`2√2 ≈ 2.83` is sharp); a constant
that clears with room survives a re-derivation, and the sharp one buys nothing here. -/
theorem w_mono {x u : ℝ} (hu : 0 < u) (h : u / 2 ≤ x) :
    1 / (x * Real.sqrt x) ≤ 4 / (u * Real.sqrt u) := by
  have hx : 0 < x := lt_of_lt_of_le (by linarith) h
  have hp : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hq : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hp2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hq2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hle : Real.sqrt u ≤ 3 / 2 * Real.sqrt x := by
    have h1 : u ≤ 9 / 4 * x := by linarith
    have h2 : Real.sqrt u ≤ Real.sqrt (9 / 4 * x) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 / 4),
      show Real.sqrt (9 / 4 : ℝ) = 3 / 2 from by
        rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]] at h2
  have hcube : Real.sqrt u ^ 3 ≤ 4 * Real.sqrt x ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (mul_nonneg hq.le hq.le),
      mul_nonneg (sub_nonneg.mpr hle) (mul_nonneg hp.le hq.le),
      mul_nonneg (sub_nonneg.mpr hle) (mul_nonneg hp.le hp.le),
      pow_nonneg hp.le 3]
  have hkey : u * Real.sqrt u / 4 ≤ x * Real.sqrt x := by
    have e1 : u * Real.sqrt u = Real.sqrt u ^ 3 := by
      rw [show Real.sqrt u ^ 3 = Real.sqrt u ^ 2 * Real.sqrt u from by ring, hq2]
    have e2 : x * Real.sqrt x = Real.sqrt x ^ 3 := by
      rw [show Real.sqrt x ^ 3 = Real.sqrt x ^ 2 * Real.sqrt x from by ring, hp2]
    rw [e1, e2]; linarith
  calc 1 / (x * Real.sqrt x) ≤ 1 / (u * Real.sqrt u / 4) :=
        one_div_le_one_div_of_le (by positivity) hkey
    _ = 4 / (u * Real.sqrt u) := by field_simp

/-- `|m − ½| ≥ |m|/2` for `m ≥ 1` and `≥ |m−1|/2` for `m ≤ 0`, so the row's majorant is
dominated by two shifted copies of `|·|^{−3/2}`.  The two-term majorant exists because `|m|` and
`|m−1|` each VANISH at one integer, where `1/(0·√0) = 0` and the comparison would fail. -/
theorem maj_le (m : ℤ) :
    3 * Real.pi / 2 / (A m * Real.sqrt (A m))
      ≤ 6 * Real.pi * (1 / (|(m : ℝ)| * Real.sqrt |(m : ℝ)|)
          + 1 / (|(m : ℝ) - 1| * Real.sqrt |(m : ℝ) - 1|)) := by
  have hpi := Real.pi_pos
  have hstep : ∀ u : ℝ, 0 < u → u / 2 ≤ A m →
      3 * Real.pi / 2 / (A m * Real.sqrt (A m)) ≤ 6 * Real.pi * (1 / (u * Real.sqrt u)) := by
    intro u hu hle
    have h := w_mono hu hle
    have h2 : 3 * Real.pi / 2 * (1 / (A m * Real.sqrt (A m)))
        ≤ 3 * Real.pi / 2 * (4 / (u * Real.sqrt u)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    calc 3 * Real.pi / 2 / (A m * Real.sqrt (A m))
        = 3 * Real.pi / 2 * (1 / (A m * Real.sqrt (A m))) := by ring
      _ ≤ 3 * Real.pi / 2 * (4 / (u * Real.sqrt u)) := h2
      _ = 6 * Real.pi * (1 / (u * Real.sqrt u)) := by ring
  by_cases hm : m ≤ 0
  · have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    have hu : |(m : ℝ) - 1| = 1 - (m : ℝ) := by
      rw [abs_of_nonpos (by linarith)]; ring
    have hAm : A m = 1 / 2 - (m : ℝ) := by
      rw [A, abs_of_nonpos (by linarith)]; ring
    have h := hstep (1 - (m : ℝ)) (by linarith) (by rw [hAm]; linarith)
    rw [← hu] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hnn : 0 ≤ 1 / (|(m : ℝ)| * Real.sqrt |(m : ℝ)|) := by positivity
    linarith
  · have hm1 : (1 : ℤ) ≤ m := by omega
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hu : |(m : ℝ)| = (m : ℝ) := abs_of_pos (by linarith)
    have hAm : A m = (m : ℝ) - 1 / 2 := by
      rw [A, abs_of_pos (by linarith)]
    have h := hstep (m : ℝ) (by linarith) (by rw [hAm]; linarith)
    rw [← hu] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hnn : 0 ≤ 1 / (|(m : ℝ) - 1| * Real.sqrt |(m : ℝ) - 1|) := by positivity
    linarith

/-- `|x|^{−3/2}` in elementary form — and the two agree at `x = 0`, where both are `0` by
Lean's division and `rpow` conventions. -/
theorem rpow_neg_three_halves (x : ℝ) :
    |x| ^ (-(3 / 2) : ℝ) = 1 / (|x| * Real.sqrt |x|) := by
  rcases eq_or_ne x 0 with h | h
  · subst h; simp
  · have hx : 0 < |x| := abs_pos.mpr h
    rw [Real.rpow_neg hx.le, show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num,
      Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]

theorem summable_w : Summable (fun m : ℤ => 1 / (|(m : ℝ)| * Real.sqrt |(m : ℝ)|)) :=
  (Real.summable_abs_int_rpow (b := 3 / 2) (by norm_num)).congr
    (fun m => rpow_neg_three_halves _)

theorem summable_w_shift :
    Summable (fun m : ℤ => 1 / (|(m : ℝ) - 1| * Real.sqrt |(m : ℝ) - 1|)) := by
  have hinj : Function.Injective (fun m : ℤ => m - 1) := by
    intro a b hab
    simp only at hab
    omega
  refine (summable_w.comp_injective hinj).congr (fun m => ?_)
  simp only [Function.comp_apply]
  push_cast
  rfl

/-- **PIECE (c).**  `∑_m ∫‖term m‖ < ∞` — the hypothesis
`integral_tsum_of_summable_integral_norm` asks for. -/
theorem summable_integral_norm : Summable (fun m : ℤ => ∫ s : ℝ, ‖term m s‖) :=
  Summable.of_nonneg_of_le
    (fun m => integral_nonneg (fun s => norm_nonneg (term m s)))
    (fun m => (integral_norm_term_le m).trans (maj_le m))
    ((summable_w.add summable_w_shift).mul_left (6 * Real.pi))

/-! ## §5. The pointwise expansion and the interchange -/

/-- The integrand IS the series, everywhere off the real axis. -/
theorem Hn_zero_eq_tsum {s : ℝ} (hs : s ≠ 0) :
    L7MidM123.Hn 0 (L7MidM5.lineB 0 s) = ∑' m : ℤ, term m s := by
  rw [Zeta2L7Id0.Hn_zero_collapse _ (Zeta2L7Id0.sin_lineB_zero_ne s)
      (Zeta2L7Id0.lineB_zero_add_one_ne s),
    div_mul_eq_div_div_swap, hinge_on_lineB hs, kern, ← tsum_div_const]
  refine tsum_congr (fun m => ?_)
  rw [term, lineB_add_intCast, ← lineB_add_one, div_div, one_div]

theorem ae_ne_zero : ∀ᵐ s : ℝ, s ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simp

/-- **The interchange**, executed. -/
theorem integral_Hn_zero :
    ∫ s : ℝ, L7MidM123.Hn 0 (L7MidM5.lineB 0 s) = ∑' m : ℤ, ∫ s : ℝ, term m s := by
  have hae : (fun s : ℝ => L7MidM123.Hn 0 (L7MidM5.lineB 0 s))
      =ᵐ[volume] (fun s : ℝ => ∑' m : ℤ, term m s) := by
    filter_upwards [ae_ne_zero] with s hs
    exact Hn_zero_eq_tsum hs
  rw [integral_congr_ae hae]
  exact (integral_tsum_of_summable_integral_norm integrable_term summable_integral_norm).symm

/-! ## §6. Summing the per-`m` integrals: `2π·ζ(2)`

`0` for `m ≥ 2` (both poles on one side), `0` for `m = 1` (the triple pole, §2), `2π/(m−1)²`
for `m ≤ 0`.  Reindexed by `k = 1 − m ≥ 0` the family is `2π/k²`, whose `k = 0` entry is `0` by
Lean's division convention — which is exactly the `m = 1` value, so the reindexing needs no
special case. -/

theorem V_ge_two {m : ℤ} (hm : 2 ≤ m) : ∫ s : ℝ, term m s = 0 :=
  integral_term_ge_two hm

theorem V_le_zero {m : ℤ} (hm : m ≤ 0) :
    ∫ s : ℝ, term m s = ((2 * Real.pi / ((m : ℝ) - 1) ^ 2 : ℝ) : ℂ) :=
  integral_term_le_zero hm

theorem V_reindex (k : ℕ) :
    ∫ s : ℝ, term (1 - (k : ℤ)) s = ((2 * Real.pi / (k : ℝ) ^ 2 : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using integral_term_one
  · have hm : (1 : ℤ) - (k : ℤ) ≤ 0 := by omega
    rw [V_le_zero hm]
    congr 2
    push_cast
    ring

theorem hasSum_V :
    HasSum (fun m : ℤ => ∫ s : ℝ, term m s) ((2 * Real.pi * Zeta2Defs.zeta2 : ℝ) : ℂ) := by
  have hinj : Function.Injective (fun k : ℕ => (1 : ℤ) - (k : ℤ)) := by
    intro a b hab
    simp only at hab
    omega
  have hzero : ∀ m ∉ Set.range (fun k : ℕ => (1 : ℤ) - (k : ℤ)),
      (fun m : ℤ => ∫ s : ℝ, term m s) m = 0 := by
    intro m hm
    refine V_ge_two ?_
    by_contra hlt
    refine absurd ?_ hm
    refine ⟨(1 - m).toNat, ?_⟩
    show (1 : ℤ) - (((1 - m).toNat : ℕ) : ℤ) = m
    omega
  refine (Function.Injective.hasSum_iff hinj hzero).mp ?_
  have hreal : HasSum (fun k : ℕ => (2 * Real.pi / (k : ℝ) ^ 2 : ℝ))
      (2 * Real.pi * Zeta2Defs.zeta2) := by
    have h := Zeta2Defs.hasSum_zeta2.mul_left (2 * Real.pi)
    have hf : (fun n : ℕ => 2 * Real.pi * (1 / (n : ℝ) ^ 2))
        = (fun n : ℕ => 2 * Real.pi / (n : ℝ) ^ 2) := by
      funext n; ring
    rwa [hf] at h
  have hcomp : ((fun m : ℤ => ∫ s : ℝ, term m s) ∘ fun k : ℕ => (1 : ℤ) - (k : ℤ))
      = fun k : ℕ => ((2 * Real.pi / (k : ℝ) ^ 2 : ℝ) : ℂ) := by
    funext k
    exact V_reindex k
  rw [hcomp]
  exact Complex.hasSum_ofReal.mpr hreal

/-! ## §7. The row's target

`rIntC 0 = ζ(2)` as a COMPLEX equation — so no `Complex.re`-through-an-integral step is needed,
and `rLine 0 = (rIntC 0).re` is one `Complex.ofReal_re`.  With `Zeta2L7Id0.rn_zero`
(`rₙ 0 = −ζ(2)`) that is the row. -/

theorem rIntC_zero : L7MidM5.rIntC 0 = ((Zeta2Defs.zeta2 : ℝ) : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [L7MidM5.rIntC, integral_Hn_zero, hasSum_V.tsum_eq]
  push_cast
  field_simp

/-- **The VALUE half.**  `rLine 0 = +ζ(2)`. -/
theorem rLine_zero : L7MidM5.rLine 0 = Zeta2Defs.zeta2 := by
  rw [L7MidM5.rLine, rIntC_zero, Complex.ofReal_re]

/-- **ROW L7ID-0.**  `rₙ = −rLine n` at `n = 0`, at `candidateM.rn` itself — the binder shape
`hdecay` consumes (`|Δ n * candidateM.rn n|`), not a restatement.  The minus is the convention
clash between `Zeta2Defs.Member.sgn ≡ −1` and `L7MidM123.Hn`'s `(−1)^(6n+3) ≡ −1`; the row's
PREVIOUS target is machine-checked false in `Zeta2L7Id0.row_target_is_false`. -/
theorem rn_eq_neg_rLine_zero : Zeta2Defs.candidateM.rn 0 = -L7MidM5.rLine 0 := by
  rw [Zeta2L7Id0.rn_zero, rLine_zero]

/-- Composition check (LEAN.md §3): the corrected target and the refuted one are contradictory,
so this file and `Zeta2L7Id0.row_target_is_false` cannot both be vacuous. -/
theorem rLine_zero_pos : 0 < L7MidM5.rLine 0 := by
  rw [rLine_zero, Zeta2Defs.zeta2]
  positivity

/-! ## §9. The names this file resolved against the landed olean

`#check`s, not prose, so a drift fails the elaboration (LEAN.md §2, §8).  The two conjugation
lemmas the cell names and that DO exist are checked here even though §1 uses neither — the
record of the corrected route is the point. -/
section Names
#check @Zeta2MB.pi_sq_div_sin_sq_eq_tsum
#check @Zeta2L7Id0.sin_pi_lineB_zero
#check @Zeta2L7Id0.Hn_zero_collapse
#check @Zeta2L7LineInt.integral_line_two_pole
#check @Zeta2L7LineInt.integral_term_ge_two
#check @Zeta2L7LineInt.integral_term_le_zero
#check @Complex.sin_conj
#check @Complex.conj_conj
#check @MeasureTheory.integral_tsum_of_summable_integral_norm
#check @Real.summable_abs_int_rpow
end Names

end Zeta2L7Id0Val

#print axioms Zeta2L7Id0Val.kern_neg
#print axioms Zeta2L7Id0Val.sin_sq_lineB_neg
#print axioms Zeta2L7Id0Val.hinge_on_lineB
#print axioms Zeta2L7Id0Val.integrable_inv_lin_cube
#print axioms Zeta2L7Id0Val.integral_inv_lin_cube
#print axioms Zeta2L7Id0Val.integral_term_one
#print axioms Zeta2L7Id0Val.norm_term
#print axioms Zeta2L7Id0Val.amgm_inv_sqrt
#print axioms Zeta2L7Id0Val.norm_term_le
#print axioms Zeta2L7Id0Val.integrable_term
#print axioms Zeta2L7Id0Val.integral_norm_term_le
#print axioms Zeta2L7Id0Val.w_mono
#print axioms Zeta2L7Id0Val.maj_le
#print axioms Zeta2L7Id0Val.summable_integral_norm
#print axioms Zeta2L7Id0Val.Hn_zero_eq_tsum
#print axioms Zeta2L7Id0Val.integral_Hn_zero
#print axioms Zeta2L7Id0Val.hasSum_V
#print axioms Zeta2L7Id0Val.rIntC_zero
#print axioms Zeta2L7Id0Val.rLine_zero
#print axioms Zeta2L7Id0Val.rn_eq_neg_rLine_zero
#print axioms Zeta2L7Id0Val.rLine_zero_pos
