/-
# Row L7ID — the off-`ℍₒ` extension of the hinge, at EVERY `n`

Row L7ID-0 closed on 2026-09-19 and its cell records that it is a POOR template for L7ID.  The
first of the five things L7ID does NOT inherit is the one this file discharges.

**What did not transfer.**  `Zeta2L7Id0Val` escaped `Zeta2MB.pi_sq_div_sin_sq_eq_tsum`'s `ℍₒ`
hypothesis by the REINDEXING `m ↦ 1 − m`, which works because

    lineB 0 (−s) + (1 − m) = −(lineB 0 s + m)        EXACTLY.

On `Re t = −σ̃n − ½` the same reflection `m ↦ K − m` asks for `K = 2σ̃n + 1`, and `K` has to be
an INTEGER.  `σ̃ = 58008700/9999999`, so at `n = 1`, `K = 12.6017…`; `l7id_ratfun_check.py`
ARM 6 checks exactly (`Fraction`) that `K ∈ ℤ` at `n = 0` and at no other `n ≤ 40`.  The
reindexing route is an identity of the `n = 0` contour and of nothing else.

**What replaces it.**  POINTWISE CONJUGATION, which knows nothing about `Re t` and is therefore
contour-free: `conj z` is in `ℍₒ` iff `z` is in the open lower half-plane, `sin` commutes with
`conj`, and `conj` passes through a `tsum` (`tsum_star`).  So `hinge_off_axis` holds at EVERY
`z` off the real axis, and `hinge_on_lineB` is its instance at every `n` — strictly more general
than the `n = 0` lemma it replaces, and it supersedes `Zeta2L7Id0Val.kern_neg` /
`sin_sq_lineB_neg` / `hinge_on_lineB` rather than being a second copy of them.

**`MeasureTheory.integral_conj` is still absent at this pin and is still not needed**: nothing
here conjugates an INTEGRAL.  The conjugation is applied to a pointwise identity, before any
integral exists.  (`Complex.sin_conj`, `Complex.conj_conj`, `Complex.conj_ofReal` are present
and are `#check`ed by their use below.  `map_tsum` is an UNKNOWN IDENTIFIER at this pin; the
name that works is `tsum_star`, and in current Mathlib it carries a `SummationFilter` argument.)

## WHAT THIS FILE DOES NOT DO, and one of them is a finding

This is ONE of row L7ID's five non-inherited obligations.  It does NOT close the row.

`Hn_eq_Rfac_mul_tsum` below expands `Hn` termwise off the real axis at every `n`, which is the
step L7ID's route calls "expand the kernel by the hinge".  **The route's NEXT step, "integrate
termwise", cannot be taken on this family at any `n ≥ 1`, and that is measured, not feared.**
`R_n` is a rational function — every `Γ` shift is a positive integer, so the four-over-four
ratio is the Pochhammer quotient

    R_n(t) = (t+1)_{9n} · (t+2n+1)_{9n} · (t+4n+1)_{9n} / (t+15n+1)_{11n+1}

of degree `27n − (11n+1) = 16n − 1`, with `11n+1` poles.  At `n = 0` that is degree `−1` (and
indeed `R_0 = 1/(t+1)`, which is why every term of L7ID-0's family decays like `|s|^{−3}` and is
integrable).  At `n = 1` it is degree `15` with `12` poles — the chain cell's own two numbers,
DERIVED here rather than quoted — so each term `R_n(t)/(t+m)²` GROWS like `|s|^{16n−3}` and is
NOT integrable.  `integral_tsum_of_summable_integral_norm`'s first hypothesis (`∀ i, Integrable
(F i)`) is therefore FALSE at every `n ≥ 1`.

The consequence for the route, and it is an ORDER correction to the chain cell's route sentence:
the `Ppol`/residue split must come BEFORE the termwise integration, not after it.  The residue
part decays like `|t|^{−1}`, so its `m`-th terms decay like `|t|^{−3}` and the interchange does
apply to them; the `Ppol` part has to go through the moment arm against the FULL kernel
`(π/sin πt)²`, which decays like `exp(−2π|s|)`.  All of this is MEASURED by
`l7id_ratfun_check.py` (26 arms, 3 of them falsifiers) and NONE of it is proved in Lean.

Receipts: 12, all `[propext, Classical.choice, Quot.sound]`.  `lean` rc read separately.
Falsifier: `falsify_l7idhinge.sh` → `out_l7idhinge_falsify.txt`.
Second implementation: `l7id_ratfun_check.py` / `.out`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732, buildbox.
-/
import Mathlib
import Zeta2SinSqSeries
import L7MidM5

open Real Complex

namespace Zeta2L7IdHinge

/-! ## §1. The hinge off `ℍₒ`, by pointwise conjugation -/

/-- `conj z` lies in the open upper half-plane exactly when `z` lies in the open lower one. -/
theorem conj_mem_upper {z : ℂ} (hz : z.im < 0) :
    (starRingEnd ℂ) z ∈ UpperHalfPlane.upperHalfPlaneSet := by
  show 0 < ((starRingEnd ℂ) z).im
  simpa using hz

/-- `sin(π·conj z) = conj (sin (π z))` — `Complex.sin_conj` after `π` is moved through `conj`
by `Complex.conj_ofReal`. -/
theorem sin_pi_conj (z : ℂ) :
    Complex.sin ((π : ℂ) * (starRingEnd ℂ) z)
      = (starRingEnd ℂ) (Complex.sin ((π : ℂ) * z)) := by
  have h : ((π : ℂ) * (starRingEnd ℂ) z) = (starRingEnd ℂ) ((π : ℂ) * z) := by
    rw [map_mul, Complex.conj_ofReal]
  rw [h, Complex.sin_conj]

/-- The series, conjugated termwise: `conj (1/(conj z + m)²) = 1/(z + m)²`, because `m` is real
and `conj` is an involution. -/
theorem conj_term (z : ℂ) (m : ℤ) :
    (starRingEnd ℂ) (1 / ((starRingEnd ℂ) z + (m : ℂ)) ^ 2) = 1 / (z + (m : ℂ)) ^ 2 := by
  rw [map_div₀, map_pow, map_add, Complex.conj_conj, map_one]
  norm_num

/-- `conj` through a `tsum`.  UNCONDITIONAL — no `Summable` hypothesis — because `conj` is a
continuous additive equivalence, so it carries the junk value `0` to `0` as well as carrying
genuine sums to sums.  That is what makes this route cheap: the hinge's series is never proved
summable anywhere in this file. -/
theorem conj_tsum (f : ℤ → ℂ) :
    (starRingEnd ℂ) (∑' m : ℤ, f m) = ∑' m : ℤ, (starRingEnd ℂ) (f m) := by
  simpa using (tsum_star (f := f))

/-- **The hinge on the open LOWER half-plane.** -/
theorem hinge_lower {z : ℂ} (hz : z.im < 0) :
    (π : ℂ) ^ 2 / Complex.sin ((π : ℂ) * z) ^ 2 = ∑' m : ℤ, 1 / (z + (m : ℂ)) ^ 2 := by
  have h := Zeta2MB.pi_sq_div_sin_sq_eq_tsum (conj_mem_upper hz)
  have hc := congrArg (starRingEnd ℂ) h
  rw [map_div₀, map_pow, map_pow, Complex.conj_ofReal, sin_pi_conj z, Complex.conj_conj,
    conj_tsum] at hc
  rw [hc]
  exact tsum_congr fun m => conj_term z m

/-- **The hinge off the real axis, at EVERY `z`.**  The hypothesis is `z.im ≠ 0` and it is
load-bearing: at `z ∈ ℤ` the left side divides by `0` and the right side diverges. -/
theorem hinge_off_axis {z : ℂ} (hz : z.im ≠ 0) :
    (π : ℂ) ^ 2 / Complex.sin ((π : ℂ) * z) ^ 2 = ∑' m : ℤ, 1 / (z + (m : ℂ)) ^ 2 := by
  rcases lt_or_gt_of_ne hz with h | h
  · exact hinge_lower h
  · exact Zeta2MB.pi_sq_div_sin_sq_eq_tsum (show 0 < z.im from h)

/-! ## §2. `sin(πt) ≠ 0` off the real axis -/

/-- `Hn_eq_kernel_form`'s side condition, discharged from `Im t ≠ 0` alone — so it costs nothing
on any vertical contour away from the single real point. -/
theorem sin_pi_ne_zero_of_im_ne_zero {t : ℂ} (ht : t.im ≠ 0) :
    Complex.sin ((π : ℂ) * t) ≠ 0 := by
  intro h
  rw [Complex.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht' : t = (k : ℂ) := by
    refine mul_left_cancel₀ hpi ?_
    rw [hk]; ring
  exact ht (by rw [ht']; simp)

/-! ## §3. The σ̃ contour -/

theorem lineB_im (n : ℕ) (s : ℝ) : (L7MidM5.lineB n s).im = s := by
  simp [L7MidM5.lineB]

/-- **ROW L7ID'S FIRST NON-INHERITED OBLIGATION, DISCHARGED AT EVERY `n`.**  The hinge on the
σ̃ contour `Re t = −σ̃n − ½`.  L7ID-0 got the `n = 0` case from a reindexing that is an identity
of `Re t = −½`; this comes from a conjugation that never looks at `Re t`, so `n` is free. -/
theorem hinge_on_lineB (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    (π : ℂ) ^ 2 / Complex.sin ((π : ℂ) * L7MidM5.lineB n s) ^ 2
      = ∑' m : ℤ, 1 / (L7MidM5.lineB n s + (m : ℂ)) ^ 2 :=
  hinge_off_axis (by rw [lineB_im]; exact hs)

/-! ## §4. `Hn` expanded termwise -/

/-- The `Γ`-ratio `Π(n)·R_n(t)` of `zeta2-l7-proof.md` §1, exactly as `Hn_eq_kernel_form`
spells it.  It is a RATIONAL function of `t` (every shift is a positive integer); its degree is
`16n − 1`, measured in `l7id_ratfun_check.py` ARM 1 and NOT proved here. -/
noncomputable def Rfac (n : ℕ) (t : ℂ) : ℂ :=
  (L7MidM123.Pi_n n : ℂ)
    * (Complex.Gamma (t + (L7MidM123.a₁ n : ℂ)) * Complex.Gamma (t + (L7MidM123.a₂ n : ℂ))
        * Complex.Gamma (t + (L7MidM123.a₃ n : ℂ)) * Complex.Gamma (t + (L7MidM123.a₄ n : ℂ)))
    * ((Complex.Gamma (t + (L7MidM123.b₁ n : ℂ)))⁻¹
        * (Complex.Gamma (t + (L7MidM123.b₂ n : ℂ)))⁻¹
        * (Complex.Gamma (t + (L7MidM123.b₃ n : ℂ)))⁻¹
        * (Complex.Gamma (t + (L7MidM123.b₄ n : ℂ)))⁻¹)

/-- **The termwise expansion of `Hn` off the real axis, at every `n`** — the step L7ID's route
calls "expand the kernel by the hinge".  The route's NEXT step is NOT available on this family:
see the header, and `l7id_ratfun_check.py` ARM 4. -/
theorem Hn_eq_Rfac_mul_tsum (n : ℕ) {t : ℂ} (ht : t.im ≠ 0) :
    L7MidM123.Hn n t = Rfac n t * ∑' m : ℤ, 1 / (t + (m : ℂ)) ^ 2 := by
  rw [L7MidM123.Hn_eq_kernel_form n t (sin_pi_ne_zero_of_im_ne_zero ht), Rfac,
    div_pow, hinge_off_axis ht]

/-- The same on the σ̃ contour, with the constant pushed under the sum — the shape an
interchange would consume, stated at every `n` and at `L7MidM5.lineB n`, not at a restatement. -/
theorem Hn_lineB_eq_tsum (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    L7MidM123.Hn n (L7MidM5.lineB n s)
      = ∑' m : ℤ, Rfac n (L7MidM5.lineB n s) / (L7MidM5.lineB n s + (m : ℂ)) ^ 2 := by
  rw [Hn_eq_Rfac_mul_tsum n (by rw [lineB_im]; exact hs), ← tsum_mul_left]
  exact tsum_congr fun m => by ring

/-- `s = 0` is the one point of the contour on the real axis and it is `volume`-null, so every
consumer of the three lemmas above is `ae`. -/
theorem ae_ne_zero : ∀ᵐ s : ℝ, s ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simp

end Zeta2L7IdHinge

#print axioms Zeta2L7IdHinge.conj_mem_upper
#print axioms Zeta2L7IdHinge.sin_pi_conj
#print axioms Zeta2L7IdHinge.conj_term
#print axioms Zeta2L7IdHinge.conj_tsum
#print axioms Zeta2L7IdHinge.hinge_lower
#print axioms Zeta2L7IdHinge.hinge_off_axis
#print axioms Zeta2L7IdHinge.sin_pi_ne_zero_of_im_ne_zero
#print axioms Zeta2L7IdHinge.lineB_im
#print axioms Zeta2L7IdHinge.hinge_on_lineB
#print axioms Zeta2L7IdHinge.Hn_eq_Rfac_mul_tsum
#print axioms Zeta2L7IdHinge.Hn_lineB_eq_tsum
#print axioms Zeta2L7IdHinge.ae_ne_zero
