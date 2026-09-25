/-
  `Zeta2L7LineInt.lean` — row **L7ID-0**, the VALUE half, **piece (a)**: the per-`m` complex
  line integral.

  THE ROW'S NAMED NEXT PROBE, and the reason this file exists: on the contour `t = −½ + is`
  the hinge `Zeta2MB.pi_sq_div_sin_sq_eq_tsum` expands `H₀(t) = π²/((t+1)·sin²(πt))` into
  `Σ_{m∈ℤ} 1/((t+m)²(t+1))`, whose `m`-th term is the real-line integral

      ∫_ℝ ds / ((a + is)² (b + is)),      a = m − ½,  b = ½.

  The row's cell graded this **the top risk and the one piece with no Mathlib support at all**
  — "Mathlib has NO residue theorem (2026-09-11 census) and the partial fraction's two simple
  terms are INDIVIDUALLY DIVERGENT, so this is a complex-log antiderivative with branch care,
  NOT the `arctan` the old cell implied: 150–300 lines."

  **That grading is REFUTED by this file, and the refutation is the finding.** No complex
  logarithm appears below and no branch is chosen.  Two elementary moves replace the contour
  argument:

  1. **Split the double pole off algebraically.**
     `1/((a+is)²(b+is)) = (1/(b−a))·(a+is)⁻² + (1/(a−b))·((a+is)(b+is))⁻¹`,
     and BOTH summands decay like `s⁻²`, so neither is the divergent object the cell feared.
     The divergent partial fraction `A/(a+is) + C/(b+is)` is simply never formed.
  2. **The surviving `(a+is)⁻¹(b+is)⁻¹` is split into REAL and IMAGINARY parts, not into
     poles.**  `Re (c+is)⁻¹ = c/(s²+c²)` is integrable for every `c ≠ 0` — the divergence of
     the naive partial fraction lives ENTIRELY in the imaginary part `−s/(s²+c²)`, which is
     odd and cancels between the two terms.  What is left is Mathlib's Cauchy kernel,
     `∫_ℝ (s²+c²)⁻¹ ds = π/c` (`ProbabilityTheory.integral_cauchyPDFReal_eq_one`).

  **The sign — the whole point of row L7ID-0 — enters at exactly one place**, the `|c|` in

      ∫_ℝ c·(s²+c²)⁻¹ ds = π·c/|c| = π·sgn c        (`integral_lin_re`)

  which is where "the pole is on the other side of the contour" is spelled in real-variable
  language.  The winding number of the classical argument is this `sgn`, and nothing else in
  this file knows about sides of a contour.

  Consequently the per-`m` integral is

      ∫_ℝ ds/((a+is)²(b+is)) = π·(b/|b| − a/|a|)/(a−b)²

  — `0` when `a` and `b` have the SAME sign (both poles on one side: the classical vanishing),
  and `2π/(a−b)²` when they have opposite signs.  At `a = m − ½`, `b = ½` that is `0` for
  `m ≥ 2` and `2π/(m−1)²` for `m ≤ 0` (at `m = 1` the two factors coincide and the term is the
  triple pole `(½+is)⁻³`, which is NOT covered here), so the termwise sum over `m ≤ 0` is
  `2π·Σ_{k≥1} k⁻² = 2π·ζ(2)` and `rIntC 0 = (1/2π)·2π·ζ(2) = ζ(2)` — the `+ζ(2)` the row's
  reroute predicts.

  **Pieces (b), (c), (d) of the row are NOT in this file** — the hinge's lower-half-line
  extension by conjugation, the summability estimate feeding
  `integral_tsum_of_summable_integral_norm`, and integrability of the `n = 0` integrand.  This
  is piece (a) alone, and `Zeta2Target.zeta2_not_liouvilleWith` remains `sorry`.

  Toolchain: Lean `v4.34.0-rc2`, Mathlib `5aedf732` (the buildbox `~/mathlib-current` pin).
  No local dependencies — `import Mathlib` only.  Falsifier: `falsify_l7lineint.sh`.
-/
import Mathlib

open MeasureTheory Complex Filter Topology
open scoped Real NNReal

namespace Zeta2L7LineInt

/-! ### §0. The line factor `a + is` -/

/-- The linear factor `a + is` on the vertical contour, as a function of the real ordinate `s`.
Written `↑a + ↑s * I` to match `L7MidM5.lineB`'s orientation, so a consumer rewrites rather
than commutes. -/
noncomputable def lin (a s : ℝ) : ℂ := (a : ℂ) + (s : ℂ) * Complex.I

theorem lin_re (a s : ℝ) : (lin a s).re = a := by simp [lin]

theorem lin_im (a s : ℝ) : (lin a s).im = s := by simp [lin]

theorem continuous_lin (a : ℝ) : Continuous (lin a) := by
  unfold lin
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

theorem lin_ne_zero {a : ℝ} (ha : a ≠ 0) (s : ℝ) : lin a s ≠ 0 := by
  intro h
  apply ha
  have hre := congrArg Complex.re h
  rwa [lin_re, Complex.zero_re] at hre

theorem normSq_lin (a s : ℝ) : Complex.normSq (lin a s) = s ^ 2 + a ^ 2 := by
  rw [Complex.normSq_apply, lin_re, lin_im]; ring

theorem norm_sq_lin (a s : ℝ) : ‖lin a s‖ ^ 2 = s ^ 2 + a ^ 2 := by
  rw [Complex.sq_norm, normSq_lin]

theorem lin_sub_lin (a b s : ℝ) : lin a s - lin b s = ((a - b : ℝ) : ℂ) := by
  simp only [lin]; push_cast; ring

/-- `∫ ↑(f s) = ↑(∫ f)` for a `ℂ`-valued real integral.  Mathlib's `integral_ofReal` is stated
through `RCLike.ofReal` and does not rewrite against `Complex.ofReal` (there is an explicit
`TODO` in `IntervalIntegral/Basic.lean` asking for the `Complex` version), so the corpus's
three-line `ContinuousLinearMap.integral_comp_comm` route is spelled once, here. -/
theorem integral_ofReal_eq {f : ℝ → ℝ} (hf : Integrable f) :
    ∫ s : ℝ, ((f s : ℝ) : ℂ) = ((∫ s : ℝ, f s : ℝ) : ℂ) := by
  simpa using ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hf

/-! ### §1. Mathlib's Cauchy kernel: `∫_ℝ (s² + c²)⁻¹ ds = π/c` -/

/-- `(s² + c²)⁻¹` is `(π/c)` times the standard Cauchy density at location `0`, scale `c`. -/
theorem inv_sq_add_sq_eq {c : ℝ} (hc : 0 < c) (s : ℝ) :
    (s ^ 2 + c ^ 2)⁻¹
      = (Real.pi / c) * ProbabilityTheory.cauchyPDFReal 0 c.toNNReal s := by
  rw [ProbabilityTheory.cauchyPDFReal_def, Real.coe_toNNReal c hc.le, sub_zero]
  have hone : Real.pi / c * (Real.pi⁻¹ * c) = 1 := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  calc (s ^ 2 + c ^ 2)⁻¹
      = (Real.pi / c * (Real.pi⁻¹ * c)) * (s ^ 2 + c ^ 2)⁻¹ := by rw [hone, one_mul]
    _ = Real.pi / c * (Real.pi⁻¹ * c * (s ^ 2 + c ^ 2)⁻¹) := by ring

theorem integrable_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun s : ℝ => (s ^ 2 + c ^ 2)⁻¹) := by
  have h := (ProbabilityTheory.integrable_cauchyPDFReal (γ := c.toNNReal) 0).const_mul
    (Real.pi / c)
  refine h.congr ?_
  filter_upwards with s
  exact (inv_sq_add_sq_eq hc s).symm

/-- **The Cauchy kernel.**  `∫_ℝ (s² + c²)⁻¹ ds = π/c` for `c > 0`. -/
theorem integral_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, (s ^ 2 + c ^ 2)⁻¹ = Real.pi / c := by
  have hγ : c.toNNReal ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact hc
  calc ∫ s : ℝ, (s ^ 2 + c ^ 2)⁻¹
      = ∫ s : ℝ, (Real.pi / c) * ProbabilityTheory.cauchyPDFReal 0 c.toNNReal s :=
        integral_congr_ae (Filter.Eventually.of_forall (inv_sq_add_sq_eq hc))
    _ = (Real.pi / c) * ∫ s : ℝ, ProbabilityTheory.cauchyPDFReal 0 c.toNNReal s :=
        integral_const_mul _ _
    _ = Real.pi / c := by
        rw [ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 hγ, mul_one]

theorem integrable_lin_re {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun s : ℝ => c * (s ^ 2 + c ^ 2)⁻¹) := by
  have habs : (0 : ℝ) < |c| := abs_pos.mpr hc
  have h := (integrable_inv_sq_add_sq habs).const_mul c
  refine h.congr ?_
  filter_upwards with s
  rw [sq_abs]

/-- **THE SIGN, and the only place it enters this file.**  `Re (c+is)⁻¹ = c/(s²+c²)` integrates
to `π·sgn c`: the real-variable spelling of "which side of the contour the pole is on". -/
theorem integral_lin_re {c : ℝ} (hc : c ≠ 0) :
    ∫ s : ℝ, c * (s ^ 2 + c ^ 2)⁻¹ = Real.pi * c / |c| := by
  have habs : (0 : ℝ) < |c| := abs_pos.mpr hc
  calc ∫ s : ℝ, c * (s ^ 2 + c ^ 2)⁻¹
      = ∫ s : ℝ, c * (s ^ 2 + |c| ^ 2)⁻¹ := by simp_rw [sq_abs]
    _ = c * ∫ s : ℝ, (s ^ 2 + |c| ^ 2)⁻¹ := integral_const_mul _ _
    _ = c * (Real.pi / |c|) := by rw [integral_inv_sq_add_sq habs]
    _ = Real.pi * c / |c| := by ring

/-! ### §2. The real/imaginary split of a single simple factor -/

/-- `(c+is)⁻¹ = c/(s²+c²) − i·s/(s²+c²)`.  Holds unconditionally (both sides are `0` at
`c = s = 0`).  **The divergence of the naive partial fraction lives in the second summand**,
which is odd; the first is Mathlib's Cauchy kernel. -/
theorem inv_lin (c s : ℝ) :
    (lin c s)⁻¹
      = ((c / (s ^ 2 + c ^ 2) : ℝ) : ℂ)
        + ((-s / (s ^ 2 + c ^ 2) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.inv_re, normSq_lin, lin_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp only [Complex.add_im, Complex.inv_im, normSq_lin, lin_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

/-! ### §3. The double pole integrates to zero -/

theorem hasDerivAt_lin (a s : ℝ) : HasDerivAt (lin a) Complex.I s := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 s := by
    simpa using (hasDerivAt_id s).ofReal_comp
  have h2 := (h1.mul_const Complex.I).const_add ((a : ℂ))
  rw [one_mul] at h2
  exact h2

theorem integrable_inv_lin_sq {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun s : ℝ => ((lin a s) ^ 2)⁻¹) := by
  have habs : (0 : ℝ) < |a| := abs_pos.mpr ha
  have hcont : Continuous (fun s : ℝ => ((lin a s) ^ 2)⁻¹) :=
    Continuous.inv₀ ((continuous_lin a).pow 2) (fun s => pow_ne_zero 2 (lin_ne_zero ha s))
  refine (integrable_inv_sq_add_sq habs).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with s
  rw [norm_inv, norm_pow, norm_sq_lin, sq_abs]

theorem tendsto_norm_lin_atTop (a : ℝ) :
    Tendsto (fun s : ℝ => ‖lin a s‖) atTop atTop := by
  refine tendsto_atTop_mono (fun s => ?_) tendsto_abs_atTop_atTop
  have h := Complex.abs_im_le_norm (lin a s)
  rwa [lin_im] at h

theorem tendsto_norm_lin_atBot (a : ℝ) :
    Tendsto (fun s : ℝ => ‖lin a s‖) atBot atTop := by
  refine tendsto_atTop_mono (fun s => ?_) tendsto_abs_atBot_atTop
  have h := Complex.abs_im_le_norm (lin a s)
  rwa [lin_im] at h

theorem tendsto_inv_lin (a : ℝ) (l : Filter ℝ)
    (hl : Tendsto (fun s : ℝ => ‖lin a s‖) l atTop) :
    Tendsto (fun s : ℝ => Complex.I * (lin a s)⁻¹) l (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have heq : ∀ s : ℝ, ‖Complex.I * (lin a s)⁻¹‖ = (‖lin a s‖)⁻¹ := by
    intro s
    rw [norm_mul, Complex.norm_I, one_mul, norm_inv]
  simp only [heq]
  exact hl.inv_tendsto_atTop

/-- **The double pole contributes nothing.**  `∫_ℝ (a+is)⁻² ds = 0` for every `a ≠ 0` — by an
exact antiderivative `i·(a+is)⁻¹` that vanishes at both ends, with no branch to choose. -/
theorem integral_inv_lin_sq {a : ℝ} (ha : a ≠ 0) :
    ∫ s : ℝ, ((lin a s) ^ 2)⁻¹ = 0 := by
  have hI : Complex.I * (-Complex.I) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => Complex.I * (lin a s)⁻¹) (((lin a s) ^ 2)⁻¹) s := by
    intro s
    have h := ((hasDerivAt_lin a s).inv (lin_ne_zero ha s)).const_mul Complex.I
    have hcoef : Complex.I * (-Complex.I / (lin a s) ^ 2) = ((lin a s) ^ 2)⁻¹ := by
      rw [← mul_div_assoc, hI, one_div]
    rwa [hcoef] at h
  have h := integral_of_hasDerivAt_of_tendsto hderiv (integrable_inv_lin_sq ha)
    (tendsto_inv_lin a atBot (tendsto_norm_lin_atBot a))
    (tendsto_inv_lin a atTop (tendsto_norm_lin_atTop a))
  simpa using h

/-! ### §4. The mixed product `(a+is)⁻¹(b+is)⁻¹` -/

/-- The real part of `(a+is)⁻¹(b+is)⁻¹`. -/
noncomputable def mixRe (a b s : ℝ) : ℝ :=
  (a - b)⁻¹ * (b * (s ^ 2 + b ^ 2)⁻¹ - a * (s ^ 2 + a ^ 2)⁻¹)

/-- The imaginary part of `(a+is)⁻¹(b+is)⁻¹`.  Odd in `s`, hence integrates to zero — this is
where the divergence of the naive partial fraction went.  Stated in the PRODUCT form, which is
the one that is visibly `O(s⁻³)`; `mixIm_eq` is the difference form the algebra produces. -/
noncomputable def mixIm (a b s : ℝ) : ℝ :=
  -(a + b) * (s / ((s ^ 2 + a ^ 2) * (s ^ 2 + b ^ 2)))

theorem mixIm_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (s : ℝ) :
    mixIm a b s = (a - b)⁻¹ * (s * (s ^ 2 + a ^ 2)⁻¹ - s * (s ^ 2 + b ^ 2)⁻¹) := by
  have ha2 : (s ^ 2 + a ^ 2) ≠ 0 := by positivity
  have hb2 : (s ^ 2 + b ^ 2) ≠ 0 := by positivity
  have habR : a - b ≠ 0 := sub_ne_zero.mpr hab
  unfold mixIm
  field_simp
  ring

theorem mix_split {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (s : ℝ) :
    (lin a s * lin b s)⁻¹ = ((mixRe a b s : ℝ) : ℂ) + ((mixIm a b s : ℝ) : ℂ) * Complex.I := by
  have hA : lin a s ≠ 0 := lin_ne_zero ha s
  have hB : lin b s ≠ 0 := lin_ne_zero hb s
  have habR : a - b ≠ 0 := sub_ne_zero.mpr hab
  have habC : ((a - b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast habR
  have hdiff : (lin b s)⁻¹ - (lin a s)⁻¹ = ((a - b : ℝ) : ℂ) * (lin a s * lin b s)⁻¹ := by
    rw [← lin_sub_lin a b s]; field_simp
  have hstep : (lin a s * lin b s)⁻¹
      = (((a - b : ℝ) : ℂ))⁻¹ * ((lin b s)⁻¹ - (lin a s)⁻¹) := by
    rw [hdiff, ← mul_assoc, inv_mul_cancel₀ habC, one_mul]
  rw [hstep, inv_lin a s, inv_lin b s, mixIm_eq ha hb hab s]
  simp only [mixRe]
  push_cast
  ring

theorem integrable_mixRe {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (mixRe a b) :=
  ((integrable_lin_re hb).sub (integrable_lin_re ha)).const_mul (a - b)⁻¹

theorem integral_mixRe {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∫ s : ℝ, mixRe a b s = Real.pi * (b / |b| - a / |a|) / (a - b) := by
  have hsub : ∫ s : ℝ, (b * (s ^ 2 + b ^ 2)⁻¹ - a * (s ^ 2 + a ^ 2)⁻¹)
      = Real.pi * b / |b| - Real.pi * a / |a| := by
    rw [integral_sub (integrable_lin_re hb) (integrable_lin_re ha),
      integral_lin_re hb, integral_lin_re ha]
  calc ∫ s : ℝ, mixRe a b s
      = (a - b)⁻¹ * ∫ s : ℝ, (b * (s ^ 2 + b ^ 2)⁻¹ - a * (s ^ 2 + a ^ 2)⁻¹) := by
        simp only [mixRe]; exact integral_const_mul _ _
    _ = (a - b)⁻¹ * (Real.pi * b / |b| - Real.pi * a / |a|) := by rw [hsub]
    _ = Real.pi * (b / |b| - a / |a|) / (a - b) := by ring

/-- `|s|/(s²+a²) ≤ 1/(2|a|)` — the AM–GM bound that makes `mixIm` dominated. -/
theorem abs_div_sq_add_sq_le {a : ℝ} (ha : a ≠ 0) (s : ℝ) :
    |s| / (s ^ 2 + a ^ 2) ≤ 1 / (2 * |a|) := by
  have h2 : (0 : ℝ) < s ^ 2 + a ^ 2 := by positivity
  have h3 : (0 : ℝ) < 2 * |a| := by positivity
  rw [div_le_div_iff₀ h2 h3]
  nlinarith [sq_nonneg (|s| - |a|), sq_abs s, sq_abs a]

theorem integrable_mixIm {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (mixIm a b) := by
  have habs : (0 : ℝ) < |b| := abs_pos.mpr hb
  have hg0 : Integrable (fun s : ℝ => (s ^ 2 + b ^ 2)⁻¹) := by
    refine (integrable_inv_sq_add_sq habs).congr ?_
    filter_upwards with s
    rw [sq_abs]
  have hg := hg0.const_mul (|a + b| / (2 * |a|))
  have hcont : Continuous (mixIm a b) := by
    unfold mixIm
    refine continuous_const.mul (continuous_id.div (Continuous.mul ?_ ?_) (fun s => ?_))
    · exact (continuous_pow 2).add continuous_const
    · exact (continuous_pow 2).add continuous_const
    · positivity
  refine hg.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with s
  have ha2 : (0 : ℝ) < s ^ 2 + a ^ 2 := by positivity
  have hb2 : (0 : ℝ) < s ^ 2 + b ^ 2 := by positivity
  have hkey : |s| / (s ^ 2 + a ^ 2) ≤ 1 / (2 * |a|) := abs_div_sq_add_sq_le ha s
  have hnorm : ‖mixIm a b s‖ = |a + b| * (|s| / ((s ^ 2 + a ^ 2) * (s ^ 2 + b ^ 2))) := by
    simp only [mixIm, Real.norm_eq_abs, abs_mul, abs_neg, abs_div]
    rw [abs_of_pos ha2, abs_of_pos hb2]
  have hbound : |s| / ((s ^ 2 + a ^ 2) * (s ^ 2 + b ^ 2))
      ≤ (1 / (2 * |a|)) * (s ^ 2 + b ^ 2)⁻¹ := by
    rw [div_mul_eq_div_div, div_eq_mul_inv (|s| / (s ^ 2 + a ^ 2)) (s ^ 2 + b ^ 2)]
    exact mul_le_mul_of_nonneg_right hkey (by positivity)
  rw [hnorm]
  calc |a + b| * (|s| / ((s ^ 2 + a ^ 2) * (s ^ 2 + b ^ 2)))
      ≤ |a + b| * ((1 / (2 * |a|)) * (s ^ 2 + b ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = |a + b| / (2 * |a|) * (s ^ 2 + b ^ 2)⁻¹ := by ring

/-- Every odd function integrates to zero on `ℝ` — Mathlib's `integral_neg_eq_self` for the
neg-invariant Lebesgue measure.  No integrability hypothesis: when the integral is undefined
both sides are Lean's junk value `0`. -/
theorem integral_eq_zero_of_odd {f : ℝ → ℝ} (hodd : ∀ s : ℝ, f (-s) = -f s) :
    ∫ s : ℝ, f s = 0 := by
  have h1 : ∫ s : ℝ, f (-s) = ∫ s : ℝ, f s := integral_neg_eq_self f volume
  have h2 : ∫ s : ℝ, f (-s) = ∫ s : ℝ, -f s :=
    integral_congr_ae (Filter.Eventually.of_forall hodd)
  rw [h2, integral_neg] at h1
  linarith

theorem integral_mixIm (a b : ℝ) : ∫ s : ℝ, mixIm a b s = 0 := by
  refine integral_eq_zero_of_odd (fun s => ?_)
  simp only [mixIm, neg_sq]
  ring

/-- **The mixed product.**  `∫_ℝ ds/((a+is)(b+is)) = π(b/|b| − a/|a|)/(a−b)`. -/
theorem integral_inv_lin_mul_lin {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∫ s : ℝ, (lin a s * lin b s)⁻¹
      = ((Real.pi * (b / |b| - a / |a|) / (a - b) : ℝ) : ℂ) := by
  have hR : Integrable (fun s : ℝ => ((mixRe a b s : ℝ) : ℂ)) :=
    (integrable_mixRe ha hb).ofReal
  have hJ : Integrable (fun s : ℝ => ((mixIm a b s : ℝ) : ℂ) * Complex.I) :=
    ((integrable_mixIm ha hb).ofReal).mul_const Complex.I
  calc ∫ s : ℝ, (lin a s * lin b s)⁻¹
      = ∫ s : ℝ, (((mixRe a b s : ℝ) : ℂ) + ((mixIm a b s : ℝ) : ℂ) * Complex.I) :=
        integral_congr_ae (Filter.Eventually.of_forall (mix_split ha hb hab))
    _ = (∫ s : ℝ, ((mixRe a b s : ℝ) : ℂ))
        + ∫ s : ℝ, ((mixIm a b s : ℝ) : ℂ) * Complex.I := integral_add hR hJ
    _ = ((∫ s : ℝ, mixRe a b s : ℝ) : ℂ)
        + ((∫ s : ℝ, mixIm a b s : ℝ) : ℂ) * Complex.I := by
        rw [integral_mul_const, integral_ofReal_eq (integrable_mixRe ha hb),
          integral_ofReal_eq (integrable_mixIm ha hb)]
    _ = ((Real.pi * (b / |b| - a / |a|) / (a - b) : ℝ) : ℂ) := by
        rw [integral_mixRe ha hb, integral_mixIm a b]
        push_cast
        ring

/-! ### §5. The per-`m` line integral, with its sign -/

/-- **PIECE (a), the row's named risk, CLOSED.**

`∫_ℝ ds/((a+is)²(b+is)) = π(b/|b| − a/|a|)/(a−b)²`.

`0` when `a` and `b` agree in sign; `2π/(a−b)²` when they do not.  No residue theorem, no
complex logarithm, no branch. -/
theorem integral_line_two_pole {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∫ s : ℝ, ((lin a s) ^ 2 * lin b s)⁻¹
      = ((Real.pi * (b / |b| - a / |a|) / (a - b) ^ 2 : ℝ) : ℂ) := by
  have habR : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hbaR : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have habC : ((a - b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast habR
  have hbaC : ((b - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hbaR
  -- the algebraic split: both summands decay like `s⁻²`, so neither is the divergent object
  have hsplit : ∀ s : ℝ, ((lin a s) ^ 2 * lin b s)⁻¹
      = (((b - a : ℝ) : ℂ))⁻¹ * ((lin a s) ^ 2)⁻¹
        + (((a - b : ℝ) : ℂ))⁻¹ * (lin a s * lin b s)⁻¹ := by
    intro s
    have hA : lin a s ≠ 0 := lin_ne_zero ha s
    have hB : lin b s ≠ 0 := lin_ne_zero hb s
    have hneg : ((b - a : ℝ) : ℂ) = -((a - b : ℝ) : ℂ) := by push_cast; ring
    have hkey : (((b - a : ℝ) : ℂ))⁻¹ * lin b s + (((a - b : ℝ) : ℂ))⁻¹ * lin a s = 1 := by
      rw [hneg, inv_neg]
      have hcollect : -(((a - b : ℝ) : ℂ))⁻¹ * lin b s + (((a - b : ℝ) : ℂ))⁻¹ * lin a s
          = (((a - b : ℝ) : ℂ))⁻¹ * (lin a s - lin b s) := by ring
      rw [hcollect, lin_sub_lin, inv_mul_cancel₀ habC]
    have hfactor : (((b - a : ℝ) : ℂ))⁻¹ * ((lin a s) ^ 2)⁻¹
          + (((a - b : ℝ) : ℂ))⁻¹ * (lin a s * lin b s)⁻¹
        = ((lin a s) ^ 2 * lin b s)⁻¹
          * ((((b - a : ℝ) : ℂ))⁻¹ * lin b s + (((a - b : ℝ) : ℂ))⁻¹ * lin a s) := by
      field_simp
    rw [hfactor, hkey, mul_one]
  have hI1 : Integrable (fun s : ℝ => (((b - a : ℝ) : ℂ))⁻¹ * ((lin a s) ^ 2)⁻¹) :=
    (integrable_inv_lin_sq ha).const_mul _
  have hI2 : Integrable (fun s : ℝ => (((a - b : ℝ) : ℂ))⁻¹ * (lin a s * lin b s)⁻¹) := by
    have hR : Integrable (fun s : ℝ => ((mixRe a b s : ℝ) : ℂ)) :=
      (integrable_mixRe ha hb).ofReal
    have hJ : Integrable (fun s : ℝ => ((mixIm a b s : ℝ) : ℂ) * Complex.I) :=
      ((integrable_mixIm ha hb).ofReal).mul_const Complex.I
    refine Integrable.const_mul ?_ _
    refine (hR.add hJ).congr ?_
    filter_upwards with s
    exact (mix_split ha hb hab s).symm
  calc ∫ s : ℝ, ((lin a s) ^ 2 * lin b s)⁻¹
      = ∫ s : ℝ, ((((b - a : ℝ) : ℂ))⁻¹ * ((lin a s) ^ 2)⁻¹
          + (((a - b : ℝ) : ℂ))⁻¹ * (lin a s * lin b s)⁻¹) :=
        integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = (∫ s : ℝ, (((b - a : ℝ) : ℂ))⁻¹ * ((lin a s) ^ 2)⁻¹)
        + ∫ s : ℝ, (((a - b : ℝ) : ℂ))⁻¹ * (lin a s * lin b s)⁻¹ := integral_add hI1 hI2
    _ = (((b - a : ℝ) : ℂ))⁻¹ * (∫ s : ℝ, ((lin a s) ^ 2)⁻¹)
        + (((a - b : ℝ) : ℂ))⁻¹ * ∫ s : ℝ, (lin a s * lin b s)⁻¹ := by
        rw [integral_const_mul, integral_const_mul]
    _ = ((Real.pi * (b / |b| - a / |a|) / (a - b) ^ 2 : ℝ) : ℂ) := by
        rw [integral_inv_lin_sq ha, integral_inv_lin_mul_lin ha hb hab]
        push_cast
        field_simp
        ring

/-! ### §6. The two named instances, and the per-`m` corollaries -/

/-- **THE ROW'S NAMED NEXT PROBE**, verbatim from the L7ID-0 cell: the single line integral
`∫_ℝ ds/((3/2+is)²(1/2+is))`, elaborated on its own before any assembly.

**Its value is `0`** — and that is a finding about the row, not about this lemma: `a = 3/2`
and `b = 1/2` have the SAME sign, so both poles lie on one side of the contour and the term
contributes nothing.  On the contour `t = −½ + is` this is the `m = 2` term of the hinge
(`a = m − ½`), so the cell's "m = 1" names a VANISHING term; the `m = 1` term itself is the
triple pole `(1/2+is)⁻³`. -/
theorem probe_named :
    ∫ s : ℝ, ((lin (3 / 2) s) ^ 2 * lin (1 / 2) s)⁻¹ = 0 := by
  have h := integral_line_two_pole (a := 3 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  rw [h]
  norm_num

/-- The first NON-vanishing term, `a = −1/2` (the hinge's `m = 0`): `2π`.  Opposite signs, so
the classical residue survives — `2π/(a−b)² = 2π/1 = 2π`. -/
theorem probe_m_zero :
    ∫ s : ℝ, ((lin (-(1 / 2)) s) ^ 2 * lin (1 / 2) s)⁻¹ = ((2 * Real.pi : ℝ) : ℂ) := by
  have h := integral_line_two_pole (a := -(1 / 2)) (b := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  rw [h]
  congr 1
  rw [show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num,
    show |(-(1 / 2) : ℝ)| = 1 / 2 from by norm_num]
  ring

/-- **The per-`m` term on the row's own contour**, `a = m − ½`, `b = ½`, for `m ≥ 2`: it
VANISHES.  Both poles are on the same side. -/
theorem integral_term_ge_two {m : ℤ} (hm : 2 ≤ m) :
    ∫ s : ℝ, ((lin ((m : ℝ) - 1 / 2) s) ^ 2 * lin (1 / 2) s)⁻¹ = 0 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hgt : (0 : ℝ) < (m : ℝ) - 1 / 2 := by linarith
  have ha : ((m : ℝ) - 1 / 2) ≠ 0 := ne_of_gt hgt
  have hb : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hab : ((m : ℝ) - 1 / 2) ≠ 1 / 2 := by intro h; linarith
  rw [integral_line_two_pole ha hb hab]
  rw [show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num, abs_of_pos hgt,
    div_self ha, show (1 / 2 : ℝ) / (1 / 2) = 1 from by norm_num]
  norm_num

/-- **The per-`m` term on the row's own contour**, `a = m − ½`, `b = ½`, for `m ≤ 0`:
`2π/(m−1)²`.  Summing over `k = 1 − m ≥ 1` gives `2π·Σ_{k≥1} k⁻² = 2π·ζ(2)`. -/
theorem integral_term_le_zero {m : ℤ} (hm : m ≤ 0) :
    ∫ s : ℝ, ((lin ((m : ℝ) - 1 / 2) s) ^ 2 * lin (1 / 2) s)⁻¹
      = ((2 * Real.pi / ((m : ℝ) - 1) ^ 2 : ℝ) : ℂ) := by
  have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm
  have hlt : (m : ℝ) - 1 / 2 < 0 := by linarith
  have ha : ((m : ℝ) - 1 / 2) ≠ 0 := ne_of_lt hlt
  have hb : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hab : ((m : ℝ) - 1 / 2) ≠ 1 / 2 := by intro h; linarith
  rw [integral_line_two_pole ha hb hab]
  congr 1
  rw [show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num, abs_of_neg hlt,
    show (1 / 2 : ℝ) / (1 / 2) = 1 from by norm_num,
    div_neg_eq_neg_div, div_self ha]
  have hden : ((m : ℝ) - 1 / 2 - 1 / 2) = (m : ℝ) - 1 := by ring
  rw [hden]
  ring

/-! ### §7. Raw-form restatements, for a consumer that has not opened this namespace -/

/-- `probe_named` with `lin` unfolded — the cell's literal `∫ℝ ds/((3/2+is)²(1/2+is))`. -/
theorem probe_named_raw :
    ∫ s : ℝ, ((((3 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I) ^ 2
        * (((1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I))⁻¹ = 0 := by
  simpa [lin] using probe_named

/-- `integral_line_two_pole` with `lin` unfolded. -/
theorem integral_line_two_pole_raw {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∫ s : ℝ, (((a : ℂ) + (s : ℂ) * Complex.I) ^ 2 * ((b : ℂ) + (s : ℂ) * Complex.I))⁻¹
      = ((Real.pi * (b / |b| - a / |a|) / (a - b) ^ 2 : ℝ) : ℂ) := by
  simpa [lin] using integral_line_two_pole ha hb hab

end Zeta2L7LineInt

#print axioms Zeta2L7LineInt.integral_inv_sq_add_sq
#print axioms Zeta2L7LineInt.integral_lin_re
#print axioms Zeta2L7LineInt.inv_lin
#print axioms Zeta2L7LineInt.integral_inv_lin_sq
#print axioms Zeta2L7LineInt.mix_split
#print axioms Zeta2L7LineInt.integral_mixRe
#print axioms Zeta2L7LineInt.integral_mixIm
#print axioms Zeta2L7LineInt.integral_inv_lin_mul_lin
#print axioms Zeta2L7LineInt.integral_line_two_pole
#print axioms Zeta2L7LineInt.probe_named
#print axioms Zeta2L7LineInt.probe_m_zero
#print axioms Zeta2L7LineInt.integral_term_ge_two
#print axioms Zeta2L7LineInt.integral_term_le_zero
#print axioms Zeta2L7LineInt.probe_named_raw
#print axioms Zeta2L7LineInt.integral_line_two_pole_raw
