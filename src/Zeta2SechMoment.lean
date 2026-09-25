/-
# Row L7ID — `SechMomentTable`, PROVED

`∫ℝ s^{2m}·π² sech²(π s) ds = (−1)^m · 2π · B_{2m}(½)`, for every `m : ℕ`.

This is the ONE `n`-independent analytic obligation `Zeta2L7IdMoment` left of the `Ppol` moment
arm, and hence — through `Zeta2L7IdSum.PpolMomentValue` — the whole VALUE residue of row L7ID.
It is stated here in bare Mathlib vocabulary (`Real.cosh`, `Polynomial.bernoulli`) so that this
file has NO chain dependency and elaborates on its own; `Zeta2SechBridge.lean` discharges
`Zeta2L7IdMoment.SechMomentTable` from it.

## The route, and why it is neither of the two the censuses priced

Route A (antiderivative against `tanh`) and route B (`riemannZeta_two_mul_nat`) both end at the
Bernoulli NUMBER `B_{2m}` and then owe `B_{2m}(½) = (2^{1−2m} − 1)·B_{2m}` — Raabe's / the
duplication formula, measured ABSENT at this pin under all six spellings a census can ask
(`Polynomial.bernoulli_eval_one_half`, `_eval_half`, `_eval_two_mul`, `_eval_mul`,
`bernoulli_multiplication`, `bernoulli_raabe`).  That conversion was never priced by either
earlier census and is the real cost of both routes.

ROUTE C retires it outright.  `hasSum_one_div_nat_pow_mul_cos` is PRESENT and is stated at a
general `x ∈ [0,1]` AGAINST THE BERNOULLI POLYNOMIAL:

    HasSum (fun n => 1/n^{2k} · cos (2π n x))
           ((−1)^{k+1}·(2π)^{2k}/2/(2k)! · (bernoulli (2k)).eval x)

and `cos (2π n · ½) = cos (n π) = (−1)^n`, so at `x = ½` it IS the alternating zeta value
already written at `B_{2k}(½)`.  Nothing has to be converted.

So the file is: expand `sech²` as a geometric series in `e^{−2πs}` on `(0,∞)`, integrate
termwise (`integral_tsum_of_summable_integral_norm` — the same lemma `Zeta2L7IdResid` used, and
the summability is `Σ k^{−2m}`, which is why `m = 0` is a separate branch), evaluate each term
by the Γ-integral, and read the alternating sum off route C.  The `m = 0` branch is route A
after all, but only at its one easy instance: `∫ π² sech²(πs) ds = π·tanh(πs)|_{−∞}^{∞} = 2π`.
The census found every piece of `hasDerivAt_tanh` present even though the lemma is not.

## What is NOT in this file

No estimate: obligation 2 of row L7ID (the decay rate on `rₙ`) is untouched here, and this
table is a VALUE.  No chain object appears in any statement.
-/
import Mathlib

namespace Zeta2SechMoment

open MeasureTheory Filter Set

/-! ## §1. The kernel and its elementary properties -/

/-- `π² sech²(π s)`, spelled exactly as `Zeta2L7IdMoment.SechMomentTable` spells it. -/
noncomputable def sechKer (s : ℝ) : ℝ := Real.pi ^ 2 / Real.cosh (Real.pi * s) ^ 2

theorem sechKer_even (s : ℝ) : sechKer (-s) = sechKer s := by
  rw [sechKer, sechKer, mul_neg, Real.cosh_neg]

theorem sechKer_nonneg (s : ℝ) : 0 ≤ sechKer s := by
  rw [sechKer]; positivity

theorem continuous_sechKer : Continuous sechKer := by
  have hc : Continuous fun s : ℝ => Real.cosh (Real.pi * s) ^ 2 :=
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).pow 2
  exact continuous_const.div hc (fun s => pow_ne_zero 2 (Real.cosh_pos _).ne')

/-- `e^{|x|} ≤ 2 cosh x` — the one inequality the exponential majorant rests on. -/
theorem exp_abs_le_two_mul_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  rcases abs_choice x with h | h <;> rw [h]
  · have := (Real.exp_pos (-x)).le; linarith
  · have := (Real.exp_pos x).le; linarith

theorem sechKer_le (s : ℝ) :
    sechKer s ≤ 4 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi * |s|)) := by
  have hpi := Real.pi_pos
  have habs : |Real.pi * s| = Real.pi * |s| := by rw [abs_mul, abs_of_pos hpi]
  have hc : 0 < Real.cosh (Real.pi * s) := Real.cosh_pos _
  have he : 0 < Real.exp (Real.pi * |s|) := Real.exp_pos _
  have h1 : Real.exp (Real.pi * |s|) ≤ 2 * Real.cosh (Real.pi * s) := by
    rw [← habs]; exact exp_abs_le_two_mul_cosh _
  have h3 : Real.exp (Real.pi * |s|) ^ 2 = Real.exp (2 * Real.pi * |s|) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hkey : Real.exp (2 * Real.pi * |s|) ≤ 4 * Real.cosh (Real.pi * s) ^ 2 := by
    nlinarith [h1, h3, he.le, hc.le]
  have hE : (0 : ℝ) < Real.exp (2 * Real.pi * |s|) := Real.exp_pos _
  have hE0 : Real.exp (2 * Real.pi * |s|) ≠ 0 := ne_of_gt hE
  rw [sechKer, Real.exp_neg, div_le_iff₀ (by positivity : (0:ℝ) < Real.cosh (Real.pi * s) ^ 2)]
  have hprod : (0:ℝ) ≤ Real.pi ^ 2 * (Real.exp (2 * Real.pi * |s|))⁻¹
      * (4 * Real.cosh (Real.pi * s) ^ 2 - Real.exp (2 * Real.pi * |s|)) := by
    apply mul_nonneg (by positivity)
    linarith [hkey]
  have hexpand : Real.pi ^ 2 * (Real.exp (2 * Real.pi * |s|))⁻¹
        * (4 * Real.cosh (Real.pi * s) ^ 2 - Real.exp (2 * Real.pi * |s|))
      = 4 * Real.pi ^ 2 * (Real.exp (2 * Real.pi * |s|))⁻¹ * Real.cosh (Real.pi * s) ^ 2
        - Real.pi ^ 2 := by
    first
    | (field_simp; ring)
    | field_simp
  linarith [hprod, hexpand.le, hexpand.ge]

/-! ## §2. The even split — the two facts `integral_add_compl` needs -/

theorem integrable_of_even {f : ℝ → ℝ} (hf : ∀ s, f (-s) = f s)
    (h : IntegrableOn f (Ioi 0) volume) : Integrable f volume := by
  have hIio : IntegrableOn f (Iio (0:ℝ)) volume := by
    have h1 : Integrable ((Ioi (0:ℝ)).indicator f) volume :=
      (integrable_indicator_iff measurableSet_Ioi).mpr h
    have h2 : Integrable (fun t : ℝ => (Ioi (0:ℝ)).indicator f (-t)) volume := h1.comp_neg
    have heq : (fun t : ℝ => (Ioi (0:ℝ)).indicator f (-t)) = (Iio (0:ℝ)).indicator f := by
      funext t
      simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_Iio, neg_pos]
      by_cases ht : t < 0
      · simp [ht, hf t]
      · simp [ht]
    rw [heq] at h2
    exact (integrable_indicator_iff measurableSet_Iio).mp h2
  have hIic : IntegrableOn f (Iic (0:ℝ)) volume := hIio.congr_set_ae (Iio_ae_eq_Iic).symm
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
  exact integrableOn_union.mpr ⟨hIic, h⟩

theorem integral_even {f : ℝ → ℝ} (hf : ∀ s, f (-s) = f s) (hint : Integrable f volume) :
    (∫ s : ℝ, f s) = 2 * ∫ s in Ioi (0:ℝ), f s := by
  have hsplit := integral_add_compl (measurableSet_Ioi (a := (0:ℝ))) hint
  rw [Set.compl_Ioi] at hsplit
  have hIic : (∫ s in Iic (0:ℝ), f s) = ∫ s in Ioi (0:ℝ), f s := by
    have h1 : (∫ s in Iic (0:ℝ), f (-s)) = ∫ s in Ioi (-(0:ℝ)), f s := integral_comp_neg_Iic 0 f
    rw [neg_zero] at h1
    rw [← h1]
    exact setIntegral_congr_fun measurableSet_Iic (fun x _ => (hf x).symm)
  rw [hIic] at hsplit
  linarith [hsplit]

/-! ## §3. The exponential moments on `(0,∞)`, from the Γ-integral -/

theorem integral_exp_neg_mul_pow_unit (j : ℕ) :
    (∫ x in Ioi (0:ℝ), Real.exp (-x) * x ^ j) = (j.factorial : ℝ) := by
  have h : Real.Gamma ((j : ℝ) + 1)
      = ∫ x in Ioi (0:ℝ), Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1) :=
    Real.Gamma_eq_integral (by positivity)
  have h2 : (∫ x in Ioi (0:ℝ), Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1))
      = ∫ x in Ioi (0:ℝ), Real.exp (-x) * x ^ j := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    simp only [add_sub_cancel_right, Real.rpow_natCast]
  rw [h2, Real.Gamma_nat_eq_factorial] at h
  exact h.symm

theorem integrableOn_exp_neg_mul_pow_unit (j : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ j) (Ioi 0) volume := by
  have hbase : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1)) (Ioi 0) volume :=
    Real.GammaIntegral_convergent (by positivity)
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [add_sub_cancel_right, Real.rpow_natCast]

theorem integrableOn_pow_mul_exp (j : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => s ^ j * Real.exp (-(c * s))) (Ioi 0) volume := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hscale : IntegrableOn (fun s : ℝ => Real.exp (-(c * s)) * (c * s) ^ j) (Ioi 0) volume := by
    refine (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x) * x ^ j) 0 hc).mpr ?_
    rw [mul_zero]
    exact integrableOn_exp_neg_mul_pow_unit j
  have hconst : IntegrableOn
      (fun s : ℝ => (c ^ j)⁻¹ * (Real.exp (-(c * s)) * (c * s) ^ j)) (Ioi 0) volume :=
    hscale.const_mul ((c ^ j)⁻¹)
  refine hconst.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [mul_pow]
  first
  | (field_simp; ring)
  | field_simp

theorem integral_pow_mul_exp (j : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ s in Ioi (0:ℝ), s ^ j * Real.exp (-(c * s))) = (j.factorial : ℝ) / c ^ (j + 1) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hsub := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x) * x ^ j) 0 hc
  rw [mul_zero, integral_exp_neg_mul_pow_unit, smul_eq_mul] at hsub
  have hL : (∫ s in Ioi (0:ℝ), Real.exp (-(c * s)) * (c * s) ^ j)
      = c ^ j * ∫ s in Ioi (0:ℝ), s ^ j * Real.exp (-(c * s)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    simp only [mul_pow]
    ring
  rw [hL] at hsub
  rw [eq_div_iff (by positivity : (c : ℝ) ^ (j + 1) ≠ 0), pow_succ]
  calc (∫ s in Ioi (0:ℝ), s ^ j * Real.exp (-(c * s))) * (c ^ j * c)
      = (c ^ j * ∫ s in Ioi (0:ℝ), s ^ j * Real.exp (-(c * s))) * c := by ring
    _ = (c⁻¹ * (j.factorial : ℝ)) * c := by rw [hsub]
    _ = (j.factorial : ℝ) := by field_simp

/-! ## §4. Integrability of the moment integrand -/

theorem neg_pow_two_mul (m : ℕ) (s : ℝ) : (-s) ^ (2 * m) = s ^ (2 * m) := by
  rw [pow_mul, pow_mul, neg_sq]

theorem integrableOn_moment (m : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ (2 * m) * sechKer s) (Ioi 0) volume := by
  have hpi := Real.pi_pos
  have hmaj : IntegrableOn
      (fun s : ℝ => (4 * Real.pi ^ 2) * (s ^ (2 * m) * Real.exp (-(2 * Real.pi * s))))
      (Ioi 0) volume :=
    (integrableOn_pow_mul_exp (2 * m) (by positivity : (0:ℝ) < 2 * Real.pi)).const_mul _
  refine Integrable.mono' hmaj
    (((continuous_pow (2 * m)).mul continuous_sechKer).aestronglyMeasurable) ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with s hs
  have hs0 : (0:ℝ) < s := hs
  have habs : |s| = s := abs_of_pos hs0
  have hker : sechKer s ≤ 4 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi * s)) := by
    have := sechKer_le s
    rwa [habs] at this
  have hpow : (0:ℝ) ≤ s ^ (2 * m) := by positivity
  have hnn : (0:ℝ) ≤ s ^ (2 * m) * sechKer s := mul_nonneg hpow (sechKer_nonneg s)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  nlinarith [hker, hpow]

theorem integrable_moment (m : ℕ) : Integrable (fun s : ℝ => s ^ (2 * m) * sechKer s) volume :=
  integrable_of_even (fun s => by rw [neg_pow_two_mul, sechKer_even]) (integrableOn_moment m)

theorem integrable_sechKer : Integrable sechKer volume := by
  have h := integrable_moment 0
  simpa using h

/-! ## §5. The geometric expansion of `sech²` and the termwise integration -/

/-- `sech²` in the variable the geometric series wants: `u = e^{−2πs}`. -/
theorem sechKer_eq (s : ℝ) :
    sechKer s = 4 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi * s))
      / (1 + Real.exp (-(2 * Real.pi * s))) ^ 2 := by
  have hE : (0:ℝ) < Real.exp (Real.pi * s) := Real.exp_pos _
  have hE0 : Real.exp (Real.pi * s) ≠ 0 := ne_of_gt hE
  have hEi : (0:ℝ) < (Real.exp (Real.pi * s))⁻¹ := inv_pos.mpr hE
  have hu : Real.exp (-(2 * Real.pi * s))
      = (Real.exp (Real.pi * s))⁻¹ * (Real.exp (Real.pi * s))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hcosh : Real.cosh (Real.pi * s)
      = (Real.exp (Real.pi * s) + (Real.exp (Real.pi * s))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  have hd : (0:ℝ) < Real.exp (Real.pi * s) + (Real.exp (Real.pi * s))⁻¹ := by linarith
  have hd2 : (0:ℝ) < 1 + (Real.exp (Real.pi * s))⁻¹ * (Real.exp (Real.pi * s))⁻¹ := by
    nlinarith [hEi]
  rw [sechKer, hcosh, hu]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

/-- The `k`-th term of the expansion of `s^{2m}·π² sech²(π s)` on `(0,∞)`. -/
noncomputable def G (m k : ℕ) (s : ℝ) : ℝ :=
  (-(4 * Real.pi ^ 2)) * ((-1 : ℝ) ^ k * (k : ℝ))
    * (s ^ (2 * m) * Real.exp (-(2 * Real.pi * (k : ℝ) * s)))

theorem G_zero (m : ℕ) (s : ℝ) : G m 0 s = 0 := by
  rw [G]
  norm_num

theorem hasSum_G {m : ℕ} {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℕ => G m k s) (s ^ (2 * m) * sechKer s) := by
  have hpi := Real.pi_pos
  set u : ℝ := Real.exp (-(2 * Real.pi * s)) with hu
  have hupos : 0 < u := Real.exp_pos _
  have hult : u < 1 := by
    rw [hu, Real.exp_lt_one_iff]
    nlinarith
  have hnorm : ‖(-u : ℝ)‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos hupos]
    exact hult
  have hgeo := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hmul := hgeo.mul_left (-(4 * Real.pi ^ 2) * s ^ (2 * m))
  have hfun : (fun k : ℕ => (-(4 * Real.pi ^ 2) * s ^ (2 * m)) * ((k : ℝ) * (-u) ^ k))
      = fun k : ℕ => G m k s := by
    funext k
    rw [G]
    have hpow : ((-u) ^ k : ℝ) = (-1 : ℝ) ^ k * Real.exp (-(2 * Real.pi * (k : ℝ) * s)) := by
      rw [neg_pow, hu, ← Real.exp_nat_mul]
      congr 2
      ring
    rw [hpow]
    ring
  have hval : (-(4 * Real.pi ^ 2) * s ^ (2 * m)) * ((-u) / (1 - (-u)) ^ 2)
      = s ^ (2 * m) * sechKer s := by
    rw [sechKer_eq s, ← hu, sub_neg_eq_add]
    ring
  rw [hfun, hval] at hmul
  exact hmul

theorem integrableOn_G (m k : ℕ) : IntegrableOn (fun s : ℝ => G m k s) (Ioi 0) volume := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hz : (fun s : ℝ => G m 0 s) = fun _ : ℝ => (0:ℝ) := by funext s; exact G_zero m s
    rw [hz]
    exact integrableOn_zero
  · have hpi := Real.pi_pos
    have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hc : (0:ℝ) < 2 * Real.pi * (k : ℝ) := by positivity
    have h : IntegrableOn
        (fun s : ℝ => ((-(4 * Real.pi ^ 2)) * ((-1 : ℝ) ^ k * (k : ℝ)))
          * (s ^ (2 * m) * Real.exp (-(2 * Real.pi * (k : ℝ) * s)))) (Ioi 0) volume :=
      (integrableOn_pow_mul_exp (2 * m) hc).const_mul _
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp only [G]

theorem integral_G (m k : ℕ) :
    (∫ s in Ioi (0:ℝ), G m k s)
      = (-(4 * Real.pi ^ 2)) * ((-1 : ℝ) ^ k * (k : ℝ))
          * (((2 * m).factorial : ℝ) / (2 * Real.pi * (k : ℝ)) ^ (2 * m + 1)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hz : (fun s : ℝ => G m 0 s) = fun _ : ℝ => (0:ℝ) := by funext s; exact G_zero m s
    rw [hz]
    norm_num
  · have hpi := Real.pi_pos
    have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hc : (0:ℝ) < 2 * Real.pi * (k : ℝ) := by positivity
    have heq : (∫ s in Ioi (0:ℝ), G m k s)
        = ∫ s in Ioi (0:ℝ), ((-(4 * Real.pi ^ 2)) * ((-1 : ℝ) ^ k * (k : ℝ)))
            * (s ^ (2 * m) * Real.exp (-(2 * Real.pi * (k : ℝ) * s))) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x _
      simp only [G]
    rw [heq, integral_const_mul, integral_pow_mul_exp (2 * m) hc]

theorem norm_G (m k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖G m k s‖ = (4 * Real.pi ^ 2 * (k : ℝ))
      * (s ^ (2 * m) * Real.exp (-(2 * Real.pi * (k : ℝ) * s))) := by
  have hpi := Real.pi_pos
  have h1 : |(-(4 * Real.pi ^ 2)) * ((-1 : ℝ) ^ k * (k : ℝ))| = 4 * Real.pi ^ 2 * (k : ℝ) := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2),
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  have h2 : |s ^ (2 * m) * Real.exp (-(2 * Real.pi * (k : ℝ) * s))|
      = s ^ (2 * m) * Real.exp (-(2 * Real.pi * (k : ℝ) * s)) :=
    abs_of_nonneg (by positivity)
  rw [G, Real.norm_eq_abs, abs_mul, h1, h2]

theorem integral_norm_G (m k : ℕ) :
    (∫ s in Ioi (0:ℝ), ‖G m k s‖)
      = (4 * Real.pi ^ 2 * (k : ℝ))
          * (((2 * m).factorial : ℝ) / (2 * Real.pi * (k : ℝ)) ^ (2 * m + 1)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hz : (fun s : ℝ => ‖G m 0 s‖) = fun _ : ℝ => (0:ℝ) := by
      funext s; rw [G_zero, norm_zero]
    rw [hz]
    norm_num
  · have hpi := Real.pi_pos
    have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hc : (0:ℝ) < 2 * Real.pi * (k : ℝ) := by positivity
    have heq : (∫ s in Ioi (0:ℝ), ‖G m k s‖)
        = ∫ s in Ioi (0:ℝ), (4 * Real.pi ^ 2 * (k : ℝ))
            * (s ^ (2 * m) * Real.exp (-(2 * Real.pi * (k : ℝ) * s))) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      exact norm_G m k (le_of_lt hx)
    rw [heq, integral_const_mul, integral_pow_mul_exp (2 * m) hc]

theorem integral_norm_G_eq (m k : ℕ) (hm : m ≠ 0) :
    (∫ s in Ioi (0:ℝ), ‖G m k s‖)
      = (4 * Real.pi ^ 2 * ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m + 1))
          * (1 / (k : ℝ) ^ (2 * m)) := by
  have hpi := Real.pi_pos
  rw [integral_norm_G m k]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Nat.cast_zero, zero_pow (by omega : 2 * m ≠ 0)]
    norm_num
  · have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
    have hp0 : ((2 : ℝ) * Real.pi) ^ (2 * m) ≠ 0 := by positivity
    have hs1 : ((2 * Real.pi * (k : ℝ)) ^ (2 * m + 1) : ℝ)
        = ((2 * Real.pi) ^ (2 * m) * (2 * Real.pi)) * ((k : ℝ) ^ (2 * m) * (k : ℝ)) := by
      rw [mul_pow, pow_succ, pow_succ]
    have hs2 : ((2 * Real.pi) ^ (2 * m + 1) : ℝ) = (2 * Real.pi) ^ (2 * m) * (2 * Real.pi) :=
      pow_succ _ _
    rw [hs1, hs2]
    first
    | (field_simp; ring)
    | field_simp

theorem summable_integral_norm_G {m : ℕ} (hm : m ≠ 0) :
    Summable (fun k : ℕ => ∫ s in Ioi (0:ℝ), ‖G m k s‖) := by
  have hb : Summable (fun k : ℕ => (1:ℝ) / (k : ℝ) ^ (2 * m)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hmul := hb.mul_left
    (4 * Real.pi ^ 2 * ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m + 1))
  refine hmul.congr ?_
  intro k
  exact (integral_norm_G_eq m k hm).symm

theorem integral_moment_Ioi {m : ℕ} (hm : m ≠ 0) :
    (∫ s in Ioi (0:ℝ), s ^ (2 * m) * sechKer s) = ∑' k : ℕ, ∫ s in Ioi (0:ℝ), G m k s := by
  have h := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0:ℝ))) (F := fun k : ℕ => fun s : ℝ => G m k s)
    (fun k => integrableOn_G m k) (summable_integral_norm_G hm)
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro s hs
  exact ((hasSum_G (m := m) hs).tsum_eq).symm

/-! ## §6. Route C — the alternating zeta value, already at `B_{2m}(½)` -/

theorem eval_bernoulli_half_real (j : ℕ) :
    Polynomial.eval (1/2 : ℝ) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli j))
      = (((Polynomial.bernoulli j).eval (1/2 : ℚ) : ℚ) : ℝ) := by
  rw [Polynomial.eval_map]
  have hcast : (1/2 : ℝ) = (algebraMap ℚ ℝ) (1/2 : ℚ) := by
    rw [eq_ratCast]; norm_num
  rw [hcast, Polynomial.eval₂_at_apply, eq_ratCast]

theorem hasSum_alt {m : ℕ} (hm : m ≠ 0) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (k : ℝ) ^ (2 * m))
      ((-1 : ℝ) ^ (m + 1) * (2 * Real.pi) ^ (2 * m) / 2 / (((2 * m).factorial : ℕ) : ℝ)
        * (((Polynomial.bernoulli (2 * m)).eval (1/2 : ℚ) : ℚ) : ℝ)) := by
  have hx : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    constructor <;> norm_num
  have h := hasSum_one_div_nat_pow_mul_cos (k := m) hm hx
  have hfun : (fun n : ℕ => 1 / (n : ℝ) ^ (2 * m) * Real.cos (2 * Real.pi * (n : ℝ) * (1/2 : ℝ)))
      = fun n : ℕ => (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * m) := by
    funext n
    have harg : 2 * Real.pi * (n : ℝ) * (1/2 : ℝ) = (n : ℝ) * Real.pi := by ring
    rw [harg, Real.cos_nat_mul_pi]
    ring
  rw [hfun, eval_bernoulli_half_real] at h
  exact h

/-! ## §7. The `m = 0` branch — route A at its one easy instance -/

theorem hasDerivAt_tanhPi (s : ℝ) :
    HasDerivAt (fun x : ℝ => Real.pi * Real.tanh (Real.pi * x)) (sechKer s) s := by
  have hcosh : Real.cosh (Real.pi * s) ≠ 0 := (Real.cosh_pos _).ne'
  have htanh : HasDerivAt Real.tanh (1 / Real.cosh (Real.pi * s) ^ 2) (Real.pi * s) := by
    have h := (Real.hasDerivAt_sinh (Real.pi * s)).div
      (Real.hasDerivAt_cosh (Real.pi * s)) hcosh
    have heq : (Real.sinh / Real.cosh) = Real.tanh := by
      funext x
      rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
    rw [heq] at h
    have hone : Real.cosh (Real.pi * s) * Real.cosh (Real.pi * s)
        - Real.sinh (Real.pi * s) * Real.sinh (Real.pi * s) = 1 := by
      have h2 := Real.cosh_sq_sub_sinh_sq (Real.pi * s)
      rw [pow_two, pow_two] at h2
      exact h2
    rw [hone] at h
    exact h
  have hinner : HasDerivAt (fun x : ℝ => Real.pi * x) Real.pi s := by
    simpa using (hasDerivAt_id s).const_mul Real.pi
  have hcomp := htanh.comp s hinner
  have h2 := hcomp.const_mul Real.pi
  have h3 : HasDerivAt (fun x : ℝ => Real.pi * Real.tanh (Real.pi * x))
      (Real.pi * (1 / Real.cosh (Real.pi * s) ^ 2 * Real.pi)) s := h2
  convert h3 using 1
  rw [sechKer]
  ring

theorem tanh_eq_one_sub (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
  have hx : (0:ℝ) < Real.exp x := Real.exp_pos x
  have hx0 : Real.exp x ≠ 0 := ne_of_gt hx
  have h1 : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have hden : (0:ℝ) < Real.exp x + Real.exp (-x) := by
    have := Real.exp_pos (-x); linarith
  rw [Real.tanh_eq, h1, h2]
  first
  | (field_simp; ring)
  | field_simp

theorem tanh_eq_exp_sub (x : ℝ) :
    Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  have hx : (0:ℝ) < Real.exp x := Real.exp_pos x
  have hx0 : Real.exp x ≠ 0 := ne_of_gt hx
  have h1 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  have hden : (0:ℝ) < Real.exp x + Real.exp (-x) := by
    have := Real.exp_pos (-x); linarith
  rw [Real.tanh_eq, h1, Real.exp_neg]
  first
  | (field_simp; ring)
  | field_simp

theorem tendsto_two_mul_atTop : Tendsto (fun x : ℝ => 2 * x) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro b
  refine ⟨|b|, fun a ha => ?_⟩
  have h1 : (0:ℝ) ≤ |b| := abs_nonneg b
  have h2 : b ≤ |b| := le_abs_self b
  linarith

theorem tendsto_two_mul_atBot : Tendsto (fun x : ℝ => 2 * x) atBot atBot := by
  refine Filter.tendsto_atBot_atBot.mpr ?_
  intro b
  refine ⟨-|b|, fun a ha => ?_⟩
  have h1 : (0:ℝ) ≤ |b| := abs_nonneg b
  have h2 : -|b| ≤ b := neg_abs_le b
  linarith

theorem tendsto_tanh_atTop : Tendsto Real.tanh atTop (nhds 1) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_two_mul_atTop
  have hlim : Tendsto (fun x : ℝ => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))))
      atTop (nhds ((1 - 0) / (1 + 0))) :=
    Filter.Tendsto.div (tendsto_const_nhds.sub hexp) (tendsto_const_nhds.add hexp) (by norm_num)
  have heq : Real.tanh = fun x : ℝ => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
    funext x; exact tanh_eq_one_sub x
  rw [heq]
  simpa using hlim

theorem tendsto_tanh_atBot : Tendsto Real.tanh atBot (nhds (-1)) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (2 * x)) atBot (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_two_mul_atBot
  have hlim : Tendsto (fun x : ℝ => (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1))
      atBot (nhds ((0 - 1) / (0 + 1))) :=
    Filter.Tendsto.div (hexp.sub tendsto_const_nhds) (hexp.add tendsto_const_nhds) (by norm_num)
  have heq : Real.tanh = fun x : ℝ => (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
    funext x; exact tanh_eq_exp_sub x
  rw [heq]
  simpa using hlim

theorem tendsto_pi_mul_tanh_atTop :
    Tendsto (fun x : ℝ => Real.pi * Real.tanh (Real.pi * x)) atTop (nhds Real.pi) := by
  have hpi := Real.pi_pos
  have hinner : Tendsto (fun x : ℝ => Real.pi * x) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr ?_
    intro b
    refine ⟨|b| / Real.pi + |b|, fun a ha => ?_⟩
    have h1 : (0:ℝ) ≤ |b| := abs_nonneg b
    have h2 : b ≤ |b| := le_abs_self b
    have h3 : (0:ℝ) ≤ |b| / Real.pi := by positivity
    have h4 : |b| / Real.pi ≤ a := by linarith
    have h5 : Real.pi * (|b| / Real.pi) ≤ Real.pi * a :=
      mul_le_mul_of_nonneg_left h4 hpi.le
    rw [mul_div_cancel₀ _ (ne_of_gt hpi)] at h5
    linarith
  have h := tendsto_tanh_atTop.comp hinner
  have h2 := h.const_mul Real.pi
  simpa using h2

theorem tendsto_pi_mul_tanh_atBot :
    Tendsto (fun x : ℝ => Real.pi * Real.tanh (Real.pi * x)) atBot (nhds (-Real.pi)) := by
  have hpi := Real.pi_pos
  have hinner : Tendsto (fun x : ℝ => Real.pi * x) atBot atBot := by
    refine Filter.tendsto_atBot_atBot.mpr ?_
    intro b
    refine ⟨-(|b| / Real.pi) - |b|, fun a ha => ?_⟩
    have h1 : (0:ℝ) ≤ |b| := abs_nonneg b
    have h2 : -|b| ≤ b := neg_abs_le b
    have h3 : (0:ℝ) ≤ |b| / Real.pi := by positivity
    have h4 : a ≤ -(|b| / Real.pi) := by linarith
    have h5 : Real.pi * a ≤ Real.pi * (-(|b| / Real.pi)) :=
      mul_le_mul_of_nonneg_left h4 hpi.le
    rw [mul_neg, mul_div_cancel₀ _ (ne_of_gt hpi)] at h5
    linarith
  have h := tendsto_tanh_atBot.comp hinner
  have h2 := h.const_mul Real.pi
  simpa using h2

/-- The `m = 0` instance: `∫ℝ π² sech²(π s) ds = 2π`. -/
theorem table_zero : (∫ s : ℝ, sechKer s) = 2 * Real.pi := by
  have h := integral_of_hasDerivAt_of_tendsto
    (f := fun x : ℝ => Real.pi * Real.tanh (Real.pi * x)) (f' := sechKer)
    (m := -Real.pi) (n := Real.pi)
    (fun x => hasDerivAt_tanhPi x) integrable_sechKer
    tendsto_pi_mul_tanh_atBot tendsto_pi_mul_tanh_atTop
  rw [h]
  ring

/-! ## §8. The table -/

theorem hasSum_integral_G {m : ℕ} (hm : m ≠ 0) :
    HasSum (fun k : ℕ => ∫ s in Ioi (0:ℝ), G m k s)
      ((-1 : ℝ) ^ m * Real.pi * (((Polynomial.bernoulli (2 * m)).eval (1/2 : ℚ) : ℚ) : ℝ)) := by
  have hpi := Real.pi_pos
  have hfacpos : (0:ℝ) < (((2 * m).factorial : ℕ) : ℝ) := by
    exact_mod_cast (2 * m).factorial_pos
  have hfac : (((2 * m).factorial : ℕ) : ℝ) ≠ 0 := ne_of_gt hfacpos
  have hp0 : ((2 : ℝ) * Real.pi) ^ (2 * m) ≠ 0 := by positivity
  set K : ℝ := -(4 * Real.pi ^ 2) * (((2 * m).factorial : ℕ) : ℝ) / (2 * Real.pi) ^ (2 * m + 1)
    with hK
  have hz := (hasSum_alt hm).mul_left K
  have hfun : (fun k : ℕ => K * ((-1 : ℝ) ^ k / (k : ℝ) ^ (2 * m)))
      = fun k : ℕ => ∫ s in Ioi (0:ℝ), G m k s := by
    funext k
    rw [integral_G m k]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [Nat.cast_zero, zero_pow (by omega : 2 * m ≠ 0)]
      norm_num
    · have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
      have hs1 : ((2 * Real.pi * (k : ℝ)) ^ (2 * m + 1) : ℝ)
          = ((2 * Real.pi) ^ (2 * m) * (2 * Real.pi)) * ((k : ℝ) ^ (2 * m) * (k : ℝ)) := by
        rw [mul_pow, pow_succ, pow_succ]
      have hs2 : ((2 * Real.pi) ^ (2 * m + 1) : ℝ) = (2 * Real.pi) ^ (2 * m) * (2 * Real.pi) :=
        pow_succ _ _
      rw [hK, hs1, hs2]
      first
      | (field_simp; ring)
      | field_simp
  have hval : K * ((-1 : ℝ) ^ (m + 1) * (2 * Real.pi) ^ (2 * m) / 2
        / (((2 * m).factorial : ℕ) : ℝ)
      * (((Polynomial.bernoulli (2 * m)).eval (1/2 : ℚ) : ℚ) : ℝ))
      = (-1 : ℝ) ^ m * Real.pi * (((Polynomial.bernoulli (2 * m)).eval (1/2 : ℚ) : ℚ) : ℝ) := by
    have hs2 : ((2 * Real.pi) ^ (2 * m + 1) : ℝ) = (2 * Real.pi) ^ (2 * m) * (2 * Real.pi) :=
      pow_succ _ _
    have hs3 : ((-1 : ℝ) ^ (m + 1)) = (-1 : ℝ) ^ m * (-1 : ℝ) := pow_succ _ _
    rw [hK, hs2, hs3]
    first
    | (field_simp; ring)
    | field_simp
  rw [hfun, hval] at hz
  exact hz

/-- **`SechMomentTable`, PROVED.**  `∫ℝ s^{2m}·π² sech²(π s) ds = (−1)^m·2π·B_{2m}(½)`, at every
`m : ℕ`, with no hypothesis.  This is the body of `Zeta2L7IdMoment.SechMomentTable`, spelled
here in bare Mathlib vocabulary; `Zeta2SechBridge` discharges that `Prop` from it. -/
theorem sech_moment_table (m : ℕ) :
    (∫ s : ℝ, s ^ (2 * m) * (Real.pi ^ 2 / Real.cosh (Real.pi * s) ^ 2))
      = (-1 : ℝ) ^ m * (2 * Real.pi)
          * (((Polynomial.bernoulli (2 * m)).eval (1/2 : ℚ) : ℚ) : ℝ) := by
  have hker : (fun s : ℝ => s ^ (2 * m) * (Real.pi ^ 2 / Real.cosh (Real.pi * s) ^ 2))
      = fun s : ℝ => s ^ (2 * m) * sechKer s := rfl
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hb : (((Polynomial.bernoulli (2 * 0)).eval (1/2 : ℚ) : ℚ) : ℝ) = 1 := by
      norm_num
    rw [hker, hb]
    simp only [Nat.mul_zero, pow_zero, one_mul, mul_one]
    exact table_zero
  · rw [hker, integral_even (fun s => by rw [neg_pow_two_mul, sechKer_even])
      (integrable_moment m), integral_moment_Ioi hm.ne', (hasSum_integral_G hm.ne').tsum_eq]
    ring

end Zeta2SechMoment

/-! ## RECEIPTS — the footprint AND the type, for every theorem (LEAN.md §1).

No theorem in this file carries a hypothesis beyond the `m ≠ 0` / `0 < s` / `0 < c` its type
prints, and `sech_moment_table` carries none at all — read the `#check` lines. -/

#print axioms Zeta2SechMoment.sechKer_even
#check @Zeta2SechMoment.sechKer_even
#print axioms Zeta2SechMoment.sechKer_nonneg
#check @Zeta2SechMoment.sechKer_nonneg
#print axioms Zeta2SechMoment.continuous_sechKer
#check @Zeta2SechMoment.continuous_sechKer
#print axioms Zeta2SechMoment.exp_abs_le_two_mul_cosh
#check @Zeta2SechMoment.exp_abs_le_two_mul_cosh
#print axioms Zeta2SechMoment.sechKer_le
#check @Zeta2SechMoment.sechKer_le
#print axioms Zeta2SechMoment.integrable_of_even
#check @Zeta2SechMoment.integrable_of_even
#print axioms Zeta2SechMoment.integral_even
#check @Zeta2SechMoment.integral_even
#print axioms Zeta2SechMoment.integral_exp_neg_mul_pow_unit
#check @Zeta2SechMoment.integral_exp_neg_mul_pow_unit
#print axioms Zeta2SechMoment.integrableOn_exp_neg_mul_pow_unit
#check @Zeta2SechMoment.integrableOn_exp_neg_mul_pow_unit
#print axioms Zeta2SechMoment.integrableOn_pow_mul_exp
#check @Zeta2SechMoment.integrableOn_pow_mul_exp
#print axioms Zeta2SechMoment.integral_pow_mul_exp
#check @Zeta2SechMoment.integral_pow_mul_exp
#print axioms Zeta2SechMoment.neg_pow_two_mul
#check @Zeta2SechMoment.neg_pow_two_mul
#print axioms Zeta2SechMoment.integrableOn_moment
#check @Zeta2SechMoment.integrableOn_moment
#print axioms Zeta2SechMoment.integrable_moment
#check @Zeta2SechMoment.integrable_moment
#print axioms Zeta2SechMoment.integrable_sechKer
#check @Zeta2SechMoment.integrable_sechKer
#print axioms Zeta2SechMoment.sechKer_eq
#check @Zeta2SechMoment.sechKer_eq
#print axioms Zeta2SechMoment.G_zero
#check @Zeta2SechMoment.G_zero
#print axioms Zeta2SechMoment.hasSum_G
#check @Zeta2SechMoment.hasSum_G
#print axioms Zeta2SechMoment.integrableOn_G
#check @Zeta2SechMoment.integrableOn_G
#print axioms Zeta2SechMoment.integral_G
#check @Zeta2SechMoment.integral_G
#print axioms Zeta2SechMoment.norm_G
#check @Zeta2SechMoment.norm_G
#print axioms Zeta2SechMoment.integral_norm_G
#check @Zeta2SechMoment.integral_norm_G
#print axioms Zeta2SechMoment.integral_norm_G_eq
#check @Zeta2SechMoment.integral_norm_G_eq
#print axioms Zeta2SechMoment.summable_integral_norm_G
#check @Zeta2SechMoment.summable_integral_norm_G
#print axioms Zeta2SechMoment.integral_moment_Ioi
#check @Zeta2SechMoment.integral_moment_Ioi
#print axioms Zeta2SechMoment.eval_bernoulli_half_real
#check @Zeta2SechMoment.eval_bernoulli_half_real
#print axioms Zeta2SechMoment.hasSum_alt
#check @Zeta2SechMoment.hasSum_alt
#print axioms Zeta2SechMoment.hasDerivAt_tanhPi
#check @Zeta2SechMoment.hasDerivAt_tanhPi
#print axioms Zeta2SechMoment.tanh_eq_one_sub
#check @Zeta2SechMoment.tanh_eq_one_sub
#print axioms Zeta2SechMoment.tanh_eq_exp_sub
#check @Zeta2SechMoment.tanh_eq_exp_sub
#print axioms Zeta2SechMoment.tendsto_tanh_atTop
#check @Zeta2SechMoment.tendsto_tanh_atTop
#print axioms Zeta2SechMoment.tendsto_tanh_atBot
#check @Zeta2SechMoment.tendsto_tanh_atBot
#print axioms Zeta2SechMoment.tendsto_pi_mul_tanh_atTop
#check @Zeta2SechMoment.tendsto_pi_mul_tanh_atTop
#print axioms Zeta2SechMoment.tendsto_pi_mul_tanh_atBot
#check @Zeta2SechMoment.tendsto_pi_mul_tanh_atBot
#print axioms Zeta2SechMoment.table_zero
#check @Zeta2SechMoment.table_zero
#print axioms Zeta2SechMoment.hasSum_integral_G
#check @Zeta2SechMoment.hasSum_integral_G
#print axioms Zeta2SechMoment.sech_moment_table
#check @Zeta2SechMoment.sech_moment_table
