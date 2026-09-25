/-
Row L7ID: the `m`-SUMMATION, the two arms' SEPARATE integrability, and the first statement
anywhere in the chain about `Zeta2Defs.candidateM.rn` — `docs/future/zeta2-lean-chain.md`.

WHAT THIS FILE PROVES, in the order the row needs it.

1.  THE `m`-SUMMATION.  `Zeta2L7IdTermVal` evaluated each `∫ F n m` and stopped; this file sums
    them.  The family is supported on `m ≤ 4n`, so the `ℤ`-indexed `tsum` reindexes along
    `i ↦ 4n − i` and every window pole's tail is a harmonic remainder:

      tsum_integral_F (n) : ∑' m : ℤ, ∫ s, F n m s
        = ∑ k ∈ window n, ↑(Pin n * ck n k) * ↑(2π * (zeta2 − harm 2 (harmIndex n k)))

    with `harmIndex n k = k − 4n − 1` the CHAIN's own index (`Zeta2L7IdTermVal.harmIndex_eq`),
    not a lookalike.  Composed with obligation 3 this gives the RESID arm's contour integral in
    closed form, `integral_ResidArm_lineA_eq`.

2.  THE TWO ARMS ARE SEPARATELY INTEGRABLE, which the split did not give.  The RESID arm is
    bounded by `2·C n·(π/cosh πs)²` — the finite `k`-sum's denominators are all at least `½`
    from the contour — and `(π/cosh πs)² ≤ 4π²e^{−2π|s|}`, so `L7MidM6.integrable_of_exp_decay`
    applies with NO hypothesis on `n`.  The `Ppol` arm is then `H_n − ResidArm`, which needs
    `1 ≤ n` only because `integrable_Hn_lineA` does.  That is what licenses `integral_add`, and
    so `integral_Hn_lineA_split`.

3.  THE IDENTIFICATION WITH `candidateM.rn`, and it is UNCONDITIONAL:

      rn_add_rLine (hn : 1 ≤ n) : candidateM.rn n + L7MidM5.rLine n
        = (1/(2π)) * (∫ s, PpolArm n (lineA n s)).re − ↑(Pin n * pnPoly n)

    Up to here nothing in the chain mentioned `candidateM.rn` at all, which is why RDECAY was
    blocked; the sign is the convention clash the row has carried since 2026-09-14, and it now
    comes out of `sgn ≡ −1` rather than being asserted.  The row's target follows as an
    EQUIVALENCE, `rn_eq_neg_rLine_iff`, so the whole residue of L7ID is the single named `Prop`
    `PpolMomentValue n` — the `Ppol` arm's moment, whose remaining analytic content is
    `Zeta2L7IdMoment.SechMomentTable`.

WHERE THE ALGEBRA COMES FROM.  `Pin·∑_k ck = −qn` (because `sgn ≡ −1` at the candidate, `dsum =
16`), `pnHarm = ∑_k ck·harm 2 (harmIndex)` and `pn = Pin·(pnPoly − pnHarm)`, so

  residSum n := ∑_k ↑(Pin·ck)·(ζ(2) − ↑(harm 2 (harmIndex n k))) = −rn n − ↑(Pin n · pnPoly n)

exactly (`residSum_eq`) — one line of ℚ-algebra against the definitions, no analysis.

WHAT THIS FILE DOES NOT DO.  `PpolMomentValue n` is TAKEN, not proved: it is the `Ppol` arm's
value, and its own residue is the `n`-independent `SechMomentTable`.  Obligation 2, the row's
decay ESTIMATE, is untouched — `residSum` is an identity, not a rate.  So L7ID does not close.
The hypothesis's sign is MEASURED rather than assumed (`l7id_sum_check.py` ARM 5, at `n = 1` and
`n = 2`, two precisions each, with a sign-flip falsifier in ARM 6): a theorem conditional on a
FALSE hypothesis is vacuous and elaborates clean, and `#print axioms` cannot see a binder.

ACCEPTANCE (LEAN.md §1, as sharpened 2026-09-20): the receipt AND the printed type.  Every
theorem prints both, and the two that carry a hypothesis say so in their own docstring.

Elaborate: sh external_tests/zeta2_arith/run_probe.sh Zeta2L7IdSum.lean
Falsifier:  bash external_tests/zeta2_arith/falsify_l7idsum.sh
Second implementation: python3 external_tests/zeta2_arith/l7id_sum_check.py

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2
         mathlib   5aedf732b6987e8c26ab3c9ebc855314f82b045f
-/
import Mathlib
import Zeta2L7IdTermVal

namespace Zeta2L7IdSum

open MeasureTheory Complex Finset
open Zeta2Defs

/-! ## §1. The harmonic tail

`hasSum_zeta2` is `∑'_{j : ℕ} 1/j² = ζ(2)` with the `j = 0` term `1/0 = 0`, so the tail from `d`
is `ζ(2)` minus the first `d` terms, and those are exactly `harm 2 (d − 1)`. -/

/-- `harm` is Mathlib's sum, cast. -/
theorem harm_cast (e : ℕ) :
    ((harm 2 e : ℚ) : ℝ) = ∑ i ∈ range e, 1 / ((i : ℝ) + 1) ^ 2 := by
  rw [harm]
  push_cast
  rfl

/-- The first `e + 1` terms of `∑ 1/j²` are `harm 2 e`: the `j = 0` term is `1/0 = 0`. -/
theorem sum_range_inv_sq (e : ℕ) :
    ∑ i ∈ range (e + 1), 1 / ((i : ℕ) : ℝ) ^ 2 = ((harm 2 e : ℚ) : ℝ) := by
  rw [Finset.sum_range_succ', harm_cast]
  push_cast
  simp

/-- **The harmonic tail.**  `∑'_{i : ℕ} 1/(i + d)² = ζ(2) − harm 2 (d − 1)` for `1 ≤ d`. -/
theorem hasSum_tail {d : ℕ} (hd : 1 ≤ d) :
    HasSum (fun i : ℕ => 1 / (((i + d : ℕ) : ℝ)) ^ 2)
      (zeta2 - ((harm 2 (d - 1) : ℚ) : ℝ)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  refine (hasSum_nat_add_iff (f := fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ 2) (e + 1)).mpr ?_
  have hs : ∑ i ∈ range (e + 1), 1 / ((i : ℕ) : ℝ) ^ 2 = ((harm 2 e : ℚ) : ℝ) :=
    sum_range_inv_sq e
  simp only [Nat.add_sub_cancel, hs]
  have : zeta2 - ((harm 2 e : ℚ) : ℝ) + ((harm 2 e : ℚ) : ℝ) = zeta2 := by ring
  rw [this]
  exact hasSum_zeta2

/-! ## §2. One window pole's `m`-sum

`k ≥ 15n + 1` on the window, so `d = k − 4n ≥ 11n + 1 ≥ 1`: every tail is a genuine tail and no
window fact beyond that lower bound is used. -/

theorem window_lower {n k : ℕ} (hk : k ∈ candidateM.window n) : 15 * n + 1 ≤ k := by
  rw [Member.window, Finset.mem_Icc] at hk
  simpa [candidateM] using hk.1

theorem harmIndex_succ {n k : ℕ} (hk : k ∈ candidateM.window n) :
    k - 4 * n = candidateM.harmIndex n k + 1 := by
  have h := window_lower hk
  rw [Zeta2L7IdTermVal.harmIndex_eq]
  omega

/-- The abscissa bookkeeping: at `m = 4n − i` the pole gap `k − m` is the natural `k − 4n + i`. -/
theorem gap_eq {n k : ℕ} (hk : k ∈ candidateM.window n) (i : ℕ) :
    ((k : ℝ) - ((4 * (n : ℤ) - (i : ℤ) : ℤ) : ℝ)) = ((i + (k - 4 * n) : ℕ) : ℝ) := by
  have h := window_lower hk
  have hle : 4 * n ≤ k := by omega
  push_cast [Nat.cast_sub hle]
  ring

/-- **One window pole's whole `m`-sum**, in exactly the shape `integral_F_eq` produces. -/
theorem hasSum_window_term {n k : ℕ} (hk : k ∈ candidateM.window n) :
    HasSum (fun i : ℕ =>
        ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
          * ((2 * Real.pi / ((k : ℝ) - ((4 * (n : ℤ) - (i : ℤ) : ℤ) : ℝ)) ^ 2 : ℝ) : ℂ))
      (((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
        * ((2 * Real.pi
            * (zeta2 - ((harm 2 (candidateM.harmIndex n k) : ℚ) : ℝ)) : ℝ) : ℂ)) := by
  have h := window_lower hk
  have hd : 1 ≤ k - 4 * n := by omega
  have hbase := hasSum_tail hd
  -- Rewrite only the TAIL INDEX `d − 1 = harmIndex n k`, never the summand's `k − 4n`:
  -- `rw [harmIndex_succ hk]` rewrites both and the summand then no longer matches (measured).
  rw [show k - 4 * n - 1 = candidateM.harmIndex n k from
    (Zeta2L7IdTermVal.harmIndex_eq n k).symm] at hbase
  -- Scale by `2π` in ℝ (where `ring` can move the division), cast to ℂ, then scale by the
  -- residue.  Deliberately NO `norm_num` anywhere near the goal: `Pin`/`ck` are factorial
  -- quotients and `norm_num` tries to EVALUATE them — measured on this file's first
  -- elaboration as a `whnf` heartbeat timeout at this very theorem.
  have hR : HasSum (fun i : ℕ => 2 * Real.pi / (((i + (k - 4 * n) : ℕ) : ℝ)) ^ 2)
      (2 * Real.pi * (zeta2 - ((harm 2 (candidateM.harmIndex n k) : ℚ) : ℝ))) := by
    have h := hbase.mul_left (2 * Real.pi)
    have hfun : (fun i : ℕ => 2 * Real.pi * (1 / (((i + (k - 4 * n) : ℕ) : ℝ)) ^ 2))
        = fun i : ℕ => 2 * Real.pi / (((i + (k - 4 * n) : ℕ) : ℝ)) ^ 2 := by
      funext i
      ring
    rwa [hfun] at h
  have hC := Complex.ofRealCLM.hasSum hR
  have hfin := hC.mul_left ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
  have heq : (fun i : ℕ =>
        ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
          * ((2 * Real.pi / ((k : ℝ) - ((4 * (n : ℤ) - (i : ℤ) : ℤ) : ℝ)) ^ 2 : ℝ) : ℂ))
      = fun i : ℕ =>
        ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
          * ((2 * Real.pi / (((i + (k - 4 * n) : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
    funext i
    rw [gap_eq hk i]
  rw [heq]
  exact hfin

/-! ## §3. The `m`-summation

The support is `m ≤ 4n` (`integral_F_eq_zero`), so the `ℤ`-sum reindexes along the injection
`i ↦ 4n − i` and becomes the `ℕ`-sum §2 computes termwise. -/

/-- The closed form's right-hand side, as a REAL number: the chain's own harmonic sum. -/
noncomputable def residSum (n : ℕ) : ℝ :=
  ∑ k ∈ candidateM.window n,
    ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℝ)
      * (zeta2 - ((harm 2 (candidateM.harmIndex n k) : ℚ) : ℝ))

/-- The shifted family sums, termwise in `k`. -/
theorem hasSum_shifted (n : ℕ) :
    HasSum (fun i : ℕ => ∫ s : ℝ, Zeta2L7IdResid.F n (4 * (n : ℤ) - (i : ℤ)) s)
      (∑ k ∈ candidateM.window n,
        ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
          * ((2 * Real.pi
              * (zeta2 - ((harm 2 (candidateM.harmIndex n k) : ℚ) : ℝ)) : ℝ) : ℂ)) := by
  have hfun : (fun i : ℕ => ∫ s : ℝ, Zeta2L7IdResid.F n (4 * (n : ℤ) - (i : ℤ)) s)
      = fun i : ℕ => ∑ k ∈ candidateM.window n,
          ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
            * ((2 * Real.pi
                / ((k : ℝ) - ((4 * (n : ℤ) - (i : ℤ) : ℤ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
    funext i
    exact Zeta2L7IdTermVal.integral_F_eq n (by omega)
  rw [hfun]
  exact hasSum_sum fun k hk => hasSum_window_term hk

/-- **THE `m`-SUMMATION.**  The RESID arm's per-`m` integrals sum to the chain's harmonic sum. -/
theorem tsum_integral_F (n : ℕ) :
    (∑' m : ℤ, ∫ s : ℝ, Zeta2L7IdResid.F n m s)
      = ∑ k ∈ candidateM.window n,
          ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
            * ((2 * Real.pi
                * (zeta2 - ((harm 2 (candidateM.harmIndex n k) : ℚ) : ℝ)) : ℝ) : ℂ) := by
  have hinj : Function.Injective (fun i : ℕ => 4 * (n : ℤ) - (i : ℤ)) := by
    intro a b hab
    simp only at hab
    omega
  have hsupp : Function.support (fun m : ℤ => ∫ s : ℝ, Zeta2L7IdResid.F n m s)
      ⊆ Set.range (fun i : ℕ => 4 * (n : ℤ) - (i : ℤ)) := by
    intro m hm
    have hle : m ≤ 4 * (n : ℤ) := by
      by_contra hcon
      push_neg at hcon
      exact hm (Zeta2L7IdTermVal.integral_F_eq_zero n hcon)
    refine ⟨(4 * (n : ℤ) - m).toNat, ?_⟩
    -- the `show` is load-bearing: without it `omega` is handed a BETA-REDEX it cannot see
    -- through and reports a "possible counterexample" (measured, first elaboration).
    show 4 * (n : ℤ) - (((4 * (n : ℤ) - m).toNat : ℕ) : ℤ) = m
    omega
  rw [← hinj.tsum_eq hsupp]
  exact (hasSum_shifted n).tsum_eq

/-- The real-valued spelling of the same sum. -/
theorem sum_eq_ofReal (n : ℕ) :
    (∑ k ∈ candidateM.window n,
        ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
          * ((2 * Real.pi
              * (zeta2 - ((harm 2 (candidateM.harmIndex n k) : ℚ) : ℝ)) : ℝ) : ℂ))
      = ((2 * Real.pi * residSum n : ℝ) : ℂ) := by
  rw [residSum, Finset.mul_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- **THE RESID ARM'S CONTOUR INTEGRAL, IN CLOSED FORM** — obligation 3 composed with §3, at
every `n` and with no hypothesis. -/
theorem integral_ResidArm_lineA_eq (n : ℕ) :
    (∫ s : ℝ, Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s))
      = ((2 * Real.pi * residSum n : ℝ) : ℂ) := by
  rw [Zeta2L7IdResid.integral_ResidArm_lineA n, tsum_integral_F n, sum_eq_ofReal n]

/-! ## §4. The two arms are SEPARATELY integrable

The split (`Zeta2L7IdSplit.Hn_eq_PpolArm_add_ResidArm`) is an identity of values; `integral_add`
needs each arm's own integrability, and that is this section. -/

/-- `(π/cosh πs)² ≤ 4π²e^{−2π|s|}`: `cosh x ≥ e^{|x|}/2`, and `π|s| = |πs|` because `π > 0`. -/
theorem kernel_le (s : ℝ) :
    ((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ)
      ≤ (4 * Real.pi ^ 2) * Real.exp (-(2 * Real.pi) * |s|) := by
  have hpi := Real.pi_pos
  have hcosh := Real.cosh_pos (Real.pi * s)
  have habs : |Real.pi * s| = Real.pi * |s| := by
    rw [abs_mul, abs_of_pos hpi]
  have hlow : Real.exp (Real.pi * |s|) / 2 ≤ Real.cosh (Real.pi * s) := by
    rw [Real.cosh_eq, ← habs]
    rcases abs_choice (Real.pi * s) with h | h <;> rw [h]
    · have := (Real.exp_pos (-(Real.pi * s))).le
      linarith
    · have := (Real.exp_pos (Real.pi * s)).le
      linarith
  have hexp : (0 : ℝ) < Real.exp (Real.pi * |s|) := Real.exp_pos _
  have hstep : Real.pi / Real.cosh (Real.pi * s)
      ≤ 2 * Real.pi * Real.exp (-(Real.pi * |s|)) := by
    -- `div_le_iff₀` rather than `gcongr`: `gcongr` discharged its own side goal from the
    -- context here and the following bullet then errored "No goals to be solved" (measured).
    rw [div_le_iff₀ hcosh, Real.exp_neg]
    have hc : 2 * Real.pi * (Real.exp (Real.pi * |s|))⁻¹ * (Real.exp (Real.pi * |s|) / 2)
        ≤ 2 * Real.pi * (Real.exp (Real.pi * |s|))⁻¹ * Real.cosh (Real.pi * s) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    have hkey : 2 * Real.pi * (Real.exp (Real.pi * |s|))⁻¹ * (Real.exp (Real.pi * |s|) / 2)
        = Real.pi := by
      field_simp
    linarith [hc, hkey.le, hkey.ge]
  have hnn : (0 : ℝ) ≤ Real.pi / Real.cosh (Real.pi * s) := by positivity
  have hsq : (Real.pi / Real.cosh (Real.pi * s)) ^ 2
      ≤ (2 * Real.pi * Real.exp (-(Real.pi * |s|))) ^ 2 := by
    have hpos : (0 : ℝ) ≤ 2 * Real.pi * Real.exp (-(Real.pi * |s|)) := by positivity
    nlinarith [hstep, hnn, hpos]
  have hval : (2 * Real.pi * Real.exp (-(Real.pi * |s|))) ^ 2
      = (4 * Real.pi ^ 2) * Real.exp (-(2 * Real.pi) * |s|) := by
    have : (Real.exp (-(Real.pi * |s|))) ^ 2 = Real.exp (-(2 * Real.pi) * |s|) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [mul_pow, mul_pow, this]
    ring
  linarith [hsq, hval.le, hval.ge]

/-- Every window pole is at least `½` from the cell contour — `Zeta2L7IdResid`'s own bound at
its weakest point, which is all the finite `k`-sum needs. -/
theorem half_le_norm_lineA_add (n k : ℕ) (s : ℝ) :
    (1 : ℝ) / 2 ≤ ‖Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)‖ := by
  have h : Real.sqrt ((1 / 2 : ℝ) ^ 2) ≤ Real.sqrt (s ^ 2 + (1 / 2 : ℝ) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg s]
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
  exact h.trans (Zeta2L7IdResid.sqrt_le_norm_lineA_add_natCast n k s)

theorem lineA_add_ne_zero (n k : ℕ) (s : ℝ) :
    Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ) ≠ 0 := by
  have h := half_le_norm_lineA_add n k s
  intro hz
  rw [hz, norm_zero] at h
  linarith

theorem continuous_ResidArm_lineA (n : ℕ) :
    Continuous (fun s : ℝ => Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s)) := by
  have heq : (fun s : ℝ => Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s))
      = fun s : ℝ => (∑ k ∈ candidateM.window n,
            ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
              / (Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)))
          * (((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ) : ℂ) := by
    funext s
    exact Zeta2L7IdContour.ResidArm_lineA n s
  rw [heq]
  -- `continuous_finset_sum` is DEPRECATED at this pin; `continuous_finsetSum` is the name.
  refine Continuous.mul (continuous_finsetSum _ fun k _ => ?_) ?_
  · exact Continuous.div continuous_const
      ((Zeta2L7IdContour.continuous_lineA n).add continuous_const)
      (fun s => lineA_add_ne_zero n k s)
  · refine Complex.continuous_ofReal.comp (Continuous.pow ?_ 2)
    exact continuous_const.div
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
      (fun s => (Real.cosh_pos _).ne')

/-- **The RESID arm's pointwise bound on the cell contour.**  The finite `k`-sum contributes at
most `2·C n` because every denominator is at least `½`; the kernel supplies all the decay. -/
theorem norm_ResidArm_lineA_le (n : ℕ) (s : ℝ) :
    ‖Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s)‖
      ≤ (2 * Zeta2L7IdResid.C n) * ((Real.pi / Real.cosh (Real.pi * s)) ^ 2) := by
  rw [Zeta2L7IdContour.ResidArm_lineA n s, norm_mul]
  have hker : ‖(((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ) : ℂ)‖
      = (Real.pi / Real.cosh (Real.pi * s)) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsum : ‖∑ k ∈ candidateM.window n,
      ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
        / (Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ))‖ ≤ 2 * Zeta2L7IdResid.C n := by
    refine (norm_sum_le _ _).trans ?_
    rw [Zeta2L7IdResid.C, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_div]
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (half_le_norm_lineA_add n k s))]
    have h := half_le_norm_lineA_add n k s
    nlinarith [norm_nonneg ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)]
  rw [hker]
  exact mul_le_mul_of_nonneg_right hsum (by positivity)

/-- **The RESID arm is integrable on the cell contour, at EVERY `n` and with no hypothesis.** -/
theorem integrable_ResidArm_lineA (n : ℕ) :
    Integrable (fun s : ℝ => Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s)) := by
  have hC := Zeta2L7IdResid.C_nonneg n
  refine L7MidM6.integrable_of_exp_decay (continuous_ResidArm_lineA n)
    (K := (2 * Zeta2L7IdResid.C n) * (4 * Real.pi ^ 2)) (c := 2 * Real.pi)
    (by positivity) ?_
  intro y _
  have h1 := norm_ResidArm_lineA_le n y
  have h2 : (2 * Zeta2L7IdResid.C n) * ((Real.pi / Real.cosh (Real.pi * y)) ^ 2)
      ≤ (2 * Zeta2L7IdResid.C n) * ((4 * Real.pi ^ 2) * Real.exp (-(2 * Real.pi) * |y|)) :=
    mul_le_mul_of_nonneg_left (kernel_le y) (by linarith)
  have h3 : (2 * Zeta2L7IdResid.C n) * ((4 * Real.pi ^ 2) * Real.exp (-(2 * Real.pi) * |y|))
      = (2 * Zeta2L7IdResid.C n) * (4 * Real.pi ^ 2) * Real.exp (-(2 * Real.pi) * |y|) := by
    ring
  linarith [h1, h2, h3.le, h3.ge]

/-- **The `Ppol` arm is integrable at `1 ≤ n`** — as `H_n` minus the RESID arm, so the only
hypothesis is `integrable_Hn_lineA`'s own. -/
theorem integrable_PpolArm_lineA {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun s : ℝ => Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s)) := by
  refine ((Zeta2L7IdContour.integrable_Hn_lineA hn).sub (integrable_ResidArm_lineA n)).congr ?_
  filter_upwards [Zeta2L7IdHinge.ae_ne_zero] with s hs
  -- `Integrable.sub` leaves the goal as an UNREDUCED `(f - g) s`, so `rw` finds no `Hn` to
  -- rewrite until `Pi.sub_apply` fires (measured, first elaboration).
  simp only [Pi.sub_apply]
  rw [Zeta2L7IdContour.Hn_lineA_eq_PpolArm_add_ResidArm n hs]
  ring

/-- **The split, under the integral sign** — the step `integral_add` licenses and the split
alone did not. -/
theorem integral_Hn_lineA_split {n : ℕ} (hn : 1 ≤ n) :
    (∫ s : ℝ, L7MidM123.Hn n (Zeta2L7IdMoment.lineA n s))
      = (∫ s : ℝ, Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s))
        + ∫ s : ℝ, Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s) := by
  rw [← integral_add (integrable_PpolArm_lineA hn) (integrable_ResidArm_lineA n)]
  refine integral_congr_ae ?_
  filter_upwards [Zeta2L7IdHinge.ae_ne_zero] with s hs
  exact Zeta2L7IdContour.Hn_lineA_eq_PpolArm_add_ResidArm n hs

/-! ## §5. The bridge to `candidateM.rn` — ℚ-algebra, no analysis

`sgn ≡ −1` at the candidate because `dsum = 16`, so `Pin·∑ck = −qn` and `pn = Pin·(pnPoly −
pnHarm)`.  `residSum` is then `−rn − Pin·pnPoly` exactly. -/

theorem candidate_dsum : candidateM.dsum = 16 := by decide

/-- `sgn ≡ −1` at the candidate — the `n`-independence L7ID-0 measured, here derived. -/
theorem candidate_sgn (n : ℕ) : candidateM.sgn n = -1 := by
  rw [Member.sgn, candidate_dsum, pow_succ, Even.neg_one_pow ⟨8 * n, by ring⟩]
  ring

theorem Pin_mul_sum_ck (n : ℕ) :
    candidateM.Pin n * ∑ k ∈ candidateM.window n, candidateM.ck n k = -candidateM.qn n := by
  rw [Member.qn, candidate_sgn]
  ring

theorem pn_eq (n : ℕ) :
    candidateM.pn n = candidateM.Pin n * (candidateM.pnPoly n - candidateM.pnHarm n) := by
  rw [Member.pn, candidate_sgn]
  ring

/-- **`residSum` IS `−r_n` minus the `Ppol` coordinate** — the first identity in the chain with
`candidateM.rn` on one side of it. -/
theorem residSum_eq (n : ℕ) :
    residSum n = -candidateM.rn n - ((candidateM.Pin n * candidateM.pnPoly n : ℚ) : ℝ) := by
  have hsplit : residSum n
      = ((candidateM.Pin n * ∑ k ∈ candidateM.window n, candidateM.ck n k : ℚ) : ℝ) * zeta2
        - ((candidateM.Pin n * candidateM.pnHarm n : ℚ) : ℝ) := by
    rw [residSum, Member.pnHarm, Finset.mul_sum, Finset.mul_sum]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, Pin_mul_sum_ck n, Member.rn, pn_eq n]
  push_cast
  ring

/-! ## §6. THE ROW'S TARGET, as an equivalence

Everything above composes to one unconditional identity; the row's statement then holds iff the
`Ppol` arm has its moment value, and that single `Prop` is L7ID's whole remaining VALUE residue
(obligation 2, the estimate, is a separate and untouched obligation). -/

/-- The one obligation left of the `Ppol` arm, named so that a consumer can carry it.  Its
remaining analytic content is `Zeta2L7IdMoment.SechMomentTable`; its VALUE is measured at
`n = 1, 2` in `l7id_sum_check.py` ARM 5 with a sign-flip falsifier in ARM 6. -/
def PpolMomentValue (n : ℕ) : Prop :=
  (1 / (2 * Real.pi))
      * (∫ s : ℝ, Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s)).re
    = ((candidateM.Pin n * candidateM.pnPoly n : ℚ) : ℝ)

/-- **UNCONDITIONAL, AND THE FIRST STATEMENT IN THE CHAIN ABOUT `candidateM.rn`.**  The chain's
linear form and M5's line integral differ by exactly the `Ppol` arm's defect. -/
theorem rn_add_rLine {n : ℕ} (hn : 1 ≤ n) :
    candidateM.rn n + L7MidM5.rLine n
      = (1 / (2 * Real.pi))
          * (∫ s : ℝ, Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s)).re
        - ((candidateM.Pin n * candidateM.pnPoly n : ℚ) : ℝ) := by
  have hpi := Real.pi_pos
  have hr : (∫ s : ℝ, Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s)).re
      = 2 * Real.pi * residSum n := by
    rw [integral_ResidArm_lineA_eq n, Complex.ofReal_re]
  rw [Zeta2L7IdContour.rLine_eq_lineA hn, integral_Hn_lineA_split hn, Complex.add_re, hr,
    mul_add, residSum_eq n]
  field_simp
  ring

/-- **ROW L7ID'S TARGET, as an EQUIVALENCE**: `r_n = −rLine n` holds at `1 ≤ n` exactly when the
`Ppol` arm has its moment value.  So the row's whole VALUE residue is `PpolMomentValue`. -/
theorem rn_eq_neg_rLine_iff {n : ℕ} (hn : 1 ≤ n) :
    candidateM.rn n = -L7MidM5.rLine n ↔ PpolMomentValue n := by
  rw [PpolMomentValue, ← sub_eq_zero (a := candidateM.rn n), sub_neg_eq_add,
    rn_add_rLine hn, sub_eq_zero]

/-- **ROW L7ID'S TARGET, conditional on the one obligation left.**  The hypothesis is a BINDER
and `#print axioms` cannot see it (LEAN.md §1), so it is named here, in the docstring, and in
the `#check` receipt below. -/
theorem rn_eq_neg_rLine {n : ℕ} (hn : 1 ≤ n) (hP : PpolMomentValue n) :
    candidateM.rn n = -L7MidM5.rLine n :=
  (rn_eq_neg_rLine_iff hn).mpr hP

/-! ## §7. EDGES (LEAN.md §5), asked of the real data

At `n = 0` the `Ppol` arm is absent (`Ppol 0 = 0`, so `pnPoly 0 = 0`), which is exactly why
L7ID-0 never met this arm — and it is why `n = 0` is NOT a template for `PpolMomentValue`. -/

theorem pnPoly_zero : candidateM.pnPoly 0 = 0 := by
  -- `Zeta2L7IdSplit.Ppol_zero` is CONSUMED, not recomputed: it derives `Ppol 0 = 0` from
  -- `Ppol_spec` plus RESID's own `n = 0` corollary, and a second division here would be a
  -- second copy of that fact (LEAN.md §6).
  rw [Member.pnPoly, Zeta2L7IdSplit.Ppol_zero]
  simp

/-- At `n = 0` the RESID arm carries the whole of `−r_n`: there is no `Ppol` defect to close. -/
theorem residSum_zero : residSum 0 = -candidateM.rn 0 := by
  rw [residSum_eq 0, pnPoly_zero]
  push_cast
  ring

end Zeta2L7IdSum

/-! ## RECEIPTS — the footprint AND the type, for every theorem (LEAN.md §1).

`#print axioms` is byte-identical for a conditional theorem and an unconditional one, so the
`#check` lines are half the acceptance test, not decoration: `rn_eq_neg_rLine` carries
`PpolMomentValue n` and `rn_add_rLine` carries nothing but `1 ≤ n`. -/

#print axioms Zeta2L7IdSum.harm_cast
#check @Zeta2L7IdSum.harm_cast
#print axioms Zeta2L7IdSum.sum_range_inv_sq
#check @Zeta2L7IdSum.sum_range_inv_sq
#print axioms Zeta2L7IdSum.hasSum_tail
#check @Zeta2L7IdSum.hasSum_tail
#print axioms Zeta2L7IdSum.window_lower
#check @Zeta2L7IdSum.window_lower
#print axioms Zeta2L7IdSum.harmIndex_succ
#check @Zeta2L7IdSum.harmIndex_succ
#print axioms Zeta2L7IdSum.gap_eq
#check @Zeta2L7IdSum.gap_eq
#print axioms Zeta2L7IdSum.hasSum_window_term
#check @Zeta2L7IdSum.hasSum_window_term
#print axioms Zeta2L7IdSum.hasSum_shifted
#check @Zeta2L7IdSum.hasSum_shifted
#print axioms Zeta2L7IdSum.tsum_integral_F
#check @Zeta2L7IdSum.tsum_integral_F
#print axioms Zeta2L7IdSum.sum_eq_ofReal
#check @Zeta2L7IdSum.sum_eq_ofReal
#print axioms Zeta2L7IdSum.integral_ResidArm_lineA_eq
#check @Zeta2L7IdSum.integral_ResidArm_lineA_eq
#print axioms Zeta2L7IdSum.kernel_le
#check @Zeta2L7IdSum.kernel_le
#print axioms Zeta2L7IdSum.half_le_norm_lineA_add
#check @Zeta2L7IdSum.half_le_norm_lineA_add
#print axioms Zeta2L7IdSum.lineA_add_ne_zero
#check @Zeta2L7IdSum.lineA_add_ne_zero
#print axioms Zeta2L7IdSum.continuous_ResidArm_lineA
#check @Zeta2L7IdSum.continuous_ResidArm_lineA
#print axioms Zeta2L7IdSum.norm_ResidArm_lineA_le
#check @Zeta2L7IdSum.norm_ResidArm_lineA_le
#print axioms Zeta2L7IdSum.integrable_ResidArm_lineA
#check @Zeta2L7IdSum.integrable_ResidArm_lineA
#print axioms Zeta2L7IdSum.integrable_PpolArm_lineA
#check @Zeta2L7IdSum.integrable_PpolArm_lineA
#print axioms Zeta2L7IdSum.integral_Hn_lineA_split
#check @Zeta2L7IdSum.integral_Hn_lineA_split
#print axioms Zeta2L7IdSum.candidate_dsum
#check @Zeta2L7IdSum.candidate_dsum
#print axioms Zeta2L7IdSum.candidate_sgn
#check @Zeta2L7IdSum.candidate_sgn
#print axioms Zeta2L7IdSum.Pin_mul_sum_ck
#check @Zeta2L7IdSum.Pin_mul_sum_ck
#print axioms Zeta2L7IdSum.pn_eq
#check @Zeta2L7IdSum.pn_eq
#print axioms Zeta2L7IdSum.residSum_eq
#check @Zeta2L7IdSum.residSum_eq
#print axioms Zeta2L7IdSum.rn_add_rLine
#check @Zeta2L7IdSum.rn_add_rLine
#print axioms Zeta2L7IdSum.rn_eq_neg_rLine_iff
#check @Zeta2L7IdSum.rn_eq_neg_rLine_iff
#print axioms Zeta2L7IdSum.rn_eq_neg_rLine
#check @Zeta2L7IdSum.rn_eq_neg_rLine
#print axioms Zeta2L7IdSum.pnPoly_zero
#check @Zeta2L7IdSum.pnPoly_zero
#print axioms Zeta2L7IdSum.residSum_zero
#check @Zeta2L7IdSum.residSum_zero
