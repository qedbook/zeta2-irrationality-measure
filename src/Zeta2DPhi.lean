/-
# HC2 — `d_φ̃ ≥ 15.98087905`, the explicit LOWER bound on leg B's limit

Row HC2 of `docs/future/zeta2-lean-chain.md`.  PT-RATE proved `log Φ̃ₙ / n → d_φ̃` where

  `d_φ̃ = ∑ i, pv i * ∑' k, (1/(k + pa i) − 1/(k + pb i))`

(`Zeta2LegBCandidate.pa/pb/pv`, the 26 pieces of `Zeta2Profile.candidateProfile`), and
`Zeta2L12`'s `hc2 : c2 ≤ 15.01912095` needs `d_φ̃ ≥ 31 − 15.01912095 = 15.98087905`.  This file
proves it, with room: `d_phi_ge_slack : 15.98087906 ≤ d_φ̃`.

## Route

For one piece `f k = 1/(k+a) − 1/(k+b)` (positive, decreasing, convex on `k ≥ 0`):

* the first `N` terms are summed EXACTLY, in `ℚ`, by the kernel (`decide +kernel`);
* the tail `∑_{k ≥ N} f k` is bounded BELOW by the trapezoid rule for the convex integrand:
  `∫_k^{k+1} f ≤ (f k + f (k+1))/2`, summed and telescoped, gives
  `∑_{k≥N} f k ≥ ∫_N^∞ f + f N / 2 = log((N+b)/(N+a)) + f N / 2`;
* `log((N+b)/(N+a)) = −log(1 − x)` at `x = (b−a)/(N+b) ∈ [0, 1)` is bounded below by any
  partial sum of its Taylor series (`Real.hasSum_pow_div_log_of_abs_lt_one`, all terms ≥ 0).

**The direction is a theorem about the sign of one derivative, not a numeric check.**  The
trapezoid defect `h(x) = log(x+1) − log x − (1/x + 1/(x+1))/2` has `h'(x) = 1/(2x²(x+1)²) > 0`
(`trapDef_hasDerivAt`), so `h` is MONOTONE on `(0, ∞)` (`trapDef_monotoneOn`), which at
`x = k+a ≤ y = k+b` is exactly `∫_k^{k+1} f ≤ (f k + f(k+1))/2` written without an integral
(`step_le`).  The MIDPOINT rule goes the other way for a convex integrand (it bounds the tail
from ABOVE) — the falsifier's arm that asserts `h` antitone is rejected at the derivative's sign,
which is where the two rules differ in Lean.

No integral appears anywhere: the per-step inequality is the monotonicity of `h`, the sum over
`k` telescopes by `Finset.sum_range_sub'`, and the limit `M → ∞` is `le_of_tendsto_of_tendsto'`.

## Numbers

`N = 250` terms per piece, 5 Taylor terms.  MEASURED (`hc2_round_probe.out`, exact ℚ): the
floored partial sum plus trapezoid tail at `N = 250` is `15.9808790629884`, so the literal
`15.98087906` clears by `3.0e-9` and the kernel refuses `15.98087907` (falsifier arm K1);
at `N = 188` the same bound is `15.98087905032`, which clears the row's `15.98087905` by only
`3.2e-10` and does NOT clear `15.98087906` (arm K2 — the `(N, literal)` pairs are coupled and
`188` was sized to the re-cut literal with zero slack).  The true value is `15.980879072391963`.
Everything the kernel checks here is exact rational arithmetic; the only rounding is the
Taylor truncation, which is one-signed (below).

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox; Lean
never runs on the laptop (owner ruling 2026-09-07).
-/
import Zeta2LegBCand

namespace Zeta2DPhi

open Finset Filter Topology
open Zeta2Profile Zeta2LegBCandidate

/-! ## §1. The trapezoid defect and its sign -/

/-- `h(x) = ∫_x^{x+1} dt/t − (1/x + 1/(x+1))/2`: integral minus trapezoid for `1/t`. -/
noncomputable def trapDef (x : ℝ) : ℝ :=
  Real.log (x + 1) - Real.log x - (x⁻¹ + (x + 1)⁻¹) / 2

/-- `h'(x) = 1/(2x²(x+1)²)`.  This sign IS the trapezoid direction. -/
theorem trapDef_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt trapDef (1 / (2 * x ^ 2 * (x + 1) ^ 2)) x := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have h1 : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (x + 1)) x :=
    ((hasDerivAt_id' x).add_const 1).log hx1.ne'
  have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h3 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx.ne'
  have h4 : HasDerivAt (fun y : ℝ => (y + 1)⁻¹) (-1 / (x + 1) ^ 2) x :=
    ((hasDerivAt_id' x).add_const 1).inv hx1.ne'
  have h : HasDerivAt (fun y : ℝ => Real.log (y + 1) - Real.log y - (y⁻¹ + (y + 1)⁻¹) / 2)
      (1 / (x + 1) - x⁻¹ - (-(x ^ 2)⁻¹ + -1 / (x + 1) ^ 2) / 2) x :=
    (h1.sub h2).sub ((h3.add h4).div_const 2)
  have e : (1 / (x + 1) - x⁻¹ - (-(x ^ 2)⁻¹ + -1 / (x + 1) ^ 2) / 2)
      = 1 / (2 * x ^ 2 * (x + 1) ^ 2) := by
    field_simp
    ring
  rw [← e]
  exact h

/-- `h` is monotone on `(0, ∞)` — the trapezoid rule OVER-estimates `∫ 1/t`, and by more at
smaller `x`. -/
theorem trapDef_monotoneOn : MonotoneOn trapDef (Set.Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx
    exact (trapDef_hasDerivAt hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro x hx
    exact (trapDef_hasDerivAt hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx
    rw [(trapDef_hasDerivAt hx).deriv]
    have : (0 : ℝ) < x := hx
    positivity

/-! ## §2. One step: `∫_k^{k+1} f ≤ (f k + f (k+1))/2`, integral-free -/

/-- For `f t = 1/(t+a) − 1/(t+b)`: `[G k − G (k+1)] ≤ (f k + f (k+1))/2` where
`G m = log(m+b) − log(m+a)`, i.e. `G k − G (k+1) = ∫_k^{k+1} f`. -/
theorem step_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    (Real.log ((k : ℝ) + b) - Real.log ((k : ℝ) + a))
        - (Real.log (((k : ℝ) + 1) + b) - Real.log (((k : ℝ) + 1) + a))
      ≤ ((1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b))
          + (1 / (((k : ℝ) + 1) + a) - 1 / (((k : ℝ) + 1) + b))) / 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hx : (0 : ℝ) < (k : ℝ) + a := by linarith
  have hy : (0 : ℝ) < (k : ℝ) + b := by linarith
  have h := trapDef_monotoneOn (show (k : ℝ) + a ∈ Set.Ioi 0 from hx)
    (show (k : ℝ) + b ∈ Set.Ioi 0 from hy) (by linarith : (k : ℝ) + a ≤ (k : ℝ) + b)
  unfold trapDef at h
  have e1 : (k : ℝ) + a + 1 = (k : ℝ) + 1 + a := by ring
  have e2 : (k : ℝ) + b + 1 = (k : ℝ) + 1 + b := by ring
  rw [e1, e2] at h
  simp only [one_div]
  linarith

/-! ## §3. The tail: `∑_{k ≥ N} f k ≥ log((N+b)/(N+a)) + f N / 2` -/

/-- `G m = log(m+b) − log(m+a) → 0`, by the squeeze `0 ≤ G m ≤ ((b−a)/a) · 1/(m+1)`. -/
theorem logdiff_tendsto_zero (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun m : ℕ => Real.log ((m : ℝ) + b) - Real.log ((m : ℝ) + a)) atTop (𝓝 0) := by
  have hC : Tendsto (fun m : ℕ => ((b - a) / a) * (1 / ((m : ℝ) + 1))) atTop (𝓝 (((b - a) / a) * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at hC
  refine squeeze_zero (fun m => ?_) (fun m => ?_) hC
  · have hk : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hx : (0 : ℝ) < (m : ℝ) + a := by linarith
    have := Real.log_le_log hx (by linarith : (m : ℝ) + a ≤ (m : ℝ) + b)
    linarith
  · have hk : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hx : (0 : ℝ) < (m : ℝ) + a := by linarith
    have hy : (0 : ℝ) < (m : ℝ) + b := by linarith
    have h1 : Real.log ((m : ℝ) + b) - Real.log ((m : ℝ) + a) ≤ ((m : ℝ) + b) / ((m : ℝ) + a) - 1 := by
      rw [← Real.log_div hy.ne' hx.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hy hx)
    have h2 : ((m : ℝ) + b) / ((m : ℝ) + a) - 1 = (b - a) / ((m : ℝ) + a) := by
      field_simp
      ring
    have h3 : (b - a) / ((m : ℝ) + a) ≤ ((b - a) / a) * (1 / ((m : ℝ) + 1)) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hx (by positivity)]
      have : a * (m : ℝ) ≤ (m : ℝ) := by nlinarith
      nlinarith
    linarith

/-- **The trapezoid-convexity tail bound.**  The sum over `k ≥ N` of the density terms is at
least `log((N+b)/(N+a)) + f N / 2`. -/
theorem tail_lower (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hb1 : b ≤ a + 1) (N : ℕ) :
    (Real.log ((N : ℝ) + b) - Real.log ((N : ℝ) + a))
        + (1 / ((N : ℝ) + a) - 1 / ((N : ℝ) + b)) / 2
      ≤ ∑' k : ℕ, (1 / (((k + N : ℕ) : ℝ) + a) - 1 / (((k + N : ℕ) : ℝ) + b)) := by
  set f : ℕ → ℝ := fun k => 1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b) with hf
  set G : ℕ → ℝ := fun m => Real.log ((m : ℝ) + b) - Real.log ((m : ℝ) + a) with hG
  have hsum : Summable f := Zeta2LegB.summable_density a b ha hab hb1
  have hs : Summable (fun k => f (k + N)) := (summable_nat_add_iff N).2 hsum
  -- every partial sum of the tail dominates the telescoped trapezoid sum
  have hpart : ∀ M : ℕ,
      (G N - G (M + N)) + (f N - f (M + N)) / 2 ≤ ∑ k ∈ range M, f (k + N) := by
    intro M
    have h1 : ∑ k ∈ range M, (G (k + N) - G (k + N + 1)) = G N - G (M + N) := by
      have := Finset.sum_range_sub' (fun k => G (k + N)) M
      simp only [zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show k + 1 + N = k + N + 1 by omega]
    have h2 : ∑ k ∈ range M, (f (k + N) - f (k + N + 1)) = f N - f (M + N) := by
      have := Finset.sum_range_sub' (fun k => f (k + N)) M
      simp only [zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show k + 1 + N = k + N + 1 by omega]
    have h3 : ∀ k ∈ range M,
        (G (k + N) - G (k + N + 1)) + (f (k + N) - f (k + N + 1)) / 2 ≤ f (k + N) := by
      intro k _
      have hstep := step_le a b ha hab (k + N)
      simp only [hf, hG]
      push_cast at hstep ⊢
      linarith
    calc (G N - G (M + N)) + (f N - f (M + N)) / 2
        = ∑ k ∈ range M, ((G (k + N) - G (k + N + 1)) + (f (k + N) - f (k + N + 1)) / 2) := by
          rw [Finset.sum_add_distrib, h1, ← Finset.sum_div, h2]
      _ ≤ ∑ k ∈ range M, f (k + N) := Finset.sum_le_sum h3
  -- pass to the limit
  have hlim1 : Tendsto (fun M => ∑ k ∈ range M, f (k + N)) atTop (𝓝 (∑' k, f (k + N))) :=
    hs.hasSum.tendsto_sum_nat
  have hG0 : Tendsto (fun M : ℕ => G (M + N)) atTop (𝓝 0) :=
    (logdiff_tendsto_zero a b ha hab hb).comp (tendsto_add_atTop_nat N)
  have hf0 : Tendsto (fun M : ℕ => f (M + N)) atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero.comp (tendsto_add_atTop_nat N)
  have hlim2 : Tendsto (fun M : ℕ => (G N - G (M + N)) + (f N - f (M + N)) / 2) atTop
      (𝓝 ((G N - 0) + (f N - 0) / 2)) :=
    (tendsto_const_nhds.sub hG0).add ((tendsto_const_nhds.sub hf0).div_const 2)
  have := le_of_tendsto_of_tendsto' hlim2 hlim1 hpart
  simpa [hf, hG] using this

/-! ## §4. One piece: exact head + trapezoid tail ≤ the tsum -/

theorem piece_lower (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hb1 : b ≤ a + 1) (N : ℕ) :
    ∑ k ∈ range N, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b))
        + ((Real.log ((N : ℝ) + b) - Real.log ((N : ℝ) + a))
          + (1 / ((N : ℝ) + a) - 1 / ((N : ℝ) + b)) / 2)
      ≤ ∑' k : ℕ, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b)) := by
  have hs := Zeta2LegB.summable_density a b ha hab hb1
  rw [← hs.sum_add_tsum_nat_add N]
  exact add_le_add (le_refl _) (tail_lower a b ha hab hb hb1 N)

/-! ## §5. A rational lower bound on `log v − log u` -/

/-- Any partial sum of the Taylor series of `−log(1−x)` at `x = (v−u)/v ∈ [0,1)` is a lower
bound: every term is nonnegative (`Real.hasSum_pow_div_log_of_abs_lt_one`). -/
theorem log_sub_log_ge (u v x : ℝ) (hu : 0 < u) (huv : u ≤ v) (hx : x = (v - u) / v) (n : ℕ) :
    ∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1) ≤ Real.log v - Real.log u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hx0 : 0 ≤ x := by rw [hx]; exact div_nonneg (by linarith) hv.le
  have hx1 : x < 1 := by rw [hx, div_lt_one hv]; linarith
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h1x : 1 - x = u / v := by rw [hx]; field_simp; ring
  rw [h1x, Real.log_div hu.ne' hv.ne', neg_sub] at hsum
  exact sum_le_hasSum (range n) (fun i _ => div_nonneg (pow_nonneg hx0 _) (by positivity)) hsum

/-! ## §6. The closed form in `ℚ`, and its cast to the real bound -/

/-- The density term over `ℚ`. -/
def fQ (a b : ℚ) (k : ℕ) : ℚ := 1 / ((k : ℚ) + a) - 1 / ((k : ℚ) + b)

/-- `v · (∑_{k<N} f k + ∑_{i<n} x^{i+1}/(i+1) + f N / 2)` at `x = (b−a)/(N+b)` — the piece's
weighted lower bound as one rational, computable by the kernel. -/
def lowerQ (t : ℚ × ℚ × ℚ) (N n : ℕ) : ℚ :=
  t.2.2 * (∑ k ∈ range N, fQ t.1 t.2.1 k
    + ∑ i ∈ range n, ((t.2.1 - t.1) / ((N : ℚ) + t.2.1)) ^ (i + 1) / ((i : ℚ) + 1)
    + fQ t.1 t.2.1 N / 2)

/-- **The generic real inequality**: for a valid piece, `lowerQ` is below the weighted tsum. -/
theorem lowerQ_le (t : ℚ × ℚ × ℚ)
    (ht : 0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 ≤ 1 ∧ t.2.1 ≤ t.1 + 1) (hv : 0 < t.2.2) (N n : ℕ) :
    ((lowerQ t N n : ℚ) : ℝ)
      ≤ ((t.2.2 : ℚ) : ℝ) * ∑' k : ℕ, (1 / ((k : ℝ) + ((t.1 : ℚ) : ℝ)) - 1 / ((k : ℝ) + ((t.2.1 : ℚ) : ℝ))) := by
  obtain ⟨a, b, v⟩ := t
  simp only at ht hv ⊢
  obtain ⟨ha, hab, hb1, hba⟩ := ht
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hba' : (b : ℝ) ≤ a + 1 := by exact_mod_cast hba
  have hv' : (0 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv.le
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpiece := piece_lower a b ha' hab' hb1' hba' N
  have hlog := log_sub_log_ge ((N : ℝ) + a) ((N : ℝ) + b) (((b : ℝ) - a) / ((N : ℝ) + b))
    (by linarith) (by linarith) (by ring) n
  unfold lowerQ fQ
  push_cast
  apply mul_le_mul_of_nonneg_left _ hv'
  linarith [hpiece, hlog]

/-! ## §7. The kernel computation over the landed profile -/

/-- **`d_φ̃ ≥ 15.98087906` as a closed rational fact.**  26 pieces × 250 exact terms, plus 26
five-term Taylor tails, summed by the kernel.  Falsifier arm K1 raises the literal to
`15.98087907` and is refused; arm K2 drops `N` to `188` and is refused. -/
theorem kernel_total :
    (1598087906 / 10 ^ 8 : ℚ)
      ≤ ∑ i : Fin candidateProfile.length, lowerQ (candidateProfile.get i) 250 5 := by
  decide +kernel

/-- **The cell's `N ≈ 188` sizing, executed**: at `N = 188` the same bound clears the row's
literal `15.98087905` — and arm K2 shows it does NOT clear `15.98087906`, so the `(N, literal)`
pairs are coupled exactly as `hc2_round_probe.out` measured (`15.98087905032` at 188). -/
theorem kernel_total_188 :
    (1598087905 / 10 ^ 8 : ℚ)
      ≤ ∑ i : Fin candidateProfile.length, lowerQ (candidateProfile.get i) 188 5 := by
  decide +kernel

/-! ## §8. The headline -/

/-- The chain's `d_φ̃`, in PT-RATE's vocabulary. -/
noncomputable def dPhi : ℝ :=
  ∑ i : Fin candidateProfile.length,
    pv i * ∑' k : ℕ, (1 / ((k : ℝ) + pa i) - 1 / ((k : ℝ) + pb i))

/-- **`15.98087906 ≤ d_φ̃`** — one ulp of room above what `hc2` needs. -/
theorem d_phi_ge_slack : (15.98087906 : ℝ) ≤ dPhi := by
  have hk : ((1598087906 / 10 ^ 8 : ℚ) : ℝ)
      ≤ ((∑ i : Fin candidateProfile.length, lowerQ (candidateProfile.get i) 250 5 : ℚ) : ℝ) := by
    exact_mod_cast kernel_total
  rw [Rat.cast_sum] at hk
  have h2 : ∑ i : Fin candidateProfile.length, ((lowerQ (candidateProfile.get i) 250 5 : ℚ) : ℝ)
      ≤ dPhi := by
    unfold dPhi
    apply Finset.sum_le_sum
    intro i _
    have hmem := List.get_mem candidateProfile i
    exact lowerQ_le _ (candidateProfile_valid _ hmem) (candidateProfile_values_pos _ hmem) 250 5
  calc (15.98087906 : ℝ) = ((1598087906 / 10 ^ 8 : ℚ) : ℝ) := by norm_num
    _ ≤ _ := hk
    _ ≤ dPhi := h2

/-- **HC2's statement: `d_φ̃ ≥ 15.98087905`**, exactly the row's `theorem d_phi_ge`. -/
theorem d_phi_ge :
    (15.98087905 : ℝ) ≤ ∑ i : Fin candidateProfile.length,
      pv i * ∑' k : ℕ, (1 / ((k : ℝ) + pa i) - 1 / ((k : ℝ) + pb i)) :=
  le_trans (by norm_num) d_phi_ge_slack

/-- **`hc2` in L12's shape** for any `c2 = 31 − d_φ̃ + ε'` with `ε' ≤ 1e-8` — DRATE's `c2`. -/
theorem hc2_of_dphi (ε' : ℝ) (hε : ε' ≤ 1 / 10 ^ 8) : 31 - dPhi + ε' ≤ (15.01912095 : ℝ) := by
  have := d_phi_ge_slack
  norm_num at this hε ⊢
  linarith

#print axioms trapDef_monotoneOn
#print axioms step_le
#print axioms tail_lower
#print axioms piece_lower
#print axioms log_sub_log_ge
#print axioms lowerQ_le
#print axioms kernel_total
#print axioms kernel_total_188
#print axioms d_phi_ge_slack
#print axioms d_phi_ge
#print axioms hc2_of_dphi

end Zeta2DPhi
