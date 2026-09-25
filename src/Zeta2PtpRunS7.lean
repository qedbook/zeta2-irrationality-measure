/-
# Row PT-P, layer 16 — the run stratum `[3/13, 4/17)` (`φ̃ = 1`) at `m < p²`, CLOSED for the
# polynomial half, and `ResidualRunOpen` narrowed past it

On the stratum, with `n = p·a + s`, the nine floors `⌊c·s/p⌋` are fixed — `⌊5x⌋ = 1`, `⌊9x⌋ = 2`,
`⌊11x⌋ = 2`, `⌊13x⌋ = 3`, `⌊15x⌋ = 3`, `⌊17x⌋ = 3`, `⌊22x⌋ = 5`, `⌊24x⌋ = 5`, `⌊26x⌋ = 6` (`s7_res`)
— and at a polar row `m mod p = 11s − 2p`.  The block polynomial's degree is then
`(p−1−(11s−2p)) + (13s−3p) + (9s−2p) + (5s−p) = 16s − 3p − 1 ≤ p − 2 ⟺ 16s < 4p`, the
harmonic side's own count (`Zeta2PtpS7.runPoly_natDegree_le`), because the units digits are the
same four.  What is new is the SUPPORT, measured residue-constant on the stratum
(`wraps.py` census in the probe's notes) and proved here by `omega`:

* LO blocks `t ≤ 13a + 3`: the support forces `u > 26s − 6p`, `u ≤ 24s − 5p`, `u > 22s − 5p`
  (wraps F, T, F), so the high digits are `26a + 5 − t`, `24a + 5 − t`, `22a + 4 − t` and no top
  is truncated (`s7_lo_hsup`);
* TAIL blocks `t ≥ 26a + 6`: wraps T, F, F, high digits `t − 13a − 3`, `t − 15a − 4`,
  `t − 17a − 4` — the last in BOTH cases `17s + 1 < 4p` and `17s + 1 = 4p`, where `17n + 1` is a
  multiple of `p` (the cell `n = 3, p = 13` is one) and the borrow disappears into the quotient
  (`s7_hi_hsup`);
* every other block of either half is identically `0` (`Tlo_eq_zero_of_gt13`,
  `Thi_eq_zero_of_le26`).

So `p ∣ h_m` (`Zeta2PtpRunBlock.pow_dvd_hc_of_blocks`), `v_p(L·C(m,L)) = 1` at a polar row below
`p²`, and `Zeta2PtpResPair.pval_coeff_of_dvd` gives **`coeff_runLow_S7`**: the coefficient bound
at every polar row on `[3/13, 4/17)` with `m < p²`, for every `n`.

`ResidualRunRestOpen` is `ResidualRunOpen` without those rows, and
`residualRunOpen_of_rest : ResidualRunRestOpen → Zeta2PtpResPair.ResidualRunOpen`,
`polyHalfOpen_of_rest : ResidualRunRestOpen → PolyHalfOpen` carry it in their TYPE.

WHAT IS NOT CLAIMED.  The four φ̃ = 2 run strata below `p²` and every polar run-strata row at
`m ≥ p²` (including this stratum's) are the named residual.  Row PT-P does not close and
`Zeta2Target.zeta2_not_liouvilleWith` is `sorry`.

Probe: `ptp_resid_narrow_probe.py` / `.out` (arms S1–S3).  Falsifier: `falsify_ptprunlo.sh`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2PnHarm
import Zeta2Profile
import Zeta2PhiT
import Zeta2NewtonCarry
import Zeta2NewtonAssemble
import Zeta2PnCleared
import Zeta2PnFunc
import Zeta2PnHarmDelta
import Zeta2PhiTDvd
import Zeta2PtpPolar
import Zeta2PtpRun
import Zeta2PtpStratum
import Zeta2PtpCong
import Zeta2PtpBlock
import Zeta2CarryFull
import Zeta2PtpS7
import Zeta2PtpPoly
import Zeta2PtpCoeff
import Zeta2HatCarry
import Zeta2PtpKummer
import Zeta2PtpKumRes
import Zeta2PtpKumS1
import Zeta2PtpKumS2
import Zeta2PtpKumS3
import Zeta2PtpKumS4
import Zeta2PtpKumRows
import Zeta2PtpResPair
import Zeta2PtpRunBlock

set_option maxRecDepth 20000

namespace Zeta2PtpRunS7

open Zeta2PtpRunBlock Finset

/-! ## 1. The stratum's residues, and its two supports -/

section Res
variable {p : ℕ} [hp : Fact p.Prime]

/-- The residues of `c·n` on the stratum, `n = p·a + s`. -/
theorem s7_res {n a s : ℕ} (hn : n = p * a + s) (h1 : 3 * p ≤ 13 * s) (h2 : 17 * s < 4 * p) :
    (5 * n) % p = 5 * s - p ∧ (9 * n) % p = 9 * s - 2 * p ∧ (11 * n) % p = 11 * s - 2 * p
    ∧ (13 * n) % p = 13 * s - 3 * p ∧ (22 * n) % p = 22 * s - 5 * p
    ∧ (24 * n) % p = 24 * s - 5 * p ∧ (26 * n) % p = 26 * s - 6 * p := by
  have hp0 := hp.out.pos
  have e : ∀ c, c * n = c * s + (c * a) * p := fun c => by rw [hn]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mod_of_lin hp0 (q := 5 * a + 1) ?_ (by omega)
    have := e 5; have e2 : (5 * a + 1) * p = 5 * a * p + p := by ring
    omega
  · refine mod_of_lin hp0 (q := 9 * a + 2) ?_ (by omega)
    have := e 9; have e2 : (9 * a + 2) * p = 9 * a * p + 2 * p := by ring
    omega
  · refine mod_of_lin hp0 (q := 11 * a + 2) ?_ (by omega)
    have := e 11; have e2 : (11 * a + 2) * p = 11 * a * p + 2 * p := by ring
    omega
  · refine mod_of_lin hp0 (q := 13 * a + 3) ?_ (by omega)
    have := e 13; have e2 : (13 * a + 3) * p = 13 * a * p + 3 * p := by ring
    omega
  · refine mod_of_lin hp0 (q := 22 * a + 5) ?_ (by omega)
    have := e 22; have e2 : (22 * a + 5) * p = 22 * a * p + 5 * p := by ring
    omega
  · refine mod_of_lin hp0 (q := 24 * a + 5) ?_ (by omega)
    have := e 24; have e2 : (24 * a + 5) * p = 24 * a * p + 5 * p := by ring
    omega
  · refine mod_of_lin hp0 (q := 26 * a + 6) ?_ (by omega)
    have := e 26; have e2 : (26 * a + 6) * p = 26 * a * p + 6 * p := by ring
    omega

/-- **The LO support on the stratum**: wraps `(F, T, F)`, no truncation below `22n`. -/
theorem s7_lo_hsup {n m a s t u : ℕ} (hn : n = p * a + s) (h1 : 3 * p ≤ 13 * s)
    (h2 : 17 * s < 4 * p) (hm : m % p = 11 * s - 2 * p) (ht : t ≤ 13 * a + 3) (hu : u < p)
    (hsupp : SuppLo p n m u) :
    t * p + u ≤ 22 * n ∧ (26 * n - (t * p + u)) / p = 26 * a + 5 - t
      ∧ (24 * n - (t * p + u)) / p = 24 * a + 5 - t ∧ (22 * n - (t * p + u)) / p = 22 * a + 4 - t := by
  have hp0 := hp.out.pos
  obtain ⟨r5, r9, _, r13, r22, r24, r26⟩ := s7_res (p := p) hn h1 h2
  unfold SuppLo at hsupp
  rw [hm, r13, r26, r9, r24, r5, r22, Zeta2PtpKumRes.wrap_mod hu (show 26 * s - 6 * p < p by omega),
    Zeta2PtpKumRes.wrap_mod hu (show 24 * s - 5 * p < p by omega),
    Zeta2PtpKumRes.wrap_mod hu (show 22 * s - 5 * p < p by omega)] at hsupp
  obtain ⟨hA, hB, hC, hD⟩ := hsupp
  have w3 : 22 * s - 5 * p < u := by split_ifs at hD <;> omega
  have hT : t * p ≤ (13 * a + 3) * p := Nat.mul_le_mul_right p ht
  have eA : (13 * a + 3) * p = 13 * (p * a) + 3 * p := by ring
  have e26 : (26 * a + 5 - t) * p = (26 * a + 5) * p - t * p := Nat.sub_mul _ _ _
  have e24 : (24 * a + 5 - t) * p = (24 * a + 5) * p - t * p := Nat.sub_mul _ _ _
  have e22 : (22 * a + 4 - t) * p = (22 * a + 4) * p - t * p := Nat.sub_mul _ _ _
  have f26 : (26 * a + 5) * p = 26 * (p * a) + 5 * p := by ring
  have f24 : (24 * a + 5) * p = 24 * (p * a) + 5 * p := by ring
  have f22 : (22 * a + 4) * p = 22 * (p * a) + 4 * p := by ring
  subst hn
  refine ⟨by omega, ?_, ?_, ?_⟩
  · exact div_of_lin hp0 (r := 26 * s - 5 * p - u) (by omega) (by omega)
  · exact div_of_lin hp0 (r := 24 * s - 5 * p - u) (by omega) (by omega)
  · exact div_of_lin hp0 (r := 22 * s - 4 * p - u) (by omega) (by omega)

/-- **The TAIL support on the stratum**: wraps `(T, F, F)`, every top past `17n`. -/
theorem s7_hi_hsup {n m a s t u : ℕ} (hn : n = p * a + s) (h1 : 3 * p ≤ 13 * s)
    (h2 : 17 * s < 4 * p) (hm : m % p = 11 * s - 2 * p) (ht : 26 * a + 6 ≤ t) (hu : u < p)
    (hsupp : SuppHi p n m u) :
    17 * n + 1 ≤ t * p + u ∧ (t * p + u - 13 * n - 1) / p = t - 13 * a - 3
      ∧ (t * p + u - 15 * n - 1) / p = t - 15 * a - 4
      ∧ (t * p + u - 17 * n - 1) / p = t - 17 * a - 4 := by
  have hp0 := hp.out.pos
  obtain ⟨r5, r9, _, r13, _, _, _⟩ := s7_res (p := p) hn h1 h2
  have e : ∀ c, c * n + 1 = c * s + 1 + c * a * p := fun c => by rw [hn]; ring
  have q13 : (13 * n + 1) % p = 13 * s - 3 * p + 1 := by
    refine mod_of_lin hp0 (q := 13 * a + 3) ?_ (by omega)
    have := e 13; have e2 : (13 * a + 3) * p = 13 * a * p + 3 * p := by ring
    omega
  have q15 : (15 * n + 1) % p = 15 * s - 3 * p + 1 := by
    refine mod_of_lin hp0 (q := 15 * a + 3) ?_ (by omega)
    have := e 15; have e2 : (15 * a + 3) * p = 15 * a * p + 3 * p := by ring
    omega
  -- the third top: `17n + 1` is `(17s − 3p + 1) + (17a + 3)p`, or `(17a + 4)p` exactly
  have q17 : u ≤ 17 * s - 3 * p ∧ 22 * s - 5 * p + 1 ≤ u := by
    unfold SuppHi at hsupp
    obtain ⟨hA, -, -, hD⟩ := hsupp
    rw [r5] at hD
    by_cases hedge : 17 * s + 1 < 4 * p
    · have q : (17 * n + 1) % p = 17 * s - 3 * p + 1 := by
        refine mod_of_lin hp0 (q := 17 * a + 3) ?_ (by omega)
        have := e 17; have e2 : (17 * a + 3) * p = 17 * a * p + 3 * p := by ring
        omega
      rw [q, wrap_mod_up hu (by omega)] at hD
      split_ifs at hD <;> omega
    · have q : (17 * n + 1) % p = 0 := by
        refine mod_of_lin hp0 (q := 17 * a + 4) ?_ (by omega)
        have := e 17; have e2 : (17 * a + 4) * p = 17 * a * p + 4 * p := by ring
        omega
      rw [q, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hu] at hD
      omega
  unfold SuppHi at hsupp
  rw [hm, r13, r9, r5, q13, q15, wrap_mod_up hu (show 13 * s - 3 * p + 1 < p by omega),
    wrap_mod_up hu (show 15 * s - 3 * p + 1 < p by omega)] at hsupp
  obtain ⟨hA, hB, hC, -⟩ := hsupp
  have w1 : 13 * s - 3 * p + 1 ≤ u := by split_ifs at hB <;> omega
  have w2 : u < 15 * s - 3 * p + 1 := by split_ifs at hC <;> omega
  have hT : (26 * a + 6) * p ≤ t * p := Nat.mul_le_mul_right p ht
  have eA : (26 * a + 6) * p = 26 * (p * a) + 6 * p := by ring
  have g13 : (t - 13 * a - 3) * p = t * p - (13 * a + 3) * p := by
    rw [show t - 13 * a - 3 = t - (13 * a + 3) by omega, Nat.sub_mul]
  have g15 : (t - 15 * a - 4) * p = t * p - (15 * a + 4) * p := by
    rw [show t - 15 * a - 4 = t - (15 * a + 4) by omega, Nat.sub_mul]
  have g17 : (t - 17 * a - 4) * p = t * p - (17 * a + 4) * p := by
    rw [show t - 17 * a - 4 = t - (17 * a + 4) by omega, Nat.sub_mul]
  have f13 : (13 * a + 3) * p = 13 * (p * a) + 3 * p := by ring
  have f15 : (15 * a + 4) * p = 15 * (p * a) + 4 * p := by ring
  have f17 : (17 * a + 4) * p = 17 * (p * a) + 4 * p := by ring
  subst hn
  refine ⟨by omega, ?_, ?_, ?_⟩
  · exact div_of_lin hp0 (r := u - (13 * s - 3 * p + 1)) (by omega) (by omega)
  · exact div_of_lin hp0 (r := u + 4 * p - 15 * s - 1) (by omega) (by omega)
  · exact div_of_lin hp0 (r := u + 4 * p - 17 * s - 1) (by omega) (by omega)

end Res

/-! ## 2. The stratum closed at `m < p²` -/

/-- **THE RUN STRATUM `[3/13, 4/17)` AT `m < p²`, CLOSED.**  At a polar row on the stratum below
`p²`, `v_p(coeff n r) ≥ φ̃ + b_r − 1`: every LO block and every TAIL block of `h_m` is a
multiple of `p` (`lo_block_dvd`, `hi_block_dvd` on the stratum's supports), and `v_p(L·C(m,L)) = 1`. -/
theorem coeff_runLow_S7 {n p r : ℕ} (hp : p ∈ Zeta2PhiT.phiWindow n) (hr : r < 16 * n)
    (hpol : p ∣ r + 1) (hm : 11 * n + 1 + r < p ^ 2) (h1 : 3 * p ≤ 13 * (n % p))
    (h2 : 17 * (n % p) < 4 * p) :
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ) := by
  have hpp := Zeta2PhiT.prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 := hpp.pos
  have hsq := Zeta2PhiT.sq_gt_of_mem_phiWindow hp
  have hn1 := Zeta2PtpPolar.pos_of_mem_phiWindow hp
  have hp2 : 2 < p := by
    by_contra hc
    have : p ^ 2 ≤ 4 := by
      have : p ≤ 2 := by omega
      calc p ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left this 2
        _ = 4 := by norm_num
    omega
  refine Zeta2PtpResPair.pval_coeff_of_dvd hp ?_
  rw [Zeta2PtpKumRes.padicValNat_LC_polar hp hm hpol, Zeta2PtpKumRes.bbit_polar hpol,
    Zeta2PtpS7.phiT_piece7_res hp0 (by omega) h2]
  -- the row's `h_m` is a multiple of `p`
  have hn' : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  generalize n / p = a at hn'
  generalize hs : n % p = s at hn' h1 h2
  obtain ⟨r5, r9, r11, r13, _, _, _⟩ := s7_res (p := p) hn' h1 h2
  have hmod : (11 * n + 1 + r) % p = 11 * s - 2 * p := by
    rw [show 11 * n + 1 + r = 11 * n + (r + 1) by ring, Nat.add_mod, Nat.mod_eq_zero_of_dvd hpol,
      Nat.add_zero, Nat.mod_mod, r11]
  have hdeg : (p - 1 - (11 * n + 1 + r) % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2 := by
    rw [hmod, r13, r9, r5]
    omega
  have hdvd : (p : ℤ) ^ 1 ∣ Zeta2NewtonAssemble.hc n (11 * n + 1 + r) := by
    refine pow_dvd_hc_of_blocks hp0 hn1 (fun t _ => ?_) (fun t _ => ?_)
    · by_cases ht : t ≤ 13 * a + 3
      · rw [pow_one]
        exact lo_block_dvd hp2 hn1 hdeg fun u hu hsupp =>
          s7_lo_hsup hn' h1 h2 hmod ht hu hsupp
      · have hz : ∀ u ∈ Finset.range p, Tlo n (11 * n + 1 + r) (t * p + u) = 0 := by
          intro u _
          have hT : (13 * a + 4) * p ≤ t * p := Nat.mul_le_mul_right p (by omega)
          have e : (13 * a + 4) * p = 13 * (p * a) + 4 * p := by ring
          exact Tlo_eq_zero_of_gt13 hn1 (by omega)
        rw [Finset.sum_eq_zero hz]
        exact dvd_zero _
    · by_cases ht : 26 * a + 6 ≤ t
      · rw [pow_one]
        exact hi_block_dvd hp2 hn1 hdeg fun u hu hsupp =>
          s7_hi_hsup hn' h1 h2 hmod ht hu hsupp
      · have hz : ∀ u ∈ Finset.range p, Thi n (11 * n + 1 + r) (t * p + u) = 0 := by
          intro u hu
          have hu' := Finset.mem_range.mp hu
          have hT : t * p ≤ (26 * a + 5) * p := Nat.mul_le_mul_right p (by omega)
          have e : (26 * a + 5) * p = 26 * (p * a) + 5 * p := by ring
          exact Thi_eq_zero_of_le26 hn1 (by omega)
        rw [Finset.sum_eq_zero hz]
        exact dvd_zero _
  rw [show 1 + 1 - 1 + 1 = 1 + 1 by rfl, pow_succ']
  exact mul_dvd_mul_left _ hdvd

/-! ## 3. `ResidualRunOpen`, narrowed past the stratum -/

/-- **THE RESIDUAL, NARROWED PAST `[3/13, 4/17)` BELOW `p²`**: the polar run-strata rows except
those `coeff_runLow_S7` closes. -/
def ResidualRunRestOpen : Prop :=
  ∀ n p r : ℕ, p ∈ Zeta2PhiT.phiWindow n → r < 16 * n → p ∣ r + 1 →
    Zeta2PtpKumRows.RunStrata p (n % p) →
    ¬ (11 * n + 1 + r < p ^ 2 ∧ 3 * p ≤ 13 * (n % p) ∧ 17 * (n % p) < 4 * p) →
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ)

theorem residualRunOpen_of_rest (h : ResidualRunRestOpen) : Zeta2PtpResPair.ResidualRunOpen := by
  intro n p r hp hr hpol hrun
  by_cases hs7 : 11 * n + 1 + r < p ^ 2 ∧ 3 * p ≤ 13 * (n % p) ∧ 17 * (n % p) < 4 * p
  · exact coeff_runLow_S7 hp hr hpol hs7.1 hs7.2.1 hs7.2.2
  · exact h n p r hp hr hpol hrun hs7

theorem polyHalfOpen_of_rest (h : ResidualRunRestOpen) : Zeta2PtpPolar.PolyHalfOpen :=
  Zeta2PtpResPair.polyHalfOpen_of_run (residualRunOpen_of_rest h)

/-! ## 4. Pins -/

/-- The stratum's smallest window cell, `n = 3, p = 13` (`s = 3`), is ALSO the edge case of the
TAIL support: `17·3 + 1 = 52 = 4·13`. -/
theorem edge_3_13 : 13 ∈ Zeta2PhiT.phiWindow 3 ∧ 3 * 13 ≤ 13 * (3 % 13) ∧ 17 * (3 % 13) < 4 * 13
    ∧ (17 * 3 + 1) % 13 = 0 := by
  refine ⟨by decide +kernel, by decide, by decide, by decide⟩

end Zeta2PtpRunS7

#print axioms Zeta2PtpRunS7.s7_res
#check @Zeta2PtpRunS7.s7_res
#print axioms Zeta2PtpRunS7.s7_lo_hsup
#check @Zeta2PtpRunS7.s7_lo_hsup
#print axioms Zeta2PtpRunS7.s7_hi_hsup
#check @Zeta2PtpRunS7.s7_hi_hsup
#print axioms Zeta2PtpRunS7.coeff_runLow_S7
#check @Zeta2PtpRunS7.coeff_runLow_S7
#print axioms Zeta2PtpRunS7.residualRunOpen_of_rest
#check @Zeta2PtpRunS7.residualRunOpen_of_rest
#print axioms Zeta2PtpRunS7.polyHalfOpen_of_rest
#check @Zeta2PtpRunS7.polyHalfOpen_of_rest
#print Zeta2PtpRunS7.ResidualRunRestOpen
#print axioms Zeta2PtpRunS7.edge_3_13
