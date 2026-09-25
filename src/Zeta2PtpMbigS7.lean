/-
# Row PT-P, part (b), layer 2 — the φ̃ = 1 run stratum `[3/13, 4/17)` CLOSED at `m ≥ p²`

`Zeta2PtpRunS7.coeff_runLow_S7` closed this stratum's polar rows below `p²`.  Above it
(`m = p² + μ`, `0 ≤ μ < n`) the bound is `p² ∣ h_m`, and `h_m` is FOLDED (`Zeta2PtpFold.hc_eq_fold`):
`h_m = Σ_{t<p} Σ_{u<p} (T(tp + u) + T(p² + tp + u))`.  Each folded block is `0 mod p²`:

* **pair blocks** `t ≤ ⌊μ/p⌋`: the fold law gives `T(j) + T(p² + j) ≡ −p·λ(j)·T(j) (mod p²)`, and on
  the stratum `λ` is the SAME at every pair index whose term is a unit — its six floors are the
  support's fixed high digits (`s7_lo_hsup`) and low digits (`s7_lo_low`), and its `C(m,·)` part is
  `H_{⌊μ/p⌋−t} − H_t` (`s7_lam`); the raw block is `0 mod p` by `Zeta2PtpRunBlock.lo_block_dvd`
  UNCHANGED, and the unpaired terms `u > μ mod p` carry two carries (`Zeta2PtpFold.pair_block_sq`);
* **middle blocks** `t > ⌊μ/p⌋`: `p ∣ C(⌊m/p⌋, t)` (Lucas: `⌊m/p⌋ = p + ⌊μ/p⌋`), so the block is a
  multiple of `p` times the block of the reduced row `tp + (m mod p)` modulo `p²`
  (`Zeta2PtpFold.mid_block_sq`), which `lo_block_dvd` / `hi_block_dvd` kill on the stratum's
  supports — the same `s7_lo_hsup` / `s7_hi_hsup` as below `p²`.

**`coeff_runHigh_S7`**: the coefficient bound at every polar row on `[3/13, 4/17)` with `m ≥ p²`, for
every `n` (`ptp_mbig_probe.out`: 42 such rows at `n ≤ 4000`, the first `(717, 137, 10959)`).  So
`RestAboveOpen` narrows to the four φ̃ = 2 strata: `restAboveOpen_of_S2 : RestAboveS2Open →
RestAboveOpen`, `polyHalfOpen_of_S2 : RestAboveS2Open → PolyHalfOpen` — carried in the TYPE.

WHAT IS NOT CLAIMED.  The four φ̃ = 2 strata at `m ≥ p²` (`RestAboveS2Open`).  Row PT-P does not
close and `Zeta2Target.zeta2_not_liouvilleWith` is `sorry`.

Probe: `ptp_mbig_probe.py` / `.out`.  Falsifier: `falsify_ptpfold.sh` / `out_ptpfold_falsify.txt`.
Runner: `run_resid.sh`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2PtpFold
import Zeta2PtpMbig

set_option maxRecDepth 20000

namespace Zeta2PtpMbigS7

open Zeta2PtpFold Zeta2PtpRunBlock Zeta2PtpRunS7 Finset

section S
variable {p : ℕ} [hp : Fact p.Prime]

/-- `(c − (tp + u)) mod p = (c mod p + p − u) mod p`. -/
theorem mod_sub_block {c t u : ℕ} (h : t * p + u ≤ c) (hu : u < p) :
    (c - (t * p + u)) % p = (c % p + p - u) % p := by
  rw [← ZMod.natCast_eq_natCast_iff', cast_sub_block h, ← ZMod.natCast_mod (c % p + p - u) p,
    cast_wrap c u hu.le]

/-- A LO term with NO units carry sits on the units support. -/
theorem supp_of_kum0 {n m t u : ℕ} (hu : u < p) (hj : t * p + u ≤ 13 * n)
    (hk : Zeta2PtpKummer.kumLo n p m (t * p + u) = 0) : SuppLo p n m u := by
  have hjmod : (t * p + u) % p = u := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  unfold Zeta2PtpKummer.kumLo Zeta2PtpRun.cb at hk
  rw [hjmod, mod_sub_block (c := 26 * n) (by omega) hu, mod_sub_block (c := 24 * n) (by omega) hu,
    mod_sub_block (c := 22 * n) (by omega) hu] at hk
  unfold SuppLo
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs at hk <;> omega

/-- **The LO support's LOW digits on the stratum**, for a block `t ≤ a`: the three bottoms. -/
theorem s7_lo_low {n m a s t u : ℕ} (hn : n = p * a + s) (h1 : 3 * p ≤ 13 * s)
    (h2 : 17 * s < 4 * p) (hm : m % p = 11 * s - 2 * p) (ht : t ≤ a) (hu : u < p)
    (hsupp : SuppLo p n m u) :
    (13 * n - (t * p + u)) / p = 13 * a + 2 - t ∧ (15 * n - (t * p + u)) / p = 15 * a + 3 - t
      ∧ (17 * n - (t * p + u)) / p = 17 * a + 3 - t := by
  have hp0 := hp.out.pos
  obtain ⟨r5, r9, _, r13, r22, r24, r26⟩ := s7_res (p := p) hn h1 h2
  unfold SuppLo at hsupp
  rw [hm, r13, r26, r9, r24, r5, r22, Zeta2PtpKumRes.wrap_mod hu (show 26 * s - 6 * p < p by omega),
    Zeta2PtpKumRes.wrap_mod hu (show 24 * s - 5 * p < p by omega),
    Zeta2PtpKumRes.wrap_mod hu (show 22 * s - 5 * p < p by omega)] at hsupp
  obtain ⟨hA, hB, hC, hD⟩ := hsupp
  have wD : 22 * s - 5 * p < u := by split_ifs at hD <;> omega
  have wC : u ≤ 15 * s - 3 * p := by split_ifs at hC <;> omega
  have hT : t * p ≤ a * p := Nat.mul_le_mul_right p ht
  have ea : a * p = p * a := Nat.mul_comm a p
  have e13 : (13 * a + 2 - t) * p = (13 * a + 2) * p - t * p := Nat.sub_mul _ _ _
  have e15 : (15 * a + 3 - t) * p = (15 * a + 3) * p - t * p := Nat.sub_mul _ _ _
  have e17 : (17 * a + 3 - t) * p = (17 * a + 3) * p - t * p := Nat.sub_mul _ _ _
  have f13 : (13 * a + 2) * p = 13 * (p * a) + 2 * p := by ring
  have f15 : (15 * a + 3) * p = 15 * (p * a) + 3 * p := by ring
  have f17 : (17 * a + 3) * p = 17 * (p * a) + 3 * p := by ring
  subst hn
  refine ⟨?_, ?_, ?_⟩
  · exact div_of_lin hp0 (r := 13 * s - 2 * p - u) (by omega) (by omega)
  · exact div_of_lin hp0 (r := 15 * s - 3 * p - u) (by omega) (by omega)
  · exact div_of_lin hp0 (r := 17 * s - 3 * p - u) (by omega) (by omega)

/-- **`λ` is CONSTANT on a pair block's units support.** -/
theorem s7_lam {n m a s t u : ℕ} (hn : n = p * a + s) (h1 : 3 * p ≤ 13 * s)
    (h2 : 17 * s < 4 * p) (hm : m % p = 11 * s - 2 * p) (hmsq : p ^ 2 ≤ m) (hu : u < p)
    (hsupp : SuppLo p n m u) (hpair : t * p + u ≤ m - p ^ 2) (hta : t ≤ a) :
    lam p n m (t * p + u)
      = hsum p 0 ((m - p ^ 2) / p - t) - hsum p 0 t
        + (-hsum p (13 * a + 2 - t) (26 * a + 5 - t) - hsum p (15 * a + 3 - t) (24 * a + 5 - t)
          - hsum p (17 * a + 3 - t) (22 * a + 4 - t)) := by
  have hp0 := hp.out.pos
  obtain ⟨l13, l15, l17⟩ := s7_lo_low hn h1 h2 hm hta hu hsupp
  obtain ⟨_, u26, u24, u22⟩ := s7_lo_hsup hn h1 h2 hm (by omega : t ≤ 13 * a + 3) hu hsupp
  have hjdiv : (t * p + u) / p = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hu, zero_add]
  have hμ : (m - (t * p + u) - p ^ 2) / p = (m - p ^ 2) / p - t := by
    have hdm := Nat.div_add_mod (m - p ^ 2) p
    have hpp : p ^ 2 = p * p := sq p
    have hmm : m % p = (m - p ^ 2) % p := by
      have hm' : m = (m - p ^ 2) + p * p := by omega
      conv_lhs => rw [hm']
      rw [Nat.add_mul_mod_self_left]
    have hum : u ≤ (m - p ^ 2) % p := by rw [← hmm]; exact hsupp.1
    have htμ : t ≤ (m - p ^ 2) / p := by
      have := Nat.div_le_div_right (c := p) hpair
      rwa [hjdiv] at this
    have e1 : ((m - p ^ 2) / p - t) * p = (m - p ^ 2) / p * p - t * p := Nat.sub_mul _ _ _
    have e2 : t * p ≤ (m - p ^ 2) / p * p := Nat.mul_le_mul_right p htμ
    have e3 : (m - p ^ 2) / p * p = p * ((m - p ^ 2) / p) := Nat.mul_comm _ _
    exact div_of_lin hp0 (r := (m - p ^ 2) % p - u) (by omega)
      (by have := Nat.mod_lt (m - p ^ 2) hp0; omega)
  unfold lam lamC lamH
  rw [hjdiv, hμ, l13, l15, l17, u26, u24, u22]

end S

/-! ## The stratum closed above `p²` -/

/-- **THE RUN STRATUM `[3/13, 4/17)` AT `m ≥ p²`, CLOSED.** -/
theorem coeff_runHigh_S7 {n p r : ℕ} (hp : p ∈ Zeta2PhiT.phiWindow n) (hr : r < 16 * n)
    (hpol : p ∣ r + 1) (hm : p ^ 2 ≤ 11 * n + 1 + r) (h1 : 3 * p ≤ 13 * (n % p))
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
  rw [Zeta2PtpResPair.padicValNat_LC_sq hp hr hm, Zeta2PtpResPair.units_LC_polar hp hpol,
    Zeta2PtpKumRes.bbit_polar hpol, Zeta2PtpS7.phiT_piece7_res hp0 (by omega) h2]
  suffices hdvd : (p : ℤ) ^ 2 ∣ Zeta2NewtonAssemble.hc n (11 * n + 1 + r) by
    rw [show 1 + 1 - 1 + (1 + 1) = 1 + 2 by rfl, pow_add, pow_one]
    exact mul_dvd_mul_left _ hdvd
  have hpp2 : p ^ 2 = p * p := sq p
  have hp12 : p ≤ 12 * n := by
    by_contra h
    push_neg at h
    have := Nat.mul_le_mul h h
    nlinarith
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
  set m := 11 * n + 1 + r with hmdef
  have hm2 : m < p ^ 2 + p ^ 2 := by omega
  have hm3 : m < p ^ 3 := by
    have : p ^ 3 = p * p ^ 2 := by ring
    have : 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  set μ := m - p ^ 2 with hμdef
  have hμn : μ < n := by omega
  have hμm : m = μ + p * p := by omega
  have hμdm := Nat.div_add_mod μ p
  have hμmodlt := Nat.mod_lt μ hp0
  have hmp : m % p = μ % p := by rw [hμm, Nat.add_mul_mod_self_left]
  have hμ1 : μ / p < p := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
  have hMdiv : m / p = p + μ / p := by
    rw [hμm, Nat.add_mul_div_right _ _ hp0, Nat.add_comm]
  have hμa : μ / p ≤ a := by
    have : μ / p < a + 1 := (Nat.div_lt_iff_lt_mul hp0).mpr (by
      have e : (a + 1) * p = p * a + p := by ring
      omega)
    omega
  have hμp : μ / p * p = p * (μ / p) := Nat.mul_comm _ _
  rw [hc_eq_fold hm2]
  refine dvd_sum fun t ht => ?_
  have ht' := mem_range.mp ht
  have htp1 : (t + 1) * p ≤ p * p := Nat.mul_le_mul_right p ht'
  have etp1 : (t + 1) * p = t * p + p := by ring
  by_cases hpair : t ≤ μ / p
  · -- a PAIR block
    have hta : t ≤ a := le_trans hpair hμa
    have htpμ : t * p ≤ μ / p * p := Nat.mul_le_mul_right p hpair
    refine pair_block_sq (n := n) (m := m) (t := t)
      (ℓ₀ := hsum p 0 (μ / p - t) - hsum p 0 t
        + (-hsum p (13 * a + 2 - t) (26 * a + 5 - t) - hsum p (15 * a + 3 - t) (24 * a + 5 - t)
          - hsum p (17 * a + 3 - t) (22 * a + 4 - t))) hsq (by omega) hm2 (by omega) ?_ ?_ ?_
    · intro u hu hj hT
      have hk : Zeta2PtpKummer.kumLo n p m (t * p + u) = 0 := by
        by_contra hk
        refine hT ?_
        unfold Tm
        exact (dvd_pow_self (p : ℤ) hk).trans
          (Zeta2PtpKummer.pow_kumLo_dvd_term (by omega) (by omega))
      exact s7_lam hn' h1 h2 hmod (by omega) hu (supp_of_kum0 hu (by omega) hk) hj hta
    · intro u hu hj
      have hjmod : (t * p + u) % p = u := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
      have hcb : Zeta2PtpRun.cb p m (t * p + u) = 1 := by
        unfold Zeta2PtpRun.cb
        rw [hjmod]
        simp [show m % p < u by omega]
      have hk : 2 ≤ Zeta2PtpKummer.kumLo n p m (t * p + u) + 1 := by
        unfold Zeta2PtpKummer.kumLo
        omega
      unfold Tm
      exact (pow_dvd_pow _ hk).trans (Zeta2PtpResPair.pow_term_lo_succ (by omega) (by omega)
        (by omega) hm3 (by omega) (by omega))
    · have hlo := lo_block_dvd hp2 hn1 hdeg (t := t) fun u hu hsupp =>
        s7_lo_hsup hn' h1 h2 hmod (by omega) hu hsupp
      have e : ∑ u ∈ range p, Tm n m (t * p + u)
          = (-1 : ℤ) ^ (27 * n) * ∑ u ∈ range p, Tlo n m (t * p + u) := by
        rw [mul_sum]
        refine sum_congr rfl fun u hu => ?_
        have hu' := mem_range.mp hu
        unfold Tm
        rw [term_eq_lo_add_hi n m (t * p + u) hn1 (by omega), Thi_eq_zero_of_le26 hn1 (by omega),
          add_zero]
      rw [e]
      exact Dvd.dvd.mul_left hlo _
  · -- a MIDDLE block
    have hlt : μ < t * p := by
      have := (Nat.div_lt_iff_lt_mul hp0).mp (show μ / p < t by omega)
      exact this
    have hTz : ∀ u < p, Tm n m (p ^ 2 + (t * p + u)) = 0 := by
      intro u _
      unfold Tm
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [sum_congr rfl fun u hu => by rw [hTz u (mem_range.mp hu), add_zero]]
    have hmp'' : (t * p + m % p) % p = m % p := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
    have hdeg'' : (p - 1 - (t * p + m % p) % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p
        ≤ p - 2 := by rw [hmp'']; exact hdeg
    have hmod'' : (t * p + m % p) % p = 11 * s - 2 * p := hmp''.trans hmod
    have hMt : p ∣ (m / p).choose t := by
      rw [← ZMod.natCast_eq_zero_iff, hMdiv, Zeta2PtpS7.lucas_raw (p + μ / p) t, Nat.add_mod_left,
        Nat.mod_eq_of_lt hμ1, Nat.mod_eq_of_lt ht', Nat.choose_eq_zero_of_lt (by omega),
        Nat.cast_zero, zero_mul]
    have hM1 : 1 ≤ m / p := by rw [hMdiv]; exact Nat.le_add_right_of_le hp0
    have htm : t * p + p ≤ m + 1 := by
      have h1 : t * p + p ≤ p * p := etp1 ▸ htp1
      have h2 : p * p ≤ m := hpp2 ▸ hm
      exact le_trans h1 (le_trans h2 (Nat.le_succ m))
    refine mid_block_sq hn1 hM1 hMt htm ?_ ?_
    · by_cases htl : t ≤ 13 * a + 3
      · exact lo_block_dvd hp2 hn1 hdeg'' fun u hu hsupp => s7_lo_hsup hn' h1 h2 hmod'' htl hu hsupp
      · have hT : (13 * a + 4) * p ≤ t * p := Nat.mul_le_mul_right p (by omega)
        have e : (13 * a + 4) * p = 13 * (p * a) + 4 * p := by ring
        rw [sum_eq_zero fun u _ => Tlo_eq_zero_of_gt13 hn1 (by omega)]
        exact dvd_zero _
    · by_cases hth : 26 * a + 6 ≤ t
      · exact hi_block_dvd hp2 hn1 hdeg'' fun u hu hsupp => s7_hi_hsup hn' h1 h2 hmod'' hth hu hsupp
      · have hT : t * p ≤ (26 * a + 5) * p := Nat.mul_le_mul_right p (by omega)
        have e : (26 * a + 5) * p = 26 * (p * a) + 5 * p := by ring
        rw [sum_eq_zero fun u hu => Thi_eq_zero_of_le26 hn1 (by have := mem_range.mp hu; omega)]
        exact dvd_zero _

/-! ## `RestAboveOpen`, narrowed to the four φ̃ = 2 strata -/

/-- **The `m ≥ p²` half, narrowed past `[3/13, 4/17)`**: the polar rows on the four φ̃ = 2 strata. -/
def RestAboveS2Open : Prop :=
  ∀ n p r : ℕ, p ∈ Zeta2PhiT.phiWindow n → r < 16 * n → p ∣ r + 1 →
    Zeta2PtpKumRows.RunStrata p (n % p) →
    ¬ (3 * p ≤ 13 * (n % p) ∧ 17 * (n % p) < 4 * p) →
    p ^ 2 ≤ 11 * n + 1 + r →
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ)

theorem restAboveOpen_of_S2 (h : RestAboveS2Open) : Zeta2PtpMbig.RestAboveOpen := by
  intro n p r hp hr hpol hrun hm
  by_cases hs7 : 3 * p ≤ 13 * (n % p) ∧ 17 * (n % p) < 4 * p
  · exact coeff_runHigh_S7 hp hr hpol hm hs7.1 hs7.2
  · exact h n p r hp hr hpol hrun hs7 hm

/-- **THE POLYNOMIAL HALF OF PT-P, ON THE FOUR φ̃ = 2 STRATA ABOVE `p²` ALONE.** -/
theorem polyHalfOpen_of_S2 (h : RestAboveS2Open) : Zeta2PtpPolar.PolyHalfOpen :=
  Zeta2PtpMbig.polyHalfOpen_of_above (restAboveOpen_of_S2 h)

end Zeta2PtpMbigS7

#print axioms Zeta2PtpMbigS7.mod_sub_block
#check @Zeta2PtpMbigS7.mod_sub_block
#print axioms Zeta2PtpMbigS7.supp_of_kum0
#check @Zeta2PtpMbigS7.supp_of_kum0
#print axioms Zeta2PtpMbigS7.s7_lo_low
#check @Zeta2PtpMbigS7.s7_lo_low
#print axioms Zeta2PtpMbigS7.s7_lam
#check @Zeta2PtpMbigS7.s7_lam
#print axioms Zeta2PtpMbigS7.coeff_runHigh_S7
#check @Zeta2PtpMbigS7.coeff_runHigh_S7
#print axioms Zeta2PtpMbigS7.restAboveOpen_of_S2
#check @Zeta2PtpMbigS7.restAboveOpen_of_S2
#print axioms Zeta2PtpMbigS7.polyHalfOpen_of_S2
#check @Zeta2PtpMbigS7.polyHalfOpen_of_S2
#print Zeta2PtpMbigS7.RestAboveS2Open
