/-
# Row PT-P, part (b), layer 3 — THE φ̃ = 2 CUBE BLOCK LEMMA above `p²`: Anton at three digits

On the two φ̃ = 2 run strata whose carried factor is `C(m, i)` (`[6/13, 7/15)`, `[12/13, 14/15)`),
at a polar row `m = p² + μ ≥ p²`, every MIDDLE block `t` (`⌊μ/p⌋ < t < p`) of `h_m` has to be
`0 mod p³`.  There `C(m, tp + u)` carries in the TENS digit always and in the units digit exactly
when `u > m mod p` (`ptp_mbig_phi2_probe.py`), so `v_p C = 2` on the short residues, and Anton's
general-`κ` congruence (`Zeta2Anton.choose_div_pow_mul_eq`, three digits) gives the unit part:

    C(m, tp + u) / p²  ≡  m₀! · m₁! / (u! · t! · (p + m₀ − u)! · (p + m₁ − 1 − t)!)     (mod p)

— the SAME `u`-shape `m₀!/(u!(p + m₀ − u)!)` as the two-digit `Zeta2PtpRunG2.choose_m_div_eq`,
so Wilson's reflection (`Zeta2PtpS2Kit.factorial_inv_eq_denLow`) gives `Den(u)⁻¹` over `rootsLow`
and the sibling's abstract `Zeta2PtpRunG2.sq_dvd_of_quot` applies to `T/p` (`choose_m_div_sq_eq`,
`Thi_div_sq_eq_hi4`, **`hi4_block_cube`**).  This includes the block `t = p − 1` that has no
two-digit helper row — no helper row is used at all.

Probe: `ptp_mbig_phi2_probe.py` / `.out`.  Runner: `run_resid.sh`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2PtpFold
import Zeta2PtpRunS2

set_option maxRecDepth 20000

namespace Zeta2PtpMbigG2

open Zeta2PtpRunG2 Zeta2PtpRunBlock Zeta2PtpBlock Zeta2PtpS2Kit Finset Polynomial Nat

open Zeta2PtpFold (hsum)
open Zeta2NewtonAssemble (Hfun)

section G
variable {p : ℕ} [hp : Fact p.Prime]

/-- The digits of a three-digit `m ∈ [p², 2p²)`: `m = p·p + m₁·p + m₀`. -/
theorem digits3 {m : ℕ} (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2) :
    m = p * p + (m / p % p) * p + m % p ∧ m / p ^ 2 = 1 := by
  have hp0 := hp.out.pos
  have hq : m / p ^ 2 = 1 := Nat.div_eq_of_lt_le (by rw [one_mul]; exact hm) (by omega)
  have h1 := Nat.div_add_mod m p
  have h2 := Nat.div_add_mod (m / p) p
  rw [Nat.div_div_eq_div_mul, ← sq, hq, mul_one] at h2
  refine ⟨?_, hq⟩
  have e : m / p = p + m / p % p := by omega
  calc m = p * (m / p) + m % p := h1.symm
    _ = p * (p + m / p % p) + m % p := by rw [← e]
    _ = p * p + (m / p % p) * p + m % p := by ring

/-- **Anton at three digits, two carries**: `C(m, tp + u)/p²` for `m ∈ [p², 2p²)`,
`m₁ < t < p`, `u > m₀`. -/
theorem choose_m_div_sq_eq (hp2 : 2 < p) {m t u : ℕ} (hu : u < p) (hc : m % p < u)
    (ht1 : m / p % p ≤ t) (htp : t < p) (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2) :
    ((m.choose (t * p + u) / p ^ 2 : ℕ) : ZMod p)
      = (-1) ^ (m % p + u) * (((m % p)! : ℕ) : ZMod p)
        * ((((m / p % p)! : ℕ) : ZMod p) * (((t)! : ℕ) : ZMod p)⁻¹
          * (((p + m / p % p - 1 - t)! : ℕ) : ZMod p)⁻¹)
        * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹ := by
  have hp0 := hp.out.pos
  obtain ⟨hmd, hm2d⟩ := digits3 hm hm2
  have hM0 := Nat.mod_lt m hp0
  have hM1 := Nat.mod_lt (m / p) hp0
  generalize hM0d : m % p = M₀ at *
  generalize hM1d : m / p % p = M₁ at *
  have hpp : t * p + p ≤ p * p := by
    have := Nat.mul_le_mul_right p htp
    rwa [Nat.succ_mul] at this
  have htt : M₁ * p ≤ t * p := Nat.mul_le_mul_right p ht1
  have hb : t * p + u ≤ m := by omega
  have hbp : t * p + u < p ^ 2 := by rw [sq]; omega
  set E := p + M₁ - 1 - t with hEdef
  have hE : E + t + 1 = p + M₁ := by omega
  have hEp : E * p + t * p + p = p * p + M₁ * p := by
    rw [show E * p + t * p + p = (E + t + 1) * p by ring, hE, add_mul]
  have hEle : E * p + p ≤ p * p := by
    have : E + 1 ≤ p := by omega
    have := Nat.mul_le_mul_right p this
    rwa [Nat.succ_mul] at this
  have hD : m - (t * p + u) = (p + M₀ - u) + E * p := by omega
  have hDmod : (m - (t * p + u)) % p = p + M₀ - u := by
    rw [hD]; exact mod_of_lin hp0 rfl (by omega)
  have hDdiv : (m - (t * p + u)) / p % p = E := by
    rw [hD, div_of_lin hp0 rfl (by omega : p + M₀ - u < p), Nat.mod_eq_of_lt (by omega)]
  have hDsq : (m - (t * p + u)) / p ^ 2 % p = 0 := by
    rw [Nat.div_eq_of_lt (by rw [hD, sq]; omega)]
    simp
  have hbmod : (t * p + u) % p = u := mod_of_lin hp0 (by ring) hu
  have hbdiv : (t * p + u) / p % p = t := by
    rw [div_of_lin hp0 (by ring) hu, Nat.mod_eq_of_lt htp]
  have hbsq : (t * p + u) / p ^ 2 % p = 0 := by
    rw [Nat.div_eq_of_lt hbp]
    simp
  have hmmod : m % p = M₀ := hM0d
  have hmdiv : m / p % p = M₁ := hM1d
  have hmsq : m / p ^ 2 % p = 1 := by rw [hm2d]; exact Nat.mod_eq_of_lt hp.out.one_lt
  have hm3 : m < p ^ 3 := by
    have : p ^ 3 = p * p ^ 2 := by ring
    have : 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hv : padicValNat p (m.choose (t * p + u)) = 2 := by
    rw [Zeta2PtpResPair.padicValNat_choose_eq_cb_succ hb hm hm3 hbp (by rw [sq]; omega)]
    unfold Zeta2PtpRun.cb
    rw [hmmod, hbmod]
    simp [hc]
  have h := Zeta2Anton.choose_div_pow_mul_eq (p := p) (N := 3) hb hm3
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, Nat.div_one,
    one_mul] at h
  rw [hv, hmmod, hmdiv, hmsq, hbmod, hbdiv, hbsq, hDmod, hDdiv, hDsq] at h
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_one] at h
  have hu0 : ((u ! : ℕ) : ZMod p) ≠ 0 := Zeta2Anton.cast_factorial_ne_zero_of_lt hu
  have ht0 : ((t ! : ℕ) : ZMod p) ≠ 0 := Zeta2Anton.cast_factorial_ne_zero_of_lt htp
  have hF0 : (((p + M₀ - u)! : ℕ) : ZMod p) ≠ 0 :=
    Zeta2Anton.cast_factorial_ne_zero_of_lt (by omega)
  have hE0 : ((E ! : ℕ) : ZMod p) ≠ 0 := Zeta2Anton.cast_factorial_ne_zero_of_lt (by omega)
  have h' : ((m.choose (t * p + u) / p ^ 2 : ℕ) : ZMod p)
      * ((((u ! : ℕ) : ZMod p) * ((t ! : ℕ) : ZMod p))
        * ((((p + M₀ - u)! : ℕ) : ZMod p) * ((E ! : ℕ) : ZMod p)))
      = ((M₀ ! : ℕ) : ZMod p) * ((M₁ ! : ℕ) : ZMod p) := by
    linear_combination h
  have hx := (eq_mul_inv_iff_mul_eq₀ (mul_ne_zero (mul_ne_zero hu0 ht0) (mul_ne_zero hF0 hE0))).mpr h'
  rw [hx, rootsLow_eval hc]
  have hW := factorial_inv_eq_denLow (p := p) (e := M₀) (X₀ := u) hc hu (by omega)
  rw [show M₀ + p - u = p + M₀ - u by omega] at hW
  linear_combination (((M₁ ! : ℕ) : ZMod p) * ((t ! : ℕ) : ZMod p)⁻¹ * ((E ! : ℕ) : ZMod p)⁻¹) * hW

/-- The block constant when `C(m, i)` carries twice (units and tens). -/
noncomputable def k4sq (p n m t h1 h2 h3 : ℕ) : ZMod p :=
  (-1) ^ (m + t) * (-1) ^ (m % p) * (((Nat.factorial (m % p)) : ℕ) : ZMod p)
    * ((((m / p % p)! : ℕ) : ZMod p) * (((Nat.factorial t : ℕ) : ZMod p))⁻¹
        * (((p + m / p % p - 1 - t)! : ℕ) : ZMod p)⁻¹)
    * ((h1.choose (13 * n / p) : ℕ) : ZMod p) * ((h2.choose (9 * n / p) : ℕ) : ZMod p)
    * ((h3.choose (5 * n / p) : ℕ) : ZMod p)

/-- **The TAIL term over `p²`, in the block's own shape**, at a double carry of `C(m, i)`. -/
theorem Thi_div_sq_eq_hi4 (hp2 : 2 < p) {n m t u h1 h2 h3 : ℕ} (hu : u < p) (hc : m % p < u)
    (ht1 : m / p % p ≤ t) (htp : t < p) (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2)
    (htr : 17 * n + 1 ≤ t * p + u)
    (e1 : (t * p + u - (13 * n + 1)) / p = h1) (e2 : (t * p + u - (15 * n + 1)) / p = h2)
    (e3 : (t * p + u - (17 * n + 1)) / p = h3) :
    ((Thi n m (t * p + u) / (p : ℤ) ^ 2 : ℤ) : ZMod p)
      = k4sq p n m t h1 h2 h3 * ((Nhi4 p n).eval (u : ZMod p)
          * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹) := by
  have hp0 := hp.out.pos
  have hv := choose_m_div_sq_eq hp2 hu hc ht1 htp hm hm2
  have hdvd : p ^ 2 ∣ m.choose (t * p + u) := by
    have hm3 : m < p ^ 3 := by
      have : p ^ 3 = p * p ^ 2 := by ring
      have : 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨hmd, _⟩ := digits3 hm hm2
    have hpp : t * p + p ≤ p * p := by
      have := Nat.mul_le_mul_right p htp
      rwa [Nat.succ_mul] at this
    have htt : m / p % p * p ≤ t * p := Nat.mul_le_mul_right p ht1
    have hbmod : (t * p + u) % p = u := mod_of_lin hp0 (by ring) hu
    have hsqp : p ^ 2 = p * p := sq p
    have hv2 : padicValNat p (m.choose (t * p + u)) = 2 := by
      rw [Zeta2PtpResPair.padicValNat_choose_eq_cb_succ (by omega) hm hm3 (by rw [sq]; omega)
        (by rw [sq]; omega)]
      unfold Zeta2PtpRun.cb
      rw [hbmod]
      simp [hc]
    rw [← hv2]
    exact pow_padicValNat_dvd
  obtain ⟨q, hq⟩ := hdvd
  have hq' : m.choose (t * p + u) / p ^ 2 = q := by
    rw [hq, Nat.mul_div_cancel_left _ (by positivity)]
  rw [hq'] at hv
  have hT : Thi n m (t * p + u) = (p : ℤ) ^ 2 * ((-1 : ℤ) ^ (m + (t * p + u)) * (q : ℤ)
      * (((t * p + u - (13 * n + 1)).choose (13 * n) : ℕ) : ℤ)
      * (((t * p + u - (15 * n + 1)).choose (9 * n) : ℕ) : ℤ)
      * (((t * p + u - (17 * n + 1)).choose (5 * n) : ℕ) : ℤ)) := by
    rw [Thi_nat, hq]; push_cast; ring
  rw [hT, Int.mul_ediv_cancel_left _ (by positivity)]
  push_cast
  rw [sign_block hp2, lucas_factor (t * p + u - (13 * n + 1)) (13 * n),
    lucas_factor (t * p + u - (15 * n + 1)) (9 * n), lucas_factor (t * p + u - (17 * n + 1)) (5 * n),
    e1, e2, e3, cast_block_sub (by omega), cast_block_sub (by omega), cast_block_sub htr, hv]
  unfold k4sq Nhi4
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X]
  rw [pow_add (-1 : ZMod p) (m % p) u]
  push_cast
  rcases Nat.even_or_odd u with hpar | hpar
  · rw [hpar.neg_one_pow]; ring
  · rw [hpar.neg_one_pow]; ring

theorem div_p_of_sq {z : ℤ} (h : (p : ℤ) ^ 2 ∣ z) : (p : ℤ) ∣ z / p := by
  obtain ⟨w, rfl⟩ := h
  rw [sq, mul_assoc, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.out.ne_zero)]
  exact dvd_mul_right _ _

theorem sq_div_p_of_cube {z : ℤ} (h : (p : ℤ) ^ 3 ∣ z) : (p : ℤ) ^ 2 ∣ z / p := by
  obtain ⟨w, rfl⟩ := h
  rw [show (p : ℤ) ^ 3 * w = (p : ℤ) * ((p : ℤ) ^ 2 * w) by ring,
    Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.out.ne_zero)]
  exact dvd_mul_right _ _

theorem div_div_of_sq {z : ℤ} (h : (p : ℤ) ^ 2 ∣ z) : z / p / p = z / (p : ℤ) ^ 2 := by
  obtain ⟨w, rfl⟩ := h
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [sq, mul_assoc, Int.mul_ediv_cancel_left _ hp0, Int.mul_ediv_cancel_left _ hp0,
    ← mul_assoc, Int.mul_ediv_cancel_left _ (mul_ne_zero hp0 hp0)]

/-- **THE CUBE BLOCK LEMMA (TAIL).**  If every `C(m, tp + u)` is `0 mod p`, and `0 mod p²` where
it carries in the units digit, the sibling's residue facts (`hone`, `htwo`) and degree bound hold,
and on the one-carry set `T/p² ≡ κ·N/Den`, then the block is `0 mod p³`. -/
theorem hi4_block_cube {n m t : ℕ} (hn : 1 ≤ n)
    (hdeg : (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2 + (m % p + 1))
    (hone : ∀ u < p, cHi1 p n u ∨ cHi2 p n u ∨ cHi3 p n u ∨ c4 p m u)
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cHi1 p n u ∧ cHi2 p n u) ∨ (cHi1 p n u ∧ cHi3 p n u) ∨ (cHi2 p n u ∧ cHi3 p n u))
    (hT1 : ∀ u < p, p ∣ m.choose (t * p + u))
    (hT2 : ∀ u < p, c4 p m u → p ^ 2 ∣ m.choose (t * p + u))
    (κ : ZMod p)
    (hid : ∀ u < p, c4 p m u → ¬ cHi1 p n u → ¬ cHi2 p n u → ¬ cHi3 p n u →
      ((Thi n m (t * p + u) / (p : ℤ) ^ 2 : ℤ) : ZMod p)
        = κ * ((Nhi4 p n).eval (u : ZMod p)
          * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹)) :
    (p : ℤ) ^ 3 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) := by
  have hp0 := hp.out.pos
  have hm0 := Nat.mod_lt m hp0
  have f1 : ∀ u < p, cHi1 p n u → p ∣ (t * p + u - (13 * n + 1)).choose (13 * n) :=
    fun u hu h => dvd_choose_of_carry_up hu (by omega) h
  have f2 : ∀ u < p, cHi2 p n u → p ∣ (t * p + u - (15 * n + 1)).choose (9 * n) :=
    fun u hu h => dvd_choose_of_carry_up hu (by omega) h
  have f3 : ∀ u < p, cHi3 p n u → p ∣ (t * p + u - (17 * n + 1)).choose (5 * n) :=
    fun u hu h => dvd_choose_of_carry_up hu (by omega) h
  -- `p^k ∣ C·H` lifts to `p^k ∣ Thi`
  have lift : ∀ u k, p ^ k ∣ m.choose (t * p + u) * ((t * p + u - (13 * n + 1)).choose (13 * n)
      * (t * p + u - (15 * n + 1)).choose (9 * n) * (t * p + u - (17 * n + 1)).choose (5 * n)) →
      (p : ℤ) ^ k ∣ Thi n m (t * p + u) := by
    intro u k h
    rw [Thi_nat]
    exact Dvd.dvd.mul_left (by exact_mod_cast Int.natCast_dvd_natCast.2 h) _
  -- the H part divisible by `p` at one carry, by `p²` at two
  have hH1 : ∀ u < p, (cHi1 p n u ∨ cHi2 p n u ∨ cHi3 p n u) →
      p ∣ (t * p + u - (13 * n + 1)).choose (13 * n) * (t * p + u - (15 * n + 1)).choose (9 * n)
        * (t * p + u - (17 * n + 1)).choose (5 * n) := by
    intro u hu h
    rcases h with h | h | h
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (f1 u hu h) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (f2 u hu h) _) _
    · exact Dvd.dvd.mul_left (f3 u hu h) _
  have hH2 : ∀ u < p, ¬ c4 p m u →
      p ^ 2 ∣ (t * p + u - (13 * n + 1)).choose (13 * n) * (t * p + u - (15 * n + 1)).choose (9 * n)
        * (t * p + u - (17 * n + 1)).choose (5 * n) := by
    intro u hu h4
    rw [sq]
    rcases htwo u hu h4 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Dvd.dvd.mul_right (mul_dvd_mul (f1 u hu ha) (f2 u hu hb)) _
    · rw [mul_right_comm]
      exact Dvd.dvd.mul_right (mul_dvd_mul (f1 u hu ha) (f3 u hu hb)) _
    · rw [mul_assoc]
      exact Dvd.dvd.mul_left (mul_dvd_mul (f2 u hu ha) (f3 u hu hb)) _
  -- `p² ∣ T` everywhere, `p³ ∣ T` off the one-carry set
  have hsq : ∀ u < p, (p : ℤ) ^ 2 ∣ Thi n m (t * p + u) := by
    intro u hu
    refine lift u 2 ?_
    by_cases h4 : c4 p m u
    · exact Dvd.dvd.mul_right (hT2 u hu h4) _
    · rw [sq]
      exact mul_dvd_mul (hT1 u hu) ((dvd_pow_self p two_ne_zero).trans (hH2 u hu h4))
  have hcube : ∀ u < p, (¬ c4 p m u ∨ (c4 p m u ∧ (cHi1 p n u ∨ cHi2 p n u ∨ cHi3 p n u))) →
      (p : ℤ) ^ 3 ∣ Thi n m (t * p + u) := by
    intro u hu h
    refine lift u 3 ?_
    rcases h with h4 | ⟨h4, hc⟩
    · rw [show 3 = 1 + 2 by rfl, pow_add, pow_one]
      exact mul_dvd_mul (hT1 u hu) (hH2 u hu h4)
    · rw [show 3 = 2 + 1 by rfl, pow_add, pow_one]
      exact mul_dvd_mul (hT2 u hu h4) (hH1 u hu hc)
  have hmain : (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) / p := by
    refine sq_dvd_of_quot (fun u => Thi n m (t * p + u) / p) κ (Nhi4 p n)
      (rootsLow p (m % p)) (rootsLow_nodup hm0) ?_ ?_ ?_ ?_
    · rw [rootsLow_card]
      exact (Nhi4_natDegree_le n).trans hdeg
    · intro u hu
      exact div_p_of_sq (hsq u hu)
    · intro u hu hm
      have hn4 : ¬ c4 p m u := by unfold c4; have := (mem_rootsLow hu hm0).1 hm; omega
      refine ⟨cast_div_zero_of_sq (sq_div_p_of_cube (hcube u hu (Or.inl hn4))), ?_⟩
      unfold Nhi4
      rcases htwo u hu hn4 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact X_sub_C_sq_dvd_of_two (binPoly_up_isRoot ha) (binPoly_up_isRoot hb)
      · rw [mul_right_comm]
        exact X_sub_C_sq_dvd_of_two (binPoly_up_isRoot ha) (binPoly_up_isRoot hb)
      · rw [pow_two, mul_assoc]
        exact (mul_dvd_mul (dvd_iff_isRoot.2 (binPoly_up_isRoot ha))
          (dvd_iff_isRoot.2 (binPoly_up_isRoot hb))).mul_left _
    · intro u hu hm
      have h4 : c4 p m u := by
        unfold c4
        by_contra h
        exact hm ((mem_rootsLow hu hm0).2 (by omega))
      show ((Thi n m (t * p + u) / p / p : ℤ) : ZMod p) = _
      by_cases hrest : ¬ cHi1 p n u ∧ ¬ cHi2 p n u ∧ ¬ cHi3 p n u
      · rw [div_div_of_sq (hsq u hu)]
        exact hid u hu h4 hrest.1 hrest.2.1 hrest.2.2
      · have hN : (Nhi4 p n).eval (u : ZMod p) = 0 := by
          unfold Nhi4
          by_cases h1 : cHi1 p n u
          · exact isRoot_mul_left' (isRoot_mul_left' (binPoly_up_isRoot h1))
          by_cases h2 : cHi2 p n u
          · exact isRoot_mul_left' (isRoot_mul_right' (binPoly_up_isRoot h2))
          have h3 : cHi3 p n u := by tauto
          exact isRoot_mul_right' (binPoly_up_isRoot h3)
        rw [hN, zero_mul, mul_zero]
        have hc3 : cHi1 p n u ∨ cHi2 p n u ∨ cHi3 p n u := by tauto
        exact cast_div_zero_of_sq (sq_div_p_of_cube (hcube u hu (Or.inr ⟨h4, hc3⟩)))
  have hsum : ∑ u ∈ Finset.range p, Thi n m (t * p + u)
      = (p : ℤ) * ∑ u ∈ Finset.range p, Thi n m (t * p + u) / p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    exact (Int.mul_ediv_cancel' ((dvd_pow_self (p : ℤ) two_ne_zero).trans
      (hsq u (Finset.mem_range.mp hu)))).symm
  rw [hsum, show (3 : ℕ) = 1 + 2 by rfl, pow_add, pow_one]
  exact mul_dvd_mul_left _ hmain

/-- The tens-and-units carry facts of `C(m, tp + u)` at a middle block above `p²`. -/
theorem choose_mid_dvd {m t u : ℕ} (hu : u < p) (ht1 : m / p % p < t) (htp : t < p)
    (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2) :
    p ∣ m.choose (t * p + u) ∧ (m % p < u → p ^ 2 ∣ m.choose (t * p + u)) := by
  have hp0 := hp.out.pos
  obtain ⟨hmd, _⟩ := digits3 hm hm2
  have hm3 : m < p ^ 3 := by
    have : p ^ 3 = p * p ^ 2 := by ring
    have : 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpp : t * p + p ≤ p * p := by
    have := Nat.mul_le_mul_right p htp
    rwa [Nat.succ_mul] at this
  generalize m / p % p = M₁ at hmd ht1
  have htt : (M₁ + 1) * p ≤ t * p := Nat.mul_le_mul_right p ht1
  have e1 : (M₁ + 1) * p = M₁ * p + p := by ring
  have hbmod : (t * p + u) % p = u := mod_of_lin hp0 (by ring) hu
  have hsqp : p ^ 2 = p * p := sq p
  have hM0 := Nat.mod_lt m hp0
  have hv := Zeta2PtpResPair.padicValNat_choose_eq_cb_succ (p := p) (S := m) (A := t * p + u)
    (by omega) hm hm3 (by rw [sq]; omega) (by rw [sq]; omega)
  refine ⟨?_, fun hc => ?_⟩
  · have : 1 ≤ padicValNat p (m.choose (t * p + u)) := by rw [hv]; omega
    exact (pow_one p ▸ pow_dvd_pow p this).trans pow_padicValNat_dvd
  · have : 2 ≤ padicValNat p (m.choose (t * p + u)) := by
      rw [hv]
      unfold Zeta2PtpRun.cb
      rw [hbmod]
      simp [hc]
    exact (pow_dvd_pow p this).trans pow_padicValNat_dvd

/-- `p² ∣ C(m, tp + u)` at a units carry with `m₁ ≤ t < p` (units AND tens carry). -/
theorem choose_sq_dvd_two {m t u : ℕ} (hu : u < p) (hc : m % p < u) (ht1 : m / p % p ≤ t)
    (htp : t < p) (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2) :
    p ^ 2 ∣ m.choose (t * p + u) := by
  have hp0 := hp.out.pos
  obtain ⟨hmd, _⟩ := digits3 hm hm2
  have hm3 : m < p ^ 3 := by
    have : p ^ 3 = p * p ^ 2 := by ring
    have : 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpp : t * p + p ≤ p * p := by
    have := Nat.mul_le_mul_right p htp
    rwa [Nat.succ_mul] at this
  generalize m / p % p = M₁ at hmd ht1
  have htt : M₁ * p ≤ t * p := Nat.mul_le_mul_right p ht1
  have hbmod : (t * p + u) % p = u := mod_of_lin hp0 (by ring) hu
  have hsqp : p ^ 2 = p * p := sq p
  have hv := Zeta2PtpResPair.padicValNat_choose_eq_cb_succ (p := p) (S := m) (A := t * p + u)
    (by omega) hm hm3 (by rw [sq]; omega) (by rw [sq]; omega)
  have : 2 ≤ padicValNat p (m.choose (t * p + u)) := by
    rw [hv]
    unfold Zeta2PtpRun.cb
    rw [hbmod]
    simp [hc]
  exact (pow_dvd_pow p this).trans pow_padicValNat_dvd

/-- **The LO term over `p²`** at a double carry of `C(m, i)` (`m₁ ≤ t < p`, `u > m₀`). -/
theorem Tlo_div_sq_eq_lo4 (hp2 : 2 < p) {n m t u h1 h2 h3 : ℕ} (hu : u < p) (hc : m % p < u)
    (ht1 : m / p % p ≤ t) (htp : t < p) (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2)
    (htr : t * p + u ≤ 22 * n)
    (e1 : (26 * n - (t * p + u)) / p = h1) (e2 : (24 * n - (t * p + u)) / p = h2)
    (e3 : (22 * n - (t * p + u)) / p = h3) :
    ((Tlo n m (t * p + u) / (p : ℤ) ^ 2 : ℤ) : ZMod p)
      = k4sq p n m t h1 h2 h3 * ((Nlo4 p n).eval (u : ZMod p)
          * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹) := by
  have hp0 := hp.out.pos
  have hv := choose_m_div_sq_eq hp2 hu hc ht1 htp hm hm2
  obtain ⟨q, hq⟩ := choose_sq_dvd_two hu hc ht1 htp hm hm2
  have hq' : m.choose (t * p + u) / p ^ 2 = q := by
    rw [hq, Nat.mul_div_cancel_left _ (by positivity)]
  rw [hq'] at hv
  have hT : Tlo n m (t * p + u) = (p : ℤ) ^ 2 * ((-1 : ℤ) ^ (m + (t * p + u)) * (q : ℤ)
      * (((26 * n - (t * p + u)).choose (13 * n) : ℕ) : ℤ)
      * (((24 * n - (t * p + u)).choose (9 * n) : ℕ) : ℤ)
      * (((22 * n - (t * p + u)).choose (5 * n) : ℕ) : ℤ)) := by
    rw [Tlo_def, hq]; push_cast; ring
  rw [hT, Int.mul_ediv_cancel_left _ (by positivity)]
  push_cast
  rw [sign_block hp2, lucas_factor (26 * n - (t * p + u)) (13 * n),
    lucas_factor (24 * n - (t * p + u)) (9 * n), lucas_factor (22 * n - (t * p + u)) (5 * n),
    e1, e2, e3, cast_sub_block (by omega), cast_sub_block (by omega), cast_sub_block htr, hv]
  unfold k4sq Nlo4
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X]
  rw [pow_add (-1 : ZMod p) (m % p) u]
  rcases Nat.even_or_odd u with hpar | hpar
  · rw [hpar.neg_one_pow]; ring
  · rw [hpar.neg_one_pow]; ring

/-- **THE CUBE BLOCK LEMMA (LO), restricted to the `C(m, i)`-carry residues** `u > m mod p`. -/
theorem lo4_cube_c4 {n m t : ℕ} (hn : 1 ≤ n)
    (hdeg : (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2 + (m % p + 1))
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cLo1 p n u ∧ cLo2 p n u) ∨ (cLo1 p n u ∧ cLo3 p n u) ∨ (cLo2 p n u ∧ cLo3 p n u))
    (hT2 : ∀ u < p, c4 p m u → p ^ 2 ∣ m.choose (t * p + u))
    (κ : ZMod p)
    (hid : ∀ u < p, c4 p m u → ¬ cLo1 p n u → ¬ cLo2 p n u → ¬ cLo3 p n u →
      ((Tlo n m (t * p + u) / (p : ℤ) ^ 2 : ℤ) : ZMod p)
        = κ * ((Nlo4 p n).eval (u : ZMod p)
          * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹)) :
    (p : ℤ) ^ 3 ∣ ∑ u ∈ Finset.range p, (if m % p < u then Tlo n m (t * p + u) else 0) := by
  have hp0 := hp.out.pos
  have hm0 := Nat.mod_lt m hp0
  have f1 : ∀ u < p, cLo1 p n u → p ∣ (26 * n - (t * p + u)).choose (13 * n) :=
    fun u hu h => dvd_choose_of_carry hu (by omega) h
  have f2 : ∀ u < p, cLo2 p n u → p ∣ (24 * n - (t * p + u)).choose (9 * n) :=
    fun u hu h => dvd_choose_of_carry hu (by omega) h
  have f3 : ∀ u < p, cLo3 p n u → p ∣ (22 * n - (t * p + u)).choose (5 * n) :=
    fun u hu h => dvd_choose_of_carry hu (by omega) h
  have lift : ∀ u k, p ^ k ∣ m.choose (t * p + u) * ((26 * n - (t * p + u)).choose (13 * n)
      * (24 * n - (t * p + u)).choose (9 * n) * (22 * n - (t * p + u)).choose (5 * n)) →
      (p : ℤ) ^ k ∣ Tlo n m (t * p + u) := by
    intro u k h
    rw [Tlo_nat]
    exact Dvd.dvd.mul_left (by exact_mod_cast Int.natCast_dvd_natCast.2 h) _
  have hsqc : ∀ u < p, c4 p m u → (p : ℤ) ^ 2 ∣ Tlo n m (t * p + u) :=
    fun u hu h4 => lift u 2 (Dvd.dvd.mul_right (hT2 u hu h4) _)
  have hcube : ∀ u < p, c4 p m u → (cLo1 p n u ∨ cLo2 p n u ∨ cLo3 p n u) →
      (p : ℤ) ^ 3 ∣ Tlo n m (t * p + u) := by
    intro u hu h4 hc
    refine lift u 3 ?_
    rw [show 3 = 2 + 1 by rfl, pow_add, pow_one]
    refine mul_dvd_mul (hT2 u hu h4) ?_
    rcases hc with h | h | h
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (f1 u hu h) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (f2 u hu h) _) _
    · exact Dvd.dvd.mul_left (f3 u hu h) _
  have hmain : (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p,
      (if m % p < u then Tlo n m (t * p + u) else 0) / p := by
    refine sq_dvd_of_quot (fun u => (if m % p < u then Tlo n m (t * p + u) else 0) / p) κ
      (Nlo4 p n) (rootsLow p (m % p)) (rootsLow_nodup hm0) ?_ ?_ ?_ ?_
    · rw [rootsLow_card]
      exact (Nlo4_natDegree_le n).trans hdeg
    · intro u hu
      by_cases h4 : m % p < u
      · simp only [h4, ite_true]
        exact div_p_of_sq (hsqc u hu h4)
      · simp [h4]
    · intro u hu hm
      have hn4 : ¬ c4 p m u := by unfold c4; have := (mem_rootsLow hu hm0).1 hm; omega
      have hn4' : ¬ m % p < u := hn4
      refine ⟨by simp [hn4'], ?_⟩
      unfold Nlo4
      rcases htwo u hu hn4 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact X_sub_C_sq_dvd_of_two (binPoly_down_isRoot hu ha) (binPoly_down_isRoot hu hb)
      · rw [mul_right_comm]
        exact X_sub_C_sq_dvd_of_two (binPoly_down_isRoot hu ha) (binPoly_down_isRoot hu hb)
      · rw [pow_two, mul_assoc]
        exact (mul_dvd_mul (dvd_iff_isRoot.2 (binPoly_down_isRoot hu ha))
          (dvd_iff_isRoot.2 (binPoly_down_isRoot hu hb))).mul_left _
    · intro u hu hm
      have h4 : c4 p m u := by
        unfold c4
        by_contra h
        exact hm ((mem_rootsLow hu hm0).2 (by omega))
      have h4' : m % p < u := h4
      show (((if m % p < u then Tlo n m (t * p + u) else 0) / p / p : ℤ) : ZMod p) = _
      simp only [h4', ite_true]
      by_cases hrest : ¬ cLo1 p n u ∧ ¬ cLo2 p n u ∧ ¬ cLo3 p n u
      · rw [div_div_of_sq (hsqc u hu h4)]
        exact hid u hu h4 hrest.1 hrest.2.1 hrest.2.2
      · have hN : (Nlo4 p n).eval (u : ZMod p) = 0 := by
          unfold Nlo4
          by_cases h1 : cLo1 p n u
          · exact isRoot_mul_left' (isRoot_mul_left' (binPoly_down_isRoot hu h1))
          by_cases h2 : cLo2 p n u
          · exact isRoot_mul_left' (isRoot_mul_right' (binPoly_down_isRoot hu h2))
          have h3 : cLo3 p n u := by tauto
          exact isRoot_mul_right' (binPoly_down_isRoot hu h3)
        rw [hN, zero_mul, mul_zero]
        have hc3 : cLo1 p n u ∨ cLo2 p n u ∨ cLo3 p n u := by tauto
        exact cast_div_zero_of_sq (sq_div_p_of_cube (hcube u hu h4 hc3))
  have hsum : ∑ u ∈ Finset.range p, (if m % p < u then Tlo n m (t * p + u) else 0)
      = (p : ℤ) * ∑ u ∈ Finset.range p, (if m % p < u then Tlo n m (t * p + u) else 0) / p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    by_cases h4 : m % p < u
    · simp only [h4, ite_true]
      exact (Int.mul_ediv_cancel' ((dvd_pow_self (p : ℤ) two_ne_zero).trans
        (hsqc u (Finset.mem_range.mp hu) h4))).symm
    · simp [h4]
  rw [hsum, show (3 : ℕ) = 1 + 2 by rfl, pow_add, pow_one]
  exact mul_dvd_mul_left _ hmain

/-- `⌊(X − A)/p⌋ = ⌊X/p⌋ − ⌊A/p⌋ − [borrow]`. -/
theorem floor_sub {X A : ℕ} (hA : A ≤ X) :
    (X - A) / p = X / p - A / p - (if X % p < A % p then 1 else 0) := by
  have hp0 := hp.out.pos
  have hX := Nat.div_add_mod X p
  have hAd := Nat.div_add_mod A p
  have hXl := Nat.mod_lt X hp0
  have hAl := Nat.mod_lt A hp0
  have ha1 : A / p ≤ X / p := Nat.div_le_div_right hA
  generalize X / p = x1 at *
  generalize X % p = x0 at *
  generalize A / p = a1 at *
  generalize A % p = a0 at *
  split_ifs with h
  · have hlt : a1 < x1 := by
      rcases Nat.lt_or_eq_of_le ha1 with h' | h'
      · exact h'
      · subst h'; omega
    have e : (x1 - a1 - 1) * p + p * a1 + p = p * x1 := by
      have e' : x1 - a1 - 1 + a1 + 1 = x1 := by omega
      calc (x1 - a1 - 1) * p + p * a1 + p = (x1 - a1 - 1 + a1 + 1) * p := by ring
        _ = p * x1 := by rw [e', mul_comm]
    exact div_of_lin hp0 (r := x0 + p - a0) (by omega) (by omega)
  · have e : (x1 - a1) * p + p * a1 = p * x1 := by
      have e' : x1 - a1 + a1 = x1 := by omega
      calc (x1 - a1) * p + p * a1 = (x1 - a1 + a1) * p := by ring
        _ = p * x1 := by rw [e', mul_comm]
    rw [Nat.sub_zero]
    exact div_of_lin hp0 (r := x0 - a0) (by omega) (by omega)

/-- **`λ` at a pair index, in the block's digits and carry bits.** -/
theorem lam_pair_eq {n m t u : ℕ} (hu : u < p) (hpair : t * p + u ≤ m - p ^ 2)
    (hlo : t * p + u ≤ 13 * n) :
    Zeta2PtpFold.lam p n m (t * p + u) =
      hsum p 0 ((m - p ^ 2) / p - t - (if (m - p ^ 2) % p < u then 1 else 0)) - hsum p 0 t
      + (-hsum p ((26 * n - (t * p + u)) / p - 13 * n / p
            - (if ((26 * n) % p + p - u) % p < (13 * n) % p then 1 else 0))
            ((26 * n - (t * p + u)) / p)
         - hsum p ((24 * n - (t * p + u)) / p - 9 * n / p
            - (if ((24 * n) % p + p - u) % p < (9 * n) % p then 1 else 0))
            ((24 * n - (t * p + u)) / p)
         - hsum p ((22 * n - (t * p + u)) / p - 5 * n / p
            - (if ((22 * n) % p + p - u) % p < (5 * n) % p then 1 else 0))
            ((22 * n - (t * p + u)) / p)) := by
  have hp0 := hp.out.pos
  have hjdiv : (t * p + u) / p = t := div_of_lin hp0 (by ring) hu
  have hjmod : (t * p + u) % p = u := mod_of_lin hp0 (by ring) hu
  have e0 : m - (t * p + u) - p ^ 2 = (m - p ^ 2) - (t * p + u) := by omega
  have f0 := floor_sub (p := p) hpair
  rw [hjdiv, hjmod] at f0
  have e13 : 13 * n - (t * p + u) = (26 * n - (t * p + u)) - 13 * n := by omega
  have e15 : 15 * n - (t * p + u) = (24 * n - (t * p + u)) - 9 * n := by omega
  have e17 : 17 * n - (t * p + u) = (22 * n - (t * p + u)) - 5 * n := by omega
  have f13 := floor_sub (p := p) (X := 26 * n - (t * p + u)) (A := 13 * n) (by omega)
  have f15 := floor_sub (p := p) (X := 24 * n - (t * p + u)) (A := 9 * n) (by omega)
  have f17 := floor_sub (p := p) (X := 22 * n - (t * p + u)) (A := 5 * n) (by omega)
  rw [Zeta2PtpRunG2.mod_sub_block (by omega) hu] at f13 f15 f17
  unfold Zeta2PtpFold.lam Zeta2PtpFold.lamC Zeta2PtpFold.lamH
  rw [e0, f0, e13, f13, e15, f15, e17, f17, hjdiv]

/-- **THE FOLDED PAIR BLOCK, mod `p³`.**  Every pair term `0 mod p`; `λ` constant (`ℓ₀`) where a
pair term is not `0 mod p²`; every unpaired term `0 mod p³`; the raw block `0 mod p²`. -/
theorem pair_block_cube {n m t : ℕ} {ℓ₀ : ZMod p} (hsq : 26 * n + 1 < p ^ 2) (hm : p ^ 2 ≤ m)
    (hm2 : m < p ^ 2 + p ^ 2) (hμ : m - p ^ 2 < n)
    (hmin : ∀ u < p, t * p + u ≤ m - p ^ 2 → (p : ℤ) ∣ Zeta2PtpFold.Tm n m (t * p + u))
    (hconst : ∀ u < p, t * p + u ≤ m - p ^ 2 → ¬ (p : ℤ) ^ 2 ∣ Zeta2PtpFold.Tm n m (t * p + u)
      → Zeta2PtpFold.lam p n m (t * p + u) = ℓ₀)
    (hrest : ∀ u < p, m - p ^ 2 < t * p + u → (p : ℤ) ^ 3 ∣ Zeta2PtpFold.Tm n m (t * p + u))
    (hblk : (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Zeta2PtpFold.Tm n m (t * p + u)) :
    (p : ℤ) ^ 3 ∣ ∑ u ∈ Finset.range p,
      (Zeta2PtpFold.Tm n m (t * p + u) + Zeta2PtpFold.Tm n m (p ^ 2 + (t * p + u))) := by
  have hterm : ∀ u < p, (p : ℤ) ^ 3 ∣ Zeta2PtpFold.Tm n m (t * p + u)
      + Zeta2PtpFold.Tm n m (p ^ 2 + (t * p + u))
      + (p : ℤ) * ((ℓ₀.val : ℕ) : ℤ) * Zeta2PtpFold.Tm n m (t * p + u) := by
    intro u hu
    by_cases hpair : t * p + u ≤ m - p ^ 2
    · have e : Zeta2PtpFold.Tm n m (t * p + u) + Zeta2PtpFold.Tm n m (p ^ 2 + (t * p + u))
          + (p : ℤ) * ((ℓ₀.val : ℕ) : ℤ) * Zeta2PtpFold.Tm n m (t * p + u)
          = (Zeta2PtpFold.Tm n m (t * p + u) + Zeta2PtpFold.Tm n m (p ^ 2 + (t * p + u))
            + (p : ℤ) * (((Zeta2PtpFold.lam p n m (t * p + u)).val : ℕ) : ℤ)
              * Zeta2PtpFold.Tm n m (t * p + u))
          + (p : ℤ) * (((ℓ₀.val : ℕ) : ℤ) - ((Zeta2PtpFold.lam p n m (t * p + u)).val : ℤ))
            * Zeta2PtpFold.Tm n m (t * p + u) := by ring
      rw [e]
      by_cases hT : (p : ℤ) ^ 2 ∣ Zeta2PtpFold.Tm n m (t * p + u)
      · have hf := Zeta2PtpFold.fold_law (p := p) (n := n) (m := m) (j := t * p + u) (K := 2) hsq
          (by omega) (by omega) hm2 hT
        refine dvd_add ((pow_dvd_pow _ (by omega)).trans hf) ?_
        obtain ⟨c, hc⟩ := hT
        rw [hc]
        exact ⟨(((ℓ₀.val : ℕ) : ℤ) - ((Zeta2PtpFold.lam p n m (t * p + u)).val : ℤ)) * c, by ring⟩
      · have hf := Zeta2PtpFold.fold_law (p := p) (n := n) (m := m) (j := t * p + u) (K := 1) hsq
          (by omega) (by omega) hm2 (by rw [pow_one]; exact hmin u hu hpair)
        rw [hconst u hu hpair hT, sub_self, mul_zero, zero_mul, add_zero]
        rw [hconst u hu hpair hT] at hf
        exact hf
    · have h0 : Zeta2PtpFold.Tm n m (p ^ 2 + (t * p + u)) = 0 := by
        unfold Zeta2PtpFold.Tm
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      have hr := hrest u hu (by omega)
      rw [h0, add_zero]
      refine dvd_add hr ?_
      obtain ⟨c, hc⟩ := hr
      rw [hc]
      exact ⟨(p : ℤ) * ((ℓ₀.val : ℕ) : ℤ) * c, by ring⟩
  have hsum_t : (p : ℤ) ^ 3 ∣ ∑ u ∈ Finset.range p, (Zeta2PtpFold.Tm n m (t * p + u)
      + Zeta2PtpFold.Tm n m (p ^ 2 + (t * p + u))
      + (p : ℤ) * ((ℓ₀.val : ℕ) : ℤ) * Zeta2PtpFold.Tm n m (t * p + u)) :=
    Finset.dvd_sum fun u hu => hterm u (Finset.mem_range.mp hu)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_t
  have h2 : (p : ℤ) ^ 3 ∣ (p : ℤ) * ((ℓ₀.val : ℕ) : ℤ)
      * ∑ u ∈ Finset.range p, Zeta2PtpFold.Tm n m (t * p + u) := by
    obtain ⟨c, hc⟩ := hblk
    rw [hc]
    exact ⟨((ℓ₀.val : ℕ) : ℤ) * c, by ring⟩
  have := dvd_sub hsum_t h2
  rwa [add_sub_cancel_right] at this

/-- **THE MIDDLE BLOCK, mod `p³`**: `mid_block_sq` with every `H` term divisible by `p` and the
reduced row's block `0 mod p²`. -/
theorem mid_block_cube {n m t : ℕ} (hM : 1 ≤ m / p) (hMt : p ∣ (m / p).choose t)
    (htm : t * p + p ≤ m + 1)
    (hH : ∀ u < p, (p : ℤ) ∣ Hfun n ↑(t * p + u))
    (hsum2 : (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Zeta2PtpFold.Tm n (t * p + m % p) (t * p + u)) :
    (p : ℤ) ^ 3 ∣ ∑ u ∈ Finset.range p, Zeta2PtpFold.Tm n m (t * p + u) := by
  have hp0 := hp.out.pos
  have hmlt := Nat.mod_lt m hp0
  have hdm := Nat.div_add_mod m p
  have hc : (p : ℤ) ∣ (((p * (m / p)).choose (p * t) : ℕ) : ℤ) := by
    exact_mod_cast Zeta2PtpFold.dvd_choose_mul hMt
  obtain ⟨e, he⟩ := hc
  have h''mod : (t * p + m % p) % p = m % p := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmlt]
  have h''div : (t * p + m % p) / p = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hmlt, zero_add]
  have hterm : ∀ u < p, (p : ℤ) ^ 3 ∣ Zeta2PtpFold.Tm n m (t * p + u)
      - (p : ℤ) * e * (-1 : ℤ) ^ (m + (t * p + m % p))
        * Zeta2PtpFold.Tm n (t * p + m % p) (t * p + u) := by
    intro u hu
    have himod : (t * p + u) % p = u := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
    have hidiv : (t * p + u) / p = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hu, zero_add]
    have h1 := Zeta2PtpFold.choose_mul_add_sq (p := p) (M := m / p) (a := m % p) (t := t) (b := u)
      hmlt hu hM hMt
    rw [hdm, show p * t + u = t * p + u by ring, he] at h1
    obtain ⟨c1, hc1⟩ := hH u hu
    unfold Zeta2PtpFold.Tm
    by_cases hi : u ≤ m % p
    · have h2 : (p : ℤ) ∣ (((t * p + m % p).choose (t * p + u) : ℕ) : ℤ)
          - (((m % p).choose u : ℕ) : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [Zeta2PtpS7.lucas_raw (t * p + m % p) (t * p + u), h''mod, h''div, himod, hidiv,
          Nat.choose_self]
        push_cast
        ring
      obtain ⟨d, hd⟩ := h2
      have hs : (-1 : ℤ) ^ (m + (t * p + m % p)) * (-1 : ℤ) ^ (t * p + m % p - (t * p + u))
          = (-1 : ℤ) ^ (m - (t * p + u)) := by
        rw [← pow_add, show m + (t * p + m % p) + (t * p + m % p - (t * p + u))
          = (m - (t * p + u)) + 2 * (t * p + m % p) by omega, pow_add, pow_mul]
        norm_num
      obtain ⟨c2, hc2⟩ := h1
      have key : (p : ℤ) ^ 3 ∣ (-1 : ℤ) ^ (m - (t * p + u)) * Hfun n ↑(t * p + u)
          * (((((m.choose (t * p + u) : ℕ) : ℤ) - (p : ℤ) * e * (((m % p).choose u : ℕ) : ℤ)))
            - (p : ℤ) * e * ((((t * p + m % p).choose (t * p + u) : ℕ) : ℤ)
              - (((m % p).choose u : ℕ) : ℤ))) := by
        rw [hc2, hd, hc1]
        exact ⟨(-1 : ℤ) ^ (m - (t * p + u)) * c1 * (c2 - e * d), by ring⟩
      convert key using 1
      rw [← hs]
      ring
    · rw [Nat.choose_eq_zero_of_lt (show m % p < u by omega), Nat.cast_zero, mul_zero,
        sub_zero] at h1
      rw [Nat.choose_eq_zero_of_lt (show t * p + m % p < t * p + u by omega)]
      simp only [Nat.cast_zero, mul_zero, zero_mul, sub_zero]
      obtain ⟨c2, hc2⟩ := h1
      rw [hc2, hc1]
      exact ⟨(-1 : ℤ) ^ (m - (t * p + u)) * c2 * c1, by ring⟩
  have hsplit : ∑ u ∈ Finset.range p, Zeta2PtpFold.Tm n m (t * p + u)
      = ∑ u ∈ Finset.range p, (Zeta2PtpFold.Tm n m (t * p + u)
          - (p : ℤ) * e * (-1 : ℤ) ^ (m + (t * p + m % p))
            * Zeta2PtpFold.Tm n (t * p + m % p) (t * p + u))
        + (p : ℤ) * e * (-1 : ℤ) ^ (m + (t * p + m % p))
          * ∑ u ∈ Finset.range p, Zeta2PtpFold.Tm n (t * p + m % p) (t * p + u) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hsplit]
  refine dvd_add (Finset.dvd_sum fun u hu => hterm u (Finset.mem_range.mp hu)) ?_
  obtain ⟨f, hf⟩ := hsum2
  rw [hf]
  exact ⟨e * (-1 : ℤ) ^ (m + (t * p + m % p)) * f, by ring⟩

/-- **Anton at three digits, ONE carry**: `C(m, tp + u)/p` for `m ∈ [p², 2p²)`, `t < m₁`,
`u > m₀` — the two-digit `choose_m_div_eq` with `⌊m/p⌋` replaced by its units digit `m₁`. -/
theorem choose_m_div_eq3 (hp2 : 2 < p) {m t u : ℕ} (hu : u < p) (hc : m % p < u)
    (ht : t < m / p % p) (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2) :
    ((m.choose (t * p + u) / p : ℕ) : ZMod p)
      = (-1) ^ (m % p + u) * (-(((m % p)! : ℕ) : ZMod p))
        * ((((m / p % p)! : ℕ) : ZMod p) * (((t)! : ℕ) : ZMod p)⁻¹
          * (((m / p % p - 1 - t)! : ℕ) : ZMod p)⁻¹)
        * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹ := by
  have hp0 := hp.out.pos
  obtain ⟨hmd, hm2d⟩ := digits3 hm hm2
  have hM0 := Nat.mod_lt m hp0
  have hM1 := Nat.mod_lt (m / p) hp0
  generalize hM0d : m % p = M₀ at *
  generalize hM1d : m / p % p = M₁ at *
  have hm3 : m < p ^ 3 := by
    have : p ^ 3 = p * p ^ 2 := by ring
    have : 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  set E := M₁ - 1 - t with hEdef
  have hE : E + t + 1 = M₁ := by omega
  have hEp : E * p + t * p + p = M₁ * p := by
    rw [show E * p + t * p + p = (E + t + 1) * p by ring, hE]
  have hPE : (p + E) * p = p * p + E * p := by ring
  have hEl : E < p := by omega
  have hEl' : E * p + p ≤ p * p := by
    have := Nat.mul_le_mul_right p (show E + 1 ≤ p by omega)
    rwa [Nat.succ_mul] at this
  have hb : t * p + u ≤ m := by omega
  have hbp : t * p + u < p ^ 2 := by
    have := Nat.mul_le_mul_right p (show t + 1 ≤ p by omega)
    rw [Nat.succ_mul] at this
    rw [sq]; omega
  have hx : m - (t * p + u) = (p + M₀ - u) + (p + E) * p := by omega
  have hxmod : (m - (t * p + u)) % p = p + M₀ - u := mod_of_lin hp0 hx (by omega)
  have hxdiv : (m - (t * p + u)) / p = p + E := div_of_lin hp0 hx (by omega)
  have hxd1 : (m - (t * p + u)) / p % p = E := by
    rw [hxdiv]; exact mod_of_lin hp0 (show p + E = E + 1 * p by ring) hEl
  have hxd2 : (m - (t * p + u)) / p ^ 2 % p = 1 := by
    rw [sq, ← Nat.div_div_eq_div_mul, hxdiv, div_of_lin hp0 (show p + E = E + 1 * p by ring) hEl]
    exact Nat.mod_eq_of_lt hp.out.one_lt
  have hbmod : (t * p + u) % p = u := mod_of_lin hp0 (by ring) hu
  have hbdiv : (t * p + u) / p % p = t := by
    rw [div_of_lin hp0 (by ring) hu, Nat.mod_eq_of_lt (by omega)]
  have hbsq : (t * p + u) / p ^ 2 % p = 0 := by
    rw [Nat.div_eq_of_lt hbp]
    simp
  have hmsq : m / p ^ 2 % p = 1 := by rw [hm2d]; exact Nat.mod_eq_of_lt hp.out.one_lt
  have hv : padicValNat p (m.choose (t * p + u)) = 1 := by
    have hmx : m = (m - (t * p + u)) + (t * p + u) := by omega
    have hlog : Nat.log p ((m - (t * p + u)) + (t * p + u)) < 3 :=
      Nat.log_lt_of_lt_pow (by omega) (by rw [← hmx]; exact hm3)
    have key : padicValNat p (((m - (t * p + u)) + (t * p + u)).choose (t * p + u)) = 1 := by
      rw [padicValNat_choose' hlog]
      have hIco : Finset.Ico 1 3 = ({1, 2} : Finset ℕ) := by
        ext i
        simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hx2 : (m - (t * p + u)) % p ^ 2 = m - (t * p + u) - p ^ 2 := by
        rw [sq]
        exact mod_of_lin (Nat.mul_pos hp0 hp0) (q := 1) (by rw [hx, hPE]; omega) (by omega)
      have h1 : p ≤ (t * p + u) % p + (m - (t * p + u)) % p := by rw [hbmod, hxmod]; omega
      have h2 : ¬ p ^ 2 ≤ (t * p + u) % p ^ 2 + (m - (t * p + u)) % p ^ 2 := by
        rw [Nat.mod_eq_of_lt hbp, hx2, sq]
        rw [sq] at hm2
        omega
      have h1' : p ≤ u % p + (m - (t * p + u)) % p := by
        rw [Nat.mod_eq_of_lt hu, hxmod]; omega
      rw [hIco, Finset.filter_insert, Finset.filter_singleton]
      simp [h1, h1', h2]
    rwa [← hmx] at key
  have h := Zeta2Anton.choose_div_p_mul_eq_of_padicValNat_eq_one (p := p) (N := 3) hb hm3 hv
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, Nat.div_one,
    one_mul] at h
  rw [hM0d, hM1d, hmsq, hbmod, hbdiv, hbsq, hxmod, hxd1, hxd2] at h
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_one] at h
  have hu0 : ((u ! : ℕ) : ZMod p) ≠ 0 := Zeta2Anton.cast_factorial_ne_zero_of_lt hu
  have ht0 : ((t ! : ℕ) : ZMod p) ≠ 0 := Zeta2Anton.cast_factorial_ne_zero_of_lt (by omega)
  have hF0 : (((p + M₀ - u)! : ℕ) : ZMod p) ≠ 0 :=
    Zeta2Anton.cast_factorial_ne_zero_of_lt (by omega)
  have hE0 : ((E ! : ℕ) : ZMod p) ≠ 0 := Zeta2Anton.cast_factorial_ne_zero_of_lt hEl
  have h' : ((m.choose (t * p + u) / p : ℕ) : ZMod p)
      * ((((u ! : ℕ) : ZMod p) * ((t ! : ℕ) : ZMod p))
        * ((((p + M₀ - u)! : ℕ) : ZMod p) * ((E ! : ℕ) : ZMod p)))
      = -(((M₀ ! : ℕ) : ZMod p) * ((M₁ ! : ℕ) : ZMod p)) := by
    linear_combination h
  have hx' := (eq_mul_inv_iff_mul_eq₀ (mul_ne_zero (mul_ne_zero hu0 ht0) (mul_ne_zero hF0 hE0))).mpr h'
  rw [hx', rootsLow_eval hc]
  have hW := factorial_inv_eq_denLow (p := p) (e := M₀) (X₀ := u) hc hu (by omega)
  rw [show M₀ + p - u = p + M₀ - u by omega] at hW
  linear_combination (-(((M₁ ! : ℕ) : ZMod p) * ((t ! : ℕ) : ZMod p)⁻¹
    * ((E ! : ℕ) : ZMod p)⁻¹)) * hW

/-- The block constant of a ONE-carry `C(m, i)` at three digits. -/
noncomputable def k43 (p n m t h1 h2 h3 : ℕ) : ZMod p :=
  (-1) ^ (m + t) * (-1) ^ (m % p) * (-(((Nat.factorial (m % p)) : ℕ) : ZMod p))
    * (((Nat.factorial (m / p % p) : ℕ) : ZMod p) * (((Nat.factorial t : ℕ) : ZMod p))⁻¹
        * (((Nat.factorial (m / p % p - 1 - t) : ℕ) : ZMod p))⁻¹)
    * ((h1.choose (13 * n / p) : ℕ) : ZMod p) * ((h2.choose (9 * n / p) : ℕ) : ZMod p)
    * ((h3.choose (5 * n / p) : ℕ) : ZMod p)

/-- **The LO term over `p`** at a single units carry of a three-digit `C(m, i)`, `t < m₁`. -/
theorem Tlo_div_eq_lo4_3 (hp2 : 2 < p) {n m t u h1 h2 h3 : ℕ} (hu : u < p) (hc : m % p < u)
    (ht : t < m / p % p) (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2) (htr : t * p + u ≤ 22 * n)
    (e1 : (26 * n - (t * p + u)) / p = h1) (e2 : (24 * n - (t * p + u)) / p = h2)
    (e3 : (22 * n - (t * p + u)) / p = h3) :
    ((Tlo n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p)
      = k43 p n m t h1 h2 h3 * ((Nlo4 p n).eval (u : ZMod p)
          * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹) := by
  have hp0 := hp.out.pos
  have hdvd : p ∣ m.choose (t * p + u) := dvd_choose_m_of_carry hu hc
  obtain ⟨q, hq⟩ := hdvd
  have hq' : m.choose (t * p + u) / p = q := by rw [hq, Nat.mul_div_cancel_left _ hp0]
  have hA := choose_m_div_eq3 hp2 hu hc ht hm hm2
  rw [hq'] at hA
  have hT : Tlo n m (t * p + u) = (p : ℤ) * ((-1 : ℤ) ^ (m + (t * p + u)) * (q : ℤ)
      * (((26 * n - (t * p + u)).choose (13 * n) : ℕ) : ℤ)
      * (((24 * n - (t * p + u)).choose (9 * n) : ℕ) : ℤ)
      * (((22 * n - (t * p + u)).choose (5 * n) : ℕ) : ℤ)) := by
    rw [Tlo_def, hq]; push_cast; ring
  rw [hT, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp0.ne')]
  push_cast
  rw [sign_block hp2, lucas_factor (26 * n - (t * p + u)) (13 * n),
    lucas_factor (24 * n - (t * p + u)) (9 * n), lucas_factor (22 * n - (t * p + u)) (5 * n),
    e1, e2, e3, cast_sub_block (by omega), cast_sub_block (by omega), cast_sub_block htr, hA]
  unfold k43 Nlo4
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X]
  rw [pow_add (-1 : ZMod p) (m % p) u]
  rcases Nat.even_or_odd u with hpar | hpar
  · rw [hpar.neg_one_pow]; ring
  · rw [hpar.neg_one_pow]; ring

end G

/-! ## The block `t = p − 1` (and every middle TAIL block) on the two `C(m, i)` strata -/

open Zeta2PtpRunS2 in
/-- **`[12/13, 14/15)`: every middle TAIL block above `p²` is `0 mod p³`** — including `t = p − 1`. -/
theorem S2d_hi_mid_cube {p : ℕ} [hp : Fact p.Prime] (hp2 : 2 < p) {n m a s t : ℕ}
    (hn1 : 1 ≤ n) (hn : n = p * a + s) (h1 : 12 * p ≤ 13 * s) (h2 : 15 * s < 14 * p)
    (hmr : m % p = (11 * n) % p) (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2)
    (ht1 : m / p % p < t) (htp : t < p) (ht : 26 * a + 24 ≤ t) :
    (p : ℤ) ^ 3 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) := by
  obtain ⟨hone, htwo⟩ := S2d_hi hn h1 h2 hmr
  refine hi4_block_cube hn1 (S2d_deg hn h1 h2 hmr) hone htwo
    (fun u hu => (choose_mid_dvd hu ht1 htp hm hm2).1)
    (fun u hu hc => (choose_mid_dvd hu ht1 htp hm hm2).2 hc)
    (k4sq p n m t (t - (13 * a + 12)) (t - (15 * a + 14)) (t - (17 * a + 16))) ?_
  intro u hu hk ho1 ho2 ho3
  obtain ⟨htr, e1, e2, e3⟩ := S2d_hi_hsup hn h1 h2 hmr ht htp hu hk ho1 ho2 ho3
  exact Thi_div_sq_eq_hi4 hp2 hu hk ht1.le htp hm hm2 htr e1 e2 e3

open Zeta2PtpRunS2 in
/-- **`[6/13, 7/15)`: every middle TAIL block above `p²` is `0 mod p³`** — including `t = p − 1`. -/
theorem S2c_hi_mid_cube {p : ℕ} [hp : Fact p.Prime] (hp2 : 2 < p) {n m a s t : ℕ}
    (hn1 : 1 ≤ n) (hn : n = p * a + s) (h1 : 6 * p ≤ 13 * s) (h2 : 15 * s < 7 * p)
    (hmr : m % p = (11 * n) % p) (hm : p ^ 2 ≤ m) (hm2 : m < p ^ 2 + p ^ 2)
    (ht1 : m / p % p < t) (htp : t < p) (ht : 26 * a + 12 ≤ t) :
    (p : ℤ) ^ 3 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) := by
  obtain ⟨hone, htwo⟩ := S2c_hi hn h1 h2 hmr
  refine hi4_block_cube hn1 (S2c_deg hn h1 h2 hmr) hone htwo
    (fun u hu => (choose_mid_dvd hu ht1 htp hm hm2).1)
    (fun u hu hc => (choose_mid_dvd hu ht1 htp hm hm2).2 hc)
    (k4sq p n m t (t - (13 * a + 6)) (t - (15 * a + 7)) (t - (17 * a + 8))) ?_
  intro u hu hk ho1 ho2 ho3
  obtain ⟨htr, e1, e2, e3⟩ := S2c_hi_hsup hn h1 h2 hmr ht htp hu hk ho1 ho2 ho3
  exact Thi_div_sq_eq_hi4 hp2 hu hk ht1.le htp hm hm2 htr e1 e2 e3

end Zeta2PtpMbigG2

#print axioms Zeta2PtpMbigG2.digits3
#print axioms Zeta2PtpMbigG2.choose_m_div_sq_eq
#check @Zeta2PtpMbigG2.choose_m_div_sq_eq
#print axioms Zeta2PtpMbigG2.Thi_div_sq_eq_hi4
#print axioms Zeta2PtpMbigG2.hi4_block_cube
#check @Zeta2PtpMbigG2.hi4_block_cube
#print axioms Zeta2PtpMbigG2.choose_mid_dvd
#print axioms Zeta2PtpMbigG2.S2d_hi_mid_cube
#check @Zeta2PtpMbigG2.S2d_hi_mid_cube
#print axioms Zeta2PtpMbigG2.S2c_hi_mid_cube
#check @Zeta2PtpMbigG2.S2c_hi_mid_cube
#print axioms Zeta2PtpMbigG2.choose_sq_dvd_two
#print axioms Zeta2PtpMbigG2.Tlo_div_sq_eq_lo4
#print axioms Zeta2PtpMbigG2.lo4_cube_c4
#check @Zeta2PtpMbigG2.lo4_cube_c4
#print axioms Zeta2PtpMbigG2.floor_sub
#print axioms Zeta2PtpMbigG2.lam_pair_eq
#check @Zeta2PtpMbigG2.lam_pair_eq
#print axioms Zeta2PtpMbigG2.pair_block_cube
#check @Zeta2PtpMbigG2.pair_block_cube
#print axioms Zeta2PtpMbigG2.mid_block_cube
#check @Zeta2PtpMbigG2.mid_block_cube
#print axioms Zeta2PtpMbigG2.choose_m_div_eq3
#check @Zeta2PtpMbigG2.choose_m_div_eq3
#print axioms Zeta2PtpMbigG2.Tlo_div_eq_lo4_3
