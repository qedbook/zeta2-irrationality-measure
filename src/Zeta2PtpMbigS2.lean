/-
# Row PT-P, part (b), layer 4 — the four φ̃ = 2 run strata CLOSED above `p²`, `restAboveOpen`, and
# the POLYNOMIAL HALF OF PT-P WITH NO BINDER

At a polar run-strata row with `m = p² + μ ≥ p²` on a φ̃ = 2 stratum, `h_m` must be `0 mod p³`.
Folded (`Zeta2PtpFold.hc_eq_fold`), block by block `t < p`:

* **`C(m, i)`-carried strata** `[6/13, 7/15)`, `[12/13, 14/15)` (`f2_high`):
  - pair blocks `t < ⌊μ/p⌋`: the fold law with `λ` constant on the one-carry set (`c4` alone —
    `Zeta2PtpMbigG2.lam_pair_eq` on the sibling's `*_lo_hsup` digits) and the raw block `0 mod p²`
    by the sibling's `lo4_block_dvd_of` with a THREE-digit one-carry Anton identity
    (`Zeta2PtpMbigG2.Tlo_div_eq_lo4_3`) — `Zeta2PtpMbigG2.pair_block_cube`;
  - the top pair block `t = ⌊μ/p⌋`: the pairs are `0 mod p³` termwise (two `H` carries, the fold
    gains a third) and the unpaired residues `u > μ₀` are the `C(m, i)`-restricted cube block
    (`Zeta2PtpMbigG2.lo4_cube_c4`) — the φ̃ = 2 partial-block mechanism of
    `ptp_mbig_phi2_probe.out`;
  - middle blocks: `lo4_cube_c4` plus termwise, and `Zeta2PtpMbigG2.S2?_hi_mid_cube`.
* **third-`H`-block-carried strata** `[1/9, 3/26)`, `[3/26, 2/17)`, `[5/9, 9/16)` (`f1_high`):
  - pair blocks: the fold law with `λ` constant on the one-carry set (`cLo3` alone), the raw
    block `0 mod p²` by the sibling's `lo3_block_dvd` at `m` itself, and the unpaired residues
    termwise (a `C(m, i)` double carry and an `H` carry) — `pair_block_cube`;
  - middle blocks: `Zeta2PtpMbigG2.mid_block_cube` against the reduced row `tp + (m mod p)`,
    whose block the sibling's `lo3`/`hi3` lemmas kill mod `p²`.

**`restAboveS2Open : Zeta2PtpMbigS7.RestAboveS2Open`**, so **`restAboveOpen`** and
**`polyHalfOpen : Zeta2PtpPolar.PolyHalfOpen`** — hypothesis-free.

WHAT IS NOT CLAIMED.  The harmonic half and the rest of PT-P are not touched here; the
headline `Zeta2Target.zeta2_not_liouvilleWith` is still `sorry` and carries PT-P's other rows and
the standing binder `hψ` as the chain doc states.

Probe: `ptp_mbig_probe.py`, `ptp_mbig_phi2_probe.py`.  Runner: `run_resid.sh`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2PtpMbigG2
import Zeta2PtpMbigS7

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zeta2PtpMbigS2

open Zeta2PtpMbigG2 Zeta2PtpRunG2 Zeta2PtpRunBlock Finset
open Zeta2PtpFold (Tm lam hsum hc_eq_fold)
open Zeta2NewtonAssemble (Hfun)

section A
variable {p : ℕ} [hp : Fact p.Prime]

theorem Tm_eq_lo_hi (n m i : ℕ) (hn : 1 ≤ n) :
    Tm n m i = (-1 : ℤ) ^ (27 * n) * Tlo n m i + Thi n m i := by
  by_cases hi : i ≤ m
  · exact term_eq_lo_add_hi n m i hn hi
  · unfold Tm
    rw [Tlo_eq_zero_of_gt (by omega), Thi_eq_zero_of_gt (by omega),
      Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem Tm_eq_lo {n m i : ℕ} (hn : 1 ≤ n) (hi : i ≤ 26 * n) :
    Tm n m i = (-1 : ℤ) ^ (27 * n) * Tlo n m i := by
  rw [Tm_eq_lo_hi n m i hn, Thi_eq_zero_of_le26 hn hi, add_zero]

theorem Tlo_dvd_of {n m t u k : ℕ} (h : p ^ k ∣ m.choose (t * p + u)
      * ((26 * n - (t * p + u)).choose (13 * n) * (24 * n - (t * p + u)).choose (9 * n)
        * (22 * n - (t * p + u)).choose (5 * n))) :
    (p : ℤ) ^ k ∣ Tlo n m (t * p + u) := by
  rw [Tlo_nat]
  exact Dvd.dvd.mul_left (by exact_mod_cast Int.natCast_dvd_natCast.2 h) _

theorem Thi_dvd_of {n m t u k : ℕ} (h : p ^ k ∣ m.choose (t * p + u)
      * ((t * p + u - (13 * n + 1)).choose (13 * n) * (t * p + u - (15 * n + 1)).choose (9 * n)
        * (t * p + u - (17 * n + 1)).choose (5 * n))) :
    (p : ℤ) ^ k ∣ Thi n m (t * p + u) := by
  rw [Thi_nat]
  exact Dvd.dvd.mul_left (by exact_mod_cast Int.natCast_dvd_natCast.2 h) _

/-- `(m − p²) mod p = m mod p`. -/
theorem sub_sq_mod {m : ℕ} (hm : p ^ 2 ≤ m) : (m - p ^ 2) % p = m % p := by
  have hm' : m = (m - p ^ 2) + p * p := by rw [← sq]; omega
  conv_rhs => rw [hm']
  rw [Nat.add_mul_mod_self_left]

/-- The LO carry facts, as divisibility of the four factors. -/
theorem lo_facts {n m t u : ℕ} (hu : u < p) :
    (cLo1 p n u → p ∣ (26 * n - (t * p + u)).choose (13 * n))
    ∧ (cLo2 p n u → p ∣ (24 * n - (t * p + u)).choose (9 * n))
    ∧ (cLo3 p n u → p ∣ (22 * n - (t * p + u)).choose (5 * n))
    ∧ (c4 p m u → p ∣ m.choose (t * p + u)) := by
  have hp0 := hp.out.pos
  have hp1 : ∀ k, 0 < k * n ∨ k * n = 0 := fun k => Nat.eq_zero_or_pos _ |>.symm
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => dvd_choose_m_of_carry hu h⟩
  · rcases Nat.eq_zero_or_pos (13 * n) with h0 | h0
    · unfold cLo1 at h; rw [h0] at h; simp at h
    · exact dvd_choose_of_carry hu h0 h
  · rcases Nat.eq_zero_or_pos (9 * n) with h0 | h0
    · unfold cLo2 at h; rw [h0] at h; simp at h
    · exact dvd_choose_of_carry hu h0 h
  · rcases Nat.eq_zero_or_pos (5 * n) with h0 | h0
    · unfold cLo3 at h; rw [h0] at h; simp at h
    · exact dvd_choose_of_carry hu h0 h

/-- The TAIL carry facts. -/
theorem hi_facts {n m t u : ℕ} (hu : u < p) (hn : 1 ≤ n) :
    (cHi1 p n u → p ∣ (t * p + u - (13 * n + 1)).choose (13 * n))
    ∧ (cHi2 p n u → p ∣ (t * p + u - (15 * n + 1)).choose (9 * n))
    ∧ (cHi3 p n u → p ∣ (t * p + u - (17 * n + 1)).choose (5 * n))
    ∧ (c4 p m u → p ∣ m.choose (t * p + u)) :=
  ⟨fun h => dvd_choose_of_carry_up hu (by omega) h, fun h => dvd_choose_of_carry_up hu (by omega) h,
    fun h => dvd_choose_of_carry_up hu (by omega) h, fun h => dvd_choose_m_of_carry hu h⟩

end A

/-! ## The `C(m, i)`-carried strata: the generic high-`m` closure -/

/-- **`p³ ∣ h_m` on a `C(m, i)`-carried φ̃ = 2 stratum above `p²`**, from the stratum's residue
facts (the sibling's `*_lo`, `*_hi`, `*_deg`, `*_lo_hsup`) and its middle TAIL cube. -/
theorem f2_high {p : ℕ} [hp : Fact p.Prime] (hp2 : 2 < p) {n r a s A1 A2 A3 LO HI : ℕ}
    (hsq : 26 * n + 1 < p ^ 2) (hn1 : 1 ≤ n) (hr : r < 16 * n) (hmsq : p ^ 2 ≤ 11 * n + 1 + r)
    (hmp : (11 * n + 1 + r) % p = (11 * n) % p) (hn : n = p * a + s) (hs : s < p)
    (hdeg : (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2 + ((11 * n + 1 + r) % p + 1))
    (hone : ∀ u < p, cLo1 p n u ∨ cLo2 p n u ∨ cLo3 p n u ∨ c4 p (11 * n + 1 + r) u)
    (htwo : ∀ u < p, ¬ c4 p (11 * n + 1 + r) u →
      (cLo1 p n u ∧ cLo2 p n u) ∨ (cLo1 p n u ∧ cLo3 p n u) ∨ (cLo2 p n u ∧ cLo3 p n u))
    (hsup : ∀ t u, t ≤ LO → u < p → c4 p (11 * n + 1 + r) u → ¬ cLo1 p n u → ¬ cLo2 p n u →
      ¬ cLo3 p n u → t * p + u ≤ 22 * n ∧ (26 * n - (t * p + u)) / p = A1 - t
        ∧ (24 * n - (t * p + u)) / p = A2 - t ∧ (22 * n - (t * p + u)) / p = A3 - t)
    (haLO : a ≤ LO) (hLO : 13 * n < (LO + 1) * p)
    (hHI : HI * p ≤ 26 * n + 1)
    (hmid_hi : ∀ t, (11 * n + 1 + r) / p % p < t → t < p → HI ≤ t →
      (p : ℤ) ^ 3 ∣ ∑ u ∈ range p, Thi n (11 * n + 1 + r) (t * p + u)) :
    (p : ℤ) ^ 3 ∣ Zeta2NewtonAssemble.hc n (11 * n + 1 + r) := by
  have hp0 := hp.out.pos
  have hpp2 : p ^ 2 = p * p := sq p
  have hp12 : p ≤ 12 * n := by
    by_contra h
    push_neg at h
    have := Nat.mul_le_mul h.le h.le
    nlinarith
  set m := 11 * n + 1 + r with hmdef
  have hm2 : m < p ^ 2 + p ^ 2 := by omega
  set μ := m - p ^ 2 with hμdef
  have hμn : μ < n := by omega
  have hμm : m = μ + p * p := by omega
  have hmodμ : m % p = μ % p := by rw [hμm, Nat.add_mul_mod_self_left]
  have hμ1 : μ / p < p := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
  have hMdiv : m / p = p + μ / p := by rw [hμm, Nat.add_mul_div_right _ _ hp0, Nat.add_comm]
  have hM1 : m / p % p = μ / p := by rw [hMdiv, Nat.add_mod_left, Nat.mod_eq_of_lt hμ1]
  have hμdm := Nat.div_add_mod μ p
  have hμa : μ / p ≤ a := by
    have : μ / p < a + 1 := (Nat.div_lt_iff_lt_mul hp0).mpr (by
      have e : (a + 1) * p = p * a + p := by ring
      omega)
    omega
  have hμp : μ / p * p = p * (μ / p) := Nat.mul_comm _ _
  have hmlt := Nat.mod_lt m hp0
  rw [hc_eq_fold hm2]
  refine dvd_sum fun t ht => ?_
  have ht' := mem_range.mp ht
  have htp1 : (t + 1) * p ≤ p * p := Nat.mul_le_mul_right p ht'
  have etp1 : (t + 1) * p = t * p + p := by ring
  by_cases hpair : t ≤ μ / p
  · have hta : t ≤ a := le_trans hpair hμa
    have htpa : t * p ≤ a * p := Nat.mul_le_mul_right p hta
    have hap : a * p = p * a := Nat.mul_comm _ _
    have hi26 : ∀ u < p, t * p + u ≤ 13 * n := fun u hu => by
      have : t * p + u < t * p + p := by omega
      omega
    -- the per-residue facts at `m`
    have hTlo2 : ∀ u < p, ¬ c4 p m u → (p : ℤ) ^ 2 ∣ Tm n m (t * p + u) := by
      intro u hu h4
      obtain ⟨f1, f2, f3, -⟩ := lo_facts (n := n) (m := m) (t := t) hu
      rw [Tm_eq_lo hn1 (by have := hi26 u hu; omega)]
      refine Dvd.dvd.mul_left (Tlo_dvd_of ?_) _
      rw [sq]
      refine Dvd.dvd.mul_left ?_ _
      rcases htwo u hu h4 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Dvd.dvd.mul_right (mul_dvd_mul (f1 ha) (f2 hb)) _
      · rw [mul_right_comm]
        exact Dvd.dvd.mul_right (mul_dvd_mul (f1 ha) (f3 hb)) _
      · rw [mul_assoc]
        exact Dvd.dvd.mul_left (mul_dvd_mul (f2 ha) (f3 hb)) _
    by_cases htop : t = μ / p
    · -- the TOP pair block: pairs termwise, the `C(m, i)` residues by the restricted cube
      have hsplit : ∀ u < p, Tm n m (t * p + u) + Tm n m (p ^ 2 + (t * p + u))
          = (if m % p < u then Tm n m (t * p + u) else 0)
            + (if m % p < u then 0 else Tm n m (t * p + u) + Tm n m (p ^ 2 + (t * p + u))) := by
        intro u hu
        by_cases h4 : m % p < u
        · have h0 : Tm n m (p ^ 2 + (t * p + u)) = 0 := by
            unfold Tm
            rw [Nat.choose_eq_zero_of_lt (by rw [hmodμ] at h4; subst htop; omega)]
            simp
          simp [h4, h0]
        · simp [h4]
      rw [sum_congr rfl fun u hu => hsplit u (mem_range.mp hu), sum_add_distrib]
      refine dvd_add ?_ (dvd_sum fun u hu => ?_)
      · have e : ∑ u ∈ range p, (if m % p < u then Tm n m (t * p + u) else 0)
            = (-1 : ℤ) ^ (27 * n) * ∑ u ∈ range p, (if m % p < u then Tlo n m (t * p + u) else 0) := by
          rw [mul_sum]
          refine sum_congr rfl fun u hu => ?_
          by_cases h4 : m % p < u
          · simp only [h4, ite_true]
            exact Tm_eq_lo hn1 (by have := hi26 u (mem_range.mp hu); omega)
          · simp [h4]
        rw [e]
        refine Dvd.dvd.mul_left (lo4_cube_c4 hn1 hdeg htwo
          (fun u hu h4 => choose_sq_dvd_two hu h4 (by rw [hM1, htop]) ht' hmsq hm2)
          (k4sq p n m t (A1 - t) (A2 - t) (A3 - t)) fun u hu h4 ho1 ho2 ho3 => ?_) _
        obtain ⟨htr, e1, e2, e3⟩ := hsup t u (le_trans hta haLO) hu h4 ho1 ho2 ho3
        exact Tlo_div_sq_eq_lo4 hp2 hu h4 (by rw [hM1, htop]) ht' hmsq hm2 htr e1 e2 e3
      · have hu := mem_range.mp hu
        by_cases h4 : m % p < u
        · simp [h4]
        · simp only [h4, ite_false]
          have hT2 := hTlo2 u hu h4
          have hjμ : t * p + u ≤ μ := by
            have : u ≤ μ % p := by rw [← hmodμ]; omega
            subst htop; omega
          have hj : t * p + u < n := by omega
          have hf := Zeta2PtpFold.fold_law (p := p) (n := n) (m := m) (j := t * p + u) (K := 2)
            hsq hj (by rw [hpp2]; omega) hm2 hT2
          have hl : (p : ℤ) ^ 3 ∣ (p : ℤ) * ((lam p n m (t * p + u)).val : ℤ) * Tm n m (t * p + u) := by
            obtain ⟨c, hc⟩ := hT2
            rw [hc]
            exact ⟨((lam p n m (t * p + u)).val : ℤ) * c, by ring⟩
          have := dvd_sub ((pow_dvd_pow _ (by omega)).trans hf) hl
          rwa [add_sub_cancel_right] at this
    · -- a pair block below the top
      have htlt : t < μ / p := lt_of_le_of_ne hpair htop
      have htμ : t * p + p ≤ μ / p * p := by
        have := Nat.mul_le_mul_right p htlt
        rwa [Nat.succ_mul] at this
      refine pair_block_cube (n := n) (m := m) (t := t)
        (ℓ₀ := hsum p 0 ((m - p ^ 2) / p - t - 1) - hsum p 0 t
          + (-hsum p (A1 - t - 13 * n / p - 0) (A1 - t) - hsum p (A2 - t - 9 * n / p - 0) (A2 - t)
            - hsum p (A3 - t - 5 * n / p - 0) (A3 - t)))
        hsq hmsq hm2 (by omega) ?_ ?_ ?_ ?_
      · -- every pair term `0 mod p`
        intro u hu _
        obtain ⟨f1, f2, f3, f4⟩ := lo_facts (n := n) (m := m) (t := t) hu
        rw [Tm_eq_lo hn1 (by have := hi26 u hu; omega)]
        refine Dvd.dvd.mul_left ((pow_one (p : ℤ)) ▸ Tlo_dvd_of ?_) _
        rw [pow_one]
        exact dvd_prod4 (by
          rcases hone u hu with h | h | h | h
          exacts [Or.inr (Or.inl (f1 h)), Or.inr (Or.inr (Or.inl (f2 h))),
            Or.inr (Or.inr (Or.inr (f3 h))), Or.inl (f4 h)])
      · -- `λ` on the one-carry set
        intro u hu hj hT
        obtain ⟨f1, f2, f3, f4⟩ := lo_facts (n := n) (m := m) (t := t) hu
        have h4 : c4 p m u := by
          by_contra h4
          exact hT (hTlo2 u hu h4)
        have hno : ∀ (P : Prop), (P → p ∣ (26 * n - (t * p + u)).choose (13 * n)
            * (24 * n - (t * p + u)).choose (9 * n) * (22 * n - (t * p + u)).choose (5 * n)) →
            ¬ P := by
          intro P hP hP'
          refine hT ?_
          rw [Tm_eq_lo hn1 (by have := hi26 u hu; omega)]
          refine Dvd.dvd.mul_left (Tlo_dvd_of ?_) _
          rw [sq]
          exact mul_dvd_mul (f4 h4) (hP hP')
        have ho1 : ¬ cLo1 p n u := hno _ fun h => Dvd.dvd.mul_right (Dvd.dvd.mul_right (f1 h) _) _
        have ho2 : ¬ cLo2 p n u := hno _ fun h => Dvd.dvd.mul_right (Dvd.dvd.mul_left (f2 h) _) _
        have ho3 : ¬ cLo3 p n u := hno _ fun h => Dvd.dvd.mul_left (f3 h) _
        obtain ⟨_, e1, e2, e3⟩ := hsup t u (le_trans hta haLO) hu h4 ho1 ho2 ho3
        rw [lam_pair_eq hu hj (hi26 u hu), e1, e2, e3, sub_sq_mod hmsq]
        have c4' : m % p < u := h4
        have c1' : ¬ (((26 * n) % p + p - u) % p < (13 * n) % p) := ho1
        have c2' : ¬ (((24 * n) % p + p - u) % p < (9 * n) % p) := ho2
        have c3' : ¬ (((22 * n) % p + p - u) % p < (5 * n) % p) := ho3
        simp only [c4', c1', c2', c3', ite_true, ite_false]
      · intro u hu hlt
        exfalso
        omega
      · -- the raw block `0 mod p²`: the sibling's quotient lemma with three-digit Anton
        have e : ∑ u ∈ range p, Tm n m (t * p + u)
            = (-1 : ℤ) ^ (27 * n) * ∑ u ∈ range p, Tlo n m (t * p + u) := by
          rw [mul_sum]
          exact sum_congr rfl fun u hu => Tm_eq_lo hn1 (by have := hi26 u (mem_range.mp hu); omega)
        rw [e]
        refine Dvd.dvd.mul_left (lo4_block_dvd_of hn1 hdeg hone htwo
          (k43 p n m t (A1 - t) (A2 - t) (A3 - t)) fun u hu h4 ho1 ho2 ho3 => ?_) _
        obtain ⟨htr, e1, e2, e3⟩ := hsup t u (le_trans hta haLO) hu h4 ho1 ho2 ho3
        exact Tlo_div_eq_lo4_3 hp2 hu h4 (by rw [hM1]; exact htlt) hmsq hm2 htr e1 e2 e3
  · -- a MIDDLE block: nothing pairs
    have hlt : μ < t * p := (Nat.div_lt_iff_lt_mul hp0).mp (by omega)
    have hT0 : ∀ u < p, Tm n m (p ^ 2 + (t * p + u)) = 0 := by
      intro u _
      unfold Tm
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [sum_congr rfl fun u hu => by rw [hT0 u (mem_range.mp hu), add_zero],
      sum_congr rfl fun u _ => Tm_eq_lo_hi n m (t * p + u) hn1, sum_add_distrib, ← mul_sum]
    have ht1 : m / p % p < t := by rw [hM1]; omega
    refine dvd_add (Dvd.dvd.mul_left ?_ _) ?_
    · by_cases hLOt : t ≤ LO
      · have hsplit : ∑ u ∈ range p, Tlo n m (t * p + u)
            = ∑ u ∈ range p, (if m % p < u then Tlo n m (t * p + u) else 0)
              + ∑ u ∈ range p, (if m % p < u then 0 else Tlo n m (t * p + u)) := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun u _ => by split_ifs <;> simp
        rw [hsplit]
        refine dvd_add (lo4_cube_c4 hn1 hdeg htwo
          (fun u hu h4 => choose_sq_dvd_two hu h4 ht1.le ht' hmsq hm2)
          (k4sq p n m t (A1 - t) (A2 - t) (A3 - t)) fun u hu h4 ho1 ho2 ho3 => ?_)
          (dvd_sum fun u hu => ?_)
        · obtain ⟨htr, e1, e2, e3⟩ := hsup t u hLOt hu h4 ho1 ho2 ho3
          exact Tlo_div_sq_eq_lo4 hp2 hu h4 ht1.le ht' hmsq hm2 htr e1 e2 e3
        · have hu := mem_range.mp hu
          by_cases h4 : m % p < u
          · simp [h4]
          · simp only [h4, ite_false]
            obtain ⟨f1, f2, f3, -⟩ := lo_facts (n := n) (m := m) (t := t) hu
            refine Tlo_dvd_of ?_
            rw [show 3 = 1 + 2 by rfl, pow_add, pow_one]
            refine mul_dvd_mul (choose_mid_dvd hu ht1 ht' hmsq hm2).1 ?_
            rw [sq]
            rcases htwo u hu h4 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
            · exact Dvd.dvd.mul_right (mul_dvd_mul (f1 ha) (f2 hb)) _
            · rw [mul_right_comm]
              exact Dvd.dvd.mul_right (mul_dvd_mul (f1 ha) (f3 hb)) _
            · rw [mul_assoc]
              exact Dvd.dvd.mul_left (mul_dvd_mul (f2 ha) (f3 hb)) _
      · have hT : (LO + 1) * p ≤ t * p := Nat.mul_le_mul_right p (by omega)
        rw [sum_eq_zero fun u _ => Tlo_eq_zero_of_gt13 hn1 (by omega)]
        exact dvd_zero _
    · by_cases hHIt : HI ≤ t
      · exact hmid_hi t ht1 ht' hHIt
      · have hT : t * p + p ≤ HI * p := by
          have := Nat.mul_le_mul_right p (show t + 1 ≤ HI by omega)
          rwa [Nat.succ_mul] at this
        rw [sum_eq_zero fun u hu => Thi_eq_zero_of_le26 hn1 (by have := mem_range.mp hu; omega)]
        exact dvd_zero _

/-! ## The third-`H`-block-carried strata: the generic high-`m` closure -/

/-- **`p³ ∣ h_m` on a third-block-carried φ̃ = 2 stratum above `p²`**, from the stratum's residue
facts and the sibling's `p²` block lemmas at every row with the same `m mod p` (`hblk2`). -/
theorem f1_high {p : ℕ} [hp : Fact p.Prime] {n r a s A1 A2 A3 : ℕ}
    (hsq : 26 * n + 1 < p ^ 2) (hn1 : 1 ≤ n) (hr : r < 16 * n) (hmsq : p ^ 2 ≤ 11 * n + 1 + r)
    (hmp : (11 * n + 1 + r) % p = (11 * n) % p) (hn : n = p * a + s) (hs : s < p)
    (hone : ∀ u < p, cLo1 p n u ∨ cLo2 p n u ∨ cLo3 p n u ∨ c4 p (11 * n + 1 + r) u)
    (htwo : ∀ u < p, ¬ cLo3 p n u → (cLo1 p n u ∧ cLo2 p n u)
      ∨ (cLo1 p n u ∧ c4 p (11 * n + 1 + r) u) ∨ (cLo2 p n u ∧ c4 p (11 * n + 1 + r) u))
    (htwo_hi : ∀ u < p, ¬ cHi3 p n u → (cHi1 p n u ∧ cHi2 p n u)
      ∨ (cHi1 p n u ∧ c4 p (11 * n + 1 + r) u) ∨ (cHi2 p n u ∧ c4 p (11 * n + 1 + r) u))
    (hsup : ∀ t u, t ≤ a → u < p → cLo3 p n u → ¬ cLo1 p n u → ¬ cLo2 p n u →
      ¬ c4 p (11 * n + 1 + r) u → t * p + u ≤ 22 * n ∧ (26 * n - (t * p + u)) / p = A1 - t
        ∧ (24 * n - (t * p + u)) / p = A2 - t ∧ (22 * n - (t * p + u)) / p = A3 - t)
    (hblk2 : ∀ m', m' % p = (11 * n) % p → ∀ t < p,
      (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, Tlo n m' (t * p + u)
        ∧ (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, Thi n m' (t * p + u)) :
    (p : ℤ) ^ 3 ∣ Zeta2NewtonAssemble.hc n (11 * n + 1 + r) := by
  have hp0 := hp.out.pos
  have hpp2 : p ^ 2 = p * p := sq p
  have hp12 : p ≤ 12 * n := by
    by_contra h
    push_neg at h
    have := Nat.mul_le_mul h.le h.le
    nlinarith
  set m := 11 * n + 1 + r with hmdef
  have hm2 : m < p ^ 2 + p ^ 2 := by omega
  set μ := m - p ^ 2 with hμdef
  have hμn : μ < n := by omega
  have hμm : m = μ + p * p := by omega
  have hmodμ : m % p = μ % p := by rw [hμm, Nat.add_mul_mod_self_left]
  have hμ1 : μ / p < p := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
  have hMdiv : m / p = p + μ / p := by rw [hμm, Nat.add_mul_div_right _ _ hp0, Nat.add_comm]
  have hM1 : m / p % p = μ / p := by rw [hMdiv, Nat.add_mod_left, Nat.mod_eq_of_lt hμ1]
  have hμdm := Nat.div_add_mod μ p
  have hμa : μ / p ≤ a := by
    have : μ / p < a + 1 := (Nat.div_lt_iff_lt_mul hp0).mpr (by
      have e : (a + 1) * p = p * a + p := by ring
      omega)
    omega
  have hμp : μ / p * p = p * (μ / p) := Nat.mul_comm _ _
  have hmlt := Nat.mod_lt m hp0
  have hHlo : ∀ u < p, cLo1 p n u ∨ cLo2 p n u ∨ cLo3 p n u := by
    intro u hu
    by_cases h3 : cLo3 p n u
    · exact Or.inr (Or.inr h3)
    · rcases htwo u hu h3 with ⟨ha, -⟩ | ⟨ha, -⟩ | ⟨ha, -⟩
      exacts [Or.inl ha, Or.inl ha, Or.inr (Or.inl ha)]
  have hHhi : ∀ u < p, cHi1 p n u ∨ cHi2 p n u ∨ cHi3 p n u := by
    intro u hu
    by_cases h3 : cHi3 p n u
    · exact Or.inr (Or.inr h3)
    · rcases htwo_hi u hu h3 with ⟨ha, -⟩ | ⟨ha, -⟩ | ⟨ha, -⟩
      exacts [Or.inl ha, Or.inl ha, Or.inr (Or.inl ha)]
  -- the `H` part of a LO term is `0 mod p`
  have hHdvd : ∀ t u, u < p → p ∣ (26 * n - (t * p + u)).choose (13 * n)
      * (24 * n - (t * p + u)).choose (9 * n) * (22 * n - (t * p + u)).choose (5 * n) := by
    intro t u hu
    obtain ⟨f1, f2, f3, -⟩ := lo_facts (n := n) (m := m) (t := t) hu
    rcases hHlo u hu with h | h | h
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (f1 h) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (f2 h) _) _
    · exact Dvd.dvd.mul_left (f3 h) _
  rw [hc_eq_fold hm2]
  refine dvd_sum fun t ht => ?_
  have ht' := mem_range.mp ht
  have htp1 : (t + 1) * p ≤ p * p := Nat.mul_le_mul_right p ht'
  have etp1 : (t + 1) * p = t * p + p := by ring
  by_cases hpair : t ≤ μ / p
  · have hta : t ≤ a := le_trans hpair hμa
    have htpa : t * p ≤ a * p := Nat.mul_le_mul_right p hta
    have hap : a * p = p * a := Nat.mul_comm _ _
    have htμ : t * p ≤ μ / p * p := Nat.mul_le_mul_right p hpair
    have hi26 : ∀ u < p, t * p + u ≤ 13 * n := fun u hu => by
      have : t * p + u < t * p + p := by omega
      omega
    refine pair_block_cube (n := n) (m := m) (t := t)
      (ℓ₀ := hsum p 0 ((m - p ^ 2) / p - t - 0) - hsum p 0 t
        + (-hsum p (A1 - t - 13 * n / p - 0) (A1 - t) - hsum p (A2 - t - 9 * n / p - 0) (A2 - t)
          - hsum p (A3 - t - 5 * n / p - 1) (A3 - t)))
      hsq hmsq hm2 (by omega) ?_ ?_ ?_ ?_
    · intro u hu _
      obtain ⟨f1, f2, f3, f4⟩ := lo_facts (n := n) (m := m) (t := t) hu
      rw [Tm_eq_lo hn1 (by have := hi26 u hu; omega)]
      refine Dvd.dvd.mul_left ((pow_one (p : ℤ)) ▸ Tlo_dvd_of ?_) _
      rw [pow_one]
      exact dvd_prod4 (by
        rcases hone u hu with h | h | h | h
        exacts [Or.inr (Or.inl (f1 h)), Or.inr (Or.inr (Or.inl (f2 h))),
          Or.inr (Or.inr (Or.inr (f3 h))), Or.inl (f4 h)])
    · intro u hu hj hT
      obtain ⟨f1, f2, f3, f4⟩ := lo_facts (n := n) (m := m) (t := t) hu
      have hsq2 : p ^ 2 ∣ m.choose (t * p + u) * ((26 * n - (t * p + u)).choose (13 * n)
          * (24 * n - (t * p + u)).choose (9 * n) * (22 * n - (t * p + u)).choose (5 * n))
          → False := by
        intro h
        refine hT ?_
        rw [Tm_eq_lo hn1 (by have := hi26 u hu; omega)]
        exact Dvd.dvd.mul_left (Tlo_dvd_of h) _
      have hn4 : ¬ c4 p m u := fun h4 => hsq2 (by rw [sq]; exact mul_dvd_mul (f4 h4) (hHdvd t u hu))
      have h3 : cLo3 p n u := by
        by_contra h3
        refine hsq2 (by
          rw [sq]
          rcases htwo u hu h3 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (mul_dvd_mul (f1 ha) (f2 hb)) _) _
          · exact mul_dvd_mul (f4 hb) (Dvd.dvd.mul_right (Dvd.dvd.mul_right (f1 ha) _) _)
          · exact mul_dvd_mul (f4 hb) (Dvd.dvd.mul_right (Dvd.dvd.mul_left (f2 ha) _) _))
      have ho1 : ¬ cLo1 p n u := fun h => hsq2 (by
        have hH : p * p ∣ (26 * n - (t * p + u)).choose (13 * n)
            * (24 * n - (t * p + u)).choose (9 * n) * (22 * n - (t * p + u)).choose (5 * n) := by
          rw [mul_right_comm]
          exact Dvd.dvd.mul_right (mul_dvd_mul (f1 h) (f3 h3)) _
        rw [sq]
        exact Dvd.dvd.mul_left hH _)
      have ho2 : ¬ cLo2 p n u := fun h => hsq2 (by
        have hH : p * p ∣ (26 * n - (t * p + u)).choose (13 * n)
            * (24 * n - (t * p + u)).choose (9 * n) * (22 * n - (t * p + u)).choose (5 * n) := by
          rw [mul_assoc]
          exact Dvd.dvd.mul_left (mul_dvd_mul (f2 h) (f3 h3)) _
        rw [sq]
        exact Dvd.dvd.mul_left hH _)
      obtain ⟨_, e1, e2, e3⟩ := hsup t u hta hu h3 ho1 ho2 hn4
      rw [lam_pair_eq hu hj (hi26 u hu), e1, e2, e3, sub_sq_mod hmsq]
      have c4' : ¬ m % p < u := hn4
      have c1' : ¬ (((26 * n) % p + p - u) % p < (13 * n) % p) := ho1
      have c2' : ¬ (((24 * n) % p + p - u) % p < (9 * n) % p) := ho2
      have c3' : ((22 * n) % p + p - u) % p < (5 * n) % p := h3
      simp only [c4', c1', c2', c3', ite_true, ite_false]
    · intro u hu hlt
      have htop : t = μ / p := by
        by_contra hne
        have : t < μ / p := lt_of_le_of_ne hpair hne
        have := Nat.mul_le_mul_right p this
        rw [Nat.succ_mul] at this
        omega
      have h4 : m % p < u := by rw [hmodμ]; subst htop; omega
      obtain ⟨-, -, -, f4⟩ := lo_facts (n := n) (m := m) (t := t) hu
      rw [Tm_eq_lo hn1 (by have := hi26 u hu; omega)]
      refine Dvd.dvd.mul_left (Tlo_dvd_of ?_) _
      rw [show 3 = 2 + 1 by rfl, pow_add, pow_one]
      exact mul_dvd_mul (choose_sq_dvd_two hu h4 (by rw [hM1, htop]) ht' hmsq hm2) (hHdvd t u hu)
    · have e : ∑ u ∈ range p, Tm n m (t * p + u)
          = (-1 : ℤ) ^ (27 * n) * ∑ u ∈ range p, Tlo n m (t * p + u) := by
        rw [mul_sum]
        exact sum_congr rfl fun u hu => Tm_eq_lo hn1 (by have := hi26 u (mem_range.mp hu); omega)
      rw [e]
      exact Dvd.dvd.mul_left (hblk2 m hmp t ht').1 _
  · -- a MIDDLE block, against the reduced row `tp + (m mod p)`
    have hlt : μ < t * p := (Nat.div_lt_iff_lt_mul hp0).mp (by omega)
    have hT0 : ∀ u < p, Tm n m (p ^ 2 + (t * p + u)) = 0 := by
      intro u _
      unfold Tm
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [sum_congr rfl fun u hu => by rw [hT0 u (mem_range.mp hu), add_zero]]
    have hMt : p ∣ (m / p).choose t := by
      rw [← ZMod.natCast_eq_zero_iff, hMdiv, Zeta2PtpS7.lucas_raw (p + μ / p) t, Nat.add_mod_left,
        Nat.mod_eq_of_lt hμ1, Nat.mod_eq_of_lt ht', Nat.choose_eq_zero_of_lt (by omega),
        Nat.cast_zero, zero_mul]
    have hM1' : 1 ≤ m / p := by rw [hMdiv]; exact Nat.le_add_right_of_le hp0
    have htm : t * p + p ≤ m + 1 := by
      have h1 : t * p + p ≤ p * p := etp1 ▸ htp1
      have h2 : p * p ≤ m := hpp2 ▸ hmsq
      exact le_trans h1 (le_trans h2 (Nat.le_succ m))
    refine mid_block_cube hM1' hMt htm (fun u hu => ?_) ?_
    · by_cases hi1 : t * p + u ≤ 13 * n
      · rw [Zeta2PtpCoeff.Hfun_of_le n _ hi1]
        exact Dvd.dvd.mul_left (by exact_mod_cast Int.natCast_dvd_natCast.2 (hHdvd t u hu)) _
      · by_cases hi2 : t * p + u ≤ 26 * n
        · rw [Zeta2PtpCoeff.Hfun_eq_zero n _ (by omega) hi2]
          exact dvd_zero _
        · rw [Zeta2PtpKummer.Hfun_of_gt n _ (by omega)]
          obtain ⟨g1, g2, g3, -⟩ := hi_facts (n := n) (m := m) (t := t) hu hn1
          have hd : p ∣ (t * p + u - (13 * n + 1)).choose (13 * n)
              * (t * p + u - (15 * n + 1)).choose (9 * n)
              * (t * p + u - (17 * n + 1)).choose (5 * n) := by
            rcases hHhi u hu with h | h | h
            · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (g1 h) _) _
            · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (g2 h) _) _
            · exact Dvd.dvd.mul_left (g3 h) _
          rw [show t * p + u - 13 * n - 1 = t * p + u - (13 * n + 1) by omega,
            show t * p + u - 15 * n - 1 = t * p + u - (15 * n + 1) by omega,
            show t * p + u - 17 * n - 1 = t * p + u - (17 * n + 1) by omega]
          exact_mod_cast Int.natCast_dvd_natCast.2 hd
    · have hm'' : (t * p + m % p) % p = (11 * n) % p := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod, hmp]
      obtain ⟨hl, hh⟩ := hblk2 _ hm'' t ht'
      rw [sum_congr rfl fun u _ => Tm_eq_lo_hi n _ (t * p + u) hn1, sum_add_distrib, ← mul_sum]
      exact dvd_add (Dvd.dvd.mul_left hl _) hh

/-! ## The strata -/

/-- The coefficient bound at a polar row above `p²` from `p³ ∣ h_m`, on a φ̃ = 2 stratum. -/
theorem pval_of_cube {n p r : ℕ} (hp : p ∈ Zeta2PhiT.phiWindow n) (hr : r < 16 * n)
    (hpol : p ∣ r + 1) (hm : p ^ 2 ≤ 11 * n + 1 + r)
    (hphi : Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) = 2)
    (h : (p : ℤ) ^ 3 ∣ Zeta2NewtonAssemble.hc n (11 * n + 1 + r)) :
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ) := by
  have hpp := Zeta2PhiT.prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  refine Zeta2PtpResPair.pval_coeff_of_dvd hp ?_
  rw [Zeta2PtpResPair.padicValNat_LC_sq hp hr hm, Zeta2PtpResPair.units_LC_polar hp hpol,
    Zeta2PtpKumRes.bbit_polar hpol, hphi]
  rw [show 2 + 1 - 1 + (1 + 1) = 1 + 3 by rfl, pow_add, pow_one]
  exact mul_dvd_mul_left _ h

section Strata
variable {p : ℕ} [hp : Fact p.Prime]

open Zeta2PtpRunS2

theorem S2a1_blk2 (hp2 : 2 < p) {n m a s t : ℕ} (hn1 : 1 ≤ n) (hn' : n = p * a + s)
    (h1 : 1 * p ≤ 9 * s) (h2 : 26 * s < 3 * p) (hpa : 26 * 9 * a + 26 * 1 < 9 * p)
    (hmp : m % p = (11 * n) % p) (htp : t < p) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, Tlo n m (t * p + u)
      ∧ (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, Thi n m (t * p + u) := by
  obtain ⟨hone_lo, htwo_lo⟩ := S2a1_lo hn' h1 h2 hmp
  obtain ⟨hone_hi, htwo_hi⟩ := S2a1_hi hn' h1 h2 hmp
  have hdeg := S2a1_deg hn' h1 h2 hmp
  obtain ⟨r5, -, -, -, -, -, -⟩ := S2a1_res hn' h1 h2
  refine ⟨?_, ?_⟩
  · by_cases hz : 13 * a + 1 < t
    · have e1 : (13 * a + 1 + 1) * p ≤ t * p := Nat.mul_le_mul_right p hz
      have e2 : (13 * a + 1 + 1) * p = 13 * (p * a) + 2 * p := by ring
      exact lo_all_zero hn1 (by omega)
    obtain ⟨hh3, h3p⟩ := S2a1_lo_h3 hn' h1 h2 hpa (t := t) (by omega)
    exact lo3_block_dvd hp2 hn1 hdeg (by omega) hone_lo htwo_lo
      (fun u hu hk ho1 ho2 ho3 => S2a1_lo_hsup hn' h1 h2 hpa hmp (by omega) hu hk ho1 ho2 ho3)
      hh3 h3p
  · by_cases hz : t < 26 * a + 2
    · have e1 : t * p + p ≤ (26 * a + 2) * p := by
        have := Nat.mul_le_mul_right p hz
        rw [Nat.succ_mul] at this; exact this
      have e2 : (26 * a + 2) * p = 26 * (p * a) + 2 * p := by ring
      exact hi_all_zero hn1 (by omega)
    by_cases hlowb : t = 26 * a + 2
    · subst hlowb
      exact hi3_block_low hn1 htwo_hi (fun u hu hk ho1 ho2 ho3 =>
        S2a1_hi_low hn' h1 h2 hmp hu hk ho1 ho2 ho3)
    obtain ⟨hh3, h3p⟩ := S2a1_hi_h3 hn' h1 h2 (t := t) (by omega) htp
    exact hi3_block_dvd hp2 hn1 hdeg (by omega) hone_hi htwo_hi
      (fun u hu hk ho1 ho2 ho3 => S2a1_hi_hsup hn' h1 h2 hmp (by omega) htp hu hk ho1 ho2 ho3)
      hh3 h3p

theorem S2a2_blk2 (hp2 : 2 < p) {n m a s t : ℕ} (hn1 : 1 ≤ n) (hn' : n = p * a + s)
    (h1 : 3 * p ≤ 26 * s) (h2 : 17 * s < 2 * p) (hpa : 26 * 26 * a + 26 * 3 < 26 * p)
    (hmp : m % p = (11 * n) % p) (htp : t < p) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, Tlo n m (t * p + u)
      ∧ (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, Thi n m (t * p + u) := by
  obtain ⟨hone_lo, htwo_lo⟩ := S2a2_lo hn' h1 h2 hmp
  obtain ⟨hone_hi, htwo_hi⟩ := S2a2_hi hn' h1 h2 hmp
  have hdeg := S2a2_deg hn' h1 h2 hmp
  obtain ⟨r5, -, -, -, -, -, -⟩ := S2a2_res hn' h1 h2
  refine ⟨?_, ?_⟩
  · by_cases hz : 13 * a + 1 < t
    · have e1 : (13 * a + 1 + 1) * p ≤ t * p := Nat.mul_le_mul_right p hz
      have e2 : (13 * a + 1 + 1) * p = 13 * (p * a) + 2 * p := by ring
      exact lo_all_zero hn1 (by omega)
    obtain ⟨hh3, h3p⟩ := S2a2_lo_h3 hn' h1 h2 hpa (t := t) (by omega)
    exact lo3_block_dvd hp2 hn1 hdeg (by omega) hone_lo htwo_lo
      (fun u hu hk ho1 ho2 ho3 => S2a2_lo_hsup hn' h1 h2 hpa hmp (by omega) hu hk ho1 ho2 ho3)
      hh3 h3p
  · by_cases hz : t < 26 * a + 3
    · have e1 : t * p + p ≤ (26 * a + 3) * p := by
        have := Nat.mul_le_mul_right p hz
        rw [Nat.succ_mul] at this; exact this
      have e2 : (26 * a + 3) * p = 26 * (p * a) + 3 * p := by ring
      exact hi_all_zero hn1 (by omega)
    obtain ⟨hh3, h3p⟩ := S2a2_hi_h3 hn' h1 h2 (t := t) (by omega) htp
    exact hi3_block_dvd hp2 hn1 hdeg (by omega) hone_hi htwo_hi
      (fun u hu hk ho1 ho2 ho3 => S2a2_hi_hsup hn' h1 h2 hmp (by omega) htp hu hk ho1 ho2 ho3)
      hh3 h3p

theorem S2b_blk2 (hp2 : 2 < p) {n m a s t : ℕ} (hn1 : 1 ≤ n) (hn' : n = p * a + s)
    (h1 : 5 * p ≤ 9 * s) (h2 : 16 * s < 9 * p) (hpa : 26 * 9 * a + 26 * 5 < 9 * p)
    (hmp : m % p = (11 * n) % p) (htp : t < p) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, Tlo n m (t * p + u)
      ∧ (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, Thi n m (t * p + u) := by
  obtain ⟨hone_lo, htwo_lo⟩ := S2b_lo hn' h1 h2 hmp
  obtain ⟨hone_hi, htwo_hi⟩ := S2b_hi hn' h1 h2 hmp
  have hdeg := S2b_deg hn' h1 h2 hmp
  obtain ⟨r5, -, -, -, -, -, -⟩ := S2b_res hn' h1 h2
  refine ⟨?_, ?_⟩
  · by_cases hz : 13 * a + 7 < t
    · have e1 : (13 * a + 7 + 1) * p ≤ t * p := Nat.mul_le_mul_right p hz
      have e2 : (13 * a + 7 + 1) * p = 13 * (p * a) + 8 * p := by ring
      exact lo_all_zero hn1 (by omega)
    obtain ⟨hh3, h3p⟩ := S2b_lo_h3 hn' h1 h2 hpa (t := t) (by omega)
    exact lo3_block_dvd hp2 hn1 hdeg (by omega) hone_lo htwo_lo
      (fun u hu hk ho1 ho2 ho3 => S2b_lo_hsup hn' h1 h2 hpa hmp (by omega) hu hk ho1 ho2 ho3)
      hh3 h3p
  · by_cases hz : t < 26 * a + 14
    · have e1 : t * p + p ≤ (26 * a + 14) * p := by
        have := Nat.mul_le_mul_right p hz
        rw [Nat.succ_mul] at this; exact this
      have e2 : (26 * a + 14) * p = 26 * (p * a) + 14 * p := by ring
      exact hi_all_zero hn1 (by omega)
    by_cases hlowb : t = 26 * a + 14
    · subst hlowb
      exact hi3_block_low hn1 htwo_hi (fun u hu hk ho1 ho2 ho3 =>
        S2b_hi_low hn' h1 h2 hmp hu hk ho1 ho2 ho3)
    obtain ⟨hh3, h3p⟩ := S2b_hi_h3 hn' h1 h2 (t := t) (by omega) htp
    exact hi3_block_dvd hp2 hn1 hdeg (by omega) hone_hi htwo_hi
      (fun u hu hk ho1 ho2 ho3 => S2b_hi_hsup hn' h1 h2 hmp (by omega) htp hu hk ho1 ho2 ho3)
      hh3 h3p

end Strata

/-- The common preamble: a window prime is `> 2`, and the stratum's `n = p·a + s`. -/
theorem two_lt_of_window {n p : ℕ} (hp : p ∈ Zeta2PhiT.phiWindow n) : 2 < p := by
  have hsq := Zeta2PhiT.sq_gt_of_mem_phiWindow hp
  have hn1 := Zeta2PtpPolar.pos_of_mem_phiWindow hp
  by_contra hc
  have : p ^ 2 ≤ 4 := by
    have : p ≤ 2 := by omega
    calc p ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left this 2
      _ = 4 := by norm_num
  omega

theorem polar_mod {n p r : ℕ} (hpol : p ∣ r + 1) : (11 * n + 1 + r) % p = (11 * n) % p := by
  rw [show 11 * n + 1 + r = 11 * n + (r + 1) by ring, Nat.add_mod, Nat.mod_eq_zero_of_dvd hpol,
    Nat.add_zero, Nat.mod_mod]

/-- **`[1/9, 3/26)` ABOVE `p²`, CLOSED.** -/
theorem S2a1_high {n p r : ℕ} (hp : p ∈ Zeta2PhiT.phiWindow n) (hr : r < 16 * n)
    (hpol : p ∣ r + 1) (hm : p ^ 2 ≤ 11 * n + 1 + r) (h1 : 1 * p ≤ 9 * (n % p))
    (h2 : 26 * (n % p) < 3 * p) :
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ) := by
  have hpp := Zeta2PhiT.prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 := hpp.pos
  have hsq := Zeta2PhiT.sq_gt_of_mem_phiWindow hp
  have hn1 := Zeta2PtpPolar.pos_of_mem_phiWindow hp
  have hp2 := two_lt_of_window hp
  refine pval_of_cube hp hr hpol hm (Zeta2PtpS2a.phiT_piece2_res hp0 (by omega) (by omega)) ?_
  have hmp := polar_mod (n := n) hpol
  have hn' : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hwin : 26 * (p * (n / p) + n % p) + 1 < p ^ 2 := by rw [← hn']; exact hsq
  have hs := Nat.mod_lt n hp0
  generalize n / p = a at hn' hwin
  generalize n % p = s at hn' h1 h2 hwin hs
  have hpa := win_bound hwin h1 (by norm_num)
  obtain ⟨hone, htwo⟩ := Zeta2PtpRunS2.S2a1_lo hn' h1 h2 hmp
  obtain ⟨-, htwo_hi⟩ := Zeta2PtpRunS2.S2a1_hi hn' h1 h2 hmp
  exact f1_high hsq hn1 hr hm hmp hn' hs hone htwo htwo_hi
    (fun t u ht hu hk ho1 ho2 ho3 =>
      Zeta2PtpRunS2.S2a1_lo_hsup hn' h1 h2 hpa hmp (by omega) hu hk ho1 ho2 ho3)
    (fun m' hm' t ht => S2a1_blk2 hp2 hn1 hn' h1 h2 hpa hm' ht)

/-- **`[3/26, 2/17)` ABOVE `p²`, CLOSED.** -/
theorem S2a2_high {n p r : ℕ} (hp : p ∈ Zeta2PhiT.phiWindow n) (hr : r < 16 * n)
    (hpol : p ∣ r + 1) (hm : p ^ 2 ≤ 11 * n + 1 + r) (h1 : 3 * p ≤ 26 * (n % p))
    (h2 : 17 * (n % p) < 2 * p) :
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ) := by
  have hpp := Zeta2PhiT.prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 := hpp.pos
  have hsq := Zeta2PhiT.sq_gt_of_mem_phiWindow hp
  have hn1 := Zeta2PtpPolar.pos_of_mem_phiWindow hp
  have hp2 := two_lt_of_window hp
  refine pval_of_cube hp hr hpol hm (Zeta2PtpS2a.phiT_piece2_res hp0 (by omega) (by omega)) ?_
  have hmp := polar_mod (n := n) hpol
  have hn' : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hwin : 26 * (p * (n / p) + n % p) + 1 < p ^ 2 := by rw [← hn']; exact hsq
  have hs := Nat.mod_lt n hp0
  generalize n / p = a at hn' hwin
  generalize n % p = s at hn' h1 h2 hwin hs
  have hpa := win_bound hwin h1 (by norm_num)
  obtain ⟨hone, htwo⟩ := Zeta2PtpRunS2.S2a2_lo hn' h1 h2 hmp
  obtain ⟨-, htwo_hi⟩ := Zeta2PtpRunS2.S2a2_hi hn' h1 h2 hmp
  exact f1_high hsq hn1 hr hm hmp hn' hs hone htwo htwo_hi
    (fun t u ht hu hk ho1 ho2 ho3 =>
      Zeta2PtpRunS2.S2a2_lo_hsup hn' h1 h2 hpa hmp (by omega) hu hk ho1 ho2 ho3)
    (fun m' hm' t ht => S2a2_blk2 hp2 hn1 hn' h1 h2 hpa hm' ht)

/-- **`[5/9, 9/16)` ABOVE `p²`, CLOSED.** -/
theorem S2b_high {n p r : ℕ} (hp : p ∈ Zeta2PhiT.phiWindow n) (hr : r < 16 * n)
    (hpol : p ∣ r + 1) (hm : p ^ 2 ≤ 11 * n + 1 + r) (h1 : 5 * p ≤ 9 * (n % p))
    (h2 : 16 * (n % p) < 9 * p) :
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ) := by
  have hpp := Zeta2PhiT.prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 := hpp.pos
  have hsq := Zeta2PhiT.sq_gt_of_mem_phiWindow hp
  have hn1 := Zeta2PtpPolar.pos_of_mem_phiWindow hp
  have hp2 := two_lt_of_window hp
  refine pval_of_cube hp hr hpol hm (Zeta2PtpS2b.phiT_piece16_res hp0 (by omega) (by omega)) ?_
  have hmp := polar_mod (n := n) hpol
  have hn' : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hwin : 26 * (p * (n / p) + n % p) + 1 < p ^ 2 := by rw [← hn']; exact hsq
  have hs := Nat.mod_lt n hp0
  generalize n / p = a at hn' hwin
  generalize n % p = s at hn' h1 h2 hwin hs
  have hpa := win_bound hwin h1 (by norm_num)
  obtain ⟨hone, htwo⟩ := Zeta2PtpRunS2.S2b_lo hn' h1 h2 hmp
  obtain ⟨-, htwo_hi⟩ := Zeta2PtpRunS2.S2b_hi hn' h1 h2 hmp
  exact f1_high hsq hn1 hr hm hmp hn' hs hone htwo htwo_hi
    (fun t u ht hu hk ho1 ho2 ho3 =>
      Zeta2PtpRunS2.S2b_lo_hsup hn' h1 h2 hpa hmp (by omega) hu hk ho1 ho2 ho3)
    (fun m' hm' t ht => S2b_blk2 hp2 hn1 hn' h1 h2 hpa hm' ht)

/-- **`[6/13, 7/15)` ABOVE `p²`, CLOSED.** -/
theorem S2c_high {n p r : ℕ} (hp : p ∈ Zeta2PhiT.phiWindow n) (hr : r < 16 * n)
    (hpol : p ∣ r + 1) (hm : p ^ 2 ≤ 11 * n + 1 + r) (h1 : 6 * p ≤ 13 * (n % p))
    (h2 : 15 * (n % p) < 7 * p) :
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ) := by
  have hpp := Zeta2PhiT.prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 := hpp.pos
  have hsq := Zeta2PhiT.sq_gt_of_mem_phiWindow hp
  have hn1 := Zeta2PtpPolar.pos_of_mem_phiWindow hp
  have hp2 := two_lt_of_window hp
  refine pval_of_cube hp hr hpol hm (Zeta2PtpS2c.phiT_piece13_res hp0 (by omega) (by omega)) ?_
  have hmp := polar_mod (n := n) hpol
  have hm2 : 11 * n + 1 + r < p ^ 2 + p ^ 2 := by omega
  have hn' : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hwin : 26 * (p * (n / p) + n % p) + 1 < p ^ 2 := by rw [← hn']; exact hsq
  have hs := Nat.mod_lt n hp0
  generalize n / p = a at hn' hwin
  generalize n % p = s at hn' h1 h2 hwin hs
  have hpa := win_bound hwin h1 (by norm_num)
  obtain ⟨hone, htwo⟩ := Zeta2PtpRunS2.S2c_lo hn' h1 h2 hmp
  have e1 : (13 * a + 6 + 1) * p = 13 * (p * a) + 7 * p := by ring
  have e2 : (26 * a + 12) * p = 26 * (p * a) + 12 * p := by ring
  exact f2_high hp2 hsq hn1 hr hm hmp hn' hs (Zeta2PtpRunS2.S2c_deg hn' h1 h2 hmp) hone htwo
    (fun t u ht hu hk ho1 ho2 ho3 =>
      Zeta2PtpRunS2.S2c_lo_hsup hn' h1 h2 hpa hmp ht hu hk ho1 ho2 ho3)
    (by omega) (by omega) (by omega)
    (fun t ht1 htp hHI => S2c_hi_mid_cube hp2 hn1 hn' h1 h2 hmp hm hm2 ht1 htp hHI)

/-- **`[12/13, 14/15)` ABOVE `p²`, CLOSED.** -/
theorem S2d_high {n p r : ℕ} (hp : p ∈ Zeta2PhiT.phiWindow n) (hr : r < 16 * n)
    (hpol : p ∣ r + 1) (hm : p ^ 2 ≤ 11 * n + 1 + r) (h1 : 12 * p ≤ 13 * (n % p))
    (h2 : 15 * (n % p) < 14 * p) :
    Zeta2PtpPolar.PVal p (Zeta2PhiT.phiT (Int.fract ((n : ℚ) / (p : ℚ))) + Zeta2PtpPoly.bbit n p r - 1)
      ((Zeta2PtpPoly.coeff n r : ℤ) : ℚ) := by
  have hpp := Zeta2PhiT.prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 := hpp.pos
  have hsq := Zeta2PhiT.sq_gt_of_mem_phiWindow hp
  have hn1 := Zeta2PtpPolar.pos_of_mem_phiWindow hp
  have hp2 := two_lt_of_window hp
  refine pval_of_cube hp hr hpol hm (Zeta2PtpS2d.phiT_piece25_res hp0 (by omega) (by omega)) ?_
  have hmp := polar_mod (n := n) hpol
  have hm2 : 11 * n + 1 + r < p ^ 2 + p ^ 2 := by omega
  have hn' : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hwin : 26 * (p * (n / p) + n % p) + 1 < p ^ 2 := by rw [← hn']; exact hsq
  have hs := Nat.mod_lt n hp0
  generalize n / p = a at hn' hwin
  generalize n % p = s at hn' h1 h2 hwin hs
  have hpa := win_bound hwin h1 (by norm_num)
  obtain ⟨hone, htwo⟩ := Zeta2PtpRunS2.S2d_lo hn' h1 h2 hmp
  have e1 : (13 * a + 12 + 1) * p = 13 * (p * a) + 13 * p := by ring
  have e2 : (26 * a + 24) * p = 26 * (p * a) + 24 * p := by ring
  exact f2_high hp2 hsq hn1 hr hm hmp hn' hs (Zeta2PtpRunS2.S2d_deg hn' h1 h2 hmp) hone htwo
    (fun t u ht hu hk ho1 ho2 ho3 =>
      Zeta2PtpRunS2.S2d_lo_hsup hn' h1 h2 hpa hmp ht hu hk ho1 ho2 ho3)
    (by omega) (by omega) (by omega)
    (fun t ht1 htp hHI => S2d_hi_mid_cube hp2 hn1 hn' h1 h2 hmp hm hm2 ht1 htp hHI)

/-! ## `RestAboveS2Open`, `RestAboveOpen`, and the polynomial half -/

/-- **THE FOUR φ̃ = 2 STRATA ABOVE `p²`, CLOSED.** -/
theorem restAboveS2Open : Zeta2PtpMbigS7.RestAboveS2Open := by
  intro n p r hp hr hpol hrun hns7 hm
  unfold Zeta2PtpKumRows.RunStrata at hrun
  rcases hrun with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases h3 : 26 * (n % p) < 3 * p
    · exact S2a1_high hp hr hpol hm (by omega) h3
    · exact S2a2_high hp hr hpol hm (by omega) (by omega)
  · exact absurd ⟨h1, h2⟩ hns7
  · exact S2c_high hp hr hpol hm (by omega) (by omega)
  · exact S2b_high hp hr hpol hm (by omega) (by omega)
  · exact S2d_high hp hr hpol hm (by omega) (by omega)

/-- **`RestAboveOpen` IS A THEOREM** — every polar run-strata row at or above `p²`. -/
theorem restAboveOpen : Zeta2PtpMbig.RestAboveOpen :=
  Zeta2PtpMbigS7.restAboveOpen_of_S2 restAboveS2Open

/-- **THE POLYNOMIAL HALF OF ROW PT-P, WITH NO BINDER.** -/
theorem polyHalfOpen : Zeta2PtpPolar.PolyHalfOpen :=
  Zeta2PtpMbigS7.polyHalfOpen_of_S2 restAboveS2Open

end Zeta2PtpMbigS2

#print axioms Zeta2PtpMbigS2.f2_high
#print axioms Zeta2PtpMbigS2.f1_high
#print axioms Zeta2PtpMbigS2.S2a1_high
#print axioms Zeta2PtpMbigS2.S2a2_high
#print axioms Zeta2PtpMbigS2.S2b_high
#print axioms Zeta2PtpMbigS2.S2c_high
#print axioms Zeta2PtpMbigS2.S2d_high
#print axioms Zeta2PtpMbigS2.restAboveS2Open
#check @Zeta2PtpMbigS2.restAboveS2Open
#print axioms Zeta2PtpMbigS2.restAboveOpen
#check @Zeta2PtpMbigS2.restAboveOpen
#print axioms Zeta2PtpMbigS2.polyHalfOpen
#check @Zeta2PtpMbigS2.polyHalfOpen
#print Zeta2PtpPolar.PolyHalfOpen
