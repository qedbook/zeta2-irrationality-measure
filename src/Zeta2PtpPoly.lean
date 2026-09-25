/-
# Row PT-P, layer 8 — the POLYNOMIAL half `PolyHalfOpen`, reduced to ONE bound per Newton
# coefficient, with the `(r, m)` accounting that `ptp_poly_probe.py` measured termwise

`Zeta2PtpPolar.PolyHalfOpen` is `v_p(Δ·Π·pnPoly) ≥ φ̃({n/p})` at every window prime.  The landed
Newton form (`Zeta2PnFunc.Pin_mul_pnPoly_newton`, `Lf_nbp`) writes

    Π·pnPoly = Σ_{r<16n} a_r · L_r,   a_r = h_{L+r} / (L·C(L+r,L)),   L_r = Σ_{m≤r} (−1)^m/(m+1)·C(11n, r−m),

`L = 11n+1`, `h_m = Δ^m H(0)` (`Zeta2NewtonAssemble.hc`), and `Δ 16 15 n = D(16n)·D(15n)` clears
the two denominators separately: `D(15n)·a_r ∈ ℤ` (`termwise_at_D15`) and `D(16n)/(m+1) ∈ ℤ`.
So `Δ·Π·pnPoly` is the DOUBLE sum of integers `coeff n r · mterm n r m`, and the probe
(`ptp_poly_probe.out`, 622 cells, 97 120 `r`-rows) found the obligation TERMWISE in that double
sum with the profile carried by the coefficient alone:

    v_p(coeff n r) ≥ φ̃ + b_r − 1,   b_r := [(r+1) % p ≤ (11n) % p]      (all 97 120 rows),

while `D(16n)/(m+1)` carries one `p` unless `p ∣ m+1`, and at such a POLAR `m` the binomial
`C(11n, r−m)` carries exactly when `b_r = 0` — the units digit of `r−m` is that of `r+1`.
THIS FILE PROVES THAT ACCOUNTING: `polyHalfOpen_of_coeffBound : CoeffBoundOpen → PolyHalfOpen`,
axiom-free, with `CoeffBoundOpen` the per-`r` bound above as a named `Prop`.

WHAT IS NOT CLAIMED.  `CoeffBoundOpen` is NOT proved here — it is measured, and its mechanism
is mapped in the probe: a Kummer count on `h_m = Σ_i (−1)^{m−i} C(m,i) H(i)` gives it at 97 069
of 97 120 rows, and the 51 others (all at `r ≡ −1 (mod p)`) are the sibling's run congruence on
the four run strata plus one `m ≥ p²` pairing.  `polyHalfOpen_of_coeffBound` is a CONDITIONAL
theorem whose type names that binder; `#print axioms` cannot see it (LEAN.md §1).  PT-P does NOT
close and `Zeta2Target.zeta2_not_liouvilleWith` is `sorry`.

Falsifier: `falsify_ptppoly.sh` / `out_ptppoly_falsify.txt`.

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

namespace Zeta2PtpPoly

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpPolar Zeta2PnFunc Zeta2NewtonAssemble Nat Finset

/-! ## 1. The two integer factors of the `(r, m)` term -/

/-- **`coeff n r = D(15n)·a_r`**, the Newton coefficient of `Π·Ppol` cleared by `D(15n)`:
`D(15n)·h_{L+r} / (L·C(L+r, L))`, an exact integer division by `termwise_at_D15`. -/
def coeff (n r : ℕ) : ℤ :=
  ((D (15 * n) : ℕ) : ℤ) * hc n (11 * n + 1 + r)
    / (((11 * n + 1) * ((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℤ)

theorem LC_ne_zero (n r : ℕ) :
    (((11 * n + 1) * ((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℤ) ≠ 0 := by
  have := Nat.choose_pos (show 11 * n + 1 ≤ 11 * n + 1 + r by omega)
  simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero, not_or]
  omega

/-- The division is exact: `L·C(L+r,L) · coeff = D(15n)·h_{L+r}`. -/
theorem coeff_spec (n r : ℕ) :
    (((11 * n + 1) * ((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℤ) * coeff n r
      = ((D (15 * n) : ℕ) : ℤ) * hc n (11 * n + 1 + r) := by
  obtain ⟨z, hz⟩ := termwise_at_D15 n r
  rw [coeff, hz, Int.mul_ediv_cancel_left _ (LC_ne_zero n r)]

/-- **`mterm n r m = (−1)^m · D(16n)/(m+1) · C(11n, r−m)`**, the `m`-th term of `D(16n)·L_r`. -/
def mterm (n r m : ℕ) : ℤ :=
  (-1 : ℤ) ^ m * ((D (16 * n) / (m + 1) : ℕ) : ℤ) * (((11 * n).choose (r - m) : ℕ) : ℤ)

/-- `D(16n)·L_r = Σ_{m ≤ r} mterm n r m` — `D_mul_Lf_nbp_int`'s witness, exhibited. -/
theorem D16_mul_Lf_nbp (n r : ℕ) (hr : r + 1 ≤ 16 * n) :
    ((D (16 * n) : ℕ) : ℚ) * Lf n (16 * n + 1) (nbp ((15 * n : ℕ) : ℚ) r)
      = ∑ m ∈ range (r + 1), ((mterm n r m : ℤ) : ℚ) := by
  rw [Lf_nbp n (16 * n + 1) r (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : m + 1 ≤ 16 * n := by
    have := Finset.mem_range.mp hm
    omega
  have hdvd : (m + 1) ∣ D (16 * n) := dvd_D (by omega) hm1
  have hne : (((m + 1 : ℕ)) : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  -- NOT `push_cast` on the division (`Int.natCast_div` destroys the exact-division shape).
  rw [mterm]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  rw [Nat.cast_div hdvd hne, cf]
  rw [show (((m + 1 : ℕ)) : ℚ) = (m : ℚ) + 1 by push_cast; ring] at hne ⊢
  field_simp

/-! ## 2. `Δ·Π·pnPoly` as the double sum of integers -/

/-- **The `(r, m)` expansion.**  `Δ 16 15 n · Π · pnPoly = Σ_r Σ_{m ≤ r} coeff n r · mterm n r m`. -/
theorem Delta_Pin_pnPoly_eq (n : ℕ) :
    ((Δ 16 15 n : ℕ) : ℚ) * (candidateM.Pin n * candidateM.pnPoly n)
      = ∑ r ∈ range (16 * n), ∑ m ∈ range (r + 1), ((coeff n r * mterm n r m : ℤ) : ℚ) := by
  rw [Pin_mul_pnPoly_newton, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrlt : r < 16 * n := Finset.mem_range.mp hr
  have hL : ((11 * n + 1 : ℕ) : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hcb : ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ) ≠ 0 := by
    have := Nat.choose_pos (show 11 * n + 1 ≤ 11 * n + 1 + r by omega)
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hcq : ((D (15 * n) : ℕ) : ℚ) * ((hc n (11 * n + 1 + r) : ℤ) : ℚ)
      = ((11 * n + 1 : ℕ) : ℚ) * ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ)
          * ((coeff n r : ℤ) : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (coeff_spec n r)
    push_cast at h ⊢
    linear_combination (-1 : ℚ) * h
  have hwq := D16_mul_Lf_nbp n r (by omega)
  have hsplit : ((D (16 * n) : ℕ) : ℚ) * ((D (15 * n) : ℕ) : ℚ)
        * (((hc n (11 * n + 1 + r) : ℤ) : ℚ)
            / (((11 * n + 1 : ℕ) : ℚ) * ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ))
          * Lf n (16 * n + 1) (nbp ((15 * n : ℕ) : ℚ) r))
      = (((D (16 * n) : ℕ) : ℚ) * Lf n (16 * n + 1) (nbp ((15 * n : ℕ) : ℚ) r))
        * ((((D (15 * n) : ℕ) : ℚ) * ((hc n (11 * n + 1 + r) : ℤ) : ℚ))
            / (((11 * n + 1 : ℕ) : ℚ)
              * ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ))) := by
    field_simp
  rw [Zeta2Arith.Δ, Nat.cast_mul, hsplit, hcq, hwq]
  have hLC : ((11 * n + 1 : ℕ) : ℚ) * ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ) ≠ 0 :=
    mul_ne_zero hL hcb
  rw [mul_div_cancel_left₀ _ hLC, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

/-! ## 3. The valuation of each factor at a window prime -/

theorem pval_natCast {p : ℕ} (hp : p.Prime) (x : ℕ) : PVal p 0 ((x : ℚ)) :=
  ⟨x, 1, one_pos, not_dvd_one hp, by push_cast; ring⟩

/-- **A non-polar `m` keeps one `p` in `D(16n)/(m+1)`**: `p ∣ D(16n)` (`p ≤ 15n`) and `p ∤ m+1`. -/
theorem pval_D16_div {n p m : ℕ} (hp : p ∈ phiWindow n) (hm : m + 1 ≤ 16 * n)
    (hnd : ¬ p ∣ m + 1) : PVal p 1 (((D (16 * n) / (m + 1) : ℕ) : ℚ)) := by
  have hpp := prime_of_mem_phiWindow hp
  have hle := Zeta2PhiTDvd.le_of_mem_phiWindow hp
  obtain ⟨q, hq⟩ := dvd_D (show 1 ≤ m + 1 by omega) hm
  have hpD : p ∣ D (16 * n) := dvd_D hpp.pos (by omega)
  rw [hq] at hpD
  have hpq : p ∣ q := ((Nat.Prime.dvd_mul hpp).mp hpD).resolve_left hnd
  have hdiv : D (16 * n) / (m + 1) = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left q (by omega)
  rw [hdiv]
  obtain ⟨c, hc⟩ := hpq
  exact ⟨c, 1, one_pos, not_dvd_one hpp, by rw [hc]; push_cast; ring⟩

/-- **A carried binomial**: at a window prime `C(11n, j)`, `j ≤ 11n`, carries exactly its units
bit (`Zeta2PtpRun.vp_choose_eq_cb`), so `(11n) % p < j % p` gives `p ∣ C(11n, j)`. -/
theorem pval_choose_of_units {n p j : ℕ} (hp : p ∈ phiWindow n) (hj : j ≤ 11 * n)
    (hc : (11 * n) % p < j % p) : PVal p 1 ((((11 * n).choose j : ℕ)) : ℚ) := by
  have hpp := prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hsq : 26 * n + 1 < p ^ 2 := sq_gt_of_mem_phiWindow hp
  have hlog : Nat.log p (11 * n) ≤ 1 := Zeta2PtpRun.log_le_one_of_lt_sq (by omega)
  have hv : padicValNat p ((11 * n).choose j) = 1 := by
    rw [Zeta2PtpRun.vp_choose_eq_cb hj hlog]
    simp [Zeta2PtpRun.cb, hc]
  have hdvd : p ^ 1 ∣ (11 * n).choose j := by
    rw [← hv]
    exact pow_padicValNat_dvd
  obtain ⟨c, hc'⟩ := hdvd
  exact ⟨c, 1, one_pos, not_dvd_one hpp, by rw [hc']; push_cast; ring⟩

/-- At a polar `m` (`p ∣ m+1`, `m ≤ r`) the units digit of `r − m` is that of `r + 1`. -/
theorem sub_mod_eq_succ_mod {p r m : ℕ} (hm : m ≤ r) (hd : p ∣ m + 1) :
    (r - m) % p = (r + 1) % p := by
  have h : r + 1 = (r - m) + (m + 1) := by omega
  rw [h, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero, Nat.mod_mod]

/-! ## 4. The per-`r` bound, and the `(r, m)` accounting -/

/-- `b_r = [(r+1) % p ≤ (11n) % p]` — the complement of the polar binomial's carry bit. -/
def bbit (n p r : ℕ) : ℕ := if (r + 1) % p ≤ (11 * n) % p then 1 else 0

/-- **THE ONE OPEN OBLIGATION OF THE POLYNOMIAL HALF.**  `v_p(D(15n)·a_r) ≥ φ̃ + b_r − 1` at
every window cell and every `r < 16n`.  Measured at 97 120 of 97 120 rows
(`ptp_poly_probe.out`); NOT proved here. -/
def CoeffBoundOpen : Prop :=
  ∀ n p r : ℕ, p ∈ phiWindow n → r < 16 * n →
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r - 1) ((coeff n r : ℤ) : ℚ)

/-- **One `(r, m)` term carries `p^φ̃`**, from the coefficient bound: a non-polar `m` pays with
`D(16n)/(m+1)`, a polar `m` with `b_r = 1` pays with the coefficient's extra unit, and a polar
`m` with `b_r = 0` pays with the carried `C(11n, r−m)`. -/
theorem pval_term {n p r m : ℕ} (hp : p ∈ phiWindow n) (hr : r < 16 * n) (hm : m ≤ r)
    (hc : PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r - 1) ((coeff n r : ℤ) : ℚ)) :
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ)))) ((coeff n r * mterm n r m : ℤ) : ℚ) := by
  -- (`φ` is `Nat.totient`'s notation under `open Nat`, so the profile value is never abbreviated.)
  have hpp := prime_of_mem_phiWindow hp
  have hcast : ((coeff n r * mterm n r m : ℤ) : ℚ)
      = ((coeff n r : ℤ) : ℚ)
        * ((((-1 : ℤ) ^ m : ℤ) : ℚ) * (((D (16 * n) / (m + 1) : ℕ)) : ℚ)
            * ((((11 * n).choose (r - m) : ℕ)) : ℚ)) := by
    rw [mterm]
    -- NOT `push_cast`: `Int.natCast_div` would push the cast through `D (16n) / (m+1)` on one
    -- side only.  The cast set closes the goal by itself (a trailing `ring` reads "No goals").
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  rw [hcast]
  have hsign : PVal p 0 ((((-1 : ℤ) ^ m : ℤ) : ℚ)) := pval_intCast hpp _
  by_cases hd : p ∣ m + 1
  · -- POLAR `m`
    by_cases hb : (r + 1) % p ≤ (11 * n) % p
    · -- `b_r = 1`: the coefficient alone carries `φ̃`
      have hb1 : bbit n p r = 1 := by simp [bbit, hb]
      rw [hb1] at hc
      have h := pval_mul hpp hc (pval_mul hpp (pval_mul hpp hsign
        (pval_natCast hpp (D (16 * n) / (m + 1)))) (pval_natCast hpp ((11 * n).choose (r - m))))
      exact pval_mono (by omega) h
    · -- `b_r = 0`: `C(11n, r−m)` carries, or vanishes
      have hb0 : bbit n p r = 0 := by simp [bbit, hb]
      rw [hb0] at hc
      by_cases hj : r - m ≤ 11 * n
      · have hcarry : (11 * n) % p < (r - m) % p := by
          rw [sub_mod_eq_succ_mod hm hd]
          omega
        have h := pval_mul hpp hc (pval_mul hpp (pval_mul hpp hsign
          (pval_natCast hpp (D (16 * n) / (m + 1)))) (pval_choose_of_units hp hj hcarry))
        exact pval_mono (by omega) h
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        simpa using pval_zero hpp _
  · -- NON-POLAR `m`: `D(16n)/(m+1)` keeps one `p`
    have h := pval_mul hpp hc (pval_mul hpp (pval_mul hpp hsign
      (pval_D16_div hp (by omega) hd)) (pval_natCast hpp ((11 * n).choose (r - m))))
    exact pval_mono (by omega) h

/-- **The polynomial half at one cell, from the coefficient bound at that cell.** -/
theorem polyHalf_of_coeffBound {n p : ℕ} (hp : p ∈ phiWindow n)
    (h : ∀ r, r < 16 * n →
      PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r - 1) ((coeff n r : ℤ) : ℚ)) :
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))))
      (((Δ 16 15 n : ℕ) : ℚ) * (candidateM.Pin n * candidateM.pnPoly n)) := by
  have hpp := prime_of_mem_phiWindow hp
  rw [Delta_Pin_pnPoly_eq]
  refine pval_sum hpp _ _ fun r hr => pval_sum hpp _ _ fun m hm => ?_
  have hrlt := Finset.mem_range.mp hr
  have hmle : m ≤ r := by have := Finset.mem_range.mp hm; omega
  exact pval_term hp hrlt hmle (h r hrlt)

/-- **`PolyHalfOpen` FROM THE COEFFICIENT BOUND.**  Read the type: the hypothesis is the whole
remaining content of the polynomial half, one valuation per `(n, p, r)`. -/
theorem polyHalfOpen_of_coeffBound (h : CoeffBoundOpen) : PolyHalfOpen :=
  fun n p hp => polyHalf_of_coeffBound hp (fun r hr => h n p r hp hr)

/-! ## 5. Pins — the accounting's three cases are each REACHED -/

/-- `b_r` is not constant: at `n = 3, p = 13` (`11n % 13 = 7`) it is `1` at `r = 6` and `0` at
`r = 7`. -/
theorem bbit_3_13_6 : bbit 3 13 6 = 1 := by decide
theorem bbit_3_13_7 : bbit 3 13 7 = 0 := by decide

/-- The complement in `pval_term`'s polar case is exact: `(11n) % p < (r+1) % p ↔ b_r = 0`. -/
theorem bbit_eq_zero_iff (n p r : ℕ) : bbit n p r = 0 ↔ (11 * n) % p < (r + 1) % p := by
  rw [bbit]
  split <;> omega

#print axioms Zeta2PtpPoly.coeff_spec
#check @Zeta2PtpPoly.coeff_spec
#print axioms Zeta2PtpPoly.D16_mul_Lf_nbp
#check @Zeta2PtpPoly.D16_mul_Lf_nbp
#print axioms Zeta2PtpPoly.Delta_Pin_pnPoly_eq
#check @Zeta2PtpPoly.Delta_Pin_pnPoly_eq
#print axioms Zeta2PtpPoly.pval_D16_div
#check @Zeta2PtpPoly.pval_D16_div
#print axioms Zeta2PtpPoly.pval_choose_of_units
#check @Zeta2PtpPoly.pval_choose_of_units
#print axioms Zeta2PtpPoly.sub_mod_eq_succ_mod
#check @Zeta2PtpPoly.sub_mod_eq_succ_mod
#print axioms Zeta2PtpPoly.pval_term
#check @Zeta2PtpPoly.pval_term
#print axioms Zeta2PtpPoly.polyHalf_of_coeffBound
#check @Zeta2PtpPoly.polyHalf_of_coeffBound
#print axioms Zeta2PtpPoly.polyHalfOpen_of_coeffBound
#check @Zeta2PtpPoly.polyHalfOpen_of_coeffBound
#print axioms Zeta2PtpPoly.bbit_3_13_6
#print axioms Zeta2PtpPoly.bbit_3_13_7
#print axioms Zeta2PtpPoly.bbit_eq_zero_iff
#check @Zeta2PtpPoly.bbit_eq_zero_iff

end Zeta2PtpPoly
