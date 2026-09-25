/-
# Row PT-P, layer 10 — `CoeffBoundOpen` REDUCED to a units-carry count on the terms of `h_m`,
# with the rows that count cannot reach named as one residual `Prop`

`Zeta2PtpPoly` left the polynomial half on `CoeffBoundOpen`: `PVal p (φ̃ + b_r − 1) (coeff n r)` at
every window cell and `r < 16n`, `coeff n r = D(15n)·h_{L+r} / (L·C(L+r, L))`.  `Zeta2PtpCoeff`
wrote `h_m = Σ_{i≤m} (−1)^{m−i} C(m,i) H(i)` with `H(i)` a product of three ordinary binomials
below `13n` and above `26n`, and `ptp_kummer_rows_probe.py` measured the bound TERMWISE there:

    kum(m, i) := the four UNITS carry bits of `C(m,i)` and the three blocks         (`kumLo`/`kumHi`)
    φ̃ + b_r − 1 + v_p(L·C(m,L))  ≤  kum(m, i) + 1     for every i ≤ m         (K1, 95 998 of 95 998)

on every NON-polar row (`p ∤ r+1`, `m < p²`, `φ̃ + b_r ≥ 1`); the `+1` is the one `p` of `D(15n)`.

THIS FILE PROVES THE REDUCTION.  `pval_coeff_of_kum`: the termwise inequality at a row gives
`PVal p w (coeff n r)` there — each term of `h_m` is divisible by `p^{kum}` (a units carry bit is
a LOWER bound on `v_p` of a binomial, `Zeta2HatCarry.carry_bit_le_padicValNat_choose`, so this
needs no `m < p²`), hence `p^{w+e} ∣ p·h_m ∣ D(15n)·h_m = L·C(m,L)·coeff`, and `L·C(m,L) = p^e·u`
with `p ∤ u` cancels.  Then `coeffBoundOpen_of_rows : KummerRowsOpen → ResidualRowsOpen →
CoeffBoundOpen`, where

  * `KummerRowsOpen` is the termwise inequality above as a `Prop` — a RESIDUE statement in
    `(n, r, i) mod p`, decided on the box, NOT proved here;
  * `ResidualRowsOpen` is the coefficient bound on the rows the count does not reach: `p ∣ r+1`
    (the polar rows, where the probe's 51 short rows all sit — 50 on the sibling's four run strata,
    cancelling blockwise by `AHalfOpen`'s own mechanism) or `p² ≤ m` (the one cell `n = 11,
    p = 17, r = 169`, where `C(m,L)` carries twice).  1119 of the 1170 residual rows of the box
    are in fact covered by the same units-bit count; the 51 are what the dispatch against the
    sibling's files owes.

WHAT IS NOT CLAIMED.  Neither `Prop` is proved; `CoeffBoundOpen`, `PolyHalfOpen` and PT-P stay
open and `Zeta2Target.zeta2_not_liouvilleWith` is `sorry`.  `#print axioms` on the two
compositions cannot see their binders (LEAN.md §1) — read the `#check @` types.

Falsifier: `falsify_ptpkummer.sh` / `out_ptpkummer_falsify.txt`.

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
import Zeta2PtpPoly
import Zeta2PtpCoeff
import Zeta2HatCarry

namespace Zeta2PtpKummer

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpPolar Zeta2PtpPoly Zeta2PtpCoeff Zeta2NewtonCarry
  Zeta2NewtonAssemble Zeta2PtpRun Nat Finset

/-! ## 1. A units carry bit is a lower bound on `v_p` of the binomial, unconditionally -/

/-- `cb p S A ≤ v_p(C(S, A))` for `A ≤ S` — Kummer's units digit, no `S < p²` needed. -/
theorem cb_le_padicValNat_choose {p : ℕ} [Fact p.Prime] {S A : ℕ} (h : A ≤ S) :
    cb p S A ≤ padicValNat p (S.choose A) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h1 := Zeta2HatCarry.carry_bit_le_padicValNat_choose p (S - A) A
  rw [show S - A + A = S by omega] at h1
  have hiff := carry_bit p (S - A) A hp0
  rw [show S - A + A = S by omega] at hiff
  by_cases hc : S % p < A % p
  · have h2 : p ≤ A % p + (S - A) % p := hiff.2 hc
    simp only [h2, ↓reduceIte] at h1
    simpa [cb, hc] using h1
  · simp [cb, hc]

theorem pow_cb_dvd_choose {p : ℕ} [Fact p.Prime] {S A : ℕ} (h : A ≤ S) :
    p ^ cb p S A ∣ S.choose A :=
  (pow_dvd_pow p (cb_le_padicValNat_choose h)).trans pow_padicValNat_dvd

/-! ## 2. `H(i)` above the second block's zeros, and the units count of a term -/

/-- **`H(i)` for `i > 26n`**: three ordinary binomials, no sign. -/
theorem Hfun_of_gt (n i : ℕ) (hi : 26 * n < i) :
    Hfun n i = (((i - 13 * n - 1).choose (13 * n) * (i - 15 * n - 1).choose (9 * n)
      * (i - 17 * n - 1).choose (5 * n) : ℕ) : ℤ) := by
  rw [Hfun, listProd_memberBlocks]
  have e1 : (i : ℤ) - (13 * (n : ℤ) + 1) = (((i - 13 * n - 1 : ℕ)) : ℤ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : (i : ℤ) - (15 * (n : ℤ) + 1) = (((i - 15 * n - 1 : ℕ)) : ℤ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : (i : ℤ) - (17 * (n : ℤ) + 1) = (((i - 17 * n - 1 : ℕ)) : ℤ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [e1, e2, e3, Ring.choose_natCast, Ring.choose_natCast, Ring.choose_natCast]
  push_cast
  ring

/-- The units count of the `i`-th term of `h_m` for `i ≤ 13n`. -/
def kumLo (n p m i : ℕ) : ℕ :=
  cb p m i + cb p (26 * n - i) (13 * n) + cb p (24 * n - i) (9 * n) + cb p (22 * n - i) (5 * n)

/-- The units count of the `i`-th term of `h_m` for `i > 26n`. -/
def kumHi (n p m i : ℕ) : ℕ :=
  cb p m i + cb p (i - 13 * n - 1) (13 * n) + cb p (i - 15 * n - 1) (9 * n)
    + cb p (i - 17 * n - 1) (5 * n)

theorem pow_kumLo_dvd_term {n p m i : ℕ} [Fact p.Prime] (hi : i ≤ 13 * n) (him : i ≤ m) :
    (p : ℤ) ^ kumLo n p m i ∣ (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * Hfun n i := by
  rw [Hfun_of_le n i hi]
  have h0 : p ^ cb p m i ∣ m.choose i := pow_cb_dvd_choose him
  have hA : p ^ cb p (26 * n - i) (13 * n) ∣ (26 * n - i).choose (13 * n) :=
    pow_cb_dvd_choose (by omega)
  have hB : p ^ cb p (24 * n - i) (9 * n) ∣ (24 * n - i).choose (9 * n) :=
    pow_cb_dvd_choose (by omega)
  have hC : p ^ cb p (22 * n - i) (5 * n) ∣ (22 * n - i).choose (5 * n) :=
    pow_cb_dvd_choose (by omega)
  have hd : p ^ kumLo n p m i
      ∣ m.choose i * ((26 * n - i).choose (13 * n) * (24 * n - i).choose (9 * n)
          * (22 * n - i).choose (5 * n)) := by
    refine (dvd_of_eq ?_).trans (mul_dvd_mul h0 (mul_dvd_mul (mul_dvd_mul hA hB) hC))
    simp only [kumLo]
    ring
  have hz : ((p ^ kumLo n p m i : ℕ) : ℤ)
      ∣ ((m.choose i * ((26 * n - i).choose (13 * n) * (24 * n - i).choose (9 * n)
          * (22 * n - i).choose (5 * n)) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hd
  push_cast at hz
  exact (Dvd.dvd.mul_left hz ((-1 : ℤ) ^ (m - i) * (-1 : ℤ) ^ (27 * n))).trans
    (dvd_of_eq (by push_cast; ring))

theorem pow_kumHi_dvd_term {n p m i : ℕ} [Fact p.Prime] (hi : 26 * n < i) (him : i ≤ m) :
    (p : ℤ) ^ kumHi n p m i ∣ (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * Hfun n i := by
  rw [Hfun_of_gt n i hi]
  have h0 : p ^ cb p m i ∣ m.choose i := pow_cb_dvd_choose him
  have hA : p ^ cb p (i - 13 * n - 1) (13 * n) ∣ (i - 13 * n - 1).choose (13 * n) :=
    pow_cb_dvd_choose (by omega)
  have hB : p ^ cb p (i - 15 * n - 1) (9 * n) ∣ (i - 15 * n - 1).choose (9 * n) :=
    pow_cb_dvd_choose (by omega)
  have hC : p ^ cb p (i - 17 * n - 1) (5 * n) ∣ (i - 17 * n - 1).choose (5 * n) :=
    pow_cb_dvd_choose (by omega)
  have hd : p ^ kumHi n p m i
      ∣ m.choose i * ((i - 13 * n - 1).choose (13 * n) * (i - 15 * n - 1).choose (9 * n)
          * (i - 17 * n - 1).choose (5 * n)) := by
    refine (dvd_of_eq ?_).trans (mul_dvd_mul h0 (mul_dvd_mul (mul_dvd_mul hA hB) hC))
    simp only [kumHi]
    ring
  have hz : ((p ^ kumHi n p m i : ℕ) : ℤ)
      ∣ ((m.choose i * ((i - 13 * n - 1).choose (13 * n) * (i - 15 * n - 1).choose (9 * n)
          * (i - 17 * n - 1).choose (5 * n)) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hd
  push_cast at hz
  exact (Dvd.dvd.mul_left hz ((-1 : ℤ) ^ (m - i))).trans (dvd_of_eq (by push_cast; ring))

/-- **Termwise divisibility of `h_m`**: a floor under every term's units count is a divisor. -/
theorem pow_dvd_hc {n p m v : ℕ} [Fact p.Prime]
    (hlo : ∀ i, i ≤ m → i ≤ 13 * n → v ≤ kumLo n p m i)
    (hhi : ∀ i, i ≤ m → 26 * n < i → v ≤ kumHi n p m i) :
    (p : ℤ) ^ v ∣ hc n m := by
  rw [hc_eq_signed_sum]
  refine Finset.dvd_sum fun i hi => ?_
  have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
  by_cases h1 : i ≤ 13 * n
  · exact (pow_dvd_pow _ (hlo i him h1)).trans (pow_kumLo_dvd_term h1 him)
  · by_cases h2 : 26 * n < i
    · exact (pow_dvd_pow _ (hhi i him h2)).trans (pow_kumHi_dvd_term h2 him)
    · rw [Hfun_eq_zero n i (by omega) (by omega), mul_zero]
      exact dvd_zero _

/-! ## 3. The reduction: from the termwise count to `coeff` -/

/-- `L·C(m,L)` as a natural, the divisor `coeff` clears. -/
def LC (n r : ℕ) : ℕ := (11 * n + 1) * ((11 * n + 1 + r).choose (11 * n + 1))

theorem LC_ne_zero' (n r : ℕ) : LC n r ≠ 0 := by
  have := Nat.choose_pos (show 11 * n + 1 ≤ 11 * n + 1 + r by omega)
  unfold LC
  positivity

/-- **THE REDUCTION.**  At a window cell, if every term of `h_{L+r}` carries
`w + v_p(L·C(L+r,L)) − 1` units bits, then `coeff n r` carries `p^w`.  The `+1` is `p ∣ D(15n)`. -/
theorem pval_coeff_of_kum {n p r w : ℕ} (hp : p ∈ phiWindow n)
    (hlo : ∀ i, i ≤ 11 * n + 1 + r → i ≤ 13 * n →
      w + padicValNat p (LC n r) ≤ kumLo n p (11 * n + 1 + r) i + 1)
    (hhi : ∀ i, i ≤ 11 * n + 1 + r → 26 * n < i →
      w + padicValNat p (LC n r) ≤ kumHi n p (11 * n + 1 + r) i + 1) :
    PVal p w ((coeff n r : ℤ) : ℚ) := by
  have hpp := prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hle := Zeta2PhiTDvd.le_of_mem_phiWindow hp
  -- `L·C(m,L) = p^e · u` with `p ∤ u`, and `e` IS `padicValNat p (LC n r)`.
  obtain ⟨e, u, hu, hLC⟩ := Nat.exists_eq_pow_mul_and_not_dvd (LC_ne_zero' n r) p hpp.ne_one
  have hu0 : u ≠ 0 := by rintro rfl; simp at hLC; exact LC_ne_zero' n r hLC
  have he : padicValNat p (LC n r) = e := by
    rw [hLC, padicValNat.mul (pow_ne_zero _ hpp.ne_zero) hu0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hu, add_zero]
  rw [he] at hlo hhi
  -- `p^{w+e} ∣ p · h_m`: every term carries `p^{kum}` and `kum + 1 ≥ w + e`.
  have h1 : (p : ℤ) ^ (w + e) ∣ (p : ℤ) * hc n (11 * n + 1 + r) := by
    rw [hc_eq_signed_sum, Finset.mul_sum]
    refine Finset.dvd_sum fun i hi => ?_
    have him : i ≤ 11 * n + 1 + r := by have := Finset.mem_range.mp hi; omega
    by_cases hl : i ≤ 13 * n
    · refine (pow_dvd_pow _ (hlo i him hl)).trans ?_
      rw [pow_succ, mul_comm]
      exact mul_dvd_mul_left _ (pow_kumLo_dvd_term hl him)
    · by_cases hh : 26 * n < i
      · refine (pow_dvd_pow _ (hhi i him hh)).trans ?_
        rw [pow_succ, mul_comm]
        exact mul_dvd_mul_left _ (pow_kumHi_dvd_term hh him)
      · rw [Hfun_eq_zero n i (by omega) (by omega), mul_zero, mul_zero]
        exact dvd_zero _
  -- `p ∣ D(15n)`, so `p^{w+e} ∣ D(15n)·h_m = L·C(m,L)·coeff`.
  obtain ⟨q, hq⟩ := dvd_D hpp.pos hle
  have h2 : (p : ℤ) ^ (w + e) ∣ ((LC n r : ℕ) : ℤ) * coeff n r := by
    have hspec := coeff_spec n r
    rw [show (((11 * n + 1) * ((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℤ)
        = ((LC n r : ℕ) : ℤ) from rfl] at hspec
    rw [hspec, hq]
    push_cast
    rw [show ((p : ℤ) * (q : ℤ)) * hc n (11 * n + 1 + r)
        = (q : ℤ) * ((p : ℤ) * hc n (11 * n + 1 + r)) by ring]
    exact Dvd.dvd.mul_left h1 _
  -- cancel `p^e` and the unit `u`.
  rw [hLC] at h2
  push_cast at h2
  rw [pow_add, mul_comm ((p : ℤ) ^ w), mul_assoc] at h2
  have h3 : (p : ℤ) ^ w ∣ (u : ℤ) * coeff n r :=
    (mul_dvd_mul_iff_left (pow_ne_zero e (Nat.cast_ne_zero.mpr hpp.ne_zero))).mp h2
  have hcop : IsCoprime ((p : ℤ) ^ w) ((u : ℤ)) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hu)).pow_left
  exact pval_of_pow_dvd hpp (hcop.dvd_of_dvd_mul_left h3)

/-! ## 4. The two named `Prop`s, and `CoeffBoundOpen` from them -/

/-- **THE TERMWISE RESIDUE LEMMA, open.**  On every non-polar row with `m < p²` and a positive
target, every term of `h_m` carries `φ̃ + b_r − 1 + v_p(L·C(m,L))` units bits, less the one `p`
of `D(15n)`.  A statement about `(n, r, i) mod p`; measured at 95 998 of 95 998 rows
(`ptp_kummer_rows_probe.out`, arm K1); NOT proved. -/
def KummerRowsOpen : Prop :=
  ∀ n p r : ℕ, p ∈ phiWindow n → r < 16 * n → ¬ p ∣ r + 1 → 11 * n + 1 + r < p ^ 2 →
    1 ≤ phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r →
    (∀ i, i ≤ 11 * n + 1 + r → i ≤ 13 * n →
      phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r - 1 + padicValNat p (LC n r)
        ≤ kumLo n p (11 * n + 1 + r) i + 1) ∧
    (∀ i, i ≤ 11 * n + 1 + r → 26 * n < i →
      phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r - 1 + padicValNat p (LC n r)
        ≤ kumHi n p (11 * n + 1 + r) i + 1)

/-- **THE RESIDUAL ROWS, open.**  The coefficient bound itself on the rows the units count does
not reach: the POLAR rows `p ∣ r+1` (the probe's 51 short rows all sit here, 50 on the four run
strata `[1/9,2/17)`, `[3/13,4/17)`, `[6/13,7/15)`, `[5/9,9/16)` where they cancel blockwise by
`AHalfOpen`'s own mechanism) and the rows with `p² ≤ m` (one cell in the box, `n = 11, p = 17,
r = 169`).  Measured (arm K3); NOT proved. -/
def ResidualRowsOpen : Prop :=
  ∀ n p r : ℕ, p ∈ phiWindow n → r < 16 * n → (p ∣ r + 1 ∨ p ^ 2 ≤ 11 * n + 1 + r) →
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r - 1) ((coeff n r : ℤ) : ℚ)

/-- **`CoeffBoundOpen` FROM THE TWO.**  Read the type: it names both binders. -/
theorem coeffBoundOpen_of_rows (hk : KummerRowsOpen) (hres : ResidualRowsOpen) :
    CoeffBoundOpen := by
  intro n p r hp hr
  have hpp := prime_of_mem_phiWindow hp
  by_cases hpol : p ∣ r + 1
  · exact hres n p r hp hr (Or.inl hpol)
  by_cases hsq : p ^ 2 ≤ 11 * n + 1 + r
  · exact hres n p r hp hr (Or.inr hsq)
  by_cases hz : 1 ≤ phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r
  · obtain ⟨hlo, hhi⟩ := hk n p r hp hr hpol (by omega) hz
    exact pval_coeff_of_kum hp hlo hhi
  · have h0 : phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r - 1 = 0 := by omega
    rw [h0]
    exact pval_intCast hpp _

/-- **`PolyHalfOpen` FROM THE TWO**, through `Zeta2PtpPoly.polyHalfOpen_of_coeffBound`. -/
theorem polyHalfOpen_of_rows (hk : KummerRowsOpen) (hres : ResidualRowsOpen) : PolyHalfOpen :=
  polyHalfOpen_of_coeffBound (coeffBoundOpen_of_rows hk hres)

/-! ## 5. Pins -/

/-- The units count is REACHED: at `n = 1, p = 7, r = 2` (`m = 14`) the smallest term count is
`2` and `L·C(14,12) = 1092 = 7 · 156` with `7 ∤ 156`, so the reduction gives exactly `PVal 7 2`
there, which is the row's target (`φ̃ = 2`, `b_r = 1`) — the `+1` of `D(15n)` has no slack. -/
theorem kumLo_1_7_14_min : (Finset.range 14).inf' ⟨0, by simp⟩ (fun i => kumLo 1 7 14 i) = 2 := by
  decide
theorem LC_1_2_pin : LC 1 2 = 1092 ∧ 7 ∣ 1092 ∧ ¬ 49 ∣ 1092 := by decide

#print axioms Zeta2PtpKummer.cb_le_padicValNat_choose
#check @Zeta2PtpKummer.cb_le_padicValNat_choose
#print axioms Zeta2PtpKummer.Hfun_of_gt
#check @Zeta2PtpKummer.Hfun_of_gt
#print axioms Zeta2PtpKummer.pow_kumLo_dvd_term
#check @Zeta2PtpKummer.pow_kumLo_dvd_term
#print axioms Zeta2PtpKummer.pow_kumHi_dvd_term
#check @Zeta2PtpKummer.pow_kumHi_dvd_term
#print axioms Zeta2PtpKummer.pow_dvd_hc
#check @Zeta2PtpKummer.pow_dvd_hc
#print axioms Zeta2PtpKummer.pval_coeff_of_kum
#check @Zeta2PtpKummer.pval_coeff_of_kum
#print axioms Zeta2PtpKummer.coeffBoundOpen_of_rows
#check @Zeta2PtpKummer.coeffBoundOpen_of_rows
#print axioms Zeta2PtpKummer.polyHalfOpen_of_rows
#check @Zeta2PtpKummer.polyHalfOpen_of_rows
#check @Zeta2PtpKummer.KummerRowsOpen
#print Zeta2PtpKummer.KummerRowsOpen
#check @Zeta2PtpKummer.ResidualRowsOpen
#print Zeta2PtpKummer.ResidualRowsOpen
#print axioms Zeta2PtpKummer.kumLo_1_7_14_min
#print axioms Zeta2PtpKummer.LC_1_2_pin

end Zeta2PtpKummer
