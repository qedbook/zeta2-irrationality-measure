/-
# Row PT-P, layer 15 — `h_m` IN `p`-BLOCKS OF ITS INDEX: the generic φ̃ = 1 block lemma for the
# polar rows below `p²`, for both halves of the sum (LO `i ≤ 13n`, TAIL `i > 26n`)

`Zeta2PtpResPair` left `ResidualRunOpen`: the polar rows (`p ∣ r+1`) whose residue `n % p` lies on
one of the five run strata.  At `m = 11n + 1 + r < p²` every term of
`h_m = Σ_i (−1)^{m−i} C(m,i) H(i)` is a product of four ordinary binomials with ONE units digit
each, and `ptp_resid_narrow_probe.out` (arms S1–S3) measured the cancellation: the LO part and —
once `m > 26n` — the TAIL part vanish separately, and block by block in `i = t·p + u`.

THIS FILE IS THE STRATUM-FREE PART, in the harmonic side's shape (`Zeta2PtpBlock`, `Zeta2PtpS7`)
but in `i`-blocks, where `C(m, i)`'s Lucas split is clean — `C(m mod p, u)·C(⌊m/p⌋, t)` — and
Wilson's reflection makes `(−1)^u C(m mod p, u)` a polynomial of degree `p − 1 − (m mod p)`:

* `Tlo`, `Thi`: the two halves' summands extended to all `i` by ℕ-subtraction (they vanish where
  the other lives, and both vanish in the gap `13n < i ≤ 26n` — `term_eq_lo_add_hi`);
* `Plo`, `Phi`: the block polynomials, the reflected `C(m mod p, u)` times the three units digits
  as `binPoly`s of `c − u` (LO) or `u − c` (TAIL), degree `(p−1−m₀) + (13n)₀ + (9n)₀ + (5n)₀`;
* `SuppLo`, `SuppHi`: the units support — no units carry in any of the four binomials — stated in
  residues, so a stratum discharges it by `omega`;
* **`lo_block_dvd` / `hi_block_dvd`**: if the degree is `≤ p − 2` and on the support the block has
  no truncation and FIXED high digits, then `p ∣ Σ_{u<p} term(t·p + u)`.  Off the support BOTH
  `term` and the polynomial vanish (one units binomial is `0`; a truncated top is `C(0, B) = 0`),
  so the identity `term ≡ κ_t · P(u)` holds at every `u` and the period sum does the rest;
* `hc_eq_blocks` / `pow_dvd_hc_of_blocks`: `h_m` as the two halves' blocks, and `p^v ∣ h_m` from
  the blocks.

WHAT IS NOT HERE.  No stratum (`Zeta2PtpRunS7` is the φ̃ = 1 one); no φ̃ = 2 block lemma (the four
φ̃ = 2 strata need `term/p`, Anton and a quotient, as `Zeta2PtpS2Kit` does for the harmonic side);
nothing at `m ≥ p²`.  Row PT-P does not close and `Zeta2Target.zeta2_not_liouvilleWith` is `sorry`.

Runner: `run_resid.sh`.  Falsifier: `falsify_ptprunlo.sh` / `out_ptprunlo_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2Profile
import Zeta2PhiT
import Zeta2PtpPolar
import Zeta2PtpRun
import Zeta2PtpStratum
import Zeta2PtpCong
import Zeta2PtpBlock
import Zeta2PtpS7
import Zeta2NewtonCarry
import Zeta2NewtonAssemble
import Zeta2PtpCoeff
import Zeta2PtpPoly
import Zeta2PtpKummer

set_option maxRecDepth 20000

namespace Zeta2PtpRunBlock

open Zeta2PtpBlock Zeta2PtpS7 Zeta2NewtonAssemble Zeta2PtpCoeff Finset Polynomial

/-! ## 1. The block identity and the block lemma, LO and TAIL -/

section Block
variable {p : ℕ} [hp : Fact p.Prime]

/-- The LO summand of `h_m` (sign `(−1)^{m+i}`, the `(−1)^{27n}` of `H` dropped), extended to every
natural `i` by ℕ-subtraction: `0` for `i > 13n` and for `i > m`. -/
def Tlo (n m i : ℕ) : ℤ :=
  (-1 : ℤ) ^ (m + i) * ((m.choose i : ℕ) : ℤ)
    * ((((26 * n - i).choose (13 * n)) * ((24 * n - i).choose (9 * n))
        * ((22 * n - i).choose (5 * n)) : ℕ) : ℤ)

/-- The LO block polynomial: Wilson's reflection of `C(m mod p, u)` and the three units digits. -/
noncomputable def Plo (p n m : ℕ) : (ZMod p)[X] :=
  signChoosePoly p (m % p)
    * (binPoly p ((13 * n) % p)).comp (C ((26 * n : ℕ) : ZMod p) - X)
    * (binPoly p ((9 * n) % p)).comp (C ((24 * n : ℕ) : ZMod p) - X)
    * (binPoly p ((5 * n) % p)).comp (C ((22 * n : ℕ) : ZMod p) - X)

/-- The LO units support at residue `u`: no units carry in any of the four binomials. -/
def SuppLo (p n m u : ℕ) : Prop :=
  u ≤ m % p ∧ (13 * n) % p ≤ ((26 * n) % p + p - u) % p
    ∧ (9 * n) % p ≤ ((24 * n) % p + p - u) % p ∧ (5 * n) % p ≤ ((22 * n) % p + p - u) % p

theorem natDegree_comp_sub_le (j : ℕ) (c : ZMod p) :
    ((binPoly p j).comp (C c - X)).natDegree ≤ j := by
  refine natDegree_comp_le.trans ?_
  have h1 : (C c - X : (ZMod p)[X]).natDegree ≤ 1 := by
    have : (C c - X : (ZMod p)[X]) = -(X - C c) := by ring
    rw [this, natDegree_neg, natDegree_X_sub_C]
  calc (binPoly p j).natDegree * (C c - X : (ZMod p)[X]).natDegree
      ≤ j * 1 := Nat.mul_le_mul (binPoly_natDegree_le j) h1
    _ = j := Nat.mul_one j

theorem Plo_natDegree_le (n m : ℕ) :
    (Plo p n m).natDegree
      ≤ (p - 1 - m % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p := by
  unfold Plo
  exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le (signChoosePoly_natDegree_le _)
      (natDegree_comp_sub_le _ _)) (natDegree_comp_sub_le _ _)) (natDegree_comp_sub_le _ _)

/-- `(c − (tp+u) : ZMod p) = c − u` when there is no truncation. -/
theorem cast_sub_block {c t u : ℕ} (h : t * p + u ≤ c) :
    ((c - (t * p + u) : ℕ) : ZMod p) = (c : ZMod p) - (u : ZMod p) := by
  rw [Nat.cast_sub h]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- The wrapped residue `(c mod p + p − u) mod p` is `c − u` in `ZMod p`. -/
theorem cast_wrap (c u : ℕ) (hu : u ≤ p) :
    ((((c % p) + p - u) % p : ℕ) : ZMod p) = (c : ZMod p) - (u : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega)]
  push_cast
  rw [ZMod.natCast_self, ZMod.natCast_mod]
  ring

/-- `binPoly j` at `c − u` IS `C((c mod p + p − u) mod p, j)`. -/
theorem binPoly_eval_wrap (c u j : ℕ) (hu : u ≤ p) (hj : j < p) :
    (binPoly p j).eval ((c : ZMod p) - (u : ZMod p))
      = (((((c % p) + p - u) % p).choose j : ℕ) : ZMod p) := by
  rw [← cast_wrap c u hu, choose_cast_eq_binPoly _ _ hj]

theorem sign_block (hp2 : 2 < p) (m t u : ℕ) :
    (-1 : ZMod p) ^ (m + (t * p + u)) = (-1) ^ (m + t) * (-1) ^ u := by
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  rw [pow_add, pow_add, pow_add, pow_mul' (-1 : ZMod p) t p, hodd.neg_one_pow]
  ring

/-- **The LO block identity.**  If on the units support the block has no truncation and fixed
high digits `h₁, h₂, h₃`, then EVERY term of the block is `κ · Plo(u)` mod `p`. -/
theorem Tlo_cast_eq (hp2 : 2 < p) {n m t u h1 h2 h3 : ℕ} (hn : 1 ≤ n) (hu : u < p)
    (hsup : SuppLo p n m u → t * p + u ≤ 22 * n ∧ (26 * n - (t * p + u)) / p = h1
      ∧ (24 * n - (t * p + u)) / p = h2 ∧ (22 * n - (t * p + u)) / p = h3) :
    ((Tlo n m (t * p + u) : ℤ) : ZMod p)
      = ((-1) ^ (m + t) * (((m / p).choose t : ℕ) : ZMod p)
          * ((h1.choose (13 * n / p) : ℕ) : ZMod p) * ((h2.choose (9 * n / p) : ℕ) : ZMod p)
          * ((h3.choose (5 * n / p) : ℕ) : ZMod p))
        * (Plo p n m).eval (u : ZMod p) := by
  have hp0 := hp.out.pos
  have hdiv : (t * p + u) / p = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hu, zero_add]
  have hmod : (t * p + u) % p = u := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  have hm0 : m % p < p := Nat.mod_lt _ hp0
  have hj13 := Nat.mod_lt (13 * n) hp0
  have hj9 := Nat.mod_lt (9 * n) hp0
  have hj5 := Nat.mod_lt (5 * n) hp0
  unfold Tlo Plo
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X]
  rw [binPoly_eval_wrap _ _ _ hu.le hj13, binPoly_eval_wrap _ _ _ hu.le hj9,
    binPoly_eval_wrap _ _ _ hu.le hj5, ← signChoose_eq (m % p) u hm0 hu]
  push_cast
  rw [sign_block hp2, lucas_raw m (t * p + u), hdiv, hmod]
  by_cases hs : SuppLo p n m u
  · obtain ⟨htr, e1, e2, e3⟩ := hsup hs
    rw [lucas_factor (26 * n - (t * p + u)) (13 * n), lucas_factor (24 * n - (t * p + u)) (9 * n),
      lucas_factor (22 * n - (t * p + u)) (5 * n), e1, e2, e3,
      cast_sub_block (by omega), cast_sub_block (by omega), cast_sub_block (by omega),
      binPoly_eval_wrap _ _ _ hu.le hj13, binPoly_eval_wrap _ _ _ hu.le hj9,
      binPoly_eval_wrap _ _ _ hu.le hj5]
    ring
  · -- off the support both sides vanish: one of the four units binomials is `0`
    unfold SuppLo at hs
    -- a carried H factor is `0` mod `p` on the left (Lucas, or exactly `0` when truncated)
    have hL : ∀ (c B : ℕ), 0 < B → ((c % p) + p - u) % p < B % p →
        (((c - (t * p + u)).choose B : ℕ) : ZMod p) = 0 := by
      intro c B hB hlt
      by_cases hc : t * p + u ≤ c
      · rw [lucas_factor, cast_sub_block hc, binPoly_eval_wrap _ _ _ hu.le (Nat.mod_lt _ hp0),
          Nat.choose_eq_zero_of_lt hlt]
        simp
      · rw [show c - (t * p + u) = 0 by omega, Nat.choose_eq_zero_of_lt hB]
        simp
    by_cases h0 : u ≤ m % p
    · have h' : ¬ ((13 * n) % p ≤ ((26 * n) % p + p - u) % p
          ∧ (9 * n) % p ≤ ((24 * n) % p + p - u) % p
          ∧ (5 * n) % p ≤ ((22 * n) % p + p - u) % p) := fun h => hs ⟨h0, h⟩
      rcases not_and_or.mp h' with h1' | h1'
      · have hl := hL (26 * n) (13 * n) (by omega) (by omega)
        have hr : ((((26 * n) % p + p - u) % p).choose ((13 * n) % p) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
        simp only [hl, hr, mul_zero, zero_mul]
      rcases not_and_or.mp h1' with h2' | h3'
      · have hl := hL (24 * n) (9 * n) (by omega) (by omega)
        have hr : ((((24 * n) % p + p - u) % p).choose ((9 * n) % p) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
        simp only [hl, hr, mul_zero, zero_mul]
      · have hl := hL (22 * n) (5 * n) (by omega) (by omega)
        have hr : ((((22 * n) % p + p - u) % p).choose ((5 * n) % p) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
        simp only [hl, hr, mul_zero]
    · have hr : (((m % p).choose u : ℕ) : ZMod p) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      simp only [hr, mul_zero, zero_mul]

/-- **THE LO BLOCK LEMMA.**  Degree at most `p − 2` and a support with fixed high digits give
`p ∣ Σ_{u<p} Tlo(tp + u)`. -/
theorem lo_block_dvd (hp2 : 2 < p) {n m t h1 h2 h3 : ℕ} (hn : 1 ≤ n)
    (hdeg : (p - 1 - m % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2)
    (hsup : ∀ u < p, SuppLo p n m u → t * p + u ≤ 22 * n ∧ (26 * n - (t * p + u)) / p = h1
      ∧ (24 * n - (t * p + u)) / p = h2 ∧ (22 * n - (t * p + u)) / p = h3) :
    (p : ℤ) ∣ ∑ u ∈ range p, Tlo n m (t * p + u) :=
  dvd_sum_of_poly _ _ (Plo p n m) ((Plo_natDegree_le n m).trans hdeg)
    fun u hu => Tlo_cast_eq hp2 hn hu (hsup u hu)

/-! ### The TAIL (`i > 26n`): the same lemma with the three tops rising -/

/-- The TAIL summand of `h_m`, extended by ℕ-subtraction: `0` for `i ≤ 26n` and for `i > m`. -/
def Thi (n m i : ℕ) : ℤ :=
  (-1 : ℤ) ^ (m + i) * ((m.choose i : ℕ) : ℤ)
    * ((((i - 13 * n - 1).choose (13 * n)) * ((i - 15 * n - 1).choose (9 * n))
        * ((i - 17 * n - 1).choose (5 * n)) : ℕ) : ℤ)

noncomputable def Phi (p n m : ℕ) : (ZMod p)[X] :=
  signChoosePoly p (m % p)
    * (binPoly p ((13 * n) % p)).comp (X - C ((13 * n + 1 : ℕ) : ZMod p))
    * (binPoly p ((9 * n) % p)).comp (X - C ((15 * n + 1 : ℕ) : ZMod p))
    * (binPoly p ((5 * n) % p)).comp (X - C ((17 * n + 1 : ℕ) : ZMod p))

def SuppHi (p n m u : ℕ) : Prop :=
  u ≤ m % p ∧ (13 * n) % p ≤ (u + p - (13 * n + 1) % p) % p
    ∧ (9 * n) % p ≤ (u + p - (15 * n + 1) % p) % p ∧ (5 * n) % p ≤ (u + p - (17 * n + 1) % p) % p

theorem natDegree_comp_X_sub_le (j : ℕ) (c : ZMod p) :
    ((binPoly p j).comp (X - C c)).natDegree ≤ j := by
  refine natDegree_comp_le.trans ?_
  rw [natDegree_X_sub_C, mul_one]
  exact binPoly_natDegree_le j

theorem Phi_natDegree_le (n m : ℕ) :
    (Phi p n m).natDegree
      ≤ (p - 1 - m % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p := by
  unfold Phi
  exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le (signChoosePoly_natDegree_le _)
      (natDegree_comp_X_sub_le _ _)) (natDegree_comp_X_sub_le _ _)) (natDegree_comp_X_sub_le _ _)

theorem cast_block_sub {c t u : ℕ} (h : c ≤ t * p + u) :
    ((t * p + u - c : ℕ) : ZMod p) = (u : ZMod p) - (c : ZMod p) := by
  rw [Nat.cast_sub h]
  push_cast
  rw [ZMod.natCast_self]
  ring

theorem cast_wrap' (c u : ℕ) :
    (((u + p - c % p) % p : ℕ) : ZMod p) = (u : ZMod p) - (c : ZMod p) := by
  have hp0 := hp.out.pos
  rw [ZMod.natCast_mod, Nat.cast_sub (by have := Nat.mod_lt c hp0; omega)]
  push_cast
  rw [ZMod.natCast_self, ZMod.natCast_mod]
  ring

theorem binPoly_eval_wrap' (c u j : ℕ) (hj : j < p) :
    (binPoly p j).eval ((u : ZMod p) - (c : ZMod p))
      = ((((u + p - c % p) % p).choose j : ℕ) : ZMod p) := by
  rw [← cast_wrap' c u, choose_cast_eq_binPoly _ _ hj]

theorem Thi_cast_eq (hp2 : 2 < p) {n m t u h1 h2 h3 : ℕ} (hn : 1 ≤ n) (hu : u < p)
    (hsup : SuppHi p n m u → 17 * n + 1 ≤ t * p + u ∧ (t * p + u - 13 * n - 1) / p = h1
      ∧ (t * p + u - 15 * n - 1) / p = h2 ∧ (t * p + u - 17 * n - 1) / p = h3) :
    ((Thi n m (t * p + u) : ℤ) : ZMod p)
      = ((-1) ^ (m + t) * (((m / p).choose t : ℕ) : ZMod p)
          * ((h1.choose (13 * n / p) : ℕ) : ZMod p) * ((h2.choose (9 * n / p) : ℕ) : ZMod p)
          * ((h3.choose (5 * n / p) : ℕ) : ZMod p))
        * (Phi p n m).eval (u : ZMod p) := by
  have hp0 := hp.out.pos
  have hdiv : (t * p + u) / p = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hu, zero_add]
  have hmod : (t * p + u) % p = u := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  have hm0 : m % p < p := Nat.mod_lt _ hp0
  have hj13 := Nat.mod_lt (13 * n) hp0
  have hj9 := Nat.mod_lt (9 * n) hp0
  have hj5 := Nat.mod_lt (5 * n) hp0
  have e1 : ∀ c, t * p + u - c * n - 1 = t * p + u - (c * n + 1) := fun c => by omega
  unfold Thi Phi
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X]
  rw [binPoly_eval_wrap' _ _ _ hj13, binPoly_eval_wrap' _ _ _ hj9,
    binPoly_eval_wrap' _ _ _ hj5, ← signChoose_eq (m % p) u hm0 hu]
  push_cast
  rw [sign_block hp2, lucas_raw m (t * p + u), hdiv, hmod, e1 13, e1 15, e1 17]
  by_cases hs : SuppHi p n m u
  · obtain ⟨htr, f1, f2, f3⟩ := hsup hs
    rw [e1 13] at f1
    rw [e1 15] at f2
    rw [e1 17] at f3
    rw [lucas_factor (t * p + u - (13 * n + 1)) (13 * n),
      lucas_factor (t * p + u - (15 * n + 1)) (9 * n),
      lucas_factor (t * p + u - (17 * n + 1)) (5 * n), f1, f2, f3,
      cast_block_sub (by omega), cast_block_sub (by omega), cast_block_sub (by omega),
      binPoly_eval_wrap' _ _ _ hj13, binPoly_eval_wrap' _ _ _ hj9,
      binPoly_eval_wrap' _ _ _ hj5]
    ring
  · unfold SuppHi at hs
    have hL : ∀ (c B : ℕ), 0 < B → (u + p - c % p) % p < B % p →
        (((t * p + u - c).choose B : ℕ) : ZMod p) = 0 := by
      intro c B hB hlt
      by_cases hc : c ≤ t * p + u
      · rw [lucas_factor, cast_block_sub hc, binPoly_eval_wrap' _ _ _ (Nat.mod_lt _ hp0),
          Nat.choose_eq_zero_of_lt hlt]
        simp
      · rw [show t * p + u - c = 0 by omega, Nat.choose_eq_zero_of_lt hB]
        simp
    by_cases h0 : u ≤ m % p
    · have h' : ¬ ((13 * n) % p ≤ (u + p - (13 * n + 1) % p) % p
          ∧ (9 * n) % p ≤ (u + p - (15 * n + 1) % p) % p
          ∧ (5 * n) % p ≤ (u + p - (17 * n + 1) % p) % p) := fun h => hs ⟨h0, h⟩
      rcases not_and_or.mp h' with h1' | h1'
      · have hl := hL (13 * n + 1) (13 * n) (by omega) (by omega)
        have hr : (((u + p - (13 * n + 1) % p) % p).choose ((13 * n) % p) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
        simp only [hl, hr, mul_zero, zero_mul]
      rcases not_and_or.mp h1' with h2' | h3'
      · have hl := hL (15 * n + 1) (9 * n) (by omega) (by omega)
        have hr : (((u + p - (15 * n + 1) % p) % p).choose ((9 * n) % p) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
        simp only [hl, hr, mul_zero, zero_mul]
      · have hl := hL (17 * n + 1) (5 * n) (by omega) (by omega)
        have hr : (((u + p - (17 * n + 1) % p) % p).choose ((5 * n) % p) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
        simp only [hl, hr, mul_zero]
    · have hr : (((m % p).choose u : ℕ) : ZMod p) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      simp only [hr, mul_zero, zero_mul]

theorem hi_block_dvd (hp2 : 2 < p) {n m t h1 h2 h3 : ℕ} (hn : 1 ≤ n)
    (hdeg : (p - 1 - m % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2)
    (hsup : ∀ u < p, SuppHi p n m u → 17 * n + 1 ≤ t * p + u ∧ (t * p + u - 13 * n - 1) / p = h1
      ∧ (t * p + u - 15 * n - 1) / p = h2 ∧ (t * p + u - 17 * n - 1) / p = h3) :
    (p : ℤ) ∣ ∑ u ∈ range p, Thi n m (t * p + u) :=
  dvd_sum_of_poly _ _ (Phi p n m) ((Phi_natDegree_le n m).trans hdeg)
    fun u hu => Thi_cast_eq hp2 hn hu (hsup u hu)

end Block

/-! ## 2. The assembly: `h_m` as LO blocks plus TAIL blocks -/

/-- **Every term of `h_m` is the LO summand (with `H`'s sign) plus the TAIL summand** — each of the
two vanishes where the other lives, and both vanish in the gap `13n < i ≤ 26n`. -/
theorem term_eq_lo_add_hi (n m i : ℕ) (hn : 1 ≤ n) (him : i ≤ m) :
    (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * Hfun n i
      = (-1 : ℤ) ^ (27 * n) * Tlo n m i + Thi n m i := by
  have hs : (-1 : ℤ) ^ (m - i) = (-1) ^ (m + i) := by
    rw [show m + i = (m - i) + 2 * i by omega, pow_add, pow_mul]
    norm_num
  by_cases h1 : i ≤ 13 * n
  · rw [Hfun_of_le n i h1]
    have hz : Thi n m i = 0 := by
      unfold Thi
      rw [show i - 13 * n - 1 = 0 by omega, Nat.choose_eq_zero_of_lt (by omega : 0 < 13 * n)]
      simp
    rw [hz, add_zero, hs]
    unfold Tlo
    push_cast
    ring
  · by_cases h2 : i ≤ 26 * n
    · rw [Hfun_eq_zero n i (by omega) h2]
      have hz1 : Tlo n m i = 0 := by
        unfold Tlo
        rw [Nat.choose_eq_zero_of_lt (n := 26 * n - i) (by omega)]
        simp
      have hz2 : Thi n m i = 0 := by
        unfold Thi
        rw [Nat.choose_eq_zero_of_lt (n := i - 13 * n - 1) (by omega)]
        simp
      rw [hz1, hz2]
      simp
    · rw [Zeta2PtpKummer.Hfun_of_gt n i (by omega)]
      have hz1 : Tlo n m i = 0 := by
        unfold Tlo
        rw [show 26 * n - i = 0 by omega, Nat.choose_eq_zero_of_lt (by omega : 0 < 13 * n)]
        simp
      rw [hz1, mul_zero, zero_add, hs]
      unfold Thi
      push_cast
      ring

/-- A sum over `range (B·p)` in blocks of `p`. -/
theorem sum_range_blocks (f : ℕ → ℤ) (p : ℕ) :
    ∀ B, ∑ i ∈ range (B * p), f i = ∑ t ∈ range B, ∑ u ∈ range p, f (t * p + u)
  | 0 => by simp
  | B + 1 => by rw [Nat.succ_mul, sum_range_add, sum_range_blocks f p B, sum_range_succ]

theorem Tlo_eq_zero_of_gt {n m i : ℕ} (h : m < i) : Tlo n m i = 0 := by
  unfold Tlo; rw [Nat.choose_eq_zero_of_lt h]; simp

theorem Thi_eq_zero_of_gt {n m i : ℕ} (h : m < i) : Thi n m i = 0 := by
  unfold Thi; rw [Nat.choose_eq_zero_of_lt h]; simp

/-- **`h_m` in blocks**: `(−1)^{27n}·Σ_t LO-block_t + Σ_t TAIL-block_t`, `t < m/p + 1`. -/
theorem hc_eq_blocks {n m p : ℕ} (hp0 : 0 < p) (hn : 1 ≤ n) :
    hc n m = (-1 : ℤ) ^ (27 * n) * ∑ t ∈ range (m / p + 1), ∑ u ∈ range p, Tlo n m (t * p + u)
      + ∑ t ∈ range (m / p + 1), ∑ u ∈ range p, Thi n m (t * p + u) := by
  have hlt : m + 1 ≤ (m / p + 1) * p := by
    have := Nat.div_add_mod m p
    have := Nat.mod_lt m hp0
    have e : (m / p + 1) * p = p * (m / p) + p := by ring
    omega
  have hsub : range (m + 1) ⊆ range ((m / p + 1) * p) := range_mono hlt
  rw [hc_eq_signed_sum, ← sum_range_blocks, ← sum_range_blocks,
    ← sum_subset hsub (fun i _ hi => by rw [Tlo_eq_zero_of_gt (by simpa using hi)]),
    ← sum_subset hsub (fun i _ hi => by rw [Thi_eq_zero_of_gt (by simpa using hi)]),
    mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  exact term_eq_lo_add_hi n m i hn (Nat.lt_succ_iff.mp (mem_range.mp hi))

/-- **`p^v ∣ h_m` from its blocks.** -/
theorem pow_dvd_hc_of_blocks {n m p v : ℕ} (hp0 : 0 < p) (hn : 1 ≤ n)
    (hlo : ∀ t, t ≤ m / p → (p : ℤ) ^ v ∣ ∑ u ∈ range p, Tlo n m (t * p + u))
    (hhi : ∀ t, t ≤ m / p → (p : ℤ) ^ v ∣ ∑ u ∈ range p, Thi n m (t * p + u)) :
    (p : ℤ) ^ v ∣ hc n m := by
  rw [hc_eq_blocks hp0 hn]
  refine dvd_add (Dvd.dvd.mul_left (dvd_sum fun t ht => hlo t ?_) _)
    (dvd_sum fun t ht => hhi t ?_)
  · exact Nat.lt_succ_iff.mp (mem_range.mp ht)
  · exact Nat.lt_succ_iff.mp (mem_range.mp ht)

/-! ## 3. Residue helpers the strata share -/

theorem div_of_lin {p x q r : ℕ} (hp0 : 0 < p) (h : x = r + q * p) (hr : r < p) : x / p = q :=
  (digits_of_decomp hp0 h hr).1

theorem mod_of_lin {p x q r : ℕ} (hp0 : 0 < p) (h : x = r + q * p) (hr : r < p) : x % p = r :=
  (digits_of_decomp hp0 h hr).2

/-- `(u + p − R) % p` for `u, R < p`, as one comparison. -/
theorem wrap_mod_up {p u R : ℕ} (hu : u < p) (hR : R < p) :
    (u + p - R) % p = if R ≤ u then u - R else u + p - R := by
  split_ifs with h
  · rw [show u + p - R = (u - R) + p by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · exact Nat.mod_eq_of_lt (by omega)

/-- A LO summand past `13n` is `0`. -/
theorem Tlo_eq_zero_of_gt13 {n m i : ℕ} (hn : 1 ≤ n) (h : 13 * n < i) : Tlo n m i = 0 := by
  unfold Tlo
  rw [Nat.choose_eq_zero_of_lt (n := 26 * n - i) (by omega)]
  simp

/-- A TAIL summand at or below `26n` is `0`. -/
theorem Thi_eq_zero_of_le26 {n m i : ℕ} (hn : 1 ≤ n) (h : i ≤ 26 * n) : Thi n m i = 0 := by
  unfold Thi
  rw [Nat.choose_eq_zero_of_lt (n := i - 13 * n - 1) (by omega)]
  simp

/-! ## 4. Pins -/

/-- The LO support is REACHED and the block sum is `0 mod p` at the stratum's smallest cell:
`n = 3, p = 13, r = 12` (`m = 46`), block `t = 1`, where the support is `u ∈ [2, 6]`. -/
theorem lo_block_pin_3_13 : (13 : ℤ) ∣ ∑ u ∈ range 13, Tlo 3 46 (1 * 13 + u) := by decide

/-- ... and not `0 mod p²` there: the block cancels to exactly one place. -/
theorem lo_block_sharp_3_13 : ¬ (169 : ℤ) ∣ ∑ u ∈ range 13, Tlo 3 46 (1 * 13 + u) := by decide

end Zeta2PtpRunBlock

#print axioms Zeta2PtpRunBlock.Plo_natDegree_le
#print axioms Zeta2PtpRunBlock.Tlo_cast_eq
#check @Zeta2PtpRunBlock.Tlo_cast_eq
#print axioms Zeta2PtpRunBlock.lo_block_dvd
#check @Zeta2PtpRunBlock.lo_block_dvd
#print axioms Zeta2PtpRunBlock.Phi_natDegree_le
#print axioms Zeta2PtpRunBlock.Thi_cast_eq
#check @Zeta2PtpRunBlock.Thi_cast_eq
#print axioms Zeta2PtpRunBlock.hi_block_dvd
#check @Zeta2PtpRunBlock.hi_block_dvd
#print axioms Zeta2PtpRunBlock.term_eq_lo_add_hi
#check @Zeta2PtpRunBlock.term_eq_lo_add_hi
#print axioms Zeta2PtpRunBlock.sum_range_blocks
#print axioms Zeta2PtpRunBlock.hc_eq_blocks
#check @Zeta2PtpRunBlock.hc_eq_blocks
#print axioms Zeta2PtpRunBlock.pow_dvd_hc_of_blocks
#check @Zeta2PtpRunBlock.pow_dvd_hc_of_blocks
#print axioms Zeta2PtpRunBlock.wrap_mod_up
#print axioms Zeta2PtpRunBlock.Tlo_eq_zero_of_gt13
#print axioms Zeta2PtpRunBlock.Thi_eq_zero_of_le26
#print axioms Zeta2PtpRunBlock.lo_block_pin_3_13
#print axioms Zeta2PtpRunBlock.lo_block_sharp_3_13
