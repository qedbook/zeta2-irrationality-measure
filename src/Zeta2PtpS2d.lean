/-
# Row PT-P, layer 9d — the run congruence on the φ̃ = 2 run stratum `[12/13, 14/15)` (the dropped
# arc is `I4`), CONDITIONAL on Anton's one-carry congruence, and piece 25 `[10/11, 14/15)`
# discharged for the harmonic side under the same hypothesis

`Zeta2PtpS2c` is the template (`[6/13, 7/15)`, the other `I4` stratum); this file is that proof
at the last run-carrying stratum, with its own eight floors —
`⌊2x⌋ = 1, ⌊4x⌋ = 3, ⌊5x⌋ = 4, ⌊7x⌋ = 6, ⌊9x⌋ = 8, ⌊11x⌋ = 10, ⌊13x⌋ = 12, ⌊22x⌋ = 20` — so

    a = 13r − 12p,  b = 9r − 8p,  c = 5r − 4p,  e = 11r − 10p,     2e < c ⟺ 17r < 16p,

the run is `u ≥ c` (`Zeta2PtpCong.dropped_S24b`; `bit1 = bit2 = 0` hold there because
`c ≥ 9r − 8p` and `c ≥ 7r − 6p` are `r ≤ p`), and
`deg (N /ₘ denLow) = 16r − 14p − 1 ≤ p − 2 ⟺ 16r < 15p`.  Blocks run from `11n₁ + 10` to
`22n₁ + 19`; the last block `22n₁ + 20` has only off-run residues in the window.

`hanton : Zeta2PtpS2a.AntonOneCarry p` is the one binder on `term_div_eq_of_run`,
`blockSum_dvd_sq`, `piece25_blocks`.

Probe: `ptp_s2_mechanism_probe.py` / `.out` (5 window cells of `n ≤ 60`, M1–M7 GREEN).
Falsifier: `falsify_ptps2d.sh` / `out_ptps2d_falsify.txt`.

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
import Zeta2PtpS2Kit
import Zeta2PtpS2a
import Zeta2PtpS2c
import Zeta2CarryFull

set_option maxRecDepth 20000

namespace Zeta2PtpS2d

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpPolar Zeta2PtpBlock Zeta2PtpS7 Zeta2PtpS2Kit
  Zeta2PtpCong Zeta2PtpRun Zeta2PtpStratum Nat Finset Polynomial

/-! ## 1. The polynomial, the block constant, and the degree -/

noncomputable def numer (p : ℕ) [Fact p.Prime] (r : ℕ) : (ZMod p)[X] :=
  (binPoly p (13 * r - 12 * p)).comp (X + C ((4 * r : ℕ) : ZMod p))
    * (binPoly p (9 * r - 8 * p)).comp (X + C ((2 * r : ℕ) : ZMod p))
    * binPoly p (5 * r - 4 * p)

noncomputable def runPoly2 (p : ℕ) [Fact p.Prime] (r : ℕ) : (ZMod p)[X] :=
  quot (numer p r) (lowRoots p (11 * r - 10 * p))

def kappa2 (p n₁ r t : ℕ) : ZMod p :=
  -((-1) ^ t
    * (((t + 4 * n₁ + 4).choose (13 * n₁ + 12) : ℕ) : ZMod p)
    * (((t + 2 * n₁ + 2).choose (9 * n₁ + 8) : ℕ) : ZMod p)
    * ((t.choose (5 * n₁ + 4) : ℕ) : ZMod p)
    * (((11 * r - 10 * p)! : ℕ) : ZMod p)
    * ((((11 * n₁ + 10)! : ℕ) : ZMod p) * ((((t - 11 * n₁ - 10)! : ℕ) : ZMod p))⁻¹
        * ((((11 * n₁ + 10 - 1 - (t - 11 * n₁ - 10))! : ℕ) : ZMod p))⁻¹))

section Stratum
variable {p : ℕ} [hp : Fact p.Prime]

theorem numer_natDegree_le {r : ℕ} (_hr : r < p) (_hlo : 12 * p ≤ 13 * r)
    (_hhi : 15 * r < 14 * p) :
    (numer p r).natDegree ≤ (13 * r - 12 * p) + (9 * r - 8 * p) + (5 * r - 4 * p) := by
  unfold numer
  have hA : ((binPoly p (13 * r - 12 * p)).comp (X + C ((4 * r : ℕ) : ZMod p))).natDegree
      ≤ 13 * r - 12 * p := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact binPoly_natDegree_le _
  have hB : ((binPoly p (9 * r - 8 * p)).comp (X + C ((2 * r : ℕ) : ZMod p))).natDegree
      ≤ 9 * r - 8 * p := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact binPoly_natDegree_le _
  have hC : (binPoly p (5 * r - 4 * p)).natDegree ≤ 5 * r - 4 * p := binPoly_natDegree_le _
  exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hA hB) hC

omit hp in
theorem residues {r : ℕ} (hr : r < p) (hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p) :
    (13 * r) % p = 13 * r - 12 * p ∧ (9 * r) % p = 9 * r - 8 * p
    ∧ (5 * r) % p = 5 * r - 4 * p ∧ (11 * r) % p = 11 * r - 10 * p
    ∧ (4 * r) % p = 4 * r - 3 * p ∧ (2 * r) % p = 2 * r - p := by
  have hA := mod_eq_sub (p := p) (a := 13 * r) (q := 12) (by omega) (by omega)
  have hB := mod_eq_sub (p := p) (a := 9 * r) (q := 8) (by omega) (by omega)
  have hC := mod_eq_sub (p := p) (a := 5 * r) (q := 4) (by omega) (by omega)
  have hE := mod_eq_sub (p := p) (a := 11 * r) (q := 10) (by omega) (by omega)
  have hD := mod_eq_sub (p := p) (a := 4 * r) (q := 3) (by omega) (by omega)
  have hF := mod_eq_sub (p := p) (a := 2 * r) (q := 1) (by omega) (by omega)
  rw [one_mul] at hF
  exact ⟨hA, hB, hC, hE, hD, hF⟩

omit hp in
theorem wraps {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : 12 * p ≤ 13 * r)
    (hhi : 15 * r < 14 * p) :
    (u + 4 * r) % p
      = (if u + (4 * r - 3 * p) < p then u + (4 * r - 3 * p) else u + (4 * r - 3 * p) - p)
    ∧ (u + 2 * r) % p = (if u + (2 * r - p) < p then u + (2 * r - p) else u + (2 * r - p) - p) := by
  constructor
  · rw [show u + 4 * r = u + (4 * r - 3 * p) + 3 * p by omega, Nat.add_mul_mod_self_right]
    exact add_mod_split hu (by omega)
  · rw [show u + 2 * r = u + (2 * r - p) + p by omega, Nat.add_mod_right]
    exact add_mod_split hu (by omega)

theorem root1 {r u : ℕ} (_hr : r < p) (_hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p)
    (h : (u + 4 * r) % p < 13 * r - 12 * p) :
    ((binPoly p (13 * r - 12 * p)).comp (X + C ((4 * r : ℕ) : ZMod p))).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_add, eval_X, eval_C, ← Nat.cast_add, ← ZMod.natCast_mod,
    ← choose_cast_eq_binPoly ((u + 4 * r) % p) (13 * r - 12 * p) (by omega),
    Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

theorem root2 {r u : ℕ} (_hr : r < p) (_hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p)
    (h : (u + 2 * r) % p < 9 * r - 8 * p) :
    ((binPoly p (9 * r - 8 * p)).comp (X + C ((2 * r : ℕ) : ZMod p))).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_add, eval_X, eval_C, ← Nat.cast_add, ← ZMod.natCast_mod,
    ← choose_cast_eq_binPoly ((u + 2 * r) % p) (9 * r - 8 * p) (by omega),
    Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

theorem root3 {r u : ℕ} (_hr : r < p) (_hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p)
    (h : u < 5 * r - 4 * p) : (binPoly p (5 * r - 4 * p)).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, ← choose_cast_eq_binPoly u (5 * r - 4 * p) (by omega),
    Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

set_option maxHeartbeats 2000000 in
omit hp in
theorem two_of_three {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : 12 * p ≤ 13 * r)
    (hhi : 15 * r < 14 * p) (hue : 11 * r - 10 * p ≤ u) (hu2 : u ≤ 2 * (11 * r - 10 * p)) :
    ((u + 4 * r) % p < 13 * r - 12 * p ∧ (u + 2 * r) % p < 9 * r - 8 * p)
    ∨ ((u + 4 * r) % p < 13 * r - 12 * p ∧ u < 5 * r - 4 * p)
    ∨ ((u + 2 * r) % p < 9 * r - 8 * p ∧ u < 5 * r - 4 * p) := by
  have hp0 : 0 < p := by omega
  have hd := dropped_S24b hu hr hlo hhi
  obtain ⟨hA, hB, hC, hE, hD, hF⟩ := residues hr hlo hhi
  obtain ⟨h1, h2⟩ := wraps hu hr hlo hhi
  unfold bitsR at hd
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE] at hd
  rw [h1, h2]
  split_ifs at hd ⊢ <;> omega

set_option maxHeartbeats 2000000 in
omit hp in
theorem bits_ge {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : 12 * p ≤ 13 * r)
    (hhi : 15 * r < 14 * p) :
    1 ≤ bitsR p r u ∧ (¬ (5 * r - 4 * p ≤ u) → 2 ≤ bitsR p r u) := by
  have hp0 : 0 < p := by omega
  obtain ⟨hA, hB, hC, hE, hD, hF⟩ := residues hr hlo hhi
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> omega

end Stratum

/-! ## 2. The identity on the run -/

section Run
variable {p : ℕ} [hp : Fact p.Prime]

theorem denLow_dvd_numer {r : ℕ} (hr : r < p) (hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p) :
    linProd (lowRoots p (11 * r - 10 * p)) ∣ numer p r := by
  refine linProd_dvd_of_roots' (lowRoots_nodup _ (by omega)) fun a ha => ?_
  obtain ⟨u₀, hue, hu2, rfl⟩ := Zeta2PtpS2c.mem_lowRoots ha
  have hu : u₀ < p := by omega
  unfold numer
  rcases two_of_three hu hr hlo hhi hue hu2 with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h3⟩
  · exact Zeta2PtpS2a.isRoot_mul_of_left (Zeta2PtpS2a.isRoot_mul_of_left (root1 hr hlo hhi h1))
  · exact Zeta2PtpS2a.isRoot_mul_of_left (Zeta2PtpS2a.isRoot_mul_of_left (root1 hr hlo hhi h1))
  · exact Zeta2PtpS2a.isRoot_mul_of_right (root3 hr hlo hhi h3)

theorem runPoly2_eval_zero_of_mid {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : 12 * p ≤ 13 * r)
    (hhi : 15 * r < 14 * p) (hue : 11 * r - 10 * p ≤ u) (hu2 : u ≤ 2 * (11 * r - 10 * p)) :
    (runPoly2 p r).eval (u : ZMod p) = 0 := by
  unfold runPoly2
  refine quot_eval_zero_of_double (denLow_dvd_numer hr hlo hhi) (lowRoots_nodup _ (by omega))
    (Zeta2PtpS2c.mem_lowRoots_of hue hu2) ?_
  unfold numer
  rcases two_of_three hu hr hlo hhi hue hu2 with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
  · exact X_sub_C_sq_dvd_of_two (root1 hr hlo hhi h1) (root2 hr hlo hhi h2)
  · rw [mul_right_comm]
    exact X_sub_C_sq_dvd_of_two (root1 hr hlo hhi h1) (root3 hr hlo hhi h3)
  · rw [mul_assoc, mul_comm]
    exact X_sub_C_sq_dvd_of_two (root2 hr hlo hhi h2) (root3 hr hlo hhi h3)

theorem runPoly2_eval_of_gt {r u : ℕ} (hr : r < p) (hlo : 12 * p ≤ 13 * r)
    (hhi : 15 * r < 14 * p) (hu : u < p) (h2e : 2 * (11 * r - 10 * p) < u) :
    (runPoly2 p r).eval (u : ZMod p)
      = (numer p r).eval (u : ZMod p) * ((denLow p (11 * r - 10 * p)).eval (u : ZMod p))⁻¹ :=
  quot_eval_of_not_mem (denLow_dvd_numer hr hlo hhi) (Zeta2PtpS2c.not_mem_lowRoots h2e hu)

theorem runPoly2_eval_of_lt {r u : ℕ} (hr : r < p) (hlo : 12 * p ≤ 13 * r)
    (hhi : 15 * r < 14 * p) (hu : u < p) (hlt : u < 11 * r - 10 * p) :
    (runPoly2 p r).eval (u : ZMod p)
      = (numer p r).eval (u : ZMod p) * ((denLow p (11 * r - 10 * p)).eval (u : ZMod p))⁻¹ := by
  refine quot_eval_of_not_mem (denLow_dvd_numer hr hlo hhi) fun h => ?_
  obtain ⟨u₀, hue, _, h0⟩ := Zeta2PtpS2c.mem_lowRoots h
  have := ((ZMod.natCast_eq_natCast_iff _ _ _).1 h0).eq_of_lt_of_lt hu (by omega)
  omega

theorem runPoly2_natDegree_le {r : ℕ} (hr : r < p) (hlo : 12 * p ≤ 13 * r)
    (hhi : 15 * r < 14 * p) : (runPoly2 p r).natDegree ≤ p - 2 := by
  unfold runPoly2
  rw [quot_natDegree, lowRoots_card]
  have h := numer_natDegree_le hr hlo hhi
  omega

set_option maxHeartbeats 1000000 in
/-- **The identity on the run** `u ≥ c`, on every block `11n₁+10 ≤ t ≤ 22n₁+19`. -/
theorem term_div_eq_of_run (hanton : Zeta2PtpS2a.AntonOneCarry p) {n n₁ r t u : ℕ}
    (hp' : p ∈ phiWindow n)
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p)
    (hu : u < p) (hcu : 5 * r - 4 * p ≤ u)
    (ht : 11 * n₁ + 10 ≤ t) (ht2 : t ≤ 22 * n₁ + 19) (htp : t < p) :
    ((((-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
        * (cTerm n (t * p + u + 4 * n + 1) : ℤ) : ℤ) / (p : ℤ) : ℤ) : ZMod p)
      = kappa2 p n₁ r t * (runPoly2 p r).eval (u : ZMod p) := by
  have hp0 := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hsq := sq_gt_of_mem_phiWindow hp'
  have hk1 : t * p + u + 4 * n = (u + 4 * r - 4 * p) + (t + 4 * n₁ + 4) * p := by
    have e : (t + 4 * n₁ + 4) * p = t * p + 4 * (p * n₁) + 4 * p := by ring
    omega
  have hk2 : t * p + u + 4 * n + 1 - 2 * n - 1 = (u + 2 * r - 2 * p) + (t + 2 * n₁ + 2) * p := by
    have e : (t + 2 * n₁ + 2) * p = t * p + 2 * (p * n₁) + 2 * p := by ring
    omega
  have hk3 : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
  have hk4 : t * p + u + 4 * n + 1 - 15 * n - 1
      = (u - (11 * r - 10 * p)) + (t - 11 * n₁ - 10) * p := by
    have e : (t - 11 * n₁ - 10) * p = t * p - (11 * n₁ + 10) * p := by
      rw [show t - 11 * n₁ - 10 = t - (11 * n₁ + 10) by omega, Nat.sub_mul]
    have e2 : (11 * n₁ + 10) * p = 11 * (p * n₁) + 10 * p := by ring
    have e3 : (11 * n₁ + 10) * p ≤ t * p := Nat.mul_le_mul_right p ht
    omega
  have h13 : 13 * n = (13 * r - 12 * p) + (13 * n₁ + 12) * p := by
    have e : (13 * n₁ + 12) * p = 13 * (p * n₁) + 12 * p := by ring
    omega
  have h9 : 9 * n = (9 * r - 8 * p) + (9 * n₁ + 8) * p := by
    have e : (9 * n₁ + 8) * p = 9 * (p * n₁) + 8 * p := by ring
    omega
  have h5 : 5 * n = (5 * r - 4 * p) + (5 * n₁ + 4) * p := by
    have e : (5 * n₁ + 4) * p = 5 * (p * n₁) + 4 * p := by ring
    omega
  have h11 : 11 * n = (11 * r - 10 * p) + p * (11 * n₁ + 10) := by
    have e : p * (11 * n₁ + 10) = 11 * (p * n₁) + 10 * p := by ring
    omega
  obtain ⟨d1q, d1r⟩ := digits_of_decomp hp0 hk1 (by omega)
  obtain ⟨d2q, d2r⟩ := digits_of_decomp hp0 hk2 (by omega)
  obtain ⟨d3q, d3r⟩ := digits_of_decomp hp0 hk3 hu
  obtain ⟨a13q, a13r⟩ := digits_of_decomp hp0 h13 (by omega)
  obtain ⟨a9q, a9r⟩ := digits_of_decomp hp0 h9 (by omega)
  obtain ⟨a5q, a5r⟩ := digits_of_decomp hp0 h5 (by omega)
  have c1 : ((t * p + u + 4 * n : ℕ) : ZMod p) = (u : ZMod p) + ((4 * r : ℕ) : ZMod p) := by
    rw [cast_of_decomp hk1, Nat.cast_sub (by omega : 4 * p ≤ u + 4 * r)]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have c2 : ((t * p + u + 4 * n + 1 - 2 * n - 1 : ℕ) : ZMod p)
      = (u : ZMod p) + ((2 * r : ℕ) : ZMod p) := by
    rw [cast_of_decomp hk2, Nat.cast_sub (by omega : 2 * p ≤ u + 2 * r)]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have c3 : ((t * p + u + 4 * n + 1 - 4 * n - 1 : ℕ) : ZMod p) = (u : ZMod p) :=
    cast_of_decomp hk3
  have hsign : (-1 : ZMod p) ^ (12 * n + (t * p + u + 4 * n + 1) - 1) = (-1) ^ t * (-1) ^ u := by
    have e : 12 * n + (t * p + u + 4 * n + 1) - 1 = 2 * (8 * n) + t * p + u := by omega
    have hp1 : (-1 : ZMod p) ^ (t * p) = (-1) ^ t := by
      rw [pow_mul' (-1 : ZMod p) t p, hodd.neg_one_pow]
    have hp2 : (-1 : ZMod p) ^ (2 * (8 * n)) = 1 := by
      rw [pow_mul (-1 : ZMod p) 2 (8 * n), neg_one_sq, one_pow]
    rw [e, pow_add, pow_add, hp1, hp2]
    ring
  have hue : 11 * r - 10 * p ≤ u := by omega
  have hA := hanton (11 * r - 10 * p) (11 * n₁ + 10) (u - (11 * r - 10 * p)) (t - 11 * n₁ - 10)
    (by omega) (by omega) (by omega) (by omega)
  have hk4' : u - (11 * r - 10 * p) + p * (t - 11 * n₁ - 10)
      = t * p + u + 4 * n + 1 - 15 * n - 1 := by rw [hk4, Nat.mul_comm p (t - 11 * n₁ - 10)]
  rw [hk4', ← h11] at hA
  have hbr : (((11 * r - 10 * p)! : ℕ) : ZMod p)
        * ((((11 * r - 10 * p + p - (u - (11 * r - 10 * p)))! : ℕ) : ZMod p))⁻¹
        * ((((u - (11 * r - 10 * p))! : ℕ) : ZMod p))⁻¹
      = (-1) ^ (11 * r - 10 * p + (u - (11 * r - 10 * p))) * (((11 * r - 10 * p)! : ℕ) : ZMod p)
        * ((((u - (11 * r - 10 * p)).descFactorial (11 * r - 10 * p + 1) : ℕ) : ZMod p))⁻¹ := by
    rw [mul_right_comm]
    exact factorial_inv_eq_denLow (by omega) (by omega) (by omega)
  rw [Nat.add_sub_of_le hue] at hbr
  have hden : (denLow p (11 * r - 10 * p)).eval (u : ZMod p)
      = (((u - (11 * r - 10 * p)).descFactorial (11 * r - 10 * p + 1) : ℕ) : ZMod p) := by
    have h := denLow_eval (p := p) (11 * r - 10 * p) (u - (11 * r - 10 * p)) (by omega)
    rwa [Nat.sub_add_cancel hue] at h
  have hdvd : p ∣ (11 * n).choose (t * p + u + 4 * n + 1 - 15 * n - 1) := by
    have hle : t * p + u + 4 * n + 1 - 15 * n - 1 ≤ 11 * n := by
      have e3 : t * p ≤ (22 * n₁ + 19) * p := Nat.mul_le_mul_right p ht2
      have e : (22 * n₁ + 19) * p = 22 * (p * n₁) + 19 * p := by ring
      omega
    have hlog : Nat.log p (11 * n) ≤ 1 := by
      have hlt : 11 * n < p ^ 2 := by omega
      have hne : 11 * n ≠ 0 := by omega
      have := Nat.log_lt_of_lt_pow hne hlt
      omega
    have hv := vp_choose_eq_cb (p := p) hle hlog
    have hmod1 : (11 * n) % p = 11 * r - 10 * p := by
      rw [h11, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 11 * r - 10 * p < p)]
    have hmod2 : (t * p + u + 4 * n + 1 - 15 * n - 1) % p = u - (11 * r - 10 * p) := by
      rw [hk4, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hcb : cb p (11 * n) (t * p + u + 4 * n + 1 - 15 * n - 1) = 1 := by
      unfold cb
      rw [hmod1, hmod2]
      split_ifs with h
      · rfl
      · exfalso; omega
    rw [hcb] at hv
    have := (padicValNat_dvd_iff_le (p := p) (n := 1)
      (Nat.choose_pos hle).ne').2 (by omega)
    simpa using this
  obtain ⟨q, hq⟩ := hdvd
  have hq' : (11 * n).choose (t * p + u + 4 * n + 1 - 15 * n - 1) / p = q := by
    rw [hq, Nat.mul_div_cancel_left _ hp0]
  have hterm : (-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
      * (cTerm n (t * p + u + 4 * n + 1) : ℤ)
      = (p : ℤ) * ((-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
          * (((t * p + u + 4 * n).choose (13 * n)
              * (t * p + u + 4 * n + 1 - 2 * n - 1).choose (9 * n)
              * (t * p + u + 4 * n + 1 - 4 * n - 1).choose (5 * n) * q : ℕ) : ℤ)) := by
    rw [cTerm, hq, Nat.add_sub_cancel (n := t * p + u + 4 * n) (m := 1)]; push_cast; ring
  rw [hterm, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp0.ne')]
  push_cast
  rw [hsign, lucas_factor (t * p + u + 4 * n) (13 * n),
    lucas_factor (t * p + u + 4 * n + 1 - 2 * n - 1) (9 * n),
    lucas_factor (t * p + u + 4 * n + 1 - 4 * n - 1) (5 * n),
    d1q, d2q, d3q, a13q, a13r, a9q, a9r, a5q, a5r, c1, c2, c3, ← hq', hA, hbr, ← hden]
  rw [runPoly2_eval_of_gt hr hlo hhi hu (by omega)]
  unfold kappa2 numer
  simp only [eval_mul, eval_comp, eval_add, eval_X, eval_C]
  rcases Nat.even_or_odd u with hpar | hpar
  · rw [hpar.neg_one_pow]; ring
  · rw [hpar.neg_one_pow]; ring

end Run

/-! ## 3. The block congruence on `[12/13, 14/15)`, at every block -/

section Block
variable {p : ℕ} [hp : Fact p.Prime]

theorem sq_dvd_cTerm_of_not_run {n n₁ r t u : ℕ} (hp' : p ∈ phiWindow n)
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p)
    (hu : u < p) (hk : t * p + u + 4 * n + 1 ∈ candidateM.window n)
    (hnot : ¬ (5 * r - 4 * p ≤ u)) :
    p ^ 2 ∣ cTerm n (t * p + u + 4 * n + 1) := by
  have hp0 := hp.out.pos
  refine pow_dvd_cTerm_of_units hp' hk ?_
  have h := carries_eq_bitsR hp0 hk
  unfold carries at h
  rw [h]
  have hk3 : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
  have hr' : n % p = r := by rw [hn, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [hk3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu, hr']
  exact (bits_ge hu hr hlo hhi).2 hnot

theorem dvd_cTerm_of_stratum {n n₁ r t u : ℕ} (hp' : p ∈ phiWindow n)
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p)
    (hu : u < p) (hk : t * p + u + 4 * n + 1 ∈ candidateM.window n) :
    p ∣ cTerm n (t * p + u + 4 * n + 1) := by
  have hp0 := hp.out.pos
  have := pow_dvd_cTerm_of_units (v := 1) hp' hk ?_
  · simpa using this
  have h := carries_eq_bitsR hp0 hk
  unfold carries at h
  rw [h]
  have hk3 : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
  have hr' : n % p = r := by rw [hn, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [hk3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu, hr']
  exact (bits_ge hu hr hlo hhi).1

theorem blockSum_dvd_sq_of_all_off {n n₁ r t : ℕ} (hp' : p ∈ phiWindow n)
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p)
    (hoff : ∀ u < p, t * p + u + 4 * n + 1 ∈ candidateM.window n → ¬ (5 * r - 4 * p ≤ u)) :
    (p : ℤ) ^ 2 ∣ blockSum n p t := by
  have hp0 := hp.out.pos
  refine blockSum_sq_dvd_of_poly t 0 0 (by simp) ?_ ?_
  · intro u hu
    split_ifs with hmem
    · exact Dvd.dvd.mul_left
        (Int.natCast_dvd_natCast.2 (dvd_cTerm_of_stratum hp' hn hr hlo hhi hu hmem)) _
    · exact dvd_zero _
  · intro u hu
    rw [zero_mul]
    split_ifs with hmem
    · exact Zeta2PtpS2a.cast_div_eq_zero_of_sq_dvd (by
        have h := sq_dvd_cTerm_of_not_run hp' hn hr hlo hhi hu hmem (hoff u hu hmem)
        have h' : ((p ^ 2 : ℕ) : ℤ) ∣ ((cTerm n (t * p + u + 4 * n + 1) : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.2 h
        push_cast at h'
        exact Dvd.dvd.mul_left h' _)
    · simp

/-- **THE BLOCK CONGRUENCE ON `[12/13, 14/15)` AT EVERY BLOCK, conditional on Anton.** -/
theorem blockSum_dvd_sq (hanton : Zeta2PtpS2a.AntonOneCarry p) {n : ℕ} (hp' : p ∈ phiWindow n)
    (hlo : 12 * p ≤ 13 * (n % p)) (hhi : 15 * (n % p) < 14 * p) (t : ℕ) :
    (p : ℤ) ^ 2 ∣ blockSum n p t := by
  have hp0 := hp.out.pos
  have hn : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hr : n % p < p := Nat.mod_lt _ hp0
  generalize n / p = n₁ at hn
  generalize n % p = r at hn hr hlo hhi
  rcases Nat.lt_or_ge t (11 * n₁ + 10) with hlt | hge
  · refine blockSum_dvd_sq_of_all_off hp' hn hr hlo hhi fun u hu hmem => ?_
    rw [mem_window_iff] at hmem
    have e1 : (t + 1) * p ≤ (11 * n₁ + 10) * p := Nat.mul_le_mul_right p (by omega)
    have e2 : (t + 1) * p = t * p + p := by ring
    have e3 : (11 * n₁ + 10) * p = 11 * (p * n₁) + 10 * p := by ring
    omega
  rcases Nat.lt_or_ge (22 * n₁ + 19) t with hgt | hle
  · refine blockSum_dvd_sq_of_all_off hp' hn hr hlo hhi fun u hu hmem hcu => ?_
    rw [mem_window_iff] at hmem
    have e1 : (22 * n₁ + 20) * p ≤ t * p := Nat.mul_le_mul_right p (by omega)
    have e3 : (22 * n₁ + 20) * p = 22 * (p * n₁) + 20 * p := by ring
    omega
  have htp : t < p := by
    have hk : 26 * n + 1 ∈ candidateM.window n := (mem_window_iff n _).2 ⟨by omega, le_rfl⟩
    have hb := block_lt hp' hk
    have e : 26 * n + 1 - 4 * n - 1 = 22 * n := by omega
    rw [e] at hb
    have e2 : (22 * n₁ + 19) * p ≤ 22 * n := by
      have : (22 * n₁ + 19) * p = 22 * (p * n₁) + 19 * p := by ring
      omega
    have : 22 * n₁ + 19 ≤ 22 * n / p := (Nat.le_div_iff_mul_le hp0).2 e2
    omega
  refine blockSum_sq_dvd_of_poly t (kappa2 p n₁ r t) (runPoly2 p r)
    (runPoly2_natDegree_le hr hlo hhi) ?_ ?_
  · intro u hu
    split_ifs with hmem
    · have h := dvd_cTerm_of_stratum hp' hn hr hlo hhi hu hmem
      exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 h) _
    · exact dvd_zero _
  · intro u hu
    by_cases hrun : 5 * r - 4 * p ≤ u
    · have hmem : t * p + u + 4 * n + 1 ∈ candidateM.window n := by
        rw [mem_window_iff]
        have e1 : (11 * n₁ + 10) * p ≤ t * p := Nat.mul_le_mul_right p (by omega)
        have e2 : t * p ≤ (22 * n₁ + 19) * p := Nat.mul_le_mul_right p (by omega)
        have e3 : (11 * n₁ + 10) * p = 11 * (p * n₁) + 10 * p := by ring
        have e4 : (22 * n₁ + 19) * p = 22 * (p * n₁) + 19 * p := by ring
        constructor <;> omega
      split_ifs
      exact term_div_eq_of_run hanton hp' hn hr hlo hhi hu hrun hge hle htp
    · have hQ : (runPoly2 p r).eval (u : ZMod p) = 0 := by
        rcases Nat.lt_or_ge u (11 * r - 10 * p) with hlt | hge'
        · rw [runPoly2_eval_of_lt hr hlo hhi hu hlt]
          have hN : (numer p r).eval (u : ZMod p) = 0 := by
            unfold numer
            simp only [eval_mul]
            have := root3 (u := u) hr hlo hhi (by omega)
            rw [IsRoot.def] at this
            rw [this, mul_zero]
          rw [hN, zero_mul]
        · rcases Nat.lt_or_ge (2 * (11 * r - 10 * p)) u with hgt | hle'
          · rw [runPoly2_eval_of_gt hr hlo hhi hu hgt]
            have hN : (numer p r).eval (u : ZMod p) = 0 := by
              unfold numer
              simp only [eval_mul]
              have := root3 (u := u) hr hlo hhi (by omega)
              rw [IsRoot.def] at this
              rw [this, mul_zero]
            rw [hN, zero_mul]
          · exact runPoly2_eval_zero_of_mid hu hr hlo hhi hge' hle'
      rw [hQ, mul_zero]
      split_ifs with hmem
      · exact Zeta2PtpS2a.cast_div_eq_zero_of_sq_dvd (by
          have h := sq_dvd_cTerm_of_not_run hp' hn hr hlo hhi hu hmem hrun
          have h' : ((p ^ 2 : ℕ) : ℤ) ∣ ((cTerm n (t * p + u + 4 * n + 1) : ℕ) : ℤ) :=
            Int.natCast_dvd_natCast.2 h
          push_cast at h'
          exact Dvd.dvd.mul_left h' _)
      · simp

end Block

/-! ## 4. The φ̃ wire on piece 25, and the piece for the harmonic side -/

theorem phiT_piece25 {x : ℚ} (h1 : 10 / 11 ≤ x) (h2 : x < 14 / 15) : phiT x = 2 := by
  have h := phiT_of_mem (a := 10 / 11) (b := 14 / 15) (v := 2) (by decide +kernel) h1 h2
  exact h

theorem phiT_piece25_res {n p : ℕ} (hp : 0 < p) (hlo : 10 * p ≤ 11 * (n % p))
    (hhi : 15 * (n % p) < 14 * p) : phiT (Int.fract ((n : ℚ) / (p : ℚ))) = 2 := by
  refine phiT_piece25 ?_ ?_
  · have h := (fract_ge_iff n p 10 11 hp (by norm_num)).2 (by omega)
    exact_mod_cast h
  · have h := (fract_lt_iff n p 14 15 hp (by norm_num)).2 (by omega)
    exact_mod_cast h

/-- **PROFILE PIECE 25 `[10/11, 14/15)` FOR THE HARMONIC SIDE, conditional on Anton**: the
run-free stratum `[10/11, 12/13)` through `Zeta2PtpCong.noShort_S7`, the run stratum through
`blockSum_dvd_sq`. -/
theorem piece25_blocks {p n : ℕ} [Fact p.Prime] (hanton : Zeta2PtpS2a.AntonOneCarry p)
    (hp : p ∈ phiWindow n) (hlo : 10 * p ≤ 11 * (n % p)) (hhi : 15 * (n % p) < 14 * p)
    (t : ℕ) : (p : ℤ) ^ (phiT (Int.fract ((n : ℚ) / (p : ℚ)))) ∣ blockSum n p t := by
  have hp0 := (prime_of_mem_phiWindow hp).pos
  rw [phiT_piece25_res hp0 hlo hhi]
  rcases Nat.lt_or_ge (13 * (n % p)) (12 * p) with h13 | h13
  · exact blockSum_dvd_of_noShort hp (Zeta2PtpCong.noShort_S7 hp0 hlo h13) t
  · exact blockSum_dvd_sq hanton hp h13 hhi t

/-- The stratum is inhabited by a window cell: `n = 27`, `p = 29`, `r = 27` (`27/29 ≈ 0.931`). -/
theorem witness_27_29 :
    29 ∈ phiWindow 27 ∧ 12 * 29 ≤ 13 * (27 % 29) ∧ 15 * (27 % 29) < 14 * 29 := by
  refine ⟨by decide +kernel, by decide, by decide⟩

end Zeta2PtpS2d

#print axioms Zeta2PtpS2d.numer_natDegree_le
#check @Zeta2PtpS2d.numer_natDegree_le
#print axioms Zeta2PtpS2d.two_of_three
#check @Zeta2PtpS2d.two_of_three
#print axioms Zeta2PtpS2d.bits_ge
#check @Zeta2PtpS2d.bits_ge
#print axioms Zeta2PtpS2d.denLow_dvd_numer
#check @Zeta2PtpS2d.denLow_dvd_numer
#print axioms Zeta2PtpS2d.runPoly2_eval_zero_of_mid
#check @Zeta2PtpS2d.runPoly2_eval_zero_of_mid
#print axioms Zeta2PtpS2d.runPoly2_natDegree_le
#check @Zeta2PtpS2d.runPoly2_natDegree_le
#print axioms Zeta2PtpS2d.term_div_eq_of_run
#check @Zeta2PtpS2d.term_div_eq_of_run
#print axioms Zeta2PtpS2d.blockSum_dvd_sq
#check @Zeta2PtpS2d.blockSum_dvd_sq
#print axioms Zeta2PtpS2d.phiT_piece25
#check @Zeta2PtpS2d.phiT_piece25
#print axioms Zeta2PtpS2d.piece25_blocks
#check @Zeta2PtpS2d.piece25_blocks
#print axioms Zeta2PtpS2d.witness_27_29
#check @Zeta2PtpS2d.witness_27_29
