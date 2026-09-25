/-
# Row PT-P, layer 9b — the run congruence on the φ̃ = 2 run stratum `[5/9, 9/16)` (the dropped
# arc is `I3`), CONDITIONAL on Anton's one-carry congruence, and piece 16 `[6/11, 9/16)`
# discharged for the harmonic side under the same hypothesis

`Zeta2PtpS2a` is the template (stratum `[1/9, 2/17)`, the same dropped arc); this file is that
proof at the other `I3` stratum, with its own eight floors —
`⌊2x⌋ = 1, ⌊4x⌋ = 2, ⌊5x⌋ = 2, ⌊7x⌋ = 3, ⌊9x⌋ = 5, ⌊11x⌋ = 6, ⌊13x⌋ = 7, ⌊22x⌋ = 12` — so

    a = 13r − 7p,  b = 9r − 5p,  c = 5r − 2p,  e = 11r − 6p,      2e < c ⟺ 17r < 10p,

the run is `e ≤ u ≤ 2e` (`ptp_s2_mechanism_probe.py`, M1–M7 GREEN at the 9 window cells of
`n ≤ 60`, `dropped_S15b`), and `deg (N /ₘ denTop) = 16r − 8p − 1 ≤ p − 2 ⟺ 16r < 9p`.  The
zero-margin cell of the sixth pass, `n = 23, p = 41` (`D = p − 2` exactly), lies here and is the
witness.

The hypothesis is `Zeta2PtpS2a.AntonOneCarry p`, the same `def`, a binder on `term_div_eq_of_run`,
`blockSum_dvd_sq` and `piece16_blocks` — read the `#check @` lines.

Probe: `ptp_s2_mechanism_probe.py` / `.out`.  Falsifier: `falsify_ptps2b.sh` / `out_ptps2b_falsify.txt`.

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
import Zeta2CarryFull

set_option maxRecDepth 20000

namespace Zeta2PtpS2b

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpPolar Zeta2PtpBlock Zeta2PtpS7 Zeta2PtpS2Kit
  Zeta2PtpCong Zeta2PtpRun Zeta2PtpStratum Nat Finset Polynomial

/-! ## 1. The polynomial, the block constant, and the degree -/

/-- The three uncarried factors (the shifts `4r`, `2r` are residues, so the same `C` as on
`[1/9, 2/17)`). -/
noncomputable def numer (p : ℕ) [Fact p.Prime] (r : ℕ) : (ZMod p)[X] :=
  (binPoly p (13 * r - 7 * p)).comp (X + C ((4 * r : ℕ) : ZMod p))
    * (binPoly p (9 * r - 5 * p)).comp (X + C ((2 * r : ℕ) : ZMod p))
    * (signChoosePoly p (11 * r - 6 * p)).comp (X - C ((11 * r - 6 * p : ℕ) : ZMod p))

noncomputable def runPoly2 (p : ℕ) [Fact p.Prime] (r : ℕ) : (ZMod p)[X] :=
  quot (numer p r) (topRoots p (5 * r - 2 * p))

def kappa2 (p n₁ r t : ℕ) : ZMod p :=
  (-1) ^ t * (-1) ^ (11 * r - 6 * p)
    * (((t + 4 * n₁ + 2).choose (13 * n₁ + 7) : ℕ) : ZMod p)
    * (((t + 2 * n₁ + 1).choose (9 * n₁ + 5) : ℕ) : ZMod p)
    * (-((((5 * r - 2 * p)! : ℕ) : ZMod p))⁻¹ * ((t ! : ℕ) : ZMod p)
        * ((((5 * n₁ + 2)! : ℕ) : ZMod p))⁻¹ * ((((t - 1 - (5 * n₁ + 2))! : ℕ) : ZMod p))⁻¹)
    * (((11 * n₁ + 6).choose (t - 11 * n₁ - 6) : ℕ) : ZMod p)

section Stratum
variable {p : ℕ} [hp : Fact p.Prime]

theorem numer_natDegree_le {r : ℕ} (_hr : r < p) (_hlo : 5 * p ≤ 9 * r) (_hhi : 16 * r < 9 * p) :
    (numer p r).natDegree ≤ (13 * r - 7 * p) + (9 * r - 5 * p) + (p - 1 - (11 * r - 6 * p)) := by
  unfold numer
  have hA : ((binPoly p (13 * r - 7 * p)).comp (X + C ((4 * r : ℕ) : ZMod p))).natDegree
      ≤ 13 * r - 7 * p := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact binPoly_natDegree_le _
  have hB : ((binPoly p (9 * r - 5 * p)).comp (X + C ((2 * r : ℕ) : ZMod p))).natDegree
      ≤ 9 * r - 5 * p := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact binPoly_natDegree_le _
  have hD : ((signChoosePoly p (11 * r - 6 * p)).comp
      (X - C ((11 * r - 6 * p : ℕ) : ZMod p))).natDegree ≤ p - 1 - (11 * r - 6 * p) := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_sub_C, mul_one]
    exact signChoosePoly_natDegree_le _
  exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hA hB) hD

omit hp in
/-- The six residues the stratum's bit lemmas are spelled in. -/
theorem residues {r : ℕ} (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p) :
    (13 * r) % p = 13 * r - 7 * p ∧ (9 * r) % p = 9 * r - 5 * p ∧ (5 * r) % p = 5 * r - 2 * p
    ∧ (11 * r) % p = 11 * r - 6 * p ∧ (4 * r) % p = 4 * r - 2 * p ∧ (2 * r) % p = 2 * r - p := by
  have hA := mod_eq_sub (p := p) (a := 13 * r) (q := 7) (by omega) (by omega)
  have hB := mod_eq_sub (p := p) (a := 9 * r) (q := 5) (by omega) (by omega)
  have hC := mod_eq_sub (p := p) (a := 5 * r) (q := 2) (by omega) (by omega)
  have hE := mod_eq_sub (p := p) (a := 11 * r) (q := 6) (by omega) (by omega)
  have hD := mod_eq_sub (p := p) (a := 4 * r) (q := 2) (by omega) (by omega)
  have hF := mod_eq_sub (p := p) (a := 2 * r) (q := 1) (by omega) (by omega)
  rw [one_mul] at hF
  exact ⟨hA, hB, hC, hE, hD, hF⟩

omit hp in
/-- The wrapped forms of the two shifted residues, with the shifts reduced below `p` first
(`add_mod_split` needs `c ≤ p`, and `4r`, `2r` exceed `p` on this stratum). -/
theorem wraps {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p) :
    (u + 4 * r) % p
      = (if u + (4 * r - 2 * p) < p then u + (4 * r - 2 * p) else u + (4 * r - 2 * p) - p)
    ∧ (u + 2 * r) % p = (if u + (2 * r - p) < p then u + (2 * r - p) else u + (2 * r - p) - p) := by
  constructor
  · rw [show u + 4 * r = u + (4 * r - 2 * p) + 2 * p by omega, Nat.add_mul_mod_self_right]
    exact add_mod_split hu (by omega)
  · rw [show u + 2 * r = u + (2 * r - p) + p by omega, Nat.add_mod_right]
    exact add_mod_split hu (by omega)

/-! ### The three factors vanish where their bit is `1` -/

theorem root1 {r u : ℕ} (_hr : r < p) (_hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p)
    (h : (u + 4 * r) % p < 13 * r - 7 * p) :
    ((binPoly p (13 * r - 7 * p)).comp (X + C ((4 * r : ℕ) : ZMod p))).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_add, eval_X, eval_C, ← Nat.cast_add, ← ZMod.natCast_mod,
    ← choose_cast_eq_binPoly ((u + 4 * r) % p) (13 * r - 7 * p) (by omega),
    Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

theorem root2 {r u : ℕ} (_hr : r < p) (_hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p)
    (h : (u + 2 * r) % p < 9 * r - 5 * p) :
    ((binPoly p (9 * r - 5 * p)).comp (X + C ((2 * r : ℕ) : ZMod p))).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_add, eval_X, eval_C, ← Nat.cast_add, ← ZMod.natCast_mod,
    ← choose_cast_eq_binPoly ((u + 2 * r) % p) (9 * r - 5 * p) (by omega),
    Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

theorem cast_sub_e {r u : ℕ} (_hr : r < p) (_hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p) :
    (u : ZMod p) - ((11 * r - 6 * p : ℕ) : ZMod p)
      = (((u + (p - (11 * r - 6 * p))) % p : ℕ) : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (by omega : 11 * r - 6 * p ≤ p),
    ZMod.natCast_self]
  ring

theorem root4 {r u : ℕ} (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p)
    (h : 11 * r - 6 * p < (u + (p - (11 * r - 6 * p))) % p) :
    ((signChoosePoly p (11 * r - 6 * p)).comp
      (X - C ((11 * r - 6 * p : ℕ) : ZMod p))).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_sub, eval_X, eval_C, cast_sub_e hr hlo hhi,
    ← signChoose_eq (p := p) (11 * r - 6 * p) ((u + (p - (11 * r - 6 * p))) % p) (by omega)
      (Nat.mod_lt _ hp.out.pos),
    Nat.choose_eq_zero_of_lt h]
  simp

/-! ### The stratum's carry structure -/

-- Six `if`s (two of them the wrapped shifts) → 64 `omega` cases: over the default budget
-- (measured, draft 1: `whnf` timeout at the declaration).
set_option maxHeartbeats 2000000 in
omit hp in
theorem two_of_three {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : 5 * p ≤ 9 * r)
    (hhi : 16 * r < 9 * p) (hcu : 5 * r - 2 * p ≤ u) :
    ((u + 4 * r) % p < 13 * r - 7 * p ∧ (u + 2 * r) % p < 9 * r - 5 * p)
    ∨ ((u + 4 * r) % p < 13 * r - 7 * p ∧ 11 * r - 6 * p < (u + (p - (11 * r - 6 * p))) % p)
    ∨ ((u + 2 * r) % p < 9 * r - 5 * p ∧ 11 * r - 6 * p < (u + (p - (11 * r - 6 * p))) % p) := by
  have hp0 : 0 < p := by omega
  have hd := dropped_S15b hu hr hlo hhi
  obtain ⟨hA, hB, hC, hE, hD, hF⟩ := residues hr hlo hhi
  obtain ⟨h1, h2⟩ := wraps hu hr hlo hhi
  have h4 : (u + (p - (11 * r - 6 * p))) % p
      = if u + (p - (11 * r - 6 * p)) < p then u + (p - (11 * r - 6 * p))
        else u + (p - (11 * r - 6 * p)) - p := add_mod_split hu (by omega)
  unfold bitsR at hd
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE] at hd
  rw [h1, h2, h4]
  split_ifs at hd ⊢ <;> omega

omit hp in
theorem bits_ge {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p) :
    1 ≤ bitsR p r u
    ∧ (¬ (11 * r - 6 * p ≤ u ∧ u ≤ 2 * (11 * r - 6 * p)) → 2 ≤ bitsR p r u) := by
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

theorem denTop_dvd_numer {r : ℕ} (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p) :
    linProd (topRoots p (5 * r - 2 * p)) ∣ numer p r := by
  refine linProd_dvd_of_roots' (topRoots_nodup _ (by omega)) fun a ha => ?_
  obtain ⟨u₀, hcu, hu, rfl⟩ := Zeta2PtpS2a.mem_topRoots ha
  unfold numer
  rcases two_of_three hu hr hlo hhi hcu with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h4⟩
  · exact Zeta2PtpS2a.isRoot_mul_of_left (Zeta2PtpS2a.isRoot_mul_of_left (root1 hr hlo hhi h1))
  · exact Zeta2PtpS2a.isRoot_mul_of_left (Zeta2PtpS2a.isRoot_mul_of_left (root1 hr hlo hhi h1))
  · exact Zeta2PtpS2a.isRoot_mul_of_right (root4 hr hlo hhi h4)

theorem runPoly2_eval_zero_of_ge {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : 5 * p ≤ 9 * r)
    (hhi : 16 * r < 9 * p) (hcu : 5 * r - 2 * p ≤ u) : (runPoly2 p r).eval (u : ZMod p) = 0 := by
  unfold runPoly2
  have hmem : (u : ZMod p) ∈ topRoots p (5 * r - 2 * p) := by
    unfold topRoots
    rw [Multiset.mem_map]
    refine ⟨p - 1 - u, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_range]; omega
    · have e : (p - 1 - u + 1 : ℕ) = p - u := by omega
      rw [e, Nat.cast_sub hu.le, ZMod.natCast_self]
      ring
  refine quot_eval_zero_of_double (denTop_dvd_numer hr hlo hhi) (topRoots_nodup _ (by omega))
    hmem ?_
  unfold numer
  rcases two_of_three hu hr hlo hhi hcu with ⟨h1, h2⟩ | ⟨h1, h4⟩ | ⟨h2, h4⟩
  · exact X_sub_C_sq_dvd_of_two (root1 hr hlo hhi h1) (root2 hr hlo hhi h2)
  · rw [mul_right_comm]
    exact X_sub_C_sq_dvd_of_two (root1 hr hlo hhi h1) (root4 hr hlo hhi h4)
  · rw [mul_assoc, mul_comm]
    exact X_sub_C_sq_dvd_of_two (root2 hr hlo hhi h2) (root4 hr hlo hhi h4)

theorem runPoly2_eval_of_lt {r u : ℕ} (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p)
    (hcu : u < 5 * r - 2 * p) :
    (runPoly2 p r).eval (u : ZMod p)
      = (numer p r).eval (u : ZMod p) * ((denTop p (5 * r - 2 * p)).eval (u : ZMod p))⁻¹ :=
  quot_eval_of_not_mem (denTop_dvd_numer hr hlo hhi)
    (Zeta2PtpS2a.not_mem_topRoots hcu (by omega))

theorem runPoly2_natDegree_le {r : ℕ} (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p) :
    (runPoly2 p r).natDegree ≤ p - 2 := by
  unfold runPoly2
  rw [quot_natDegree, topRoots_card]
  have h := numer_natDegree_le hr hlo hhi
  omega

set_option maxHeartbeats 1000000 in
/-- **The identity on the run** `e ≤ u ≤ 2e`, on every in-window block. -/
theorem term_div_eq_of_run (hanton : Zeta2PtpS2a.AntonOneCarry p) {n n₁ r t u : ℕ}
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p)
    (hu : u < p) (hue : 11 * r - 6 * p ≤ u) (hu2 : u ≤ 2 * (11 * r - 6 * p))
    (ht : 11 * n₁ + 6 ≤ t) (htp : t < p) :
    ((((-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
        * (cTerm n (t * p + u + 4 * n + 1) : ℤ) : ℤ) / (p : ℤ) : ℤ) : ZMod p)
      = kappa2 p n₁ r t * (runPoly2 p r).eval (u : ZMod p) := by
  have hp0 := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  -- affine decompositions
  have hk1 : t * p + u + 4 * n = (u + 4 * r - 2 * p) + (t + 4 * n₁ + 2) * p := by
    have e : (t + 4 * n₁ + 2) * p = t * p + 4 * (p * n₁) + 2 * p := by ring
    omega
  have hk2 : t * p + u + 4 * n + 1 - 2 * n - 1 = (u + 2 * r - p) + (t + 2 * n₁ + 1) * p := by
    have e : (t + 2 * n₁ + 1) * p = t * p + 2 * (p * n₁) + p := by ring
    omega
  have hk3 : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
  have hk4 : t * p + u + 4 * n + 1 - 15 * n - 1
      = (u - (11 * r - 6 * p)) + (t - 11 * n₁ - 6) * p := by
    have e : (t - 11 * n₁ - 6) * p = t * p - (11 * n₁ + 6) * p := by
      rw [show t - 11 * n₁ - 6 = t - (11 * n₁ + 6) by omega, Nat.sub_mul]
    have e2 : (11 * n₁ + 6) * p = 11 * (p * n₁) + 6 * p := by ring
    have e3 : (11 * n₁ + 6) * p ≤ t * p := Nat.mul_le_mul_right p ht
    omega
  have h13 : 13 * n = (13 * r - 7 * p) + (13 * n₁ + 7) * p := by
    have e : (13 * n₁ + 7) * p = 13 * (p * n₁) + 7 * p := by ring
    omega
  have h9 : 9 * n = (9 * r - 5 * p) + (9 * n₁ + 5) * p := by
    have e : (9 * n₁ + 5) * p = 9 * (p * n₁) + 5 * p := by ring
    omega
  have h5 : 5 * n = (5 * r - 2 * p) + p * (5 * n₁ + 2) := by
    have e : p * (5 * n₁ + 2) = 5 * (p * n₁) + 2 * p := by ring
    omega
  have h11 : 11 * n = (11 * r - 6 * p) + (11 * n₁ + 6) * p := by
    have e : (11 * n₁ + 6) * p = 11 * (p * n₁) + 6 * p := by ring
    omega
  obtain ⟨d1q, d1r⟩ := digits_of_decomp hp0 hk1 (by omega)
  obtain ⟨d2q, d2r⟩ := digits_of_decomp hp0 hk2 (by omega)
  obtain ⟨d4q, d4r⟩ := digits_of_decomp hp0 hk4 (by omega)
  obtain ⟨a13q, a13r⟩ := digits_of_decomp hp0 h13 (by omega)
  obtain ⟨a9q, a9r⟩ := digits_of_decomp hp0 h9 (by omega)
  obtain ⟨a11q, a11r⟩ := digits_of_decomp hp0 h11 (by omega)
  -- the three uncarried factors' residue classes
  have c1 : ((t * p + u + 4 * n : ℕ) : ZMod p) = (u : ZMod p) + ((4 * r : ℕ) : ZMod p) := by
    rw [cast_of_decomp hk1, Nat.cast_sub (by omega : 2 * p ≤ u + 4 * r)]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have c2 : ((t * p + u + 4 * n + 1 - 2 * n - 1 : ℕ) : ZMod p)
      = (u : ZMod p) + ((2 * r : ℕ) : ZMod p) := by
    rw [cast_of_decomp hk2, Nat.cast_sub (by omega : p ≤ u + 2 * r)]
    push_cast
    rw [ZMod.natCast_self]
    ring
  -- the sign
  have hsign : (-1 : ZMod p) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
      = (-1) ^ t * ((-1) ^ (11 * r - 6 * p) * (-1) ^ (u - (11 * r - 6 * p))) := by
    have e : 12 * n + (t * p + u + 4 * n + 1) - 1
        = 2 * (8 * n) + t * p + ((11 * r - 6 * p) + (u - (11 * r - 6 * p))) := by omega
    have hp1 : (-1 : ZMod p) ^ (t * p) = (-1) ^ t := by
      rw [pow_mul' (-1 : ZMod p) t p, hodd.neg_one_pow]
    have hp2 : (-1 : ZMod p) ^ (2 * (8 * n)) = 1 := by
      rw [pow_mul (-1 : ZMod p) 2 (8 * n), neg_one_sq, one_pow]
    rw [e, pow_add, pow_add, pow_add, hp1, hp2]
    ring
  -- the fourth factor through the reflection
  have hsc := signChoose_eq (p := p) (11 * r - 6 * p) (u - (11 * r - 6 * p)) (by omega)
    (by omega)
  have c4 : ((u - (11 * r - 6 * p) : ℕ) : ZMod p)
      = (u : ZMod p) - ((11 * r - 6 * p : ℕ) : ZMod p) := Nat.cast_sub hue
  rw [c4] at hsc
  -- the third factor: one carry, Anton
  have hA := hanton u t (5 * r - 2 * p) (5 * n₁ + 2) (by omega) (by omega) htp (by omega)
  have hm : u + p * t = t * p + u + 4 * n + 1 - 4 * n - 1 := by rw [hk3, mul_comm]
  rw [hm, ← h5] at hA
  -- `p` divides the carried binomial (Kummer with one digit), so the term divides exactly
  have hdvd : p ∣ (t * p + u + 4 * n + 1 - 4 * n - 1).choose (5 * n) := by
    have hle : 5 * n ≤ t * p + u + 4 * n + 1 - 4 * n - 1 := by
      have e3 : (11 * n₁ + 6) * p ≤ t * p := Nat.mul_le_mul_right p ht
      have e : (11 * n₁ + 6) * p = 11 * (p * n₁) + 6 * p := by ring
      omega
    have hlog : Nat.log p (t * p + u + 4 * n + 1 - 4 * n - 1) ≤ 1 := by
      have hlt : t * p + u + 4 * n + 1 - 4 * n - 1 < p ^ 2 := by
        rw [hk3, pow_two]
        have h1 : (t + 1) * p ≤ p * p := Nat.mul_le_mul_right p htp
        have h2 : (t + 1) * p = t * p + p := by ring
        omega
      have hne : t * p + u + 4 * n + 1 - 4 * n - 1 ≠ 0 := by
        have e3 : (11 * n₁ + 6) * p ≤ t * p := Nat.mul_le_mul_right p ht
        have e : (11 * n₁ + 6) * p = 11 * (p * n₁) + 6 * p := by ring
        omega
      have := Nat.log_lt_of_lt_pow hne hlt
      omega
    have hv := vp_choose_eq_cb (p := p) hle hlog
    have hmod1 : (t * p + u + 4 * n + 1 - 4 * n - 1) % p = u := by
      rw [hk3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
    have hmod2 : (5 * n) % p = 5 * r - 2 * p := by
      rw [h5, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 5 * r - 2 * p < p)]
    have hcb : cb p (t * p + u + 4 * n + 1 - 4 * n - 1) (5 * n) = 1 := by
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
  have hq' : (t * p + u + 4 * n + 1 - 4 * n - 1).choose (5 * n) / p = q := by
    rw [hq, Nat.mul_div_cancel_left _ hp0]
  have hterm : (-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
      * (cTerm n (t * p + u + 4 * n + 1) : ℤ)
      = (p : ℤ) * ((-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
          * (((t * p + u + 4 * n).choose (13 * n)
              * (t * p + u + 4 * n + 1 - 2 * n - 1).choose (9 * n) * q
              * (11 * n).choose (t * p + u + 4 * n + 1 - 15 * n - 1) : ℕ) : ℤ)) := by
    rw [cTerm, hq, Nat.add_sub_cancel (n := t * p + u + 4 * n) (m := 1)]; push_cast; ring
  rw [hterm, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp0.ne')]
  push_cast
  rw [hsign, lucas_factor (t * p + u + 4 * n) (13 * n),
    lucas_factor (t * p + u + 4 * n + 1 - 2 * n - 1) (9 * n),
    lucas_raw (11 * n) (t * p + u + 4 * n + 1 - 15 * n - 1),
    d1q, d2q, d4q, d4r, a13q, a13r, a9q, a9r, a11q, a11r, c1, c2, ← hq', hA,
    factorial_inv_eq_denTop (by omega : u < 5 * r - 2 * p) (by omega : 5 * r - 2 * p < p)]
  rw [runPoly2_eval_of_lt hr hlo hhi (by omega)]
  unfold kappa2 numer
  simp only [eval_mul, eval_comp, eval_add, eval_sub, eval_X, eval_C]
  rw [← hsc]
  ring

end Run

/-! ## 3. The block congruence on `[5/9, 9/16)`, at every block -/

section Block
variable {p : ℕ} [hp : Fact p.Prime]

theorem sq_dvd_cTerm_of_not_run {n n₁ r t u : ℕ} (hp' : p ∈ phiWindow n)
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p) (hu : u < p)
    (hk : t * p + u + 4 * n + 1 ∈ candidateM.window n)
    (hnot : ¬ (11 * r - 6 * p ≤ u ∧ u ≤ 2 * (11 * r - 6 * p))) :
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
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p) (hu : u < p)
    (hk : t * p + u + 4 * n + 1 ∈ candidateM.window n) :
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

/-- **THE BLOCK CONGRUENCE ON `[5/9, 9/16)` AT EVERY BLOCK, conditional on Anton.** -/
theorem blockSum_dvd_sq (hanton : Zeta2PtpS2a.AntonOneCarry p) {n : ℕ} (hp' : p ∈ phiWindow n)
    (hlo : 5 * p ≤ 9 * (n % p)) (hhi : 16 * (n % p) < 9 * p) (t : ℕ) :
    (p : ℤ) ^ 2 ∣ blockSum n p t := by
  have hp0 := hp.out.pos
  have hn : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hr : n % p < p := Nat.mod_lt _ hp0
  generalize n / p = n₁ at hn
  generalize n % p = r at hn hr hlo hhi
  have hzero : (∀ u < p, t * p + u + 4 * n + 1 ∉ candidateM.window n) →
      (p : ℤ) ^ 2 ∣ blockSum n p t := by
    intro hoff
    rw [blockSum_eq_sum_range hp0 t]
    have hz : ∀ u ∈ Finset.range p,
        (if t * p + u + 4 * n + 1 ∈ candidateM.window n
          then (-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
                * (cTerm n (t * p + u + 4 * n + 1) : ℤ)
          else 0) = 0 := by
      intro u hu
      split_ifs with hmem
      · exact absurd hmem (hoff u (Finset.mem_range.mp hu))
      · rfl
    rw [Finset.sum_eq_zero hz]
    exact dvd_zero _
  rcases Nat.lt_or_ge t (11 * n₁ + 6) with hlt | hge
  · refine hzero fun u hu hmem => ?_
    rw [mem_window_iff] at hmem
    have e1 : (t + 1) * p ≤ (11 * n₁ + 6) * p := Nat.mul_le_mul_right p (by omega)
    have e2 : (t + 1) * p = t * p + p := by ring
    have e3 : (11 * n₁ + 6) * p = 11 * (p * n₁) + 6 * p := by ring
    omega
  rcases Nat.lt_or_ge (22 * n₁ + 12) t with hgt | hle
  · refine hzero fun u hu hmem => ?_
    rw [mem_window_iff] at hmem
    have e1 : (22 * n₁ + 13) * p ≤ t * p := Nat.mul_le_mul_right p (by omega)
    have e3 : (22 * n₁ + 13) * p = 22 * (p * n₁) + 13 * p := by ring
    omega
  have htp : t < p := by
    have hk : 26 * n + 1 ∈ candidateM.window n := (mem_window_iff n _).2 ⟨by omega, le_rfl⟩
    have hb := block_lt hp' hk
    have e : 26 * n + 1 - 4 * n - 1 = 22 * n := by omega
    rw [e] at hb
    have e2 : (22 * n₁ + 12) * p ≤ 22 * n := by
      have : (22 * n₁ + 12) * p = 22 * (p * n₁) + 12 * p := by ring
      omega
    have : 22 * n₁ + 12 ≤ 22 * n / p := (Nat.le_div_iff_mul_le hp0).2 e2
    omega
  refine blockSum_sq_dvd_of_poly t (kappa2 p n₁ r t) (runPoly2 p r)
    (runPoly2_natDegree_le hr hlo hhi) ?_ ?_
  · intro u hu
    split_ifs with hmem
    · have h := dvd_cTerm_of_stratum hp' hn hr hlo hhi hu hmem
      exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 h) _
    · exact dvd_zero _
  · intro u hu
    by_cases hrun : 11 * r - 6 * p ≤ u ∧ u ≤ 2 * (11 * r - 6 * p)
    · obtain ⟨hue, hu2⟩ := hrun
      have hmem : t * p + u + 4 * n + 1 ∈ candidateM.window n := by
        rw [mem_window_iff]
        have e1 : (11 * n₁ + 6) * p ≤ t * p := Nat.mul_le_mul_right p (by omega)
        have e2 : t * p ≤ (22 * n₁ + 12) * p := Nat.mul_le_mul_right p (by omega)
        have e3 : (11 * n₁ + 6) * p = 11 * (p * n₁) + 6 * p := by ring
        have e4 : (22 * n₁ + 12) * p = 22 * (p * n₁) + 12 * p := by ring
        constructor <;> omega
      split_ifs
      exact term_div_eq_of_run hanton hn hr hlo hhi hu hue hu2 (by omega) htp
    · have hQ : (runPoly2 p r).eval (u : ZMod p) = 0 := by
        rcases Nat.lt_or_ge u (5 * r - 2 * p) with hcu | hcu
        · rw [runPoly2_eval_of_lt hr hlo hhi hcu]
          have hN : (numer p r).eval (u : ZMod p) = 0 := by
            unfold numer
            simp only [eval_mul]
            by_cases hb4 : 11 * r - 6 * p < (u + (p - (11 * r - 6 * p))) % p
            · have := root4 hr hlo hhi hb4
              rw [IsRoot.def] at this
              rw [this, mul_zero]
            · by_cases hb1 : (u + 4 * r) % p < 13 * r - 7 * p
              · have := root1 hr hlo hhi hb1
                rw [IsRoot.def] at this
                rw [this, zero_mul, zero_mul]
              · exfalso
                apply hrun
                have h4 : (u + (p - (11 * r - 6 * p))) % p
                    = if u + (p - (11 * r - 6 * p)) < p then u + (p - (11 * r - 6 * p))
                      else u + (p - (11 * r - 6 * p)) - p := add_mod_split hu (by omega)
                obtain ⟨h1, _⟩ := wraps hu hr hlo hhi
                rw [h4] at hb4
                rw [h1] at hb1
                split_ifs at hb4 hb1 <;> omega
          rw [hN, zero_mul]
        · exact runPoly2_eval_zero_of_ge hu hr hlo hhi hcu
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

/-! ## 4. The φ̃ wire on piece 16, and the piece for the harmonic side -/

theorem phiT_piece16 {x : ℚ} (h1 : 6 / 11 ≤ x) (h2 : x < 9 / 16) : phiT x = 2 := by
  have h := phiT_of_mem (a := 6 / 11) (b := 9 / 16) (v := 2) (by decide +kernel) h1 h2
  exact h

theorem phiT_piece16_res {n p : ℕ} (hp : 0 < p) (hlo : 6 * p ≤ 11 * (n % p))
    (hhi : 16 * (n % p) < 9 * p) : phiT (Int.fract ((n : ℚ) / (p : ℚ))) = 2 := by
  refine phiT_piece16 ?_ ?_
  · have h := (fract_ge_iff n p 6 11 hp (by norm_num)).2 (by omega)
    exact_mod_cast h
  · have h := (fract_lt_iff n p 9 16 hp (by norm_num)).2 (by omega)
    exact_mod_cast h

/-- **PROFILE PIECE 16 `[6/11, 9/16)` FOR THE HARMONIC SIDE, conditional on Anton**: the run-free
stratum `[6/11, 5/9)` through `Zeta2PtpCong.noShort_S6`, the run stratum through
`blockSum_dvd_sq`. -/
theorem piece16_blocks {p n : ℕ} [Fact p.Prime] (hanton : Zeta2PtpS2a.AntonOneCarry p)
    (hp : p ∈ phiWindow n) (hlo : 6 * p ≤ 11 * (n % p)) (hhi : 16 * (n % p) < 9 * p) (t : ℕ) :
    (p : ℤ) ^ (phiT (Int.fract ((n : ℚ) / (p : ℚ)))) ∣ blockSum n p t := by
  have hp0 := (prime_of_mem_phiWindow hp).pos
  rw [phiT_piece16_res hp0 hlo hhi]
  rcases Nat.lt_or_ge (9 * (n % p)) (5 * p) with h9 | h9
  · exact blockSum_dvd_of_noShort hp (Zeta2PtpCong.noShort_S6 hp0 hlo h9) t
  · exact blockSum_dvd_sq hanton hp h9 hhi t

/-- The stratum is inhabited by the ZERO-MARGIN cell of the sixth pass: `n = 23`, `p = 41`,
`r = 23` (`23/41 ∈ [5/9, 9/16)`, `D = p − 2` exactly there). -/
theorem witness_23_41 :
    41 ∈ phiWindow 23 ∧ 5 * 41 ≤ 9 * (23 % 41) ∧ 16 * (23 % 41) < 9 * 41 := by
  refine ⟨by decide +kernel, by decide, by decide⟩

end Zeta2PtpS2b

#print axioms Zeta2PtpS2b.numer_natDegree_le
#check @Zeta2PtpS2b.numer_natDegree_le
#print axioms Zeta2PtpS2b.wraps
#check @Zeta2PtpS2b.wraps
#print axioms Zeta2PtpS2b.two_of_three
#check @Zeta2PtpS2b.two_of_three
#print axioms Zeta2PtpS2b.bits_ge
#check @Zeta2PtpS2b.bits_ge
#print axioms Zeta2PtpS2b.denTop_dvd_numer
#check @Zeta2PtpS2b.denTop_dvd_numer
#print axioms Zeta2PtpS2b.runPoly2_eval_zero_of_ge
#check @Zeta2PtpS2b.runPoly2_eval_zero_of_ge
#print axioms Zeta2PtpS2b.runPoly2_natDegree_le
#check @Zeta2PtpS2b.runPoly2_natDegree_le
#print axioms Zeta2PtpS2b.term_div_eq_of_run
#check @Zeta2PtpS2b.term_div_eq_of_run
#print axioms Zeta2PtpS2b.blockSum_dvd_sq
#check @Zeta2PtpS2b.blockSum_dvd_sq
#print axioms Zeta2PtpS2b.phiT_piece16
#check @Zeta2PtpS2b.phiT_piece16
#print axioms Zeta2PtpS2b.piece16_blocks
#check @Zeta2PtpS2b.piece16_blocks
#print axioms Zeta2PtpS2b.witness_23_41
#check @Zeta2PtpS2b.witness_23_41
