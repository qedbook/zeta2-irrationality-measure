/-
# Row PT-P, layer 17 — the φ̃ = 2 QUOTIENT block lemma for the polynomial half's polar rows below
# `p²`, in `i`-blocks, for both halves of `h_m` and both carried factors

On a φ̃ = 2 run stratum every term of `h_m = Σ_i (−1)^{m−i} C(m,i) H(i)` at a polar row below `p²`
carries at least one units carry, and the terms carrying exactly one carry it in ONE factor `k*`
(`ptp_resid_narrow_probe.out`, and the per-block census in its notes): the third block `C(22n−i, 5n)`
/ `C(i−17n−1, 5n)` on `[1/9, 2/17)` and `[5/9, 9/16)`, the binomial `C(m, i)` itself on `[6/13,
7/15)` and `[12/13, 14/15)`.  So `p² ∣ block` needs `Σ_{u<p} term(u)/p ≡ 0 (mod p)`, and — exactly
as the harmonic side's `Zeta2PtpS2Kit` does in its own block coordinate — `term/p` is a QUOTIENT
`κ_t · N(u) / Den(u)`:

* Anton's one-carry unit part (`Zeta2Anton.choose_div_p_modEq_of_one_carry`) on the carried factor
  gives the reciprocal: for a carried top `S₀!/(S₀+p−A₀)!` is `denTop(S₀)⁻¹`, and `S₀ ≡ c − u`
  (LO) or `u − c` (TAIL) makes it `Den(u)⁻¹` over `rootsDown` / `rootsUp`; for the carried
  `C(m, i)` Wilson's reflection twice (`Zeta2PtpS2Kit.factorial_inv_eq_denLow`) gives
  `(u(u−1)⋯(u−m₀))⁻¹`, `rootsLow`;
* `N` is the other three factors' units digits as polynomials — the reflected `C(m mod p, u)`
  (`signChoosePoly`) and `binPoly`s of `c − u` / `u − c`;
* the roots of `Den` are where `k*` does NOT carry, and there two OTHER factors carry, so `N` has a
  double root and the quotient `N /ₘ Den` vanishes (`quot_eval_zero_of_double`) exactly where
  `term/p ≡ 0`.

`sq_dvd_of_quot` is the abstract lemma; `lo3_block_dvd` / `hi3_block_dvd` / `lo4_block_dvd` /
`hi4_block_dvd` are its four instances, each with the stratum's residue facts as hypotheses
(`hone`: every residue carries; `htwo`: a residue where `k*` does not carry carries twice; `hsup`:
on the one-carry set the block has no truncated top and fixed high digits) — a stratum discharges
them by `omega` (`Zeta2PtpRunS2`).  `*_block_zero` / `*_block_past` / `hi3_block_low` / `*_all_zero`
cover the blocks whose one-carry terms vanish outright.

WHAT IS NOT HERE.  No stratum; nothing at `m ≥ p²`.  Row PT-P does not close and
`Zeta2Target.zeta2_not_liouvilleWith` is `sorry`.

Runner: `run_resid.sh`.  Falsifier: `falsify_ptpruns2.sh` / `out_ptpruns2_falsify.txt`.

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
import Zeta2PtpKumRes
import Zeta2PtpRunBlock
import Zeta2PtpS2Kit
import Zeta2Anton

set_option maxRecDepth 20000

namespace Zeta2PtpRunG2

open Zeta2PtpBlock Zeta2PtpS7 Zeta2PtpRunBlock Zeta2PtpS2Kit Finset Polynomial

section G2
variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Carries, in residues -/

/-- The LO units carries of the four factors of a term at residue `u`. -/
def cLo1 (p n u : ℕ) : Prop := ((26 * n) % p + p - u) % p < (13 * n) % p
def cLo2 (p n u : ℕ) : Prop := ((24 * n) % p + p - u) % p < (9 * n) % p
def cLo3 (p n u : ℕ) : Prop := ((22 * n) % p + p - u) % p < (5 * n) % p
def c4 (p m u : ℕ) : Prop := m % p < u

/-- `(c − (tp+u)) mod p` is the wrapped residue, without truncation. -/
theorem mod_sub_block {c t u : ℕ} (h : t * p + u ≤ c) (hu : u < p) :
    (c - (t * p + u)) % p = ((c % p) + p - u) % p := by
  have h1 : ((c - (t * p + u) : ℕ) : ZMod p) = ((((c % p) + p - u) % p : ℕ) : ZMod p) := by
    rw [cast_sub_block h, cast_wrap c u hu.le]
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
  rwa [Nat.mod_mod] at h2

/-- A carried top binomial is a multiple of `p` — by Lucas, or it is `0` (truncated). -/
theorem dvd_choose_of_carry {c t u B : ℕ} (hu : u < p) (hB : 0 < B)
    (hc : ((c % p) + p - u) % p < B % p) : p ∣ (c - (t * p + u)).choose B := by
  rw [← ZMod.natCast_eq_zero_iff]
  by_cases h : t * p + u ≤ c
  · rw [lucas_factor, cast_sub_block h, binPoly_eval_wrap _ _ _ hu.le (Nat.mod_lt _ hp.out.pos),
      Nat.choose_eq_zero_of_lt hc]
    simp
  · rw [show c - (t * p + u) = 0 by omega, Nat.choose_eq_zero_of_lt hB]
    simp

/-- A carried `C(m, i)` is a multiple of `p`. -/
theorem dvd_choose_m_of_carry {m t u : ℕ} (hu : u < p) (hc : m % p < u) :
    p ∣ m.choose (t * p + u) := by
  rw [← ZMod.natCast_eq_zero_iff, lucas_raw]
  have hmod : (t * p + u) % p = u := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  rw [hmod, Nat.choose_eq_zero_of_lt hc]
  simp

omit hp in
/-- `(a + p − u) % p` for `a, u < p`, as one comparison. -/
theorem wrap_mod_down {a u : ℕ} (hu : u < p) (ha : a < p) :
    (a + p - u) % p = if u ≤ a then a - u else a + p - u := by
  split_ifs with h
  · rw [show a + p - u = (a - u) + p by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · exact Nat.mod_eq_of_lt (by omega)

/-! ### Root sets: where a carried factor does NOT carry -/

/-- `linProd` over a mapped `range`, as a `Finset` product. -/
theorem linProd_range_eval (K : ℕ) (f : ℕ → ZMod p) (x : ZMod p) :
    (linProd ((Finset.range K).val.map f)).eval x = ∏ j ∈ Finset.range K, (x - f j) := by
  rw [linProd_eval, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

/-- Residues `c + 1, …, c + (p − A)`: where a DECREASING top `c − u` has units digit `≥ A`. -/
noncomputable def rootsDown (p c A : ℕ) : Multiset (ZMod p) :=
  (Finset.range (p - A)).val.map fun j : ℕ => ((c : ℕ) : ZMod p) + ((j + 1 : ℕ) : ZMod p)

/-- Residues `c − 1, …, c − (p − A)`: where an INCREASING top `u − c` has units digit `≥ A`. -/
noncomputable def rootsUp (p c A : ℕ) : Multiset (ZMod p) :=
  (Finset.range (p - A)).val.map fun j : ℕ => ((c : ℕ) : ZMod p) - ((j + 1 : ℕ) : ZMod p)

/-- Residues `0, …, e`: where `C(e, u)` does not vanish, i.e. `u ≤ e`. -/
noncomputable def rootsLow (p e : ℕ) : Multiset (ZMod p) :=
  (Finset.range (e + 1)).val.map fun j : ℕ => ((j : ℕ) : ZMod p)

omit hp in
theorem rootsDown_card (c A : ℕ) : Multiset.card (rootsDown p c A) = p - A := by
  unfold rootsDown; rw [Multiset.card_map, Finset.card_val, Finset.card_range]

omit hp in
theorem rootsUp_card (c A : ℕ) : Multiset.card (rootsUp p c A) = p - A := by
  unfold rootsUp; rw [Multiset.card_map, Finset.card_val, Finset.card_range]

omit hp in
theorem rootsLow_card (e : ℕ) : Multiset.card (rootsLow p e) = e + 1 := by
  unfold rootsLow; rw [Multiset.card_map, Finset.card_val, Finset.card_range]

theorem rootsDown_nodup (c : ℕ) {A : ℕ} (hA : 0 < A) : (rootsDown p c A).Nodup := by
  refine Multiset.Nodup.map_on ?_ (Finset.range (p - A)).nodup
  intro i hi j hj hij
  rw [Finset.mem_val, Finset.mem_range] at hi hj
  have h1 := add_left_cancel hij
  have h := ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).eq_of_lt_of_lt (by omega) (by omega)
  omega

theorem rootsUp_nodup (c : ℕ) {A : ℕ} (hA : 0 < A) : (rootsUp p c A).Nodup := by
  refine Multiset.Nodup.map_on ?_ (Finset.range (p - A)).nodup
  intro i hi j hj hij
  rw [Finset.mem_val, Finset.mem_range] at hi hj
  have h1 := sub_right_injective hij
  have h := ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).eq_of_lt_of_lt (by omega) (by omega)
  omega

theorem rootsLow_nodup {e : ℕ} (he : e < p) : (rootsLow p e).Nodup := by
  refine Multiset.Nodup.map_on ?_ (Finset.range (e + 1)).nodup
  intro i hi j hj hij
  rw [Finset.mem_val, Finset.mem_range] at hi hj
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).1 hij).eq_of_lt_of_lt (by omega) (by omega)

/-- **`u ∈ rootsDown c A` iff the decreasing top does NOT carry against `A`.** -/
theorem mem_rootsDown {c A u : ℕ} (hu : u < p) (hA : A ≤ p) :
    (u : ZMod p) ∈ rootsDown p c A ↔ ¬ ((c % p) + p - u) % p < A := by
  have hp0 := hp.out.pos
  have hR := Nat.mod_lt c hp0
  have hw := wrap_mod_down hu hR
  unfold rootsDown
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨j, hj, hju⟩
    rw [Finset.mem_val, Finset.mem_range] at hj
    have hc : (((c % p) + j + 1 : ℕ) : ZMod p) = (u : ZMod p) := by
      rw [← hju, Nat.cast_add, Nat.cast_add, ZMod.natCast_mod, add_assoc, ← Nat.cast_one,
        ← Nat.cast_add]
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hc
    rw [Nat.mod_eq_of_lt hu] at hmod
    intro hlt
    rw [hw] at hlt
    rcases Nat.lt_or_ge ((c % p) + j + 1) p with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at hmod
      split_ifs at hlt <;> omega
    · have e : ((c % p) + j + 1) % p = (c % p) + j + 1 - p := by
        rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
      rw [e] at hmod
      split_ifs at hlt <;> omega
  · intro hnot
    rw [hw] at hnot
    refine ⟨p - 1 - ((c % p) + p - u) % p, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_range, hw]
      split_ifs at hnot ⊢ <;> omega
    · rw [hw]
      have e : ∀ S : ℕ, S < p → ((c : ℕ) : ZMod p) + ((p - 1 - S + 1 : ℕ) : ZMod p)
          = ((c : ℕ) : ZMod p) - (S : ZMod p) := by
        intro S hS
        rw [show p - 1 - S + 1 = p - S by omega, Nat.cast_sub hS.le, ZMod.natCast_self]
        ring
      split_ifs with h
      · rw [e _ (by omega), Nat.cast_sub h, ← ZMod.natCast_mod c p]
        ring
      · rw [e _ (by omega), Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
          ZMod.natCast_mod]
        ring

/-- **`u ∈ rootsUp c A` iff the increasing top does NOT carry against `A`.** -/
theorem mem_rootsUp {c A u : ℕ} (hu : u < p) (hA : A ≤ p) :
    (u : ZMod p) ∈ rootsUp p c A ↔ ¬ (u + p - c % p) % p < A := by
  have hp0 := hp.out.pos
  have hR := Nat.mod_lt c hp0
  have hw := Zeta2PtpRunBlock.wrap_mod_up hu hR
  unfold rootsUp
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨j, hj, hju⟩
    rw [Finset.mem_val, Finset.mem_range] at hj
    -- `u + j + 1 ≡ c`
    have hc : ((u + j + 1 : ℕ) : ZMod p) = ((c % p : ℕ) : ZMod p) := by
      rw [ZMod.natCast_mod]
      push_cast at hju ⊢
      linear_combination -hju
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hc
    rw [Nat.mod_mod] at hmod
    intro hlt
    rw [hw] at hlt
    rcases Nat.lt_or_ge (u + j + 1) p with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at hmod
      split_ifs at hlt <;> omega
    · have e : (u + j + 1) % p = u + j + 1 - p := by
        rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
      rw [e] at hmod
      split_ifs at hlt <;> omega
  · intro hnot
    rw [hw] at hnot
    refine ⟨p - 1 - (u + p - c % p) % p, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_range, hw]
      split_ifs at hnot ⊢ <;> omega
    · rw [hw]
      have e : ∀ S : ℕ, S < p → ((c : ℕ) : ZMod p) - ((p - 1 - S + 1 : ℕ) : ZMod p)
          = ((c : ℕ) : ZMod p) + (S : ZMod p) := by
        intro S hS
        rw [show p - 1 - S + 1 = p - S by omega, Nat.cast_sub hS.le, ZMod.natCast_self]
        ring
      split_ifs with h
      · rw [e _ (by omega), Nat.cast_sub h, ← ZMod.natCast_mod c p]
        ring
      · rw [e _ (by omega), Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
          ZMod.natCast_mod]
        ring

theorem mem_rootsLow {e u : ℕ} (hu : u < p) (he : e < p) :
    (u : ZMod p) ∈ rootsLow p e ↔ u ≤ e := by
  unfold rootsLow
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨j, hj, hju⟩
    rw [Finset.mem_val, Finset.mem_range] at hj
    have := ((ZMod.natCast_eq_natCast_iff _ _ _).1 hju).eq_of_lt_of_lt (by omega) hu
    omega
  · intro h
    exact ⟨u, by rw [Finset.mem_val, Finset.mem_range]; omega, rfl⟩

/-- The decreasing denominator IS `denTop` at `c − u`, up to `(−1)^{p−A}`. -/
theorem rootsDown_eval (c A : ℕ) (x : ZMod p) :
    (linProd (rootsDown p c A)).eval x
      = (-1) ^ (p - A) * (denTop p A).eval ((c : ZMod p) - x) := by
  unfold denTop topRoots rootsDown
  rw [show (-1 : ZMod p) ^ (p - A) = ∏ _j ∈ Finset.range (p - A), (-1 : ZMod p) by simp,
    linProd_range_eval, linProd_range_eval, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

/-- The increasing denominator IS `denTop` at `u − c`. -/
theorem rootsUp_eval (c A : ℕ) (x : ZMod p) :
    (linProd (rootsUp p c A)).eval x = (denTop p A).eval (x - (c : ZMod p)) := by
  unfold denTop topRoots rootsUp
  rw [linProd_range_eval, linProd_range_eval]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

/-- The low denominator at `u > e` is `u(u−1)⋯(u−e)`. -/
theorem rootsLow_eval {e u : ℕ} (h : e < u) :
    (linProd (rootsLow p e)).eval (u : ZMod p) = ((u.descFactorial (e + 1) : ℕ) : ZMod p) := by
  unfold rootsLow
  rw [linProd_range_eval, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Nat.cast_sub (by omega)]

/-! ### The abstract quotient block lemma -/

/-- **`p² ∣ Σ_{u<p} g u` from a quotient identity.**  Every `g u` is a multiple of `p`; at a root
`u ∈ s` the quotient `g u / p` vanishes and `N` has a DOUBLE root; off the roots
`g u / p ≡ κ · N(u) / Den(u)`; and `deg N ≤ p − 2 + card s`. -/
theorem sq_dvd_of_quot (g : ℕ → ℤ) (κ : ZMod p) (N : (ZMod p)[X]) (s : Multiset (ZMod p))
    (hs : s.Nodup) (hdeg : N.natDegree ≤ p - 2 + Multiset.card s)
    (hdiv : ∀ u < p, (p : ℤ) ∣ g u)
    (hroot : ∀ u < p, (u : ZMod p) ∈ s →
      ((g u / (p : ℤ) : ℤ) : ZMod p) = 0 ∧ (X - C (u : ZMod p)) ^ 2 ∣ N)
    (hoff : ∀ u < p, (u : ZMod p) ∉ s →
      ((g u / (p : ℤ) : ℤ) : ZMod p) = κ * (N.eval (u : ZMod p) * ((linProd s).eval (u : ZMod p))⁻¹)) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, g u := by
  have hdbl : ∀ a ∈ s, (X - C a) ^ 2 ∣ N := by
    intro a ha
    have h := (hroot a.val (ZMod.val_lt a) (by rwa [ZMod.natCast_zmod_val])).2
    rwa [ZMod.natCast_zmod_val] at h
  have hd : linProd s ∣ N := linProd_dvd_of_roots' hs fun a ha =>
    dvd_iff_isRoot.1 ((dvd_pow_self (X - C a) two_ne_zero).trans (hdbl a ha))
  refine sq_dvd_sum_of_poly g κ (quot N s) ?_ hdiv fun u hu => ?_
  · rw [quot_natDegree]; omega
  · by_cases hm : (u : ZMod p) ∈ s
    · rw [(hroot u hu hm).1, quot_eval_zero_of_double hd hs hm (hdbl _ hm), mul_zero]
    · rw [hoff u hu hm, quot_eval_of_not_mem hd hm]

/-! ### LO, carried THIRD factor `C(22n − i, 5n)` — the `I3` strata -/

/-- The three uncarried LO factors: the reflected `C(m mod p, u)` and the first two blocks. -/
noncomputable def Nlo3 (p n m : ℕ) : (ZMod p)[X] :=
  signChoosePoly p (m % p)
    * (binPoly p ((13 * n) % p)).comp (C ((26 * n : ℕ) : ZMod p) - X)
    * (binPoly p ((9 * n) % p)).comp (C ((24 * n : ℕ) : ZMod p) - X)

/-- The block constant: sign, the three high-digit binomials, and Anton's `u`-free part. -/
noncomputable def kLo3 (p n m t h1 h2 h3 : ℕ) : ZMod p :=
  (-1) ^ (m + t) * (((m / p).choose t : ℕ) : ZMod p)
    * ((h1.choose (13 * n / p) : ℕ) : ZMod p) * ((h2.choose (9 * n / p) : ℕ) : ZMod p)
    * (-(((Nat.factorial ((5 * n) % p) : ℕ) : ZMod p))⁻¹ * (-1) ^ (p - (5 * n) % p))
    * (((Nat.factorial h3 : ℕ) : ZMod p) * (((Nat.factorial (5 * n / p) : ℕ) : ZMod p))⁻¹
        * (((Nat.factorial (h3 - 1 - 5 * n / p) : ℕ) : ZMod p))⁻¹)

theorem Nlo3_natDegree_le (n m : ℕ) :
    (Nlo3 p n m).natDegree ≤ (p - 1 - m % p) + (13 * n) % p + (9 * n) % p := by
  unfold Nlo3
  exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le
    (signChoosePoly_natDegree_le _) (natDegree_comp_sub_le _ _)) (natDegree_comp_sub_le _ _)

theorem Tlo_def (n m i : ℕ) :
    Tlo n m i = (-1 : ℤ) ^ (m + i) * ((m.choose i : ℕ) : ℤ)
      * (((26 * n - i).choose (13 * n) : ℕ) : ℤ) * (((24 * n - i).choose (9 * n) : ℕ) : ℤ)
      * (((22 * n - i).choose (5 * n) : ℕ) : ℤ) := by
  unfold Tlo; push_cast; ring

/-- **The LO identity on the one-carry set of the third factor** (Lucas on three factors, Anton on
the third, Wilson's reflection on `C(m, i)`). -/
theorem Tlo_div_eq_lo3 (hp2 : 2 < p) {n m t u h1 h2 h3 : ℕ} (hn : 1 ≤ n) (hu : u < p)
    (hc3 : ((22 * n) % p + p - u) % p < (5 * n) % p) (htr : t * p + u ≤ 22 * n) (e1 : (26 * n - (t * p + u)) / p = h1)
    (e2 : (24 * n - (t * p + u)) / p = h2) (e3 : (22 * n - (t * p + u)) / p = h3)
    (hh3 : 5 * n / p < h3) (h3p : h3 < p) :
    ((Tlo n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p)
      = kLo3 p n m t h1 h2 h3 * ((Nlo3 p n m).eval (u : ZMod p)
          * ((linProd (rootsDown p (22 * n) ((5 * n) % p))).eval (u : ZMod p))⁻¹) := by
  have hp0 := hp.out.pos
  have hA0 := Nat.mod_lt (5 * n) hp0
  have hj13 := Nat.mod_lt (13 * n) hp0
  have hj9 := Nat.mod_lt (9 * n) hp0
  have hm0 : m % p < p := Nat.mod_lt _ hp0
  have hdiv : (t * p + u) / p = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hu, zero_add]
  have hmod : (t * p + u) % p = u := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  set S0 := ((22 * n) % p + p - u) % p with hS0
  -- Anton on the third factor
  have hS : 22 * n - (t * p + u) = S0 + p * h3 := by
    rw [← e3, hS0, ← mod_sub_block htr hu, Nat.mod_add_div]
  have hA : 5 * n = (5 * n) % p + p * (5 * n / p) := (Nat.mod_add_div _ _).symm
  have hanton := Zeta2Anton.choose_div_p_modEq_of_one_carry p S0 h3 ((5 * n) % p) (5 * n / p)
    hc3 hA0 h3p hh3
  rw [← hS, ← hA] at hanton
  have hdvd : p ∣ (22 * n - (t * p + u)).choose (5 * n) :=
    dvd_choose_of_carry (c := 22 * n) hu (by omega) hc3
  obtain ⟨q, hq⟩ := hdvd
  have hq' : (22 * n - (t * p + u)).choose (5 * n) / p = q := by
    rw [hq, Nat.mul_div_cancel_left _ hp0]
  rw [hq'] at hanton
  -- the exact division
  have hT : Tlo n m (t * p + u) = (p : ℤ) * ((-1 : ℤ) ^ (m + (t * p + u))
      * ((m.choose (t * p + u) : ℕ) : ℤ) * (((26 * n - (t * p + u)).choose (13 * n) : ℕ) : ℤ)
      * (((24 * n - (t * p + u)).choose (9 * n) : ℕ) : ℤ) * (q : ℤ)) := by
    rw [Tlo_def, hq]; push_cast; ring
  rw [hT, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp0.ne')]
  -- Anton's reciprocal as the denominator
  have hden := factorial_inv_eq_denTop (p := p) (u := S0) (c := (5 * n) % p) hc3 hA0
  have hS0c : ((S0 : ℕ) : ZMod p) = ((22 * n : ℕ) : ZMod p) - (u : ZMod p) := by
    rw [hS0]; exact cast_wrap _ _ hu.le
  rw [hS0c] at hden
  have hsq : ((-1 : ZMod p) ^ (p - (5 * n) % p)) * (-1) ^ (p - (5 * n) % p) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hinv : (((-1 : ZMod p) ^ (p - (5 * n) % p)))⁻¹ = (-1) ^ (p - (5 * n) % p) := by
    rw [← inv_pow, inv_neg, inv_one]
  have hD : (denTop p ((5 * n) % p)).eval (((22 * n : ℕ) : ZMod p) - (u : ZMod p))
      = (-1) ^ (p - (5 * n) % p)
        * (linProd (rootsDown p (22 * n) ((5 * n) % p))).eval (u : ZMod p) := by
    rw [rootsDown_eval, ← mul_assoc, hsq, one_mul]
  rw [hD, mul_inv, hinv] at hden
  push_cast
  rw [sign_block hp2, lucas_raw m (t * p + u), hdiv, hmod,
    lucas_factor (26 * n - (t * p + u)) (13 * n), lucas_factor (24 * n - (t * p + u)) (9 * n),
    e1, e2, cast_sub_block (by omega), cast_sub_block (by omega), hanton, hden]
  unfold kLo3 Nlo3
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X]
  rw [← signChoose_eq (m % p) u hm0 hu]
  ring


omit hp in
theorem dvd_prod4 {a b c d : ℕ} (h : p ∣ a ∨ p ∣ b ∨ p ∣ c ∨ p ∣ d) : p ∣ a * (b * c * d) := by
  rcases h with h | h | h | h
  · exact h.mul_right _
  · exact (h.mul_right _ |>.mul_right _).mul_left _
  · exact ((h.mul_left _).mul_right _).mul_left _
  · exact (h.mul_left _).mul_left _

omit hp in
theorem sq_dvd_prod4 {a b c d : ℕ}
    (h : (p ∣ a ∧ p ∣ b) ∨ (p ∣ a ∧ p ∣ c) ∨ (p ∣ a ∧ p ∣ d) ∨ (p ∣ b ∧ p ∣ c)
      ∨ (p ∣ b ∧ p ∣ d) ∨ (p ∣ c ∧ p ∣ d)) : p ^ 2 ∣ a * (b * c * d) := by
  rw [pow_two]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨c * d, by ring⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨b * d, by ring⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨b * c, by ring⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨a * d, by ring⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨a * c, by ring⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨a * b, by ring⟩

theorem Tlo_nat (n m i : ℕ) :
    Tlo n m i = (-1 : ℤ) ^ (m + i) * ((m.choose i * ((26 * n - i).choose (13 * n)
      * (24 * n - i).choose (9 * n) * (22 * n - i).choose (5 * n)) : ℕ) : ℤ) := by
  unfold Tlo; push_cast; ring

theorem cast_div_zero_of_sq {z : ℤ} (h : (p : ℤ) ^ 2 ∣ z) : ((z / (p : ℤ) : ℤ) : ZMod p) = 0 := by
  obtain ⟨q, hq⟩ := h
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [hq, pow_two, mul_assoc, Int.mul_ediv_cancel_left _ hp0]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- `binPoly(B mod p)` at `c − u` vanishes exactly where the decreasing top carries. -/
theorem binPoly_down_isRoot {c B u : ℕ} (hu : u < p) (h : ((c % p) + p - u) % p < B % p) :
    ((binPoly p (B % p)).comp (C ((c : ℕ) : ZMod p) - X)).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_sub, eval_C, eval_X,
    binPoly_eval_wrap _ _ _ hu.le (Nat.mod_lt _ hp.out.pos), Nat.choose_eq_zero_of_lt h,
    Nat.cast_zero]

/-- The reflected `C(m mod p, u)` vanishes exactly where `C(m, i)` carries. -/
theorem signChoose_isRoot {m u : ℕ} (hu : u < p) (h : m % p < u) :
    (signChoosePoly p (m % p)).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, ← signChoose_eq (m % p) u (Nat.mod_lt _ hp.out.pos) hu,
    Nat.choose_eq_zero_of_lt h]
  simp

theorem isRoot_mul_left' {f g : (ZMod p)[X]} {a : ZMod p} (h : f.IsRoot a) : (f * g).IsRoot a := by
  rw [IsRoot.def, eval_mul, IsRoot.def.1 h, zero_mul]

theorem isRoot_mul_right' {f g : (ZMod p)[X]} {a : ZMod p} (h : g.IsRoot a) : (f * g).IsRoot a := by
  rw [IsRoot.def, eval_mul, IsRoot.def.1 h, mul_zero]

/-- **THE LO BLOCK LEMMA, φ̃ = 2, carried third factor.**  If every residue carries at least once,
every residue where the third factor does not carry carries twice among the other three, and on
the one-carry set of the third factor the block has fixed high digits with `A₁ < h₃ < p`, then
`p² ∣ Σ_{u<p} Tlo(tp + u)` — provided the quotient's degree is `≤ p − 2`. -/
theorem lo3_block_dvd_of {n m t : ℕ} (hn : 1 ≤ n)
    (hdeg : (p - 1 - m % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ 2 * p - 2)
    (hA0 : 0 < (5 * n) % p)
    (hone : ∀ u < p, cLo1 p n u ∨ cLo2 p n u ∨ cLo3 p n u ∨ c4 p m u)
    (htwo : ∀ u < p, ¬ cLo3 p n u →
      (cLo1 p n u ∧ cLo2 p n u) ∨ (cLo1 p n u ∧ c4 p m u) ∨ (cLo2 p n u ∧ c4 p m u))
    (κ : ZMod p)
    (hid : ∀ u < p, cLo3 p n u → ¬ cLo1 p n u → ¬ cLo2 p n u → ¬ c4 p m u →
      ((Tlo n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p)
        = κ * ((Nlo3 p n m).eval (u : ZMod p)
          * ((linProd (rootsDown p (22 * n) ((5 * n) % p))).eval (u : ZMod p))⁻¹)) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Tlo n m (t * p + u) := by
  have hp0 := hp.out.pos
  have hA := Nat.mod_lt (5 * n) hp0
  -- the four factors' divisibility from the four carries
  have f1 : ∀ u < p, cLo1 p n u → p ∣ (26 * n - (t * p + u)).choose (13 * n) :=
    fun u hu h => dvd_choose_of_carry hu (by omega) h
  have f2 : ∀ u < p, cLo2 p n u → p ∣ (24 * n - (t * p + u)).choose (9 * n) :=
    fun u hu h => dvd_choose_of_carry hu (by omega) h
  have f3 : ∀ u < p, cLo3 p n u → p ∣ (22 * n - (t * p + u)).choose (5 * n) :=
    fun u hu h => dvd_choose_of_carry hu (by omega) h
  have f4 : ∀ u < p, c4 p m u → p ∣ m.choose (t * p + u) :=
    fun u hu h => dvd_choose_m_of_carry hu h
  have hsq2 : ∀ u < p, (p ^ 2 ∣ m.choose (t * p + u) * ((26 * n - (t * p + u)).choose (13 * n)
      * (24 * n - (t * p + u)).choose (9 * n) * (22 * n - (t * p + u)).choose (5 * n))) →
      ((Tlo n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p) = 0 := by
    intro u _ h
    refine cast_div_zero_of_sq ?_
    rw [Tlo_nat]
    exact Dvd.dvd.mul_left (by exact_mod_cast Int.natCast_dvd_natCast.2 h) _
  refine sq_dvd_of_quot (fun u => Tlo n m (t * p + u)) κ (Nlo3 p n m)
    (rootsDown p (22 * n) ((5 * n) % p)) (rootsDown_nodup _ hA0) ?_ ?_ ?_ ?_
  · rw [rootsDown_card]
    exact (Nlo3_natDegree_le n m).trans (by omega)
  · intro u hu
    rw [Tlo_nat]
    refine Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (dvd_prod4 ?_)) _
    rcases hone u hu with h | h | h | h
    exacts [Or.inr (Or.inl (f1 u hu h)), Or.inr (Or.inr (Or.inl (f2 u hu h))),
      Or.inr (Or.inr (Or.inr (f3 u hu h))), Or.inl (f4 u hu h)]
  · intro u hu hm
    have hn3 : ¬ cLo3 p n u := (mem_rootsDown hu hA.le).1 hm
    refine ⟨hsq2 u hu (sq_dvd_prod4 ?_), ?_⟩
    · rcases htwo u hu hn3 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 u hu ha, f2 u hu hb⟩)))
      · exact Or.inl ⟨f4 u hu hb, f1 u hu ha⟩
      · exact Or.inr (Or.inl ⟨f4 u hu hb, f2 u hu ha⟩)
    · unfold Nlo3
      rcases htwo u hu hn3 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [pow_two, mul_assoc]
        exact (mul_dvd_mul (dvd_iff_isRoot.2 (binPoly_down_isRoot hu ha))
          (dvd_iff_isRoot.2 (binPoly_down_isRoot hu hb))).mul_left _
      · exact X_sub_C_sq_dvd_of_two (signChoose_isRoot hu hb) (binPoly_down_isRoot hu ha)
      · rw [mul_right_comm]
        exact X_sub_C_sq_dvd_of_two (signChoose_isRoot hu hb) (binPoly_down_isRoot hu ha)
  · intro u hu hm
    have h3 : cLo3 p n u := by
      by_contra h
      exact hm ((mem_rootsDown hu hA.le).2 h)
    by_cases hrest : ¬ cLo1 p n u ∧ ¬ cLo2 p n u ∧ ¬ c4 p m u
    · exact hid u hu h3 hrest.1 hrest.2.1 hrest.2.2
    · -- a second carry: both sides vanish
      have hN : (Nlo3 p n m).eval (u : ZMod p) = 0 := by
        unfold Nlo3
        by_cases h1 : cLo1 p n u
        · exact isRoot_mul_left' (isRoot_mul_right' (binPoly_down_isRoot hu h1))
        by_cases h2 : cLo2 p n u
        · exact isRoot_mul_right' (binPoly_down_isRoot hu h2)
        have h4 : c4 p m u := by tauto
        exact isRoot_mul_left' (isRoot_mul_left' (signChoose_isRoot hu h4))
      rw [hN, zero_mul, mul_zero]
      refine hsq2 u hu (sq_dvd_prod4 ?_)
      by_cases h1 : cLo1 p n u
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 u hu h1, f3 u hu h3⟩))))
      by_cases h2 : cLo2 p n u
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f2 u hu h2, f3 u hu h3⟩))))
      have h4 : c4 p m u := by tauto
      exact Or.inr (Or.inr (Or.inl ⟨f4 u hu h4, f3 u hu h3⟩))


/-- The LO-3 block lemma with the block's high digits fixed on the one-carry set (Anton). -/
theorem lo3_block_dvd (hp2 : 2 < p) {n m t h1 h2 h3 : ℕ} (hn : 1 ≤ n)
    (hdeg : (p - 1 - m % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ 2 * p - 2)
    (hA0 : 0 < (5 * n) % p)
    (hone : ∀ u < p, cLo1 p n u ∨ cLo2 p n u ∨ cLo3 p n u ∨ c4 p m u)
    (htwo : ∀ u < p, ¬ cLo3 p n u →
      (cLo1 p n u ∧ cLo2 p n u) ∨ (cLo1 p n u ∧ c4 p m u) ∨ (cLo2 p n u ∧ c4 p m u))
    (hsup : ∀ u < p, cLo3 p n u → ¬ cLo1 p n u → ¬ cLo2 p n u → ¬ c4 p m u →
      t * p + u ≤ 22 * n ∧ (26 * n - (t * p + u)) / p = h1
        ∧ (24 * n - (t * p + u)) / p = h2 ∧ (22 * n - (t * p + u)) / p = h3)
    (hh3 : 5 * n / p < h3) (h3p : h3 < p) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Tlo n m (t * p + u) :=
  lo3_block_dvd_of hn hdeg hA0 hone htwo (kLo3 p n m t h1 h2 h3) fun u hu h3' h1' h2' h4' => by
    obtain ⟨htr, e1, e2, e3⟩ := hsup u hu h3' h1' h2' h4'
    exact Tlo_div_eq_lo3 hp2 hn hu h3' htr e1 e2 e3 hh3 h3p

/-- A block whose one-carry terms vanish outright is `0 mod p²` term by term. -/
theorem lo3_block_zero {n m t : ℕ} (hn : 1 ≤ n)
    (htwo : ∀ u < p, ¬ cLo3 p n u →
      (cLo1 p n u ∧ cLo2 p n u) ∨ (cLo1 p n u ∧ c4 p m u) ∨ (cLo2 p n u ∧ c4 p m u))
    (hz : ∀ u < p, cLo3 p n u → ¬ cLo1 p n u → ¬ cLo2 p n u → ¬ c4 p m u →
      Tlo n m (t * p + u) = 0) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Tlo n m (t * p + u) := by
  have hp0 := hp.out.pos
  refine Finset.dvd_sum fun u hu' => ?_
  have hu := Finset.mem_range.1 hu'
  have f1 : cLo1 p n u → p ∣ (26 * n - (t * p + u)).choose (13 * n) :=
    fun h => dvd_choose_of_carry hu (by omega) h
  have f2 : cLo2 p n u → p ∣ (24 * n - (t * p + u)).choose (9 * n) :=
    fun h => dvd_choose_of_carry hu (by omega) h
  have f3 : cLo3 p n u → p ∣ (22 * n - (t * p + u)).choose (5 * n) :=
    fun h => dvd_choose_of_carry hu (by omega) h
  have f4 : c4 p m u → p ∣ m.choose (t * p + u) := fun h => dvd_choose_m_of_carry hu h
  by_cases hO : cLo3 p n u ∧ ¬ cLo1 p n u ∧ ¬ cLo2 p n u ∧ ¬ c4 p m u
  · rw [hz u hu hO.1 hO.2.1 hO.2.2.1 hO.2.2.2]
    exact dvd_zero _
  rw [Tlo_nat]
  refine Dvd.dvd.mul_left ?_ _
  rw [show (p : ℤ) ^ 2 = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl]
  refine Int.natCast_dvd_natCast.2 (sq_dvd_prod4 ?_)
  by_cases h3 : cLo3 p n u
  · by_cases h1 : cLo1 p n u
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 h1, f3 h3⟩))))
    by_cases h2 : cLo2 p n u
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f2 h2, f3 h3⟩))))
    have h4 : c4 p m u := by tauto
    exact Or.inr (Or.inr (Or.inl ⟨f4 h4, f3 h3⟩))
  · rcases htwo u hu h3 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 ha, f2 hb⟩)))
    · exact Or.inl ⟨f4 hb, f1 ha⟩
    · exact Or.inr (Or.inl ⟨f4 hb, f2 ha⟩)


/-! ### TAIL, carried THIRD factor `C(i − 17n − 1, 5n)` -/

def cHi1 (p n u : ℕ) : Prop := (u + p - (13 * n + 1) % p) % p < (13 * n) % p
def cHi2 (p n u : ℕ) : Prop := (u + p - (15 * n + 1) % p) % p < (9 * n) % p
def cHi3 (p n u : ℕ) : Prop := (u + p - (17 * n + 1) % p) % p < (5 * n) % p

theorem mod_block_sub {c t u : ℕ} (h : c ≤ t * p + u) :
    (t * p + u - c) % p = (u + p - c % p) % p := by
  have h1 : ((t * p + u - c : ℕ) : ZMod p) = (((u + p - c % p) % p : ℕ) : ZMod p) := by
    rw [cast_block_sub h, cast_wrap' c u]
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
  rwa [Nat.mod_mod] at h2

/-- A carried rising top binomial is a multiple of `p` — by Lucas, or it is `0` (truncated). -/
theorem dvd_choose_of_carry_up {c t u B : ℕ} (hu : u < p) (hB : 0 < B)
    (hc : (u + p - c % p) % p < B % p) : p ∣ (t * p + u - c).choose B := by
  rw [← ZMod.natCast_eq_zero_iff]
  by_cases h : c ≤ t * p + u
  · rw [lucas_factor, cast_block_sub h, binPoly_eval_wrap' _ _ _ (Nat.mod_lt _ hp.out.pos),
      Nat.choose_eq_zero_of_lt hc]
    simp
  · rw [show t * p + u - c = 0 by omega, Nat.choose_eq_zero_of_lt hB]
    simp

theorem binPoly_up_isRoot {c B u : ℕ} (h : (u + p - c % p) % p < B % p) :
    ((binPoly p (B % p)).comp (X - C ((c : ℕ) : ZMod p))).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_sub, eval_C, eval_X,
    binPoly_eval_wrap' _ _ _ (Nat.mod_lt _ hp.out.pos), Nat.choose_eq_zero_of_lt h,
    Nat.cast_zero]

theorem Thi_nat (n m i : ℕ) :
    Thi n m i = (-1 : ℤ) ^ (m + i) * ((m.choose i * ((i - (13 * n + 1)).choose (13 * n)
      * (i - (15 * n + 1)).choose (9 * n) * (i - (17 * n + 1)).choose (5 * n)) : ℕ) : ℤ) := by
  unfold Thi
  rw [show i - 13 * n - 1 = i - (13 * n + 1) by omega, show i - 15 * n - 1 = i - (15 * n + 1) by omega,
    show i - 17 * n - 1 = i - (17 * n + 1) by omega]
  push_cast; ring

noncomputable def Nhi3 (p n m : ℕ) : (ZMod p)[X] :=
  signChoosePoly p (m % p)
    * (binPoly p ((13 * n) % p)).comp (X - C ((13 * n + 1 : ℕ) : ZMod p))
    * (binPoly p ((9 * n) % p)).comp (X - C ((15 * n + 1 : ℕ) : ZMod p))

noncomputable def kHi3 (p n m t h1 h2 h3 : ℕ) : ZMod p :=
  (-1) ^ (m + t) * (((m / p).choose t : ℕ) : ZMod p)
    * ((h1.choose (13 * n / p) : ℕ) : ZMod p) * ((h2.choose (9 * n / p) : ℕ) : ZMod p)
    * (-(((Nat.factorial ((5 * n) % p) : ℕ) : ZMod p))⁻¹)
    * (((Nat.factorial h3 : ℕ) : ZMod p) * (((Nat.factorial (5 * n / p) : ℕ) : ZMod p))⁻¹
        * (((Nat.factorial (h3 - 1 - 5 * n / p) : ℕ) : ZMod p))⁻¹)

theorem Nhi3_natDegree_le (n m : ℕ) :
    (Nhi3 p n m).natDegree ≤ (p - 1 - m % p) + (13 * n) % p + (9 * n) % p := by
  unfold Nhi3
  exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le
    (signChoosePoly_natDegree_le _) (natDegree_comp_X_sub_le _ _)) (natDegree_comp_X_sub_le _ _)

theorem Thi_div_eq_hi3 (hp2 : 2 < p) {n m t u h1 h2 h3 : ℕ} (hn : 1 ≤ n) (hu : u < p)
    (hc3 : cHi3 p n u) (htr : 17 * n + 1 ≤ t * p + u)
    (e1 : (t * p + u - (13 * n + 1)) / p = h1) (e2 : (t * p + u - (15 * n + 1)) / p = h2)
    (e3 : (t * p + u - (17 * n + 1)) / p = h3) (hh3 : 5 * n / p < h3) (h3p : h3 < p) :
    ((Thi n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p)
      = kHi3 p n m t h1 h2 h3 * ((Nhi3 p n m).eval (u : ZMod p)
          * ((linProd (rootsUp p (17 * n + 1) ((5 * n) % p))).eval (u : ZMod p))⁻¹) := by
  have hp0 := hp.out.pos
  have hA0 := Nat.mod_lt (5 * n) hp0
  have hm0 : m % p < p := Nat.mod_lt _ hp0
  have hdiv : (t * p + u) / p = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hu, zero_add]
  have hmod : (t * p + u) % p = u := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  unfold cHi3 at hc3
  set S0 := (u + p - (17 * n + 1) % p) % p with hS0
  have hS : t * p + u - (17 * n + 1) = S0 + p * h3 := by
    rw [← e3, hS0, ← mod_block_sub htr, Nat.mod_add_div]
  have hA : 5 * n = (5 * n) % p + p * (5 * n / p) := (Nat.mod_add_div _ _).symm
  have hanton := Zeta2Anton.choose_div_p_modEq_of_one_carry p S0 h3 ((5 * n) % p) (5 * n / p)
    hc3 hA0 h3p hh3
  rw [← hS, ← hA] at hanton
  have hdvd : p ∣ (t * p + u - (17 * n + 1)).choose (5 * n) :=
    dvd_choose_of_carry_up hu (by omega) hc3
  obtain ⟨q, hq⟩ := hdvd
  have hq' : (t * p + u - (17 * n + 1)).choose (5 * n) / p = q := by
    rw [hq, Nat.mul_div_cancel_left _ hp0]
  rw [hq'] at hanton
  have hT : Thi n m (t * p + u) = (p : ℤ) * ((-1 : ℤ) ^ (m + (t * p + u))
      * ((m.choose (t * p + u) : ℕ) : ℤ) * (((t * p + u - (13 * n + 1)).choose (13 * n) : ℕ) : ℤ)
      * (((t * p + u - (15 * n + 1)).choose (9 * n) : ℕ) : ℤ) * (q : ℤ)) := by
    rw [Thi_nat, hq]; push_cast; ring
  rw [hT, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp0.ne')]
  have hden := factorial_inv_eq_denTop (p := p) (u := S0) (c := (5 * n) % p) hc3 hA0
  have hS0c : ((S0 : ℕ) : ZMod p) = (u : ZMod p) - ((17 * n + 1 : ℕ) : ZMod p) := by
    rw [hS0]; exact cast_wrap' _ _
  rw [hS0c, ← rootsUp_eval] at hden
  push_cast
  rw [sign_block hp2, lucas_raw m (t * p + u), hdiv, hmod,
    lucas_factor (t * p + u - (13 * n + 1)) (13 * n), lucas_factor (t * p + u - (15 * n + 1)) (9 * n),
    e1, e2, cast_block_sub (by omega), cast_block_sub (by omega), hanton, hden]
  unfold kHi3 Nhi3
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X]
  rw [← signChoose_eq (m % p) u hm0 hu]
  push_cast
  ring

theorem hi3_block_dvd_of {n m t : ℕ} (hn : 1 ≤ n)
    (hdeg : (p - 1 - m % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ 2 * p - 2)
    (hA0 : 0 < (5 * n) % p)
    (hone : ∀ u < p, cHi1 p n u ∨ cHi2 p n u ∨ cHi3 p n u ∨ c4 p m u)
    (htwo : ∀ u < p, ¬ cHi3 p n u →
      (cHi1 p n u ∧ cHi2 p n u) ∨ (cHi1 p n u ∧ c4 p m u) ∨ (cHi2 p n u ∧ c4 p m u))
    (κ : ZMod p)
    (hid : ∀ u < p, cHi3 p n u → ¬ cHi1 p n u → ¬ cHi2 p n u → ¬ c4 p m u →
      ((Thi n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p)
        = κ * ((Nhi3 p n m).eval (u : ZMod p)
          * ((linProd (rootsUp p (17 * n + 1) ((5 * n) % p))).eval (u : ZMod p))⁻¹)) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) := by
  have hp0 := hp.out.pos
  have hA := Nat.mod_lt (5 * n) hp0
  have f1 : ∀ u < p, cHi1 p n u → p ∣ (t * p + u - (13 * n + 1)).choose (13 * n) :=
    fun u hu h => dvd_choose_of_carry_up hu (by omega) h
  have f2 : ∀ u < p, cHi2 p n u → p ∣ (t * p + u - (15 * n + 1)).choose (9 * n) :=
    fun u hu h => dvd_choose_of_carry_up hu (by omega) h
  have f3 : ∀ u < p, cHi3 p n u → p ∣ (t * p + u - (17 * n + 1)).choose (5 * n) :=
    fun u hu h => dvd_choose_of_carry_up hu (by omega) h
  have f4 : ∀ u < p, c4 p m u → p ∣ m.choose (t * p + u) :=
    fun u hu h => dvd_choose_m_of_carry hu h
  have hsq2 : ∀ u < p, (p ^ 2 ∣ m.choose (t * p + u) * ((t * p + u - (13 * n + 1)).choose (13 * n)
      * (t * p + u - (15 * n + 1)).choose (9 * n) * (t * p + u - (17 * n + 1)).choose (5 * n))) →
      ((Thi n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p) = 0 := by
    intro u _ h
    refine cast_div_zero_of_sq ?_
    rw [Thi_nat]
    exact Dvd.dvd.mul_left (by exact_mod_cast Int.natCast_dvd_natCast.2 h) _
  refine sq_dvd_of_quot (fun u => Thi n m (t * p + u)) κ (Nhi3 p n m)
    (rootsUp p (17 * n + 1) ((5 * n) % p)) (rootsUp_nodup _ hA0) ?_ ?_ ?_ ?_
  · rw [rootsUp_card]
    exact (Nhi3_natDegree_le n m).trans (by omega)
  · intro u hu
    rw [Thi_nat]
    refine Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (dvd_prod4 ?_)) _
    rcases hone u hu with h | h | h | h
    exacts [Or.inr (Or.inl (f1 u hu h)), Or.inr (Or.inr (Or.inl (f2 u hu h))),
      Or.inr (Or.inr (Or.inr (f3 u hu h))), Or.inl (f4 u hu h)]
  · intro u hu hm
    have hn3 : ¬ cHi3 p n u := (mem_rootsUp hu hA.le).1 hm
    refine ⟨hsq2 u hu (sq_dvd_prod4 ?_), ?_⟩
    · rcases htwo u hu hn3 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 u hu ha, f2 u hu hb⟩)))
      · exact Or.inl ⟨f4 u hu hb, f1 u hu ha⟩
      · exact Or.inr (Or.inl ⟨f4 u hu hb, f2 u hu ha⟩)
    · unfold Nhi3
      rcases htwo u hu hn3 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [pow_two, mul_assoc]
        exact (mul_dvd_mul (dvd_iff_isRoot.2 (binPoly_up_isRoot ha))
          (dvd_iff_isRoot.2 (binPoly_up_isRoot hb))).mul_left _
      · exact X_sub_C_sq_dvd_of_two (signChoose_isRoot hu hb) (binPoly_up_isRoot ha)
      · rw [mul_right_comm]
        exact X_sub_C_sq_dvd_of_two (signChoose_isRoot hu hb) (binPoly_up_isRoot ha)
  · intro u hu hm
    have h3 : cHi3 p n u := by
      by_contra h
      exact hm ((mem_rootsUp hu hA.le).2 h)
    by_cases hrest : ¬ cHi1 p n u ∧ ¬ cHi2 p n u ∧ ¬ c4 p m u
    · exact hid u hu h3 hrest.1 hrest.2.1 hrest.2.2
    · have hN : (Nhi3 p n m).eval (u : ZMod p) = 0 := by
        unfold Nhi3
        by_cases h1 : cHi1 p n u
        · exact isRoot_mul_left' (isRoot_mul_right' (binPoly_up_isRoot h1))
        by_cases h2 : cHi2 p n u
        · exact isRoot_mul_right' (binPoly_up_isRoot h2)
        have h4 : c4 p m u := by tauto
        exact isRoot_mul_left' (isRoot_mul_left' (signChoose_isRoot hu h4))
      rw [hN, zero_mul, mul_zero]
      refine hsq2 u hu (sq_dvd_prod4 ?_)
      by_cases h1 : cHi1 p n u
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 u hu h1, f3 u hu h3⟩))))
      by_cases h2 : cHi2 p n u
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f2 u hu h2, f3 u hu h3⟩))))
      have h4 : c4 p m u := by tauto
      exact Or.inr (Or.inr (Or.inl ⟨f4 u hu h4, f3 u hu h3⟩))

theorem hi3_block_dvd (hp2 : 2 < p) {n m t h1 h2 h3 : ℕ} (hn : 1 ≤ n)
    (hdeg : (p - 1 - m % p) + (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ 2 * p - 2)
    (hA0 : 0 < (5 * n) % p)
    (hone : ∀ u < p, cHi1 p n u ∨ cHi2 p n u ∨ cHi3 p n u ∨ c4 p m u)
    (htwo : ∀ u < p, ¬ cHi3 p n u →
      (cHi1 p n u ∧ cHi2 p n u) ∨ (cHi1 p n u ∧ c4 p m u) ∨ (cHi2 p n u ∧ c4 p m u))
    (hsup : ∀ u < p, cHi3 p n u → ¬ cHi1 p n u → ¬ cHi2 p n u → ¬ c4 p m u →
      17 * n + 1 ≤ t * p + u ∧ (t * p + u - (13 * n + 1)) / p = h1
        ∧ (t * p + u - (15 * n + 1)) / p = h2 ∧ (t * p + u - (17 * n + 1)) / p = h3)
    (hh3 : 5 * n / p < h3) (h3p : h3 < p) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) :=
  hi3_block_dvd_of hn hdeg hA0 hone htwo (kHi3 p n m t h1 h2 h3) fun u hu h3' h1' h2' h4' => by
    obtain ⟨htr, e1, e2, e3⟩ := hsup u hu h3' h1' h2' h4'
    exact Thi_div_eq_hi3 hp2 hn hu h3' htr e1 e2 e3 hh3 h3p

theorem hi3_block_zero {n m t : ℕ} (hn : 1 ≤ n)
    (htwo : ∀ u < p, ¬ cHi3 p n u →
      (cHi1 p n u ∧ cHi2 p n u) ∨ (cHi1 p n u ∧ c4 p m u) ∨ (cHi2 p n u ∧ c4 p m u))
    (hz : ∀ u < p, cHi3 p n u → ¬ cHi1 p n u → ¬ cHi2 p n u → ¬ c4 p m u →
      Thi n m (t * p + u) = 0) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) := by
  have hp0 := hp.out.pos
  refine Finset.dvd_sum fun u hu' => ?_
  have hu := Finset.mem_range.1 hu'
  have f1 : cHi1 p n u → p ∣ (t * p + u - (13 * n + 1)).choose (13 * n) :=
    fun h => dvd_choose_of_carry_up hu (by omega) h
  have f2 : cHi2 p n u → p ∣ (t * p + u - (15 * n + 1)).choose (9 * n) :=
    fun h => dvd_choose_of_carry_up hu (by omega) h
  have f3 : cHi3 p n u → p ∣ (t * p + u - (17 * n + 1)).choose (5 * n) :=
    fun h => dvd_choose_of_carry_up hu (by omega) h
  have f4 : c4 p m u → p ∣ m.choose (t * p + u) := fun h => dvd_choose_m_of_carry hu h
  by_cases hO : cHi3 p n u ∧ ¬ cHi1 p n u ∧ ¬ cHi2 p n u ∧ ¬ c4 p m u
  · rw [hz u hu hO.1 hO.2.1 hO.2.2.1 hO.2.2.2]
    exact dvd_zero _
  rw [Thi_nat]
  refine Dvd.dvd.mul_left ?_ _
  rw [show (p : ℤ) ^ 2 = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl]
  refine Int.natCast_dvd_natCast.2 (sq_dvd_prod4 ?_)
  by_cases h3 : cHi3 p n u
  · by_cases h1 : cHi1 p n u
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 h1, f3 h3⟩))))
    by_cases h2 : cHi2 p n u
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f2 h2, f3 h3⟩))))
    have h4 : c4 p m u := by tauto
    exact Or.inr (Or.inr (Or.inl ⟨f4 h4, f3 h3⟩))
  · rcases htwo u hu h3 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 ha, f2 hb⟩)))
    · exact Or.inl ⟨f4 hb, f1 ha⟩
    · exact Or.inr (Or.inl ⟨f4 hb, f2 ha⟩)


/-! ### Carried FOURTH factor `C(m, i)` — the `I4` strata, LO and TAIL -/

/-- The three uncarried LO factors, all three blocks. -/
noncomputable def Nlo4 (p n : ℕ) : (ZMod p)[X] :=
  (binPoly p ((13 * n) % p)).comp (C ((26 * n : ℕ) : ZMod p) - X)
    * (binPoly p ((9 * n) % p)).comp (C ((24 * n : ℕ) : ZMod p) - X)
    * (binPoly p ((5 * n) % p)).comp (C ((22 * n : ℕ) : ZMod p) - X)

/-- The three uncarried TAIL factors. -/
noncomputable def Nhi4 (p n : ℕ) : (ZMod p)[X] :=
  (binPoly p ((13 * n) % p)).comp (X - C ((13 * n + 1 : ℕ) : ZMod p))
    * (binPoly p ((9 * n) % p)).comp (X - C ((15 * n + 1 : ℕ) : ZMod p))
    * (binPoly p ((5 * n) % p)).comp (X - C ((17 * n + 1 : ℕ) : ZMod p))

/-- The block constant when `C(m, i)` carries: Anton's `t`-part and the reflected `m₀!`. -/
noncomputable def k4 (p n m t h1 h2 h3 : ℕ) : ZMod p :=
  (-1) ^ (m + t) * (-1) ^ (m % p) * (-(((Nat.factorial (m % p)) : ℕ) : ZMod p))
    * (((Nat.factorial (m / p) : ℕ) : ZMod p) * (((Nat.factorial t : ℕ) : ZMod p))⁻¹
        * (((Nat.factorial (m / p - 1 - t) : ℕ) : ZMod p))⁻¹)
    * ((h1.choose (13 * n / p) : ℕ) : ZMod p) * ((h2.choose (9 * n / p) : ℕ) : ZMod p)
    * ((h3.choose (5 * n / p) : ℕ) : ZMod p)

theorem Nlo4_natDegree_le (n : ℕ) :
    (Nlo4 p n).natDegree ≤ (13 * n) % p + (9 * n) % p + (5 * n) % p := by
  unfold Nlo4
  exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le
    (natDegree_comp_sub_le _ _) (natDegree_comp_sub_le _ _)) (natDegree_comp_sub_le _ _)

theorem Nhi4_natDegree_le (n : ℕ) :
    (Nhi4 p n).natDegree ≤ (13 * n) % p + (9 * n) % p + (5 * n) % p := by
  unfold Nhi4
  exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le
    (natDegree_comp_X_sub_le _ _) (natDegree_comp_X_sub_le _ _)) (natDegree_comp_X_sub_le _ _)

/-- **Anton on the carried `C(m, i)` with Wilson's reflection**: `C(m, tp+u)/p` in the block's
own shape, `(−1)^{m₀+u}·(−m₀!)·(Anton's t-part)·(u(u−1)⋯(u−m₀))⁻¹`. -/
theorem choose_m_div_eq (hp2 : 2 < p) {m t u : ℕ} (hu : u < p) (hc : m % p < u)
    (ht : t < m / p) (hm1 : m / p < p) :
    ((m.choose (t * p + u) / p : ℕ) : ZMod p)
      = (-1) ^ (m % p + u) * (-(((Nat.factorial (m % p)) : ℕ) : ZMod p))
        * (((Nat.factorial (m / p) : ℕ) : ZMod p) * (((Nat.factorial t : ℕ) : ZMod p))⁻¹
          * (((Nat.factorial (m / p - 1 - t) : ℕ) : ZMod p))⁻¹)
        * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹ := by
  have hA := Zeta2Anton.choose_div_p_modEq_of_one_carry p (m % p) (m / p) u t hc hu hm1 ht
  rw [Nat.mod_add_div, show u + p * t = t * p + u by ring] at hA
  rw [hA, rootsLow_eval hc]
  have hW := factorial_inv_eq_denLow (p := p) (e := m % p) (X₀ := u) hc hu (by omega)
  rw [mul_right_comm] at hW
  rw [hW]
  ring

theorem Tlo_div_eq_lo4 (hp2 : 2 < p) {n m t u h1 h2 h3 : ℕ} (hu : u < p) (hc : m % p < u)
    (ht : t < m / p) (hm1 : m / p < p) (htr : t * p + u ≤ 22 * n)
    (e1 : (26 * n - (t * p + u)) / p = h1) (e2 : (24 * n - (t * p + u)) / p = h2)
    (e3 : (22 * n - (t * p + u)) / p = h3) :
    ((Tlo n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p)
      = k4 p n m t h1 h2 h3 * ((Nlo4 p n).eval (u : ZMod p)
          * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹) := by
  have hp0 := hp.out.pos
  have hdvd : p ∣ m.choose (t * p + u) := dvd_choose_m_of_carry hu hc
  obtain ⟨q, hq⟩ := hdvd
  have hq' : m.choose (t * p + u) / p = q := by rw [hq, Nat.mul_div_cancel_left _ hp0]
  have hA := choose_m_div_eq hp2 hu hc ht hm1
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
  unfold k4 Nlo4
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X]
  rw [pow_add (-1 : ZMod p) (m % p) u]
  rcases Nat.even_or_odd u with hpar | hpar
  · rw [hpar.neg_one_pow]; ring
  · rw [hpar.neg_one_pow]; ring

theorem Thi_div_eq_hi4 (hp2 : 2 < p) {n m t u h1 h2 h3 : ℕ} (hu : u < p) (hc : m % p < u)
    (ht : t < m / p) (hm1 : m / p < p) (htr : 17 * n + 1 ≤ t * p + u)
    (e1 : (t * p + u - (13 * n + 1)) / p = h1) (e2 : (t * p + u - (15 * n + 1)) / p = h2)
    (e3 : (t * p + u - (17 * n + 1)) / p = h3) :
    ((Thi n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p)
      = k4 p n m t h1 h2 h3 * ((Nhi4 p n).eval (u : ZMod p)
          * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹) := by
  have hp0 := hp.out.pos
  have hdvd : p ∣ m.choose (t * p + u) := dvd_choose_m_of_carry hu hc
  obtain ⟨q, hq⟩ := hdvd
  have hq' : m.choose (t * p + u) / p = q := by rw [hq, Nat.mul_div_cancel_left _ hp0]
  have hA := choose_m_div_eq hp2 hu hc ht hm1
  rw [hq'] at hA
  have hT : Thi n m (t * p + u) = (p : ℤ) * ((-1 : ℤ) ^ (m + (t * p + u)) * (q : ℤ)
      * (((t * p + u - (13 * n + 1)).choose (13 * n) : ℕ) : ℤ)
      * (((t * p + u - (15 * n + 1)).choose (9 * n) : ℕ) : ℤ)
      * (((t * p + u - (17 * n + 1)).choose (5 * n) : ℕ) : ℤ)) := by
    rw [Thi_nat, hq]; push_cast; ring
  rw [hT, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp0.ne')]
  push_cast
  rw [sign_block hp2, lucas_factor (t * p + u - (13 * n + 1)) (13 * n),
    lucas_factor (t * p + u - (15 * n + 1)) (9 * n), lucas_factor (t * p + u - (17 * n + 1)) (5 * n),
    e1, e2, e3, cast_block_sub (by omega), cast_block_sub (by omega), cast_block_sub htr, hA]
  unfold k4 Nhi4
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X]
  rw [pow_add (-1 : ZMod p) (m % p) u]
  push_cast
  rcases Nat.even_or_odd u with hpar | hpar
  · rw [hpar.neg_one_pow]; ring
  · rw [hpar.neg_one_pow]; ring


theorem lo4_block_dvd_of {n m t : ℕ} (hn : 1 ≤ n)
    (hdeg : (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2 + (m % p + 1))
    (hone : ∀ u < p, cLo1 p n u ∨ cLo2 p n u ∨ cLo3 p n u ∨ c4 p m u)
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cLo1 p n u ∧ cLo2 p n u) ∨ (cLo1 p n u ∧ cLo3 p n u) ∨ (cLo2 p n u ∧ cLo3 p n u))
    (κ : ZMod p)
    (hid : ∀ u < p, c4 p m u → ¬ cLo1 p n u → ¬ cLo2 p n u → ¬ cLo3 p n u →
      ((Tlo n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p)
        = κ * ((Nlo4 p n).eval (u : ZMod p)
          * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹)) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Tlo n m (t * p + u) := by
  have hp0 := hp.out.pos
  have hm0 := Nat.mod_lt m hp0
  have f1 : ∀ u < p, cLo1 p n u → p ∣ (26 * n - (t * p + u)).choose (13 * n) :=
    fun u hu h => dvd_choose_of_carry hu (by omega) h
  have f2 : ∀ u < p, cLo2 p n u → p ∣ (24 * n - (t * p + u)).choose (9 * n) :=
    fun u hu h => dvd_choose_of_carry hu (by omega) h
  have f3 : ∀ u < p, cLo3 p n u → p ∣ (22 * n - (t * p + u)).choose (5 * n) :=
    fun u hu h => dvd_choose_of_carry hu (by omega) h
  have f4 : ∀ u < p, c4 p m u → p ∣ m.choose (t * p + u) :=
    fun u hu h => dvd_choose_m_of_carry hu h
  have hsq2 : ∀ u < p, (p ^ 2 ∣ m.choose (t * p + u) * ((26 * n - (t * p + u)).choose (13 * n)
      * (24 * n - (t * p + u)).choose (9 * n) * (22 * n - (t * p + u)).choose (5 * n))) →
      ((Tlo n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p) = 0 := by
    intro u _ h
    refine cast_div_zero_of_sq ?_
    rw [Tlo_nat]
    exact Dvd.dvd.mul_left (by exact_mod_cast Int.natCast_dvd_natCast.2 h) _
  refine sq_dvd_of_quot (fun u => Tlo n m (t * p + u)) κ (Nlo4 p n)
    (rootsLow p (m % p)) (rootsLow_nodup hm0) ?_ ?_ ?_ ?_
  · rw [rootsLow_card]
    exact (Nlo4_natDegree_le n).trans hdeg
  · intro u hu
    rw [Tlo_nat]
    refine Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (dvd_prod4 ?_)) _
    rcases hone u hu with h | h | h | h
    exacts [Or.inr (Or.inl (f1 u hu h)), Or.inr (Or.inr (Or.inl (f2 u hu h))),
      Or.inr (Or.inr (Or.inr (f3 u hu h))), Or.inl (f4 u hu h)]
  · intro u hu hm
    have hn4 : ¬ c4 p m u := by unfold c4; have := (mem_rootsLow hu hm0).1 hm; omega
    refine ⟨hsq2 u hu (sq_dvd_prod4 ?_), ?_⟩
    · rcases htwo u hu hn4 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 u hu ha, f2 u hu hb⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 u hu ha, f3 u hu hb⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f2 u hu ha, f3 u hu hb⟩))))
    · unfold Nlo4
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
    by_cases hrest : ¬ cLo1 p n u ∧ ¬ cLo2 p n u ∧ ¬ cLo3 p n u
    · exact hid u hu h4 hrest.1 hrest.2.1 hrest.2.2
    · have hN : (Nlo4 p n).eval (u : ZMod p) = 0 := by
        unfold Nlo4
        by_cases h1 : cLo1 p n u
        · exact isRoot_mul_left' (isRoot_mul_left' (binPoly_down_isRoot hu h1))
        by_cases h2 : cLo2 p n u
        · exact isRoot_mul_left' (isRoot_mul_right' (binPoly_down_isRoot hu h2))
        have h3 : cLo3 p n u := by tauto
        exact isRoot_mul_right' (binPoly_down_isRoot hu h3)
      rw [hN, zero_mul, mul_zero]
      refine hsq2 u hu (sq_dvd_prod4 ?_)
      by_cases h1 : cLo1 p n u
      · exact Or.inl ⟨f4 u hu h4, f1 u hu h1⟩
      by_cases h2 : cLo2 p n u
      · exact Or.inr (Or.inl ⟨f4 u hu h4, f2 u hu h2⟩)
      have h3 : cLo3 p n u := by tauto
      exact Or.inr (Or.inr (Or.inl ⟨f4 u hu h4, f3 u hu h3⟩))

theorem lo4_block_dvd (hp2 : 2 < p) {n m t h1 h2 h3 : ℕ} (hn : 1 ≤ n)
    (hdeg : (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2 + (m % p + 1))
    (hone : ∀ u < p, cLo1 p n u ∨ cLo2 p n u ∨ cLo3 p n u ∨ c4 p m u)
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cLo1 p n u ∧ cLo2 p n u) ∨ (cLo1 p n u ∧ cLo3 p n u) ∨ (cLo2 p n u ∧ cLo3 p n u))
    (hsup : ∀ u < p, c4 p m u → ¬ cLo1 p n u → ¬ cLo2 p n u → ¬ cLo3 p n u →
      t * p + u ≤ 22 * n ∧ (26 * n - (t * p + u)) / p = h1
        ∧ (24 * n - (t * p + u)) / p = h2 ∧ (22 * n - (t * p + u)) / p = h3)
    (ht : t < m / p) (hm1 : m / p < p) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Tlo n m (t * p + u) :=
  lo4_block_dvd_of hn hdeg hone htwo (k4 p n m t h1 h2 h3) fun u hu h4' h1' h2' h3' => by
    obtain ⟨htr, e1, e2, e3⟩ := hsup u hu h4' h1' h2' h3'
    exact Tlo_div_eq_lo4 hp2 hu h4' ht hm1 htr e1 e2 e3

theorem lo4_block_zero {n m t : ℕ} (hn : 1 ≤ n)
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cLo1 p n u ∧ cLo2 p n u) ∨ (cLo1 p n u ∧ cLo3 p n u) ∨ (cLo2 p n u ∧ cLo3 p n u))
    (hz : ∀ u < p, c4 p m u → ¬ cLo1 p n u → ¬ cLo2 p n u → ¬ cLo3 p n u →
      Tlo n m (t * p + u) = 0) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Tlo n m (t * p + u) := by
  have hp0 := hp.out.pos
  refine Finset.dvd_sum fun u hu' => ?_
  have hu := Finset.mem_range.1 hu'
  have f1 : cLo1 p n u → p ∣ (26 * n - (t * p + u)).choose (13 * n) :=
    fun h => dvd_choose_of_carry hu (by omega) h
  have f2 : cLo2 p n u → p ∣ (24 * n - (t * p + u)).choose (9 * n) :=
    fun h => dvd_choose_of_carry hu (by omega) h
  have f3 : cLo3 p n u → p ∣ (22 * n - (t * p + u)).choose (5 * n) :=
    fun h => dvd_choose_of_carry hu (by omega) h
  have f4 : c4 p m u → p ∣ m.choose (t * p + u) := fun h => dvd_choose_m_of_carry hu h
  by_cases hO : c4 p m u ∧ ¬ cLo1 p n u ∧ ¬ cLo2 p n u ∧ ¬ cLo3 p n u
  · rw [hz u hu hO.1 hO.2.1 hO.2.2.1 hO.2.2.2]
    exact dvd_zero _
  rw [Tlo_nat]
  refine Dvd.dvd.mul_left ?_ _
  rw [show (p : ℤ) ^ 2 = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl]
  refine Int.natCast_dvd_natCast.2 (sq_dvd_prod4 ?_)
  by_cases h4 : c4 p m u
  · by_cases h1 : cLo1 p n u
    · exact Or.inl ⟨f4 h4, f1 h1⟩
    by_cases h2 : cLo2 p n u
    · exact Or.inr (Or.inl ⟨f4 h4, f2 h2⟩)
    have h3 : cLo3 p n u := by tauto
    exact Or.inr (Or.inr (Or.inl ⟨f4 h4, f3 h3⟩))
  · rcases htwo u hu h4 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 ha, f2 hb⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 ha, f3 hb⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f2 ha, f3 hb⟩))))

theorem hi4_block_dvd_of {n m t : ℕ} (hn : 1 ≤ n)
    (hdeg : (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2 + (m % p + 1))
    (hone : ∀ u < p, cHi1 p n u ∨ cHi2 p n u ∨ cHi3 p n u ∨ c4 p m u)
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cHi1 p n u ∧ cHi2 p n u) ∨ (cHi1 p n u ∧ cHi3 p n u) ∨ (cHi2 p n u ∧ cHi3 p n u))
    (κ : ZMod p)
    (hid : ∀ u < p, c4 p m u → ¬ cHi1 p n u → ¬ cHi2 p n u → ¬ cHi3 p n u →
      ((Thi n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p)
        = κ * ((Nhi4 p n).eval (u : ZMod p)
          * ((linProd (rootsLow p (m % p))).eval (u : ZMod p))⁻¹)) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) := by
  have hp0 := hp.out.pos
  have hm0 := Nat.mod_lt m hp0
  have f1 : ∀ u < p, cHi1 p n u → p ∣ (t * p + u - (13 * n + 1)).choose (13 * n) :=
    fun u hu h => dvd_choose_of_carry_up hu (by omega) h
  have f2 : ∀ u < p, cHi2 p n u → p ∣ (t * p + u - (15 * n + 1)).choose (9 * n) :=
    fun u hu h => dvd_choose_of_carry_up hu (by omega) h
  have f3 : ∀ u < p, cHi3 p n u → p ∣ (t * p + u - (17 * n + 1)).choose (5 * n) :=
    fun u hu h => dvd_choose_of_carry_up hu (by omega) h
  have f4 : ∀ u < p, c4 p m u → p ∣ m.choose (t * p + u) :=
    fun u hu h => dvd_choose_m_of_carry hu h
  have hsq2 : ∀ u < p, (p ^ 2 ∣ m.choose (t * p + u) * ((t * p + u - (13 * n + 1)).choose (13 * n)
      * (t * p + u - (15 * n + 1)).choose (9 * n) * (t * p + u - (17 * n + 1)).choose (5 * n))) →
      ((Thi n m (t * p + u) / (p : ℤ) : ℤ) : ZMod p) = 0 := by
    intro u _ h
    refine cast_div_zero_of_sq ?_
    rw [Thi_nat]
    exact Dvd.dvd.mul_left (by exact_mod_cast Int.natCast_dvd_natCast.2 h) _
  refine sq_dvd_of_quot (fun u => Thi n m (t * p + u)) κ (Nhi4 p n)
    (rootsLow p (m % p)) (rootsLow_nodup hm0) ?_ ?_ ?_ ?_
  · rw [rootsLow_card]
    exact (Nhi4_natDegree_le n).trans hdeg
  · intro u hu
    rw [Thi_nat]
    refine Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (dvd_prod4 ?_)) _
    rcases hone u hu with h | h | h | h
    exacts [Or.inr (Or.inl (f1 u hu h)), Or.inr (Or.inr (Or.inl (f2 u hu h))),
      Or.inr (Or.inr (Or.inr (f3 u hu h))), Or.inl (f4 u hu h)]
  · intro u hu hm
    have hn4 : ¬ c4 p m u := by unfold c4; have := (mem_rootsLow hu hm0).1 hm; omega
    refine ⟨hsq2 u hu (sq_dvd_prod4 ?_), ?_⟩
    · rcases htwo u hu hn4 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 u hu ha, f2 u hu hb⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 u hu ha, f3 u hu hb⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f2 u hu ha, f3 u hu hb⟩))))
    · unfold Nhi4
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
    by_cases hrest : ¬ cHi1 p n u ∧ ¬ cHi2 p n u ∧ ¬ cHi3 p n u
    · exact hid u hu h4 hrest.1 hrest.2.1 hrest.2.2
    · have hN : (Nhi4 p n).eval (u : ZMod p) = 0 := by
        unfold Nhi4
        by_cases h1 : cHi1 p n u
        · exact isRoot_mul_left' (isRoot_mul_left' (binPoly_up_isRoot h1))
        by_cases h2 : cHi2 p n u
        · exact isRoot_mul_left' (isRoot_mul_right' (binPoly_up_isRoot h2))
        have h3 : cHi3 p n u := by tauto
        exact isRoot_mul_right' (binPoly_up_isRoot h3)
      rw [hN, zero_mul, mul_zero]
      refine hsq2 u hu (sq_dvd_prod4 ?_)
      by_cases h1 : cHi1 p n u
      · exact Or.inl ⟨f4 u hu h4, f1 u hu h1⟩
      by_cases h2 : cHi2 p n u
      · exact Or.inr (Or.inl ⟨f4 u hu h4, f2 u hu h2⟩)
      have h3 : cHi3 p n u := by tauto
      exact Or.inr (Or.inr (Or.inl ⟨f4 u hu h4, f3 u hu h3⟩))

theorem hi4_block_dvd (hp2 : 2 < p) {n m t h1 h2 h3 : ℕ} (hn : 1 ≤ n)
    (hdeg : (13 * n) % p + (9 * n) % p + (5 * n) % p ≤ p - 2 + (m % p + 1))
    (hone : ∀ u < p, cHi1 p n u ∨ cHi2 p n u ∨ cHi3 p n u ∨ c4 p m u)
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cHi1 p n u ∧ cHi2 p n u) ∨ (cHi1 p n u ∧ cHi3 p n u) ∨ (cHi2 p n u ∧ cHi3 p n u))
    (hsup : ∀ u < p, c4 p m u → ¬ cHi1 p n u → ¬ cHi2 p n u → ¬ cHi3 p n u →
      17 * n + 1 ≤ t * p + u ∧ (t * p + u - (13 * n + 1)) / p = h1
        ∧ (t * p + u - (15 * n + 1)) / p = h2 ∧ (t * p + u - (17 * n + 1)) / p = h3)
    (ht : t < m / p) (hm1 : m / p < p) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) :=
  hi4_block_dvd_of hn hdeg hone htwo (k4 p n m t h1 h2 h3) fun u hu h4' h1' h2' h3' => by
    obtain ⟨htr, e1, e2, e3⟩ := hsup u hu h4' h1' h2' h3'
    exact Thi_div_eq_hi4 hp2 hu h4' ht hm1 htr e1 e2 e3

theorem hi4_block_zero {n m t : ℕ} (hn : 1 ≤ n)
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cHi1 p n u ∧ cHi2 p n u) ∨ (cHi1 p n u ∧ cHi3 p n u) ∨ (cHi2 p n u ∧ cHi3 p n u))
    (hz : ∀ u < p, c4 p m u → ¬ cHi1 p n u → ¬ cHi2 p n u → ¬ cHi3 p n u →
      Thi n m (t * p + u) = 0) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) := by
  have hp0 := hp.out.pos
  refine Finset.dvd_sum fun u hu' => ?_
  have hu := Finset.mem_range.1 hu'
  have f1 : cHi1 p n u → p ∣ (t * p + u - (13 * n + 1)).choose (13 * n) :=
    fun h => dvd_choose_of_carry_up hu (by omega) h
  have f2 : cHi2 p n u → p ∣ (t * p + u - (15 * n + 1)).choose (9 * n) :=
    fun h => dvd_choose_of_carry_up hu (by omega) h
  have f3 : cHi3 p n u → p ∣ (t * p + u - (17 * n + 1)).choose (5 * n) :=
    fun h => dvd_choose_of_carry_up hu (by omega) h
  have f4 : c4 p m u → p ∣ m.choose (t * p + u) := fun h => dvd_choose_m_of_carry hu h
  by_cases hO : c4 p m u ∧ ¬ cHi1 p n u ∧ ¬ cHi2 p n u ∧ ¬ cHi3 p n u
  · rw [hz u hu hO.1 hO.2.1 hO.2.2.1 hO.2.2.2]
    exact dvd_zero _
  rw [Thi_nat]
  refine Dvd.dvd.mul_left ?_ _
  rw [show (p : ℤ) ^ 2 = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl]
  refine Int.natCast_dvd_natCast.2 (sq_dvd_prod4 ?_)
  by_cases h4 : c4 p m u
  · by_cases h1 : cHi1 p n u
    · exact Or.inl ⟨f4 h4, f1 h1⟩
    by_cases h2 : cHi2 p n u
    · exact Or.inr (Or.inl ⟨f4 h4, f2 h2⟩)
    have h3 : cHi3 p n u := by tauto
    exact Or.inr (Or.inr (Or.inl ⟨f4 h4, f3 h3⟩))
  · rcases htwo u hu h4 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 ha, f2 hb⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f1 ha, f3 hb⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f2 ha, f3 hb⟩))))


/-! ### Blocks that vanish outright, or whose one-carry terms do -/

theorem lo_all_zero {n m t : ℕ} (hn : 1 ≤ n) (ht : 13 * n < t * p) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Tlo n m (t * p + u) := by
  rw [Finset.sum_eq_zero fun u _ => Tlo_eq_zero_of_gt13 hn (by omega)]
  exact dvd_zero _

theorem hi_all_zero {n m t : ℕ} (hn : 1 ≤ n) (ht : t * p + p ≤ 26 * n + 1) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) := by
  rw [Finset.sum_eq_zero fun u hu => Thi_eq_zero_of_le26 hn (by
    have := Finset.mem_range.1 hu; omega)]
  exact dvd_zero _

theorem choose_m_eq_zero_of_past {m t u : ℕ} (hc : m % p < u) (ht : m / p ≤ t) :
    m.choose (t * p + u) = 0 := by
  have hp0 := hp.out.pos
  have h1 := Nat.div_add_mod m p
  have h2 : p * (m / p) ≤ t * p := by rw [mul_comm]; exact Nat.mul_le_mul_right p ht
  exact Nat.choose_eq_zero_of_lt (by omega)

/-- Past `m/p`, a carried `C(m, i)` is `0` outright. -/
theorem lo4_block_past {n m t : ℕ} (hn : 1 ≤ n)
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cLo1 p n u ∧ cLo2 p n u) ∨ (cLo1 p n u ∧ cLo3 p n u) ∨ (cLo2 p n u ∧ cLo3 p n u))
    (ht : m / p ≤ t) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Tlo n m (t * p + u) :=
  lo4_block_zero hn htwo fun u _ h4 _ _ _ => by
    rw [Tlo_nat, choose_m_eq_zero_of_past h4 ht]; simp

theorem hi4_block_past {n m t : ℕ} (hn : 1 ≤ n)
    (htwo : ∀ u < p, ¬ c4 p m u →
      (cHi1 p n u ∧ cHi2 p n u) ∨ (cHi1 p n u ∧ cHi3 p n u) ∨ (cHi2 p n u ∧ cHi3 p n u))
    (ht : m / p ≤ t) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) :=
  hi4_block_zero hn htwo fun u _ h4 _ _ _ => by
    rw [Thi_nat, choose_m_eq_zero_of_past h4 ht]; simp

/-- A TAIL block whose one-carry residues all sit at or below `26n`. -/
theorem hi3_block_low {n m t : ℕ} (hn : 1 ≤ n)
    (htwo : ∀ u < p, ¬ cHi3 p n u →
      (cHi1 p n u ∧ cHi2 p n u) ∨ (cHi1 p n u ∧ c4 p m u) ∨ (cHi2 p n u ∧ c4 p m u))
    (hO : ∀ u < p, cHi3 p n u → ¬ cHi1 p n u → ¬ cHi2 p n u → ¬ c4 p m u → t * p + u ≤ 26 * n) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, Thi n m (t * p + u) :=
  hi3_block_zero hn htwo fun u hu h3 h1 h2 h4 => Thi_eq_zero_of_le26 hn (hO u hu h3 h1 h2 h4)


/-! ### Residue helpers for the strata -/

omit hp in
/-- `(N + 1) % p` when `N = S + A·p` and `f·p ≤ S < (f+1)·p`: one past `S`'s residue, or `0` at the
edge `S + 1 = (f+1)·p`. -/
theorem res_succ {N S A f : ℕ} (hp0 : 0 < p) (hN : N = S + A * p) (hf1 : f * p ≤ S)
    (hf2 : S < f * p + p) :
    ((N + 1) % p = S - f * p + 1 ∧ S - f * p + 1 < p) ∨ ((N + 1) % p = 0 ∧ S + 1 = f * p + p) := by
  have e : (A + f) * p = A * p + f * p := by ring
  by_cases h : S - f * p + 1 < p
  · exact Or.inl ⟨mod_of_lin hp0 (q := A + f) (by omega) h, h⟩
  · have e' : (A + f + 1) * p = A * p + f * p + p := by ring
    exact Or.inr ⟨mod_of_lin hp0 (q := A + f + 1) (r := 0) (by omega) hp0, by omega⟩

omit hp in
/-- `(c·n) % p` from an affine decomposition. -/
theorem res_mul {N S A f : ℕ} (hp0 : 0 < p) (hN : N = S + A * p) (hf1 : f * p ≤ S)
    (hf2 : S < f * p + p) : N % p = S - f * p := by
  have e : (A + f) * p = A * p + f * p := by ring
  exact mod_of_lin hp0 (q := A + f) (by omega) (by omega)

omit hp in
/-- The window, divided by `p`: `26a + 26·(c/d) < p` when `s/p ≥ c/d`. -/
theorem win_bound {a s c d : ℕ} (hwin : 26 * (p * a + s) + 1 < p ^ 2) (hs : c * p ≤ d * s)
    (hd : 0 < d) :
    26 * d * a + 26 * c < d * p := by
  rcases Nat.eq_zero_or_pos p with h0 | hp0
  · subst h0; simp at hwin
  have h1 : p * (26 * d * a + 26 * c) < p * (d * p) := by
    have e1 : p * (26 * d * a + 26 * c) = d * (26 * (p * a)) + 26 * (c * p) := by ring
    have e2 : p * (d * p) = d * p ^ 2 := by ring
    have e3 : d * (26 * (p * a + s) + 1) ≤ d * p ^ 2 := Nat.mul_le_mul_left d hwin.le
    have e4 : 26 * (c * p) ≤ 26 * (d * s) := Nat.mul_le_mul_left 26 hs
    rw [e1, e2]
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left h1


omit hp in
theorem div_eq_of_bounds {x q : ℕ} (h1 : q * p ≤ x) (h2 : x < q * p + p) : x / p = q :=
  Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)

end G2

end Zeta2PtpRunG2

#print axioms Zeta2PtpRunG2.mod_sub_block
#print axioms Zeta2PtpRunG2.dvd_choose_of_carry
#print axioms Zeta2PtpRunG2.dvd_choose_m_of_carry
#print axioms Zeta2PtpRunG2.wrap_mod_down
#print axioms Zeta2PtpRunG2.linProd_range_eval
#print axioms Zeta2PtpRunG2.rootsDown_card
#print axioms Zeta2PtpRunG2.rootsUp_card
#print axioms Zeta2PtpRunG2.rootsLow_card
#print axioms Zeta2PtpRunG2.rootsDown_nodup
#print axioms Zeta2PtpRunG2.rootsUp_nodup
#print axioms Zeta2PtpRunG2.rootsLow_nodup
#print axioms Zeta2PtpRunG2.mem_rootsDown
#print axioms Zeta2PtpRunG2.mem_rootsUp
#print axioms Zeta2PtpRunG2.mem_rootsLow
#print axioms Zeta2PtpRunG2.rootsDown_eval
#print axioms Zeta2PtpRunG2.rootsUp_eval
#print axioms Zeta2PtpRunG2.rootsLow_eval
#print axioms Zeta2PtpRunG2.sq_dvd_of_quot
#print axioms Zeta2PtpRunG2.Nlo3_natDegree_le
#print axioms Zeta2PtpRunG2.Tlo_def
#print axioms Zeta2PtpRunG2.Tlo_div_eq_lo3
#print axioms Zeta2PtpRunG2.dvd_prod4
#print axioms Zeta2PtpRunG2.sq_dvd_prod4
#print axioms Zeta2PtpRunG2.Tlo_nat
#print axioms Zeta2PtpRunG2.cast_div_zero_of_sq
#print axioms Zeta2PtpRunG2.binPoly_down_isRoot
#print axioms Zeta2PtpRunG2.signChoose_isRoot
#print axioms Zeta2PtpRunG2.isRoot_mul_left'
#print axioms Zeta2PtpRunG2.isRoot_mul_right'
#print axioms Zeta2PtpRunG2.lo3_block_dvd_of
#print axioms Zeta2PtpRunG2.lo3_block_dvd
#print axioms Zeta2PtpRunG2.lo3_block_zero
#print axioms Zeta2PtpRunG2.mod_block_sub
#print axioms Zeta2PtpRunG2.dvd_choose_of_carry_up
#print axioms Zeta2PtpRunG2.binPoly_up_isRoot
#print axioms Zeta2PtpRunG2.Thi_nat
#print axioms Zeta2PtpRunG2.Nhi3_natDegree_le
#print axioms Zeta2PtpRunG2.Thi_div_eq_hi3
#print axioms Zeta2PtpRunG2.hi3_block_dvd_of
#print axioms Zeta2PtpRunG2.hi3_block_dvd
#print axioms Zeta2PtpRunG2.hi3_block_zero
#print axioms Zeta2PtpRunG2.Nlo4_natDegree_le
#print axioms Zeta2PtpRunG2.Nhi4_natDegree_le
#print axioms Zeta2PtpRunG2.choose_m_div_eq
#print axioms Zeta2PtpRunG2.Tlo_div_eq_lo4
#print axioms Zeta2PtpRunG2.Thi_div_eq_hi4
#print axioms Zeta2PtpRunG2.lo4_block_dvd_of
#print axioms Zeta2PtpRunG2.lo4_block_dvd
#print axioms Zeta2PtpRunG2.lo4_block_zero
#print axioms Zeta2PtpRunG2.hi4_block_dvd_of
#print axioms Zeta2PtpRunG2.hi4_block_dvd
#print axioms Zeta2PtpRunG2.hi4_block_zero
#print axioms Zeta2PtpRunG2.lo_all_zero
#print axioms Zeta2PtpRunG2.hi_all_zero
#print axioms Zeta2PtpRunG2.choose_m_eq_zero_of_past
#print axioms Zeta2PtpRunG2.lo4_block_past
#print axioms Zeta2PtpRunG2.hi4_block_past
#print axioms Zeta2PtpRunG2.hi3_block_low
#print axioms Zeta2PtpRunG2.res_succ
#print axioms Zeta2PtpRunG2.res_mul
#print axioms Zeta2PtpRunG2.win_bound
#print axioms Zeta2PtpRunG2.div_eq_of_bounds
#check @Zeta2PtpRunG2.sq_dvd_of_quot
#check @Zeta2PtpRunG2.lo3_block_dvd
#check @Zeta2PtpRunG2.hi3_block_dvd
#check @Zeta2PtpRunG2.lo4_block_dvd
#check @Zeta2PtpRunG2.hi4_block_dvd
#check @Zeta2PtpRunG2.Tlo_div_eq_lo3
#check @Zeta2PtpRunG2.Thi_div_eq_hi3
#check @Zeta2PtpRunG2.Tlo_div_eq_lo4
#check @Zeta2PtpRunG2.Thi_div_eq_hi4
