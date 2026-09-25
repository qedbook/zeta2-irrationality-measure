/-
# Row PT-P, layer 14 — the rows with `m ≥ p²`: the PAIRING `i ↔ p² + i`, and
# `ResidualNarrowOpen` reduced to its polar run-strata disjunct

`Zeta2PtpKumRows.ResidualNarrowOpen` names two families of rows the units count does not reach:
the polar rows on the five run strata, and EVERY row with `p² ≤ m = 11n + 1 + r`.  The second was
read as "one cell, `n = 11, p = 17, r = 169`" off the `n ≤ 23` box; it is not.  Past that box the
window primes with `26n + 1 < p² ≤ 27n` recur for ever, and `ptp_resid_narrow_probe.out` counts
7 189 non-polar `m ≥ p²` rows at `n ≤ 500` whose terms NEED cancellation.  This file proves them all.

THE MECHANISM.  At `m ≥ p²`, `v_p C(m, L)` gains the TENS carry (`padicValNat_LC_sq`: `L` and
`r = m − L` are below `p²` and sum past it), so the target rises by one.  A term `i` of
`h_m = Σ (−1)^{m−i} C(m,i) H(i)` with `μ := m − p² < i < p²` pays it with the same tens carry of
`C(m, i)` (`padicValNat_choose_eq_cb_succ`).  The terms that CANNOT — `i ≤ μ` and `i ≥ p²` — PAIR:

    C(m, p²+j) · C(p²+j, j) = C(m, j) · C(m−j, p²),   both cofactors ≡ 1 (mod p)   (Lucas twice)
    C(p² − a, B) · B! = Π (p² − (a+i)),   (−1)^B C(a+B−1, B) · B! = Π (−(a+i)),   a + i < p²

so each factor of the pair's second term is its first term's, shifted by `p²` — one `p`-adic place
past its own valuation (`sh_prod_shift`: `p² ∤ a+i`) — and `(−1)^{p²} = −1` makes the pair a
DIFFERENCE.  `Sh` is that relation and it is multiplicative (`Sh.mul`), so `H(p² + j)` shifts
`H(j)` (`sh_Hfun`, three blocks) and the whole pair gains one place (`pair_dvd`).  Then every term
and every pair carries its units count plus one, which is the `m < p²` residue statement
(`residue_main`, `polar_main`) plus one — for every row EXCEPT the polar rows on the run strata,
where the units count itself is short and the run congruence is owed.

WHAT IS NOT CLAIMED.  `ResidualRunOpen` — the polar rows whose residue `n % p` lies on one of the
five run strata, at every `m` — is NOT proved here; `residualNarrowOpen_of_run` and
`polyHalfOpen_of_run` carry it in their TYPE (`#print axioms` cannot see a binder, LEAN.md §1).
Row PT-P does not close and `Zeta2Target.zeta2_not_liouvilleWith` is `sorry`.

Probe: `ptp_resid_narrow_probe.py` / `.out`.  Falsifier: `falsify_ptprespair.sh` /
`out_ptprespair_falsify.txt`.  Runner: `run_resid.sh` (its own olean store; see its header).

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
import Mathlib.Data.Nat.Choose.Lucas

namespace Zeta2PtpResPair

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpPolar Zeta2PtpPoly Zeta2PtpKummer Zeta2PtpRun
  Zeta2PtpCoeff Zeta2NewtonAssemble Zeta2PtpKumRes Zeta2PtpKumRows Finset

/-! ## 1. `Sh`: agreement one place past the valuation, and the `p²`-shift -/

/-- `Sh p x x'`: `x'` agrees with `x` one `p`-adic place beyond every power of `p` dividing `x`. -/
def Sh (p : ℕ) (x x' : ℤ) : Prop := ∀ K : ℕ, (p : ℤ) ^ K ∣ x → (p : ℤ) ^ (K + 1) ∣ x' - x

section Sh
variable {p : ℕ} [hp : Fact p.Prime]

theorem eq_zero_of_forall_pow_dvd {z : ℤ} (h : ∀ K : ℕ, (p : ℤ) ^ K ∣ z) : z = 0 := by
  by_contra hz
  have h1 := Int.natAbs_dvd_natAbs.mpr (h z.natAbs)
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hz) h1
  have h3 : z.natAbs < p ^ z.natAbs := Nat.lt_pow_self hp.out.one_lt
  omega

theorem Sh.zero_left {x' : ℤ} (h : Sh p 0 x') : x' = 0 := by
  refine eq_zero_of_forall_pow_dvd (p := p) fun K => ?_
  have := h K (dvd_zero _)
  rw [sub_zero] at this
  exact (pow_dvd_pow _ (Nat.le_succ K)).trans this

theorem Sh.mul {x x' y y' : ℤ} (hx : Sh p x x') (hy : Sh p y y') : Sh p (x * y) (x' * y') := by
  intro K hK
  by_cases hx0 : x = 0
  · subst hx0
    rw [Sh.zero_left hx]
    simp
  by_cases hy0 : y = 0
  · subst hy0
    rw [Sh.zero_left hy]
    simp
  have hK' : K ≤ padicValInt p x + padicValInt p y := by
    rcases (padicValInt_dvd_iff K (x * y)).1 hK with h | h
    · exact absurd h (mul_ne_zero hx0 hy0)
    · rwa [padicValInt.mul hx0 hy0] at h
  have hx1 := hx _ (padicValInt_dvd x)
  have hy1 := hy _ (padicValInt_dvd y)
  have hx2 : (p : ℤ) ^ padicValInt p x ∣ x' := by
    have := dvd_add (padicValInt_dvd x) ((pow_dvd_pow _ (Nat.le_succ _)).trans hx1)
    rwa [add_sub_cancel] at this
  have key : (p : ℤ) ^ (padicValInt p x + padicValInt p y + 1) ∣ x' * y' - x * y := by
    have e : x' * y' - x * y = x' * (y' - y) + (x' - x) * y := by ring
    rw [e]
    refine dvd_add ?_ ?_
    · rw [add_assoc, pow_add]
      exact mul_dvd_mul hx2 hy1
    · rw [add_right_comm, pow_add]
      exact mul_dvd_mul hx1 (padicValInt_dvd y)
  exact (pow_dvd_pow _ (by omega)).trans key

/-- A shift by a unit ratio `≡ 1`: `x'·U = x·U'` with `p ∤ U` and `U ≡ U' (mod p)`. -/
theorem sh_of_mul_eq {x x' : ℤ} {U U' : ℕ} (h : x' * U = x * U') (hU : ¬ p ∣ U)
    (hUU : (p : ℤ) ∣ (U' : ℤ) - U) : Sh p x x' := by
  intro K hK
  have e : (x' - x) * U = x * ((U' : ℤ) - U) := by linear_combination h
  have h1 : (p : ℤ) ^ (K + 1) ∣ (x' - x) * U := by
    rw [e, pow_succ]
    exact mul_dvd_mul hK hUU
  have hcop : IsCoprime ((p : ℤ) ^ (K + 1)) ((U : ℤ)) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hU)).pow_left
  exact hcop.dvd_of_dvd_mul_right h1

/-- `Sh` is insensitive to a common nonzero factor. -/
theorem Sh.cancel {x x' : ℤ} {g : ℕ} (hg : g ≠ 0) (h : Sh p ((g : ℤ) * x) ((g : ℤ) * x')) :
    Sh p x x' := by
  obtain ⟨e, u, hu, hgu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hg p hp.out.ne_one
  intro K hK
  have h1 : (p : ℤ) ^ (K + e) ∣ (g : ℤ) * x := by
    rw [hgu, pow_add]
    push_cast
    rw [show (p : ℤ) ^ e * (u : ℤ) * x = (p : ℤ) ^ e * ((u : ℤ) * x) by ring, mul_comm ((p : ℤ) ^ K)]
    exact mul_dvd_mul_left _ (Dvd.dvd.mul_left hK _)
  have h2 := h _ h1
  rw [hgu] at h2
  push_cast at h2
  rw [show (p : ℤ) ^ e * (u : ℤ) * x' - (p : ℤ) ^ e * (u : ℤ) * x
      = (p : ℤ) ^ e * ((u : ℤ) * (x' - x)) by ring,
    show K + e + 1 = e + (K + 1) by ring, pow_add] at h2
  have h3 := (mul_dvd_mul_iff_left (pow_ne_zero e (Nat.cast_ne_zero.mpr hp.out.ne_zero))).mp h2
  have hcop : IsCoprime ((p : ℤ) ^ (K + 1)) ((u : ℤ)) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hu)).pow_left
  exact hcop.dvd_of_dvd_mul_left h3

/-- **The `p²`-shift of a product**: factors not divisible by `p²` shift by one `p`-adic place. -/
theorem sh_prod_shift (f : ℕ → ℤ) :
    ∀ B : ℕ, (∀ i < B, ¬ (p : ℤ) ^ 2 ∣ f i) →
      Sh p (∏ i ∈ range B, f i) (∏ i ∈ range B, ((p : ℤ) ^ 2 + f i)) := by
  intro B
  induction B with
  | zero => intro _ K _; simp
  | succ B ih =>
    intro hf
    rw [prod_range_succ, prod_range_succ]
    refine (ih fun i hi => hf i (by omega)).mul fun K hK => ?_
    rw [add_sub_cancel_right]
    refine pow_dvd_pow _ ?_
    by_contra hc
    exact hf B (by omega) ((pow_dvd_pow _ (by omega)).trans hK)

/-- **The `p²`-shift of a binomial**: `C(p² − a, B) ≡ (−1)^B C(a + B − 1, B)` one place past its
valuation, for `1 ≤ a` and `a + B ≤ p²`. -/
theorem sh_choose_shift {a B : ℕ} (ha : 1 ≤ a) (haB : a + B ≤ p ^ 2) :
    Sh p ((-1 : ℤ) ^ B * ((a + B - 1).choose B : ℕ)) (((p ^ 2 - a).choose B : ℕ) : ℤ) := by
  refine Sh.cancel (Nat.factorial_ne_zero B) ?_
  have hasc : ((B.factorial : ℕ) : ℤ) * ((-1 : ℤ) ^ B * ((a + B - 1).choose B : ℕ))
      = ∏ i ∈ range B, (-((a : ℤ) + i)) := by
    have e1 : ∏ i ∈ range B, ((a : ℤ) + i) = ((a.ascFactorial B : ℕ) : ℤ) := by
      rw [Nat.ascFactorial_eq_prod_range]
      push_cast
      rfl
    rw [prod_neg, card_range, e1, Nat.ascFactorial_eq_factorial_mul_choose']
    push_cast
    ring
  have hdesc : ((B.factorial : ℕ) : ℤ) * (((p ^ 2 - a).choose B : ℕ) : ℤ)
      = ∏ i ∈ range B, ((p : ℤ) ^ 2 + -((a : ℤ) + i)) := by
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    push_cast
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hasc, hdesc]
  refine sh_prod_shift _ B fun i hi => ?_
  rw [dvd_neg]
  intro hd
  have h0 : (0 : ℤ) < (a : ℤ) + i := by positivity
  have h1 := Int.le_of_dvd h0 hd
  have h2 : ((a : ℤ) + i) < (p : ℤ) ^ 2 := by exact_mod_cast (show a + i < p ^ 2 by omega)
  linarith

/-- `C(p² + d, d) ≡ 1 (mod p)` for `d < p²` — Lucas twice. -/
theorem choose_sq_add_cast_one {d : ℕ} (hd : d < p ^ 2) :
    (((p ^ 2 + d).choose d : ℕ) : ZMod p) = 1 := by
  have hp0 := hp.out.pos
  have hdp : d / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp0]
    nlinarith
  have h1 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p ^ 2 + d) (k := d)
  rw [← ZMod.natCast_eq_natCast_iff] at h1
  rw [h1]
  have e1 : (p ^ 2 + d) % p = d % p := by
    rw [sq, Nat.mul_add_mod]
  have e2 : (p ^ 2 + d) / p = d / p + p := by
    rw [sq, Nat.mul_add_div hp0]
    ring
  rw [e1, e2, Nat.choose_self]
  have h2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := d / p + p) (k := d / p)
  rw [← ZMod.natCast_eq_natCast_iff] at h2
  push_cast
  rw [h2]
  have e3 : (d / p + p) % p = d / p := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hdp]
  have e4 : (d / p + p) / p = 1 := by
    rw [Nat.add_div_right _ hp0, Nat.div_eq_of_lt hdp]
  rw [e3, e4, Nat.mod_eq_of_lt hdp, Nat.div_eq_of_lt hdp, Nat.choose_self, Nat.choose_zero_right]
  simp

/-- `C(p² + d, p²) ≡ 1 (mod p)` for `d < p²` — Lucas twice. -/
theorem choose_sq_add_sq_cast_one {d : ℕ} (hd : d < p ^ 2) :
    (((p ^ 2 + d).choose (p ^ 2) : ℕ) : ZMod p) = 1 := by
  have hp0 := hp.out.pos
  have hdp : d / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp0]
    nlinarith
  have h1 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p ^ 2 + d) (k := p ^ 2)
  rw [← ZMod.natCast_eq_natCast_iff] at h1
  rw [h1]
  have e1 : (p ^ 2 + d) % p = d % p := by
    rw [sq, Nat.mul_add_mod]
  have e2 : (p ^ 2 + d) / p = d / p + p := by
    rw [sq, Nat.mul_add_div hp0]
    ring
  have e5 : p ^ 2 % p = 0 := by rw [sq, Nat.mul_mod_right]
  have e6 : p ^ 2 / p = p := by rw [sq, Nat.mul_div_cancel _ hp0]
  rw [e1, e2, e5, e6, Nat.choose_zero_right]
  have h2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := d / p + p) (k := p)
  rw [← ZMod.natCast_eq_natCast_iff] at h2
  push_cast
  rw [h2]
  have e3 : (d / p + p) % p = d / p := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hdp]
  have e4 : (d / p + p) / p = 1 := by
    rw [Nat.add_div_right _ hp0, Nat.div_eq_of_lt hdp]
  rw [e3, e4, Nat.mod_self, Nat.div_self hp0, Nat.choose_zero_right, Nat.choose_self]
  simp

/-- **The pair's binomial**: `C(m, p² + j)` shifts `C(m, j)` by one place, for `p² + j ≤ m < 2p²`. -/
theorem sh_choose_pair {m j : ℕ} (hm : p ^ 2 + j ≤ m) (hm2 : m < p ^ 2 + p ^ 2) :
    Sh p ((m.choose j : ℕ) : ℤ) ((m.choose (p ^ 2 + j) : ℕ) : ℤ) := by
  have hid := Nat.choose_mul (n := m) (k := p ^ 2 + j) (s := j) (by omega)
  rw [show p ^ 2 + j - j = p ^ 2 by omega] at hid
  have hU : (((p ^ 2 + j).choose j : ℕ) : ZMod p) = 1 := choose_sq_add_cast_one (by omega)
  have hU' : (((m - j).choose (p ^ 2) : ℕ) : ZMod p) = 1 := by
    rw [show m - j = p ^ 2 + (m - j - p ^ 2) by omega]
    exact choose_sq_add_sq_cast_one (by omega)
  refine sh_of_mul_eq (U := (p ^ 2 + j).choose j) (U' := (m - j).choose (p ^ 2)) ?_ ?_ ?_
  · exact_mod_cast hid
  · intro hd
    rw [← ZMod.natCast_eq_zero_iff] at hd
    rw [hd] at hU
    exact zero_ne_one hU
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hU, hU', sub_self]

end Sh

/-! ## 2. `H(p² + j)` against `H(j)` -/

section H
variable {p : ℕ} [hp : Fact p.Prime]

/-- **The member's `H` shifts by `p²`**: `H(p² + j)` agrees with `H(j)` one place past `v_p H(j)`,
for `j < n` at a window prime. -/
theorem sh_Hfun {n j : ℕ} (hsq : 26 * n + 1 < p ^ 2) (hj : j < n) :
    Sh p (Hfun n j) (Hfun n ((p ^ 2 + j : ℕ) : ℤ)) := by
  rw [Hfun_of_le n j (by omega), Hfun_of_gt n (p ^ 2 + j) (by omega)]
  have s1 := sh_choose_shift (p := p) (a := 13 * n + 1 - j) (B := 13 * n) (by omega) (by omega)
  have s2 := sh_choose_shift (p := p) (a := 15 * n + 1 - j) (B := 9 * n) (by omega) (by omega)
  have s3 := sh_choose_shift (p := p) (a := 17 * n + 1 - j) (B := 5 * n) (by omega) (by omega)
  rw [show 13 * n + 1 - j + 13 * n - 1 = 26 * n - j by omega,
    show p ^ 2 - (13 * n + 1 - j) = p ^ 2 + j - 13 * n - 1 by omega] at s1
  rw [show 15 * n + 1 - j + 9 * n - 1 = 24 * n - j by omega,
    show p ^ 2 - (15 * n + 1 - j) = p ^ 2 + j - 15 * n - 1 by omega] at s2
  rw [show 17 * n + 1 - j + 5 * n - 1 = 22 * n - j by omega,
    show p ^ 2 - (17 * n + 1 - j) = p ^ 2 + j - 17 * n - 1 by omega] at s3
  have h := (s1.mul s2).mul s3
  have e : (-1 : ℤ) ^ (27 * n) * (((26 * n - j).choose (13 * n) * (24 * n - j).choose (9 * n)
        * (22 * n - j).choose (5 * n) : ℕ) : ℤ)
      = (-1 : ℤ) ^ (13 * n) * (((26 * n - j).choose (13 * n) : ℕ) : ℤ)
        * ((-1 : ℤ) ^ (9 * n) * (((24 * n - j).choose (9 * n) : ℕ) : ℤ))
        * ((-1 : ℤ) ^ (5 * n) * (((22 * n - j).choose (5 * n) : ℕ) : ℤ)) := by
    rw [show 27 * n = 13 * n + 9 * n + 5 * n by ring, pow_add, pow_add]
    push_cast
    ring
  rw [e]
  push_cast at h ⊢
  exact h

end H

/-! ## 3. The second carry, and the three blocks' floors -/

section Carry
variable {p : ℕ} [hp : Fact p.Prime]

/-- **Kummer with two digits and a total past `p²`**: when `A` and `S − A` are both below `p²` but
`S ≥ p²`, the tens addition carries too — `v_p C(S, A) = cb + 1`. -/
theorem padicValNat_choose_eq_cb_succ {S A : ℕ} (hA : A ≤ S) (hS : p ^ 2 ≤ S) (hS3 : S < p ^ 3)
    (hAp : A < p ^ 2) (hSA : S - A < p ^ 2) : padicValNat p (S.choose A) = cb p S A + 1 := by
  have hp0 := hp.out.pos
  obtain ⟨x, rfl⟩ : ∃ x, S = x + A := ⟨S - A, by omega⟩
  rw [show x + A - A = x by omega] at hSA
  have hp2 : 0 < p ^ 2 := by positivity
  have hlog : Nat.log p (x + A) < 3 := Nat.log_lt_of_lt_pow (by omega) hS3
  rw [padicValNat_choose' hlog]
  have hIco : Finset.Ico 1 3 = ({1, 2} : Finset ℕ) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  have h2 : p ^ 2 ≤ A % p ^ 2 + x % p ^ 2 := by
    rw [Nat.mod_eq_of_lt hAp, Nat.mod_eq_of_lt hSA]
    omega
  rw [hIco, Finset.filter_insert, Finset.filter_singleton]
  by_cases h1 : p ≤ A % p + x % p
  · have hc : (x + A) % p < A % p := (carry_bit p x A hp0).1 h1
    simp [h1, h2, hc, cb]
  · have hc : ¬ ((x + A) % p < A % p) := fun h => h1 ((carry_bit p x A hp0).2 h)
    simp [h1, h2, hc, cb]

theorem pow_cb_succ_dvd_choose {S A : ℕ} (hA : A ≤ S) (hS : p ^ 2 ≤ S) (hS3 : S < p ^ 3)
    (hAp : A < p ^ 2) (hSA : S - A < p ^ 2) : p ^ (cb p S A + 1) ∣ S.choose A := by
  rw [← padicValNat_choose_eq_cb_succ hA hS hS3 hAp hSA]
  exact pow_padicValNat_dvd

/-- The three blocks' units floor, below the first zero. -/
theorem pow_Hlo_dvd {n i : ℕ} (hi : i ≤ 13 * n) :
    (p : ℤ) ^ (cb p (26 * n - i) (13 * n) + cb p (24 * n - i) (9 * n) + cb p (22 * n - i) (5 * n))
      ∣ Hfun n i := by
  rw [Hfun_of_le n i hi]
  have hA : p ^ cb p (26 * n - i) (13 * n) ∣ (26 * n - i).choose (13 * n) :=
    pow_cb_dvd_choose (by omega)
  have hB : p ^ cb p (24 * n - i) (9 * n) ∣ (24 * n - i).choose (9 * n) :=
    pow_cb_dvd_choose (by omega)
  have hC : p ^ cb p (22 * n - i) (5 * n) ∣ (22 * n - i).choose (5 * n) :=
    pow_cb_dvd_choose (by omega)
  have hz := Int.natCast_dvd_natCast.2 (mul_dvd_mul (mul_dvd_mul hA hB) hC)
  push_cast at hz
  rw [pow_add, pow_add]
  exact Dvd.dvd.mul_left (by push_cast; exact hz) _

/-- The three blocks' units floor, past the second zero. -/
theorem pow_Hhi_dvd {n i : ℕ} (hi : 26 * n < i) :
    (p : ℤ) ^ (cb p (i - 13 * n - 1) (13 * n) + cb p (i - 15 * n - 1) (9 * n)
        + cb p (i - 17 * n - 1) (5 * n)) ∣ Hfun n i := by
  rw [Hfun_of_gt n i hi]
  have hA : p ^ cb p (i - 13 * n - 1) (13 * n) ∣ (i - 13 * n - 1).choose (13 * n) :=
    pow_cb_dvd_choose (by omega)
  have hB : p ^ cb p (i - 15 * n - 1) (9 * n) ∣ (i - 15 * n - 1).choose (9 * n) :=
    pow_cb_dvd_choose (by omega)
  have hC : p ^ cb p (i - 17 * n - 1) (5 * n) ∣ (i - 17 * n - 1).choose (5 * n) :=
    pow_cb_dvd_choose (by omega)
  have hz := Int.natCast_dvd_natCast.2 (mul_dvd_mul (mul_dvd_mul hA hB) hC)
  push_cast at hz ⊢
  rw [pow_add, pow_add]
  exact hz

/-- **A term of `h_m` in the middle range carries its units count PLUS the tens carry.** -/
theorem pow_term_lo_succ {n m i : ℕ} (hi : i ≤ 13 * n) (him : i ≤ m) (hm : p ^ 2 ≤ m)
    (hm3 : m < p ^ 3) (hip : i < p ^ 2) (hmi : m - i < p ^ 2) :
    (p : ℤ) ^ (kumLo n p m i + 1) ∣ (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * Hfun n i := by
  have h1 := Int.natCast_dvd_natCast.2 (pow_cb_succ_dvd_choose (p := p) him hm hm3 hip hmi)
  push_cast at h1
  have h2 := pow_Hlo_dvd (p := p) hi
  have e : kumLo n p m i + 1 = (cb p m i + 1)
      + (cb p (26 * n - i) (13 * n) + cb p (24 * n - i) (9 * n) + cb p (22 * n - i) (5 * n)) := by
    unfold kumLo; ring
  rw [e, pow_add, mul_assoc]
  exact Dvd.dvd.mul_left (mul_dvd_mul h1 h2) _

theorem pow_term_hi_succ {n m i : ℕ} (hi : 26 * n < i) (him : i ≤ m) (hm : p ^ 2 ≤ m)
    (hm3 : m < p ^ 3) (hip : i < p ^ 2) (hmi : m - i < p ^ 2) :
    (p : ℤ) ^ (kumHi n p m i + 1) ∣ (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * Hfun n i := by
  have h1 := Int.natCast_dvd_natCast.2 (pow_cb_succ_dvd_choose (p := p) him hm hm3 hip hmi)
  push_cast at h1
  have h2 := pow_Hhi_dvd (p := p) hi
  have e : kumHi n p m i + 1 = (cb p m i + 1)
      + (cb p (i - 13 * n - 1) (13 * n) + cb p (i - 15 * n - 1) (9 * n)
        + cb p (i - 17 * n - 1) (5 * n)) := by
    unfold kumHi; ring
  rw [e, pow_add, mul_assoc]
  exact Dvd.dvd.mul_left (mul_dvd_mul h1 h2) _

end Carry

/-! ## 4. The pair -/

section Pair
variable {p : ℕ} [hp : Fact p.Prime]

/-- **THE PAIRING.**  At `m ≥ p² + j`, the terms `i = j` and `i = p² + j` of `h_m` cancel to one
place past any power of `p` that divides the first. -/
theorem pair_dvd {n m j K : ℕ} (hsq : 26 * n + 1 < p ^ 2) (hj : j < n) (hm : p ^ 2 + j ≤ m)
    (hm2 : m < p ^ 2 + p ^ 2)
    (hK : (p : ℤ) ^ K ∣ (-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * Hfun n j) :
    (p : ℤ) ^ (K + 1) ∣ (-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * Hfun n j
      + (-1 : ℤ) ^ (m - (p ^ 2 + j)) * (m.choose (p ^ 2 + j) : ℤ) * Hfun n ((p ^ 2 + j : ℕ) : ℤ) := by
  have hodd : Odd p := hp.out.odd_of_ne_two (by rintro rfl; omega)
  have hsign : (-1 : ℤ) ^ (m - j) = -(-1 : ℤ) ^ (m - (p ^ 2 + j)) := by
    rw [show m - j = (m - (p ^ 2 + j)) + p ^ 2 by omega, pow_add, (hodd.pow).neg_one_pow]
    ring
  have hs := (sh_choose_pair (p := p) hm hm2).mul (sh_Hfun (p := p) hsq hj)
  have hK' : (p : ℤ) ^ K ∣ (m.choose j : ℤ) * Hfun n j := by
    have h := Dvd.dvd.mul_left hK ((-1 : ℤ) ^ (m - j))
    have e : (-1 : ℤ) ^ (m - j) * ((-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * Hfun n j)
        = (m.choose j : ℤ) * Hfun n j := by
      rw [← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rwa [e] at h
  have h := hs K (by exact_mod_cast hK')
  push_cast at h
  have e : (-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * Hfun n j
      + (-1 : ℤ) ^ (m - (p ^ 2 + j)) * (m.choose (p ^ 2 + j) : ℤ) * Hfun n ((p ^ 2 + j : ℕ) : ℤ)
      = (-1 : ℤ) ^ (m - (p ^ 2 + j))
        * ((m.choose (p ^ 2 + j) : ℤ) * Hfun n ((p ^ 2 + j : ℕ) : ℤ)
          - (m.choose j : ℤ) * Hfun n j) := by
    rw [hsign]
    ring
  rw [e]
  push_cast
  exact Dvd.dvd.mul_left h _

end Pair

/-! ## 5. `h_m` at `m ≥ p²`: pairs, the middle, and the bound -/

section Rows
variable {p : ℕ} [hp : Fact p.Prime]

/-- **The `m ≥ p²` reduction.**  With `μ = m − p²`, `h_m` is the `μ + 1` pairs `(j, p² + j)` plus
the middle `μ < i < p²`, whose terms all carry the tens carry of `C(m, i)`.  So a per-term units
floor `w + e ≤ kum + 1` gives `p^{w + e + 1} ∣ p·h_m`: ONE MORE than the `m < p²` count, which is
exactly the tens carry `C(m, L)` itself pays (`padicValNat_LC_sq`). -/
theorem pow_dvd_p_hc_of_sq {n r w e : ℕ} (hsq : 26 * n + 1 < p ^ 2) (hr : r < 16 * n)
    (hm : p ^ 2 ≤ 11 * n + 1 + r)
    (hlo : ∀ i, i ≤ 13 * n → w + e ≤ kumLo n p (11 * n + 1 + r) i + 1)
    (hhi : ∀ i, 26 * n < i → i ≤ 11 * n + 1 + r → w + e ≤ kumHi n p (11 * n + 1 + r) i + 1) :
    (p : ℤ) ^ (w + (e + 1)) ∣ (p : ℤ) * hc n (11 * n + 1 + r) := by
  have hp1 := hp.out.one_lt
  set m := 11 * n + 1 + r with hmdef
  have hm27 : m ≤ 27 * n := by omega
  have hm2 : m < p ^ 2 + p ^ 2 := by omega
  have hm3 : m < p ^ 3 := by
    have : p ^ 3 = p * p ^ 2 := by ring
    have : 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  set μ := m - p ^ 2 with hμ
  have hμn : μ < n := by omega
  let T : ℕ → ℤ := fun i => (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * Hfun n i
  have hsplit : hc n m = ∑ j ∈ range (μ + 1), (T j + T (p ^ 2 + j))
      + ∑ i ∈ Ico (μ + 1) (p ^ 2), T i := by
    rw [hc_eq_signed_sum, sum_add_distrib]
    have h1 := sum_range_add_sum_Ico T (show p ^ 2 ≤ m + 1 by omega)
    have h2 := sum_range_add_sum_Ico T (show μ + 1 ≤ p ^ 2 by omega)
    have h3 : ∑ i ∈ Ico (p ^ 2) (m + 1), T i = ∑ j ∈ range (μ + 1), T (p ^ 2 + j) := by
      rw [sum_Ico_eq_sum_range, show m + 1 - p ^ 2 = μ + 1 by omega]
    rw [← h1, ← h2, h3]
    ring
  rw [hsplit, mul_add, mul_sum, mul_sum]
  refine dvd_add (dvd_sum fun j hj => ?_) (dvd_sum fun i hi => ?_)
  · -- a pair
    have hj' : j ≤ μ := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hK := pow_kumLo_dvd_term (p := p) (n := n) (m := m) (i := j) (by omega) (by omega)
    have hpair := pair_dvd (p := p) hsq (show j < n by omega) (show p ^ 2 + j ≤ m by omega) hm2 hK
    have hb := hlo j (by omega)
    refine (pow_dvd_pow _ (show w + (e + 1) ≤ 1 + (kumLo n p m j + 1) by omega)).trans ?_
    rw [pow_add, pow_one]
    exact mul_dvd_mul_left _ hpair
  · -- the middle
    obtain ⟨hi1, hi2⟩ := mem_Ico.mp hi
    have him : i ≤ m := by omega
    have hmi : m - i < p ^ 2 := by omega
    by_cases hlo13 : i ≤ 13 * n
    · have ht := pow_term_lo_succ (p := p) hlo13 him hm hm3 hi2 hmi
      refine (pow_dvd_pow _ (show w + (e + 1) ≤ 1 + (kumLo n p m i + 1) by
        have := hlo i hlo13; omega)).trans ?_
      rw [pow_add, pow_one]
      exact mul_dvd_mul_left _ ht
    · by_cases hhi26 : 26 * n < i
      · have ht := pow_term_hi_succ (p := p) hhi26 him hm hm3 hi2 hmi
        refine (pow_dvd_pow _ (show w + (e + 1) ≤ 1 + (kumHi n p m i + 1) by
          have := hhi i hhi26 him; omega)).trans ?_
        rw [pow_add, pow_one]
        exact mul_dvd_mul_left _ ht
      · have hz : T i = 0 := by
          simp only [T]
          rw [Hfun_eq_zero n i (by omega) (by omega), mul_zero]
        rw [hz, mul_zero]
        exact dvd_zero _

/-- The end of `Zeta2PtpKummer.pval_coeff_of_kum`, with its divisibility as the hypothesis:
`p^{w + v_p(L·C(m,L))} ∣ p·h_m` gives `PVal p w (coeff n r)`. -/
theorem pval_coeff_of_dvd {n r w : ℕ} (hp' : p ∈ phiWindow n)
    (h1 : (p : ℤ) ^ (w + padicValNat p (LC n r)) ∣ (p : ℤ) * hc n (11 * n + 1 + r)) :
    PVal p w ((coeff n r : ℤ) : ℚ) := by
  have hpp := prime_of_mem_phiWindow hp'
  have hle := Zeta2PhiTDvd.le_of_mem_phiWindow hp'
  obtain ⟨e, u, hu, hLC⟩ := Nat.exists_eq_pow_mul_and_not_dvd (LC_ne_zero' n r) p hpp.ne_one
  have hu0 : u ≠ 0 := by rintro rfl; simp at hLC; exact LC_ne_zero' n r hLC
  have he : padicValNat p (LC n r) = e := by
    rw [hLC, padicValNat.mul (pow_ne_zero _ hpp.ne_zero) hu0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hu, add_zero]
  rw [he] at h1
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
  rw [hLC] at h2
  push_cast at h2
  rw [pow_add, mul_comm ((p : ℤ) ^ w), mul_assoc] at h2
  have h3 : (p : ℤ) ^ w ∣ (u : ℤ) * coeff n r :=
    (mul_dvd_mul_iff_left (pow_ne_zero e (Nat.cast_ne_zero.mpr hpp.ne_zero))).mp h2
  have hcop : IsCoprime ((p : ℤ) ^ w) ((u : ℤ)) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hu)).pow_left
  exact pval_of_pow_dvd hpp (hcop.dvd_of_dvd_mul_left h3)

end Rows

/-- **`v_p(L·C(m,L))` at `m ≥ p²`**: `v_p(L)`, the units carry, and the tens carry. -/
theorem padicValNat_LC_sq {n p r : ℕ} (hp : p ∈ phiWindow n) (hr : r < 16 * n)
    (hm : p ^ 2 ≤ 11 * n + 1 + r) :
    padicValNat p (LC n r)
      = (if (11 * n + 1) % p = 0 then 1 else 0) + cb p (11 * n + 1 + r) (11 * n + 1) + 1 := by
  have hpp := prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hsq := sq_gt_of_mem_phiWindow hp
  have hL0 : 11 * n + 1 ≠ 0 := by omega
  have hC0 : (11 * n + 1 + r).choose (11 * n + 1) ≠ 0 := Nat.choose_pos (by omega) |>.ne'
  have hm3 : 11 * n + 1 + r < p ^ 3 := by
    have : p ^ 3 = p * p ^ 2 := by ring
    have : 2 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hpp.two_le
    omega
  rw [LC, padicValNat.mul hL0 hC0, Zeta2PtpKumRes.padicValNat_eq_ite_of_lt_sq hL0 (by omega),
    padicValNat_choose_eq_cb_succ (by omega) hm hm3 (by omega) (by omega)]
  ring

/-! ## 6. The residues at `m ≥ p²`: the target is the `m < p²` one plus the tens carry -/

/-- `targetR` against the target with `v_p(L·C(m,L))` replaced by its units part — the identity of
`Zeta2PtpKumRes.target_eq_res` with no `m < p²`. -/
theorem target_eq_res_units {n p r : ℕ} (hp : p ∈ phiWindow n) (hρ : 1 ≤ (r + 1) % p) (v : ℕ) :
    v + bbit n p r - 1
        + ((if (11 * n + 1) % p = 0 then 1 else 0) + cb p (11 * n + 1 + r) (11 * n + 1))
      = targetR p (n % p) ((r + 1) % p) v := by
  have hp0 := (prime_of_mem_phiWindow hp).pos
  have hp1 := (prime_of_mem_phiWindow hp).one_lt
  rw [bbit_eq_res, targetR]
  have hR := Nat.mod_lt (11 * (n % p)) hp0
  have hρp := Nat.mod_lt (r + 1) hp0
  have e1 : (11 * n + 1) % p = if (11 * (n % p)) % p + 1 < p then (11 * (n % p)) % p + 1
      else (11 * (n % p)) % p + 1 - p := by
    rw [Nat.add_mod, mul_mod_res 11 n p, Nat.mod_eq_of_lt hp1,
      Zeta2PtpCong.add_mod_split hR (by omega)]
  have e2 : (11 * n + 1 + r) % p = if (11 * (n % p)) % p + (r + 1) % p < p
      then (11 * (n % p)) % p + (r + 1) % p else (11 * (n % p)) % p + (r + 1) % p - p := by
    rw [Mres_eq, Mres, Zeta2PtpCong.add_mod_split hR (by omega)]
  have e1' : (11 * (n % p) % p + 1 < p ∧ (11 * n + 1) % p = 11 * (n % p) % p + 1)
      ∨ (p ≤ 11 * (n % p) % p + 1 ∧ (11 * n + 1) % p = 11 * (n % p) % p + 1 - p) := by
    rw [e1]
    split_ifs with h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨by omega, rfl⟩
  have e2' : (11 * (n % p) % p + (r + 1) % p < p
        ∧ (11 * n + 1 + r) % p = 11 * (n % p) % p + (r + 1) % p)
      ∨ (p ≤ 11 * (n % p) % p + (r + 1) % p
        ∧ (11 * n + 1 + r) % p = 11 * (n % p) % p + (r + 1) % p - p) := by
    rw [e2]
    split_ifs with h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨by omega, rfl⟩
  clear e1 e2
  unfold cb
  split_ifs <;> omega

/-- At a polar row the units part of `v_p(L·C(m,L))` is `1` — `Zeta2PtpKumRes.padicValNat_LC_polar`
with no `m < p²`. -/
theorem units_LC_polar {n p r : ℕ} (hp : p ∈ phiWindow n) (hpol : p ∣ r + 1) :
    (if (11 * n + 1) % p = 0 then 1 else 0) + cb p (11 * n + 1 + r) (11 * n + 1) = 1 := by
  have hp0 := (prime_of_mem_phiWindow hp).pos
  have hp1 := (prime_of_mem_phiWindow hp).one_lt
  have hR := Nat.mod_lt (11 * n) hp0
  have e2 : (11 * n + 1 + r) % p = (11 * n) % p := by
    rw [show 11 * n + 1 + r = 11 * n + (r + 1) by ring, Nat.add_mod, Nat.mod_eq_zero_of_dvd hpol,
      Nat.add_zero, Nat.mod_mod]
  have e1 : (11 * n + 1) % p = if (11 * n) % p + 1 < p then (11 * n) % p + 1
      else (11 * n) % p + 1 - p := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hp1, Zeta2PtpCong.add_mod_split hR (by omega)]
  have e1' : ((11 * n) % p + 1 < p ∧ (11 * n + 1) % p = (11 * n) % p + 1)
      ∨ (p ≤ (11 * n) % p + 1 ∧ (11 * n + 1) % p = (11 * n) % p + 1 - p) := by
    rw [e1]
    split_ifs with h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨by omega, rfl⟩
  clear e1
  unfold cb
  rw [e2]
  split_ifs <;> omega

/-! ## 7. Every `m ≥ p²` row OFF the polar run strata is closed -/

/-- **THE `m ≥ p²` ROWS, CLOSED — except the polar rows on the five run strata.**  Non-polar rows
take the units floor from `Zeta2PtpKumRows.residue_main`, polar rows off the strata from
`polar_main`; the pairing supplies the one place the tens carry of `C(m, L)` costs. -/
theorem coeff_bound_sq_offrun {n p r : ℕ} (hp : p ∈ phiWindow n) (hr : r < 16 * n)
    (hsq : p ^ 2 ≤ 11 * n + 1 + r) (hnot : ¬ (p ∣ r + 1 ∧ RunStrata p (n % p))) :
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r - 1) ((coeff n r : ℤ) : ℚ) := by
  have hpp := prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 := hpp.pos
  have hp1 := hpp.one_lt
  have hwin := sq_gt_of_mem_phiWindow hp
  refine pval_coeff_of_dvd hp ?_
  rw [padicValNat_LC_sq hp hr hsq]
  by_cases hpol : p ∣ r + 1
  · have hrun : ¬ RunStrata p (n % p) := fun h => hnot ⟨hpol, h⟩
    have hρ0 : (r + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hpol
    have hu1 := units_LC_polar hp hpol
    rw [bbit_polar hpol, hu1]
    refine pow_dvd_p_hc_of_sq hwin hr hsq (fun i hi => ?_) (fun i hi _ => ?_)
    · rw [kumLo_eq_res hp0 hi, hρ0]
      rcases polar_main (n := n) hp0 (Nat.mod_lt i hp0) with h1 | ⟨h1, _⟩
      · exact absurd h1 hrun
      · omega
    · rw [kumHi_eq_res hp1 hi, hρ0]
      rcases polar_main (n := n) hp0 (Nat.mod_lt i hp0) with h1 | ⟨_, h1⟩
      · exact absurd h1 hrun
      · omega
  · have hρ1 : 1 ≤ (r + 1) % p := by
      rcases Nat.eq_zero_or_pos ((r + 1) % p) with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) hpol
      · exact h
    have hρ := Nat.mod_lt (r + 1) hp0
    have ht := target_eq_res_units hp hρ1 (phiT (Int.fract ((n : ℚ) / (p : ℚ))))
    refine pow_dvd_p_hc_of_sq hwin hr hsq (fun i hi => ?_) (fun i hi _ => ?_)
    · rw [ht, kumLo_eq_res hp0 hi]
      exact (residue_main hp0 hρ1 hρ (Nat.mod_lt i hp0)).1
    · rw [ht, kumHi_eq_res hp1 hi]
      exact (residue_main hp0 hρ1 hρ (Nat.mod_lt i hp0)).2

/-! ## 8. `ResidualNarrowOpen`, reduced to the polar rows on the run strata -/

/-- **THE RESIDUAL, NARROWED TO THE RUN STRATA**: the polar rows `p ∣ r+1` whose residue
`n % p` lies on one of the five run strata — at every `m`, below and above `p²`. -/
def ResidualRunOpen : Prop :=
  ∀ n p r : ℕ, p ∈ phiWindow n → r < 16 * n → p ∣ r + 1 → RunStrata p (n % p) →
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))) + bbit n p r - 1) ((coeff n r : ℤ) : ℚ)

/-- **`ResidualNarrowOpen` FROM THE RUN STRATA ALONE.**  Read the type: the `p² ≤ m` disjunct is
discharged at every row off the polar run strata; only `ResidualRunOpen` is named. -/
theorem residualNarrowOpen_of_run (h : ResidualRunOpen) : ResidualNarrowOpen := by
  intro n p r hp hr hcase
  by_cases hrun : p ∣ r + 1 ∧ RunStrata p (n % p)
  · exact h n p r hp hr hrun.1 hrun.2
  · rcases hcase with h1 | h1
    · exact absurd h1 hrun
    · exact coeff_bound_sq_offrun hp hr h1 hrun

theorem polyHalfOpen_of_run (h : ResidualRunOpen) : PolyHalfOpen :=
  polyHalfOpen_of_narrow (residualNarrowOpen_of_run h)

/-! ## 9. Pins -/

/-- The pairing is REACHED: at `n = 20, p = 23` (`p² = 529`) the row `r = 308` has `m = p²`, so
`μ = 0` and the one pair is `(0, 529)`. -/
theorem pin_20_23 : 23 ∈ phiWindow 20 ∧ 23 ^ 2 = 11 * 20 + 1 + 308 ∧ ¬ 23 ∣ 308 + 1 := by
  refine ⟨by decide +kernel, by norm_num, by decide⟩

end Zeta2PtpResPair

#print axioms Zeta2PtpResPair.eq_zero_of_forall_pow_dvd
#check @Zeta2PtpResPair.eq_zero_of_forall_pow_dvd
#print axioms Zeta2PtpResPair.Sh.zero_left
#check @Zeta2PtpResPair.Sh.zero_left
#print axioms Zeta2PtpResPair.Sh.mul
#check @Zeta2PtpResPair.Sh.mul
#print axioms Zeta2PtpResPair.sh_of_mul_eq
#check @Zeta2PtpResPair.sh_of_mul_eq
#print axioms Zeta2PtpResPair.Sh.cancel
#check @Zeta2PtpResPair.Sh.cancel
#print axioms Zeta2PtpResPair.sh_prod_shift
#check @Zeta2PtpResPair.sh_prod_shift
#print axioms Zeta2PtpResPair.sh_choose_shift
#check @Zeta2PtpResPair.sh_choose_shift
#print axioms Zeta2PtpResPair.choose_sq_add_cast_one
#check @Zeta2PtpResPair.choose_sq_add_cast_one
#print axioms Zeta2PtpResPair.choose_sq_add_sq_cast_one
#check @Zeta2PtpResPair.choose_sq_add_sq_cast_one
#print axioms Zeta2PtpResPair.sh_choose_pair
#check @Zeta2PtpResPair.sh_choose_pair
#print axioms Zeta2PtpResPair.sh_Hfun
#check @Zeta2PtpResPair.sh_Hfun
#print axioms Zeta2PtpResPair.padicValNat_choose_eq_cb_succ
#check @Zeta2PtpResPair.padicValNat_choose_eq_cb_succ
#print axioms Zeta2PtpResPair.pow_cb_succ_dvd_choose
#check @Zeta2PtpResPair.pow_cb_succ_dvd_choose
#print axioms Zeta2PtpResPair.pow_Hlo_dvd
#check @Zeta2PtpResPair.pow_Hlo_dvd
#print axioms Zeta2PtpResPair.pow_Hhi_dvd
#check @Zeta2PtpResPair.pow_Hhi_dvd
#print axioms Zeta2PtpResPair.pow_term_lo_succ
#check @Zeta2PtpResPair.pow_term_lo_succ
#print axioms Zeta2PtpResPair.pow_term_hi_succ
#check @Zeta2PtpResPair.pow_term_hi_succ
#print axioms Zeta2PtpResPair.pair_dvd
#check @Zeta2PtpResPair.pair_dvd
#print axioms Zeta2PtpResPair.pow_dvd_p_hc_of_sq
#check @Zeta2PtpResPair.pow_dvd_p_hc_of_sq
#print axioms Zeta2PtpResPair.pval_coeff_of_dvd
#check @Zeta2PtpResPair.pval_coeff_of_dvd
#print axioms Zeta2PtpResPair.padicValNat_LC_sq
#check @Zeta2PtpResPair.padicValNat_LC_sq
#print axioms Zeta2PtpResPair.target_eq_res_units
#check @Zeta2PtpResPair.target_eq_res_units
#print axioms Zeta2PtpResPair.units_LC_polar
#check @Zeta2PtpResPair.units_LC_polar
#print axioms Zeta2PtpResPair.coeff_bound_sq_offrun
#check @Zeta2PtpResPair.coeff_bound_sq_offrun
#print axioms Zeta2PtpResPair.residualNarrowOpen_of_run
#check @Zeta2PtpResPair.residualNarrowOpen_of_run
#print axioms Zeta2PtpResPair.polyHalfOpen_of_run
#check @Zeta2PtpResPair.polyHalfOpen_of_run
#print axioms Zeta2PtpResPair.pin_20_23
#check @Zeta2PtpResPair.pin_20_23
#print Zeta2PtpResPair.ResidualRunOpen
