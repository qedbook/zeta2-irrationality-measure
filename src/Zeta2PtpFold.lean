/-
# Row PT-P, part (b), layer 1 — THE FOLD LAW: the pair `(j, p² + j)` of `h_m` to SECOND order,
# and the tens-digit Lucas congruence mod `p²` for the middle terms

At a polar run-strata row with `m = p² + μ ≥ p²` (`ptp_mbig_probe.py`), `h_m`'s terms are two
places short and cancel in two levels.  This file is the part every stratum shares.

* **`Sh2`** — `x' ≡ x·(1 + p·ℓ)` one `p`-adic place further than `Zeta2PtpResPair.Sh`: for every
  `K` with `p^K ∣ x`, `p^{K+2} ∣ x' − x − p·ℓ·x`, with `ℓ ∈ ZMod p`.  It is multiplicative with
  ADDED `ℓ` (`Sh2.mul`), insensitive to a common factor (`Sh2.cancel`), and a factor `f` with
  `p² ∤ f` shifts to `p² + f` with `ℓ = (f/p)⁻¹` or `0` (`sh2_single`), so a product of such
  factors carries the SUM (`sh2_prod`) — a harmonic sum over the multiples of `p` in its window
  (`sum_gp_pos`, `hsum`).
* The three shifts `h_m` needs: the `H` binomials (`sh2_choose_shift`), `C(p² + d, d) ≡
  1 + p·H_{⌊d/p⌋} (mod p²)` (`choose_sq_add_hsum`), and the pair binomial (`sh2_choose_pair`).
* **`fold_law`** — `T(j) + T(p² + j) ≡ −p·λ(j)·T(j) (mod p^{K+2})` whenever `p^K ∣ T(j)`, with
  `λ = lamC + lamH` (`ptp_mbig_probe.py` arm D7, 351 379 of 351 379 pair indices).
* **`pair_block_sq`** — a pair block whose `λ` is constant on the units support and whose raw
  block is `0 mod p` has a FOLDED block `0 mod p²`.
* **`choose_mul_add_sq`** — `C(pM + a, pt + b) ≡ C(pM, pt)·C(a, b) (mod p²)` whenever
  `p ∣ C(M, t)`: the middle terms' tens carry, as a CONSTANT of the block times the units digit.

Probe: `ptp_mbig_probe.py` / `.out`.  Falsifier: `falsify_ptpfold.sh` / `out_ptpfold_falsify.txt`.
Runner: `run_resid.sh`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2PtpResPair
import Zeta2PtpRunBlock

set_option maxRecDepth 20000

namespace Zeta2PtpFold

open Zeta2PtpResPair Zeta2PtpCoeff Zeta2NewtonAssemble Zeta2PtpKummer Finset

/-! ## 1. `Sh2` -/

/-- `Sh2 p x x' ℓ`: `x' − x ≡ p·ℓ·x` one `p`-adic place past `Sh`, at every power dividing `x`. -/
def Sh2 (p : ℕ) (x x' : ℤ) (ℓ : ZMod p) : Prop :=
  ∀ K : ℕ, (p : ℤ) ^ K ∣ x → (p : ℤ) ^ (K + 2) ∣ x' - x - (p : ℤ) * (ℓ.val : ℤ) * x

section Sh2
variable {p : ℕ} [hp : Fact p.Prime]

theorem dvd_rep {L : ℤ} {ℓ : ZMod p} (hL : ((L : ℤ) : ZMod p) = ℓ) :
    (p : ℤ) ∣ L - (ℓ.val : ℤ) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hL, ZMod.natCast_zmod_val, sub_self]

/-- `Sh2` from any integer representative of `ℓ`. -/
theorem Sh2.of_rep {x x' L : ℤ} {ℓ : ZMod p} (hL : ((L : ℤ) : ZMod p) = ℓ)
    (h : ∀ K : ℕ, (p : ℤ) ^ K ∣ x → (p : ℤ) ^ (K + 2) ∣ x' - x - (p : ℤ) * L * x) :
    Sh2 p x x' ℓ := by
  intro K hK
  have h2 : (p : ℤ) ^ (K + 2) ∣ (p : ℤ) * (L - (ℓ.val : ℤ)) * x := by
    rw [show K + 2 = 1 + 1 + K by ring, pow_add, pow_add, pow_one]
    exact mul_dvd_mul (mul_dvd_mul_left _ (dvd_rep hL)) hK
  have e : x' - x - (p : ℤ) * (ℓ.val : ℤ) * x
      = (x' - x - (p : ℤ) * L * x) + (p : ℤ) * (L - (ℓ.val : ℤ)) * x := by ring
  rw [e]
  exact dvd_add (h K hK) h2

theorem Sh2.zero_left {x' : ℤ} {ℓ : ZMod p} (h : Sh2 p 0 x' ℓ) : x' = 0 := by
  refine eq_zero_of_forall_pow_dvd (p := p) fun K => ?_
  have := h K (dvd_zero _)
  simp only [sub_zero, mul_zero] at this
  exact (pow_dvd_pow _ (by omega)).trans this

/-- The first-order consequences: `p^K ∣ x'` and `p^{K+1} ∣ x' − x`. -/
theorem Sh2.dvd_sub {x x' : ℤ} {ℓ : ZMod p} (h : Sh2 p x x' ℓ) {K : ℕ} (hK : (p : ℤ) ^ K ∣ x) :
    (p : ℤ) ^ (K + 1) ∣ x' - x := by
  have h1 := (pow_dvd_pow _ (Nat.le_succ (K + 1))).trans (h K hK)
  have h2 : (p : ℤ) ^ (K + 1) ∣ (p : ℤ) * (ℓ.val : ℤ) * x := by
    rw [pow_succ, mul_comm ((p : ℤ) ^ K)]
    exact mul_dvd_mul (dvd_mul_right _ _) hK
  have := dvd_add h1 h2
  rwa [sub_add_cancel] at this

theorem Sh2.dvd_right {x x' : ℤ} {ℓ : ZMod p} (h : Sh2 p x x' ℓ) {K : ℕ} (hK : (p : ℤ) ^ K ∣ x) :
    (p : ℤ) ^ K ∣ x' := by
  have := dvd_add ((pow_dvd_pow _ (Nat.le_succ K)).trans (h.dvd_sub hK)) hK
  rwa [sub_add_cancel] at this

/-- **`Sh2` is multiplicative, with the `ℓ`s ADDED.** -/
theorem Sh2.mul {x x' y y' : ℤ} {ℓ₁ ℓ₂ : ZMod p} (hx : Sh2 p x x' ℓ₁) (hy : Sh2 p y y' ℓ₂) :
    Sh2 p (x * y) (x' * y') (ℓ₁ + ℓ₂) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  refine Sh2.of_rep (L := (ℓ₁.val : ℤ) + (ℓ₂.val : ℤ)) (by push_cast; simp) ?_
  intro K hK
  by_cases hx0 : x = 0
  · subst hx0
    rw [Sh2.zero_left hx]
    simp
  by_cases hy0 : y = 0
  · subst hy0
    rw [Sh2.zero_left hy]
    simp
  have hK' : K ≤ padicValInt p x + padicValInt p y := by
    rcases (padicValInt_dvd_iff K (x * y)).1 hK with h | h
    · exact absurd h (mul_ne_zero hx0 hy0)
    · rwa [padicValInt.mul hx0 hy0] at h
  set a := padicValInt p x
  set b := padicValInt p y
  have hxa : (p : ℤ) ^ a ∣ x := padicValInt_dvd x
  have hyb : (p : ℤ) ^ b ∣ y := padicValInt_dvd y
  have hx1 := hx a hxa
  have hy1 := hy b hyb
  have hx2 := hx.dvd_right hxa
  have hx3 := hx.dvd_sub hxa
  have key : (p : ℤ) ^ (a + b + 2)
      ∣ x' * y' - x * y - (p : ℤ) * ((ℓ₁.val : ℤ) + (ℓ₂.val : ℤ)) * (x * y) := by
    have e : x' * y' - x * y - (p : ℤ) * ((ℓ₁.val : ℤ) + (ℓ₂.val : ℤ)) * (x * y)
        = x' * (y' - y - (p : ℤ) * (ℓ₂.val : ℤ) * y)
          + ((p : ℤ) * (ℓ₂.val : ℤ) * y) * (x' - x)
          + y * (x' - x - (p : ℤ) * (ℓ₁.val : ℤ) * x) := by ring
    rw [e]
    refine dvd_add (dvd_add ?_ ?_) ?_
    · rw [show a + b + 2 = a + (b + 2) by ring, pow_add]
      exact mul_dvd_mul hx2 hy1
    · rw [show a + b + 2 = (1 + b) + (a + 1) by ring, pow_add, pow_add (p : ℤ) 1 b, pow_one]
      exact mul_dvd_mul (mul_dvd_mul (dvd_mul_right _ _) hyb) hx3
    · rw [show a + b + 2 = b + (a + 2) by ring, pow_add]
      exact mul_dvd_mul hyb hx1
  exact (pow_dvd_pow _ (by omega)).trans key

/-- **`Sh2` is insensitive to a common nonzero factor.** -/
theorem Sh2.cancel {x x' : ℤ} {ℓ : ZMod p} {g : ℕ} (hg : g ≠ 0)
    (h : Sh2 p ((g : ℤ) * x) ((g : ℤ) * x') ℓ) : Sh2 p x x' ℓ := by
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
        - (p : ℤ) * (ℓ.val : ℤ) * ((p : ℤ) ^ e * (u : ℤ) * x)
      = (p : ℤ) ^ e * ((u : ℤ) * (x' - x - (p : ℤ) * (ℓ.val : ℤ) * x)) by ring,
    show K + e + 2 = e + (K + 2) by ring, pow_add] at h2
  have h3 := (mul_dvd_mul_iff_left (pow_ne_zero e (Nat.cast_ne_zero.mpr hp.out.ne_zero))).mp h2
  have hcop : IsCoprime ((p : ℤ) ^ (K + 2)) ((u : ℤ)) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hu)).pow_left
  exact hcop.dvd_of_dvd_mul_left h3

/-- `Sh2` from a unit ratio: `x'·U = x·U'` with `p ∤ U` and `U' ≡ U·(1 + p·ℓ) (mod p²)`. -/
theorem Sh2.of_mul_eq {x x' : ℤ} {U U' : ℕ} {ℓ : ZMod p} (h : x' * U = x * U') (hU : ¬ p ∣ U)
    (hUU : (p : ℤ) ^ 2 ∣ (U' : ℤ) - U - (p : ℤ) * (ℓ.val : ℤ) * U) : Sh2 p x x' ℓ := by
  intro K hK
  have e : (x' - x - (p : ℤ) * (ℓ.val : ℤ) * x) * U
      = x * ((U' : ℤ) - U - (p : ℤ) * (ℓ.val : ℤ) * U) := by linear_combination h
  have h1 : (p : ℤ) ^ (K + 2) ∣ (x' - x - (p : ℤ) * (ℓ.val : ℤ) * x) * U := by
    rw [e, pow_add]
    exact mul_dvd_mul hK hUU
  have hcop : IsCoprime ((p : ℤ) ^ (K + 2)) ((U : ℤ)) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hU)).pow_left
  exact hcop.dvd_of_dvd_mul_right h1

/-- The `ℓ` of one factor under the `p²`-shift: `(f/p)⁻¹` when `p ∣ f`, else `0`. -/
def gp (p : ℕ) (f : ℤ) : ZMod p := if (p : ℤ) ∣ f then (((f / p : ℤ) : ZMod p))⁻¹ else 0

/-- **One factor**: `f ↦ p² + f` with `p² ∤ f`. -/
theorem sh2_single {f : ℤ} (hf : ¬ (p : ℤ) ^ 2 ∣ f) : Sh2 p f ((p : ℤ) ^ 2 + f) (gp p f) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  intro K hK
  unfold gp
  split_ifs with hd
  · obtain ⟨w, rfl⟩ := hd
    have hw : ¬ (p : ℤ) ∣ w := by
      rintro ⟨c, rfl⟩
      exact hf ⟨c, by ring⟩
    have hK1 : K ≤ 1 := by
      by_contra hc
      exact hf ((pow_dvd_pow _ (by omega)).trans hK)
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [Int.mul_ediv_cancel_left _ hp0]
    have hw0 : (w : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hinv : (p : ℤ) ∣ 1 - ((((w : ZMod p))⁻¹.val : ℕ) : ℤ) * w := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ hw0, sub_self]
    have e : (p : ℤ) ^ 2 + (p : ℤ) * w - (p : ℤ) * w
        - (p : ℤ) * ((((w : ZMod p))⁻¹.val : ℕ) : ℤ) * ((p : ℤ) * w)
        = (p : ℤ) ^ 2 * (1 - ((((w : ZMod p))⁻¹.val : ℕ) : ℤ) * w) := by ring
    rw [e]
    refine (pow_dvd_pow _ (show K + 2 ≤ 2 + 1 by omega)).trans ?_
    rw [pow_add, pow_one]
    exact mul_dvd_mul_left _ hinv
  · rcases K with _ | K
    · simp
    · exact absurd ((dvd_pow_self (p : ℤ) (Nat.succ_ne_zero K)).trans hK) hd

/-- **A product of shifted factors carries the SUM of their `ℓ`s.** -/
theorem sh2_prod (f : ℕ → ℤ) : ∀ B : ℕ, (∀ i < B, ¬ (p : ℤ) ^ 2 ∣ f i) →
    Sh2 p (∏ i ∈ range B, f i) (∏ i ∈ range B, ((p : ℤ) ^ 2 + f i)) (∑ i ∈ range B, gp p (f i))
  | 0 => fun _ K _ => by simp
  | B + 1 => fun hf => by
    rw [prod_range_succ, prod_range_succ, sum_range_succ]
    exact (sh2_prod f B fun i hi => hf i (by omega)).mul (sh2_single (hf B (by omega)))

end Sh2

/-! ## 2. The harmonic sums -/

/-- `Σ_{lo < w ≤ hi} w⁻¹` in `ZMod p`. -/
def hsum (p lo hi : ℕ) : ZMod p := ∑ w ∈ Ioc lo hi, ((w : ℕ) : ZMod p)⁻¹

section Harm
variable {p : ℕ} [hp : Fact p.Prime]

/-- **The `ℓ` of the run `a, a+1, …, a+B−1`** is the harmonic sum over its multiples of `p`. -/
theorem sum_gp_pos (a : ℕ) (ha : 1 ≤ a) : ∀ B : ℕ,
    ∑ i ∈ range B, gp p ((a + i : ℕ) : ℤ) = hsum p ((a - 1) / p) ((a + B - 1) / p)
  | 0 => by simp [hsum]
  | B + 1 => by
    rw [sum_range_succ, sum_gp_pos a ha B]
    have hmono : (a - 1) / p ≤ (a + B - 1) / p := Nat.div_le_div_right (by omega)
    have hsd : (a + B - 1 + 1) / p = (a + B - 1) / p + if p ∣ a + B - 1 + 1 then 1 else 0 :=
      Nat.succ_div
    rw [show a + B - 1 + 1 = a + B by omega] at hsd
    rw [show a + (B + 1) - 1 = a + B by omega]
    unfold gp hsum
    by_cases hd : p ∣ a + B
    · rw [ite_eq_left hd] at hsd
      rw [ite_eq_left (by exact_mod_cast hd), hsd, sum_Ioc_succ_top hmono, ← Int.natCast_div, hsd,
        Int.cast_natCast]
    · rw [ite_eq_right hd, add_zero] at hsd
      rw [ite_eq_right (by exact_mod_cast hd), hsd, add_zero]

theorem gp_neg (f : ℤ) : gp p (-f) = -gp p f := by
  unfold gp
  by_cases hd : (p : ℤ) ∣ f
  · rw [ite_eq_left ((dvd_neg).mpr hd), ite_eq_left hd, Int.neg_ediv_of_dvd hd]
    push_cast
    rw [inv_neg]
  · rw [ite_eq_right (by rwa [dvd_neg]), ite_eq_right hd, neg_zero]

end Harm

/-! ## 3. The three shifts -/

section Shifts
variable {p : ℕ} [hp : Fact p.Prime]

/-- **The `H` binomial to second order**: `C(p² − a, B)` against `(−1)^B C(a + B − 1, B)`, with
`ℓ = −Σ w⁻¹` over the multiples `p·w` of `[a, a + B − 1]`. -/
theorem sh2_choose_shift {a B : ℕ} (ha : 1 ≤ a) (haB : a + B ≤ p ^ 2) :
    Sh2 p ((-1 : ℤ) ^ B * ((a + B - 1).choose B : ℕ)) (((p ^ 2 - a).choose B : ℕ) : ℤ)
      (-hsum p ((a - 1) / p) ((a + B - 1) / p)) := by
  refine Sh2.cancel (Nat.factorial_ne_zero B) ?_
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
  have h : Sh2 p (∏ i ∈ range B, (-((a : ℤ) + i))) (∏ i ∈ range B, ((p : ℤ) ^ 2 + -((a : ℤ) + i)))
      (∑ i ∈ range B, gp p (-((a : ℤ) + i))) := by
    refine sh2_prod (fun i => -((a : ℤ) + i)) B fun i hi => ?_
    show ¬ (p : ℤ) ^ 2 ∣ -((a : ℤ) + i)
    rw [dvd_neg]
    intro hd
    have h0 : (0 : ℤ) < (a : ℤ) + i := by positivity
    have h1 := Int.le_of_dvd h0 hd
    have h2 : ((a : ℤ) + i) < (p : ℤ) ^ 2 := by exact_mod_cast (show a + i < p ^ 2 by omega)
    linarith
  have hl : ∑ i ∈ range B, gp p (-((a : ℤ) + i)) = -hsum p ((a - 1) / p) ((a + B - 1) / p) := by
    rw [← sum_gp_pos a ha B, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [gp_neg]
    push_cast
    rfl
  rwa [hl] at h

/-- **`C(p² + d, d) ≡ 1 + p·H_{⌊d/p⌋} (mod p²)`** for `d < p²`. -/
theorem choose_sq_add_hsum {d : ℕ} (hd : d < p ^ 2) :
    (p : ℤ) ^ 2 ∣ (((p ^ 2 + d).choose d : ℕ) : ℤ) - 1 - (p : ℤ) * ((hsum p 0 (d / p)).val : ℤ) := by
  have h : Sh2 p (∏ i ∈ range d, ((1 + i : ℕ) : ℤ)) (∏ i ∈ range d, ((p : ℤ) ^ 2 + ((1 + i : ℕ) : ℤ)))
      (∑ i ∈ range d, gp p ((1 + i : ℕ) : ℤ)) := by
    refine sh2_prod (fun i => ((1 + i : ℕ) : ℤ)) d fun i hi => ?_
    show ¬ (p : ℤ) ^ 2 ∣ ((1 + i : ℕ) : ℤ)
    intro hdv
    have h0 : (0 : ℤ) < ((1 + i : ℕ) : ℤ) := by positivity
    have h1 := Int.le_of_dvd h0 hdv
    have h2 : ((1 + i : ℕ) : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast (show 1 + i < p ^ 2 by omega)
    linarith
  have e1 : ∏ i ∈ range d, ((1 + i : ℕ) : ℤ) = ((d.factorial : ℕ) : ℤ) * 1 := by
    rw [mul_one, ← Nat.cast_prod, ← prod_range_add_one_eq_factorial]
    congr 1
    exact prod_congr rfl fun i _ => by ring
  have e2 : ∏ i ∈ range d, ((p : ℤ) ^ 2 + ((1 + i : ℕ) : ℤ))
      = ((d.factorial : ℕ) : ℤ) * (((p ^ 2 + d).choose d : ℕ) : ℤ) := by
    have ha := Nat.ascFactorial_eq_factorial_mul_choose' (p ^ 2 + 1) d
    rw [Nat.ascFactorial_eq_prod_range, show p ^ 2 + 1 + d - 1 = p ^ 2 + d by omega] at ha
    rw [← Nat.cast_mul, ← ha]
    push_cast
    exact prod_congr rfl fun i _ => by ring
  have e3 : ∑ i ∈ range d, gp p ((1 + i : ℕ) : ℤ) = hsum p 0 (d / p) := by
    rw [sum_gp_pos 1 le_rfl d]
    simp
  rw [e1, e2, e3] at h
  have h' := (Sh2.cancel (Nat.factorial_ne_zero d) h) 0 (by simp)
  rwa [zero_add, mul_one] at h'

/-- **The pair's binomial to second order**: `C(m, p² + j)` against `C(m, j)`, with
`ℓ = H_{⌊(m − j − p²)/p⌋} − H_{⌊j/p⌋}`, for `p² + j ≤ m < 2p²`. -/
theorem sh2_choose_pair {m j : ℕ} (hm : p ^ 2 + j ≤ m) (hm2 : m < p ^ 2 + p ^ 2) :
    Sh2 p ((m.choose j : ℕ) : ℤ) ((m.choose (p ^ 2 + j) : ℕ) : ℤ)
      (hsum p 0 ((m - j - p ^ 2) / p) - hsum p 0 (j / p)) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hid := Nat.choose_mul (n := m) (k := p ^ 2 + j) (s := j) (by omega)
  rw [show p ^ 2 + j - j = p ^ 2 by omega] at hid
  have hU := choose_sq_add_hsum (p := p) (d := j) (by omega)
  have hU' := choose_sq_add_hsum (p := p) (d := m - j - p ^ 2) (by omega)
  rw [show p ^ 2 + (m - j - p ^ 2) = m - j by omega,
    Nat.choose_symm_of_eq_add (show m - j = (m - j - p ^ 2) + p ^ 2 by omega)] at hU'
  have h3 : (p : ℤ) ∣ ((hsum p 0 ((m - j - p ^ 2) / p)).val : ℤ) - ((hsum p 0 (j / p)).val : ℤ)
      - (((hsum p 0 ((m - j - p ^ 2) / p) - hsum p 0 (j / p)).val : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
  refine Sh2.of_mul_eq (U := (p ^ 2 + j).choose j) (U' := (m - j).choose (p ^ 2))
    (by exact_mod_cast hid) ?_ ?_
  · intro hd
    have h1 : (p : ℤ) ∣ (((p ^ 2 + j).choose j : ℕ) : ℤ) - 1
        - (p : ℤ) * ((hsum p 0 (j / p)).val : ℤ) := (dvd_pow_self _ two_ne_zero).trans hU
    have h2 : (p : ℤ) ∣ (((p ^ 2 + j).choose j : ℕ) : ℤ) := by exact_mod_cast hd
    have h4 : (p : ℤ) ∣ 1 := by
      have := dvd_sub (dvd_sub h2 h1) (dvd_mul_right (p : ℤ) ((hsum p 0 (j / p)).val : ℤ))
      rwa [show (((p ^ 2 + j).choose j : ℕ) : ℤ) - ((((p ^ 2 + j).choose j : ℕ) : ℤ) - 1
          - (p : ℤ) * ((hsum p 0 (j / p)).val : ℤ)) - (p : ℤ) * ((hsum p 0 (j / p)).val : ℤ)
          = 1 by ring] at this
    exact hp.out.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h4)
  · set A := ((hsum p 0 (j / p)).val : ℤ)
    set A' := ((hsum p 0 ((m - j - p ^ 2) / p)).val : ℤ)
    set V := (((hsum p 0 ((m - j - p ^ 2) / p) - hsum p 0 (j / p)).val : ℕ) : ℤ)
    set U := (((p ^ 2 + j).choose j : ℕ) : ℤ)
    set U' := (((m - j).choose (p ^ 2) : ℕ) : ℤ)
    have e : U' - U - (p : ℤ) * V * U
        = (U' - 1 - (p : ℤ) * A') - (U - 1 - (p : ℤ) * A) + (p : ℤ) * (A' - A - V)
          - (p : ℤ) * V * (U - 1 - (p : ℤ) * A) - (p : ℤ) ^ 2 * (V * A) := by ring
    rw [e]
    refine dvd_sub (dvd_sub (dvd_add (dvd_sub hU' hU) ?_) ?_) (dvd_mul_right _ _)
    · rw [sq]
      exact mul_dvd_mul_left _ h3
    · exact Dvd.dvd.mul_left hU _

/-- The `H` part of `λ`: the three blocks' windows. -/
def lamH (p n j : ℕ) : ZMod p :=
  -hsum p ((13 * n - j) / p) ((26 * n - j) / p) - hsum p ((15 * n - j) / p) ((24 * n - j) / p)
    - hsum p ((17 * n - j) / p) ((22 * n - j) / p)

/-- **`H(p² + j)` against `H(j)` to second order**, for `j < n` at a window prime. -/
theorem sh2_Hfun {n j : ℕ} (hsq : 26 * n + 1 < p ^ 2) (hj : j < n) :
    Sh2 p (Hfun n j) (Hfun n ((p ^ 2 + j : ℕ) : ℤ)) (lamH p n j) := by
  rw [Hfun_of_le n j (by omega), Hfun_of_gt n (p ^ 2 + j) (by omega)]
  have s1 := sh2_choose_shift (p := p) (a := 13 * n + 1 - j) (B := 13 * n) (by omega) (by omega)
  have s2 := sh2_choose_shift (p := p) (a := 15 * n + 1 - j) (B := 9 * n) (by omega) (by omega)
  have s3 := sh2_choose_shift (p := p) (a := 17 * n + 1 - j) (B := 5 * n) (by omega) (by omega)
  rw [show 13 * n + 1 - j + 13 * n - 1 = 26 * n - j by omega,
    show 13 * n + 1 - j - 1 = 13 * n - j by omega,
    show p ^ 2 - (13 * n + 1 - j) = p ^ 2 + j - 13 * n - 1 by omega] at s1
  rw [show 15 * n + 1 - j + 9 * n - 1 = 24 * n - j by omega,
    show 15 * n + 1 - j - 1 = 15 * n - j by omega,
    show p ^ 2 - (15 * n + 1 - j) = p ^ 2 + j - 15 * n - 1 by omega] at s2
  rw [show 17 * n + 1 - j + 5 * n - 1 = 22 * n - j by omega,
    show 17 * n + 1 - j - 1 = 17 * n - j by omega,
    show p ^ 2 - (17 * n + 1 - j) = p ^ 2 + j - 17 * n - 1 by omega] at s3
  have h := (s1.mul s2).mul s3
  have el : lamH p n j = -hsum p ((13 * n - j) / p) ((26 * n - j) / p)
      + -hsum p ((15 * n - j) / p) ((24 * n - j) / p) + -hsum p ((17 * n - j) / p) ((22 * n - j) / p) := by
    unfold lamH; ring
  have e : (-1 : ℤ) ^ (27 * n) * (((26 * n - j).choose (13 * n) * (24 * n - j).choose (9 * n)
        * (22 * n - j).choose (5 * n) : ℕ) : ℤ)
      = (-1 : ℤ) ^ (13 * n) * (((26 * n - j).choose (13 * n) : ℕ) : ℤ)
        * ((-1 : ℤ) ^ (9 * n) * (((24 * n - j).choose (9 * n) : ℕ) : ℤ))
        * ((-1 : ℤ) ^ (5 * n) * (((22 * n - j).choose (5 * n) : ℕ) : ℤ)) := by
    rw [show 27 * n = 13 * n + 9 * n + 5 * n by ring, pow_add, pow_add]
    push_cast
    ring
  rw [e, el]
  push_cast at h ⊢
  exact h

end Shifts

/-! ## 4. The fold law -/

section Fold
variable {p : ℕ} [hp : Fact p.Prime]

/-- The `i`-th term of `h_m`, zero past `m`. -/
noncomputable def Tm (n m i : ℕ) : ℤ := (-1 : ℤ) ^ (m - i) * ((m.choose i : ℕ) : ℤ) * Hfun n i

/-- The `C(m, ·)` part of `λ`. -/
def lamC (p m j : ℕ) : ZMod p := hsum p 0 ((m - j - p ^ 2) / p) - hsum p 0 (j / p)

/-- `λ(j)`, the fold's second-order constant. -/
def lam (p n m j : ℕ) : ZMod p := lamC p m j + lamH p n j

/-- **THE FOLD LAW.**  `T(j) + T(p² + j) ≡ −p·λ(j)·T(j) (mod p^{K+2})` whenever `p^K ∣ T(j)`, at
`j < n`, `p² + j ≤ m < 2p²`, `26n + 1 < p²`. -/
theorem fold_law {n m j K : ℕ} (hsq : 26 * n + 1 < p ^ 2) (hj : j < n) (hm : p ^ 2 + j ≤ m)
    (hm2 : m < p ^ 2 + p ^ 2) (hK : (p : ℤ) ^ K ∣ Tm n m j) :
    (p : ℤ) ^ (K + 2) ∣ Tm n m j + Tm n m (p ^ 2 + j)
      + (p : ℤ) * ((lam p n m j).val : ℤ) * Tm n m j := by
  have hodd : Odd p := hp.out.odd_of_ne_two (by rintro rfl; omega)
  have hsign : (-1 : ℤ) ^ (m - j) = -(-1 : ℤ) ^ (m - (p ^ 2 + j)) := by
    rw [show m - j = (m - (p ^ 2 + j)) + p ^ 2 by omega, pow_add, (hodd.pow).neg_one_pow]
    ring
  have hs := (sh2_choose_pair (p := p) hm hm2).mul (sh2_Hfun (p := p) hsq hj)
  have hK' : (p : ℤ) ^ K ∣ ((m.choose j : ℕ) : ℤ) * Hfun n j := by
    unfold Tm at hK
    have h := Dvd.dvd.mul_left hK ((-1 : ℤ) ^ (m - j))
    have e : (-1 : ℤ) ^ (m - j) * ((-1 : ℤ) ^ (m - j) * ((m.choose j : ℕ) : ℤ) * Hfun n j)
        = ((m.choose j : ℕ) : ℤ) * Hfun n j := by
      rw [← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rwa [e] at h
  have h := hs K hK'
  have e : Tm n m j + Tm n m (p ^ 2 + j) + (p : ℤ) * ((lam p n m j).val : ℤ) * Tm n m j
      = (-1 : ℤ) ^ (m - (p ^ 2 + j))
        * (((m.choose (p ^ 2 + j) : ℕ) : ℤ) * Hfun n ((p ^ 2 + j : ℕ) : ℤ)
          - ((m.choose j : ℕ) : ℤ) * Hfun n j
          - (p : ℤ) * ((lamC p m j + lamH p n j).val : ℤ) * (((m.choose j : ℕ) : ℤ) * Hfun n j)) := by
    unfold Tm lam lamC
    rw [hsign]
    push_cast
    ring
  rw [e]
  exact Dvd.dvd.mul_left h _

/-- **THE FOLDED PAIR BLOCK, mod `p²`.**  In a block `t` of the fold, with `λ` constant (`ℓ₀`) at
every pair index whose term is a unit, every unpaired term `0 mod p²`, and the raw block `0 mod
p`: the folded block is `0 mod p²`. -/
theorem pair_block_sq {n m t : ℕ} {ℓ₀ : ZMod p} (hsq : 26 * n + 1 < p ^ 2) (hm : p ^ 2 ≤ m)
    (hm2 : m < p ^ 2 + p ^ 2) (hμ : m - p ^ 2 < n)
    (hconst : ∀ u < p, t * p + u ≤ m - p ^ 2 → ¬ (p : ℤ) ∣ Tm n m (t * p + u)
      → lam p n m (t * p + u) = ℓ₀)
    (hrest : ∀ u < p, m - p ^ 2 < t * p + u → (p : ℤ) ^ 2 ∣ Tm n m (t * p + u))
    (hblk : (p : ℤ) ∣ ∑ u ∈ range p, Tm n m (t * p + u)) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, (Tm n m (t * p + u) + Tm n m (p ^ 2 + (t * p + u))) := by
  have hterm : ∀ u < p, (p : ℤ) ^ 2 ∣ Tm n m (t * p + u) + Tm n m (p ^ 2 + (t * p + u))
      + (p : ℤ) * ((ℓ₀.val : ℕ) : ℤ) * Tm n m (t * p + u) := by
    intro u hu
    by_cases hpair : t * p + u ≤ m - p ^ 2
    · have hf := fold_law (p := p) (n := n) (m := m) (j := t * p + u) (K := 0) hsq (by omega)
        (by omega) hm2 (by simp)
      rw [zero_add] at hf
      have e : Tm n m (t * p + u) + Tm n m (p ^ 2 + (t * p + u))
          + (p : ℤ) * ((ℓ₀.val : ℕ) : ℤ) * Tm n m (t * p + u)
          = (Tm n m (t * p + u) + Tm n m (p ^ 2 + (t * p + u))
            + (p : ℤ) * (((lam p n m (t * p + u)).val : ℕ) : ℤ) * Tm n m (t * p + u))
          + (p : ℤ) * (((ℓ₀.val : ℕ) : ℤ) - ((lam p n m (t * p + u)).val : ℤ))
            * Tm n m (t * p + u) := by ring
      rw [e]
      refine dvd_add hf ?_
      by_cases hT : (p : ℤ) ∣ Tm n m (t * p + u)
      · obtain ⟨c, hc⟩ := hT
        rw [hc]
        exact ⟨(((ℓ₀.val : ℕ) : ℤ) - ((lam p n m (t * p + u)).val : ℤ)) * c, by ring⟩
      · rw [hconst u hu hpair hT, sub_self, mul_zero, zero_mul]
        exact dvd_zero _
    · have h0 : Tm n m (p ^ 2 + (t * p + u)) = 0 := by
        unfold Tm
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      have hr := hrest u hu (by omega)
      rw [h0, add_zero]
      refine dvd_add hr ?_
      obtain ⟨c, hc⟩ := hr
      rw [hc]
      exact ⟨(p : ℤ) * ((ℓ₀.val : ℕ) : ℤ) * c, by ring⟩
  have hsum_t : (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, (Tm n m (t * p + u) + Tm n m (p ^ 2 + (t * p + u))
      + (p : ℤ) * ((ℓ₀.val : ℕ) : ℤ) * Tm n m (t * p + u)) :=
    dvd_sum fun u hu => hterm u (mem_range.mp hu)
  rw [sum_add_distrib, ← mul_sum] at hsum_t
  have h2 : (p : ℤ) ^ 2 ∣ (p : ℤ) * ((ℓ₀.val : ℕ) : ℤ) * ∑ u ∈ range p, Tm n m (t * p + u) := by
    obtain ⟨c, hc⟩ := hblk
    rw [hc]
    exact ⟨((ℓ₀.val : ℕ) : ℤ) * c, by ring⟩
  have := dvd_sub hsum_t h2
  rwa [add_sub_cancel_right] at this

end Fold

/-! ## 5. The middle terms: Lucas mod `p²` across a carried tens digit -/

section Middle
variable {p : ℕ} [hp : Fact p.Prime]

/-- `p² ∣ C(pM, i)` for `p ∤ i` whenever `p ∣ M·C(M − 1, ⌊i/p⌋)`. -/
theorem sq_dvd_choose_pM {M i : ℕ} (hM : 1 ≤ M) (hi : ¬ p ∣ i)
    (hdiv : p ∣ M * (M - 1).choose (i / p)) : p ^ 2 ∣ (p * M).choose i := by
  have hp0 := hp.out.pos
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact absurd (h ▸ dvd_zero p) hi
    · omega⟩
  have hdiv' : i' / p = (i' + 1) / p := by
    rw [Nat.succ_div, ite_eq_right hi, add_zero]
  have hsucc := Nat.add_one_mul_choose_eq (p * M - 1) i'
  rw [show p * M - 1 + 1 = p * M by
    have : 1 ≤ p * M := Nat.mul_pos hp0 hM; omega] at hsucc
  -- `p ∣ M·C(pM − 1, i')` by Lucas
  have hluc : p ∣ M * (p * M - 1).choose i' := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    have hq : (p * M - 1) / p = M - 1 := Zeta2PtpRunBlock.div_of_lin hp0 (r := p - 1)
      (by have : p ≤ p * M := Nat.le_mul_of_pos_right p hM
          have e : (M - 1) * p = p * M - p := by rw [Nat.sub_mul, one_mul, Nat.mul_comm M p]
          omega) (by omega)
    rw [Zeta2PtpS7.lucas_raw (p * M - 1) i', hq, hdiv']
    have h0 : ((M * (M - 1).choose ((i' + 1) / p) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
    push_cast at h0
    rw [show (M : ZMod p) * (((((p * M - 1) % p).choose (i' % p) : ℕ) : ZMod p)
        * (((M - 1).choose ((i' + 1) / p) : ℕ) : ZMod p))
        = ((M : ZMod p) * (((M - 1).choose ((i' + 1) / p) : ℕ) : ZMod p))
          * ((((p * M - 1) % p).choose (i' % p) : ℕ) : ZMod p) by ring, h0, zero_mul]
  have h2 : p ^ 2 ∣ (p * M).choose (i' + 1) * (i' + 1) := by
    rw [← hsucc]
    obtain ⟨c, hc⟩ := hluc
    exact ⟨c, by rw [mul_assoc, hc]; ring⟩
  exact (Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hi)) h2)

/-- **LUCAS MOD `p²` ACROSS A CARRIED TENS DIGIT.**  If `p ∣ C(M, t)`, then for `a, b < p`,
`C(pM + a, pt + b) ≡ C(pM, pt)·C(a, b) (mod p²)`: in Vandermonde's sum every other term has
`p ∤ i`, and `i·C(pM, i) = pM·C(pM − 1, i − 1)` carries a second `p` from `M·C(M − 1, ⌊i/p⌋)`,
which is `(M − t)·C(M, t)` or `t·C(M, t)`. -/
theorem choose_mul_add_sq {M a t b : ℕ} (ha : a < p) (hb : b < p) (hM : 1 ≤ M)
    (hMt : p ∣ M.choose t) :
    (p : ℤ) ^ 2 ∣ (((p * M + a).choose (p * t + b) : ℕ) : ℤ)
      - (((p * M).choose (p * t) : ℕ) : ℤ) * ((a.choose b : ℕ) : ℤ) := by
  have hp0 := hp.out.pos
  have hmem : (p * t, b) ∈ antidiagonal (p * t + b) := mem_antidiagonal.mpr rfl
  rw [Nat.add_choose_eq, ← add_sum_erase _ _ hmem]
  dsimp only
  push_cast
  rw [add_sub_cancel_left]
  refine dvd_sum fun ij hij => ?_
  obtain ⟨hne, hij⟩ := mem_erase.mp hij
  rw [mem_antidiagonal] at hij
  obtain ⟨i, j⟩ := ij
  dsimp only at hij hne ⊢
  by_cases hja : a < j
  · rw [Nat.choose_eq_zero_of_lt hja]
    simp
  have hjp : j < p := by omega
  have htp : t * p = p * t := Nat.mul_comm t p
  have hi : ¬ p ∣ i := by
    rintro ⟨q, rfl⟩
    have h1 : (p * q + j) / p = q := Zeta2PtpRunBlock.div_of_lin hp0 (r := j) (by ring) hjp
    have h2 : (p * t + b) / p = t := Zeta2PtpRunBlock.div_of_lin hp0 (r := b) (by ring) hb
    rw [hij] at h1
    have hqt : q = t := h1.symm.trans h2
    subst hqt
    have hjb : j = b := by omega
    exact hne (by rw [hjb])
  have hdiv : p ∣ M * (M - 1).choose (i / p) := by
    by_cases hjb : j < b
    · have hq : i / p = t := Zeta2PtpRunBlock.div_of_lin hp0 (r := b - j) (by omega) (by omega)
      rw [hq]
      have e1 := Nat.add_one_mul_choose_eq (M - 1) t
      have e2 := Nat.choose_succ_right_eq M t
      rw [show M - 1 + 1 = M by omega] at e1
      rw [e1, e2]
      exact Dvd.dvd.mul_right hMt _
    · have hjb' : b < j := by
        rcases Nat.lt_or_ge b j with h | h
        · exact h
        · exfalso
          have hjb2 : j = b := by omega
          subst hjb2
          exact hne (by rw [show i = p * t by omega])
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · subst h
          simp at hij
          omega
        · exact h
      have e0 : (t - 1) * p = t * p - p := by rw [Nat.sub_mul, one_mul]
      have hpt : p ≤ t * p := Nat.le_mul_of_pos_left p ht1
      have hq : i / p = t - 1 :=
        Zeta2PtpRunBlock.div_of_lin hp0 (r := p + b - j) (by omega) (by omega)
      rw [hq]
      have e1 := Nat.add_one_mul_choose_eq (M - 1) (t - 1)
      rw [show M - 1 + 1 = M by omega, show t - 1 + 1 = t by omega] at e1
      rw [e1]
      exact Dvd.dvd.mul_right hMt _
  have h := sq_dvd_choose_pM hM hi hdiv
  exact Dvd.dvd.mul_right (by exact_mod_cast h) _

/-- `p ∣ C(pM, pt)` when `p ∣ C(M, t)` (Lucas). -/
theorem dvd_choose_mul {M t : ℕ} (hMt : p ∣ M.choose t) : p ∣ (p * M).choose (p * t) := by
  have hp0 := hp.out.pos
  rw [← ZMod.natCast_eq_zero_iff, Zeta2PtpS7.lucas_raw, Nat.mul_mod_right, Nat.mul_mod_right,
    Nat.mul_div_cancel_left _ hp0, Nat.mul_div_cancel_left _ hp0,
    (ZMod.natCast_eq_zero_iff _ _).mpr hMt, mul_zero]

end Middle

/-! ## 6. `h_m` folded, and the middle block -/

section Assembly
variable {p : ℕ} [hp : Fact p.Prime]

open Zeta2PtpRunBlock in
/-- **`h_m` FOLDED**: for `m < 2p²`, `h_m = Σ_{t<p} Σ_{u<p} (T(tp + u) + T(p² + tp + u))`. -/
theorem hc_eq_fold {n m : ℕ} (hm2 : m < p ^ 2 + p ^ 2) :
    hc n m = ∑ t ∈ range p, ∑ u ∈ range p, (Tm n m (t * p + u) + Tm n m (p ^ 2 + (t * p + u))) := by
  have hT : ∀ i, m < i → Tm n m i = 0 := fun i hi => by
    unfold Tm
    rw [Nat.choose_eq_zero_of_lt hi]
    simp
  rw [hc_eq_signed_sum]
  show ∑ i ∈ range (m + 1), Tm n m i = _
  rw [sum_subset (range_mono (show m + 1 ≤ p ^ 2 + p ^ 2 by omega))
    (fun i _ hi => hT i (by simp at hi; omega)), sum_range_add]
  have hb := sum_range_blocks (Tm n m) p p
  have hb2 := sum_range_blocks (fun i => Tm n m (p ^ 2 + i)) p p
  rw [← pow_two] at hb hb2
  rw [hb, hb2, ← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  rw [← sum_add_distrib]

open Zeta2PtpRunBlock in
/-- **THE MIDDLE BLOCK, mod `p²`.**  If `p ∣ C(⌊m/p⌋, t)`, the raw block `t` of `h_m` is `c·(±1)`
times the block of the REDUCED row `m'' = tp + (m mod p)` modulo `p²`, with `p ∣ c`
(`choose_mul_add_sq`); so a block lemma for `m''` (LO and TAIL, `0 mod p`) gives `0 mod p²`. -/
theorem mid_block_sq {n m t : ℕ} (hn : 1 ≤ n) (hM : 1 ≤ m / p) (hMt : p ∣ (m / p).choose t)
    (htm : t * p + p ≤ m + 1)
    (hlo : (p : ℤ) ∣ ∑ u ∈ range p, Tlo n (t * p + m % p) (t * p + u))
    (hhi : (p : ℤ) ∣ ∑ u ∈ range p, Thi n (t * p + m % p) (t * p + u)) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ range p, Tm n m (t * p + u) := by
  have hp0 := hp.out.pos
  have hmlt := Nat.mod_lt m hp0
  have hdm := Nat.div_add_mod m p
  have hc : (p : ℤ) ∣ (((p * (m / p)).choose (p * t) : ℕ) : ℤ) := by
    exact_mod_cast dvd_choose_mul hMt
  obtain ⟨e, he⟩ := hc
  have h''mod : (t * p + m % p) % p = m % p := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmlt]
  have h''div : (t * p + m % p) / p = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hmlt, zero_add]
  have hT'' : ∀ i, Tm n (t * p + m % p) i
      = (-1 : ℤ) ^ (27 * n) * Tlo n (t * p + m % p) i + Thi n (t * p + m % p) i := by
    intro i
    by_cases hi : i ≤ t * p + m % p
    · exact term_eq_lo_add_hi n _ i hn hi
    · unfold Tm
      rw [Tlo_eq_zero_of_gt (by omega), Thi_eq_zero_of_gt (by omega),
        Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have hsum'' : (p : ℤ) ∣ ∑ u ∈ range p, Tm n (t * p + m % p) (t * p + u) := by
    rw [sum_congr rfl fun u _ => hT'' (t * p + u), sum_add_distrib, ← mul_sum]
    exact dvd_add (Dvd.dvd.mul_left hlo _) hhi
  have hterm : ∀ u < p, (p : ℤ) ^ 2 ∣ Tm n m (t * p + u)
      - (p : ℤ) * e * (-1 : ℤ) ^ (m + (t * p + m % p)) * Tm n (t * p + m % p) (t * p + u) := by
    intro u hu
    have himod : (t * p + u) % p = u := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
    have hidiv : (t * p + u) / p = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hu, zero_add]
    have h1 := choose_mul_add_sq (p := p) (M := m / p) (a := m % p) (t := t) (b := u) hmlt hu hM hMt
    rw [hdm, show p * t + u = t * p + u by ring, he] at h1
    unfold Tm
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
      have key : (p : ℤ) ^ 2 ∣ (-1 : ℤ) ^ (m - (t * p + u)) * Hfun n ↑(t * p + u)
          * (((((m.choose (t * p + u) : ℕ) : ℤ) - (p : ℤ) * e * (((m % p).choose u : ℕ) : ℤ)))
            - (p : ℤ) * e * ((((t * p + m % p).choose (t * p + u) : ℕ) : ℤ)
              - (((m % p).choose u : ℕ) : ℤ))) := by
        refine Dvd.dvd.mul_left (dvd_sub h1 ?_) _
        rw [hd]
        exact ⟨e * d, by ring⟩
      convert key using 1
      rw [← hs]
      ring
    · rw [Nat.choose_eq_zero_of_lt (show m % p < u by omega), Nat.cast_zero, mul_zero,
        sub_zero] at h1
      rw [Nat.choose_eq_zero_of_lt (show t * p + m % p < t * p + u by omega)]
      simp only [Nat.cast_zero, mul_zero, zero_mul, sub_zero]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 _) _
  have hsplit : ∑ u ∈ range p, Tm n m (t * p + u)
      = ∑ u ∈ range p, (Tm n m (t * p + u)
          - (p : ℤ) * e * (-1 : ℤ) ^ (m + (t * p + m % p)) * Tm n (t * p + m % p) (t * p + u))
        + (p : ℤ) * e * (-1 : ℤ) ^ (m + (t * p + m % p))
          * ∑ u ∈ range p, Tm n (t * p + m % p) (t * p + u) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun u _ => by ring
  rw [hsplit]
  refine dvd_add (dvd_sum fun u hu => hterm u (mem_range.mp hu)) ?_
  obtain ⟨f, hf⟩ := hsum''
  rw [hf]
  exact ⟨e * (-1 : ℤ) ^ (m + (t * p + m % p)) * f, by ring⟩

end Assembly

end Zeta2PtpFold

#print axioms Zeta2PtpFold.Sh2.mul
#check @Zeta2PtpFold.Sh2.mul
#print axioms Zeta2PtpFold.sh2_prod
#check @Zeta2PtpFold.sh2_prod
#print axioms Zeta2PtpFold.sum_gp_pos
#check @Zeta2PtpFold.sum_gp_pos
#print axioms Zeta2PtpFold.sh2_choose_shift
#check @Zeta2PtpFold.sh2_choose_shift
#print axioms Zeta2PtpFold.choose_sq_add_hsum
#check @Zeta2PtpFold.choose_sq_add_hsum
#print axioms Zeta2PtpFold.sh2_choose_pair
#check @Zeta2PtpFold.sh2_choose_pair
#print axioms Zeta2PtpFold.sh2_Hfun
#check @Zeta2PtpFold.sh2_Hfun
#print axioms Zeta2PtpFold.fold_law
#check @Zeta2PtpFold.fold_law
#print axioms Zeta2PtpFold.pair_block_sq
#check @Zeta2PtpFold.pair_block_sq
#print axioms Zeta2PtpFold.sq_dvd_choose_pM
#check @Zeta2PtpFold.sq_dvd_choose_pM
#print axioms Zeta2PtpFold.choose_mul_add_sq
#check @Zeta2PtpFold.choose_mul_add_sq
#print axioms Zeta2PtpFold.dvd_choose_mul
#check @Zeta2PtpFold.dvd_choose_mul
#print axioms Zeta2PtpFold.hc_eq_fold
#check @Zeta2PtpFold.hc_eq_fold
#print axioms Zeta2PtpFold.mid_block_sq
#check @Zeta2PtpFold.mid_block_sq
