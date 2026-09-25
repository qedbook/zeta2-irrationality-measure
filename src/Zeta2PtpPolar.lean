/-
Zeta2PtpPolar.lean — row PT-P, layer 3: THE POLAR SPLIT, and the `B` half discharged.

WHAT THIS FILE IS FOR.  `Zeta2PhiTDvd` reduced row PT-P to one inequality per window prime,
`φ̃({n/p}) ≤ v_p(P n)` with `(P n : ℚ) = Δ(16n)·D(15n) · pₙ`.  `ptp_cancel_probe.py` then priced
that inequality and found most of it free:

* `pₙ = −sgn·Π·(pnPoly − pnHarm)` and `Π·pnHarm = Σ_k ε_k·cTerm(n,k)·H⁽²⁾_{m_k}` with
  `m_k = k − 4n − 1 ≤ 22n < 26n + 1 < p²` at a window prime (the Legendre line);
* so `⌊log_p m⌋ ≤ 1` and `H⁽²⁾_m` has exactly ONE polar block:
  `H⁽²⁾_m = B_m + p⁻²·A_{⌊m/p⌋}`, `A_t = Σ_{j ≤ t} 1/j²`, `B_m = Σ_{i ≤ m, p ∤ i} 1/i²`,
  with BOTH pieces `p`-integral because `⌊m/p⌋ ≤ p − 1`;
* `Zeta2PhiTDvd.factorization_Delta_eq_two` says the clearing supplies EXACTLY 2 at a window
  prime and `φ̃ ≤ 2`, so the `B` half clears with nothing left to prove.

THIS FILE PROVES THAT, and states what remains as two named `Prop`s so a successor can discharge
them one at a time.  It also CORRECTS the row's framing: the previous cell said the open core was
`v_p(Σ_k ε_k cTerm_k A_{t_k}) ≥ φ̃` "and nothing else".  That is wrong by one obligation — the
probe's own arm A8, `v_p(Δ·Π·pnPoly) ≥ φ̃`, is scored SEPARATELY (366 of 366) and is needed
separately, because `P n` is the DIFFERENCE of the two halves and the ultrametric needs a bound on
each.  `PolyHalfOpen` below is that obligation, named for the first time.

THE `p`-INTEGRALITY VOCABULARY.  `PVal p v x` — `x = p^v·a/b` with `p ∤ b` — rather than
`padicValRat`, because every step here is a SUM of terms whose valuation is bounded below and
`padicValRat`'s fold carries a `≠ 0` side condition at every node.  `PVal` has no such condition:
it is closed under `+`, `*`, `-`, `Finset.sum` and monotone in `v`, and its EXIT
(`pow_dvd_of_pval`) turns it back into `(p:ℤ)^v ∣ z` on an integer with one coprimality step.

WHAT IS NOT CLAIMED.  `Zeta2Target.zeta2_not_liouvilleWith` is `sorry`.  PT-P does NOT close:
`AHalfOpen` is research (the per-cell run congruence) and `PolyHalfOpen` is measured and unpriced.
`hP_at_ΔT_of_two_halves` is a CONDITIONAL theorem and its type names both binders.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2PnHarm
import Zeta2Profile
import Zeta2PhiT
import Zeta2PnCleared
import Zeta2PnFunc
import Zeta2PnHarmDelta
import Zeta2PhiTDvd

namespace Zeta2PtpPolar

open Zeta2Defs Zeta2Arith Zeta2PhiT Nat Finset

/-! ## 1. `PVal` — "at least `v` powers of `p`", for rationals, with no nonvanishing side condition -/

/-- **`x : ℚ` carries at least `v` powers of `p`**: `b·x = p^v·a` for some integer `a` and some
`b` prime to `p`.  For `v = 0` this is exactly `p`-integrality. -/
def PVal (p v : ℕ) (x : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), 0 < b ∧ ¬ p ∣ b ∧ (b : ℚ) * x = (p : ℚ) ^ v * (a : ℚ)

theorem not_dvd_one {p : ℕ} (hp : p.Prime) : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)

theorem pval_zero {p : ℕ} (hp : p.Prime) (v : ℕ) : PVal p v 0 :=
  ⟨0, 1, one_pos, not_dvd_one hp, by push_cast; ring⟩

theorem pval_intCast {p : ℕ} (hp : p.Prime) (z : ℤ) : PVal p 0 ((z : ℚ)) :=
  ⟨z, 1, one_pos, not_dvd_one hp, by push_cast; ring⟩

theorem pval_of_pow_dvd {p v : ℕ} (hp : p.Prime) {z : ℤ} (h : (p : ℤ) ^ v ∣ z) :
    PVal p v ((z : ℚ)) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, 1, one_pos, not_dvd_one hp, by rw [hc]; push_cast; ring⟩

theorem pval_add {p v : ℕ} (hp : p.Prime) {x y : ℚ} (hx : PVal p v x) (hy : PVal p v y) :
    PVal p v (x + y) := by
  obtain ⟨a₁, b₁, hb₁, hd₁, h₁⟩ := hx
  obtain ⟨a₂, b₂, hb₂, hd₂, h₂⟩ := hy
  refine ⟨(b₂ : ℤ) * a₁ + (b₁ : ℤ) * a₂, b₁ * b₂, Nat.mul_pos hb₁ hb₂, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    exacts [hd₁ h, hd₂ h]
  · push_cast
    linear_combination (b₂ : ℚ) * h₁ + (b₁ : ℚ) * h₂

theorem pval_neg {p v : ℕ} {x : ℚ} (hx : PVal p v x) : PVal p v (-x) := by
  obtain ⟨a, b, hb, hd, h⟩ := hx
  exact ⟨-a, b, hb, hd, by push_cast; linear_combination -h⟩

theorem pval_sub {p v : ℕ} (hp : p.Prime) {x y : ℚ} (hx : PVal p v x) (hy : PVal p v y) :
    PVal p v (x - y) := by
  have := pval_add hp hx (pval_neg hy)
  simpa [sub_eq_add_neg] using this

theorem pval_mul {p v w : ℕ} (hp : p.Prime) {x y : ℚ} (hx : PVal p v x) (hy : PVal p w y) :
    PVal p (v + w) (x * y) := by
  obtain ⟨a₁, b₁, hb₁, hd₁, h₁⟩ := hx
  obtain ⟨a₂, b₂, hb₂, hd₂, h₂⟩ := hy
  refine ⟨a₁ * a₂, b₁ * b₂, Nat.mul_pos hb₁ hb₂, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    exacts [hd₁ h, hd₂ h]
  · push_cast
    rw [pow_add]
    linear_combination ((b₂ : ℚ) * y) * h₁ + ((p : ℚ) ^ v * (a₁ : ℚ)) * h₂

/-- The exponent is monotone DOWNWARD: more powers of `p` is a stronger statement. -/
theorem pval_mono {p v w : ℕ} {x : ℚ} (hw : w ≤ v) (hx : PVal p v x) : PVal p w x := by
  obtain ⟨a, b, hb, hd, h⟩ := hx
  refine ⟨(p : ℤ) ^ (v - w) * a, b, hb, hd, ?_⟩
  have hsp : (p : ℚ) ^ v = (p : ℚ) ^ w * (p : ℚ) ^ (v - w) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h, hsp]
  push_cast
  ring

theorem pval_sum {p v : ℕ} (hp : p.Prime) {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ) :
    (∀ i ∈ s, PVal p v (f i)) → PVal p v (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => intro _; simpa using pval_zero hp v
  | @insert i s hi ih =>
      intro h
      rw [Finset.sum_insert hi]
      exact pval_add hp (h i (Finset.mem_insert_self i s))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **The exit.**  On an INTEGER, `PVal` is ordinary `p`-power divisibility.  `p ∤ b` is what
makes this a one-line coprimality step rather than a valuation computation. -/
theorem pow_dvd_of_pval {p v : ℕ} (hp : p.Prime) {z : ℤ} (h : PVal p v ((z : ℚ))) :
    (p : ℤ) ^ v ∣ z := by
  obtain ⟨a, b, hb, hd, hh⟩ := h
  have hz : (b : ℤ) * z = (p : ℤ) ^ v * a := by exact_mod_cast hh
  have hcop : IsCoprime ((p : ℤ) ^ v) ((b : ℤ)) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd)).pow_left
  exact hcop.dvd_of_dvd_mul_left ⟨a, hz⟩

/-! ## 2. The polar split — `H⁽²⁾_m = B_m + p⁻²·A_{⌊m/p⌋}`, both pieces `p`-integral -/

/-- `harm` on `Icc 1 m`, which is the shape every reindex below wants. -/
theorem sum_Icc_eq_harm (s m : ℕ) : ∑ i ∈ Finset.Icc 1 m, 1 / ((i : ℚ)) ^ s = harm s m := by
  induction m with
  | zero => simp [harm]
  | succ k ih =>
      simp only [harm] at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ k + 1), ih, Finset.sum_range_succ]
      push_cast
      ring

/-- The multiples of `p` in `Icc 1 m` are exactly `p·j` for `j ∈ Icc 1 (m/p)`. -/
theorem filter_dvd_eq_image {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (Finset.Icc 1 m).filter (fun i => p ∣ i) = (Finset.Icc 1 (m / p)).image (fun j => p * j) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, c, rfl⟩
    refine ⟨c, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp at h1
      · exact hc
    · exact (Nat.le_div_iff_mul_le hp).mpr (by rw [Nat.mul_comm]; omega)
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ⟨j, rfl⟩⟩
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · have hjm := (Nat.le_div_iff_mul_le hp).mp hj2
      rw [Nat.mul_comm]
      exact hjm

/-- The polar block, summed: `Σ_{i ≤ m, p ∣ i} i^{-s} = p^{-s}·H^{(s)}_{⌊m/p⌋}`. -/
theorem sum_multiples {p : ℕ} (hp : 0 < p) (s m : ℕ) :
    ∑ i ∈ (Finset.Icc 1 m).filter (fun i => p ∣ i), 1 / ((i : ℚ)) ^ s
      = (1 / (p : ℚ) ^ s) * harm s (m / p) := by
  rw [filter_dvd_eq_image hp m,
    Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp h),
    ← sum_Icc_eq_harm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hjq : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.cast_mul, mul_pow]
  field_simp

/-- **`B_m` — the `p`-free part of `H^{(s)}_m`.** -/
def Bpart (p s m : ℕ) : ℚ := ∑ i ∈ (Finset.Icc 1 m).filter (fun i => ¬ p ∣ i), 1 / ((i : ℚ)) ^ s

/-- **THE POLAR SPLIT.**  An identity at every `m`; what the window buys is not the split but the
`p`-integrality of the two pieces (`pval_harm_of_lt` below needs `⌊m/p⌋ < p`). -/
theorem polar_split {p : ℕ} (hp : 0 < p) (s m : ℕ) :
    harm s m = Bpart p s m + (1 / (p : ℚ) ^ s) * harm s (m / p) := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 m) (fun i => p ∣ i)
    (fun i => 1 / ((i : ℚ)) ^ s)
  rw [sum_multiples hp s m] at h
  rw [← sum_Icc_eq_harm s m, ← h, Bpart]
  ring

/-- `B_m` is `p`-integral: every denominator in it is prime to `p` by construction. -/
theorem pval_Bpart {p : ℕ} (hp : p.Prime) (s m : ℕ) : PVal p 0 (Bpart p s m) := by
  refine pval_sum hp _ _ fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hi
  obtain ⟨⟨h1, _⟩, hnd⟩ := hi
  have hiq : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨1, i ^ s, pow_pos (by omega) s, fun h => hnd (hp.dvd_of_dvd_pow h), ?_⟩
  push_cast
  field_simp

/-- `A_t = H^{(s)}_t` is `p`-integral as soon as `t < p`, which at a window prime is exactly
`m < p²`.  This is the ONE place the Legendre line is spent in this file. -/
theorem pval_harm_of_lt {p : ℕ} (hp : p.Prime) (s t : ℕ) (ht : t < p) : PVal p 0 (harm s t) := by
  rw [← sum_Icc_eq_harm]
  refine pval_sum hp _ _ fun i hi => ?_
  simp only [Finset.mem_Icc] at hi
  have hiq : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨1, i ^ s, pow_pos (by omega) s, ?_, ?_⟩
  · intro h
    have hpi := hp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by omega) hpi
    omega
  · push_cast
    field_simp

/-! ## 3. The window's own facts -/

/-- A window prime forces `1 ≤ n`: it is a prime `≤ 15n`, and `2 ≤ 15·0` is false. -/
theorem pos_of_mem_phiWindow {n p : ℕ} (hp : p ∈ phiWindow n) : 1 ≤ n := by
  have h1 := Zeta2PhiTDvd.le_of_mem_phiWindow hp
  have h2 := (prime_of_mem_phiWindow hp).two_le
  omega

/-- **`φ̃ ≤ 2`** — read off the landed 26-row table, never retyped.  This and
`factorization_Delta_eq_two` are the two halves of "the clearing supplies exactly what the
profile asks and not a unit more". -/
theorem phiT_le_two (x : ℚ) : phiT x ≤ 2 := by
  unfold phiT
  split
  · rename_i t h
    have hm : t ∈ Zeta2Profile.candidateProfile := List.mem_of_find?_eq_some h
    have hall : ∀ u ∈ Zeta2Profile.candidateProfile, (u.2.2 : ℚ).num.toNat ≤ 2 := by
      decide +kernel
    exact hall t hm
  · omega

/-- `v_p(Δ 16 15 n) = 2` in `PVal` form. -/
theorem pval_Delta {n p : ℕ} (hp : p ∈ phiWindow n) :
    PVal p 2 (((Δ 16 15 n : ℕ) : ℚ)) := by
  have hpp := prime_of_mem_phiWindow hp
  have h2 := Zeta2PhiTDvd.factorization_Delta_eq_two (pos_of_mem_phiWindow hp) hp
  have hdvd : p ^ 2 ∣ Δ 16 15 n :=
    (Nat.Prime.pow_dvd_iff_le_factorization hpp (Δ_ne_zero 16 15 n)).mpr (by omega)
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨(c : ℤ), 1, one_pos, not_dvd_one hpp, by rw [hc]; push_cast; ring⟩

/-- `m_k = k − 4n − 1 < p²` at a window prime, which is what makes `⌊m/p⌋ < p`. -/
theorem harmIndex_lt_sq {n k p : ℕ} (hp : p ∈ phiWindow n) (hk : k ∈ candidateM.window n) :
    k - 4 * n - 1 < p ^ 2 := by
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  have := sq_gt_of_mem_phiWindow hp
  omega

/-! ## 4. The two halves of `Π·pnHarm`, and the `B` half discharged -/

/-- `Σ_k ε_k·cTerm(n,k)·A_{⌊m_k/p⌋}` — the `A` (polar) half.  Everything open about row PT-P's
harmonic side is a statement about THIS number. -/
def harmA (n p : ℕ) : ℚ :=
  ∑ k ∈ candidateM.window n,
    (-1 : ℚ) ^ (12 * n + k - 1) * (cTerm n k : ℚ) * harm 2 ((k - 4 * n - 1) / p)

/-- `Σ_k ε_k·cTerm(n,k)·B_{m_k}` — the `p`-free half. -/
def harmB (n p : ℕ) : ℚ :=
  ∑ k ∈ candidateM.window n,
    (-1 : ℚ) ^ (12 * n + k - 1) * (cTerm n k : ℚ) * Bpart p 2 (k - 4 * n - 1)

/-- **The split, transported to the chain's own object.**  `Π·pnHarm` is `harmB + p⁻²·harmA`;
`Pin_mul_ckAbs_eq_cTerm` is what makes each term's coefficient an INTEGER. -/
theorem Pin_pnHarm_split {n p : ℕ} (hp : p ∈ phiWindow n) :
    candidateM.Pin n * candidateM.pnHarm n = harmB n p + (1 / (p : ℚ) ^ 2) * harmA n p := by
  have hpp := prime_of_mem_phiWindow hp
  have key : ∀ k ∈ candidateM.window n,
      candidateM.Pin n * (candidateM.ck n k * harm 2 (candidateM.harmIndex n k))
        = ((-1 : ℚ) ^ (12 * n + k - 1) * (cTerm n k : ℚ) * Bpart p 2 (k - 4 * n - 1))
          + (1 / (p : ℚ) ^ 2)
              * ((-1 : ℚ) ^ (12 * n + k - 1) * (cTerm n k : ℚ)
                  * harm 2 ((k - 4 * n - 1) / p)) := by
    intro k hk
    have hct := Pin_mul_ckAbs_eq_cTerm n k hk
    rw [candidate_ck, candidate_harmIndex, polar_split hpp.pos 2 (k - 4 * n - 1)]
    linear_combination
      ((-1 : ℚ) ^ (12 * n + k - 1)
        * (Bpart p 2 (k - 4 * n - 1)
            + (1 / (p : ℚ) ^ 2) * harm 2 ((k - 4 * n - 1) / p))) * hct
  calc candidateM.Pin n * candidateM.pnHarm n
      = ∑ k ∈ candidateM.window n,
          candidateM.Pin n * (candidateM.ck n k * harm 2 (candidateM.harmIndex n k)) := by
        rw [Member.pnHarm, Finset.mul_sum]
    _ = ∑ k ∈ candidateM.window n,
          (((-1 : ℚ) ^ (12 * n + k - 1) * (cTerm n k : ℚ) * Bpart p 2 (k - 4 * n - 1))
            + (1 / (p : ℚ) ^ 2)
                * ((-1 : ℚ) ^ (12 * n + k - 1) * (cTerm n k : ℚ)
                    * harm 2 ((k - 4 * n - 1) / p))) := Finset.sum_congr rfl key
    _ = harmB n p + (1 / (p : ℚ) ^ 2) * harmA n p := by
        rw [harmB, harmA, Finset.mul_sum, Finset.sum_add_distrib]

/-- Every coefficient `ε_k·cTerm(n,k)` is an integer, hence `p`-integral. -/
theorem pval_coeff {p : ℕ} (hp : p.Prime) (n k : ℕ) :
    PVal p 0 ((-1 : ℚ) ^ (12 * n + k - 1) * (cTerm n k : ℚ)) := by
  have hrw : ((-1 : ℚ) ^ (12 * n + k - 1) * (cTerm n k : ℚ))
      = ((((-1 : ℤ) ^ (12 * n + k - 1) * (cTerm n k : ℤ)) : ℤ) : ℚ) := by
    push_cast
    ring
  rw [hrw]
  exact pval_intCast hp _

theorem pval_harmB {n p : ℕ} (hp : p ∈ phiWindow n) : PVal p 0 (harmB n p) := by
  have hpp := prime_of_mem_phiWindow hp
  refine pval_sum hpp _ _ fun k _ => ?_
  simpa using pval_mul hpp (pval_coeff hpp n k) (pval_Bpart hpp 2 (k - 4 * n - 1))

/-- **THE `B` HALF CLEARS, UNCONDITIONALLY.**  `v_p(Δ) = 2` exactly, `B` is `p`-integral, and
`φ̃ ≤ 2` — so this half of row PT-P's harmonic side needs nothing from the run congruence.
Arm A2 of `ptp_cancel_probe.py`, 366 of 366, as a theorem. -/
theorem B_half_clears {n p : ℕ} (hp : p ∈ phiWindow n) :
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ)))) (((Δ 16 15 n : ℕ) : ℚ) * harmB n p) := by
  have hpp := prime_of_mem_phiWindow hp
  refine pval_mono (phiT_le_two _) ?_
  simpa using pval_mul hpp (pval_Delta hp) (pval_harmB hp)

/-- The `A` half's individual terms ARE `p`-integral too — the whole difficulty is the FACTOR
`p⁻²` in front, which only a cancellation ACROSS `k` can pay for.  Stated so the open core reads
as what it is: not integrality, but two units of `p` out of an alternating sum. -/
theorem pval_harmA {n p : ℕ} (hp : p ∈ phiWindow n) : PVal p 0 (harmA n p) := by
  have hpp := prime_of_mem_phiWindow hp
  refine pval_sum hpp _ _ fun k hk => ?_
  have hlt : (k - 4 * n - 1) / p < p := by
    have h := harmIndex_lt_sq hp hk
    rw [pow_two] at h
    exact (Nat.div_lt_iff_lt_mul hpp.pos).mpr h
  simpa using pval_mul hpp (pval_coeff hpp n k) (pval_harm_of_lt hpp 2 _ hlt)

/-! ## 5. What is LEFT — two named obligations, and the row conditional on them -/

/-- **OBLIGATION 1 — the `A` half.  RESEARCH.**  `v_p(Δ·p⁻²·Σ_k ε_k cTerm_k A_{t_k}) ≥ φ̃`.
`pval_harmA` gives `v_p(Σ …) ≥ 0`, so with `v_p(Δ) = 2` this is already `≥ 0`; what is missing
is the two units the `p⁻²` costs, and `ptp_cancel_probe` localises them to ONE congruence per
CELL over a contiguous run of residues (`Zeta2PtpRun.pow_dvd_cTerm_of_units` confines the support,
`vp_cTerm_residue_invariant` makes the run block-independent).  No mechanism is proved. -/
def AHalfOpen : Prop :=
  ∀ n p : ℕ, p ∈ phiWindow n →
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))))
      (((Δ 16 15 n : ℕ) : ℚ) * ((1 / (p : ℚ) ^ 2) * harmA n p))

/-- **OBLIGATION 2 — the POLYNOMIAL half.  MEASURED, UNPRICED, and named here for the first
time.**  `v_p(Δ·Π·pnPoly) ≥ φ̃`.  `Zeta2PnFunc.Δ_mul_Pin_pnPoly_int` gives INTEGRALITY, which is
`v_p ≥ 0`; the profile asks for up to 2 more.  `ptp_cancel_probe.py` scores it as its own arm A8
(366 of 366) precisely because `P n` is the DIFFERENCE of the two halves and the ultrametric
needs a bound on EACH — "the open obligation is the `A` half and nothing else" was wrong by this
obligation. -/
def PolyHalfOpen : Prop :=
  ∀ n p : ℕ, p ∈ phiWindow n →
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))))
      (((Δ 16 15 n : ℕ) : ℚ) * (candidateM.Pin n * candidateM.pnPoly n))

/-- **The per-prime bound, from the two open halves and the `B` half proved.** -/
theorem pow_dvd_P_of_two_halves {n p : ℕ} (hp : p ∈ phiWindow n)
    (hpoly : PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))))
      (((Δ 16 15 n : ℕ) : ℚ) * (candidateM.Pin n * candidateM.pnPoly n)))
    (hA : PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))))
      (((Δ 16 15 n : ℕ) : ℚ) * ((1 / (p : ℚ) ^ 2) * harmA n p)))
    (P : ℕ → ℤ) (hP : ((P n : ℤ) : ℚ) = ((Δ 16 15 n : ℕ) : ℚ) * candidateM.pn n) :
    (p : ℤ) ^ phiT (Int.fract ((n : ℚ) / (p : ℚ))) ∣ P n := by
  have hpp := prime_of_mem_phiWindow hp
  refine pow_dvd_of_pval hpp ?_
  rw [hP, Member.pn, Zeta2PnFunc.sgn_candidate]
  have hsplit := Pin_pnHarm_split hp
  have hrw : ((Δ 16 15 n : ℕ) : ℚ)
        * (-(-1 : ℚ) * candidateM.Pin n * (candidateM.pnPoly n - candidateM.pnHarm n))
      = (((Δ 16 15 n : ℕ) : ℚ) * (candidateM.Pin n * candidateM.pnPoly n))
        + (-(((Δ 16 15 n : ℕ) : ℚ) * harmB n p))
        + (-(((Δ 16 15 n : ℕ) : ℚ) * ((1 / (p : ℚ) ^ 2) * harmA n p))) := by
    linear_combination (-(((Δ 16 15 n : ℕ) : ℚ))) * hsplit
  rw [hrw]
  exact pval_add hpp (pval_add hpp hpoly (pval_neg (B_half_clears hp))) (pval_neg hA)

/-- The window-wide assembly: `Φ̃ₙ` is a product over DISTINCT primes, so per-prime power
divisibility multiplies up.  The `natAbs.factorization` spelling of `Zeta2PhiTDvd` needs `z ≠ 0`;
this one does not. -/
theorem PhiT_dvd_of_forall_pow (n : ℕ) (z : ℤ)
    (h : ∀ p ∈ phiWindow n, (p : ℤ) ^ phiT (Int.fract ((n : ℚ) / (p : ℚ))) ∣ z) :
    ((PhiT n : ℕ) : ℤ) ∣ z := by
  rw [PhiT]
  push_cast
  refine Finset.prod_dvd_of_coprime ?_ h
  intro a ha b hb hab
  have hpa := prime_of_mem_phiWindow (Finset.mem_coe.mp ha)
  have hpb := prime_of_mem_phiWindow (Finset.mem_coe.mp hb)
  exact ((Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hpa hpb).mpr hab)).pow :
    IsCoprime ((a : ℤ) ^ _) ((b : ℤ) ^ _))

/-- **ROW PT-P, CONDITIONAL ON ITS TWO OPEN HALVES.**  Given `PolyHalfOpen` and `AHalfOpen`,
the row delivers `hP` at `Δ̃` — the binder every landed rate on `Δ̃` is stated at, not the
un-divided `Δ 16 15`.  Read the type: it names BOTH open obligations, so a `#print axioms`
receipt on it says nothing about whether the row is closed (LEAN.md §1, "a binder is not an
axiom"). -/
theorem hP_at_ΔT_of_two_halves (hpoly : PolyHalfOpen) (hA : AHalfOpen) :
    ∃ P : ℕ → ℤ, ∀ n, ((P n : ℤ) : ℝ) = ΔT n * ((candidateM.pn n : ℚ) : ℝ) := by
  classical
  obtain ⟨P, hP⟩ := Zeta2PnHarmDelta.pn_cleared_1615
  have hdvd : ∀ n, ((PhiT n : ℕ) : ℤ) ∣ P n := fun n =>
    PhiT_dvd_of_forall_pow n (P n) fun p hp =>
      pow_dvd_P_of_two_halves hp (hpoly n p hp) (hA n p hp) P (hP n)
  choose c hc using fun n => hdvd n
  refine ⟨c, fun n => ?_⟩
  have hΦ : ((PhiT n : ℕ) : ℝ) ≠ 0 := PhiT_cast_ne_zero n
  have hPn : ((P n : ℤ) : ℝ) = ((Δ 16 15 n : ℕ) : ℝ) * ((candidateM.pn n : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) (hP n)
  have hcn : ((PhiT n : ℕ) : ℝ) * ((c n : ℤ) : ℝ) = ((P n : ℤ) : ℝ) := by
    rw [hc n]; push_cast; ring
  have hfin : ((PhiT n : ℕ) : ℝ) * ((c n : ℤ) : ℝ)
      = ((PhiT n : ℕ) : ℝ) * (ΔT n * ((candidateM.pn n : ℚ) : ℝ)) := by
    rw [hcn, hPn, ← ΔT_mul_PhiT n]
    ring
  exact mul_left_cancel₀ hΦ hfin

/-! ## 6. Two pins that make the split non-vacuous, and the smallest cell -/

/-- The split at `p = 2, m = 3`: `H⁽²⁾₃ = 49/36`, `B₃ = 1 + 1/9 = 10/9`, `A₁ = 1`, and
`10/9 + 1/4 = 49/36`.  A file that proved the split with the WRONG index would still elaborate;
this is the arithmetic that says which index. -/
theorem polar_split_at_two_three : harm 2 3 = Bpart 2 2 3 + (1 / (2 : ℚ) ^ 2) * harm 2 1 :=
  polar_split (by norm_num) 2 3

theorem Bpart_two_three : Bpart 2 2 3 = 10 / 9 := by decide +kernel

theorem harm_two_three : harm 2 3 = 49 / 36 := by decide +kernel

end Zeta2PtpPolar

#print axioms Zeta2PtpPolar.pval_add
#check @Zeta2PtpPolar.pval_add
#print axioms Zeta2PtpPolar.pval_mul
#check @Zeta2PtpPolar.pval_mul
#print axioms Zeta2PtpPolar.pval_sum
#check @Zeta2PtpPolar.pval_sum
#print axioms Zeta2PtpPolar.pow_dvd_of_pval
#check @Zeta2PtpPolar.pow_dvd_of_pval
#print axioms Zeta2PtpPolar.sum_Icc_eq_harm
#check @Zeta2PtpPolar.sum_Icc_eq_harm
#print axioms Zeta2PtpPolar.filter_dvd_eq_image
#check @Zeta2PtpPolar.filter_dvd_eq_image
#print axioms Zeta2PtpPolar.sum_multiples
#check @Zeta2PtpPolar.sum_multiples
#print axioms Zeta2PtpPolar.polar_split
#check @Zeta2PtpPolar.polar_split
#print axioms Zeta2PtpPolar.pval_Bpart
#check @Zeta2PtpPolar.pval_Bpart
#print axioms Zeta2PtpPolar.pval_harm_of_lt
#check @Zeta2PtpPolar.pval_harm_of_lt
#print axioms Zeta2PtpPolar.pos_of_mem_phiWindow
#check @Zeta2PtpPolar.pos_of_mem_phiWindow
#print axioms Zeta2PtpPolar.phiT_le_two
#check @Zeta2PtpPolar.phiT_le_two
#print axioms Zeta2PtpPolar.pval_Delta
#check @Zeta2PtpPolar.pval_Delta
#print axioms Zeta2PtpPolar.harmIndex_lt_sq
#check @Zeta2PtpPolar.harmIndex_lt_sq
#print axioms Zeta2PtpPolar.Pin_pnHarm_split
#check @Zeta2PtpPolar.Pin_pnHarm_split
#print axioms Zeta2PtpPolar.pval_harmB
#check @Zeta2PtpPolar.pval_harmB
#print axioms Zeta2PtpPolar.B_half_clears
#check @Zeta2PtpPolar.B_half_clears
#print axioms Zeta2PtpPolar.pval_harmA
#check @Zeta2PtpPolar.pval_harmA
#print axioms Zeta2PtpPolar.pow_dvd_P_of_two_halves
#check @Zeta2PtpPolar.pow_dvd_P_of_two_halves
#print axioms Zeta2PtpPolar.PhiT_dvd_of_forall_pow
#check @Zeta2PtpPolar.PhiT_dvd_of_forall_pow
#print axioms Zeta2PtpPolar.hP_at_ΔT_of_two_halves
#check @Zeta2PtpPolar.hP_at_ΔT_of_two_halves
#print axioms Zeta2PtpPolar.polar_split_at_two_three
#check @Zeta2PtpPolar.polar_split_at_two_three
#print axioms Zeta2PtpPolar.Bpart_two_three
#print axioms Zeta2PtpPolar.harm_two_three
