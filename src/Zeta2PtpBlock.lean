/-
# Row PT-P, layer 6 — the BLOCK REDUCTION of `AHalfOpen`, and the polynomial toolkit the
# run congruence is proved with

`Zeta2PtpPolar` left row PT-P's harmonic side as ONE named `Prop`, `AHalfOpen`:

    PVal p φ̃ (Δ · p⁻² · harmA n p),   harmA n p = Σ_{k ∈ window} ε_k · cTerm n k · A_{⌊(k−4n−1)/p⌋}

and `ptp_mechanism_probe.py` (16 arms green, 9 controls fired, 4 672 scorings) identified WHY it
holds: the coefficient `A_t = H⁽²⁾_t` is constant on each `p`-block `t = ⌊m/p⌋` of `m = k−4n−1`,
so it suffices that **each signed block sum** `Σ_{⌊m/p⌋ = t} ε_k·cTerm n k` is `≡ 0 mod p^φ̃`; and
on a block the signed unit part `(−1)^{k−1}·cTerm/p^{φ̃−1} mod p` is a POLYNOMIAL in the residue
`u = m mod p` of degree `D ≤ p−2`, whose full-period sum vanishes because `Σ_{u<p} u^j ≡ 0` for
`j < p−1`.

THIS FILE IS THE STRATUM-FREE PART OF THAT PROOF, in five pieces:

1. **The period sum** — `sum_eval_eq_zero`: a polynomial over `ZMod p` of `natDegree ≤ p−2` sums
   to `0` over all of `ZMod p` (`FiniteField.sum_pow_lt_card_sub_one`, present at the pin), and
   its integer form `dvd_sum_of_poly`: if `g u ≡ κ·f(u) (mod p)` for every `u < p` then
   `p ∣ Σ_{u<p} g u`.
2. **Lucas per factor** — `lucas_factor`: `C(S, A) ≡ binPoly(A mod p)(S) · C(S/p, A/p)` where
   `binPoly p j = X(X−1)⋯(X−j+1)/j!` is a polynomial of degree `j` over `ZMod p`.  This is
   Mathlib's `Choose.choose_modEq_choose_mod_mul_choose_div_nat` with the units-digit binomial
   read as a polynomial through `descPochhammer_eval_eq_descFactorial`.  It is UNCONDITIONAL —
   when the units addition carries, both sides are `0`, so no carry case split is ever needed.
3. **Wilson's reflection** — `factorial_reflect`: `X!·(p−1−X)! ≡ (−1)^{X+1}`, and from it
   `signChoose_eq`: `(−1)^X·C(e, X) = signChoosePoly p e (X)`, a polynomial of degree `p−1−e`.
   This is what turns the FOURTH binomial `C(11n, m−11n)` — whose top argument is the constant
   `11n`, not `m` — into a polynomial in `u` together with the alternating sign.
4. **The block reduction** — `blockSum n p t` and `AHalfOpen_of_blocks`: `AHalfOpen` follows from
   `∀ n p ∈ window, ∀ t, p^φ̃ ∣ blockSum n p t`.  `blockSum_dvd_of_noShort` connects the seven
   run-free strata of `Zeta2PtpCong` to it termwise.
5. **The residue reindex** — `blockSum_eq_sum_range`: a block sum as a sum over `u < p` with the
   window membership as an `if`, the shape in which a per-stratum polynomial identity is stated.

WHAT IS NOT HERE, said plainly.  No stratum is closed in this file: the per-`(n,p)` polynomial
identity `ε_k·cTerm ≡ κ_t·Π(u)` with `deg Π ≤ p−2` is stratum-specific (it needs the six floors
`⌊c·r/p⌋` fixed) and lives in its own files.  `Zeta2PtpPolar.PolyHalfOpen` — the polynomial half
`v_p(Δ·Π·pnPoly) ≥ φ̃`, MEASURED (366 of 366) and never given a mechanism — is UNTOUCHED, and
row PT-P needs BOTH halves.  PT-P stays OPEN and `Zeta2Target.zeta2_not_liouvilleWith` stays
`sorry`.

Probe: `ptp_mechanism_probe.py` / `.out` (arms P2, S3–S6 are the facts this file proves generically).
Falsifier: `falsify_ptpblock.sh` / `out_ptpblock_falsify.txt`.

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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.NumberTheory.Wilson
import Mathlib.RingTheory.Polynomial.Pochhammer

set_option maxRecDepth 20000

namespace Zeta2PtpBlock

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpPolar Nat Finset Polynomial

/-! ## 1. The period sum: a polynomial of degree `≤ p − 2` sums to `0` over `ZMod p` -/

section PeriodSum
variable {p : ℕ} [hp : Fact p.Prime]

instance instNeZeroOfFactPrime : NeZero p := ⟨hp.out.ne_zero⟩

/-- `Σ_{x ∈ 𝔽_p} x^i = 0` for `i < p − 1` — Mathlib's `FiniteField.sum_pow_lt_card_sub_one` at
`K = ZMod p`.  This is `ptp_mechanism_probe.py` arm P2; its control R6 (`i = p − 1` gives `−1`) is
`period_sharp_five` below. -/
theorem sum_pow_eq_zero (i : ℕ) (hi : i < p - 1) : ∑ x : ZMod p, x ^ i = 0 :=
  FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) i (by rwa [ZMod.card])

/-- **A polynomial of degree `≤ p − 2` sums to `0` over a full period.** -/
theorem sum_eval_eq_zero (f : (ZMod p)[X]) (hf : f.natDegree ≤ p - 2) :
    ∑ x : ZMod p, f.eval x = 0 := by
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have h2 := hp.out.two_le
  rw [← Finset.mul_sum, sum_pow_eq_zero i (by omega), mul_zero]

/-- The full period `ZMod p` IS the residues `u < p`. -/
theorem sum_univ_eq_sum_range (F : ZMod p → ZMod p) :
    ∑ x : ZMod p, F x = ∑ u ∈ Finset.range p, F (u : ZMod p) :=
  Finset.sum_nbij' (fun x : ZMod p => x.val) (fun u : ℕ => (u : ZMod p))
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) (fun u _ => Finset.mem_univ _)
    (fun x _ => ZMod.natCast_zmod_val x)
    (fun u hu => ZMod.val_cast_of_lt (Finset.mem_range.mp hu))
    (fun x _ => by rw [ZMod.natCast_zmod_val])

theorem sum_range_eval_eq_zero (f : (ZMod p)[X]) (hf : f.natDegree ≤ p - 2) :
    ∑ u ∈ Finset.range p, f.eval (u : ZMod p) = 0 :=
  (sum_univ_eq_sum_range (fun x => f.eval x)).symm.trans (sum_eval_eq_zero f hf)

/-- **THE BLOCK LEMMA.**  If an integer sequence agrees mod `p` on `u < p` with a constant times a
polynomial of degree `≤ p − 2`, its sum over the period is divisible by `p`.  Every block
congruence of the run reduces to exhibiting `κ` and `f`. -/
theorem dvd_sum_of_poly (g : ℕ → ℤ) (κ : ZMod p) (f : (ZMod p)[X]) (hf : f.natDegree ≤ p - 2)
    (h : ∀ u < p, ((g u : ℤ) : ZMod p) = κ * f.eval (u : ZMod p)) :
    (p : ℤ) ∣ ∑ u ∈ Finset.range p, g u := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [Finset.sum_congr rfl (fun u hu => h u (Finset.mem_range.mp hu)), ← Finset.mul_sum,
    sum_range_eval_eq_zero f hf, mul_zero]

end PeriodSum

/-! ## 2. Lucas per factor: a binomial's units digit is a polynomial in its top argument -/

section Lucas
variable {p : ℕ} [hp : Fact p.Prime]

/-- `binPoly p j = X(X−1)⋯(X−j+1)/j!` over `ZMod p`, the binomial `C(X, j)` as a polynomial.
Meaningful for `j < p`, where `j!` is a unit. -/
noncomputable def binPoly (p j : ℕ) : (ZMod p)[X] :=
  C (((j ! : ℕ) : ZMod p)⁻¹) * descPochhammer (ZMod p) j

theorem binPoly_natDegree_le (j : ℕ) : (binPoly p j).natDegree ≤ j := by
  unfold binPoly
  exact (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree (ZMod p) j).le

theorem factorial_cast_ne_zero {j : ℕ} (hj : j < p) : ((j ! : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, hp.out.dvd_factorial]
  omega

/-- `C(N, j) ≡ binPoly(j)(N)` for `j < p`, at EVERY natural `N` — including `N < j`, where both
sides vanish. -/
theorem choose_cast_eq_binPoly (N j : ℕ) (hj : j < p) :
    ((N.choose j : ℕ) : ZMod p) = (binPoly p j).eval (N : ZMod p) := by
  have h : ((N.descFactorial j : ℕ) : ZMod p)
      = ((j ! : ℕ) : ZMod p) * ((N.choose j : ℕ) : ZMod p) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  unfold binPoly
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial, h, ← mul_assoc,
    inv_mul_cancel₀ (factorial_cast_ne_zero hj), one_mul]

/-- **Lucas, one factor at a time.**  `C(S, A) ≡ binPoly(A mod p)(S) · C(⌊S/p⌋, ⌊A/p⌋) (mod p)`.
Unconditional: when the units addition carries, `binPoly(A mod p)(S) = C(S mod p, A mod p) = 0`
and so is the left side. -/
theorem lucas_factor (S A : ℕ) :
    ((S.choose A : ℕ) : ZMod p)
      = (binPoly p (A % p)).eval (S : ZMod p) * (((S / p).choose (A / p) : ℕ) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := S) (k := A)
  rw [← ZMod.natCast_eq_natCast_iff] at h
  rw [h]
  push_cast
  rw [choose_cast_eq_binPoly (S % p) (A % p) (Nat.mod_lt _ hp.out.pos), ZMod.natCast_mod]

end Lucas

/-! ## 3. Wilson's reflection: `(−1)^X · C(e, X)` is a polynomial of degree `p − 1 − e` -/

section Reflect
variable {p : ℕ} [hp : Fact p.Prime]

theorem cast_eq_neg_of_add_eq {a b : ℕ} (h : a + b = p) : (a : ZMod p) = -(b : ZMod p) := by
  have := congrArg (fun m : ℕ => (m : ZMod p)) h
  push_cast at this
  rw [ZMod.natCast_self] at this
  linear_combination this

/-- **`X!·(p−1−X)! ≡ (−1)^{X+1} (mod p)`** — Wilson's lemma reflected through `X`.  Pinned at
`X = 3, p = 7` (`reflect_pin_seven`) and the sign is load-bearing (`reflect_sharp_seven`). -/
theorem factorial_reflect (X : ℕ) (hX : X ≤ p - 1) :
    ((X ! : ℕ) : ZMod p) * (((p - 1 - X)! : ℕ) : ZMod p) = (-1) ^ (X + 1) := by
  induction X with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.sub_zero, zero_add, pow_one]
    exact ZMod.wilsons_lemma p
  | succ X ih =>
    have h1 := ih (by omega)
    have hY : p - 1 - X = (p - 1 - (X + 1)) + 1 := by omega
    rw [hY, Nat.factorial_succ] at h1
    have hneg : ((p - 1 - (X + 1) + 1 : ℕ) : ZMod p) = -((X + 1 : ℕ) : ZMod p) :=
      cast_eq_neg_of_add_eq (by omega)
    rw [Nat.cast_mul, hneg] at h1
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast at h1 ⊢
    linear_combination (-1 : ZMod p) * h1

/-- `signChoosePoly p e (X) = −e! · (p−1−X)(p−2−X)⋯(e+1−X)`, of degree `p − 1 − e`. -/
noncomputable def signChoosePoly (p e : ℕ) : (ZMod p)[X] :=
  C (-((e ! : ℕ) : ZMod p)) * (descPochhammer (ZMod p) (p - 1 - e)).comp (-1 - X)

theorem signChoosePoly_natDegree_le (e : ℕ) : (signChoosePoly p e).natDegree ≤ p - 1 - e := by
  unfold signChoosePoly
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  rw [descPochhammer_natDegree]
  have h1 : (-1 - X : (ZMod p)[X]).natDegree ≤ 1 := by
    have : (-1 - X : (ZMod p)[X]) = -(X + C 1) := by rw [C_1]; ring
    rw [this, natDegree_neg, natDegree_X_add_C]
  calc (p - 1 - e) * (-1 - X : (ZMod p)[X]).natDegree
      ≤ (p - 1 - e) * 1 := Nat.mul_le_mul_left _ h1
    _ = p - 1 - e := Nat.mul_one _

/-- **`(−1)^X · C(e, X) = signChoosePoly p e (X)`** for `e < p`, `X < p` — at every such `X`,
including `X > e` where both sides are `0`. -/
theorem signChoose_eq (e X : ℕ) (he : e < p) (hX : X < p) :
    (-1 : ZMod p) ^ X * ((e.choose X : ℕ) : ZMod p)
      = (signChoosePoly p e).eval (X : ZMod p) := by
  have hcast : ((p - 1 - X : ℕ) : ZMod p) = -1 - (X : ZMod p) := by
    have h := cast_eq_neg_of_add_eq (p := p) (a := p - 1 - X) (b := X + 1) (by omega)
    rw [h]; push_cast; ring
  have hDF : (descPochhammer (ZMod p) (p - 1 - e)).eval (-1 - (X : ZMod p))
      = (((p - 1 - X).descFactorial (p - 1 - e) : ℕ) : ZMod p) := by
    rw [← hcast, descPochhammer_eval_eq_descFactorial]
  unfold signChoosePoly
  rw [eval_mul, eval_C, eval_comp, eval_sub, eval_neg, eval_one, eval_X, hDF]
  rcases Nat.lt_or_ge e X with hXe | hXe
  · rw [Nat.choose_eq_zero_of_lt hXe, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp
  · have h1 : ((e.choose X : ℕ) : ZMod p) * ((X ! : ℕ) : ZMod p) * (((e - X)! : ℕ) : ZMod p)
        = ((e ! : ℕ) : ZMod p) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hXe]
    have h2 : (((e - X)! : ℕ) : ZMod p) * (((p - 1 - X).descFactorial (p - 1 - e) : ℕ) : ZMod p)
        = (((p - 1 - X)! : ℕ) : ZMod p) := by
      have h := Nat.factorial_mul_descFactorial (show p - 1 - e ≤ p - 1 - X by omega)
      have h3 : p - 1 - X - (p - 1 - e) = e - X := by omega
      rw [h3] at h
      rw [← Nat.cast_mul, h]
    have hW := factorial_reflect (p := p) X (by omega)
    linear_combination
      (-(((p - 1 - X).descFactorial (p - 1 - e) : ℕ) : ZMod p)) * h1
      + (((e.choose X : ℕ) : ZMod p) * ((X ! : ℕ) : ZMod p)) * h2
      + ((e.choose X : ℕ) : ZMod p) * hW

end Reflect

/-! ## 4. The block reduction: `AHalfOpen` from one congruence per `p`-block -/

/-- **The signed block sum** `Σ_{k ∈ window, ⌊(k−4n−1)/p⌋ = t} (−1)^{12n+k−1} · cTerm n k`. -/
def blockSum (n p t : ℕ) : ℤ :=
  ∑ k ∈ (candidateM.window n).filter (fun k => (k - 4 * n - 1) / p = t),
    (-1 : ℤ) ^ (12 * n + k - 1) * (cTerm n k : ℤ)

/-- The block index is below `p` at a window prime — the Legendre line, spent once. -/
theorem block_lt {n k p : ℕ} (hp : p ∈ phiWindow n) (hk : k ∈ candidateM.window n) :
    (k - 4 * n - 1) / p < p := by
  have hpp := prime_of_mem_phiWindow hp
  have h := harmIndex_lt_sq hp hk
  rw [pow_two] at h
  exact (Nat.div_lt_iff_lt_mul hpp.pos).mpr h

/-- `harmA` grouped by block: `Σ_t A_t · blockSum t`. -/
theorem harmA_eq_blocks {n p : ℕ} (hp : p ∈ phiWindow n) :
    harmA n p = ∑ t ∈ Finset.range p, harm 2 t * (blockSum n p t : ℚ) := by
  unfold harmA
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range p)
      (g := fun k => (k - 4 * n - 1) / p) (fun k hk => Finset.mem_range.mpr (block_lt hp hk))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [blockSum, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [(Finset.mem_filter.mp hk).2]
  push_cast
  ring

theorem pval_harmA_of_blocks {n p v : ℕ} (hp : p ∈ phiWindow n)
    (hblk : ∀ t, (p : ℤ) ^ v ∣ blockSum n p t) : PVal p v (harmA n p) := by
  have hpp := prime_of_mem_phiWindow hp
  rw [harmA_eq_blocks hp]
  refine pval_sum hpp _ _ fun t ht => ?_
  have h := pval_mul hpp (pval_harm_of_lt hpp 2 t (Finset.mem_range.mp ht))
    (pval_of_pow_dvd hpp (hblk t))
  simpa using h

/-- `Δ/p²` is `p`-integral: the clearing supplies exactly the two units the polar factor costs. -/
theorem pval_Delta_div_sq {n p : ℕ} (hp : p ∈ phiWindow n) :
    PVal p 0 (((Δ 16 15 n : ℕ) : ℚ) * (1 / (p : ℚ) ^ 2)) := by
  obtain ⟨a, b, hb, hbp, hab⟩ := pval_Delta hp
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (prime_of_mem_phiWindow hp).ne_zero
  refine ⟨a, b, hb, hbp, ?_⟩
  rw [pow_zero, one_mul]
  field_simp
  linear_combination hab

/-- **The `A` half at one cell, from its block congruences.** -/
theorem AHalf_of_blocks {n p : ℕ} (hp : p ∈ phiWindow n)
    (hblk : ∀ t, (p : ℤ) ^ (phiT (Int.fract ((n : ℚ) / (p : ℚ)))) ∣ blockSum n p t) :
    PVal p (phiT (Int.fract ((n : ℚ) / (p : ℚ))))
      (((Δ 16 15 n : ℕ) : ℚ) * ((1 / (p : ℚ) ^ 2) * harmA n p)) := by
  have hpp := prime_of_mem_phiWindow hp
  rw [← mul_assoc]
  have h := pval_mul hpp (pval_Delta_div_sq hp) (pval_harmA_of_blocks hp hblk)
  simpa using h

/-- **`AHalfOpen` FROM BLOCK CONGRUENCES.**  Read the type: the hypothesis is the whole remaining
content of the harmonic side, one divisibility per `(n, p, t)`. -/
theorem AHalfOpen_of_blocks
    (h : ∀ n p, p ∈ phiWindow n →
      ∀ t, (p : ℤ) ^ (phiT (Int.fract ((n : ℚ) / (p : ℚ)))) ∣ blockSum n p t) :
    AHalfOpen :=
  fun n p hp => AHalf_of_blocks hp (h n p hp)

/-- On a cell with no short term the block congruence is termwise — `Zeta2PtpCong`'s seven
run-free strata plug in here through `noShort_of_runFreeTwo` / `noShort_of_runFreeOne`. -/
theorem blockSum_dvd_of_noShort {n p v : ℕ} (hp : p ∈ phiWindow n)
    (h : Zeta2PtpStratum.NoShort p n v) (t : ℕ) : (p : ℤ) ^ v ∣ blockSum n p t :=
  Zeta2PtpStratum.pow_dvd_signed_sum hp h _ (fun _ hk => (Finset.mem_filter.mp hk).1)
    (fun k => (-1 : ℤ) ^ (12 * n + k - 1))

/-! ## 5. A block as a sum over the residue `u < p` -/

/-- **The residue reindex.**  `k = t·p + u + 4n + 1`, `u < p`, with the window as an `if`: the
shape a per-stratum polynomial identity `term(u) = κ_t · Π(u)` is stated in, off-window `u`
included (where the identity says `κ_t · Π(u) = 0`). -/
theorem blockSum_eq_sum_range {n p : ℕ} (hp : 0 < p) (t : ℕ) :
    blockSum n p t = ∑ u ∈ Finset.range p,
      if t * p + u + 4 * n + 1 ∈ candidateM.window n
      then (-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
            * (cTerm n (t * p + u + 4 * n + 1) : ℤ)
      else 0 := by
  rw [blockSum, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun u => t * p + u + 4 * n + 1) (fun k => (k - 4 * n - 1) % p)
    ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_range] at hu
    rw [Finset.mem_filter]
    refine ⟨hu.2, ?_⟩
    have e : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
    rw [e, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hu.1, zero_add]
  · intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hp, ?_⟩
    have hw := (mem_window_iff n k).1 hk.1
    have hdm := Nat.div_add_mod (k - 4 * n - 1) p
    rw [hk.2, Nat.mul_comm p t] at hdm
    have e : t * p + (k - 4 * n - 1) % p + 4 * n + 1 = k := by
      generalize (k - 4 * n - 1) % p = w at hdm ⊢
      omega
    rw [e]; exact hk.1
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_range] at hu
    have e : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
    simp only [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu.1]
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hw := (mem_window_iff n k).1 hk.1
    have hdm := Nat.div_add_mod (k - 4 * n - 1) p
    rw [hk.2, Nat.mul_comm p t] at hdm
    generalize (k - 4 * n - 1) % p = w at hdm ⊢
    omega
  · intro u _; rfl

/-! ## 6. Pins — the two hypotheses that make the period sum work are SHARP -/

/-- `Σ_{x ∈ 𝔽₅} x³ = 0`: degree `3 = p − 2` still sums to `0`. -/
theorem period_pin_five : ∑ x : ZMod 5, x ^ 3 = 0 := by decide

/-- `Σ_{x ∈ 𝔽₅} x⁴ = 4 = −1 ≠ 0`: the bound `≤ p − 2` in `sum_eval_eq_zero` cannot be relaxed to
`≤ p − 1` (control R6 of the probe). -/
theorem period_sharp_five : ∑ x : ZMod 5, x ^ 4 = 4 := by decide

/-- `3!·3! = 36 ≡ 1 = (−1)⁴ (mod 7)`, `factorial_reflect` at `p = 7`, `X = 3`. -/
theorem reflect_pin_seven : ((3 ! : ℕ) : ZMod 7) * (((7 - 1 - 3)! : ℕ) : ZMod 7) = (-1) ^ 4 := by
  decide

/-- and it is NOT `(−1)³`: the exponent's `+1` is load-bearing. -/
theorem reflect_sharp_seven :
    ((3 ! : ℕ) : ZMod 7) * (((7 - 1 - 3)! : ℕ) : ZMod 7) ≠ (-1) ^ 3 := by
  decide

/-- The smallest run-carrying cell, `n = 3`, `p = 13`, `φ̃ = 1`, block `t = 2` (the block whose
run `u ∈ [8, 12]` `Zeta2PtpRun.run_at_3_13` pins): its signed block sum IS divisible by `13` … -/
theorem blockSum_pin_3_13_2 : (13 : ℤ) ∣ blockSum 3 13 2 := by decide

/-- … and NOT by `13²` — the block congruence is sharp at `φ̃` (probe control R4). -/
theorem blockSum_sharp_3_13_2 : ¬ (169 : ℤ) ∣ blockSum 3 13 2 := by decide

end Zeta2PtpBlock

#print axioms Zeta2PtpBlock.sum_pow_eq_zero
#check @Zeta2PtpBlock.sum_pow_eq_zero
#print axioms Zeta2PtpBlock.sum_eval_eq_zero
#check @Zeta2PtpBlock.sum_eval_eq_zero
#print axioms Zeta2PtpBlock.sum_univ_eq_sum_range
#check @Zeta2PtpBlock.sum_univ_eq_sum_range
#print axioms Zeta2PtpBlock.sum_range_eval_eq_zero
#check @Zeta2PtpBlock.sum_range_eval_eq_zero
#print axioms Zeta2PtpBlock.dvd_sum_of_poly
#check @Zeta2PtpBlock.dvd_sum_of_poly
#print axioms Zeta2PtpBlock.binPoly_natDegree_le
#check @Zeta2PtpBlock.binPoly_natDegree_le
#print axioms Zeta2PtpBlock.factorial_cast_ne_zero
#check @Zeta2PtpBlock.factorial_cast_ne_zero
#print axioms Zeta2PtpBlock.choose_cast_eq_binPoly
#check @Zeta2PtpBlock.choose_cast_eq_binPoly
#print axioms Zeta2PtpBlock.lucas_factor
#check @Zeta2PtpBlock.lucas_factor
#print axioms Zeta2PtpBlock.cast_eq_neg_of_add_eq
#check @Zeta2PtpBlock.cast_eq_neg_of_add_eq
#print axioms Zeta2PtpBlock.factorial_reflect
#check @Zeta2PtpBlock.factorial_reflect
#print axioms Zeta2PtpBlock.signChoosePoly_natDegree_le
#check @Zeta2PtpBlock.signChoosePoly_natDegree_le
#print axioms Zeta2PtpBlock.signChoose_eq
#check @Zeta2PtpBlock.signChoose_eq
#print axioms Zeta2PtpBlock.block_lt
#check @Zeta2PtpBlock.block_lt
#print axioms Zeta2PtpBlock.harmA_eq_blocks
#check @Zeta2PtpBlock.harmA_eq_blocks
#print axioms Zeta2PtpBlock.pval_harmA_of_blocks
#check @Zeta2PtpBlock.pval_harmA_of_blocks
#print axioms Zeta2PtpBlock.pval_Delta_div_sq
#check @Zeta2PtpBlock.pval_Delta_div_sq
#print axioms Zeta2PtpBlock.AHalf_of_blocks
#check @Zeta2PtpBlock.AHalf_of_blocks
#print axioms Zeta2PtpBlock.AHalfOpen_of_blocks
#check @Zeta2PtpBlock.AHalfOpen_of_blocks
#print axioms Zeta2PtpBlock.blockSum_dvd_of_noShort
#check @Zeta2PtpBlock.blockSum_dvd_of_noShort
#print axioms Zeta2PtpBlock.blockSum_eq_sum_range
#check @Zeta2PtpBlock.blockSum_eq_sum_range
#print axioms Zeta2PtpBlock.period_pin_five
#check @Zeta2PtpBlock.period_pin_five
#print axioms Zeta2PtpBlock.period_sharp_five
#check @Zeta2PtpBlock.period_sharp_five
#print axioms Zeta2PtpBlock.reflect_pin_seven
#check @Zeta2PtpBlock.reflect_pin_seven
#print axioms Zeta2PtpBlock.reflect_sharp_seven
#check @Zeta2PtpBlock.reflect_sharp_seven
#print axioms Zeta2PtpBlock.blockSum_pin_3_13_2
#check @Zeta2PtpBlock.blockSum_pin_3_13_2
#print axioms Zeta2PtpBlock.blockSum_sharp_3_13_2
#check @Zeta2PtpBlock.blockSum_sharp_3_13_2
