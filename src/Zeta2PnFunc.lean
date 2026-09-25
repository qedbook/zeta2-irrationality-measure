/-
# `Zeta2PnFunc.lean` — row PNCLR: the VALUES → COEFFICIENTS step

`Zeta2NewtonAssemble` left row PNCLR owing the step from what it proved —
`Δ 16 15 n · Π(n) · Ppol_n(t) ∈ ℤ` at every integer ARGUMENT `t` — to what the row's statement
is about, the polynomial's COEFFICIENTS:

    candidateM.pnPoly n = Σ_{j < 16n} (Ppol n).coeff j · momI (cell n) j.

Nothing termwise crosses (`Π·(Ppol).coeff j ∉ ℤ` at EVERY `j` and every `n`, measured), so the
content is the sum.  **This file closes that step**, and the mechanism is that `Δ 16 15 n` is a
PRODUCT of two factors doing two different jobs:

  * `D (15n)` clears the NEWTON COEFFICIENT of `Π·Ppol` — `Zeta2NewtonCarry`'s termwise
    invariant at `D (13n) ∣ D (15n)` (`termwise_at_D15` below);
  * `D (16n)` clears the BERNOULLI FUNCTIONAL of the Newton basis —

        L(nbp (15n) r) = Σ_{m ≤ r} (-1)^m / (m+1) · C(11n, r-m)                     (`Lf_nbp`)

    whose denominator divides `lcm(1 … r+1)` and hence `D (16n)` for `r ≤ 16n - 1`.

`Δ_mul_Pin_pnPoly_int` is the conclusion: `Δ 16 15 n · Π(n) · pnPoly n ∈ ℤ`.

The `-4n` in the functional is `momI (candidateM.cell n) j = (Polynomial.bernoulli j).eval (-4n)`
— **`Zeta2Defs.momI`, NOT `Zeta2Moments.momI`**, which is a different constant with no `rfl`
between them (the bridge is `Zeta2T1Eval.momI_agree`).  This file is on `Zeta2Defs.momI`
throughout, because that is what `Member.pnPoly` sums against.

## What is NOT here, said plainly

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`, and **row PNCLR does not
close here either** — for a reason no earlier cell of the chain doc stated as an obligation.
`pₙ = -sgn·Π·(pnPoly - pnHarm)` has TWO halves, and the landed harmonic lemma
`Zeta2PnHarm.harmInt_cast` clears its half by `D (22n)²`, which is not a divisor of
`Δ 16 15 n = D(16n)·D(15n)` — `D (22n)` does not even divide `D (16n)`.  So the row's harmonic
half is open AT THE ROW'S OWN CONSTANTS.  `pn_cleared_1615_of_harm` states exactly what is left,
and `harm_cleared_of_dvd` reduces it to ONE divisibility with no sum in it:

    D (k - 4n - 1)² ∣ Δ 16 15 n · cTerm n k      for every k in the window

— measured true termwise at 16 863 of 16 863 `(k, i)` pairs, `n ≤ 6`
(`pn_harm_delta_probe.py` arm B2, `.out`).

## Provenance of each step

* `nbp_absorb`, `nbp_pascal`, `nbp_comp_add_one` — the Newton basis's three laws, each by
  `Polynomial.funext` from `Zeta2NewtonAssemble.nbp_eval`.
* `umb_shift` — the umbral lift `Σ_j p.coeff j • bernoulli j` intertwines the shift with the
  derivative.  Its whole content is Mathlib's `Polynomial.sum_bernoulli`, used at `k - 1`.
  Censused 2026-09-19 at this pin: Mathlib has NO Nörlund/Stirling-style bridge between
  `Polynomial.bernoulli` and binomial coefficients, and no
  `derivative_ascPochhammer`/`derivative_descPochhammer`; `sum_bernoulli` is the one hinge.
* `deriv_nbp` — `d/du C(u, r+1) = Σ_{m ≤ r} (-1)^m/(m+1) · C(u, r-m)`, built here by induction
  through `nbp_absorb`.  Measured first as an exact polynomial identity for `r ≤ 25`
  (`pn_functional_probe.py` arm A5), and the whole decomposition measured containment-style
  (arms A0–A3, every `r < 16n`, `n ≤ 5`, plus `n = 8, 12` out of sample).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2PnHarm
import Zeta2PpolVal
import Zeta2PpolInt
import Zeta2NewtonCarry
import Zeta2NewtonAssemble
import Zeta2ArithBridge
import Zeta2ArithAssemble
import Zeta2PnCleared
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots

namespace Zeta2PnFunc

open Zeta2Defs Zeta2Arith Zeta2NewtonAssemble Finset Polynomial

/-! ## 1. Three laws of the Newton basis -/

theorem nbp_zero (s : ℚ) : nbp s 0 = 1 := by
  simp [nbp]

theorem nbp_one (s : ℚ) : nbp s 1 = X + C s := by
  simp [nbp]

/-- **Absorption.** `(X + s - r) · C(X+s, r) = (r+1) · C(X+s, r+1)`. -/
theorem nbp_absorb (s : ℚ) (r : ℕ) :
    (X + C (s - (r : ℚ))) * nbp s r = C ((r : ℚ) + 1) * nbp s (r + 1) := by
  refine Polynomial.funext fun t => ?_
  rw [eval_mul, eval_mul, eval_add, eval_X, eval_C, eval_C, nbp_eval, nbp_eval,
    Finset.prod_range_succ]
  have h1 : ((Nat.factorial r : ℕ) : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero r
  have h2 : ((Nat.factorial (r + 1) : ℕ) : ℚ) = ((r : ℚ) + 1) * ((Nat.factorial r : ℕ) : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h3 : ((r : ℚ) + 1) ≠ 0 := by positivity
  rw [h2]
  field_simp
  ring

/-- **Pascal.** `C(X+s+1, r+1) = C(X+s, r+1) + C(X+s, r)`. -/
theorem nbp_pascal (s : ℚ) (r : ℕ) :
    nbp (s + 1) (r + 1) = nbp s (r + 1) + nbp s r := by
  refine Polynomial.funext fun t => ?_
  rw [eval_add, nbp_eval, nbp_eval, nbp_eval]
  have hL : (∏ i ∈ range (r + 1), (t + (s + 1) - (i : ℚ)))
      = (∏ i ∈ range r, (t + s - (i : ℚ))) * (t + s + 1) := by
    rw [Finset.prod_range_succ' (fun i => (t + (s + 1) - (i : ℚ))) r]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by push_cast; ring
    · push_cast; ring
  have h1 : ((Nat.factorial r : ℕ) : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero r
  have h2 : ((Nat.factorial (r + 1) : ℕ) : ℚ) = ((r : ℚ) + 1) * ((Nat.factorial r : ℕ) : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h3 : ((r : ℚ) + 1) ≠ 0 := by positivity
  rw [hL, Finset.prod_range_succ, h2]
  field_simp
  ring

/-- The shift `X ↦ X + 1` moves the basis's node. -/
theorem nbp_comp_add_one (s : ℚ) (m : ℕ) : (nbp s m).comp (X + 1) = nbp (s + 1) m := by
  refine Polynomial.funext fun t => ?_
  rw [eval_comp, eval_add, eval_X, eval_one, nbp_eval, nbp_eval]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by ring

theorem nbp_natDegree (s : ℚ) (m : ℕ) : (nbp s m).natDegree = m :=
  Polynomial.natDegree_eq_of_degree_eq_some (nbp_degree s m)

/-! ## 2. The umbral lift, and the one Mathlib hinge -/

/-- `umb N p = Σ_{j < N} p.coeff j • B_j(X)` — the Bernoulli umbral lift, truncated at `N`. -/
noncomputable def umb (N : ℕ) (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ j ∈ range N, C (p.coeff j) * Polynomial.bernoulli j

theorem umb_add (N : ℕ) (p q : Polynomial ℚ) : umb N (p + q) = umb N p + umb N q := by
  simp only [umb, Polynomial.coeff_add, map_add, add_mul]
  exact Finset.sum_add_distrib

theorem umb_C_mul (N : ℕ) (a : ℚ) (p : Polynomial ℚ) : umb N (C a * p) = C a * umb N p := by
  simp only [umb, Polynomial.coeff_C_mul, map_mul, mul_assoc, Finset.mul_sum]

theorem umb_sum {ι : Type*} (N : ℕ) (s : Finset ι) (f : ι → Polynomial ℚ) :
    umb N (∑ i ∈ s, f i) = ∑ i ∈ s, umb N (f i) := by
  simp only [umb, Polynomial.finsetSum_coeff, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem umb_X_pow (N k : ℕ) (hk : k < N) :
    umb N ((X : Polynomial ℚ) ^ k) = Polynomial.bernoulli k := by
  rw [umb, Finset.sum_eq_single k]
  · simp [Polynomial.coeff_X_pow]
  · intro j _ hj
    simp [Polynomial.coeff_X_pow, hj]
  · intro h
    exact absurd (Finset.mem_range.mpr hk) h

/-- **The hinge, and it is one Mathlib lemma.**  `Σ_{j ≤ k} C(k,j) • B_j = B_k + k·X^{k-1}`,
from `Polynomial.sum_bernoulli` at `k - 1`. -/
theorem umb_X_add_one_pow (N k : ℕ) (hk : k < N) :
    umb N (((X : Polynomial ℚ) + 1) ^ k)
      = Polynomial.bernoulli k + derivative ((X : Polynomial ℚ) ^ k) := by
  have hsub : (range (k + 1) : Finset ℕ) ⊆ range N := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hsplit : umb N (((X : Polynomial ℚ) + 1) ^ k)
      = ∑ j ∈ range (k + 1), ((k.choose j : ℕ) : ℚ) • Polynomial.bernoulli j := by
    rw [umb, ← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun j _ => by
        rw [Polynomial.coeff_X_add_one_pow, smul_eq_C_mul]
    · intro j _ hj
      have hz : k.choose j = 0 :=
        Nat.choose_eq_zero_of_lt (by simpa [Finset.mem_range] using hj)
      rw [Polynomial.coeff_X_add_one_pow, hz, Nat.cast_zero, map_zero, zero_mul]
  rw [hsplit]
  cases k with
  | zero => simp
  | succ d =>
      rw [Finset.sum_range_succ, Polynomial.sum_bernoulli d, Nat.choose_self, Nat.cast_one,
        one_smul, Polynomial.derivative_X_pow]
      simp only [Nat.add_sub_cancel]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      push_cast
      ring

theorem sum_comp' {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) (q : Polynomial ℚ) :
    (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Polynomial.add_comp, ih, Finset.sum_insert ha]

/-- **The shift property.**  `umb (p(X+1)) = umb p + p'`. -/
theorem umb_shift (N : ℕ) (p : Polynomial ℚ) (hp : p.natDegree < N) :
    umb N (p.comp (X + 1)) = umb N p + derivative p := by
  have hp' : p = ∑ i ∈ range N, C (p.coeff i) * X ^ i := by
    conv_lhs => rw [Polynomial.as_sum_range' p N hp]
    exact Finset.sum_congr rfl fun i _ => (Polynomial.C_mul_X_pow_eq_monomial).symm
  have hcomp : p.comp (X + 1) = ∑ i ∈ range N, C (p.coeff i) * ((X : Polynomial ℚ) + 1) ^ i := by
    conv_lhs => rw [hp']
    rw [sum_comp']
    exact Finset.sum_congr rfl fun i _ => by
      rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp]
  have hu : umb N p = ∑ i ∈ range N, C (p.coeff i) * Polynomial.bernoulli i := rfl
  have hdp : derivative p
      = ∑ i ∈ range N, C (p.coeff i) * derivative ((X : Polynomial ℚ) ^ i) := by
    conv_lhs => rw [hp']
    rw [Polynomial.derivative_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.derivative_C_mul]
  have hterm : ∀ i ∈ range N, umb N (C (p.coeff i) * ((X : Polynomial ℚ) + 1) ^ i)
      = C (p.coeff i) * Polynomial.bernoulli i + C (p.coeff i) * derivative (X ^ i) := by
    intro i hi
    rw [umb_C_mul, umb_X_add_one_pow N i (Finset.mem_range.mp hi), mul_add]
  rw [hcomp, umb_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hu, hdp]

/-- **`umb` of the Newton basis IS the derivative of the next one.** -/
theorem umb_nbp (N : ℕ) (s : ℚ) (r : ℕ) (h : r + 1 < N) :
    umb N (nbp s r) = derivative (nbp s (r + 1)) := by
  have h1 := umb_shift N (nbp s (r + 1)) (by rw [nbp_natDegree]; exact h)
  rw [nbp_comp_add_one, nbp_pascal, umb_add] at h1
  exact add_left_cancel h1

/-! ## 3. The derivative of the Newton basis, IN the Newton basis -/

/-- `cf m = (-1)^m / (m+1)`. -/
noncomputable def cf (m : ℕ) : ℚ := (-1 : ℚ) ^ m / ((m : ℚ) + 1)

theorem cf_zero : cf 0 = 1 := by rw [cf]; norm_num

theorem cf_mul_succ (m : ℕ) : cf m * ((m : ℚ) + 1) = (-1 : ℚ) ^ m := by
  have h : ((m : ℚ) + 1) ≠ 0 := by positivity
  rw [cf]
  field_simp

/-- **`d/du C(u, r+1) = Σ_{m ≤ r} (-1)^m/(m+1) · C(u, r-m)`** — built here; Mathlib has no
derivative rule for `ascPochhammer`/`descPochhammer`/`Ring.choose` (censused at this pin). -/
theorem deriv_nbp (s : ℚ) : ∀ r : ℕ,
    derivative (nbp s (r + 1)) = ∑ m ∈ range (r + 1), C (cf m) * nbp s (r - m) := by
  intro r
  induction r with
  | zero =>
      rw [nbp_one, Finset.sum_range_one, cf_zero, map_one, one_mul, Nat.sub_self, nbp_zero]
      simp
  | succ r ih =>
      have hne : ((r : ℚ) + 2) ≠ 0 := by positivity
      -- (1) differentiate the absorption law at index r+1
      have habs := nbp_absorb s (r + 1)
      have hcast : (((r + 1 : ℕ) : ℚ)) = (r : ℚ) + 1 := by push_cast; ring
      rw [hcast] at habs
      have hd := congrArg derivative habs
      rw [derivative_mul, derivative_add, derivative_X, derivative_C, add_zero, one_mul,
        derivative_C_mul, ih, Finset.mul_sum] at hd
      -- (2) expand each term of the product
      have hterm : ∀ m ∈ range (r + 1),
          (X + C (s - ((r : ℚ) + 1))) * (C (cf m) * nbp s (r - m))
            = C (cf m * ((r : ℚ) - (m : ℚ) + 1)) * nbp s (r + 1 - m)
              - C ((-1 : ℚ) ^ m) * nbp s (r - m) := by
        intro m hm
        have hmr : m ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have hsub : (((r - m : ℕ) : ℚ)) = (r : ℚ) - (m : ℚ) := by
          rw [Nat.cast_sub hmr]
        have hidx : r + 1 - m = (r - m) + 1 := by omega
        have habs2 := nbp_absorb s (r - m)
        rw [hsub] at habs2
        rw [hidx, ← cf_mul_succ m]
        simp only [map_mul, map_add, map_sub, map_one] at habs2 ⊢
        linear_combination (C (cf m)) * habs2
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib] at hd
      -- (3) the two sides, both peeled at m = 0
      have hS1 : (∑ m ∈ range (r + 1), C (cf m * ((r : ℚ) - (m : ℚ) + 1)) * nbp s (r + 1 - m))
          = (∑ j ∈ range (r + 1),
              C (cf (j + 1) * ((r : ℚ) - ((j : ℚ) + 1) + 1)) * nbp s (r - j))
            + C ((r : ℚ) + 1) * nbp s (r + 1) := by
        have hext : (∑ m ∈ range (r + 1), C (cf m * ((r : ℚ) - (m : ℚ) + 1)) * nbp s (r + 1 - m))
            = ∑ m ∈ range (r + 1 + 1), C (cf m * ((r : ℚ) - (m : ℚ) + 1)) * nbp s (r + 1 - m) := by
          conv_rhs => rw [Finset.sum_range_succ]
          rw [show cf (r + 1) * ((r : ℚ) - ((r + 1 : ℕ) : ℚ) + 1) = 0 by push_cast; ring,
            map_zero, zero_mul, add_zero]
        rw [hext, Finset.sum_range_succ'
          (fun m => C (cf m * ((r : ℚ) - (m : ℚ) + 1)) * nbp s (r + 1 - m)) (r + 1)]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [show r + 1 - (j + 1) = r - j by omega,
            show (((j + 1 : ℕ) : ℚ)) = (j : ℚ) + 1 by push_cast; ring]
        · rw [Nat.sub_zero, Nat.cast_zero, cf_zero, one_mul, sub_zero]
      have hRHS : C ((r : ℚ) + 1 + 1) * (∑ m ∈ range (r + 1 + 1), C (cf m) * nbp s (r + 1 - m))
          = nbp s (r + 1)
            + ((∑ m ∈ range (r + 1), C (cf m * ((r : ℚ) - (m : ℚ) + 1)) * nbp s (r + 1 - m))
               - ∑ m ∈ range (r + 1), C ((-1 : ℚ) ^ m) * nbp s (r - m)) := by
        have hj : ∀ j ∈ range (r + 1),
            C ((r : ℚ) + 1 + 1) * (C (cf (j + 1)) * nbp s (r + 1 - (j + 1)))
              = C (cf (j + 1) * ((r : ℚ) - ((j : ℚ) + 1) + 1)) * nbp s (r - j)
                - C ((-1 : ℚ) ^ j) * nbp s (r - j) := by
          intro j _
          rw [show r + 1 - (j + 1) = r - j by omega, ← mul_assoc, ← map_mul, ← sub_mul,
            ← map_sub]
          congr 1
          have h2 : ((j : ℚ) + 1 + 1) ≠ 0 := by positivity
          simp only [cf]
          push_cast
          rw [pow_succ]
          field_simp
          ring
        have hC : C ((r : ℚ) + 1 + 1) = C ((r : ℚ) + 1) + 1 := by
          rw [← map_one (C : ℚ →+* Polynomial ℚ), ← map_add]
        rw [hS1, Finset.mul_sum, Finset.sum_range_succ'
          (fun m => C ((r : ℚ) + 1 + 1) * (C (cf m) * nbp s (r + 1 - m))) (r + 1),
          Finset.sum_congr rfl hj, Finset.sum_sub_distrib, Nat.sub_zero, cf_zero, map_one,
          one_mul, hC]
        ring
      rw [hd] at hRHS
      exact (mul_left_cancel₀ (Polynomial.C_ne_zero.mpr (by
        rw [show ((r : ℚ) + 1 + 1) = (r : ℚ) + 2 by ring]; exact hne)) hRHS).symm

/-! ## 4. The Bernoulli functional at the member's own cell -/

/-- `Lf n N p = Σ_{j < N} p.coeff j · momI (cell n) j` — `Member.pnPoly`'s own functional, with
the truncation length as a parameter.  `momI` here is `Zeta2Defs.momI`. -/
noncomputable def Lf (n N : ℕ) (p : Polynomial ℚ) : ℚ :=
  ∑ j ∈ range N, p.coeff j * momI (candidateM.cell n) j

theorem Lf_eq_umb_eval (n N : ℕ) (p : Polynomial ℚ) :
    Lf n N p = (umb N p).eval (((candidateM.cell n : ℤ) : ℚ) + 1) := by
  rw [Lf, umb, eval_finsetSum]
  exact Finset.sum_congr rfl fun j _ => by rw [eval_mul, eval_C]; rfl

theorem Lf_C_mul (n N : ℕ) (a : ℚ) (p : Polynomial ℚ) : Lf n N (C a * p) = a * Lf n N p := by
  simp only [Lf, Polynomial.coeff_C_mul, Finset.mul_sum, mul_assoc]

theorem Lf_sum {ι : Type*} (n N : ℕ) (s : Finset ι) (f : ι → Polynomial ℚ) :
    Lf n N (∑ i ∈ s, f i) = ∑ i ∈ s, Lf n N (f i) := by
  simp only [Lf, Polynomial.finsetSum_coeff, Finset.sum_mul]
  exact Finset.sum_comm

theorem cell_add_one (n : ℕ) : ((candidateM.cell n : ℤ) : ℚ) + 1 = ((-(4 * n : ℤ) : ℤ) : ℚ) := by
  have hb3 : candidateM.b3 = 4 := rfl
  rw [Member.cell, hb3]
  push_cast
  ring

/-- **THE ROW'S NEW CONTENT.**  The Bernoulli functional of the Newton basis, in closed form:
`L(C(t + 15n, r)) = Σ_{m ≤ r} (-1)^m/(m+1) · C(11n, r-m)`, ordinary binomial coefficients. -/
theorem Lf_nbp (n N r : ℕ) (h : r + 1 < N) :
    Lf n N (nbp ((15 * n : ℕ) : ℚ) r)
      = ∑ m ∈ range (r + 1), cf m * ((Nat.choose (11 * n) (r - m) : ℕ) : ℚ) := by
  rw [Lf_eq_umb_eval, umb_nbp N _ r h, deriv_nbp, eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_mul, eval_C, cell_add_one, nbp_eval_nat (15 * n) (r - m) (-(4 * n : ℤ)),
    show (-(4 * n : ℤ) + ((15 * n : ℕ) : ℤ)) = ((11 * n : ℕ) : ℤ) by push_cast; ring,
    Ring.choose_natCast]
  push_cast
  ring

/-- **`D (16n)` clears the functional**, because `den(L(nbp r)) ∣ lcm(1 … r+1)`. -/
theorem D_mul_Lf_nbp_int (n N r : ℕ) (h : r + 1 < N) (hr : r + 1 ≤ 16 * n) :
    ∃ z : ℤ, ((D (16 * n) : ℕ) : ℚ) * Lf n N (nbp ((15 * n : ℕ) : ℚ) r) = (z : ℚ) := by
  refine ⟨∑ m ∈ range (r + 1),
    (-1 : ℤ) ^ m * ((D (16 * n) / (m + 1) : ℕ) : ℤ) * ((Nat.choose (11 * n) (r - m) : ℕ) : ℤ), ?_⟩
  rw [Lf_nbp n N r h, Finset.mul_sum]
  -- NOT `push_cast`: it pushes the cast through `D (16n) / (m+1)` unconditionally
  -- (`Int.natCast_div`), which destroys the `((… : ℕ) : ℚ)` shape `Nat.cast_div` rewrites.
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : m + 1 ≤ 16 * n := by
    have := Finset.mem_range.mp hm
    omega
  have hdvd : (m + 1) ∣ D (16 * n) := dvd_D (by omega) hm1
  have hne : (((m + 1 : ℕ)) : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [Nat.cast_div hdvd hne, cf]
  rw [show (((m + 1 : ℕ)) : ℚ) = (m : ℚ) + 1 by push_cast; ring] at hne ⊢
  field_simp

/-! ## 5. The assembly -/

/-- The termwise invariant at `D (15n)` — the OTHER factor of `Δ 16 15 n`.  `D (13n) ∣ D (15n)`. -/
theorem termwise_at_D15 (n r : ℕ) : ∃ z : ℤ,
    ((D (15 * n) : ℕ) : ℤ) * hc n (11 * n + 1 + r)
      = (((11 * n + 1) * ((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℤ) * z := by
  obtain ⟨u, hu⟩ := D_dvd_D (show 13 * n ≤ 15 * n by omega)
  obtain ⟨v, hv⟩ := Zeta2NewtonCarry.termwise_invariant_member n r
  refine ⟨(u : ℤ) * v, ?_⟩
  have hu' : ((D (15 * n) : ℕ) : ℤ) = ((D (13 * n) : ℕ) : ℤ) * (u : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hu
  rw [hu', hc_def]
  linear_combination (u : ℤ) * hv

theorem Ppol_natDegree_le (n : ℕ) : (candidateM.Ppol n).natDegree ≤ 16 * n := by
  rw [candidate_Ppol_natDegree]
  omega

theorem pnPoly_eq_Lf (n : ℕ) : candidateM.pnPoly n = Lf n (16 * n + 1) (candidateM.Ppol n) := by
  rw [Member.pnPoly, Lf]
  refine Finset.sum_subset (fun x hx => ?_) ?_
  · simp only [Finset.mem_range] at hx ⊢
    have := Ppol_natDegree_le n
    omega
  · intro j _ hj
    have hj' : (candidateM.Ppol n).natDegree < j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj', zero_mul]

/-- `Π(n) · pnPoly n` in the Newton decomposition — the linear functional read term by term. -/
theorem Pin_mul_pnPoly_newton (n : ℕ) :
    candidateM.Pin n * candidateM.pnPoly n
      = ∑ r ∈ range (16 * n),
          (((hc n (11 * n + 1 + r) : ℤ) : ℚ)
              / (((11 * n + 1 : ℕ) : ℚ) * ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ)))
            * Lf n (16 * n + 1) (nbp ((15 * n : ℕ) : ℚ) r) := by
  have hPin : candidateM.Pin n
      = ((Zeta2PpolInt.PinNum n : ℕ) : ℚ) / ((Zeta2PpolInt.PinDen n : ℕ) : ℚ) := rfl
  have hden : ((Zeta2PpolInt.PinDen n : ℕ) : ℚ) ≠ 0 := Zeta2PpolInt.PinDen_ne_zero n
  have hnum : ((Zeta2PpolInt.PinNum n : ℕ) : ℚ) = ((Nat.factorial (11 * n) : ℕ) : ℚ) := rfl
  have hfn : ((Nat.factorial (11 * n) : ℕ) : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero _
  have hfacQ : ((Nat.factorial (11 * n + 1) : ℕ) : ℚ)
      = ((11 * n + 1 : ℕ) : ℚ) * ((Nat.factorial (11 * n) : ℕ) : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hL : ((11 * n + 1 : ℕ) : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  rw [pnPoly_eq_Lf, Ppol_eq_Qpoly, Qpoly, Lf_C_mul, Lf_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Lf_C_mul]
  have hcb : ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ) ≠ 0 := by
    have := Nat.choose_pos (show 11 * n + 1 ≤ 11 * n + 1 + r by omega)
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [hPin, hnum, hfacQ]
  field_simp

/-- **`Δ 16 15 n · Π(n) · pnPoly n ∈ ℤ`** — the VALUES → COEFFICIENTS step, closed.  The two
factors of `Δ` do two different jobs and neither alone suffices: `D (15n)` clears the Newton
coefficient, `D (16n)` clears the Bernoulli functional. -/
theorem Δ_mul_Pin_pnPoly_int (n : ℕ) :
    ∃ z : ℤ, ((Δ 16 15 n : ℕ) : ℚ) * (candidateM.Pin n * candidateM.pnPoly n) = (z : ℚ) := by
  classical
  choose v hv using fun r : ℕ => termwise_at_D15 n r
  have hwex : ∀ r : ℕ, ∃ z : ℤ, r < 16 * n →
      ((D (16 * n) : ℕ) : ℚ) * Lf n (16 * n + 1) (nbp ((15 * n : ℕ) : ℚ) r) = (z : ℚ) := by
    intro r
    by_cases hr : r < 16 * n
    · obtain ⟨z, hz⟩ := D_mul_Lf_nbp_int n (16 * n + 1) r (by omega) (by omega)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose w hw using hwex
  refine ⟨∑ r ∈ range (16 * n), v r * w r, ?_⟩
  rw [Pin_mul_pnPoly_newton, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrlt : r < 16 * n := Finset.mem_range.mp hr
  have hL : ((11 * n + 1 : ℕ) : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hcb : ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ) ≠ 0 := by
    have := Nat.choose_pos (show 11 * n + 1 ≤ 11 * n + 1 + r by omega)
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hvq : ((D (15 * n) : ℕ) : ℚ) * ((hc n (11 * n + 1 + r) : ℤ) : ℚ)
      = ((11 * n + 1 : ℕ) : ℚ) * ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ)
          * ((v r : ℤ) : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (hv r)
    push_cast at h ⊢
    linear_combination h
  have hwq := hw r hrlt
  have hsplit : ((D (16 * n) : ℕ) : ℚ) * ((D (15 * n) : ℕ) : ℚ)
        * (((hc n (11 * n + 1 + r) : ℤ) : ℚ)
            / (((11 * n + 1 : ℕ) : ℚ) * ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ))
          * Lf n (16 * n + 1) (nbp ((15 * n : ℕ) : ℚ) r))
      = (((D (16 * n) : ℕ) : ℚ) * Lf n (16 * n + 1) (nbp ((15 * n : ℕ) : ℚ) r))
        * ((((D (15 * n) : ℕ) : ℚ) * ((hc n (11 * n + 1 + r) : ℤ) : ℚ))
            / (((11 * n + 1 : ℕ) : ℚ)
              * ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ))) := by
    field_simp
  rw [Zeta2Arith.Δ, Nat.cast_mul, hsplit, hvq, hwq]
  field_simp

/-! ## 6. What the row still owes, stated so it can be discharged in one step -/

theorem sgn_candidate (n : ℕ) : candidateM.sgn n = -1 := by
  rw [candidate_sgn]
  exact Odd.neg_one_pow ⟨8 * n, by ring⟩

/-- **The row, from its harmonic half alone.**  Everything else is discharged above. -/
theorem pn_cleared_1615_of_harm
    (hharm : ∀ n : ℕ, ∃ z : ℤ,
      ((Δ 16 15 n : ℕ) : ℚ) * (candidateM.Pin n * candidateM.pnHarm n) = (z : ℚ)) :
    Zeta2PnCleared.PnClearedAt 16 15 := by
  classical
  choose a ha using fun n => Δ_mul_Pin_pnPoly_int n
  choose b hb using hharm
  refine ⟨fun n => a n - b n, fun n => ?_⟩
  rw [Member.pn, sgn_candidate]
  have h1 := ha n
  have h2 := hb n
  push_cast
  rw [← h1, ← h2]
  ring

/-- **And the harmonic half, from ONE divisibility with no sum in it.**  `D (k-4n-1)²` divides
the clearing factor times the term's own integer `cTerm n k`, at every `k` of the window.
Measured 16 863 / 16 863 termwise at `n ≤ 6` (`pn_harm_delta_probe.py` arm B2). -/
theorem harm_cleared_of_dvd (n : ℕ)
    (h : ∀ k ∈ candidateM.window n,
      (D (k - 4 * n - 1)) ^ 2 ∣ Δ 16 15 n * Zeta2Arith.cTerm n k) :
    ∃ z : ℤ, ((Δ 16 15 n : ℕ) : ℚ) * (candidateM.Pin n * candidateM.pnHarm n) = (z : ℚ) := by
  refine ⟨∑ k ∈ candidateM.window n,
    (-1 : ℤ) ^ (12 * n + k - 1)
      * (((Δ 16 15 n * Zeta2Arith.cTerm n k) / (D (k - 4 * n - 1)) ^ 2 : ℕ) : ℤ)
      * ((∑ i ∈ range (k - 4 * n - 1), (D (k - 4 * n - 1) / (i + 1)) ^ 2 : ℕ) : ℤ), ?_⟩
  rw [Member.pnHarm, Finset.mul_sum, Finset.mul_sum]
  -- NOT `push_cast`: the `D M / (i+1)` and `Δ·cTerm / (D M)²` quotients are EXACT ℕ divisions
  -- and `Int.natCast_div` would push the cast through them unconditionally.
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hD := Zeta2Arith.D_sq_mul_harm (k - 4 * n - 1) (k - 4 * n - 1) (le_refl _)
  have hct := Zeta2Arith.Pin_mul_ckAbs_eq_cTerm n k hk
  -- the quotient times the divisor, with no division left anywhere
  have hq' : ((((Δ 16 15 n * Zeta2Arith.cTerm n k) / (D (k - 4 * n - 1)) ^ 2 : ℕ)) : ℚ)
        * (((D (k - 4 * n - 1) : ℕ)) : ℚ) ^ 2
      = (((Δ 16 15 n : ℕ)) : ℚ) * ((Zeta2Arith.cTerm n k : ℕ) : ℚ) := by
    have hnat := Nat.div_mul_cancel (h k hk)
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) hnat
  rw [Zeta2Arith.candidate_ck, Zeta2Arith.candidate_harmIndex, ← hD]
  linear_combination
    (((Δ 16 15 n : ℕ) : ℚ) * (-1 : ℚ) ^ (12 * n + k - 1) * harm 2 (k - 4 * n - 1)) * hct
      - ((-1 : ℚ) ^ (12 * n + k - 1) * harm 2 (k - 4 * n - 1)) * hq'

end Zeta2PnFunc

#print axioms Zeta2PnFunc.nbp_absorb
#print axioms Zeta2PnFunc.nbp_pascal
#print axioms Zeta2PnFunc.nbp_comp_add_one
#print axioms Zeta2PnFunc.umb_shift
#print axioms Zeta2PnFunc.umb_nbp
#print axioms Zeta2PnFunc.deriv_nbp
#print axioms Zeta2PnFunc.Lf_nbp
#print axioms Zeta2PnFunc.D_mul_Lf_nbp_int
#print axioms Zeta2PnFunc.termwise_at_D15
#print axioms Zeta2PnFunc.pnPoly_eq_Lf
#print axioms Zeta2PnFunc.Pin_mul_pnPoly_newton
#print axioms Zeta2PnFunc.Δ_mul_Pin_pnPoly_int
#print axioms Zeta2PnFunc.sgn_candidate
#print axioms Zeta2PnFunc.pn_cleared_1615_of_harm
#print axioms Zeta2PnFunc.harm_cleared_of_dvd
