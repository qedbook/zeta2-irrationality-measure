/-
# Row PT-P, layer 9 — the Newton coefficient `h_m` as an EXPLICIT alternating sum of the three
# binomial blocks: the object `CoeffBoundOpen`'s Kummer count is a count OF

`Zeta2PtpPoly` reduced the polynomial half to `CoeffBoundOpen`, a valuation bound on
`coeff n r = D(15n)·h_{L+r}/(L·C(L+r,L))`, and the probe (`ptp_poly_probe`) found the bound
TERMWISE in the signed-binomial expansion of `h_m = Δ^m H(0)` at 97 069 of 97 120 rows.  This
file writes that expansion in Lean:

    h_m = Σ_{i ≤ m} (−1)^{m−i} · C(m, i) · H(i)                                  (`hc_eq_signed_sum`)
    H(i) = (−1)^{27n} · C(26n−i, 13n) · C(24n−i, 9n) · C(22n−i, 5n)   for i ≤ 13n  (`Hfun_of_le`)
    H(i) = 0                                                        for 13n < i ≤ 26n  (`Hfun_eq_zero`)

so that for `m ≤ 26n` — every `r ≤ 15n − 1` — `h_m` is a signed sum of PRODUCTS OF FOUR ORDINARY
BINOMIALS over `i ≤ 13n`, each with one units-carry bit at a window prime.  `cTerm_{26n+1−i} =
C(11n, i)·|H(i)|` (`cTerm_eq_choose_mul_Habs`) is the identity that makes it the harmonic half's
own object with the fourth factor `C(11n, i)` replaced by `C(m, i)`.

WHAT IS NOT CLAIMED.  No valuation is bounded here; `CoeffBoundOpen` stays open, PT-P stays open,
`Zeta2Target.zeta2_not_liouvilleWith` is `sorry`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2NewtonCarry
import Zeta2NewtonAssemble

namespace Zeta2PtpCoeff

open Zeta2Defs Zeta2Arith Zeta2NewtonCarry Zeta2NewtonAssemble Finset

/-! ## 1. `Δ^m f(x)` as a signed binomial sum -/

/-- **The signed-binomial expansion of the forward difference.**
`Δ^m f(x) = Σ_{i ≤ m} (−1)^{m−i} C(m,i) f(x+i)`; `pascal_sum` is the induction step. -/
theorem fwdIter_eq_signed_sum (m : ℕ) (f : ℤ → ℤ) (x : ℤ) :
    fwdIter m f x
      = ∑ i ∈ range (m + 1), (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * f (x + i) := by
  induction m generalizing x with
  | zero => simp [fwdIter]
  | succ m ih =>
    rw [fwdIter_succ_apply, ih (x + 1), ih x]
    have hp := pascal_sum m (fun i => (-1 : ℤ) ^ (m + 1 - i) * f (x + i))
    have hR : ∑ i ∈ range (m + 1 + 1), (-1 : ℤ) ^ (m + 1 - i) * ((m + 1).choose i : ℤ) * f (x + i)
        = ∑ i ∈ range (m + 2), ((m + 1).choose i : ℤ) * ((-1 : ℤ) ^ (m + 1 - i) * f (x + i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hS2 : ∑ i ∈ range (m + 1), (m.choose i : ℤ) * ((-1 : ℤ) ^ (m + 1 - (i + 1)) * f (x + ↑(i + 1)))
        = ∑ i ∈ range (m + 1), (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * f (x + 1 + i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_add_right, show x + ((i + 1 : ℕ) : ℤ) = x + 1 + (i : ℤ) by push_cast; ring]
      ring
    have hS1 : ∑ i ∈ range (m + 1), (m.choose i : ℤ) * ((-1 : ℤ) ^ (m + 1 - i) * f (x + i))
        = -∑ i ∈ range (m + 1), (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * f (x + i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
      rw [show m + 1 - i = (m - i) + 1 by omega, pow_succ]
      ring
    rw [hR, hp, hS1, hS2]
    ring

/-- `h_m = Σ_{i ≤ m} (−1)^{m−i} C(m,i) H(i)` on the member's own `H`. -/
theorem hc_eq_signed_sum (n m : ℕ) :
    hc n m = ∑ i ∈ range (m + 1), (-1 : ℤ) ^ (m - i) * (m.choose i : ℤ) * Hfun n i := by
  rw [hc_def, fwdIter_eq_signed_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Hfun, zero_add]

/-! ## 2. `H(i)` in ordinary binomials -/

/-- `Ring.choose` at a NEGATIVE integer argument, in ordinary binomials:
`C(−a, k) = (−1)^k · C(a + k − 1, k)` for `a ≥ 1`. -/
theorem ringChoose_neg_natCast (a k : ℕ) (ha : 1 ≤ a) :
    Ring.choose (-(a : ℤ)) k = (-1 : ℤ) ^ k * ((a + k - 1).choose k : ℕ) := by
  rw [Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul]
  congr 1
  have h : (a : ℤ) + k - 1 = ((a + k - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [h, Ring.choose_natCast]

/-- **`H(i)` below the first block's zeros**: for `i ≤ 13n`,
`H(i) = (−1)^{27n} · C(26n−i, 13n) · C(24n−i, 9n) · C(22n−i, 5n)`. -/
theorem Hfun_of_le (n i : ℕ) (hi : i ≤ 13 * n) :
    Hfun n i = (-1 : ℤ) ^ (27 * n)
      * (((26 * n - i).choose (13 * n) * (24 * n - i).choose (9 * n)
          * (22 * n - i).choose (5 * n) : ℕ) : ℤ) := by
  rw [Hfun, listProd_memberBlocks]
  have e1 : (i : ℤ) - (13 * (n : ℤ) + 1) = -(((13 * n + 1 - i : ℕ)) : ℤ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : (i : ℤ) - (15 * (n : ℤ) + 1) = -(((15 * n + 1 - i : ℕ)) : ℤ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : (i : ℤ) - (17 * (n : ℤ) + 1) = -(((17 * n + 1 - i : ℕ)) : ℤ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e1, e2, e3, ringChoose_neg_natCast _ _ (by omega), ringChoose_neg_natCast _ _ (by omega),
    ringChoose_neg_natCast _ _ (by omega),
    show 13 * n + 1 - i + 13 * n - 1 = 26 * n - i by omega,
    show 15 * n + 1 - i + 9 * n - 1 = 24 * n - i by omega,
    show 17 * n + 1 - i + 5 * n - 1 = 22 * n - i by omega,
    show 27 * n = 13 * n + 9 * n + 5 * n by ring, pow_add, pow_add]
  push_cast
  ring

/-- **`H(i) = 0` on `13n < i ≤ 26n`**: the first block `C(i − 13n − 1, 13n)` has a natural upper
argument below `13n`. -/
theorem Hfun_eq_zero (n i : ℕ) (h1 : 13 * n < i) (h2 : i ≤ 26 * n) : Hfun n i = 0 := by
  rw [Hfun, listProd_memberBlocks]
  have e : (i : ℤ) - (13 * (n : ℤ) + 1) = (((i - 13 * n - 1 : ℕ)) : ℤ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [e, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-! ## 3. The identity that makes `h_m` the harmonic half's object -/

/-- `cTerm_{26n+1−i} = C(11n, i) · |H(i)|` for `i ≤ 11n` — the fourth factor of `cTerm` is the
`C(11n, i)` that `h_m` replaces by `C(m, i)`. -/
theorem cTerm_eq_choose_mul_Habs (n i : ℕ) (hi : i ≤ 11 * n) :
    (cTerm n (26 * n + 1 - i) : ℤ)
      = ((11 * n).choose i : ℕ) * ((-1 : ℤ) ^ (27 * n) * Hfun n i) := by
  rw [Hfun_of_le n i (by omega), cTerm,
    show 26 * n + 1 - i - 1 = 26 * n - i by omega,
    show 26 * n + 1 - i - 2 * n - 1 = 24 * n - i by omega,
    show 26 * n + 1 - i - 4 * n - 1 = 22 * n - i by omega,
    show 26 * n + 1 - i - 15 * n - 1 = 11 * n - i by omega,
    Nat.choose_symm hi]
  have hsq : ((-1 : ℤ) ^ (27 * n)) * ((-1 : ℤ) ^ (27 * n)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  push_cast
  linear_combination (-1 : ℤ) * (((11 * n).choose i : ℤ) * (((26 * n - i).choose (13 * n) : ℤ)
    * ((24 * n - i).choose (9 * n) : ℤ) * ((22 * n - i).choose (5 * n) : ℤ))) * hsq

#print axioms Zeta2PtpCoeff.fwdIter_eq_signed_sum
#check @Zeta2PtpCoeff.fwdIter_eq_signed_sum
#print axioms Zeta2PtpCoeff.hc_eq_signed_sum
#check @Zeta2PtpCoeff.hc_eq_signed_sum
#print axioms Zeta2PtpCoeff.ringChoose_neg_natCast
#check @Zeta2PtpCoeff.ringChoose_neg_natCast
#print axioms Zeta2PtpCoeff.Hfun_of_le
#check @Zeta2PtpCoeff.Hfun_of_le
#print axioms Zeta2PtpCoeff.Hfun_eq_zero
#check @Zeta2PtpCoeff.Hfun_eq_zero
#print axioms Zeta2PtpCoeff.cTerm_eq_choose_mul_Habs
#check @Zeta2PtpCoeff.cTerm_eq_choose_mul_Habs

end Zeta2PtpCoeff
