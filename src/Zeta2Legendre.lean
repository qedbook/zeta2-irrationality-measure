/-
# The Φ̃ layer's atom — `ord_p` of a binomial above the Legendre validity line is a CARRY BIT

The profile `φ̃({n/p})` that turns `μ ≈ 659` into `μ ≤ 5.0495` (scope audit §2.1) is, for every
prime `p` with `p² > γ₀n`, a statement about `ord_p` of the four binomials in `cTerm n k`,
minimised over the window.  Above that line Legendre's formula has ONE term, and Kummer's theorem
(`padicValNat_choose'` in Mathlib) says `ord_p C(a+b, b) = #{carries} ∈ {0, 1}` with the single
carry `p ≤ a mod p + b mod p`.  This file states that atom, and then `ord_p (cTerm n k)` as the
sum of its four carry bits — the object the profile's ∀n argument will minimise over `k`.

Fail-fast increment Φ̃-1 (owner 2026-09-11: riskiest first; fail sooner).  ~seconds.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2QnInt
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Zeta2Arith

open Zeta2Defs Nat

/-- **The carry bit.**  For `a + b < p²`, `ord_p C(a+b, b) = [p ≤ b mod p + a mod p]`. -/
theorem padicValNat_choose_carry (p a b : ℕ) [hp : Fact p.Prime] (h : a + b < p ^ 2) :
    padicValNat p ((a + b).choose b) = if p ≤ b % p + a % p then 1 else 0 := by
  have hlog : Nat.log p (a + b) < 2 := by
    rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
    · rw [h0, Nat.log_zero_right]
      norm_num
    · exact Nat.log_lt_of_lt_pow h0.ne' h
  rw [padicValNat_choose' hlog, show Finset.Ico 1 2 = {1} from Nat.Ico_succ_singleton 1,
    Finset.filter_singleton]
  simp only [pow_one]
  split_ifs <;> simp

/-- **`ord_p (cTerm n k)` above the Legendre line is the sum of four carry bits.**  The window
bounds make every index a genuine sum (`k − 1 = (k − 13n − 1) + 13n`, …), and `26n + 1 < p²`
puts all four binomials below `p²`. -/
theorem padicValNat_cTerm (p n k : ℕ) [hp : Fact p.Prime] (hk : k ∈ candidateM.window n)
    (hp2 : 26 * n + 1 < p ^ 2) :
    padicValNat p (cTerm n k) =
      (if p ≤ (13 * n) % p + (k - 13 * n - 1) % p then 1 else 0)
      + (if p ≤ (9 * n) % p + (k - 11 * n - 1) % p then 1 else 0)
      + (if p ≤ (5 * n) % p + (k - 9 * n - 1) % p then 1 else 0)
      + (if p ≤ (k - 15 * n - 1) % p + (26 * n + 1 - k) % p then 1 else 0) := by
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  have f1 : (k - 1).choose (13 * n) = ((k - 13 * n - 1) + 13 * n).choose (13 * n) := by
    congr 1; omega
  have f2 : (k - 2 * n - 1).choose (9 * n) = ((k - 11 * n - 1) + 9 * n).choose (9 * n) := by
    congr 1; omega
  have f3 : (k - 4 * n - 1).choose (5 * n) = ((k - 9 * n - 1) + 5 * n).choose (5 * n) := by
    congr 1; omega
  have f4 : (11 * n).choose (k - 15 * n - 1)
      = ((26 * n + 1 - k) + (k - 15 * n - 1)).choose (k - 15 * n - 1) := by
    congr 1; omega
  have c1 : (k - 13 * n - 1) + 13 * n < p ^ 2 := by omega
  have c2 : (k - 11 * n - 1) + 9 * n < p ^ 2 := by omega
  have c3 : (k - 9 * n - 1) + 5 * n < p ^ 2 := by omega
  have c4 : (26 * n + 1 - k) + (k - 15 * n - 1) < p ^ 2 := by omega
  have n1 : (k - 1).choose (13 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n2 : (k - 2 * n - 1).choose (9 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n3 : (k - 4 * n - 1).choose (5 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n4 : (11 * n).choose (k - 15 * n - 1) ≠ 0 := Nat.choose_ne_zero (by omega)
  rw [cTerm, padicValNat.mul (mul_ne_zero (mul_ne_zero n1 n2) n3) n4,
    padicValNat.mul (mul_ne_zero n1 n2) n3, padicValNat.mul n1 n2]
  rw [f1, f2, f3, f4, padicValNat_choose_carry p _ _ c1, padicValNat_choose_carry p _ _ c2,
    padicValNat_choose_carry p _ _ c3, padicValNat_choose_carry p _ _ c4]

end Zeta2Arith

#print axioms Zeta2Arith.padicValNat_choose_carry
#print axioms Zeta2Arith.padicValNat_cTerm
