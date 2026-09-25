/-
# Row PAIR-0p — the moment recursion, as a rewrite rule for `Zeta2Defs.momI`

`Zeta2Defs.momI M j = (Polynomial.bernoulli j).eval (M + 1)` is NONcomputable, so nothing in
the kernel evaluates it.  But `Polynomial.sum_bernoulli` — `Σ_{k ≤ j} C(j+1, k) • B_k = (j+1) X^j`
— evaluated at `x = M + 1` is a recursion that DOES compute, one value from the previous ones:

    momI M j = (M+1)^j − (1/(j+1)) · Σ_{k<j} C(j+1, k) · momI M k.

This is the four-line recursion of `zeta2-integral-free.md` §5.2 and of
`Zeta2Moments.momI_eq` (proved there in the other direction, recursion → Bernoulli); here it
is stated on `Zeta2Defs.momI` directly, so the generated `Zeta2PairP{n}.lean` can `rw` with it
and hand the arithmetic to `decide +kernel`.  Row PHI-EVAL's general-`n` instance will want
the same lemma.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs

namespace Zeta2MomStep

open Zeta2Defs Finset

/-- **The step**: `momI M j` from `momI M k`, `k < j`.  `Polynomial.sum_bernoulli j` at
`x = M + 1`, with the top term `C(j+1, j) = j+1` moved across. -/
theorem momI_step (M : ℤ) (j : ℕ) :
    momI M j = ((M : ℚ) + 1) ^ j
      - (1 / ((j : ℚ) + 1)) * ∑ k ∈ range j, ((j + 1).choose k : ℚ) * momI M k := by
  have h := congrArg (Polynomial.eval ((M : ℚ) + 1)) (Polynomial.sum_bernoulli j)
  rw [Polynomial.eval_finsetSum, Polynomial.eval_monomial] at h
  simp only [Polynomial.eval_smul, smul_eq_mul] at h
  rw [Finset.sum_range_succ, Nat.choose_succ_self_right] at h
  simp only [momI]
  have hne : ((j : ℚ) + 1) ≠ 0 := by positivity
  push_cast at h
  field_simp
  linarith

/-- The edge (`LEAN.md` §5): `j = 0` is the empty sum, `momI M 0 = 1`. -/
theorem momI_step_zero (M : ℤ) : momI M 0 = 1 := by
  rw [momI_step]; simp

/-- A control value: `momI (-1) 1 = B_1(0) = −1/2` (`Zeta2Moments.momI_control_one`). -/
theorem momI_control_one : momI (-1) 1 = -(1 / 2) := by
  rw [momI_step]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, momI_step_zero]
  norm_num

end Zeta2MomStep

#print axioms Zeta2MomStep.momI_step
#print axioms Zeta2MomStep.momI_step_zero
#print axioms Zeta2MomStep.momI_control_one
