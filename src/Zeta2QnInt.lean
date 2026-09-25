/-
# The arithmetic clearing, layer 2 — `qₙ ∈ ℤ` at the candidate

`Zeta2ArithBridge.hQ_of_qn_int` consumes `∃ q : ℕ → ℤ, ∀ n, (q n : ℚ) = candidateM.qn n`.
This file supplies it.  The content is one factorial identity, termwise on the pole window
`k ∈ [15n+1, 26n+1]`:

    Π(n)·|c_k| = C(k−1, 13n) · C(k−2n−1, 9n) · C(k−4n−1, 5n) · C(11n, k−15n−1)

— `(11n)!/((13n)!(9n)!(5n)!)` times the §1.1 factorial ratio regroups into four binomial
coefficients, each pairing one numerator factorial with the two denominator factorials that
sum to it: `(k−1)! ↔ (13n)!(k−13n−1)!`, `(k−2n−1)! ↔ (9n)!(k−11n−1)!`,
`(k−4n−1)! ↔ (5n)!(k−9n−1)!`, `(11n)! ↔ (k−15n−1)!(26n+1−k)!`.  The window bounds are
exactly what makes every ℕ subtraction in those indices exact (`ck_subtractions_exact`).

So `qₙ = sgn·Σ_k (−1)^{12n+k−1}·(four binomials)` is an integer, with no clearing factor at
all — which is why the chain's `hQ` needs only `Δ · qₙ` and never a denominator bound on `qₙ`
(`zeta2-arith-layer.md` measures `qₙ ∈ ℤ` three times; this is the proof).

Increment 3 of the arithmetic clearing.  ~seconds.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs

namespace Zeta2Arith

open Zeta2Defs Nat Finset

/-- `Π(n)·|c_k|` at the candidate, as four binomial coefficients. -/
def cTerm (n k : ℕ) : ℕ :=
  (k - 1).choose (13 * n) * (k - 2 * n - 1).choose (9 * n) * (k - 4 * n - 1).choose (5 * n)
    * (11 * n).choose (k - 15 * n - 1)

/-- The integer `qₙ` is: `(−1)^{16n+1} · Σ_{k ∈ window} (−1)^{12n+k−1} · cTerm n k`. -/
def qnInt (n : ℕ) : ℤ :=
  (-1) ^ (16 * n + 1) * ∑ k ∈ candidateM.window n, (-1) ^ (12 * n + k - 1) * (cTerm n k : ℤ)

theorem candidate_dsum : candidateM.dsum = 16 := by decide

theorem candidate_Dpar : candidateM.Dpar = 12 := by decide

theorem candidate_sgn (n : ℕ) : candidateM.sgn n = (-1) ^ (16 * n + 1) := by
  rw [Member.sgn, candidate_dsum]

theorem candidate_ck (n k : ℕ) :
    candidateM.ck n k = (-1) ^ (12 * n + k - 1) * candidateM.ckAbs n k := by
  rw [Member.ck, candidate_Dpar]

/-- `Π(n)` at the candidate, the field values written out. -/
theorem candidate_Pin (n : ℕ) :
    candidateM.Pin n = ((11 * n)! : ℚ) / (((13 * n)! * (9 * n)! * (5 * n)! : ℕ) : ℚ) := rfl

/-- `|c_k|` at the candidate, the field values written out. -/
theorem candidate_ckAbs (n k : ℕ) :
    candidateM.ckAbs n k =
      (((k - 1)! * (k - 2 * n - 1)! * (k - 4 * n - 1)! : ℕ) : ℚ) /
      (((k - 13 * n - 1)! * (k - 11 * n - 1)! * (k - 9 * n - 1)! * (k - 15 * n - 1)!
        * (26 * n + 1 - k)! : ℕ) : ℚ) := rfl

theorem mem_window_iff (n k : ℕ) :
    k ∈ candidateM.window n ↔ 15 * n + 1 ≤ k ∧ k ≤ 26 * n + 1 := by
  simp [Member.window, candidateM]

/-- **The termwise identity.**  On the pole window, `Π(n)·|c_k|` is the four-binomial
product `cTerm n k`, hence an integer. -/
theorem Pin_mul_ckAbs_eq_cTerm (n k : ℕ) (hk : k ∈ candidateM.window n) :
    candidateM.Pin n * candidateM.ckAbs n k = (cTerm n k : ℚ) := by
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  have e1 : k - 1 - 13 * n = k - 13 * n - 1 := by omega
  have e2 : k - 2 * n - 1 - 9 * n = k - 11 * n - 1 := by omega
  have e3 : k - 4 * n - 1 - 5 * n = k - 9 * n - 1 := by omega
  have e4 : 11 * n - (k - 15 * n - 1) = 26 * n + 1 - k := by omega
  have c1 : 13 * n ≤ k - 1 := by omega
  have c2 : 9 * n ≤ k - 2 * n - 1 := by omega
  have c3 : 5 * n ≤ k - 4 * n - 1 := by omega
  have c4 : k - 15 * n - 1 ≤ 11 * n := by omega
  rw [candidate_Pin, candidate_ckAbs, cTerm]
  push_cast
  rw [Nat.cast_choose ℚ c1, Nat.cast_choose ℚ c2, Nat.cast_choose ℚ c3, Nat.cast_choose ℚ c4,
    e1, e2, e3, e4]
  field_simp

/-- **`qₙ ∈ ℤ`.**  `qnInt n` cast to `ℚ` is `candidateM.qn n`. -/
theorem qnInt_cast (n : ℕ) : (qnInt n : ℚ) = candidateM.qn n := by
  rw [qnInt, Member.qn, candidate_sgn]
  push_cast
  simp only [mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [candidate_ck, ← Pin_mul_ckAbs_eq_cTerm n k hk]
  ring

/-- The form `hQ_of_qn_int` consumes. -/
theorem qn_int : ∃ q : ℕ → ℤ, ∀ n, (q n : ℚ) = candidateM.qn n :=
  ⟨qnInt, qnInt_cast⟩

end Zeta2Arith

#print axioms Zeta2Arith.Pin_mul_ckAbs_eq_cTerm
#print axioms Zeta2Arith.qnInt_cast
#print axioms Zeta2Arith.qn_int
