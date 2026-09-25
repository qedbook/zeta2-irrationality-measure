/-
# The arithmetic clearing, layer 3 — the HARMONIC half of `pₙ` clears by `D(22n)²`

`pₙ = −sgn·Π·(pnPoly − pnHarm)` with `pnHarm = Σ_{k∈window} c_k · H⁽²⁾_{k−4n−1}`.  This file
proves the harmonic half's clearing:

    D(22n)² · Π(n) · pnHarm n  ∈ ℤ,

by two facts that compose:  `D M² · H⁽²⁾_m ∈ ℤ` whenever `m ≤ M` (every `1/(i+1)²` with
`i+1 ≤ M` is `(D M/(i+1))²/D M²`, and `i+1 ∣ D M` is `dvd_D`), and `Π(n)·c_k` is the signed
integer `±cTerm n k` (`Zeta2QnInt`).  The harmonic index `k−4n−1` is at most `22n` on the
window, which is where `22` comes from.

Increment 4a of the arithmetic clearing.  The polynomial half (`Π·Σ_j P_j I_j(C)`) is 4b.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt

namespace Zeta2Arith

open Zeta2Defs Nat Finset

/-- **`D M² · H⁽²⁾_m` is an integer for `m ≤ M`** — written as the sum of the squares of the
exact quotients `D M / (i+1)`. -/
theorem D_sq_mul_harm (m M : ℕ) (h : m ≤ M) :
    ((D M : ℕ) : ℚ) ^ 2 * harm 2 m = ((∑ i ∈ range m, (D M / (i + 1)) ^ 2 : ℕ) : ℚ) := by
  rw [harm, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hdvd : i + 1 ∣ D M := dvd_D (Nat.succ_pos i) (le_trans (Finset.mem_range.1 hi) h)
  rw [Nat.cast_div hdvd (by positivity)]
  push_cast
  rw [div_pow]
  ring

theorem candidate_harmIndex (n k : ℕ) : candidateM.harmIndex n k = k - 4 * n - 1 := rfl

/-- The integer `D(22n)² · Π(n) · pnHarm n` is. -/
def harmInt (n : ℕ) : ℤ :=
  ∑ k ∈ candidateM.window n, (-1) ^ (12 * n + k - 1) * (cTerm n k : ℤ)
    * ((∑ i ∈ range (k - 4 * n - 1), (D (22 * n) / (i + 1)) ^ 2 : ℕ) : ℤ)

/-- **The harmonic half clears.**  `harmInt n` cast to `ℚ` is `D(22n)² · Π(n) · pnHarm n`. -/
theorem harmInt_cast (n : ℕ) :
    (harmInt n : ℚ) = ((D (22 * n) : ℕ) : ℚ) ^ 2 * (candidateM.Pin n * candidateM.pnHarm n) := by
  rw [harmInt, Member.pnHarm, Finset.mul_sum, Finset.mul_sum]
  -- NOT `push_cast`: on the ℤ side it pushes the cast through `D M / (i+1)` unconditionally
  -- (`Int.natCast_div`), which destroys the `((Σ … : ℕ) : ℚ)` shape `D_sq_mul_harm` rewrites.
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  have hm : k - 4 * n - 1 ≤ 22 * n := by omega
  rw [candidate_ck, candidate_harmIndex, ← D_sq_mul_harm _ _ hm, ← Pin_mul_ckAbs_eq_cTerm n k hk]
  ring

end Zeta2Arith

#print axioms Zeta2Arith.D_sq_mul_harm
#print axioms Zeta2Arith.harmInt_cast
