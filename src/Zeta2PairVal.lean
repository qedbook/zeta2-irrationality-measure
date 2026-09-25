/-
# Row PAIR-VAL — the Q-HALF of the induction base, `hatQ n = qnInt n` for every `n < 12`

Row PAIR-VAL of `docs/future/zeta2-lean-chain.md`.  The pairing `∀ n, hatQ n = qnInt n` (row
PAIR) is delivered as a recurrence plus a base, and the base has to reach `N₀ + 3` where
`N₀ = max(N₀_tale1, N₀_hat)` is the first `n` from which BOTH recurrences are proved — today
`max(9, 2) = 9`, so **`n < 12`**.

This file is the Q half.  It needs no generated data at all: `hatQ n` and `qnInt n` are both
explicit finite sums over factorials and binomials, so each instance is an IDENTITY the kernel
decides — there is no literal anywhere in this file, and therefore nothing to cross-check
(`LEAN.md` §6 applies to hand-entered data; there is none here).  `Nat.choose` is rewritten to
`descFactorial / factorial` first, because the kernel's Pascal recursion for `Nat.choose` is
exponential (the PAIR-0 pattern).

`n = 0, 1, 2` are already `Zeta2Hat.hatQ_eq_qnInt_{zero,one,two}` and are reused, not restated.

**The P half is NOT here and is not claimed.**  `hatP n = candidateM.pn n` is
`Zeta2PairP{1,2,3}.hatP_eq_pn` at `n = 1, 2, 3` and `Zeta2Hat.hatP_eq_pn_zero` at `n = 0`;
`4 ≤ n ≤ 11` is OPEN, and each one needs a generated `Zeta2PairP{n}.lean` (the quotient/
remainder witnesses and the engine's `hatP` pin).  Row PAIR-VAL's status cell carries the count.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Hat

-- The wall law is part of the row's record (LEAN.md §0a column 3): every declaration slower
-- than 100 ms prints its elaboration / kernel time into the archived log.  PAIR-0 measured
-- `hatQ n = qnInt n` at 58 / 349 / 595 / 1150 / 1800 / 2730 ms for n = 1..6, i.e. ≈ n^2.2.
set_option profiler true
set_option profiler.threshold 100

namespace Zeta2PairVal

open Zeta2Defs Zeta2Arith Zeta2Hat Nat Finset

theorem hatQ_eq_qnInt_three : hatQ 3 = qnInt 3 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem hatQ_eq_qnInt_four : hatQ 4 = qnInt 4 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem hatQ_eq_qnInt_five : hatQ 5 = qnInt 5 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem hatQ_eq_qnInt_six : hatQ 6 = qnInt 6 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem hatQ_eq_qnInt_seven : hatQ 7 = qnInt 7 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem hatQ_eq_qnInt_eight : hatQ 8 = qnInt 8 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem hatQ_eq_qnInt_nine : hatQ 9 = qnInt 9 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem hatQ_eq_qnInt_ten : hatQ 10 = qnInt 10 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem hatQ_eq_qnInt_eleven : hatQ 11 = qnInt 11 := by
  simp only [hatQ, hatA, qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- **The Q half of row PAIR-VAL's base**: `hatQ n = qnInt n` at every `n < 12`, i.e. at every
cell the induction on the two recurrences will need before `N₀ = 9` takes over. -/
theorem hatQ_eq_qnInt_base : ∀ n < 12, hatQ n = qnInt n := by
  intro n hn
  interval_cases n
  · exact hatQ_eq_qnInt_zero
  · exact hatQ_eq_qnInt_one
  · exact hatQ_eq_qnInt_two
  · exact hatQ_eq_qnInt_three
  · exact hatQ_eq_qnInt_four
  · exact hatQ_eq_qnInt_five
  · exact hatQ_eq_qnInt_six
  · exact hatQ_eq_qnInt_seven
  · exact hatQ_eq_qnInt_eight
  · exact hatQ_eq_qnInt_nine
  · exact hatQ_eq_qnInt_ten
  · exact hatQ_eq_qnInt_eleven

/-- The same at the chain's own object `candidateM.qn` — the shape row PT-QB consumes. -/
theorem hatQ_cast_eq_qn_base : ∀ n < 12, (hatQ n : ℚ) = candidateM.qn n := by
  intro n hn
  rw [hatQ_eq_qnInt_base n hn, qnInt_cast]

end Zeta2PairVal

#print axioms Zeta2PairVal.hatQ_eq_qnInt_three
#print axioms Zeta2PairVal.hatQ_eq_qnInt_four
#print axioms Zeta2PairVal.hatQ_eq_qnInt_five
#print axioms Zeta2PairVal.hatQ_eq_qnInt_six
#print axioms Zeta2PairVal.hatQ_eq_qnInt_seven
#print axioms Zeta2PairVal.hatQ_eq_qnInt_eight
#print axioms Zeta2PairVal.hatQ_eq_qnInt_nine
#print axioms Zeta2PairVal.hatQ_eq_qnInt_ten
#print axioms Zeta2PairVal.hatQ_eq_qnInt_eleven
#print axioms Zeta2PairVal.hatQ_eq_qnInt_base
#print axioms Zeta2PairVal.hatQ_cast_eq_qn_base
