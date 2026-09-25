/-
# ROW PAIR-8 — CLOSED: `pairing_q` and `pairing_p`, UNCONDITIONAL

`docs/future/zeta2-lean-chain.md` row PAIR-8.  Added 2026-09-18.

**HEADLINE: `Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.**  This file
closes row PAIR-8 and nothing else: the pairing `∀ n, hatQ n = qnInt n` and
`∀ n, hatP n = candidateM.pn n` — the hat member's coordinates ARE the chain's, at every `n`.
Its consumers PT-QB and PT-P are still open, and so is L1-ASM's arithmetic half.

**What this file adds: nothing but two applications.**  `Zeta2Pair8.pairing_q_of_chain_rec`
and `.pairing_p_of_chain_rec` (landed 2026-09-14, 53 receipts) proved the row's two statements
CONDITIONAL on exactly two hypotheses — L1-ASM's `hrecq_rat`/`hrecp_rat` — and, on the `p`
side, on the base `∀ n < N₀ + 3, hatP n = candidateM.pn n`, which PAIR-VAL closed cell by cell
and never assembled.  `Zeta2L1Asm.hrecq_rat`/`hrecp_rat` (this lineage's previous landing)
are those two hypotheses BYTE FOR BYTE at `N₀ = Zeta2L1Asm.N0 = 4`, so the `q` side is one
`exact`; the `p` side takes the seven cells `n = 0 … 6` from `Zeta2Hat.hatP_eq_pn_zero` and
`Zeta2PairP{1..6}.hatP_eq_pn` (receipted through `n = 10`, so the assembly is a lookup).

**`N₀` and the direction of the induction, checked rather than assumed.**  PAIR-8's induction
determines `d(n+3)` from `d n, d(n+1), d(n+2)` for every `n ≥ max 2 N₀`, so its base is
`n < N₀ + 3` — SMALLER at a smaller `N₀`, never larger.  The `q` side needs `N₀ ≤ 9`
(`Zeta2PairVal.hatQ_eq_qnInt_base`'s reach) and the `p` side needs the cells below `N₀ + 3`:
at `N₀ = 4` that is `n ≤ 6`, and `n = 7, 8` — which the cell's `N₀ = 6` would have needed —
are not consumed.  `pairing_q_at_six`/`pairing_p_at_six` record that the same theorems come
out of the conditional ones at the cell's `N₀ = 6` too, so the closing does not depend on
which of the two numbers a reader carries.

**Receipts on the UNCONDITIONAL theorems**, as the row asks: `#print axioms` on `pairing_q`
and `pairing_p` below, in PT-QB's and PT-P's exact types (`ℤ` and `ℚ` equations).

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2Pair8Close.lean

Receipts: `out_axioms_pair8close.txt`.  Falsifier: `falsify_pair8close.sh --lean`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Pair8
import Zeta2L1Asm
import Zeta2PairP1
import Zeta2PairP2
import Zeta2PairP3
import Zeta2PairP4
import Zeta2PairP5
import Zeta2PairP6

namespace Zeta2Pair8Close

open Zeta2Defs Zeta2Arith Zeta2Hat

/-- The `p` base below `N₀ + 3 = 7`, assembled from PAIR-VAL's per-cell modules. -/
theorem hatP_base : ∀ n, n < Zeta2L1Asm.N0 + 3 → hatP n = candidateM.pn n := by
  intro n hn
  have h7 : n < 7 := by simpa [Zeta2L1Asm.N0] using hn
  interval_cases n
  · exact Zeta2Hat.hatP_eq_pn_zero
  · exact Zeta2PairP1.hatP_eq_pn
  · exact Zeta2PairP2.hatP_eq_pn
  · exact Zeta2PairP3.hatP_eq_pn
  · exact Zeta2PairP4.hatP_eq_pn
  · exact Zeta2PairP5.hatP_eq_pn
  · exact Zeta2PairP6.hatP_eq_pn

/-- **ROW PAIR-8, the `q` coordinate — UNCONDITIONAL.**  `hatQ n = qnInt n` for every `n`, in
PT-QB's type (an equation in `ℤ`). -/
theorem pairing_q : ∀ n, hatQ n = qnInt n :=
  Zeta2Pair8.pairing_q_of_chain_rec Zeta2L1Asm.N0 (by decide) (by decide) Zeta2L1Asm.hrecq_rat

/-- **ROW PAIR-8, the `p` coordinate — UNCONDITIONAL.**  `hatP n = candidateM.pn n` for every
`n`, in PT-P's type (an equation in `ℚ`). -/
theorem pairing_p : ∀ n, hatP n = candidateM.pn n :=
  Zeta2Pair8.pairing_p_of_chain_rec Zeta2L1Asm.N0 (by decide) hatP_base Zeta2L1Asm.hrecp_rat

/-- `hatQ n = candidateM.qn n` over ℚ — the cast form PT-QB's consumers also read. -/
theorem pairing_q_cast (n : ℕ) : ((hatQ n : ℤ) : ℚ) = candidateM.qn n := by
  rw [pairing_q n, qnInt_cast]

/-! ## The cell's `N₀ = 6`, as a control: the same theorems from the conditional ones there -/

theorem hrecq_rat_six : ∀ n, 6 ≤ n →
    ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * candidateM.qn (n + j) = 0 :=
  fun n hn => Zeta2L1Asm.hrecq_rat n (by simp only [Zeta2L1Asm.N0]; omega)

theorem hrecp_rat_six : ∀ n, 6 ≤ n →
    ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * candidateM.pn (n + j) = 0 :=
  fun n hn => Zeta2L1Asm.hrecp_rat n (by simp only [Zeta2L1Asm.N0]; omega)

theorem pairing_q_at_six : ∀ n, hatQ n = qnInt n :=
  Zeta2Pair8.pairing_q_of_chain_rec 6 (by decide) (by decide) hrecq_rat_six

/-- At `N₀ = 6` the `p` base is `n < 9`; its cells above `6` are not needed by the row and
are taken from `pairing_p` itself here, which is the point: the base at 6 is IMPLIED by the
theorem at 4, never the other way round. -/
theorem pairing_p_at_six : ∀ n, hatP n = candidateM.pn n :=
  Zeta2Pair8.pairing_p_of_chain_rec 6 (by decide) (fun n _ => pairing_p n) hrecp_rat_six

end Zeta2Pair8Close

#print axioms Zeta2Pair8Close.hatP_base
#print axioms Zeta2Pair8Close.pairing_q
#print axioms Zeta2Pair8Close.pairing_p
#print axioms Zeta2Pair8Close.pairing_q_cast
#print axioms Zeta2Pair8Close.hrecq_rat_six
#print axioms Zeta2Pair8Close.hrecp_rat_six
#print axioms Zeta2Pair8Close.pairing_q_at_six
#print axioms Zeta2Pair8Close.pairing_p_at_six
