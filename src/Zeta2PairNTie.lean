/-
# ROW PAIR-N, the IDENTIFICATION half — `L ≠ 0` restated at PAIR-8's own object

`docs/future/zeta2-lean-chain.md` row PAIR-N.  `Zeta2PairN.L_ne_zero` is a statement about
`StarForallCandt2.polB StarForallCandt2.al3`.  What PAIR-8's strong induction actually divides
by is `Zeta2Pair6.betaHat n 3`, and §6a's lesson in this corpus — *"a `c3_ne_zero` about
`hornerZ c3` discharges nothing about a coords-derived `α₃` until STAR-ID (ii) identifies
them"* — is that the step between those two sentences is never free until Lean has taken it.

This file takes it, and it takes it BY `show`, i.e. by definitional unfolding, so a green here
is the assertion that the two objects are the same term and not merely equal ones:

    alN_three_ne_zero     : Zeta2Pair6.alN n 3 ≠ 0
    betaHat_three_ne_zero : Zeta2Pair6.betaHat n 3 ≠ 0

The second is the whole of PAIR-8's leading-coefficient obligation in the `β̂` operator:
`betaHat n j = alN n j * (Π̂ n / Π̂ (n+j))`, and `Π̂ ≠ 0` is PAIR-6's own `hatPi_ne`.  Nothing
else PAIR-8 needs is here — not the recurrence, not `λden ≠ 0`, not `L_t1 ≠ 0`.

It is a SEPARATE module on purpose: row PAIR-N's own receipt (`Zeta2PairN.lean`) imports the
generated base and nothing else, so it costs seconds and cannot go red for a reason that lives
in the 22-module PAIR-6 chain this file has to build.

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2PairNTie.lean

Receipts: `out_axioms_pairntie.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Pair6
import Zeta2PairN

namespace Zeta2PairNTie

/-- **The `j = 3` entry of PAIR-6's operator is PAIR-N's polynomial**, definitionally: `alN n j`
is `(polB (match j with | 0 => al0 | 1 => al1 | 2 => al2 | _ => al3)).eval (n : ℚ)`, and the
`show` below is what checks that the match really does land on `al3` at `j = 3`. -/
theorem alN_three_ne_zero (n : ℕ) : Zeta2Pair6.alN n 3 ≠ 0 := by
  show (StarForallCandt2.polB StarForallCandt2.al3).eval (n : ℚ) ≠ 0
  exact Zeta2PairN.L_ne_zero n

/-- **PAIR-8's division, discharged.**  `betaHat n 3 ≠ 0` for every `n`, so the strong induction
may solve its recurrence for `d (n+3)`.  The `Π̂` half is PAIR-6's own `hatPi_ne`. -/
theorem betaHat_three_ne_zero (n : ℕ) : Zeta2Pair6.betaHat n 3 ≠ 0 := by
  show Zeta2Pair6.alN n 3 * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + 3)) ≠ 0
  exact mul_ne_zero (alN_three_ne_zero n)
    (div_ne_zero (Zeta2Pair6.hatPi_ne n) (Zeta2Pair6.hatPi_ne (n + 3)))

/-! ## Receipts (LEAN.md section 1 -- exit 0 is not an attestation) -/

#print axioms alN_three_ne_zero
#print axioms betaHat_three_ne_zero

end Zeta2PairNTie
