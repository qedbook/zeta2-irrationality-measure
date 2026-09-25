/-
# THE HEADLINE STATEMENT — **PROVED, 2026-09-24, with no binder and no `sorry`**

`docs/future/zeta2-integral-free.md` §5.1 writes the target of the whole μ(ζ(2)) formalization.
This file is where that target was first typed into Lean. It fixed the vocabulary
(`LiouvilleWith`, not a hand-rolled measure) and the constant, before any of it was proved:
**until 2026-09-24 this file carried a DELIBERATE `sorry`** on
`zeta2_not_liouvilleWith`, and its receipts printed `sorryAx` on purpose, as the one honest
place the open target was displayed.

**2026-09-24 — the `sorry` is gone (owner directive: "remove all sorrys so it's a complete
proof").**  `zeta2_not_liouvilleWith` is now `Zeta2Unconditional.zeta2_not_liouvilleWith`:
the chain's composition (`Zeta2Final`, every row landed with receipts) applied to
`Zeta2Hpsi.hψ`, which proves the chain's one standing hypothesis `Zeta2LegA.psiErrorBoundStatement`
from PNT+'s `MediumPNT`, vendored and elaborated in this same kernel
(`external_tests/pnt_port/`, see its PROVENANCE.md).  So the statement below is PROVED, it takes
NO hypothesis, and its receipt prints `[propext, Classical.choice, Quot.sound]` BESIDE a
`#check @` type that names no binder (LEAN.md §1: a binder is not an axiom, so the type is the
other half of the acceptance).

**Why the constant is `5.0495243`.**  It is strictly above the certified
`1 + v/(u−δ) = 5.049524290530377` and strictly below the record's certified `5.095411785826`,
so the statement is the candidate's improvement and not the record's.  It is NOT `5.04952429`,
which is the sweep's score and strictly stronger than the certified value
(`Zeta2TWire.certified_value_is_strictly_between_the_two_literals`).

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox, in a
store rebuilt from committed sources (`external_tests/zeta2_arith/clean_close/`); receipts
`out_axioms_target.txt`, whole-closure census `out_sorry_census.txt`.
-/
import Zeta2Unconditional
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

namespace Zeta2Target

open Zeta2Defs

/-- **THE TARGET, PROVED.**  `¬ LiouvilleWith 5.0495243 ζ(2)`: the irrationality measure of
`ζ(2)` is at most `5.0495243`.  No hypothesis. -/
theorem zeta2_not_liouvilleWith : ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2Unconditional.zeta2_not_liouvilleWith

/-- The headline as an irrationality-measure bound, by `LiouvilleWith.mono`.

It is here because §5.1's remark that the target is a SINGLE statement rather than a `∀ p` is
the kind of claim that should be checked rather than believed: it is checked, and it holds. -/
theorem zeta2_irrationality_measure_le :
    ∀ p : ℝ, (5.0495243 : ℝ) ≤ p → ¬ LiouvilleWith p zeta2 := by
  intro p hp h
  exact zeta2_not_liouvilleWith (h.mono hp)

/-! ## Receipts — BOTH channels: the axioms AND the printed type, which must name no binder -/

#print axioms zeta2_not_liouvilleWith
#check @zeta2_not_liouvilleWith
#print axioms zeta2_irrationality_measure_le
#check @zeta2_irrationality_measure_le

end Zeta2Target
