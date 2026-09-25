/-
# The arithmetic clearing, assembled — one hypothesis away from the chain's binders

With the constants PINNED by measurement (`pin_constants.py`, 2026-09-11: `D(13n)·D(16n)·pₙ ∈ ℤ`
at every `n ≤ 9`, `(13,16)` minimal, `16n` not `16n+1`), the chain's `Δ` is `Zeta2Arith.Δ 13 16`.
This file threads the three landed increments through the bridge at those constants:

  * `hΔne`  — `hΔne_of_Δ 13 16`, no hypothesis (increment 1 + 2);
  * `hQ`    — `hQ_of_qn_int qnInt qnInt_cast 13 16`, no hypothesis (increment 3 + 2);
  * `hP`    — `hP_of_cleared P 13 16 hP`, from the ONE open fact `pn_cleared`.

So `binders_of_pn_cleared` has exactly the SHAPE of `candidate_not_liouvilleWith`'s arithmetic
binders, given `∃ P, ∀ n, (P n : ℚ) = Δ 13 16 n * pₙ`.  That fact's proof is the scope audit's
residue-identity row (4b) — the whole-`pₙ` statement, NOT a termwise clearing: the measurement
shows the harmonic and polynomial halves' denominators cancel in the difference.

WHAT THIS `Δ` IS NOT (scope audit §2.1; zeta2-arith-layer.md §10.4 "WHAT `Δ 13 16` IS AND IS
NOT"): `D(13n)·D(16n)` is the NAIVE, Legendre-only clearing.  It makes the binders true, but its
growth rate is `e^{29n}`, so `C2 = 29` against `C0 = 29.108` and the chain would deliver
`μ ≈ 659`, not the headline `5.0495`.  The headline needs `Δ̃ₙ = D(16n)·D(15n)/Φ̃ₙ` — that is
`Δ 16 15 n / Φ̃ₙ`, rate `31`, `C2̃ = 31 − d_φ̃ = 15.019` — with the paired-max profile `Φ̃ₙ`
DIVIDING `Δ 16 15 n · qₙ` and `Δ 16 15 n · pₙ`.  NOT `Δ 13 16 n / Φ̃ₙ`, as this header said until
2026-09-11: `(13,16)` clears INTEGRALITY (`pin_constants.py`, still true) but is NOT a `Φ̃`-clearing
— `profile_check.out` measures 19 violations of `min(ord_p qₙ, ord_p(Δ 13 16 n · pₙ)) ≥ φ̃(n/p)`
above the Legendre line at `n ≤ 9`, every one a prime `p ∈ (13n, 15n]` on the `pₙ` side (the `qₙ`
side holds), and 0 violations at `Δ 16 15`.  The `Φ̃` layer is a further layer whose first Lean
object (`Φ̃ₙ` itself) does not exist yet.  This file is the floor that layer divides; its theorems
are about the naive clearing and are unaffected.

Increment 4b-shape of the arithmetic clearing.  ~seconds.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2ArithBridge

namespace Zeta2Arith

open Zeta2Defs

/-- **The one open fact of the arithmetic layer**, at the pinned constants. -/
def PnCleared : Prop :=
  ∃ P : ℕ → ℤ, ∀ n, (P n : ℚ) = ((Δ 13 16 n : ℕ) : ℚ) * candidateM.pn n

/-- **The chain's arithmetic binders, from `PnCleared` alone.**  `Q n = Δ 13 16 n · qnInt n`
is explicit; `P` is the witness of `PnCleared`. -/
theorem binders_of_pn_cleared (hp : PnCleared) :
    ∃ (Q P : ℕ → ℤ),
      (∀ n, ((Δ 13 16 n : ℕ) : ℝ) ≠ 0) ∧
      (∀ n, (Q n : ℝ) = ((Δ 13 16 n : ℕ) : ℝ) * ((candidateM.qn n : ℚ) : ℝ)) ∧
      (∀ n, (P n : ℝ) = ((Δ 13 16 n : ℕ) : ℝ) * ((candidateM.pn n : ℚ) : ℝ)) := by
  obtain ⟨P, hP⟩ := hp
  refine ⟨fun n => ((Δ 13 16 n : ℕ) : ℤ) * qnInt n, P, hΔne_of_Δ 13 16, fun n => ?_,
    hP_of_cleared P 13 16 hP⟩
  -- `hQ_of_qn_int`'s statement carries its casts at the leaves (`↑↑Δ * ↑(q n)`); the binder
  -- wants one cast of the integer product.  Same fact, moved across the cast.
  exact_mod_cast hQ_of_qn_int qnInt qnInt_cast 13 16 n

end Zeta2Arith

#print axioms Zeta2Arith.binders_of_pn_cleared
