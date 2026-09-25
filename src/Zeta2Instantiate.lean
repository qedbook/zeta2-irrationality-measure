/-
# X-L1, first half — a landed abstract theorem APPLIED to the real linear form

Every receipted theorem in the μ(ζ(2)) chain so far is about an abstract object:
`Zeta2StarB1.poincare_upper_bound` takes an arbitrary `y : ℕ → ℝ`, `star_growth_bound_eventual`
an arbitrary sequence with arbitrary clearing data.  `Zeta2Defs.Member.rn` is the first object
in the corpus that IS the ζ(2) candidate, so this file does the obvious next thing: it hands
`rn` to the capstone and reads what comes out.

**What this buys, and what it does not.**  It buys the composition, executed rather than
asserted — `LEAN.md` §3 is emphatic that "proving pieces with the others as hypotheses" fails
on casts and indexing exactly when nobody runs the glue, and it failed both times it was tried
in this program.  Here it goes through unchanged, which means D1's statement really does fit
the real object and no re-statement is needed.

It does NOT buy L1.  The hypothesis `hL` — that `rn` satisfies the three-term recurrence — is
row B1 + B2 + B3 + B4 of `zeta2-integral-free.md` §5.3, and none of them is proved for `rn`.
That is the honest position of this row: the interface is fitted, the input is named, and the
input is the work.

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox.
-/
import Zeta2Defs
import Zeta2StarB1

namespace Zeta2Instantiate

open Zeta2Defs Polynomial

/-- **The capstone, at the real linear form.**  `Zeta2StarB1.star_growth_bound_eventual` with
`y := Member.rn m`, and nothing else changed: every hypothesis is discharged by the caller in
the vocabulary B1 produces.

**CORRECTED 2026-09-09: the conclusion is a GROWTH bound, not "a decay bound on `r_n` itself"
as this docstring said.**  The shape is `|r n| ≤ C·ρⁿ` for whatever `ρ` the caller supplies,
and at D1's own certified constants `ρ ≈ 1.7987e18` — committed as `Zeta2XL1.one_lt_rhoChar`.
Decay is what the CHAIN needs of `r_n`, and it is L7's job; this theorem is the L5/Poincaré
half and bounds growth from above.  Calling it decay reads as though the chain's hard analytic
step were already discharged here, which is the most expensive way a docstring can be wrong.

The one hypothesis that is NOT available today is `hL`, L1 for `rn`.  It is stated here in the
exact shape B1's `star_telescopes` + the shift lemma will deliver it (`α_j` as `ℕ → ℝ`
coefficients, `B` the clearing polynomial), so that closing B1 discharges it verbatim rather
than after a re-statement.

**CORRECTED 2026-09-09: "closing B1 discharges it verbatim" is HALF true, and the false half is
the conclusion.**  `Zeta2XL1B.lean` §3 tested this sentence instead of repeating it, and split
it into two theorems.  *True — the SHAPE.*  `hL` takes `α_j : ℕ → ℝ` alongside a clearing
polynomial `B`, exactly the vocabulary the solve produces; `Zeta2XL1B.star_telescopes_four` is
`star_telescopes` instantiated at `K := ℝ`, `m := 4` with no restatement, and `h₀`–`h₃` are
discharged at the real `candidateM.rn` there.  *False — the CONCLUSION.*  `star_telescopes`
ends at `Σ_j α_j · ρ_j t = S (t+1) − S t`; `hL` needs `= 0`, at the SEQUENCE `r_{n+j}` rather
than at a contour variable `t`.  Closing that needs a linear functional `Φ` with `Φ ρ_j =
r_{n+j}`, and **`Φ` does not exist in Lean at all**.  Nor does the "shift lemma" named two
sentences above.  `Zeta2XL1B` §3 measured this by census — *"`rn (n + 1)` occurs in exactly
three places across every `.lean` file in `external_tests/`, and all three are this same
hypothesis statement"* — and ⟦re-measured 2026-09-09 by the 2B0.U staleness sweep, that COUNT
is already stale: there are now SEVEN statement sites (`Zeta2Instantiate` ×2, `Zeta2XL1` ×1,
`Zeta2XL1B` ×4, the last four added by `Zeta2XL1B` itself in the same landing that wrote the
sentence).  **The substantive claim survives the re-count and that is the point: all seven are
still the same hypothesis, so no theorem anywhere relates the linear form at consecutive
indices.**  A census is a measurement with a date; quote its finding, not its integer.⟧
`Zeta2XL1B.rec_of_telescoping_of_linear` states the missing step as one theorem, so the
remaining work is "supply `Φ`, its linearity and `hbdy`" rather than "connect two theorems
somehow".  The sentence is corrected rather than deleted because it is what made the interface
fit; only its last clause over-reached. -/
theorem rn_growth_of_L1 (m : Member)
    (α₀ α₁ α₂ α₃ : ℕ → ℝ) (P₀ P₁ P₂ P₃ B : ℝ[X]) (N₀ : ℕ)
    (hL : ∀ n : ℕ, N₀ ≤ n →
      α₀ n * m.rn n + α₁ n * m.rn (n + 1) + α₂ n * m.rn (n + 2) + α₃ n * m.rn (n + 3) = 0)
    (h₀ : ∀ n : ℕ, N₀ ≤ n → P₀.eval (n : ℝ) = B.eval (n : ℝ) * α₀ n)
    (h₁ : ∀ n : ℕ, N₀ ≤ n → P₁.eval (n : ℝ) = B.eval (n : ℝ) * α₁ n)
    (h₂ : ∀ n : ℕ, N₀ ≤ n → P₂.eval (n : ℝ) = B.eval (n : ℝ) * α₂ n)
    (h₃ : ∀ n : ℕ, N₀ ≤ n → P₃.eval (n : ℝ) = B.eval (n : ℝ) * α₃ n)
    (hP₃ : P₃ ≠ 0)
    (hd₀ : P₀.degree = P₃.degree) (hd₁ : P₁.degree = P₃.degree) (hd₂ : P₂.degree = P₃.degree)
    {A₀ A₁ A₂ ρ : ℝ}
    (hA₀ : |P₀.leadingCoeff / P₃.leadingCoeff| < A₀)
    (hA₁ : |P₁.leadingCoeff / P₃.leadingCoeff| < A₁)
    (hA₂ : |P₂.leadingCoeff / P₃.leadingCoeff| < A₂)
    (hρ : 0 < ρ) (hchar : A₂ * ρ ^ 2 + A₁ * ρ + A₀ ≤ ρ ^ 3) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n, N ≤ n → |m.rn n| ≤ C * ρ ^ n :=
  Zeta2StarB1.star_growth_bound_eventual (fun n => m.rn n) α₀ α₁ α₂ α₃ P₀ P₁ P₂ P₃ B N₀
    hL h₀ h₁ h₂ h₃ hP₃ hd₀ hd₁ hd₂ hA₀ hA₁ hA₂ hρ hchar

/-- The same at the CANDIDATE, so the statement the chain actually wants is written down at the
member it is about rather than left as an instantiation somebody has to perform. -/
theorem candidate_rn_growth_of_L1
    (α₀ α₁ α₂ α₃ : ℕ → ℝ) (P₀ P₁ P₂ P₃ B : ℝ[X]) (N₀ : ℕ)
    (hL : ∀ n : ℕ, N₀ ≤ n → α₀ n * candidateM.rn n + α₁ n * candidateM.rn (n + 1)
      + α₂ n * candidateM.rn (n + 2) + α₃ n * candidateM.rn (n + 3) = 0)
    (h₀ : ∀ n : ℕ, N₀ ≤ n → P₀.eval (n : ℝ) = B.eval (n : ℝ) * α₀ n)
    (h₁ : ∀ n : ℕ, N₀ ≤ n → P₁.eval (n : ℝ) = B.eval (n : ℝ) * α₁ n)
    (h₂ : ∀ n : ℕ, N₀ ≤ n → P₂.eval (n : ℝ) = B.eval (n : ℝ) * α₂ n)
    (h₃ : ∀ n : ℕ, N₀ ≤ n → P₃.eval (n : ℝ) = B.eval (n : ℝ) * α₃ n)
    (hP₃ : P₃ ≠ 0)
    (hd₀ : P₀.degree = P₃.degree) (hd₁ : P₁.degree = P₃.degree) (hd₂ : P₂.degree = P₃.degree)
    {A₀ A₁ A₂ ρ : ℝ}
    (hA₀ : |P₀.leadingCoeff / P₃.leadingCoeff| < A₀)
    (hA₁ : |P₁.leadingCoeff / P₃.leadingCoeff| < A₁)
    (hA₂ : |P₂.leadingCoeff / P₃.leadingCoeff| < A₂)
    (hρ : 0 < ρ) (hchar : A₂ * ρ ^ 2 + A₁ * ρ + A₀ ≤ ρ ^ 3) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n, N ≤ n → |candidateM.rn n| ≤ C * ρ ^ n :=
  rn_growth_of_L1 candidateM α₀ α₁ α₂ α₃ P₀ P₁ P₂ P₃ B N₀ hL h₀ h₁ h₂ h₃ hP₃ hd₀ hd₁ hd₂
    hA₀ hA₁ hA₂ hρ hchar

/-! ## Receipts -/

#print axioms rn_growth_of_L1
#print axioms candidate_rn_growth_of_L1

end Zeta2Instantiate
