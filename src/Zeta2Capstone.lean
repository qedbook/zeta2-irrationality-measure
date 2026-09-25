/-
# THE CAPSTONE COMPOSITION — the μ(ζ(2)) chain reduced to TWO named hypotheses

**What this file proves.**  One theorem, and everything else here exists to make it readable or
to stop it meaning less than it says:

```
Zeta2Capstone.target_of_psi_and_ptp :
    Zeta2LegA.psiErrorBoundStatement → Zeta2TWire.PT_P_open →
      ¬ LiouvilleWith 5.0495243 Zeta2Defs.zeta2
```

**Why it is a landing and not a one-liner in a doc.**  `Zeta2RDecay.target_of_one_open_row`
concludes the target from `hψ`, `hP : ∀ n, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n`, two `ε'`
side conditions and `PT_P_open`; `Zeta2PpolMoment.ppolMomentValue : ∀ n, PpolMomentValue n`
carries no hypothesis at all.  Substituting one into the other is one line ON PAPER — and
LEAN.md §3 is the section that says a composition is EXECUTED or it is not done.  The concrete
obstacle here was not casts or indexing: it was that the two theorems had never been shown to
live in ONE Lean environment.  `Zeta2RDecay` reaches `L7MidM5.rLine` through `Zeta2C7Mod`
(the capstone with the M5 prefix IMPORTED), `Zeta2PpolMoment` reaches it through the
`L7MidM5` module directly, and until this file nothing had imported both.  If those were two
constants, `moment_is_the_identification_across_modules` below would not typecheck — that
theorem applies `Zeta2RDecay.moment_binder_is_the_identification` (stated through `Zeta2C7Mod`'s
import path) to `Zeta2PpolMoment.rn_eq_neg_rLine_uncond` (stated through `Zeta2PpolMoment`'s),
and the typechecker, not this comment, is what rules that they are one constant.

**WHAT THIS FILE DOES NOT CLAIM.**

* It does **not** prove `μ(ζ(2)) ≤ 5.0495243`.  Two hypotheses are open and NEITHER is an
  axiom, so `#print axioms` on the theorem below reads `[propext, Classical.choice, Quot.sound]`
  — byte-identical to what an unconditional proof would print (LEAN.md §1, 2026-09-20: a binder
  is not an axiom).  **The receipt is HALF the acceptance; `#check @` is the other half**, and
  both are printed at the bottom of this file.
  - `hψ : Zeta2LegA.psiErrorBoundStatement` — MediumPNT's error rate on Chebyshev's `ψ`,
    discharged on `PrimeNumberTheoremAnd` at that project's own toolchain (LEAN.md §7), never
    on this pin.  ACCEPTED, per the owner fork answered A on 2026-09-20.
  - `hPT_P : Zeta2TWire.PT_P_open` — row PT-P, the p-half of the clearing at `Δ̃`.  OPEN, and
    the only mathematical row this chain still owes.
* It does **not** reach `5.04952429`.  The literal is `5.0495243`, the chain's own, and
  `Zeta2TWire.certified_value_is_strictly_between_the_two_literals` is where that is settled.
* It does **not** touch `Zeta2Target.zeta2_not_liouvilleWith`, whose `sorry` is deliberate and
  stays confined to `Zeta2Target.lean`.

**The `ε'` binders are not hidden.**  `target_of_psi_and_ptp_at` keeps them exactly as
`Zeta2RDecay.target_of_one_open_row` states them; `target_of_psi_and_ptp` supplies the single
witness `epsCap := 10⁻¹⁸` with both side conditions proved by `norm_num` in this file.  That is
a strengthening (one `ε'` is all the chain needs, and the conclusion does not mention `ε'`),
not a weakening — no binder anywhere was altered to make anything typecheck.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
Runner `run_capstone.sh`, falsifier `falsify_capstone.sh`, receipts `out_axioms_capstone.txt`
and `out_capstone_falsify.txt`.
-/
import Zeta2RDecay
import Zeta2PpolMoment

namespace Zeta2Capstone

open Zeta2Defs

/-! ## §1. The binder RDECAY carried, discharged from a theorem that carries none -/

/-- **L7ID's residue, supplied.**  `Zeta2RDecay.target_of_one_open_row` asks for
`∀ n, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n`; `Zeta2PpolMoment.ppolMomentValue` proves
`∀ n, PpolMomentValue n` with NO hypothesis, so the `1 ≤ n` gate is discarded rather than
assumed.  This is the whole of the discharge, and it is written out so that the shape RDECAY
asks for and the shape L7ID proves can be compared side by side. -/
theorem moment_all : ∀ n : ℕ, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n :=
  fun n _ => Zeta2PpolMoment.ppolMomentValue n

/-! ## §2. THE COMPOSITION, EXECUTED — with the chain's own `ε'` binders intact -/

/-- **The composition with every binder `Zeta2RDecay.target_of_one_open_row` states, kept.**
Only `hP` is discharged; `hε'0`, `hε'` and `hPT_P` are passed through unchanged, so a reader
can see that the substitution touched exactly one argument. -/
theorem target_of_psi_and_ptp_at (hψ : Zeta2LegA.psiErrorBoundStatement)
    {ε' : ℝ} (hε'0 : 0 < ε') (hε' : ε' ≤ 1 / 10 ^ 8)
    (hPT_P : Zeta2TWire.PT_P_open) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2RDecay.target_of_one_open_row hψ moment_all hε'0 hε' hPT_P

/-! ## §3. The `ε'` witness, chosen and proved rather than assumed -/

/-- The `ε'` the headline form is instantiated at.  `ε'` is `Zeta2DRate.ΔT_clearing_rate`'s
slack; it does not appear in the conclusion, so ONE admissible value is all the chain needs.
`10⁻¹⁸` is `Zeta2RDecay.epsR`'s value, chosen for the same reason it was chosen there. -/
noncomputable def epsCap : ℝ := 1 / 10 ^ 18

theorem epsCap_pos : 0 < epsCap := by rw [epsCap]; norm_num

theorem epsCap_le : epsCap ≤ (1 : ℝ) / 10 ^ 8 := by rw [epsCap]; norm_num

/-! ## §4. THE HEADLINE, CONDITIONAL ON EXACTLY TWO HYPOTHESES -/

/-- **THE CAPSTONE.**  `hψ` and `PT_P_open` are the only hypotheses; read the `#check @` at the
bottom of this file, because the `#print axioms` beside it cannot say so.

`hψ` is the standing external binder (accepted; LEAN.md §7).  `PT_P_open` is row PT-P, the one
open row.  Everything else the chain owed — L1's recurrence, L5's growth, L7's decay, L9/L11's
criterion, the arithmetic clearing at `Δ̃`, and L7ID's identification of `candidateM.rn` — is
inside this term. -/
theorem target_of_psi_and_ptp (hψ : Zeta2LegA.psiErrorBoundStatement)
    (hPT_P : Zeta2TWire.PT_P_open) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  target_of_psi_and_ptp_at hψ epsCap_pos epsCap_le hPT_P

/-- The same, as an irrationality-measure bound, by `LiouvilleWith.mono` — the shape
`Zeta2Target.zeta2_irrationality_measure_le` states from the `sorry`'d unconditional target,
proved here from the conditional one instead. -/
theorem zeta2_irrationality_measure_le_of_psi_of_ptp
    (hψ : Zeta2LegA.psiErrorBoundStatement) (hPT_P : Zeta2TWire.PT_P_open) :
    ∀ p : ℝ, (5.0495243 : ℝ) ≤ p → ¬ LiouvilleWith p zeta2 :=
  fun _ hp h => target_of_psi_and_ptp hψ hPT_P (h.mono hp)

/-! ## §5. Rung 0 — the checks that stop this green meaning less than it says (LEAN.md §5)

None of these is a step of the chain. -/

/-- **THE TWO MODULES NAME ONE `L7MidM5.rLine`, AND THE TYPECHECKER SAYS SO.**  This is the
check the L7ID unit named and declined to assume.  `Zeta2RDecay.moment_binder_is_the_identification`
is stated in an environment reaching `rLine` through `Zeta2C7Mod`;
`Zeta2PpolMoment.rn_eq_neg_rLine_uncond` is stated in one reaching it through the `L7MidM5`
module.  Applying the first to the second is only well-typed if they are the same constant —
the duplicate-declaration failure `falsify_rdecay.sh`'s arm A10 measured
(`environment already contains 'L7MidM6.Kn'`) is what this rules out, positively. -/
theorem moment_is_the_identification_across_modules {n : ℕ} (hn : 1 ≤ n) :
    Zeta2L7IdSum.PpolMomentValue n :=
  (Zeta2RDecay.moment_binder_is_the_identification hn).mp
    (Zeta2PpolMoment.rn_eq_neg_rLine_uncond hn)

/-- **THE DISCHARGED BINDER CAME FROM A THEOREM WITH NO HYPOTHESIS.**  `hP` was not weakened,
generalised or assumed: `ppolMomentValue` is `∀ n, PpolMomentValue n`, full stop.  Stated here
so that "`hP` is discharged" is checkable without opening `Zeta2PpolMoment.lean`. -/
theorem moment_is_unconditional : ∀ n : ℕ, Zeta2L7IdSum.PpolMomentValue n :=
  Zeta2PpolMoment.ppolMomentValue

/-- **THE REMAINING TWO HYPOTHESES ARE NOT THE SAME THING.**  `hψ` is an analytic statement
about Chebyshev's `ψ` and `PT_P_open` is an arithmetic statement about `Δ̃ₙ·pₙ`; a composition
that had accidentally collapsed one onto the other would still typecheck above.  Inhabiting the
pair from the pair is trivial — the content is that the two `Prop`s are BOTH still named in the
capstone's type, which `#check @target_of_psi_and_ptp` shows and this signature pins. -/
theorem both_hypotheses_are_still_asked_for
    (hψ : Zeta2LegA.psiErrorBoundStatement) (hPT_P : Zeta2TWire.PT_P_open) :
    Zeta2LegA.psiErrorBoundStatement ∧ Zeta2TWire.PT_P_open :=
  ⟨hψ, hPT_P⟩

/-- **THE CONSTANT IS THE CHAIN'S, NOT THE OLD HEADLINE'S.**  `5.04952429 < 5.0495243`, so the
retired advertised numeral is a STRICTLY STRONGER claim that `LiouvilleWith.mono` cannot reach
from this theorem (`Zeta2TWire.headline_numeral_is_not_reached_by_mono` is where that is
proved).  Re-asserted here as a literal comparison so that this file's own conclusion cannot be
misread as the stronger one. -/
theorem the_literal_is_the_chains : (5.04952429 : ℝ) < 5.0495243 := by norm_num

end Zeta2Capstone

/-! ## RECEIPTS — LEAN.md §1, BOTH channels, and the type beside every receipt.

`#print axioms` answers "is the proof of what it states sound?".  It CANNOT answer "is what it
states the claim being advertised?", because a hypothesis is an argument and axioms are not
arguments.  So every theorem is printed twice: the receipt, then `#check @` with the full type.
The acceptance for this landing is that
`Zeta2Capstone.target_of_psi_and_ptp` prints
`[propext, Classical.choice, Quot.sound]` AND a type naming exactly
`Zeta2LegA.psiErrorBoundStatement` and `Zeta2TWire.PT_P_open` and no other hypothesis. -/

#print axioms Zeta2Capstone.moment_all
#check @Zeta2Capstone.moment_all
#print axioms Zeta2Capstone.target_of_psi_and_ptp_at
#check @Zeta2Capstone.target_of_psi_and_ptp_at
#print axioms Zeta2Capstone.epsCap_pos
#check @Zeta2Capstone.epsCap_pos
#print axioms Zeta2Capstone.epsCap_le
#check @Zeta2Capstone.epsCap_le
#print axioms Zeta2Capstone.target_of_psi_and_ptp
#check @Zeta2Capstone.target_of_psi_and_ptp
#print axioms Zeta2Capstone.zeta2_irrationality_measure_le_of_psi_of_ptp
#check @Zeta2Capstone.zeta2_irrationality_measure_le_of_psi_of_ptp
#print axioms Zeta2Capstone.moment_is_the_identification_across_modules
#check @Zeta2Capstone.moment_is_the_identification_across_modules
#print axioms Zeta2Capstone.moment_is_unconditional
#check @Zeta2Capstone.moment_is_unconditional
#print axioms Zeta2Capstone.both_hypotheses_are_still_asked_for
#check @Zeta2Capstone.both_hypotheses_are_still_asked_for
#print axioms Zeta2Capstone.the_literal_is_the_chains
#check @Zeta2Capstone.the_literal_is_the_chains

/-! The two open hypotheses, printed as the `Prop`s they are, so a reader can see what is owed
without opening another file. -/
#check @Zeta2TWire.PT_P_open
#print Zeta2TWire.PT_P_open
#check @Zeta2PpolMoment.ppolMomentValue
#check @Zeta2RDecay.target_of_one_open_row
