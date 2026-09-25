/-
# ROW T-WIRE — the composition DRY RUN.  **IT PROVES THE WIRING, NOT THE THEOREM; since
# 2026-09-24 it carries NO `sorry`.**

**HEADLINE: PROVED ELSEWHERE, 2026-09-24.**  `Zeta2Unconditional.zeta2_not_liouvilleWith` (and
`Zeta2Target.zeta2_not_liouvilleWith`, which applies it) close the headline with no binder.  This
file's former §4 — `PT_P_sorried`, `RDECAY_sorried`, `QGROW_sorried` and the `twire_target_sorried`
built from them, carrying `sorryAx` by design — was REMOVED that day (owner directive: no sorry in
the proof), because every row it stubbed is proved: PT-P by `Zeta2PtpClose.pt_p`, RDECAY by
`Zeta2RDecay.rdecay_of_psi_of_moment`, QGROW by `Zeta2QGrow.qgrow_of_psi`, and their standing
binder `hψ` by `Zeta2Hpsi.hψ`.  Every receipt below reads the allowlist.

**What this file is for.**  Thirty-seven of the chain's forty-three rows are closed and **not one
line anywhere checked that they compose.**  `Zeta2L12.candidate_target_of_certified_constants`
binds eighteen hypotheses; a row that "closes" a binder in prose but proves a differently
quantified, differently indexed or differently NORMALISED statement fails at the application and
nowhere else (LEAN.md §3: composition failed on casts and indexing BOTH times it was tried on
this corpus).  So §3's acceptance is the EXECUTED application, and that is what §2 below is:
every binder the doc calls closed is filled from its real landed theorem, and only the three rows
the doc lists as OPEN — PT-P, RDECAY, QGROW — are left as hypotheses.

**CORRECTED 2026-09-20 by row QGROW — §1b, and the correction is in the INTERFACE, not in prose.**
Two of those three rows cannot be stated hypothesis-free AND be provable: RDECAY and QGROW both
reach `Δ̃`'s rate through `Zeta2DRate`, every theorem of which takes
`hψ : Zeta2LegA.psiErrorBoundStatement` explicitly, so the strongest statement either can produce
is `hψ → …`.  §1b names those two implications (`QGROW_deliverable`, `RDECAY_deliverable`) and §2's
`target_of_deliverable_rows` executes the composition in that shape.  QGROW is landed against it
(`Zeta2QGrow.qgrow_of_psi`); RDECAY is not, and its own blocker — L7ID's `rn` identification —
is unchanged by the correction.

**§2's `target_of_open_rows` is the deliverable and it is AXIOM-FREE.**  It is not "the pieces
with their neighbours as hypotheses": its hypotheses are exactly the three open rows' own
statements, at the objects the capstone binds, and every CLOSED row in the composition is the
landed theorem itself.  (Until 2026-09-24 a §4 discharged those three with `sorry` to execute the
eighteen-binder term in one piece; it is removed — the headline files now execute it for real.)

**The composition GOES THROUGH.**  All eighteen binders are supplied, nothing had to be weakened,
and no landed theorem needed a bridge.  The chain's two previously-disjoint partial compositions
— `Zeta2L4Br.target_of_arith_and_rates` (the star side: seven binders) and
`Zeta2Hc1.hc1` / `Zeta2DPhi.hc2_of_dphi` (the constants) — had never been applied to each other;
they are, here.

**What it found.  Read §3.**  The capstone binds ONE `Δ : ℕ → ℝ`, shared by `hΔne`, `hQ`, `hP`
and `hdecay`.  The chain's `Δ` is `Zeta2PhiT.ΔT = D(16n)·D(15n)/Φ̃ₙ` — the divided object, which
is what `Zeta2DRate.ΔT_growth` and `Zeta2PhiTRate` are about.  Row PNCLR's `binders_1615`
(closed 2026-09-19, the thirty-seventh row) proves `hΔne ∧ hQ ∧ hP` at the **un-divided**
`Zeta2Arith.Δ 16 15`, and those are DIFFERENT FUNCTIONS (`PNCLR_delta_is_not_the_chain_delta`,
in the kernel at `n = 1`, where `Φ̃₁ = 5929`).  Both instantiations typecheck against the
capstone — §3 executes the second one too — so nothing in Lean objects; what changes is which
function `hdecay` and `hgrowth` are then ABOUT, and only `ΔT` has a landed rate.  This is
LEAN.md §0a's binder-shape trap exactly: the binder SHAPE is not the headline NUMBER.  PNCLR's
own consumer is PT-P, which divides the witness by `Φ̃ₙ`; the chain's bookkeeping says so and
this file confirms it in the typechecker rather than in prose.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2L12
import Zeta2L4Br
import Zeta2PhiT
import Zeta2HatAssemble
import Zeta2Hc1
import Zeta2DRate
import Zeta2PnHarmDelta

namespace Zeta2TWire

open Zeta2Defs

/-! ## §1. The three OPEN rows, stated at the objects the capstone binds

Each is written at `Zeta2PhiT.ΔT` (the chain's `Δ̃`), at `Zeta2HatAssemble.QT` (the integer
sequence PT-QB's `hQ_at_ΔT` is about), at `candidateM.rn` and at `candidateM.pn` — never at a
stand-in — and each rate is at the constant its certifying row PINS: `c1 := Real.log
Zeta2XL1.rhoChar` (HC1) and `c2 := 31 − Zeta2DPhi.dPhi + ε'` (HC2).  Writing them at a
re-derived literal instead would need a bridge nobody has built. -/

/-- **PT-P, OPEN** — the p-half of the clearing at `Δ̃`.  PNCLR proves this at `Δ 16 15`;
PT-P is the division by `Φ̃ₙ`. -/
def PT_P_open : Prop :=
  ∃ P : ℕ → ℤ, ∀ n, ((P n : ℤ) : ℝ) = Zeta2PhiT.ΔT n * ((candidateM.pn n : ℚ) : ℝ)

/-- **RDECAY, OPEN** — `hc0`, `hδ`, `hCr` and `hdecay` travel together, because `c0` and `δ`
are FIXED by the decay bound and by nothing else in the chain.

**NOT DELIVERABLE AS STATED — see `RDECAY_deliverable` below.**  This `Prop` is the row's TARGET
and is hypothesis-free; the row's OUTPUT is `hψ → RDECAY_open ε'`, because the `Δ̃` half comes
from `Zeta2DRate.ΔT_clearing_rate(_hc2)`, whose first explicit argument is
`Zeta2LegA.psiErrorBoundStatement`.  RDECAY's own remaining blocker is unchanged by that
observation: it is L7ID's identification of `candidateM.rn`. -/
def RDECAY_open (ε' : ℝ) : Prop :=
  ∃ (c0 δ Cr : ℝ) (Nr : ℕ),
    (29.10787127 : ℝ) ≤ c0 ∧ δ ≤ 1 / 10 ^ 16 ∧ 0 < Cr ∧
      ∀ n, Nr ≤ n → |Zeta2PhiT.ΔT n * candidateM.rn n|
        ≤ Cr * Real.exp (-(c0 - (31 - Zeta2DPhi.dPhi + ε') - δ)) ^ n

/-- **QGROW** — `hCq` and `hgrowth`, at HC1's own `c1` and HC2's own `c2`.

**NOT DELIVERABLE AS STATED — see `QGROW_deliverable` below.**  This `Prop` is the row's TARGET
and is hypothesis-free; the row's OUTPUT is `hψ → QGROW_open ε'`, and that is what is landed
(`Zeta2QGrow.qgrow_of_psi`, 2026-09-20).  `QT n = Δ̃ₙ · qₙ`
(`Zeta2HatAssemble.hQ_at_ΔT`), so bounding `|QT n|` needs a rate for `Δ̃`, and all six landed
theorems that rate `Δ̃` take `Zeta2LegA.psiErrorBoundStatement` explicitly. -/
def QGROW_open (ε' : ℝ) : Prop :=
  ∃ (Cq : ℝ) (Nq : ℕ), 0 < Cq ∧
    ∀ n, Nq ≤ n → |((Zeta2HatAssemble.QT n : ℤ) : ℝ)|
      ≤ Cq * Real.exp (Real.log Zeta2XL1.rhoChar + (31 - Zeta2DPhi.dPhi + ε')) ^ n

/-! ### §1b. The SHAPE CORRECTION — what the two rate rows can actually deliver

**Added 2026-09-20 by row QGROW, and it is an interface fix rather than a remark.**  §1 states
all three open rows hypothesis-free.  For `PT_P_open` that is right — it is pure arithmetic.  For
the two RATE rows it is not: both reach `Δ̃`'s growth through `Zeta2DRate`, every theorem of which
takes `hψ : Zeta2LegA.psiErrorBoundStatement` as its first explicit argument, so the strongest
statement either row can produce is the IMPLICATION.  Leaving only the hypothesis-free form in the
scaffold let `QGROW_sorried`/`RDECAY_sorried` (both removed 2026-09-24) read as promises that some file would discharge them
outright; neither can, and no `#print axioms` anywhere in this corpus could have said so, because
a binder is not an axiom (LEAN.md §1).

The owner's answered fork of the same day makes `hψ` an ACCEPTED STANDING BINDER of the headline,
so these two definitions are the honest interface and not a weakening: a consumer written against
them cannot silently assume the unconditional form. -/

/-- **What row QGROW delivers.**  Landed: `Zeta2QGrow.qgrow_of_psi` inhabits this at every
`0 < ε'`. -/
def QGROW_deliverable (ε' : ℝ) : Prop :=
  Zeta2LegA.psiErrorBoundStatement → QGROW_open ε'

/-- **What row RDECAY delivers.**  Not yet inhabited — RDECAY is blocked on L7ID's `rn`
identification, which this correction does not touch. -/
def RDECAY_deliverable (ε' : ℝ) : Prop :=
  Zeta2LegA.psiErrorBoundStatement → RDECAY_open ε'

/-! ## §2. THE COMPOSITION, EXECUTED — and this theorem is AXIOM-FREE

Eighteen binders.  Fifteen are filled from landed theorems, by name:

| binder | filled by | row |
|---|---|---|
| `hrecq` `hrecp` | `Zeta2L1Asm.hrecq` / `hrecp`, inside `target_of_arith_and_rates` | L1-ASM (recurrence half) |
| `hN₁` `hM₀` `hα₃` `hα₀` `hrow` | `Zeta2L4Br.hN₁`/`hM₀`/`hα₃`/`hα₀`/`hrow`, same | L4-BR, THRESH |
| `hc1` | `Zeta2Hc1.hc1` — pins `c1 := Real.log Zeta2XL1.rhoChar` | HC1 |
| `hc2` | `Zeta2DPhi.hc2_of_dphi` — pins `c2 := 31 − dPhi + ε'` | HC2 |
| `hΔne` | `Zeta2PhiT.ΔT_ne_zero` | PT-DEF |
| `hQ` | `Zeta2HatAssemble.hQ_at_ΔT` | PT-QB |

and the remaining three — `hP`, the `hc0`/`hδ`/`hCr`/`hdecay` block, and `hCq`/`hgrowth` — are
this theorem's hypotheses, which is what an open row is. -/

/-- **T-WIRE.**  The capstone applied with every closed row's real theorem; the three open rows
are the hypotheses.  Axiom-free: `#print axioms` below. -/
theorem target_of_open_rows {ε' : ℝ} (hε' : ε' ≤ 1 / 10 ^ 8)
    (hPT_P : PT_P_open) (hRDECAY : RDECAY_open ε') (hQGROW : QGROW_open ε') :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 := by
  obtain ⟨P, hP⟩ := hPT_P
  obtain ⟨c0, δ, Cr, Nr, hc0, hδ, hCr, hdecay⟩ := hRDECAY
  obtain ⟨Cq, Nq, hCq, hgrowth⟩ := hQGROW
  exact Zeta2L4Br.target_of_arith_and_rates
    Zeta2HatAssemble.QT P Zeta2PhiT.ΔT
    hc0 Zeta2Hc1.hc1 (Zeta2DPhi.hc2_of_dphi ε' hε') hδ
    Zeta2PhiT.ΔT_ne_zero Zeta2HatAssemble.hQ_at_ΔT hP
    hCr hdecay hCq hgrowth

/-- **T-WIRE in the deliverable shape** (added 2026-09-20 with §1b).  The same eighteen-binder
application, with the two rate rows taken in the form they can actually be proved and `hψ`
carried explicitly — which is the form the owner's answered fork accepts.  It is `¬ LiouvilleWith
5.0495243 zeta2` from: `hψ`, PT-P, RDECAY-as-an-implication, and QGROW-as-an-implication.  Axiom
free, and its TYPE is the disclosure `#print axioms` cannot make. -/
theorem target_of_deliverable_rows (hψ : Zeta2LegA.psiErrorBoundStatement)
    {ε' : ℝ} (hε' : ε' ≤ 1 / 10 ^ 8)
    (hPT_P : PT_P_open) (hRDECAY : RDECAY_deliverable ε') (hQGROW : QGROW_deliverable ε') :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  target_of_open_rows hε' hPT_P (hRDECAY hψ) (hQGROW hψ)

/-! ## §3. Diagnostics — the checks this dry run exists to make

None of these is a step of the chain.  Each is a question that had never been asked in Lean. -/

/-- **NUMERAL, arm 1.**  The capstone's conclusion and `Zeta2Target.zeta2_not_liouvilleWith`'s
statement are the same literal, so the wiring reaches the target's own statement. -/
theorem capstone_numeral : (5.0495243 : ℝ) = 50495243 / 10 ^ 7 := by norm_num

/-- **NUMERAL, arm 2 — a DISCREPANCY, and it is in the DOC, not in the Lean.**  The chain doc's
title is `μ(ζ(2)) ≤ 5.04952429`; every Lean file proves `¬ LiouvilleWith 5.0495243`, i.e.
`μ ≤ 5.04952430`.  The two are not equal, and the doc's is the SMALLER. -/
theorem headline_numeral_is_below_the_theorem_numeral :
    (5.04952429 : ℝ) < (5.0495243 : ℝ) := by norm_num

/-- **NUMERAL, arm 3 — and `5.04952429` is not a bound this chain can deliver.**  The certified
`1 + v/(u−δ)` at the archived constants is `5.049524290530377` (`Zeta2L12.L12_archived_real`),
and the doc's headline literal is strictly BELOW it: it is the certified value TRUNCATED, not
rounded outward.  `5.0495243` is the first eight-decimal literal above it, which is why every
file uses that one. -/
theorem headline_numeral_is_below_the_certified_value :
    (5.04952429 : ℝ)
      < 1 + (42.033615807966612 + 15.019120927608038)
          / (29.107871270207490 - 15.019120927608038 - 994 / 10 ^ 19) := by
  norm_num

/-- **NUMERAL, arm 4 — the three numbers in one statement, with both directions.**  Write
`V := 1 + v/(u−δ)` at the archived constants (`= 5.049524290530377`), `H := 5.04952429` the doc
title's literal and `T := 5.0495243 = 5.04952430` the literal every Lean file proves.  Then
`H < V < T`.  The right half is `Zeta2L12.L12_archived_real`; the left half is the finding.
Since `T` and `H` are CONSECUTIVE eight-decimal literals, `T` is the SMALLEST eight-decimal
literal that clears and `H` is the LARGEST that does not. -/
theorem certified_value_is_strictly_between_the_two_literals :
    (5.04952429 : ℝ)
        < 1 + (42.033615807966612 + 15.019120927608038)
            / (29.107871270207490 - 15.019120927608038 - 994 / 10 ^ 19)
      ∧ 1 + ((42.033615807966612 : ℝ) + 15.019120927608038)
            / (29.107871270207490 - 15.019120927608038 - 994 / 10 ^ 19)
        < (5.0495243 : ℝ)
      ∧ (5.04952429 : ℝ) + 1 / 10 ^ 8 = (5.0495243 : ℝ) := by
  refine ⟨by norm_num, Zeta2L12.L12_archived_real, by norm_num⟩

/-- **NUMERAL, arm 5 — and `mono` runs the wrong way to rescue the doc's literal.**
`LiouvilleWith` is downward-closed in the exponent, so `Zeta2Target.zeta2_irrationality_measure_le`
turns `¬ LiouvilleWith 5.0495243` into `¬ LiouvilleWith p` for every `p ≥ 5.0495243` and for no
`p` below it.  `5.04952429` is below it.  So the doc-title claim is STRICTLY STRONGER than the
chain's, not a rounding of it, and no closing of the open rows will produce it. -/
theorem headline_numeral_is_not_reached_by_mono :
    ¬ ((5.0495243 : ℝ) ≤ 5.04952429) := by norm_num

/-- **Δ INSTANTIATION — the check the whole dry run was for.**  `Zeta2PhiT.ΔT` (the chain's
`Δ̃`, what `Zeta2DRate.ΔT_growth` bounds and what `hdecay`/`hgrowth` must be about) and
`Zeta2Arith.Δ 16 15` (what row PNCLR's `binders_1615` is about) are DIFFERENT FUNCTIONS.  At
`n = 1` they differ by `Φ̃₁ = 5929`.  The capstone binds ONE `Δ`, so at most one of the two can
be the instantiation. -/
theorem PNCLR_delta_is_not_the_chain_delta :
    Zeta2PhiT.ΔT 1 ≠ ((Zeta2Arith.Δ 16 15 1 : ℕ) : ℝ) := by
  have hm := Zeta2PhiT.ΔT_mul_PhiT 1
  rw [Zeta2PhiT.PhiT_one] at hm
  have hpos : (0 : ℝ) < Zeta2PhiT.ΔT 1 := Zeta2PhiT.ΔT_pos 1
  intro h
  rw [h] at hm hpos
  push_cast at hm
  linarith

/-- **And PNCLR's binders DO typecheck into the capstone — which is exactly why the check above
was needed.**  This is the same executed composition as §2 with `Δ := Δ 16 15` and PNCLR's
`binders_1615` in the three arithmetic slots.  Lean raises no objection; what it does is FORCE
the decay and growth hypotheses to be about `Δ 16 15`, and no landed row bounds that.
(`Zeta2DRate`'s own falsifier arm N1 is the row restated at the un-divided `Δ 16 15`, and it
REDS.)  So the binder SHAPE is satisfied at both objects and only one of them carries the
headline μ — LEAN.md §0a's trap, executed rather than argued. -/
theorem capstone_at_the_undivided_delta {Nr Nq : ℕ} {Cr Cq c0 δ ε' : ℝ}
    (hε' : ε' ≤ 1 / 10 ^ 8)
    (hc0 : (29.10787127 : ℝ) ≤ c0) (hδ : δ ≤ 1 / 10 ^ 16) (hCr : 0 < Cr)
    (hdecay : ∀ n, Nr ≤ n →
      |((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) * candidateM.rn n|
        ≤ Cr * Real.exp (-(c0 - (31 - Zeta2DPhi.dPhi + ε') - δ)) ^ n)
    (hCq : 0 < Cq)
    (hgrowth : ∀ Q : ℕ → ℤ,
      (∀ n, (Q n : ℝ) = ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) * ((candidateM.qn n : ℚ) : ℝ)) →
      ∀ n, Nq ≤ n → |(Q n : ℝ)|
        ≤ Cq * Real.exp (Real.log Zeta2XL1.rhoChar + (31 - Zeta2DPhi.dPhi + ε')) ^ n) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 := by
  obtain ⟨Q, P, hΔne, hQ, hP⟩ := Zeta2PnHarmDelta.binders_1615
  exact Zeta2L4Br.target_of_arith_and_rates Q P
    (fun n => ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ))
    hc0 Zeta2Hc1.hc1 (Zeta2DPhi.hc2_of_dphi ε' hε') hδ hΔne hQ hP
    hCr hdecay hCq (hgrowth Q hQ)

/-- **THE SMALLEST BRIDGE, and it is exactly row PT-P.**  The capstone binds ONE `Δ`, so the
integrality binders and `hdecay` cannot be at different objects; the chain's object is `ΔT`,
because that is the only one with a landed rate.  What separates PNCLR's landed `binders_1615`
from the capstone's `hP` at `ΔT` is therefore ONE divisibility — `Φ̃ₙ` divides PNCLR's own
witness — and this theorem is that reduction, executed: hand it the divisibility and it hands
back `PT_P_open`.  `Zeta2PhiT.ΔT_mul_PhiT` is the landed arithmetic bridge and it is NOT enough
on its own; the missing content is the divisibility, the p-side twin of PT-QB's landed
`Zeta2HatAssemble.PhiT_dvd_qnInt`.  So PNCLR is not closed at the wrong object — its row
statement is `PnClearedAt 16 15` and its declared consumer is PT-P — but `binders_1615` is a
STAND-IN triple, and none of the capstone's three arithmetic binders at the chain's `Δ` comes
from it. -/
theorem PT_P_of_PhiT_dvd
    (h : ∀ P : ℕ → ℤ,
      (∀ n, ((P n : ℤ) : ℝ)
        = ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) * ((candidateM.pn n : ℚ) : ℝ)) →
      ∀ n, ((Zeta2PhiT.PhiT n : ℕ) : ℤ) ∣ P n) :
    PT_P_open := by
  obtain ⟨Q, P, hΔne, hQ, hP⟩ := Zeta2PnHarmDelta.binders_1615
  have hdvd := h P hP
  refine ⟨fun n => P n / ((Zeta2PhiT.PhiT n : ℕ) : ℤ), fun n => ?_⟩
  obtain ⟨c, hc⟩ := hdvd n
  have hne : ((Zeta2PhiT.PhiT n : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Zeta2PhiT.PhiT_ne_zero n
  have hR : ((Zeta2PhiT.PhiT n : ℕ) : ℝ) ≠ 0 := Zeta2PhiT.PhiT_cast_ne_zero n
  have hdiv : P n / ((Zeta2PhiT.PhiT n : ℕ) : ℤ) = c := by
    rw [hc]; exact Int.mul_ediv_cancel_left c hne
  have hcR : ((Zeta2PhiT.PhiT n : ℕ) : ℝ) * ((c : ℤ) : ℝ) = ((P n : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hc.symm
  show ((P n / ((Zeta2PhiT.PhiT n : ℕ) : ℤ) : ℤ) : ℝ)
      = Zeta2PhiT.ΔT n * ((candidateM.pn n : ℚ) : ℝ)
  rw [hdiv]
  have hgoal : Zeta2PhiT.ΔT n * ((candidateM.pn n : ℚ) : ℝ) = ((c : ℤ) : ℝ) := by
    rw [show Zeta2PhiT.ΔT n
        = ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) / ((Zeta2PhiT.PhiT n : ℕ) : ℝ) from rfl,
      div_mul_eq_mul_div, ← hP n, ← hcR]
    field_simp
  exact hgoal.symm

/-- **VACUITY (LEAN.md §5, and `Zeta2L12.hmu_is_vacuous_at_u_zero`'s mechanism).**  That theorem
records that `hmu : 1 + v/u < 5.0495243` is Lean-vacuous at `u = 0`, because `v / 0 = 0`.  The
mechanism is NOT live in this instantiation: the constants wired above force `u > 0` with no
extra hypothesis, since `hc0`, HC2's `hc2` and `hδ` compose to `uRate ≤ u` and `uRate > 0`.
So the decay base `exp(−u)` is a real decay here, not `exp 0 = 1`. -/
theorem u_is_positive_at_the_wired_constants {c0 δ ε' : ℝ}
    (hc0 : (29.10787127 : ℝ) ≤ c0) (hδ : δ ≤ 1 / 10 ^ 16) (hε' : ε' ≤ 1 / 10 ^ 8) :
    0 < c0 - (31 - Zeta2DPhi.dPhi + ε') - δ := by
  have h := Zeta2L12.uRate_le_certified hc0 (Zeta2DPhi.hc2_of_dphi ε' hε') hδ
  linarith [Zeta2L12.uRate_pos]

/-- **NON-VACUITY of the `Δ` slot.**  `hΔne` is not satisfied by a degenerate `Δ`: the wired
one is strictly positive at every `n`, so `hQ`/`hP` are statements about genuinely nonzero
multiples and not about the zero sequence. -/
theorem wired_delta_is_positive (n : ℕ) : 0 < Zeta2PhiT.ΔT n := Zeta2PhiT.ΔT_pos n

/-! ## §4. REMOVED 2026-09-24 — the `sorry`'d one-piece term

§4 used to apply `target_of_open_rows` to `sorry`'d copies of the three open rows
(`PT_P_sorried`, `RDECAY_sorried`, `QGROW_sorried`, giving `twire_target_sorried`, which carried
`sorryAx` by design).  Every one of those rows is now proved, and the eighteen-binder term is
executed for real, with no hypothesis, by `Zeta2Unconditional.zeta2_not_liouvilleWith`; the
scaffold is deleted under the owner's 2026-09-24 directive that the proof carry no `sorry`. -/

end Zeta2TWire

/-! ## Receipts (LEAN.md §1 — and read the exit code separately; neither channel is sufficient)

Every theorem below must come back inside `{propext, Classical.choice, Quot.sound}`. -/

#print axioms Zeta2TWire.target_of_open_rows
#print axioms Zeta2TWire.target_of_deliverable_rows
#print axioms Zeta2TWire.capstone_numeral
#print axioms Zeta2TWire.headline_numeral_is_below_the_theorem_numeral
#print axioms Zeta2TWire.headline_numeral_is_below_the_certified_value
#print axioms Zeta2TWire.certified_value_is_strictly_between_the_two_literals
#print axioms Zeta2TWire.headline_numeral_is_not_reached_by_mono
#print axioms Zeta2TWire.PNCLR_delta_is_not_the_chain_delta
#print axioms Zeta2TWire.capstone_at_the_undivided_delta
#print axioms Zeta2TWire.PT_P_of_PhiT_dvd
#print axioms Zeta2TWire.u_is_positive_at_the_wired_constants
#print axioms Zeta2TWire.wired_delta_is_positive

/-! **And the TYPES beside the receipts** (LEAN.md §1, added 2026-09-20): `#print axioms` on
`target_of_open_rows` and on `target_of_deliverable_rows` are byte-identical, and the two
theorems make very different claims.  The difference is visible only here. -/

#check @Zeta2TWire.target_of_open_rows
#check @Zeta2TWire.target_of_deliverable_rows
#check @Zeta2TWire.QGROW_deliverable
#check @Zeta2TWire.RDECAY_deliverable
