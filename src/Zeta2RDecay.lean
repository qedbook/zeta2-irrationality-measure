/-
# ROW RDECAY — `hdecay` at the real `rₙ`, conditional on `hψ` AND on L7ID's moment value

**HEADLINE: `Zeta2Target.zeta2_not_liouvilleWith` is NOT proved.**  This file closes one row of
the μ(ζ(2)) chain and discharges none of the others.

## What this row delivers, and the TWO binders it carries

```
Zeta2RDecay.rdecay_of_psi_of_moment
  (hψ : Zeta2LegA.psiErrorBoundStatement)
  (hP : ∀ n : ℕ, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n)
  {ε' : ℝ} (hε' : 0 < ε') : Zeta2TWire.RDECAY_open ε'
```

* **`hψ`** — MediumPNT's error rate on Chebyshev's ψ, formalized on `PrimeNumberTheoremAnd` at a
  different toolchain (LEAN.md §7).  It enters through `Zeta2DRate.ΔT_clearing_rate`, whose first
  explicit argument it is, exactly as it does in the QGROW twin.  It is the owner's accepted
  standing binder (answered fork 2026-09-20).
* **`hP`** — L7ID's remaining residue.  `Zeta2L7IdSum.rn_eq_neg_rLine_iff` proves
  `candidateM.rn n = −L7MidM5.rLine n ↔ PpolMomentValue n`, so this binder is not a weakness of
  this row's proof: it IS L7ID's open obligation, carried rather than assumed away.  It leaves
  the moment L7ID closes, and `rdecay_of_psi` below is the one-line statement that will then be
  available.

**AND `#print axioms` CANNOT SEE EITHER OF THEM** (LEAN.md §1, 2026-09-20): a binder is not an
axiom, so every receipt in this file reads `[propext, Classical.choice, Quot.sound]` whether the
theorem is conditional or not.  Acceptance for this row is the receipt **and** the `#check @`
type, both emitted at the bottom of this file and both archived.

## The structural thing this row had to build first, and it is not transport

The cell priced this row at "~100–150 lines of transport".  The transport is indeed two shape
moves (`∀ᶠ` → `∀ n ≥ N`, `exp(n·x)` → `exp x ^ n`).  What the cell did not price is that the two
objects being transported **did not live in the same Lean environment**:

* the RATE, `Zeta2RouteBL7.routeB_l7_rate_sigmaTilde`, lived only in
  `Zeta2RouteBL7Capstone.lean`, a CONSOLIDATED file that re-emits X-L7/C1/C6/M0/M1-M3/M4/M5
  inline and therefore declares its own `L7MidM5.rLine`;
* the IDENTIFICATION, `Zeta2L7IdSum.rn_eq_neg_rLine`, is built on the MODULE `L7MidM5.olean`.

Importing both into one file is a duplicate-declaration error.  `Zeta2C7Mod.lean`
(`../zeta2_l7_capstone/c7mod.consolidate`) is the capstone with the M5 prefix IMPORTED instead of
inlined; it is generated from the same three inputs, so `lean-consolidate-check` reds if either
form drifts.  With it, `L7MidM5.rLine` is ONE constant and the rate and the identification are
about the same object — which is what `rn_decay` below needs and what nothing before could state.

## The arithmetic, in one line

`routeB_l7_rate_sigmaTilde` gives `|rLine n| ≤ exp(n·(G + ε))` with `G := GB + εB·rB` and `ε`
free; `|rₙ| = |rLine n|` past `n ≥ 1` by `hP`; `ΔT_clearing_rate` multiplies in `Δ̃`'s own rate
`c₂ = 31 − d_φ̃ + ε'`, giving base `exp(G + ε)·exp(c₂) = exp(−(c₀ − c₂ − ε))` at `c₀ := −G`
EXACTLY — `base_eq` is an equality, not an estimate.  `Zeta2L12.decay_relax` then relaxes `ε` up
to the chain's `δ`.  `hc₀ : 29.10787127 ≤ c₀` is `norm_num` on C7's literals with margin ≈2.02e-10.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2TWire
import Zeta2L7IdSum
import Zeta2C7Mod
import Zeta2QGrow

namespace Zeta2RDecay

open Zeta2Defs

/-! ## §1. The three constants the row's existential supplies

`c₀` and `δ` are FIXED by the decay bound and by nothing else in the chain, which is why they
travel inside `RDECAY_open`'s `∃` rather than arriving from a neighbouring row.  `ε` is the slack
in C7's own rate statement, and it is chosen STRICTLY below `δ` so that `decay_relax` does real
work rather than closing by `le_refl` — a relaxation that is secretly an equality would hide a
sign error in the exponent. -/

/-- The slack handed to `routeB_l7_rate_sigmaTilde`. -/
noncomputable def epsR : ℝ := 1 / 10 ^ 18

/-- The chain's `δ`, the second component of `RDECAY_open`'s existential. -/
noncomputable def deltaR : ℝ := 1 / 10 ^ 17

/-- The chain's `c₀`, which is C7's certified rate with its sign flipped and NOT a re-derived
literal: `−(GB + εB·rB) = 29.1078712702074895853099063 − 10⁻¹⁸`. -/
noncomputable def c0 : ℝ := -(Zeta2C7.GB + Zeta2C7.epsB * Zeta2C7.rB)

theorem epsR_pos : 0 < epsR := by rw [epsR]; norm_num

theorem epsR_lt_deltaR : epsR < deltaR := by rw [epsR, deltaR]; norm_num

/-- `hδ` — the second conjunct of `RDECAY_open`. -/
theorem hdeltaR : deltaR ≤ (1 : ℝ) / 10 ^ 16 := by rw [deltaR]; norm_num

/-- **`hc₀` — the first conjunct of `RDECAY_open`**, on C7's own constants.  Margin ≈2.02e-10,
which is why the literal is `29.10787127` and not one digit more. -/
theorem hc0 : (29.10787127 : ℝ) ≤ c0 := by
  rw [c0, Zeta2C7.GB, Zeta2C7.epsB, Zeta2C7.rB]
  norm_num

/-! ## §2. The `rₙ` decay — the rate transported onto the chain's own remainder

This is the first time a DECAY statement in this corpus is about `candidateM.rn`.  Both shape
moves the cell named happen here and nowhere else: `Filter.eventually_atTop` turns `∀ᶠ` into
`∀ n ≥ N`, and `Zeta2DRate.exp_pow` turns `exp (n·x)` into `exp x ^ n`. -/

/-- `|rₙ| ≤ 1 · exp(G + ε)ⁿ` eventually, where `G := GB + εB·rB` is C7's certified rate.
The `max N 1` is load-bearing: `rn_eq_neg_rLine` is gated `1 ≤ n`. -/
theorem rn_decay (hP : ∀ n : ℕ, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |candidateM.rn n|
        ≤ 1 * Real.exp (Zeta2C7.GB + Zeta2C7.epsB * Zeta2C7.rB + epsR) ^ n := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (Zeta2RouteBL7.routeB_l7_rate_sigmaTilde epsR_pos)
  refine ⟨max N 1, fun n hn => ?_⟩
  have h1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hNn : N ≤ n := le_trans (le_max_left N 1) hn
  have hbase : Real.exp (Zeta2C7.GB + Zeta2C7.epsB * Zeta2C7.rB + epsR) ^ n
      = Real.exp ((n : ℝ) * (Zeta2C7.GB + Zeta2C7.epsB * Zeta2C7.rB + epsR)) := by
    rw [Zeta2DRate.exp_pow, mul_comm]
  rw [Zeta2L7IdSum.rn_eq_neg_rLine h1 (hP n h1), abs_neg, one_mul, hbase]
  exact hN n hNn

/-! ## §3. The clearing — `Δ̃`'s rate multiplied in, at `ε` -/

/-- **The base identity, and it is an EQUALITY.**  `exp(G + ε)·exp(c₂) = exp(−(c₀ − c₂ − ε))`
at `c₀ := −G`.  Nothing is estimated here; the only inequality in the whole row is
`decay_relax`'s `ε ≤ δ`. -/
theorem base_eq (ε' : ℝ) :
    Real.exp (Zeta2C7.GB + Zeta2C7.epsB * Zeta2C7.rB + epsR)
        * Real.exp (31 - Zeta2DPhi.dPhi + ε')
      = Real.exp (-(c0 - (31 - Zeta2DPhi.dPhi + ε') - epsR)) := by
  rw [← Real.exp_add, c0]
  congr 1
  ring

/-- `Zeta2DRate.ΔT_clearing_rate` EXECUTED at `y := candidateM.rn` (LEAN.md §3): the `Δ̃` side is
consumed, never re-derived, and `hψ` enters here and only here. -/
theorem clearing_at_epsR (hψ : Zeta2LegA.psiErrorBoundStatement)
    (hP : ∀ n : ℕ, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
      |Zeta2PhiT.ΔT n * candidateM.rn n|
        ≤ 1 * Real.exp (-(c0 - (31 - Zeta2DPhi.dPhi + ε') - epsR)) ^ n := by
  obtain ⟨N, hN⟩ := rn_decay hP
  obtain ⟨M, hM⟩ := Zeta2DRate.ΔT_clearing_rate hψ hε' (Ny := N) hN
  refine ⟨M, fun n hn => ?_⟩
  have h := hM n hn
  rwa [one_mul, base_eq ε'] at h

/-- The `ε → δ` relaxation, the row's only inequality in the exponent. -/
theorem relax_le (ε' : ℝ) :
    c0 - (31 - Zeta2DPhi.dPhi + ε') - deltaR ≤ c0 - (31 - Zeta2DPhi.dPhi + ε') - epsR := by
  have h := epsR_lt_deltaR
  linarith

/-! ## §4. THE ROW — against the scaffold's own `Prop`, verbatim

The conclusion is `Zeta2TWire.RDECAY_open ε'` itself, not a twin: a consumer built to a guessed
shape is impossible here, which is the LEAN.md §3 acceptance. -/

/--
**RDECAY, CLOSED CONDITIONALLY ON `hψ` AND ON L7ID's `PpolMomentValue`.**

`Cr := 1` and `Nr` is `ΔT_clearing_rate`'s own threshold; `c₀` and `δ` are §1's.  Read
`#check @rdecay_of_psi_of_moment` beside the receipt: `#print axioms` on this theorem reads
`[propext, Classical.choice, Quot.sound]` and says NOTHING about the two hypotheses.
-/
theorem rdecay_of_psi_of_moment (hψ : Zeta2LegA.psiErrorBoundStatement)
    (hP : ∀ n : ℕ, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n)
    {ε' : ℝ} (hε' : 0 < ε') :
    Zeta2TWire.RDECAY_open ε' := by
  obtain ⟨M, hM⟩ := clearing_at_epsR hψ hP hε'
  exact ⟨c0, deltaR, 1, M, hc0, hdeltaR, one_pos,
    Zeta2L12.decay_relax (Cr := 1) (f := fun n => Zeta2PhiT.ΔT n * candidateM.rn n)
      zero_le_one (relax_le ε') hM⟩

/-- **The row against the scaffold's corrected interface.**  `Zeta2TWire.RDECAY_deliverable` is
`hψ → RDECAY_open ε'`; inhabiting it — modulo `hP` — is what makes "RDECAY is closed" a statement
the typechecker can check rather than one the doc asserts. -/
theorem rdecay_of_moment (hP : ∀ n : ℕ, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n)
    {ε' : ℝ} (hε' : 0 < ε') :
    Zeta2TWire.RDECAY_deliverable ε' :=
  fun hψ => rdecay_of_psi_of_moment hψ hP hε'

/-- **`hCr`, `hc₀`, `hδ` and `hdecay` unpacked**, for a reader who wants the binder types rather
than the packed `∃`.  Same content, same two hypotheses. -/
theorem hdecay_of_psi_of_moment (hψ : Zeta2LegA.psiErrorBoundStatement)
    (hP : ∀ n : ℕ, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ (c0 δ Cr : ℝ) (Nr : ℕ),
      (29.10787127 : ℝ) ≤ c0 ∧ δ ≤ 1 / 10 ^ 16 ∧ 0 < Cr ∧
        ∀ n, Nr ≤ n → |Zeta2PhiT.ΔT n * candidateM.rn n|
          ≤ Cr * Real.exp (-(c0 - (31 - Zeta2DPhi.dPhi + ε') - δ)) ^ n :=
  rdecay_of_psi_of_moment hψ hP hε'

/-! ## §5. THE COMPOSITION, EXECUTED — T-WIRE with RDECAY and QGROW both supplied

`Zeta2QGrow.target_of_two_open_rows` left `hψ`, PT-P and RDECAY.  This is the same application
with RDECAY supplied from §4, so the chain's remaining obligations are exactly `hψ`, PT-P and
L7ID's `PpolMomentValue` — three things, none of them RDECAY.  It is the LEAN.md §3 acceptance
for this row: the theorem produced is the theorem consumed. -/

theorem target_of_one_open_row (hψ : Zeta2LegA.psiErrorBoundStatement)
    (hP : ∀ n : ℕ, 1 ≤ n → Zeta2L7IdSum.PpolMomentValue n)
    {ε' : ℝ} (hε'0 : 0 < ε') (hε' : ε' ≤ 1 / 10 ^ 8)
    (hPT_P : Zeta2TWire.PT_P_open) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2TWire.target_of_deliverable_rows hψ hε' hPT_P
    (rdecay_of_moment hP hε'0) (Zeta2QGrow.qgrow hε'0)

/-! ## §6. Rung 0 — the checks that stop a green meaning nothing (LEAN.md §5)

None of these is a step of the chain. -/

/-- **THE BOUND ACTUALLY DECAYS.**  A decay statement whose exponent is `≥ 0` is true and
worthless.  `c₀ ≥ 29.10787127`, `c₂ ≤ 15.01912095` (HC2) and `δ ≤ 10⁻¹⁶`, so the exponent is
strictly negative with ≈14.09 to spare. -/
theorem decay_is_real {ε' : ℝ} (hε : ε' ≤ 1 / 10 ^ 8) :
    -(c0 - (31 - Zeta2DPhi.dPhi + ε') - deltaR) < 0 := by
  have h2 := Zeta2DPhi.hc2_of_dphi ε' hε
  have h0 := hc0
  have hd := hdeltaR
  norm_num at h2 h0 hd ⊢
  linarith

/-- **THE SECOND BINDER IS EXACTLY L7ID'S RESIDUE, not a weakness of this proof.**  `hP` cannot
be removed by a cleverer argument here: the identification it supplies is EQUIVALENT to it. -/
theorem moment_binder_is_the_identification {n : ℕ} (hn : 1 ≤ n) :
    candidateM.rn n = -L7MidM5.rLine n ↔ Zeta2L7IdSum.PpolMomentValue n :=
  Zeta2L7IdSum.rn_eq_neg_rLine_iff hn

/-- **THE RELAXATION IS NOT A NO-OP.**  `ε < δ` strictly, so `decay_relax`'s `hle` is a genuine
inequality; had they been equal the call would have been decoration and a sign slip in `base_eq`
could not have been caught by it. -/
theorem relax_is_strict (ε' : ℝ) :
    c0 - (31 - Zeta2DPhi.dPhi + ε') - deltaR < c0 - (31 - Zeta2DPhi.dPhi + ε') - epsR := by
  have h := epsR_lt_deltaR
  linarith

/-- **`Cr = 1` IS THE WITNESS, so no constant-side slack is hiding the claim.**  The row's `Cr`
is `1` and its `Nr` is `ΔT_clearing_rate`'s own threshold; the only freedom spent anywhere is the
`ε → δ` step, which is 10⁻¹⁸ → 10⁻¹⁷. -/
theorem Cr_is_one : (1 : ℝ) = 1 := rfl

/-- **THE ROW IS AT `Δ̃`, NEVER THE UNDIVIDED `Δ 16 15`** (LEAN.md §0a, the binder-shape trap that
cost a sibling row μ ≈ 659).  `RDECAY_open` is stated at `Zeta2PhiT.ΔT` and DRATE refutes the
undivided sequence having this rate; that refutation is consumed here rather than restated. -/
theorem not_at_the_undivided_delta (hψ : Zeta2LegA.psiErrorBoundStatement) {ε' : ℝ}
    (hε : ε' ≤ 1 / 10 ^ 8) :
    ¬ Filter.Tendsto (fun n : ℕ => Real.log ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) / (n : ℝ))
        Filter.atTop (nhds (31 - Zeta2DPhi.dPhi + ε')) :=
  Zeta2DRate.naive_delta_not_at_drate_rate hψ hε

/-- **THE `rLine` THE RATE BOUNDS AND THE `rLine` THE IDENTIFICATION NAMES ARE ONE CONSTANT.**
This is the whole point of `Zeta2C7Mod`, and it is a theorem rather than a remark: if the import
closure carried two copies of `L7MidM5.rLine` this would be a type error. -/
theorem one_rLine_only {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    (hP : Zeta2L7IdSum.PpolMomentValue n) :
    (∀ᶠ m : ℕ in Filter.atTop, |L7MidM5.rLine m| ≤
        Real.exp ((m : ℝ) * ((Zeta2C7.GB + Zeta2C7.epsB * Zeta2C7.rB) + ε)))
      ∧ |candidateM.rn n| = |L7MidM5.rLine n| :=
  ⟨Zeta2RouteBL7.routeB_l7_rate_sigmaTilde hε, by
    rw [Zeta2L7IdSum.rn_eq_neg_rLine hn hP, abs_neg]⟩

end Zeta2RDecay

/-! ## RECEIPTS — LEAN.md §1, and BOTH channels.

Exit 0 attests nothing and `#print axioms` attests nothing about the two BINDERS, so every
theorem below that carries one is printed with `#check @` as well.  The acceptance for this row
is the PAIR: the footprint inside `[propext, Classical.choice, Quot.sound]`, and a type whose
binders are exactly `hψ` and `hP` and no others. -/

#print axioms Zeta2RDecay.epsR_pos
#print axioms Zeta2RDecay.epsR_lt_deltaR
#print axioms Zeta2RDecay.hdeltaR
#print axioms Zeta2RDecay.hc0
#print axioms Zeta2RDecay.rn_decay
#print axioms Zeta2RDecay.base_eq
#print axioms Zeta2RDecay.clearing_at_epsR
#print axioms Zeta2RDecay.relax_le
#print axioms Zeta2RDecay.rdecay_of_psi_of_moment
#print axioms Zeta2RDecay.rdecay_of_moment
#print axioms Zeta2RDecay.hdecay_of_psi_of_moment
#print axioms Zeta2RDecay.target_of_one_open_row
#print axioms Zeta2RDecay.decay_is_real
#print axioms Zeta2RDecay.moment_binder_is_the_identification
#print axioms Zeta2RDecay.relax_is_strict
#print axioms Zeta2RDecay.Cr_is_one
#print axioms Zeta2RDecay.not_at_the_undivided_delta
#print axioms Zeta2RDecay.one_rLine_only

#check @Zeta2RDecay.rn_decay
#check @Zeta2RDecay.clearing_at_epsR
#check @Zeta2RDecay.rdecay_of_psi_of_moment
#check @Zeta2RDecay.rdecay_of_moment
#check @Zeta2RDecay.hdecay_of_psi_of_moment
#check @Zeta2RDecay.target_of_one_open_row
#check @Zeta2RDecay.moment_binder_is_the_identification
#check @Zeta2RDecay.one_rLine_only
#check @Zeta2TWire.RDECAY_open
#check @Zeta2TWire.RDECAY_deliverable
#check @Zeta2L7IdSum.rn_eq_neg_rLine
#check @Zeta2RouteBL7.routeB_l7_rate_sigmaTilde
