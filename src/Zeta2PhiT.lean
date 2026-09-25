/-
# Row PT-DEF — `Φ̃` and `Δ̃` as Lean objects, and `hΔne` at `Δ̃`

`docs/future/zeta2-lean-chain.md` row **PT-DEF**.  The chain's top-level statement
(`Zeta2L9L11Instantiate.candidate_not_liouvilleWith`) binds `Δ : ℕ → ℝ` and five hypotheses on
it — `hΔne`, `hQ`, `hP`, `hdecay`, `hgrowth`.  This file builds the `Δ` those five must be at,
and discharges the first of them.

## WHICH `Δ` IS WHICH — read this before using anything below

There are now **three** distinct objects in this corpus whose names contain `Δ`, and they are not
interchangeable.  LEAN.md §0a's binder trap is exactly the failure of confusing them, and it has
already produced a wrong headline in this program once (`μ ≈ 659` instead of `5.0495`):

* `Zeta2Arith.Δ c₁ c₂ n : ℕ` — the LANDED naive clearing `D(c₁n)·D(c₂n)`, a **ℕ**, generic in
  `c₁ c₂`.  Not this row's object.  `Δ 13 16` is the one that yields `μ ≈ 659`.
* `Zeta2PhiT.ΔT n : ℝ` — **THIS ROW'S OBJECT**, `Δ̃ₙ = D(16n)·D(15n)/Φ̃ₙ`, a **ℝ**, with the
  profile clearing divided out.  It is what the headline's `C0 = 29.108` budget needs.
* the chain's bound variable `Δ : ℕ → ℝ`, which is instantiated at `ΔT` and at nothing else.

`ΔT` is NOT `Zeta2Arith.Δ` under another name and no `rfl` relates them: they differ in type and
in value.  The bridge is `ΔT_mul_PhiT`, proved below, and `ΔT_one_ne_naive` proves that at `n = 1`
`ΔT` already differs from the naive `Δ 13 16` — **while `hDne_does_not_pin_Delta` proves that the
binder `hΔne` is satisfied by BOTH.**  That theorem is the binder trap stated as a machine-checked
fact rather than as a warning: `hΔne` is a real obligation and a useless discriminator, so
discharging it says nothing about whether the chain is being run at the right `Δ`.  The rows that
DO pin the object are PT-QA/QB (`hQ`), PT-P (`hP`) and DRATE (`hdecay`/`hgrowth`).

## `φ̃` is DERIVED from the landed table, never retyped

LEAN.md §6: 26 rational triples transcribed by hand would compile unchanged with a mistyped digit.
`phiT` therefore reads `Zeta2Profile.candidateProfile` — the landed, gated table — through
`List.find?`, so there is no second copy of the data in this corpus to drift against the first.
The cross-check that the table is the RIGHT table is `phi_profile_probe.out`'s own `φ̃` column,
compared triple by triple in `../../tools/..`-free scratch at map time: **0 mismatches over the 34
primes of `PhiT 12`'s window.**

## The cutoff is `p² > 26n+1`, deliberately NOT the audit's `√(17n)`

`padicValNat_cTerm` (the landed atom PT-QA/QB consume) has `26n+1 < p²` as its hypothesis; the
audit's `γ₀` line is `p² > 17n`, which is WEAKER, so it admits primes for which the atom would
need its two-term Legendre form.  This row cuts `Φ̃` at the atom's line so PT-QA/QB never meet
that form, at an `o(n)` cost PT-RATE absorbs.  `cutoff_green`/`cutoff_red` and
`cutoff_difference_twelve` make the difference between the two lines a machine-checked fact at
`n = 12` rather than prose: the two windows differ by exactly `{17}` there.

## MEASURED, and it corrects a number PT-RATE's cell quotes

`phi_profile_probe.out`'s header line `log Φ̃/12 = 14.7207` is the **UNCUT** product, over every
prime the probe lists.  `PhiT 12` — this row's object, cut at `p² > 26n+1` — gives
`log (PhiT 12)/12 = 13.7314`.  The difference is exactly the discarded factor
`7 · 11² · 13² = 143143`, worth `0.9893`, and `13.7314 + 0.9893 = 14.7207` to four places.  A
PT-RATE probe that compares `Real.log (PhiT 12)` against `14.7207` would therefore RED on a
correct `PhiT`.  See the PT-DEF and PT-RATE cells.

## Receipts

`#print axioms` on every theorem at the foot (LEAN.md §1).  Falsifier suite:
`falsify_phit.sh`, archived to `out_phit_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox
`~/mathlib-current` — the toolchain the whole ζ(2) chain corpus elaborates against.  This is NOT
the repo's `tools/lean_probe.sh` / `lean_verify` pin (v4.16.0, the main tree's olean store), and
nothing here was checked under that pin; the Mathlib names above are as of `5aedf732` only.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.NormNum
import Zeta2Arith
import Zeta2Profile

namespace Zeta2PhiT

open Zeta2Profile

/-! ## `D` IS Mathlib's `Nat.lcmUpto`, and the free-in-Mathlib row is discharged here

The chain doc's *Free in Mathlib* table claims `ord_p (D k) = ⌊log_p k⌋` from
`Nat.factorization_lcmUpto`, and DRATE's cell claims `Nat.lcmUpto (16*n) * Nat.lcmUpto (15*n)` in
leg A IS `Zeta2Arith.Δ 16 15 n` *definitionally*.  Both are ASSERTIONS in the doc.  They are
proved here, by `rfl`, so that the next row inherits a theorem rather than a claim — and so that a
Mathlib rename of `lcmUpto` reds this file instead of silently rotting the doc.

`Nat.lcmUpto` is genuinely awkward to name: it lives in `Mathlib/NumberTheory/Chebyshev.lean`, but
inside an interleaved `namespace Nat` block (lines 205–265 of that file), so `Chebyshev.lcmUpto`
is an unknown identifier while its neighbour `Chebyshev.psi_eq_log_lcmUpto` IS `Chebyshev.`-
qualified.  `Zeta2LegA.lean`'s header recorded that after it cost a probe cycle; this file takes
the warning and pins it. -/

/-- `Zeta2Arith.D` and Mathlib's `Nat.lcmUpto` are the same definition: both are
`(Finset.Icc 1 k).lcm id`. -/
theorem D_eq_lcmUpto (k : ℕ) : Zeta2Arith.D k = Nat.lcmUpto k := rfl

/-- DRATE's cell asserts this is definitional.  It is. -/
theorem Δ_eq_lcmUpto (c₁ c₂ n : ℕ) :
    Zeta2Arith.Δ c₁ c₂ n = Nat.lcmUpto (c₁ * n) * Nat.lcmUpto (c₂ * n) := rfl

/-- `D k = ∏_{p ≤ k} p ^ ⌊log_p k⌋` — free in Mathlib, via `Nat.lcmUpto_eq_prod_pow_log`. -/
theorem D_eq_prod_pow_log (k : ℕ) :
    Zeta2Arith.D k = ∏ p ∈ Nat.primesLE k, p ^ Nat.log p k := by
  rw [D_eq_lcmUpto]
  exact Nat.lcmUpto_eq_prod_pow_log k

/-- `ord_p (D k) = ⌊log_p k⌋` — the chain doc's *Free in Mathlib* row, discharged.
Free via `Nat.factorization_lcmUpto`. -/
theorem factorization_D (k : ℕ) {p : ℕ} (hp : p.Prime) :
    (Zeta2Arith.D k).factorization p = Nat.log p k := by
  rw [D_eq_lcmUpto]
  exact Nat.factorization_lcmUpto k hp

/-! ## `φ̃` — the profile as a function, read off the LANDED table -/

/-- `φ̃ : ℚ → ℕ`.  `candidateProfile` stores `(a, b, v)` meaning `φ̃ = v` on `[a, b)`; `φ̃ = 0`
off the pieces.  The pieces are pairwise disjoint (`candidateProfile_valid` plus the table's own
ordering), so `find?` — first match wins — is the whole definition.

DERIVED, not retyped: the only copy of the 26 triples in this corpus is `Zeta2Profile`'s. -/
def phiT (x : ℚ) : ℕ :=
  match candidateProfile.find? (fun t => decide (t.1 ≤ x ∧ x < t.2.1)) with
  | some t => t.2.2.num.toNat
  | none => 0

/-- `φ̃` vanishes off the table, by construction. -/
theorem phiT_of_find_none {x : ℚ}
    (h : candidateProfile.find? (fun t => decide (t.1 ≤ x ∧ x < t.2.1)) = none) :
    phiT x = 0 := by
  unfold phiT
  rw [h]

/-- Below the first piece `φ̃ = 0`.  LEAN.md §5: the edge case compiles, so state it.
`1/15` is the smallest `a` in the table — a piece starting at `0` would have broken
`0 < k + a` at `k = 0` in leg B's block decomposition, which is why
`candidateProfile_valid`'s `0 < t.1` is load-bearing. -/
theorem phiT_zero : phiT 0 = 0 := by decide +kernel

/-! ## `Φ̃ₙ` — the profile clearing -/

/-- The primes `Φ̃ₙ` runs over: `p ≤ 15n` and **`p² > 26n+1`**, the landed atom's line. -/
def phiWindow (n : ℕ) : Finset ℕ :=
  (Nat.primesLE (15 * n)).filter (fun p => 26 * n + 1 < p ^ 2)

theorem prime_of_mem_phiWindow {n p : ℕ} (hp : p ∈ phiWindow n) : p.Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1

theorem sq_gt_of_mem_phiWindow {n p : ℕ} (hp : p ∈ phiWindow n) : 26 * n + 1 < p ^ 2 := by
  have := (Finset.mem_filter.mp hp).2
  simpa using this

/-- `Φ̃ₙ = ∏_{p ∈ window} p ^ φ̃({n/p})`. -/
def PhiT (n : ℕ) : ℕ :=
  ∏ p ∈ phiWindow n, p ^ phiT (Int.fract ((n : ℚ) / (p : ℚ)))

/-- `Φ̃ₙ > 0` — every factor is a positive prime power.  This is what `ΔT` needs to be well
defined and what PT-QA/QB/P need to divide by. -/
theorem PhiT_pos (n : ℕ) : 0 < PhiT n := by
  refine Finset.prod_pos ?_
  intro p hp
  exact pow_pos (prime_of_mem_phiWindow hp).pos _

theorem PhiT_ne_zero (n : ℕ) : PhiT n ≠ 0 := (PhiT_pos n).ne'

theorem PhiT_cast_ne_zero (n : ℕ) : ((PhiT n : ℕ) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (PhiT_ne_zero n)

/-! ## `Δ̃` and the binder `hΔne` -/

/-- **`Δ̃ₙ = D(16n)·D(15n)/Φ̃ₙ`** — the chain's `Δ`, and the only object the five binders may be
instantiated at.  Note `(16, 15)`, not the audit's `(13, 16)`: `phi_profile_probe.out` measures
0 divisibility failures below the Legendre line at `(16,15)` and 32 at `(13,16)`. -/
noncomputable def ΔT (n : ℕ) : ℝ :=
  ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) / ((PhiT n : ℕ) : ℝ)

/-- **The row's theorem: the binder `hΔne : ∀ n, Δ n ≠ 0` at `Δ := ΔT`.** -/
theorem ΔT_ne_zero : ∀ n, ΔT n ≠ 0 := fun n =>
  div_ne_zero (Nat.cast_ne_zero.mpr (Zeta2Arith.Δ_ne_zero 16 15 n)) (PhiT_cast_ne_zero n)

/-- The defining relation, in the form PT-QA/QB and PT-P consume: `Δ̃ₙ · Φ̃ₙ = D(16n)·D(15n)`.
This is the bridge between `ΔT` and the landed `Zeta2Arith.Δ`; there is no `rfl` between them. -/
theorem ΔT_mul_PhiT (n : ℕ) :
    ΔT n * ((PhiT n : ℕ) : ℝ) = ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) := by
  unfold ΔT
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self (PhiT_cast_ne_zero n), mul_one]

theorem ΔT_pos (n : ℕ) : 0 < ΔT n := by
  unfold ΔT
  apply div_pos
  · exact_mod_cast Zeta2Arith.Δ_pos 16 15 n
  · exact_mod_cast PhiT_pos n

/-! ## The `n = 12` probe — the cheapest possible falsification of a wrong `phiT`

`phi_profile_probe.out`'s per-prime table at `n = 12` is 34 primes in this row's window.  The
literal below was computed from `Zeta2Profile.candidateProfile` (NOT from the probe output) and
then cross-checked against the probe's own `φ̃` column: 0 mismatches.  Both sources must be wrong
in the same place for this to pass. -/

theorem phiWindow_twelve_card : (phiWindow 12).card = 34 := by decide +kernel

theorem PhiT_one : PhiT 1 = 5929 := by decide +kernel

theorem PhiT_twelve :
    PhiT 12 = 364510354998787330259435615810488279162463850115139447354799052309420243 := by
  decide +kernel

/-! ## §6 falsifier — the GREEN/RED pair, on one object

`Zeta2T1Eval.phi_eval_green`/`phi_eval_red` is the model: a red arm that shows a PROOF breaks is
not a red arm that shows a STATEMENT is false, and this corpus has been wrong about a binder
before by having only the first.  Both halves below are machine-checked. -/

/-- GREEN — the landed table's value at `{12/41}`. -/
theorem phiT_green : phiT (Int.fract ((12 : ℚ) / 41)) = 2 := by decide +kernel

/-- RED — the perturbed value is FALSE, proved rather than merely unprovable.  `falsify_phit.sh`
arm R2 flips `candidateProfile`'s value at this piece and the whole file must red. -/
theorem phiT_red : phiT (Int.fract ((12 : ℚ) / 41)) ≠ 3 := by decide +kernel

/-- GREEN — `17` is OUT of this row's window at `n = 12`: `17² = 289 ≤ 26·12+1 = 313`. -/
theorem cutoff_green : 17 ∉ phiWindow 12 := by decide +kernel

/-- RED — and it would be IN the audit's `√(17n)` window: `289 > 17·12 = 204`.  So the two
cutoffs are genuinely different windows, not two spellings of one. -/
theorem cutoff_red :
    17 ∈ (Nat.primesLE (15 * 12)).filter (fun p => 17 * 12 < p ^ 2) := by decide +kernel

/-- …and at `n = 12` they differ by EXACTLY `{17}` — the `o(n)` the row discards, made concrete. -/
theorem cutoff_difference_twelve :
    ((Nat.primesLE (15 * 12)).filter (fun p => 17 * 12 < p ^ 2)) \ phiWindow 12 = {17} := by
  decide +kernel

/-! ## The binder trap, as a theorem

LEAN.md §0a: `Δ 13 16` satisfies `hΔne`/`hQ`/`hP`'s TYPES and yields `μ ≈ 659`.  Here is the
`hΔne` half of that, machine-checked: the binder is satisfied by BOTH objects, and the objects are
different.  **Discharging `hΔne` is therefore not evidence that the chain is at the right `Δ`.** -/

/-- At `n = 1` the two clearings have the same numerator (`D 13 = D 15 = 360360`), so they differ
by exactly `Φ̃₁ = 5929`.  That is the whole content of this row's division. -/
theorem ΔT_one_ne_naive : ΔT 1 ≠ ((Zeta2Arith.Δ 13 16 1 : ℕ) : ℝ) := by
  have hEq : Zeta2Arith.Δ 16 15 1 = Zeta2Arith.Δ 13 16 1 := by decide +kernel
  have hne : ((Zeta2Arith.Δ 13 16 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Zeta2Arith.Δ_ne_zero 13 16 1)
  have hΔ : ΔT 1 = ((Zeta2Arith.Δ 13 16 1 : ℕ) : ℝ) / 5929 := by
    unfold ΔT
    rw [hEq, PhiT_one]
    norm_num
  rw [hΔ]
  intro h
  rw [div_eq_iff (by norm_num : (5929 : ℝ) ≠ 0)] at h
  exact hne (by linarith)

/-- **The trap.**  `hΔne`'s type is satisfied at the right `Δ` and at the wrong one alike. -/
theorem hDne_does_not_pin_Delta :
    (∀ n, ΔT n ≠ 0) ∧
      (∀ n, ((Zeta2Arith.Δ 13 16 n : ℕ) : ℝ) ≠ 0) ∧
      ΔT 1 ≠ ((Zeta2Arith.Δ 13 16 1 : ℕ) : ℝ) :=
  ⟨ΔT_ne_zero,
   fun n => Nat.cast_ne_zero.mpr (Zeta2Arith.Δ_ne_zero 13 16 n),
   ΔT_one_ne_naive⟩

/-! ## Receipts (LEAN.md §1) -/

#print axioms D_eq_lcmUpto
#print axioms Δ_eq_lcmUpto
#print axioms D_eq_prod_pow_log
#print axioms factorization_D
#print axioms phiT_of_find_none
#print axioms phiT_zero
#print axioms prime_of_mem_phiWindow
#print axioms sq_gt_of_mem_phiWindow
#print axioms PhiT_pos
#print axioms PhiT_ne_zero
#print axioms PhiT_cast_ne_zero
#print axioms ΔT_ne_zero
#print axioms ΔT_mul_PhiT
#print axioms ΔT_pos
#print axioms phiWindow_twelve_card
#print axioms PhiT_one
#print axioms PhiT_twelve
#print axioms phiT_green
#print axioms phiT_red
#print axioms cutoff_green
#print axioms cutoff_red
#print axioms cutoff_difference_twelve
#print axioms ΔT_one_ne_naive
#print axioms hDne_does_not_pin_Delta

end Zeta2PhiT
