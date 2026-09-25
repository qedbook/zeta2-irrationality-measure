/-
# Row DRATE — the `Δ̃` rate, in `hdecay`/`hgrowth`'s shape

`docs/future/zeta2-lean-chain.md`, row **DRATE**.  The row's theorem is

    ΔT_growth : ∃ NΔ, ∀ n ≥ NΔ, |ΔT n| ≤ Real.exp c2 ^ n     at   c2 = 31 − d_φ̃ + ε'

built from three landed inputs and ending in the EXECUTED application of
`Zeta2L9L11.clearing_rate` at `Δ := ΔT` (LEAN.md §3 — `clearing_rate` was proved, generic and
had NO caller until this file; a generic lemma with no caller is where a hypothesis mismatch
hides, and this corpus has a standing lesson that "a sound instrument nothing calls" proves
nothing about the call site).

## THE HYPOTHESIS THIS ROW INHERITS AND DOES NOT DISCHARGE

Every theorem here that mentions `hψ` carries **leg B's standing ψ-error hypothesis** —
`Zeta2LegA.psiErrorBoundStatement`, `MediumPNT`'s rate on Chebyshev's `ψ`.  It is proved on
`PrimeNumberTheoremAnd` (toolchain `v4.32.2`) with an archived axiom receipt and is **NOT proved
on this toolchain**.  PT-RATE inherits it; this row inherits it from PT-RATE *and* from leg A,
which is the same statement, so the chain still rests on ONE external citation and not two.
**This row adds no hypothesis and discharges none.**  RDECAY and QGROW inherit it in turn.

## The three inputs, by name

* `Zeta2LegA.legA_candidate_from_psi` — `log(D(16n)·D(15n))/n → 31`.
* `Zeta2PhiTRate.tendsto_log_PhiT_div` — `log Φ̃ₙ/n → d_φ̃` (row PT-RATE, closed 2026-09-15).
* `Zeta2PhiT.ΔT` / `ΔT_pos` / `Δ_eq_lcmUpto` — row PT-DEF's definition and its `ℕ`-cast seam
  (`Δ 16 15 n = lcmUpto (16n) · lcmUpto (15n)` by `rfl`, a LANDED theorem, not a claim).
* `Zeta2DPhi.hc2_of_dphi` / `d_phi_ge_slack` — row HC2, closed 2026-09-18.  **`c2` is stated in
  HC2's shape (`31 − dPhi + ε'`, `ε' ≤ 1e-8`), never as a re-derived literal**, so RDECAY and
  QGROW need no bridge.  `ΔT_growth_hc2` hands them the pair.

## The `Tendsto → eventual bound` conversion

`Zeta2StarB1.star_growth_bound_eventual` was the cell's cited pattern; it turned out to be a
Poincaré-recurrence bound, not a limit conversion, so the conversion is written here directly
from `Filter.Tendsto.eventually` + `gt_mem_nhds` (stable API — LEAN.md §8), and `exp_pow`
replaces `Real.exp_nat_mul`, whose spelling has drifted.

## Containment — the substitution nothing in the types would refuse

`Zeta2PhiT.hDne_does_not_pin_Delta` proves the chain's `hΔne` binder holds at the NAIVE
`Δ 13 16` too (the clearing that yields μ ≈ 659).  A rate theorem stated at the un-divided
`Δ 16 15` would type-check just as well, so `naive_delta_not_at_drate_rate` REFUTES it in Lean:
the un-divided sequence's rate is 31, DRATE's is `31 − d_φ̃ + ε' ≤ 15.01912095`, and the two
cannot both be the limit.  `drate_rate_lt_31` pins the gap as a number.

## What was RE-DERIVED here and what was taken on trust

A census entry right about one consumer can be wrong about the next, so:

* **Re-derived (executed, not cited):** that `Zeta2L9L11.clearing_rate`'s hypotheses are
  dischargeable at `Δ := ΔT` (§5 — it had never been called); that leg A's hypothesis and
  PT-RATE's spelled-out `hψ` are the SAME statement (they unify in `tendsto_log_ΔT_div`); that
  `Δ 16 15 n` is leg A's `lcmUpto` product after the cast (`Δ_cast_eq`); that `Zeta2DPhi.dPhi`
  is PT-RATE's limit point (`tendsto_log_ΔT_div` type-checks at it).
* **Taken on trust (landed elsewhere, receipts archived there):** PT-RATE's limit, HC2's
  `d_phi_ge_slack` / `hc2_of_dphi`, PT-DEF's `ΔT_pos` / `Δ_eq_lcmUpto`, leg A's limit, and leg
  B's ψ-error discharge on `PrimeNumberTheoremAnd` (§ the inherited hypothesis above).
* **Cell claim CORRECTED:** the chain doc's DRATE cell cited
  `Zeta2StarB1.star_growth_bound_eventual` as carrying the `Tendsto → ∀ n ≥ N` conversion.  It
  does not — it is a Poincaré-recurrence bound and contains no limit conversion.  §4 writes the
  conversion directly; the cost was ~10 lines, not a re-plan.

The cell's own cheap probe — `clearing_rate` applied to leg A ALONE, the `Φ̃`-free version —
was run first and elaborated clean; it is subsumed by `ΔT_clearing_rate` and not kept as a
separate file (LEAN.md §10: what this file regenerates is not preserved twice).

Probe: `sh run_probe.sh Zeta2DRate.lean`.  Falsifier: `sh falsify_drate.sh`.
Lean never runs on the laptop (owner rule 2026-09-07).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732.
-/
import Zeta2Arith
import Zeta2PhiT
import Zeta2PhiTRate
import Zeta2DPhi
import Zeta2LegA
import Zeta2L9L11

open Filter
open scoped Topology

namespace Zeta2DRate

open Zeta2PhiT (ΔT PhiT)

/-! ## §1. Two API-stable helpers

LEAN.md §8: assume drift.  `Real.exp_nat_mul`'s spelling has moved; this induction has not. -/

/-- `exp c ^ m = exp (c * m)`, by induction rather than by a remembered lemma name. -/
theorem exp_pow (c : ℝ) : ∀ m : ℕ, Real.exp c ^ m = Real.exp (c * m) := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      push_cast
      ring_nf

/-- **The `ℕ`-cast seam the cell's grade names.**  `Δ 16 15 n` is leg A's product of `lcmUpto`s,
cast once.  The `ℕ`-level identity is PT-DEF's landed `Zeta2PhiT.Δ_eq_lcmUpto` (`rfl`). -/
theorem Δ_cast_eq (n : ℕ) :
    ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ)
      = (Nat.lcmUpto (16 * n) : ℝ) * (Nat.lcmUpto (15 * n) : ℝ) := by
  rw [Zeta2PhiT.Δ_eq_lcmUpto]
  push_cast
  ring

/-! ## §2. `log Δ̃ₙ = log(D(16n)·D(15n)) − log Φ̃ₙ`

The only place the quotient in PT-DEF's `ΔT` is opened.  Both factors are nonzero by landed
theorems (`Zeta2Arith.Δ_ne_zero`, `Zeta2PhiT.PhiT_cast_ne_zero`), so `Real.log_div` applies
with no side condition left over. -/

theorem log_ΔT_eq (n : ℕ) :
    Real.log (ΔT n)
      = Real.log ((Nat.lcmUpto (16 * n) : ℝ) * (Nat.lcmUpto (15 * n) : ℝ))
        - Real.log ((PhiT n : ℕ) : ℝ) := by
  unfold Zeta2PhiT.ΔT
  rw [Real.log_div (Nat.cast_ne_zero.mpr (Zeta2Arith.Δ_ne_zero 16 15 n))
      (Zeta2PhiT.PhiT_cast_ne_zero n), Δ_cast_eq]

/-! ## §3. THE ROW'S LIMIT — `log Δ̃ₙ / n → 31 − d_φ̃`

Leg A minus PT-RATE.  **Both take the SAME `hψ`** (`Zeta2LegA.psiErrorBoundStatement` unfolds to
exactly PT-RATE's spelled-out hypothesis), so the composition costs one citation, not two. -/

theorem tendsto_log_ΔT_div (hψ : Zeta2LegA.psiErrorBoundStatement) :
    Tendsto (fun n : ℕ => Real.log (ΔT n) / (n : ℝ)) atTop (𝓝 (31 - Zeta2DPhi.dPhi)) := by
  have hA := Zeta2LegA.legA_candidate_from_psi hψ
  have hB : Tendsto (fun n : ℕ => Real.log (PhiT n) / (n : ℝ)) atTop (𝓝 Zeta2DPhi.dPhi) :=
    Zeta2PhiTRate.tendsto_log_PhiT_div hψ
  refine (hA.sub hB).congr fun n => ?_
  rw [log_ΔT_eq, sub_div]

/-! ## §4. THE ROW'S THEOREM — the `Tendsto → ∀ n ≥ N` conversion, at HC2's `c2` -/

/--
**DRATE.**  `∃ NΔ, ∀ n ≥ NΔ, |Δ̃ₙ| ≤ exp(c2)^n` at `c2 = 31 − d_φ̃ + ε'`.

**INHERITED, NOT DISCHARGED:** `hψ` is leg B's standing ψ-error hypothesis, proved on
`PrimeNumberTheoremAnd` from `MediumPNT` and **not on this toolchain**.

`0 < ε'` is load-bearing and not cosmetic: the conversion needs the limit STRICTLY below the
rate, and at `ε' = 0` the statement is a claim about the limit point itself, which a `Tendsto`
does not give.  `NΔ` is `max N 1` because `log/n` says nothing at `n = 0`
(`Zeta2LegA.legA_at_zero_is_junk`: the sequence's value there is `0`, not `31`).
-/
theorem ΔT_growth (hψ : Zeta2LegA.psiErrorBoundStatement) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ NΔ : ℕ, ∀ n : ℕ, NΔ ≤ n →
      |ΔT n| ≤ Real.exp (31 - Zeta2DPhi.dPhi + ε') ^ n := by
  have h := tendsto_log_ΔT_div hψ
  have hlt : (31 - Zeta2DPhi.dPhi : ℝ) < 31 - Zeta2DPhi.dPhi + ε' := by linarith
  have hev := h.eventually (gt_mem_nhds hlt)
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have h0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hpos : (0 : ℝ) < ΔT n := Zeta2PhiT.ΔT_pos n
  have hkey : Real.log (ΔT n) / (n : ℝ) * (n : ℝ) = Real.log (ΔT n) := by field_simp
  have hmul := mul_lt_mul_of_pos_right (hN n hnN) h0
  rw [hkey] at hmul
  calc |ΔT n| = ΔT n := abs_of_pos hpos
    _ = Real.exp (Real.log (ΔT n)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp ((31 - Zeta2DPhi.dPhi + ε') * (n : ℝ)) := Real.exp_le_exp.mpr hmul.le
    _ = Real.exp (31 - Zeta2DPhi.dPhi + ε') ^ n := (exp_pow _ _).symm

/--
**DRATE in HC2's shape, as one object.**  The growth bound AND `hc2 : c2 ≤ 15.01912095` for the
same `c2`, so `Zeta2L12.candidate_target_of_certified_constants`' `hc2` binder and its `hgrowth`
binder are filled from ONE theorem with no bridge between them (HC2's own report: "DRATE
inherits `hc2_of_dphi`'s shape, so RDECAY's `ε' = 4e-17` fits").
-/
theorem ΔT_growth_hc2 (hψ : Zeta2LegA.psiErrorBoundStatement) {ε' : ℝ}
    (hε' : 0 < ε') (hε : ε' ≤ 1 / 10 ^ 8) :
    31 - Zeta2DPhi.dPhi + ε' ≤ (15.01912095 : ℝ)
      ∧ ∃ NΔ : ℕ, ∀ n : ℕ, NΔ ≤ n →
          |ΔT n| ≤ Real.exp (31 - Zeta2DPhi.dPhi + ε') ^ n :=
  ⟨Zeta2DPhi.hc2_of_dphi ε' hε, ΔT_growth hψ hε'⟩

/-! ## §5. THE ACCEPTANCE — `clearing_rate` EXECUTED at `Δ := ΔT`

LEAN.md §3.  `Zeta2L9L11.clearing_rate` is proved, generic, and had no caller before this file.
`hCΔ`, `hρΔ` and `hΔ` are discharged here from landed theorems; `hy` is left exactly as RDECAY
and QGROW will supply it (`y := rn`, with their own decay/growth rate), which is the shape the
consumers produce (LEAN.md §3's corollary).  The `max Ny NΔ` threshold is `clearing_rate`'s own,
unmodified — the second of the two seams the cell's grade names. -/

theorem ΔT_clearing_rate (hψ : Zeta2LegA.psiErrorBoundStatement) {ε' : ℝ} (hε' : 0 < ε')
    {y : ℕ → ℝ} {Cy ρy : ℝ} {Ny : ℕ}
    (hy : ∀ n, Ny ≤ n → |y n| ≤ Cy * ρy ^ n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |ΔT n * y n| ≤ Cy * 1 * (ρy * Real.exp (31 - Zeta2DPhi.dPhi + ε')) ^ n := by
  obtain ⟨NΔ, hΔ⟩ := ΔT_growth hψ hε'
  exact ⟨max Ny NΔ, Zeta2L9L11.clearing_rate (CΔ := 1) (ρΔ := Real.exp (31 - Zeta2DPhi.dPhi + ε'))
    (by norm_num) (Real.exp_nonneg _) hy (fun n hn => by simpa using hΔ n hn)⟩

/-- The same application with the consumers' `hc2` carried alongside, so RDECAY and QGROW get
the clearing bound and the constant's certificate from one call. -/
theorem ΔT_clearing_rate_hc2 (hψ : Zeta2LegA.psiErrorBoundStatement) {ε' : ℝ}
    (hε' : 0 < ε') (hε : ε' ≤ 1 / 10 ^ 8)
    {y : ℕ → ℝ} {Cy ρy : ℝ} {Ny : ℕ}
    (hy : ∀ n, Ny ≤ n → |y n| ≤ Cy * ρy ^ n) :
    31 - Zeta2DPhi.dPhi + ε' ≤ (15.01912095 : ℝ)
      ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          |ΔT n * y n| ≤ Cy * 1 * (ρy * Real.exp (31 - Zeta2DPhi.dPhi + ε')) ^ n :=
  ⟨Zeta2DPhi.hc2_of_dphi ε' hε, ΔT_clearing_rate hψ hε' hy⟩

/-! ## §6. Containment — LEAN.md §5, and the binder trap as a REFUTATION

`Zeta2PhiT.hDne_does_not_pin_Delta` shows the chain's `hΔne` binder is satisfied by the naive
`Δ 13 16` as well, so nothing in the TYPES stops a rate theorem being stated at an un-divided
`Δ`.  These are the positive theorems that stop it. -/

/-- **The rate DRATE delivers is strictly below 31 — Φ̃ cut something.**  `d_φ̃ ≥ 15.98087906`
(HC2), so `c2 ≤ 15.01912095 < 31`.  A row whose `c2` came out at 31 would be leg A alone. -/
theorem drate_rate_lt_31 {ε' : ℝ} (hε : ε' ≤ 1 / 10 ^ 8) :
    31 - Zeta2DPhi.dPhi + ε' < (31 : ℝ) := by
  have h := Zeta2DPhi.hc2_of_dphi ε' hε
  norm_num at h ⊢
  linarith

/--
**THE FALSIFIER, AS A THEOREM: the un-divided `Δ 16 15` does NOT have DRATE's rate.**

This is the substitution nothing in the types would refuse — drop the `/Φ̃ₙ` from `ΔT` and every
statement above still type-checks.  It is refuted here: leg A pins the un-divided sequence's
limit at `31`, DRATE's rate is `≤ 15.01912095`, and a sequence has one limit.
-/
theorem naive_delta_not_at_drate_rate (hψ : Zeta2LegA.psiErrorBoundStatement) {ε' : ℝ}
    (hε : ε' ≤ 1 / 10 ^ 8) :
    ¬ Tendsto (fun n : ℕ => Real.log ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) / (n : ℝ)) atTop
        (𝓝 (31 - Zeta2DPhi.dPhi + ε')) := by
  intro h
  have hA : Tendsto (fun n : ℕ => Real.log ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) / (n : ℝ)) atTop
      (𝓝 31) := by
    refine (Zeta2LegA.legA_candidate_from_psi hψ).congr fun n => ?_
    rw [Δ_cast_eq]
  have heq : (31 : ℝ) = 31 - Zeta2DPhi.dPhi + ε' := tendsto_nhds_unique hA h
  have := drate_rate_lt_31 (ε' := ε') hε
  linarith

/-- **And the limit DRATE is stated at is not leg A's.**  The companion direction: `ΔT`'s own
rate is not `31`, so the division by `Φ̃ₙ` is not cosmetic. -/
theorem ΔT_rate_ne_31 (hψ : Zeta2LegA.psiErrorBoundStatement) :
    ¬ Tendsto (fun n : ℕ => Real.log (ΔT n) / (n : ℝ)) atTop (𝓝 31) := by
  intro h
  have heq : (31 - Zeta2DPhi.dPhi : ℝ) = 31 := tendsto_nhds_unique (tendsto_log_ΔT_div hψ) h
  have hd := Zeta2DPhi.d_phi_ge_slack
  norm_num at heq
  linarith

/-- **`0 < ε'` is load-bearing.**  At a rate BELOW the limit the eventual bound is false, and
that is why the row cannot be stated at `31 − d_φ̃ − ε'`: the same proof script applied there
would be proving something no `Tendsto` supports.  Stated as the positive fact that makes the
direction unambiguous — the limit is strictly above any such rate. -/
theorem below_limit_is_not_a_rate {ε' : ℝ} (hε' : 0 < ε') :
    (31 : ℝ) - Zeta2DPhi.dPhi - ε' < 31 - Zeta2DPhi.dPhi := by linarith

/-! ## §7. Receipts — LEAN.md §1: exit 0 attests nothing, `#print axioms` does.

The receipt that matters is on the EXECUTED APPLICATION (`ΔT_clearing_rate`), not only on the
pieces. -/

#print axioms exp_pow
#print axioms Δ_cast_eq
#print axioms log_ΔT_eq
#print axioms tendsto_log_ΔT_div
#print axioms ΔT_growth
#print axioms ΔT_growth_hc2
#print axioms ΔT_clearing_rate
#print axioms ΔT_clearing_rate_hc2
#print axioms drate_rate_lt_31
#print axioms naive_delta_not_at_drate_rate
#print axioms ΔT_rate_ne_31
#print axioms below_limit_is_not_a_rate

end Zeta2DRate
