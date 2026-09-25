/-
# L12 at the REAL objects — `hu`, `hv`, `hmu` of `candidate_target_of_rates`, discharged

`Zeta2L9L11Instantiate.candidate_target_of_rates` concludes `¬ LiouvilleWith 5.0495243 zeta2`
from **17** named hypotheses.  Three of them are row L12's, and D3's dependency table graded
them "certified numerically" — the only row of the seventeen whose warrant was a Python
computation rather than a theorem:

* `hu : 0 < u`,  `hv : 0 ≤ v`,  `hmu : 1 + v / u < 5.0495243`,

in the vocabulary the criterion consumes, where `ρr = Real.exp (-u)` is the decay base and
`ρq = Real.exp v` the growth base.  **This file turns that certification into Lean theorems and
discharges all three, leaving 14.**  `Zeta2D4.L12_bound` did the arithmetic over `ℚ`; nothing
connected it to the `ℝ`-valued `u`/`v` the criterion actually quantifies over, and `ℚ → ℝ` is
not where the interest is.

## The collapse — the same SHAPE as C7's, for a different reason

C7 was priced for an `arctan`/`log` enclosure machine and found every argument rational, so the
sum folded exactly.  **L12's quantities are NOT rational and not reducible**: `u = C0 − C2̃ − δ`
and `v = C1 + C2̃`, where `C0` is a saddle value carrying twenty logarithms at rationals (that is
what C7 enclosed to 19 places), `C1` comes from the characteristic cubic's root moduli, and `C2̃`
is `γ₁ + γ₂ − d_φ̃` with `d_φ̃` a weighted digamma-difference density.  Every one is
transcendental.

**And L12 still needs no enclosure machinery, because it never has to look at them.**  The rate
bound is MONOTONE in both coordinates: a decay bound at base `exp(−u)` is also a decay bound at
base `exp(−u′)` for any `u′ ≤ u`, and a growth bound at `exp(v)` is one at `exp(v′)` for any
`v′ ≥ v` (`decay_relax` / `growth_relax` below).  So the transcendental rates are replaced by
RATIONAL LITERALS **before** L12's arithmetic runs, and `hu`, `hv`, `hmu` become `norm_num`
facts with no hypotheses at all.  The transcendental content stays where it belongs — in
`hdecay` and `hgrowth`, which are the rows that certify the rates.

## Precision — eight decimals, and it is not a choice

`Zeta2D4.L12_margin_is_tight` proves L12's margin is `9.4696e-9` in `μ` and that SEVEN decimal
places of enclosure fail.  The rational rates here are the archived constants rounded OUTWARD at
**eight** decimals (`uRate` down, `vRate` up), which is the first width that clears:

| | value | |
|---|---|---|
| exact `1 + v/(u−δ)` | `5.049524290530377` | margin `9.4696e-9` |
| at the 2026-09-10 8-decimal rates (`c2 ≤ 15.01912093`) | `5.049524294465938` | margin `5.5341e-9` |
| **at the re-cut rates below (`c2 ≤ 15.01912095`)** | `5.049524298759807` | margin `1.2402e-9` |
| at 7-decimal rates | `5.049524343188369` | **OVER by `4.3188e-8`** |

`L12_seven_decimals_insufficient` is that third row as a theorem.

## The 2026-09-18 re-cut of `c2` (row HC2)

`hc2 : c2 ≤ 15.01912093` was the archived `C2̃ = 15.019120927608038` rounded up at eight
decimals — leaving the row that must PROVE it (`d_φ̃ ≥ 31 − c2`) a room of `2.39e-9`, which
costs `N ≈ 395` exact terms per piece (`hc2_round_probe.out`).  `c2 ≤ 15.01912095` is the
loosest literal at which `μ` still clears (`…96` overshoots by `2.34e-9`), gives that row a
room of `2.24e-8`, and is what `Zeta2DPhi.hc2_of_dphi` now delivers.  The re-cut moves FOUR
things together — `hc2`'s literal in `uRate_le_certified`, `certified_le_vRate` and
`candidate_target_of_certified_constants`, and BOTH rate literals — and `L12_rational_gap` is
re-`norm_num`'d at the new pair.  **It also forced `uRate` to sixteen decimals**: at the old
"rounded down by a full ulp" convention `u = 14.08875031` gives `μ = 5.0495243016 > 5.0495243`
(the arm `falsify_l12_lega.sh` F), so `uRate` is now exactly `c0 − c2 − 1e-16` at the literal
enclosures, i.e. `14.0887503199999999`, with no ulp thrown away.  The `hδ` bound `1e-16` is
what that literal's last digits encode, and `uRate_le_certified` is `linarith` from it.

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox; Lean
never runs on the laptop (owner ruling 2026-09-07).
-/
import Zeta2L9L11Instantiate

namespace Zeta2L12

open Zeta2Defs

/-! ## §1. The certified rates, as rational literals

Outward-rounded at eight decimals from the archived constants of
`zeta2-integral-free.md` §0: `C0 = 29.107871270207490`, `C1 = 42.033615807966612`,
`C2̃ = 15.019120927608038`, route-B `δ = 9.94e-17`.

`uRate` is `29.10787127 − 15.01912095 − 1e-16 = 14.0887503199999999` EXACTLY — the three
literal enclosures `hc0`, `hc2`, `hδ` composed, with nothing rounded away.  Until the HC2 re-cut
it was `14.08875033`, rounded DOWN by a full unit in the last place (because `δ > 0` forbids
`14.08875034`); at `c2 ≤ 15.01912095` that convention would cost `2.9e-9` of a `1.24e-9`
margin and `L12_rational_gap` would be false (see the re-cut note above). -/

/-- **`u`, the certified decay rate, as a rational literal** — a LOWER bound for
`C0 − C2̃ − δ`, so relaxing the decay hypothesis to it is sound (`decay_relax`). -/
noncomputable def uRate : ℝ := 140887503199999999 / 10 ^ 16

/-- **`v`, the certified growth rate, as a rational literal** — an UPPER bound for `C1 + C2̃`,
so relaxing the growth hypothesis to it is sound (`growth_relax`).  `42.03361581 + 15.01912095`. -/
noncomputable def vRate : ℝ := 5705273676 / 10 ^ 8

/-- **`hu` at the certified rate.**  Discharges hypothesis 12 of 17. -/
theorem uRate_pos : 0 < uRate := by
  norm_num [uRate]

/-- **`hv` at the certified rate.**  Discharges hypothesis 13 of 17. -/
theorem vRate_nonneg : 0 ≤ vRate := by
  norm_num [vRate]

/--
**`hmu` at the certified rate — L12's whole content, kernel-checked.**  Discharges hypothesis
17 of 17.  `1 + 57.05273676/14.0887503199999999 = 5.049524298759807 < 5.0495243`, with
`1.2402e-9` of the `9.4696e-9` margin left after the outward rounding and the HC2 re-cut.
(Before the re-cut: `1 + 57.05273674/14.08875033 = 5.049524294465938`, margin `5.5341e-9`.)
-/
theorem L12_rational_gap : 1 + vRate / uRate < (5.0495243 : ℝ) := by
  have hu : (0 : ℝ) < uRate := uRate_pos
  rw [show (5.0495243 : ℝ) = 1 + 4.0495243 by norm_num, add_lt_add_iff_left,
    div_lt_iff₀ hu]
  norm_num [uRate, vRate]

/-! ## §2. Monotonicity of a rate bound — why the transcendental rates never appear

These two are the whole reason L12 needs no enclosure of `C0`, `C1` or `C2̃`.  They are stated
for an arbitrary sequence, because nothing about the candidate enters. -/

/--
**A decay bound relaxes DOWNWARD in the rate.**  If `|f n| ≤ Cr·exp(−u)ⁿ` past `Nr` and
`u′ ≤ u`, then the same bound holds at `u′`.  Applied with `u′ = uRate` a rational literal and
`u` the chain's certified transcendental rate.
-/
theorem decay_relax {Nr : ℕ} {Cr u u' : ℝ} {f : ℕ → ℝ} (hCr : 0 ≤ Cr) (hle : u' ≤ u)
    (h : ∀ n, Nr ≤ n → |f n| ≤ Cr * Real.exp (-u) ^ n) :
    ∀ n, Nr ≤ n → |f n| ≤ Cr * Real.exp (-u') ^ n := by
  intro n hn
  refine (h n hn).trans ?_
  have hb : Real.exp (-u) ≤ Real.exp (-u') := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_nonneg _) hb n) hCr

/--
**A growth bound relaxes UPWARD in the rate.**  If `|g n| ≤ Cq·exp(v)ⁿ` past `Nq` and `v ≤ v′`,
then the same bound holds at `v′`.
-/
theorem growth_relax {Nq : ℕ} {Cq v v' : ℝ} {g : ℕ → ℝ} (hCq : 0 ≤ Cq) (hle : v ≤ v')
    (h : ∀ n, Nq ≤ n → |g n| ≤ Cq * Real.exp v ^ n) :
    ∀ n, Nq ≤ n → |g n| ≤ Cq * Real.exp v' ^ n := by
  intro n hn
  refine (h n hn).trans ?_
  have hb : Real.exp v ≤ Real.exp v' := Real.exp_le_exp.mpr hle
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_nonneg _) hb n) hCq

/-! ## §3. The transport — from the chain's certified constants to the rational rates

These are the ONLY places the archived numbers appear, and each takes exactly the shape the
upstream row produces: a rational LOWER bound on `C0` (C7's `c7_hG`, which delivers 19 decimal
places against the 8 needed here), rational UPPER bounds on `C1` (L2/L3 off the certified
cubic) and on `C2̃` (`γ₁ + γ₂ − d_φ̃`, D5), and route B's certified slack `δ ≤ 1e-16`
(measured `9.94e-17`).  No LOWER bound on `C1` or `C2̃` is needed anywhere — `hv` is discharged
from the literal. -/

/-- `uRate` is below the certified `u = C0 − C2̃ − δ`, from the 8-decimal enclosures (and it is
EXACTLY their composition, so the `norm_num` fact is an equality read as `≤`). -/
theorem uRate_le_certified {c0 c2 δ : ℝ} (hc0 : (29.10787127 : ℝ) ≤ c0)
    (hc2 : c2 ≤ (15.01912095 : ℝ)) (hδ : δ ≤ 1 / 10 ^ 16) : uRate ≤ c0 - c2 - δ := by
  have h : (1 : ℝ) / 10 ^ 16 ≤ 29.10787127 - 15.01912095 - uRate := by
    norm_num [uRate]
  linarith

/-- `vRate` is above the certified `v = C1 + C2̃`, from the 8-decimal enclosures. -/
theorem certified_le_vRate {c1 c2 : ℝ} (hc1 : c1 ≤ (42.03361581 : ℝ))
    (hc2 : c2 ≤ (15.01912095 : ℝ)) : c1 + c2 ≤ vRate := by
  have h : (42.03361581 : ℝ) + 15.01912095 ≤ vRate := by norm_num [vRate]
  linarith

/-! ## §4. The headline, with L12 discharged — 17 hypotheses become 14

`candidate_target_at_certified_rates` IS the `example` that checks the discharge: it applies the
real `Zeta2L9L11Instantiate.candidate_target_of_rates`, so the kernel — not this docstring —
confirms that `uRate_pos`, `vRate_nonneg` and `L12_rational_gap` have exactly the types `hu`,
`hv` and `hmu` demand.  A drift on either side is an elaboration error at that application. -/

/--
**THE §5.1 TARGET AT THE CERTIFIED RATES.**  Every hypothesis of
`Zeta2L9L11Instantiate.candidate_target_of_rates` except L12's three, with the decay and growth
bases written as the rational literals `exp(−uRate)` and `exp(vRate)`.

Fourteen hypotheses remain, all of them other rows': `hrecq`/`hrecp` (L1, rows B1–B5),
`hΔne`/`hQ`/`hP` (A1–A4 / L10 clearing), `hN₁`/`hM₀`/`hα₃`/`hα₀`/`hrow` (D4-L4),
`hCr`/`hdecay` (C1–C7 + L7 + L8 + L10) and `hCq`/`hgrowth` (D1/L5 + L10).
-/
theorem candidate_target_at_certified_rates
    (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    {N₀ n₁ m₀ Nr Nq : ℕ} {Cr Cq : ℝ}
    (hrecq : ∀ n, N₀ ≤ n →
      α₀ n * ((candidateM.qn n : ℚ) : ℝ) + α₁ n * ((candidateM.qn (n + 1) : ℚ) : ℝ)
        + α₂ n * ((candidateM.qn (n + 2) : ℚ) : ℝ)
        + α₃ n * ((candidateM.qn (n + 3) : ℚ) : ℝ) = 0)
    (hrecp : ∀ n, N₀ ≤ n →
      α₀ n * ((candidateM.pn n : ℚ) : ℝ) + α₁ n * ((candidateM.pn (n + 1) : ℚ) : ℝ)
        + α₂ n * ((candidateM.pn (n + 2) : ℚ) : ℝ)
        + α₃ n * ((candidateM.pn (n + 3) : ℚ) : ℝ) = 0)
    (hΔne : ∀ n, Δ n ≠ 0)
    (hQ : ∀ n, (Q n : ℝ) = Δ n * ((candidateM.qn n : ℚ) : ℝ))
    (hP : ∀ n, (P n : ℝ) = Δ n * ((candidateM.pn n : ℚ) : ℝ))
    (hN₁ : N₀ ≤ n₁) (hM₀ : N₀ ≤ m₀)
    (hα₃ : ∀ n, n₁ ≤ n → α₃ n ≠ 0) (hα₀ : ∀ n, m₀ ≤ n → α₀ n ≠ 0)
    (hrow : ∃ k, m₀ ≤ k ∧ candidateM.qn k ≠ 0)
    (hCr : 0 < Cr)
    (hdecay : ∀ n, Nr ≤ n → |Δ n * candidateM.rn n| ≤ Cr * Real.exp (-uRate) ^ n)
    (hCq : 0 < Cq)
    (hgrowth : ∀ n, Nq ≤ n → |(Q n : ℝ)| ≤ Cq * Real.exp vRate ^ n) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2L9L11Instantiate.candidate_target_of_rates Q P Δ α₀ α₁ α₂ α₃ hrecq hrecp hΔne hQ hP
    hN₁ hM₀ hα₃ hα₀ hrow hCr uRate_pos vRate_nonneg hdecay hCq hgrowth L12_rational_gap

/--
**THE SAME, AT THE CHAIN'S OWN CONSTANTS.**  The decay and growth rows produce their bounds at
the transcendental `u = C0 − C2̃ − δ` and `v = C1 + C2̃`, not at rational literals; this is the
form that consumes them directly, with §2's monotonicity doing the transport and §3's
enclosures — the four numbers upstream rows actually certify — as the only arithmetic input.

Still fourteen hypotheses on the chain's side; the four enclosure facts are C7's, L2/L3's, D5's
and route B's outputs, not new obligations.  `hc2` at `15.01912095` is delivered by
`Zeta2DPhi.hc2_of_dphi` (row HC2, 2026-09-18) for `c2 := 31 − d_φ̃ + ε'`, `ε' ≤ 1e-8`;
`Zeta2Hc2.candidate_target_of_hc2` is this theorem with that binder discharged.
-/
theorem candidate_target_of_certified_constants
    (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    {N₀ n₁ m₀ Nr Nq : ℕ} {Cr Cq c0 c1 c2 δ : ℝ}
    (hc0 : (29.10787127 : ℝ) ≤ c0) (hc1 : c1 ≤ (42.03361581 : ℝ))
    (hc2 : c2 ≤ (15.01912095 : ℝ)) (hδ : δ ≤ 1 / 10 ^ 16)
    (hrecq : ∀ n, N₀ ≤ n →
      α₀ n * ((candidateM.qn n : ℚ) : ℝ) + α₁ n * ((candidateM.qn (n + 1) : ℚ) : ℝ)
        + α₂ n * ((candidateM.qn (n + 2) : ℚ) : ℝ)
        + α₃ n * ((candidateM.qn (n + 3) : ℚ) : ℝ) = 0)
    (hrecp : ∀ n, N₀ ≤ n →
      α₀ n * ((candidateM.pn n : ℚ) : ℝ) + α₁ n * ((candidateM.pn (n + 1) : ℚ) : ℝ)
        + α₂ n * ((candidateM.pn (n + 2) : ℚ) : ℝ)
        + α₃ n * ((candidateM.pn (n + 3) : ℚ) : ℝ) = 0)
    (hΔne : ∀ n, Δ n ≠ 0)
    (hQ : ∀ n, (Q n : ℝ) = Δ n * ((candidateM.qn n : ℚ) : ℝ))
    (hP : ∀ n, (P n : ℝ) = Δ n * ((candidateM.pn n : ℚ) : ℝ))
    (hN₁ : N₀ ≤ n₁) (hM₀ : N₀ ≤ m₀)
    (hα₃ : ∀ n, n₁ ≤ n → α₃ n ≠ 0) (hα₀ : ∀ n, m₀ ≤ n → α₀ n ≠ 0)
    (hrow : ∃ k, m₀ ≤ k ∧ candidateM.qn k ≠ 0)
    (hCr : 0 < Cr)
    (hdecay : ∀ n, Nr ≤ n → |Δ n * candidateM.rn n| ≤ Cr * Real.exp (-(c0 - c2 - δ)) ^ n)
    (hCq : 0 < Cq)
    (hgrowth : ∀ n, Nq ≤ n → |(Q n : ℝ)| ≤ Cq * Real.exp (c1 + c2) ^ n) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  candidate_target_at_certified_rates Q P Δ α₀ α₁ α₂ α₃ hrecq hrecp hΔne hQ hP hN₁ hM₀
    hα₃ hα₀ hrow hCr
    (decay_relax hCr.le (uRate_le_certified hc0 hc2 hδ) hdecay) hCq
    (growth_relax hCq.le (certified_le_vRate hc1 hc2) hgrowth)

/-! ## §5. Edges — LEAN.md §5

Four hypotheses in this corpus have been found Lean-vacuous or wrong-but-green.  Each theorem
below makes one such reading a positive fact, so nobody can simplify the hypothesis away without
turning a green file red. -/

/--
**`hu : 0 < u` IS LOAD-BEARING, AND `hmu` IS LEAN-VACUOUS WITHOUT IT.**  At `u = 0` Lean's
junk-value convention gives `v / 0 = 0`, so `1 + v/0 = 1 < 5.0495243` holds **for every `v`,
however large**.  `hmu` alone therefore constrains nothing: an instantiation at `u = 0` would
satisfy it while the underlying decay rate `exp(−0) = 1` is no decay at all.  This is the
`liouville_denominator_zero_vacuous` pattern one level up, and it is the reason
`candidate_target_of_rates` carries `hu` separately rather than deriving it.
-/
theorem hmu_is_vacuous_at_u_zero (v : ℝ) : 1 + v / 0 < (5.0495243 : ℝ) := by
  rw [div_zero]
  norm_num

/--
**`hv : 0 ≤ v` IS NOT IMPLIED BY `hu` AND `hmu`.**  Here is a witness pair satisfying both while
`v < 0`.  So `hv` cannot be dropped as redundant — it is what supplies `1 ≤ ρq`, which L11's
three-wide growth window needs (`Zeta2L9L11.growth_window_needs_one_le`).
-/
theorem hv_not_implied_by_hu_hmu :
    ∃ u v : ℝ, 0 < u ∧ 1 + v / u < (5.0495243 : ℝ) ∧ v < 0 :=
  ⟨1, -1, by norm_num, by norm_num, by norm_num⟩

/--
**SEVEN decimal places do not clear, over `ℝ`.**  `Zeta2D4.L12_margin_is_tight` proves this over
`ℚ`; the criterion quantifies over `ℝ`, and a margin argument that only holds in the rationals
would attest nothing about it.  Same numbers, `ℝ`-valued: the identical arithmetic at
`C0 ≥ 29.1078712`, `C1 ≤ 42.0336159`, `C2̃ ≤ 15.0191210` overshoots by `4.3188e-8`.
-/
theorem L12_seven_decimals_insufficient :
    ¬ (1 + ((42.0336159 : ℝ) + 15.0191210) / (29.1078712 - 15.0191210)
        < (5.0495243 : ℝ)) := by
  norm_num

/--
**THE ARCHIVED `δ_max` IS ROUNDED THE WRONG WAY, AND AT IT THE BOUND FAILS.**
`zeta2-integral-free.md` §0 records `δ_max = 3.2945884120e−8`; the exact threshold is
`3.2945883555e−8`, so the archived value is rounded UP in its ninth significant digit and lies
`5.65e−16` ABOVE the largest slack that still clears `5.0495243`.  At the archived value the
inequality is FALSE (by `1.62e−16`) — a wrong-but-invisible number of exactly the class §5
warns about.

**Harmless where it stands**, because route B's certified `δ = 9.94e−17` is eight orders of
magnitude below either figure and nothing in the chain consumes `δ_max`.  Committed as a
theorem so that if anything ever does, it is a red file rather than a plausible number.
-/
theorem archived_delta_max_overshoots_the_threshold :
    ¬ (1 + ((42.033615807966612 : ℝ) + 15.019120927608038) /
        (29.107871270207490 - 15.019120927608038 - 32945884120 / 10 ^ 18)
      < (5.0495243 : ℝ)) := by
  norm_num

/--
**The restore control for the theorem above** (LEAN.md §6 — a check that cannot go the other way
attests nothing).  One digit below the archived value, at `δ = 3.2945883e−8`, the identical
arithmetic CLEARS.  So the failure above is attributable to `δ_max`'s ninth digit and not to a
mistyped constant elsewhere in the expression.
-/
theorem delta_below_the_threshold_clears :
    1 + ((42.033615807966612 : ℝ) + 15.019120927608038) /
        (29.107871270207490 - 15.019120927608038 - 32945883 / 10 ^ 15)
      < (5.0495243 : ℝ) := by
  norm_num

/--
**The archived constants themselves, over `ℝ`.**  `Zeta2D4.L12_archived` in the criterion's own
number system, at route B's measured `δ = 9.94e−17`: `μ̃ = 5.049524290530377`.
-/
theorem L12_archived_real :
    1 + ((42.033615807966612 : ℝ) + 15.019120927608038) /
        (29.107871270207490 - 15.019120927608038 - 994 / 10 ^ 19) < (5.0495243 : ℝ) := by
  norm_num

/-! ## §6. Receipts — LEAN.md §1: exit 0 attests nothing, `#print axioms` does.

`Zeta2Target.lean`'s deliberate `sorry` is not in this file's dependency graph: nothing here
imports it. -/

#print axioms uRate_pos
#print axioms vRate_nonneg
#print axioms L12_rational_gap
#print axioms decay_relax
#print axioms growth_relax
#print axioms uRate_le_certified
#print axioms certified_le_vRate
#print axioms candidate_target_at_certified_rates
#print axioms candidate_target_of_certified_constants
#print axioms hmu_is_vacuous_at_u_zero
#print axioms hv_not_implied_by_hu_hmu
#print axioms L12_seven_decimals_insufficient
#print axioms archived_delta_max_overshoots_the_threshold
#print axioms delta_below_the_threshold_clears
#print axioms L12_archived_real

end Zeta2L12
