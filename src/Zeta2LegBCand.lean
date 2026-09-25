/-
LEG B AT THE CANDIDATE — the instantiation module.

This file was `legb_glue.lean` until 2026-09-15: a fragment with no imports, consumable ONLY by
`lean_consolidate.py` when it built `Zeta2LegBComplete.lean`.  Row **PT-RATE** needs
`blockSum`/`pa`/`pb`/`pv`/`legB_candidate_from_psi` as an IMPORTABLE module, and the consolidated
monolith cannot serve: it inlines its own copy of `Zeta2Profile`, so importing it beside
`Zeta2PhiT` (which imports the real `Zeta2Profile`) is a duplicate-declaration error.  The only
alternative was a second `blockSum` in PT-RATE's file — the twin-definition trap this corpus has
already been bitten by twice (`Zeta2Moments.momI` vs `Zeta2Defs.momI`).  So the fragment became a
module, and `legb.consolidate` now takes it through the same `section NAME PATH` route as
`Zeta2LegB.lean` and `Zeta2Profile.lean`, which hoists these two imports away.  Nothing in the
body changed; `consolidate.sh --check` is the drift guard.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current).
-/

import Zeta2LegB
import Zeta2Profile

/-! ## THE INSTANTIATION — leg B's theorems applied at the CANDIDATE's real profile.

`Zeta2LegB` proves the general machinery; `Zeta2Profile` carries the candidate's 26 verified
triples. This section wires them together, so the statement is about the actual member
`α = (13,11,9,15), β = (0,2,4,26)` rather than an arbitrary profile.
-/

namespace Zeta2LegBCandidate

open Filter Zeta2Profile
open scoped Topology

/-- The `i`-th piece's left endpoint, as a real. -/
noncomputable def pa (i : Fin candidateProfile.length) : ℝ := ((candidateProfile.get i).1 : ℚ)
/-- The `i`-th piece's right endpoint, as a real. -/
noncomputable def pb (i : Fin candidateProfile.length) : ℝ := ((candidateProfile.get i).2.1 : ℚ)
/-- The `i`-th piece's weight, as a real. -/
noncomputable def pv (i : Fin candidateProfile.length) : ℝ := ((candidateProfile.get i).2.2 : ℚ)

/-- Each piece satisfies the hypotheses leg B's lemmas need — read off the verified table. -/
theorem piece_valid (i : Fin candidateProfile.length) :
    0 < pa i ∧ pa i ≤ pb i ∧ pb i ≤ pa i + 1 ∧ pb i ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := candidateProfile_valid _ (List.get_mem candidateProfile i)
  simp only [pa, pb]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2.le, by exact_mod_cast h4,
    by exact_mod_cast h3⟩

/-- **LEG B AT THE CANDIDATE.** Given per-piece convergence (which `legB_one_interval` supplies),
the weighted profile sum converges to `∑ᵢ vᵢ · S(aᵢ, bᵢ)` — the candidate's `d_φ̃`. -/
theorem legB_candidate
    (F : Fin candidateProfile.length → ℕ → ℝ)
    (hF : ∀ i, Tendsto (fun n : ℕ => F i n / (n : ℝ)) atTop
      (𝓝 (∑' k : ℕ, (1 / ((k : ℝ) + pa i) - 1 / ((k : ℝ) + pb i))))) :
    Tendsto (fun n : ℕ => (∑ i : Fin candidateProfile.length, pv i * F i n) / (n : ℝ)) atTop
      (𝓝 (∑ i : Fin candidateProfile.length,
        pv i * ∑' k : ℕ, (1 / ((k : ℝ) + pa i) - 1 / ((k : ℝ) + pb i)))) :=
  Zeta2LegB.tendsto_profile_sum Finset.univ pv F _ (fun i _ => hF i)

/-- The block sum for piece `i` at block-count `K n` — the object leg B's chain estimates. -/
noncomputable def blockSum (K : ℕ → ℕ) (i : Fin candidateProfile.length) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K n + 1),
    (Chebyshev.theta ((n : ℝ) / ((k : ℝ) + pa i))
      - Chebyshev.theta ((n : ℝ) / ((k : ℝ) + pb i)))

/-- **LEG B AT THE CANDIDATE, THREADED.** `legB_one_interval` is applied at every piece — its
`0 < a`, `a ≤ b`, `b ≤ a+1` side conditions discharged by `piece_valid` from the verified table —
and `tendsto_profile_sum` lifts the result over all 26.

The only remaining hypothesis is `hblk`, the per-piece block bound, which is
`block_sum_close × harmonic_weight_bound`; `hδ0`/`hδlog` are what `psi_error_bound` supplies
through `theta_error_le` and `error_rate_beats_log`. -/
theorem legB_candidate_threaded
    (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (δ : ℕ → ℝ)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδlog : Tendsto (fun n => δ n * Real.log (K n)) atTop (𝓝 0))
    (hblk : ∀ i : Fin candidateProfile.length, ∀ n : ℕ,
      |blockSum K i n
        - (n : ℝ) * (∑ k ∈ Finset.range (K n + 1),
            (1 / ((k : ℝ) + pa i) - 1 / ((k : ℝ) + pb i)))|
        ≤ δ n * (n : ℝ) * (1 / pa i + 1 + Real.log (K n))
          + δ n * (n : ℝ) * (1 / pb i + 1 + Real.log (K n))) :
    Tendsto (fun n : ℕ =>
        (∑ i : Fin candidateProfile.length, pv i * blockSum K i n) / (n : ℝ)) atTop
      (𝓝 (∑ i : Fin candidateProfile.length,
        pv i * ∑' k : ℕ, (1 / ((k : ℝ) + pa i) - 1 / ((k : ℝ) + pb i)))) :=
  legB_candidate (blockSum K) fun i =>
    Zeta2LegB.legB_one_interval (pa i) (pb i)
      (piece_valid i).1 (piece_valid i).2.1 (piece_valid i).2.2.1
      K hK δ hδ0 hδlog (hblk i)

/-- **LEG B FOR THE CANDIDATE, at the CONCRETE block count `K n = ⌊√n⌋ − 1`.**

Every hypothesis of `legB_candidate_threaded` is now discharged from a named theorem:
`blockCount_tendsto` for `K n → ∞`; `hblk_assembled` for the per-piece bound, fed
`block_lower_bound ∘ blockCount_le_sqrt` for its thresholds and `hE` for the `θ` error.

The ONLY remaining input is `hE` — a `θ` error bound at rate `δ n` above `√n` — which
`theta_error_le` derives from `psi_error_bound`, itself proved from `MediumPNT` on PNT+.

`n = 0` is handled separately and vanishes: both sides are `0` there. -/
theorem legB_candidate_final
    (δ : ℕ → ℝ) (hδnn : ∀ n, 0 ≤ δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδlog : Tendsto (fun n => δ n * Real.log ((Nat.sqrt n - 1 : ℕ) : ℝ)) atTop (𝓝 0))
    (hE : ∀ n : ℕ, ∀ x : ℝ, Real.sqrt n ≤ x → |Chebyshev.theta x - x| ≤ δ n * x) :
    Tendsto (fun n : ℕ =>
        (∑ i : Fin candidateProfile.length,
          pv i * blockSum (fun m => Nat.sqrt m - 1) i n) / (n : ℝ)) atTop
      (𝓝 (∑ i : Fin candidateProfile.length,
        pv i * ∑' k : ℕ, (1 / ((k : ℝ) + pa i) - 1 / ((k : ℝ) + pb i)))) := by
  refine legB_candidate_threaded _ Zeta2LegB.blockCount_tendsto δ hδ0 hδlog ?_
  intro i n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [blockSum, Chebyshev.theta_zero]
  · obtain ⟨hpa, hab, _, hb1⟩ := piece_valid i
    have hpb : 0 < pb i := lt_of_lt_of_le hpa hab
    have ha1 : pa i ≤ 1 := le_trans hab hb1
    exact Zeta2LegB.hblk_assembled n _ (pa i) (pb i) (δ n) (Real.sqrt n) hpa hpb (hδnn n)
      (hE n)
      (Zeta2LegB.block_lower_bound n _ hn (pa i) hpa
        (Zeta2LegB.blockCount_le_sqrt n hn (pa i) ha1))
      (Zeta2LegB.block_lower_bound n _ hn (pb i) hpb
        (Zeta2LegB.blockCount_le_sqrt n hn (pb i) hb1))

/-- **THE INTERFACE — LEG B AT THE CANDIDATE, FROM THE `ψ` BOUND ALONE.**

This is `legB_candidate_final` with its last hypothesis discharged. The ONLY hypothesis left is a
`ψ` error bound, stated in the vocabulary `Chebyshev.psi` that BOTH projects share — and it is
byte-for-byte the statement of `PsiErrorBound.psi_error_bound`, which is proved on PNT+ from
`MediumPNT` and is `#print axioms`-clean there.

The whole path between the two is CURRENT MATHLIB, which is the cross-toolchain hypothesis form
(LEAN.md §7) rather than a port:

* `Chebyshev.psi_sub_theta_le_mul_sqrt` — the `ψ → θ` transfer (Mathlib's own, not PNT+);
* `Zeta2LegB.errRate` + `errRate_antitone` — the threshold bookkeeping: `hE` asks for ONE `δ n`
  covering the whole tail `x ≥ √n`, which an antitone majorant evaluated at `√n` supplies;
* `Zeta2LegB.theta_error_le_self` — the crude `|θ x − x| ≤ x`, which covers the `n` below the
  eventual bound's threshold, so `δ` is total as `hE`'s `∀ n` demands;
* `Zeta2LegB.errRate_sqrt_mul_log_tendsto` — `δ n · log n → 0`, i.e. `error_rate_beats_log` at
  the concrete threshold. `hδ0` and `hδlog` are both squeezed by it.

`c`, `C` and `B` are the two rate constants and the `ψ − θ` constant; `C` and `B` are taken
through `max _ 0` because the hypothesis and `psi_sub_theta_le_mul_sqrt` both merely assert
existence, and the majorant's monotonicity needs them nonnegative. -/
theorem legB_candidate_from_psi
    (hψ : ∃ c > 0, ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x) :
    Tendsto (fun n : ℕ =>
        (∑ i : Fin candidateProfile.length,
          pv i * blockSum (fun m => Nat.sqrt m - 1) i n) / (n : ℝ)) atTop
      (𝓝 (∑ i : Fin candidateProfile.length,
        pv i * ∑' k : ℕ, (1 / ((k : ℝ) + pa i) - 1 / ((k : ℝ) + pb i)))) := by
  obtain ⟨c, hc, C, hev⟩ := hψ
  obtain ⟨B0, hB0⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hev
  set C' : ℝ := max C 0 with hC'def
  set B' : ℝ := max B0 0 with hB'def
  set X : ℝ := max X0 1 with hXdef
  have hC'0 : (0 : ℝ) ≤ C' := le_max_right _ _
  have hB'0 : (0 : ℝ) ≤ B' := le_max_right _ _
  have hX1 : (1 : ℝ) ≤ X := le_max_right _ _
  have hX0X : X0 ≤ X := le_max_left _ _
  set δ : ℕ → ℝ :=
    fun n => if X ≤ Real.sqrt n then Zeta2LegB.errRate c C' B' (Real.sqrt n) else 1 with hδdef
  -- `δ` is nonnegative everywhere, which both the squeeze and `hblk_assembled` need.
  have hδnn : ∀ n, 0 ≤ δ n := by
    intro n
    simp only [hδdef]
    split_ifs with h
    · exact Zeta2LegB.errRate_nonneg hC'0 hB'0 _
    · norm_num
  -- above `X²` the `if` takes its first branch
  have hbig : ∀ᶠ n : ℕ in atTop, X ≤ Real.sqrt n := by
    have hXnn : (0 : ℝ) ≤ X := le_trans zero_le_one hX1
    filter_upwards [Filter.eventually_ge_atTop (⌈X ^ 2⌉₊)] with n hn
    have h1 : X ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    exact (Real.le_sqrt hXnn (Nat.cast_nonneg n)).mpr h1
  -- the one limit everything else is squeezed by
  have hmain : Tendsto (fun n : ℕ => δ n * Real.log (n : ℝ)) atTop (𝓝 0) := by
    refine (Zeta2LegB.errRate_sqrt_mul_log_tendsto c C' B' hc).congr' ?_
    filter_upwards [hbig] with n hn
    -- `split_ifs` discharges the `¬ (X ≤ √n)` branch against `hn` itself
    simp only [hδdef]
    split_ifs
    rfl
  have hlogbig : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall hδnn) ?_ hmain
    filter_upwards [hlogbig] with n hn
    nlinarith [hδnn n]
  have hδlog : Tendsto (fun n : ℕ => δ n * Real.log ((Nat.sqrt n - 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall ?_) (Filter.Eventually.of_forall ?_) hmain
    · exact fun n => mul_nonneg (hδnn n) (Zeta2LegB.log_natCast_nonneg _)
    · exact fun n => mul_le_mul_of_nonneg_left
        (Zeta2LegB.log_natCast_le_log_natCast
          (le_trans (Nat.sub_le _ _) (Nat.sqrt_le_self n))) (hδnn n)
  -- the `θ` error bound itself
  have hE : ∀ n : ℕ, ∀ x : ℝ, Real.sqrt n ≤ x → |Chebyshev.theta x - x| ≤ δ n * x := by
    intro n x hx
    simp only [hδdef]
    split_ifs with h
    · have hx1 : (1 : ℝ) ≤ x := le_trans hX1 (le_trans h hx)
      have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx1
      have hpsi := hX0 x (le_trans hX0X (le_trans h hx))
      have hpsi' : |Chebyshev.psi x - x|
          ≤ C' * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x := by
        refine hpsi.trans ?_
        have hnn : (0 : ℝ) ≤ Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x :=
          mul_nonneg (Real.exp_pos _).le hx0
        have hCC : C ≤ C' := le_max_left _ _
        nlinarith
      have hpt : Chebyshev.psi x - Chebyshev.theta x ≤ B' * Real.sqrt x := by
        refine (hB0 x).trans ?_
        have hBB : B0 ≤ B' := le_max_left _ _
        nlinarith [Real.sqrt_nonneg x]
      refine (Zeta2LegB.theta_rel_le_errRate hx1 hpsi' hpt).trans ?_
      exact mul_le_mul_of_nonneg_right
        (Zeta2LegB.errRate_antitone hc.le hC'0 hB'0 (le_trans hX1 h) hx) hx0
    · have hx0 : (0 : ℝ) ≤ x := le_trans (Real.sqrt_nonneg _) hx
      simpa using Zeta2LegB.theta_error_le_self hx0
  exact legB_candidate_final δ hδnn hδ0 hδlog hE

/-- **THE INTERFACE STATEMENT, NAMED** — written in the SAME text as
`PsiErrorBound.psiErrorBoundStatement` on PNT+ and `Zeta2PsiInterface.psiErrorBoundStatement`
on current Mathlib. The three `#print`s are what makes "the statements match" a measurement
rather than a reading. -/
def psiErrorBoundStatement : Prop := ∃ c > 0, ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
    |Chebyshev.psi x - x| ≤ C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x

/-- Kernel check that `legB_candidate_from_psi`'s hypothesis IS that statement — so the text
above cannot drift away from the theorem it is supposed to describe. On PNT+ the mirror-image
check is `example : psiErrorBoundStatement := psi_error_bound`. -/
example (h : psiErrorBoundStatement) := legB_candidate_from_psi h

end Zeta2LegBCandidate

/-! ## RECEIPTS — LEAN.md §1: exit 0 attests nothing, `#print axioms` does.

Emitted by the file itself so the receipt is regenerated on every elaboration rather than being
a remembered green run. Expected on both lines: `[propext, Classical.choice, Quot.sound]`. -/

#print Zeta2LegBCandidate.psiErrorBoundStatement
#print axioms Zeta2LegBCandidate.legB_candidate_final
#print axioms Zeta2LegBCandidate.legB_candidate_from_psi
