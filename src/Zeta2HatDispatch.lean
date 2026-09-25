/-
# PT-QB clump 3 — the DISPATCH's uniqueness layer, probed

Row PT-QB of `docs/future/zeta2-lean-chain.md` (registry `2B0.AW`).  The gap-cell lemmas
(`Zeta2HatGap`) are statements about `(r, p)` inequalities.  Turning them into
`PhiT_dvd_qnInt` needs the PROFILE ALGEBRA: `∀ x, φ̃ x ≤ max (φ x) (φ̂ x)` over the 52-cell
common refinement of `Zeta2CarryFold.phiTable` (41 rows) and `Zeta2Profile.candidateProfile`
(26 rows).  That step was priced at ~300–400 lines with nothing probed, and after three gap
cells it is the row's LARGEST remaining unknown.

**Its load-bearing piece is uniqueness on both tables**, and this module lands it.  Both
profiles are `List.find?` — first match wins — so every theorem about them has to get from
"`x` lies in THIS row" to "`find?` returns THIS row".  PT-QA proved `phiTable_pairwise` (the 41
intervals are nonempty and pairwise ordered, its `piece_unique`) and then stated no consequence
of it; `carry_ge_of_mem_table` dispatches on membership and never needs the value back.  The
dispatch does.

`phiSingle_of_mem` is that consequence: membership in ANY row determines `φ x`, whatever
`find?` reaches first.  25 lines, and the `candidateProfile` twin is the same proof over a
`Pairwise` this corpus does not yet have — which is now the only unmeasured piece of the
uniqueness layer.

## What this file does NOT claim

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  This is ONE lemma of the
dispatch.  `φ̃ x ≤ max (φ x) (φ̂ x)`, the 52-cell case analysis and `PhiT_dvd_qnInt` are not
here, and neither is `candidateProfile`'s own disjointness.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
API at this pin, measured, three drafts:
  * `List.Pairwise.forall` takes the `Pairwise` as its FIRST explicit argument and gets
    symmetry from an instance, not from an explicit `Symmetric` proof;
  * the symmetry class is **`Std.Symm`**, not `IsSymm` (unknown identifier here);
  * its field takes the two points explicitly — `⟨fun _ _ h => h.symm⟩`, not `⟨fun h => …⟩`.
-/
import Zeta2CarryFold
import Zeta2PhiT

namespace Zeta2HatDispatch

open Zeta2Arith Zeta2PhiT

/-- **First match is the only match, on PT-QA's 41-row table.**  `phiTable_pairwise` says the
intervals are nonempty and pairwise ordered, hence disjoint; so if `x` lies in the row
`(a, b, v)` then `φ x = v`, whatever row `List.find?` happens to reach first.

This is the step every consumer of a `find?`-defined profile needs and that PT-QA's own
dispatch did not: `carry_ge_of_mem_table` goes FROM membership and never has to come back. -/
theorem phiSingle_of_mem {x a b : ℚ} {v : ℕ} (ht : (a, b, v) ∈ phiTable)
    (h1 : a ≤ x) (h2 : x < b) : phiSingle x = v := by
  have : Std.Symm (fun s t : ℚ × ℚ × ℕ => Before s t ∨ Before t s) := ⟨fun _ _ h => h.symm⟩
  have hpw : phiTable.Pairwise (fun s t => Before s t ∨ Before t s) :=
    phiTable_pairwise.imp Or.inl
  unfold phiSingle
  rcases hf : phiTable.find? (fun t => decide (t.1 ≤ x ∧ x < t.2.1)) with _ | t'
  · -- `find?` found nothing, yet `(a, b, v)` matches: impossible.
    exfalso
    have hn := List.find?_eq_none.1 hf (a, b, v) ht
    simp only [decide_eq_true_eq, not_and] at hn
    exact absurd h2 (hn h1)
  · rw [hf]
    have hmem' := List.mem_of_find?_eq_some hf
    have hp' := List.find?_some hf
    simp only [decide_eq_true_eq] at hp'
    by_cases heq : t' = (a, b, v)
    · rw [heq]
    · -- two DIFFERENT rows both contain `x`, which `Before` forbids in either order
      exfalso
      rcases List.Pairwise.forall hpw hmem' ht heq with h | h
      · have hba : t'.2.1 ≤ a := h.2
        have := hp'.2
        linarith
      · have hbt : b ≤ t'.1 := h.2
        have := hp'.1
        linarith

/-- Non-vacuity (LEAN.md §5): the lemma is applied, at a row that is NOT the first match —
`1/7` is row 5 of 41, so a proof that only handled the head would not reach it. -/
theorem phiSingle_one_seventh_of_mem : phiSingle (1 / 7) = 2 :=
  phiSingle_of_mem (a := 1 / 7) (b := 2 / 13) (v := 2) (by norm_num [phiTable])
    (by norm_num) (by norm_num)

/-- The half-open endpoint survives the new route: `2/13` is row 5's `b`, and lies in row 6. -/
theorem phiSingle_two_thirteenths_of_mem : phiSingle (2 / 13) = 1 :=
  phiSingle_of_mem (a := 2 / 13) (b := 1 / 6) (v := 1) (by norm_num [phiTable])
    (by norm_num) (by norm_num)

end Zeta2HatDispatch

#print axioms Zeta2HatDispatch.phiSingle_of_mem
#print axioms Zeta2HatDispatch.phiSingle_one_seventh_of_mem
#print axioms Zeta2HatDispatch.phiSingle_two_thirteenths_of_mem
