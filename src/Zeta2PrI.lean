/-
# `prI` — one affine run `∏_{l ∈ [a,b]} (u + l)`, and the merges every (★) identification uses

`docs/future/zeta2-lean-chain.md` rows STAR-ID and PAIR-6.

**Why this is its own module.**  These lemmas were written for row PAIR-6 as §1 of
`Zeta2Pair6Runs.lean`.  They depend on nothing but Mathlib — yet that file imports the GENERATED
16 MB `StarForallCandt2Base`, so a second consumer (row STAR-ID, on the cand-t1 solve) could only
reach them by importing the HAT base or by copying them.  A copy of a landed lemma is the defect
`/review` caught in PAIR-7's diff, so the block is lifted here, VERBATIM, and STAR-ID imports it.

`Zeta2Pair6Runs.lean` still carries its own §1.  Re-pointing it at this module renames
`Zeta2Pair6Runs.prI` to `Zeta2PrI.prI` under a receipted row and its downstream `Zeta2Pair6`, so
that is recorded as a `found_arch` entry rather than done inside STAR-ID's landing.

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2PrI.lean

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic

namespace Zeta2PrI

open Finset

/-- `∏_{l ∈ [a,b]} (u + l)`.  `u` is `t` or `2t`; the run bounds are affine in `n`. -/
noncomputable def prI (u : ℚ) (a b : ℕ) : ℚ := ∏ l ∈ Icc a b, (u + (l : ℚ))

theorem prI_split (u : ℚ) (a b c : ℕ) (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    prI u a c = prI u a b * prI u (b + 1) c := by
  classical
  have hsplit : Icc a c = Icc a b ∪ Icc (b + 1) c := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Icc a b) (Icc (b + 1) c) := by
    rw [Finset.disjoint_left]; intro x hx hy
    simp only [Finset.mem_Icc] at hx hy; omega
  simp only [prI, hsplit, Finset.prod_union hdisj]

theorem prI_shift (u : ℚ) (a b k : ℕ) :
    prI (u + (k : ℚ)) a b = prI u (a + k) (b + k) := by
  simp only [prI]
  rw [← Finset.map_add_right_Icc a b k, Finset.prod_map]
  refine Finset.prod_congr rfl ?_
  intro l _
  simp only [addRightEmbedding_apply, Nat.cast_add]
  ring

theorem prI_one (u : ℚ) (a : ℕ) : prI u a a = u + (a : ℚ) := by
  simp [prI]

theorem prI_empty (u : ℚ) (a b : ℕ) (h : b < a) : prI u a b = 1 := by
  have he : Icc a b = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  simp only [prI, he, Finset.prod_empty]

/-- Merge two adjacent runs.  `b'` is passed separately so that the three side conditions are
all `omega` and no `b + 1` has to be normalised at the call site. -/
theorem prI_cat (u : ℚ) (a b b' c : ℕ) (hb : b' = b + 1) (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    prI u a b * prI u b' c = prI u a c := by
  subst hb; exact (prI_split u a b c h1 h2).symm

/-- Append one factor at the top of a run. -/
theorem prI_top (u : ℚ) (a b c : ℕ) (hc : c = b + 1) (h1 : a ≤ b + 1) :
    prI u a b * (u + (c : ℚ)) = prI u a c := by
  subst hc
  rw [← prI_one u (b + 1)]
  exact prI_cat u a b (b + 1) (b + 1) rfl h1 (by omega)

/-- Prepend one factor at the bottom of a run. -/
theorem prI_bot (u : ℚ) (a a' b : ℕ) (ha : a' = a + 1) (h : a ≤ b) :
    (u + (a : ℚ)) * prI u a' b = prI u a b := by
  subst ha
  rw [← prI_one u a]
  exact prI_cat u a a (a + 1) b rfl (by omega) h

/-- A run as a `range` product, which is the shape the `afProd` induction produces. -/
theorem prI_range (u : ℚ) (a m : ℕ) :
    prI u a (a + m) = ∏ i ∈ Finset.range (m + 1), (u + ((a : ℚ) + (i : ℚ))) := by
  induction m with
  | zero => simp [prI]
  | succ m ih =>
    have hstep : prI u a (a + m + 1) = prI u a (a + m) * (u + ((a + m + 1 : ℕ) : ℚ)) := by
      simp only [prI]
      exact Finset.prod_Icc_succ_top (by omega) _
    rw [show a + (m + 1) = a + m + 1 from rfl, hstep, ih]
    conv_rhs => rw [Finset.prod_range_succ]
    push_cast
    ring

#print axioms prI_split
#print axioms prI_shift
#print axioms prI_one
#print axioms prI_empty
#print axioms prI_cat
#print axioms prI_top
#print axioms prI_bot
#print axioms prI_range

end Zeta2PrI
