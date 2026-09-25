/-
# Row PAIR-VAL — a COMPUTABLE moment evaluator, so `pnPoly n` is ONE kernel reduction

`Zeta2Defs.momI M j = (Polynomial.bernoulli j).eval (M + 1)` is NONcomputable, and row
PAIR-0p evaluated it the only way available then: one `theorem mom_j` per index, each
rewriting `Zeta2MomStep.momI_step` and handing the arithmetic to `decide +kernel`.  That
works and is what `Zeta2PairP1`/`Zeta2PairP2` do — but the measured cost is **1.7 s / 5.6 s
per lemma, flat in j**, and there are `16n` of them, which is the whole reason `pn n` scales
as ≈ n^2.8 and puts the induction base of row PAIR-VAL (n ≤ 11) hours away.

This file removes the per-index lemma.  `momList M j` is the list `[momI M 0, …, momI M (j−1)]`
built by the same recursion as a `def`, so the kernel computes all `j` values in ONE reduction;
`momC M j` reads the last entry, and `momC_eq_momI` identifies it with `momI` **once and for
all**, by induction on `j`.  After that a `pnPoly` evaluation is a single `decide +kernel`
over `sum_momI` and there are no moment lemmas at all.

Two shape decisions, both about KERNEL cost rather than about the mathematics
(`LEAN.md` §8: the cost is a property of the definition's shape, not of the value):

* `momList` is written as an explicit `Nat.rec`, not through the equation compiler — a
  structural definition that the elaborator decides to compile through `WellFounded.fix` does
  not reduce in the kernel at all, and the failure mode is a `decide +kernel` that never
  returns rather than an error.  `momList M j` also occurs EXACTLY ONCE in the `Nat.rec` step,
  so the kernel's iota rule substitutes one subterm rather than two.
* the consumer-facing lemma is `sum_momI`, which puts ONE `momList M N` under the sum and
  indexes it, instead of `momC M j` inside the summand.  `momC M j` re-runs the recursion from
  zero at every term, so a degree-`d` `pnPoly` would cost `Σ_{j≤d} j²` rational operations
  instead of `d²`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2MomStep

namespace Zeta2MomC

open Zeta2Defs Finset

/-! ## The evaluator

The two `List.getD` facts the prefix argument needs are `List.getD_append` and
`List.getD_append_right`, both in `Mathlib/Data/List/GetD.lean` with exactly the shape used here
(census 2026-09-12, `grep getD_append` over the pinned Mathlib tree — the first draft of this
file re-proved both as private inductions, which is `LEAN.md` §2's exact failure). -/

/-- The next moment from the ones already computed: `Zeta2MomStep.momI_step` read as an
assignment.  `prev` is `[momI M 0, …, momI M (j−1)]` and the value produced is `momI M j`. -/
def stepVal (M : ℤ) (prev : List ℚ) : ℚ :=
  ((M : ℚ) + 1) ^ prev.length
    - (1 / ((prev.length : ℚ) + 1))
      * ∑ k ∈ range prev.length, ((prev.length + 1).choose k : ℚ) * prev.getD k 0

/-- `momList M j = [momI M 0, …, momI M (j−1)]` (`momList_getD`), computable.  Written as an
explicit `Nat.rec` so the kernel reduces it by `Nat.rec`'s own iota rule. -/
def momList (M : ℤ) (j : ℕ) : List ℚ :=
  Nat.rec (motive := fun _ => List ℚ) [] (fun _ prev => prev ++ [stepVal M prev]) j

theorem momList_zero (M : ℤ) : momList M 0 = [] := rfl

theorem momList_succ (M : ℤ) (j : ℕ) :
    momList M (j + 1) = momList M j ++ [stepVal M (momList M j)] := rfl

/-- **The computable moment.**  `momC M j = momI M j` (`momC_eq_momI`). -/
def momC (M : ℤ) (j : ℕ) : ℚ := (momList M (j + 1)).getD j 0

theorem momList_length (M : ℤ) : ∀ j, (momList M j).length = j
  | 0 => rfl
  | j + 1 => by
      rw [momList_succ, List.length_append, momList_length M j]
      rfl

theorem momList_getD_self (M : ℤ) (j : ℕ) :
    (momList M (j + 1)).getD j 0 = stepVal M (momList M j) := by
  have hlen := momList_length M j
  rw [momList_succ, List.getD_append_right _ _ _ _ hlen.le, hlen]
  simp

/-- Every entry of `momList M j` below `j` is the corresponding `momC`: the list is a PREFIX
of every longer one, which is what makes `momC` well defined independently of `j`. -/
theorem momList_getD (M : ℤ) : ∀ (j k : ℕ), k < j → (momList M j).getD k 0 = momC M k := by
  intro j
  induction j with
  | zero => intro k h; exact absurd h (Nat.not_lt_zero k)
  | succ j ih =>
      intro k h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
      · rw [momList_succ,
          List.getD_append _ _ _ _ (by rw [momList_length]; exact h')]
        exact ih k h'
      · subst h'; rfl

/-- `momC` satisfies `Zeta2MomStep.momI_step`'s recursion — by unfolding one `Nat.rec` step,
with no arithmetic. -/
theorem momC_step (M : ℤ) (j : ℕ) :
    momC M j = ((M : ℚ) + 1) ^ j
      - (1 / ((j : ℚ) + 1)) * ∑ k ∈ range j, ((j + 1).choose k : ℚ) * momC M k := by
  have hsum : ∑ k ∈ range j, ((j + 1).choose k : ℚ) * (momList M j).getD k 0
      = ∑ k ∈ range j, ((j + 1).choose k : ℚ) * momC M k :=
    Finset.sum_congr rfl fun k hk => by rw [momList_getD M j k (mem_range.1 hk)]
  rw [momC, momList_getD_self, stepVal, momList_length, hsum]

/-- The bridge, stated as the strong-induction hypothesis it is proved by. -/
theorem momC_eq_momI_of_lt (M : ℤ) : ∀ (j k : ℕ), k < j → momC M k = momI M k := by
  intro j
  induction j with
  | zero => intro k h; exact absurd h (Nat.not_lt_zero k)
  | succ j ih =>
      intro k h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
      · exact ih k h'
      · subst h'
        have hsum : ∑ m ∈ range k, ((k + 1).choose m : ℚ) * momC M m
            = ∑ m ∈ range k, ((k + 1).choose m : ℚ) * momI M m :=
          Finset.sum_congr rfl fun m hm => by rw [ih m (mem_range.1 hm)]
        rw [momC_step, Zeta2MomStep.momI_step, hsum]

/-- **The row's new object**: `momI`, which the kernel cannot evaluate, IS the computable
`momC`, at every cell and every index. -/
theorem momC_eq_momI (M : ℤ) (j : ℕ) : momC M j = momI M j :=
  momC_eq_momI_of_lt M (j + 1) j (Nat.lt_succ_self j)

/-- **The form every consumer rewrites with.**  One `momList M N` under the sum, indexed —
so the recursion runs once for the whole `pnPoly`, not once per term. -/
theorem sum_momI (M : ℤ) (N : ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ range N, f j * momI M j = ∑ j ∈ range N, f j * (momList M N).getD j 0 :=
  Finset.sum_congr rfl fun j hj => by
    rw [momList_getD M N j (mem_range.1 hj), momC_eq_momI]

/-! ## Rung 0 — the evaluator actually reduces in the kernel, and reproduces a landed value

`Zeta2MomStep.momI_control_one` is the corpus' control for the moment recursion, proved from
`Polynomial.sum_bernoulli`: `momI (-1) 1 = B₁(0) = −1/2`.  Here the SAME number is produced by
kernel computation through `momC`, and carried back to `momI` by the bridge — so a `momC` that
computed something else, or that did not reduce at all, cannot pass this file. -/

theorem momC_control_one : momC (-1) 1 = -(1 / 2 : ℚ) := by decide +kernel

theorem momI_control_one' : momI (-1) 1 = -(1 / 2 : ℚ) := by
  rw [← momC_eq_momI]; exact momC_control_one

end Zeta2MomC

#print axioms Zeta2MomC.momList_length
#print axioms Zeta2MomC.momList_getD
#print axioms Zeta2MomC.momC_step
#print axioms Zeta2MomC.momC_eq_momI
#print axioms Zeta2MomC.sum_momI
#print axioms Zeta2MomC.momC_control_one
#print axioms Zeta2MomC.momI_control_one'
