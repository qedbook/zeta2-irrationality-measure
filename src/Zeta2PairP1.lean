/-
# `Zeta2PairP1.lean` — GENERATED.  Do not hand-edit.

Generator: `external_tests/zeta2_arith/gen_pn_lean.py` (`--check` re-derives and diffs;
`--falsify` proves its checks can fail).  Rows PAIR-0p / PAIR-VAL of
`docs/future/zeta2-lean-chain.md` — one cell of the pairing's induction base:
**`hatP 1 = candidateM.pn 1`**, in the kernel.  `LEAN.md` §6.

`candidateM.pn 1` runs through `Polynomial ℚ` division (`Ppol`) and Bernoulli-polynomial
values (`momI`), neither of which the kernel can evaluate, so both get explicit witnesses:
the quotient `Q` (degree 15) and remainder `R` (degree 11) of `numPoly 1` (degree 27)
by `denPoly 1` (degree 12), proved to be the quotient by `div_modByMonic_unique` — the
identity is one `ring` over the 27 explicit linear factors — and the 16 moments
`momI (-5) j = B_j(-4)` through `Zeta2MomC.sum_momI`, which replaces the
noncomputable `momI` under the sum by ONE indexed `momList` the kernel builds in a single
reduction (row PAIR-VAL).  The harmonic half `pnHarm` is computable already.

Every literal below was equated by the generator (exactly, in ℚ) with the tale-1 engine
`z2a.linear_form`, with `gen_hat_lean.hatP` (the hat closed form — the pairing computed by
two independent closed forms), with the archived K7 literal, and with the
`Zeta2DefsCheck.enginePnPoly` row; the quotient with the engine's own division, the moments
with `mb.moments`.

The HAT side's kernel pin `hatP_engine` is in this file rather than in `Zeta2HatCheck.lean`
(both are rendered by the one `gen_hat_lean.hatP_pin_lines`): the induction base is twelve
cells, and one file per cell keeps every elaboration independently runnable instead of
making one file carry the whole base's kernel work.
-/
import Zeta2Hat
import Zeta2MomC
import Zeta2HarmC
import Mathlib.Tactic.ComputeDegree

-- The wall law is part of the row's record (LEAN.md §0a column 3): every declaration
-- slower than 100 ms prints its elaboration / kernel time into the archived log.
set_option profiler true
set_option profiler.threshold 100

-- MEASURED at n = 4, 2026-09-12: the default 512 is not enough from that cell on — both
-- `div_identity`'s traversal of the 108 explicit factors and `pnPoly_eq`'s `decide +kernel`
-- hit `maximum recursion depth has been reached`, and the receipt then names `sorryAx`.
-- This is an elaborator stack budget, not a proof obligation: the kernel still checks every
-- term, and the `#print axioms` receipts below are what say so.
set_option maxRecDepth 20000

-- MEASURED at n = 6, 2026-09-12: the default heartbeat budget kills the DEFINITION of `Q`
-- (`(deterministic) timeout at «synthesize pending MVars»` on its coefficient list), after
-- which every later error in the file is the spurious `Unknown identifier Q` — the worst
-- possible failure shape, because it hides which declaration actually ran out.  This file
-- is a deliberate large kernel computation and its budget is the WALL recorded in the
-- archived log beside it, not a heartbeat count; a fixed number would need re-tuning at
-- every cell of the base.
set_option maxHeartbeats 0

namespace Zeta2PairP1

open Zeta2Defs Zeta2Hat Zeta2MomC Polynomial Finset

/-- The quotient `numPoly 1 /ₘ denPoly 1`, degree 15, integer coefficients. -/
noncomputable def Q : ℚ[X] :=
  C (1 : ℚ) * X ^ 15
      + C (-69 : ℚ) * X ^ 14
      + C (4438 : ℚ) * X ^ 13
      + C (-234696 : ℚ) * X ^ 12
      + C (11284294 : ℚ) * X ^ 11
      + C (-502545582 : ℚ) * X ^ 10
      + C (21119085944 : ℚ) * X ^ 9
      + C (-846996531348 : ℚ) * X ^ 8
      + C (32686562012489 : ℚ) * X ^ 7
      + C (-1221200944013589 : ℚ) * X ^ 6
      + C (44378486436281018 : ℚ) * X ^ 5
      + C (-1574462316241723356 : ℚ) * X ^ 4
      + C (54696713980889639016 : ℚ) * X ^ 3
      + C (-1865181150116231175360 : ℚ) * X ^ 2
      + C (62559757145491871932800 : ℚ) * X ^ 1
      + C (-2067415766504461562112000 : ℚ) * X ^ 0

/-- The remainder `numPoly 1 %ₘ denPoly 1`, degree 11 < 12. -/
noncomputable def R : ℚ[X] :=
  C (67414539626884372995072000 : ℚ) * X ^ 11
      + C (15221161403171541574428672000 : ℚ) * X ^ 10
      + C (1560772574717252320867322880000 : ℚ) * X ^ 9
      + C (95929302082135904987251046400000 : ℚ) * X ^ 8
      + C (3926385763974536775675324097536000 : ℚ) * X ^ 7
      + C (112359707540355110461032212822016000 : ℚ) * X ^ 6
      + C (2293708558320842796571023306040320000 : ℚ) * X ^ 5
      + C (33399434789459227585803324012595200000 : ℚ) * X ^ 4
      + C (339942425670677067130993335712468992000 : ℚ) * X ^ 3
      + C (2303118363677236637872080894933491712000 : ℚ) * X ^ 2
      + C (9347277611204480129567873608337817600000 : ℚ) * X ^ 1
      + C (17215157635638288084852101763032678400000 : ℚ) * X ^ 0

/-- The division identity `R + denPoly 1 · Q = numPoly 1`: the three numerator blocks
and the denominator block unfold to 27 and 12 explicit factors `X + k`, and `ring`
closes it. -/
theorem div_identity : R + candidateM.denPoly 1 * Q = candidateM.numPoly 1 := by
  simp only [Q, R, Member.numPoly, Member.denPoly, candidateM, block, Nat.reduceMul,
    Nat.reduceSub, Nat.reduceAdd, Finset.prod_range_succ, Finset.prod_range_zero, map_natCast,
    map_ofNat, map_neg, map_one]
  push_cast
  ring

theorem R_degree_lt : R.degree < (candidateM.denPoly 1).degree := by
  apply Polynomial.degree_lt_degree
  rw [candidateM.denPoly_natDegree 1]
  have h : R.natDegree ≤ 11 := by rw [R]; compute_degree!
  simp only [candidateM] at h ⊢
  omega

/-- **`Ppol 1` is `Q`** — the first evaluation of `candidateM.Ppol` in the corpus. -/
theorem Ppol_eq : candidateM.Ppol 1 = Q :=
  (Polynomial.div_modByMonic_unique Q R (candidateM.denPoly_monic 1)
    ⟨div_identity, R_degree_lt⟩).1

theorem cell_eq : candidateM.cell 1 = -5 := by decide

/-- `Σ_j Q_j · momI (cell 1) j` — the polynomial half of `pn 1`, the number
`Zeta2DefsCheck.enginePnPoly` only RECORDS.  `sum_momI` replaces the noncomputable `momI`
under the sum by the 16-entry list `momList (-5) 16`, which the kernel
builds ONCE; `simp only [Q, …]` turns each `Q.coeff j` into its literal.  Row PAIR-VAL. -/
theorem pnPoly_eq : candidateM.pnPoly 1 = (-31098482130308598631825920 / 13 : ℚ) := by
  have hd : (candidateM.Ppol 1).natDegree = 15 := by
    rw [candidate_Ppol_natDegree]
  rw [Member.pnPoly, hd, Ppol_eq, cell_eq, Zeta2MomC.sum_momI]
  simp only [Q, coeff_add, coeff_C_mul_X_pow]
  decide +kernel

/-- The harmonic half, computable: `Σ_k ck 1 k · H^{(2)}_{k − 5}` over the window.
`Zeta2HarmC.pnHarm_shared` puts ONE `harmList 2 22` under the sum and indexes it, so the
kernel adds 22 rationals instead of recomputing `harm 2` at each of the 12 window
terms (row PAIR-VAL, third pass — the same lever `Zeta2MomC.sum_momI` is on the moment side). -/
theorem pnHarm_eq : candidateM.pnHarm 1 = (1410503664700665182226378240 / 13 : ℚ) := by
  rw [Zeta2HarmC.pnHarm_shared candidateM (by decide) 1]
  decide +kernel

/-- **`pn 1`, evaluated** — the same literal `hatP_engine` below pins from the hat side. -/
theorem pn_eq : candidateM.pn 1 = (-41381969327296379567 / 2535 : ℚ) := by
  rw [Member.pn, pnPoly_eq, pnHarm_eq]
  decide +kernel

/-- Kernel pin on the HAT side: `hatP 1` is the tale-1 engine's `p_1`.  Rendered by
`gen_hat_lean.hatP_pin_lines`, the same function `Zeta2HatCheck.lean` uses for n ≤ 3. -/
theorem hatP_engine : hatP 1 = (-41381969327296379567 / 2535 : ℚ) := by
  rw [Zeta2HarmC.hatP_shared]
  simp only [hatA, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- **The row's statement at n = 1**: `hatP 1 = candidateM.pn 1`. -/
theorem hatP_eq_pn : hatP 1 = candidateM.pn 1 := by
  rw [hatP_engine, pn_eq]

end Zeta2PairP1

#print axioms Zeta2PairP1.div_identity
#print axioms Zeta2PairP1.R_degree_lt
#print axioms Zeta2PairP1.Ppol_eq
#print axioms Zeta2PairP1.pnPoly_eq
#print axioms Zeta2PairP1.pnHarm_eq
#print axioms Zeta2PairP1.pn_eq
#print axioms Zeta2PairP1.hatP_engine
#print axioms Zeta2PairP1.hatP_eq_pn
