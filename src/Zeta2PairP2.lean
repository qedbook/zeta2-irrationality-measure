/-
# `Zeta2PairP2.lean` — GENERATED.  Do not hand-edit.

Generator: `external_tests/zeta2_arith/gen_pn_lean.py` (`--check` re-derives and diffs;
`--falsify` proves its checks can fail).  Rows PAIR-0p / PAIR-VAL of
`docs/future/zeta2-lean-chain.md` — one cell of the pairing's induction base:
**`hatP 2 = candidateM.pn 2`**, in the kernel.  `LEAN.md` §6.

`candidateM.pn 2` runs through `Polynomial ℚ` division (`Ppol`) and Bernoulli-polynomial
values (`momI`), neither of which the kernel can evaluate, so both get explicit witnesses:
the quotient `Q` (degree 31) and remainder `R` (degree 22) of `numPoly 2` (degree 54)
by `denPoly 2` (degree 23), proved to be the quotient by `div_modByMonic_unique` — the
identity is one `ring` over the 54 explicit linear factors — and the 32 moments
`momI (-9) j = B_j(-8)` through `Zeta2MomC.sum_momI`, which replaces the
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

namespace Zeta2PairP2

open Zeta2Defs Zeta2Hat Zeta2MomC Polynomial Finset

/-- The quotient `numPoly 2 /ₘ denPoly 2`, degree 31, integer coefficients. -/
noncomputable def Q : ℚ[X] :=
  C (1 : ℚ) * X ^ 31
      + C (-237 : ℚ) * X ^ 30
      + C (42941 : ℚ) * X ^ 29
      + C (-6278493 : ℚ) * X ^ 28
      + C (806297373 : ℚ) * X ^ 27
      + C (-93854547045 : ℚ) * X ^ 26
      + C (10125754473705 : ℚ) * X ^ 25
      + C (-1027204554711465 : ℚ) * X ^ 24
      + C (99002416070491635 : ℚ) * X ^ 23
      + C (-9135625733588097315 : ℚ) * X ^ 22
      + C (811918001205353464695 : ℚ) * X ^ 21
      + C (-69824253534152854435335 : ℚ) * X ^ 20
      + C (5832687615438403678672335 : ℚ) * X ^ 19
      + C (-474739550190148737474707175 : ℚ) * X ^ 18
      + C (37748435527977351154548335475 : ℚ) * X ^ 17
      + C (-2938714990468602118987205488275 : ℚ) * X ^ 16
      + C (224414280739350674217088723081440 : ℚ) * X ^ 15
      + C (-16837817983128011798428276133636580 : ℚ) * X ^ 14
      + C (1243025111618588834565885511445432240 : ℚ) * X ^ 13
      + C (-90401107831586703897730153472745705120 : ℚ) * X ^ 12
      + C (6484034251872555046816666258495140296704 : ℚ) * X ^ 11
      + C (-459112731479437595184275911796464603329408 : ℚ) * X ^ 10
      + C (32119995306309120995872363355166044016294144 : ℚ) * X ^ 9
      + C (-2222054114923404456803720815619527581927405312 : ℚ) * X ^ 8
      + C (152112310898019311543403165695216327180774080512 : ℚ) * X ^ 7
      + C (-10310584138466039261468442680973754684690739082240 : ℚ) * X ^ 6
      + C (692412148405422946678932643599669929755931018956800 : ℚ) * X ^ 5
      + C (-46093506285963488476405763440058484919962576254976000 : ℚ) * X ^ 4
      + C (3043127007660473615269771134187689786621418886062080000 : ℚ) * X ^ 3
      + C (-199342532182768709985959778407135421725783836350873600000 : ℚ) * X ^ 2
      + C (12961591104306791252339073040036886542249617205297152000000 : ℚ) * X ^ 1
      + C (-836874357548177623711232349808175666268394027682365440000000 : ℚ) * X ^ 0

/-- The remainder `numPoly 2 %ₘ denPoly 2`, degree 22 < 23. -/
noncomputable def R : ℚ[X] :=
  C (53673340432524547772349620094903191932331486532442521600000000 : ℚ) * X ^ 22
      + C (48427903105232249528283025847121778104766289238433569177600000000 : ℚ) * X ^ 21
      + C (20839249868364461022801142600081300149522380662915793839718400000000 : ℚ) * X ^ 20
      + C (5689345057255153095261411604429139382020115459269262110726553600000000 : ℚ) * X ^ 19
      + C (1105843406751125117679295268703808421071879294640140594550774169600000000 : ℚ) * X ^ 18
      + C (162776800663948701564836766465944853086906366124672872220616713830400000000 : ℚ) * X ^ 17
      + C (18842470686889710030296507054118044155956239168572400664054902607052800000000 : ℚ) * X ^ 16
      + C (1758133066913211621026982407715285882660309840203867591719682097492787200000000 : ℚ) * X ^ 15
      + C (134456726819732917837235787393245181234724991996043665317199997492107673600000000 : ℚ) * X ^ 14
      + C (8523711044232376236968442704039124194513490402466768305036600567729959731200000000 : ℚ) * X ^ 13
      + C (451188164123237394700107224265944898182443442875497755330112305600319927091200000000 : ℚ) * X ^ 12
      + C (20024004695240617342217875826990228508865832446443550357794123488100242738380800000000 : ℚ) * X ^ 11
      + C (746071457237360678327181465912882581627218886748444399460101289217164519774617600000000 : ℚ) * X ^ 10
      + C (23305747064251496799656369057965144361841414401793308554566173357166442038951936000000000 : ℚ) * X ^ 9
      + C (607863569498675598539694962505750185484392294552104679690991983938254211630340505600000000 : ℚ) * X ^ 8
      + C (13141080156214822478144697574427240980352187490375602408409809692265825969103070822400000000 : ℚ) * X ^ 7
      + C (232824182985704154103377215958062402516489641915521953258795555635447277277285030297600000000 : ℚ) * X ^ 6
      + C (3324585042653365761141533476277544755963743492350058251843727353056743164656919301324800000000 : ℚ) * X ^ 5
      + C (37327209998113129041256248521998151144402513777185081640662919384107232478308736172032000000000 : ℚ) * X ^ 4
      + C (317323117399641617119224339593824452878872340231440446675447162674150616364491636473856000000000 : ℚ) * X ^ 3
      + C (1920161599383121104787886372537754682426469966474899983047129277730462538846778289029120000000000 : ℚ) * X ^ 2
      + C (7369945324832545171838030282648073754307183323402217019229445374132728745649802471014400000000000 : ℚ) * X ^ 1
      + C (13487282302909796392043036154288100230438621131924041040358764306301158758909810311168000000000000 : ℚ) * X ^ 0

/-- The division identity `R + denPoly 2 · Q = numPoly 2`: the three numerator blocks
and the denominator block unfold to 54 and 23 explicit factors `X + k`, and `ring`
closes it. -/
theorem div_identity : R + candidateM.denPoly 2 * Q = candidateM.numPoly 2 := by
  simp only [Q, R, Member.numPoly, Member.denPoly, candidateM, block, Nat.reduceMul,
    Nat.reduceSub, Nat.reduceAdd, Finset.prod_range_succ, Finset.prod_range_zero, map_natCast,
    map_ofNat, map_neg, map_one]
  push_cast
  ring

theorem R_degree_lt : R.degree < (candidateM.denPoly 2).degree := by
  apply Polynomial.degree_lt_degree
  rw [candidateM.denPoly_natDegree 2]
  have h : R.natDegree ≤ 22 := by rw [R]; compute_degree!
  simp only [candidateM] at h ⊢
  omega

/-- **`Ppol 2` is `Q`** — the first evaluation of `candidateM.Ppol` in the corpus. -/
theorem Ppol_eq : candidateM.Ppol 2 = Q :=
  (Polynomial.div_modByMonic_unique Q R (candidateM.denPoly_monic 2)
    ⟨div_identity, R_degree_lt⟩).1

theorem cell_eq : candidateM.cell 2 = -9 := by decide

/-- `Σ_j Q_j · momI (cell 2) j` — the polynomial half of `pn 2`, the number
`Zeta2DefsCheck.enginePnPoly` only RECORDS.  `sum_momI` replaces the noncomputable `momI`
under the sum by the 32-entry list `momList (-9) 32`, which the kernel
builds ONCE; `simp only [Q, …]` turns each `Q.coeff j` into its literal.  Row PAIR-VAL. -/
theorem pnPoly_eq : candidateM.pnPoly 2 = (-866249288371806200936944439912597965701280178152271522562048000 / 899 : ℚ) := by
  have hd : (candidateM.Ppol 2).natDegree = 31 := by
    rw [candidate_Ppol_natDegree]
  rw [Member.pnPoly, hd, Ppol_eq, cell_eq, Zeta2MomC.sum_momI]
  simp only [Q, coeff_add, coeff_C_mul_X_pow]
  decide +kernel

/-- The harmonic half, computable: `Σ_k ck 2 k · H^{(2)}_{k − 9}` over the window.
`Zeta2HarmC.pnHarm_shared` puts ONE `harmList 2 44` under the sum and indexes it, so the
kernel adds 44 rationals instead of recomputing `harm 2` at each of the 23 window
terms (row PAIR-VAL, third pass — the same lever `Zeta2MomC.sum_momI` is on the moment side). -/
theorem pnHarm_eq : candidateM.pnHarm 2 = (58246132723133282679601518128617993890262262716428255536087040000 / 667 : ℚ) := by
  rw [Zeta2HarmC.pnHarm_shared candidateM (by decide) 2]
  decide +kernel

/-- **`pn 2`, evaluated** — the same literal `hatP_engine` below pins from the hat side. -/
theorem pn_eq : candidateM.pn 2 = (-400738225483448453563002162179509842017053106921 / 37836428760000 : ℚ) := by
  rw [Member.pn, pnPoly_eq, pnHarm_eq]
  decide +kernel

/-- Kernel pin on the HAT side: `hatP 2` is the tale-1 engine's `p_2`.  Rendered by
`gen_hat_lean.hatP_pin_lines`, the same function `Zeta2HatCheck.lean` uses for n ≤ 3. -/
theorem hatP_engine : hatP 2 = (-400738225483448453563002162179509842017053106921 / 37836428760000 : ℚ) := by
  rw [Zeta2HarmC.hatP_shared]
  simp only [hatA, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- **The row's statement at n = 2**: `hatP 2 = candidateM.pn 2`. -/
theorem hatP_eq_pn : hatP 2 = candidateM.pn 2 := by
  rw [hatP_engine, pn_eq]

end Zeta2PairP2

#print axioms Zeta2PairP2.div_identity
#print axioms Zeta2PairP2.R_degree_lt
#print axioms Zeta2PairP2.Ppol_eq
#print axioms Zeta2PairP2.pnPoly_eq
#print axioms Zeta2PairP2.pnHarm_eq
#print axioms Zeta2PairP2.pn_eq
#print axioms Zeta2PairP2.hatP_engine
#print axioms Zeta2PairP2.hatP_eq_pn
