/-
# PT-QA — the ultrametric fold: `p ^ phiSingle({n/p}) ∣ qₙ` at every prime above the line

Row PT-QA of `docs/future/zeta2-lean-chain.md` (registry `2B0.AV`), the row's LAST piece.
`Zeta2CarryFull.lean` holds the residue bridge and all 41 per-piece carry lemmas
`carry_ge_piece<i>_res`, each stated at the full residue range, `∀ k ∈ window n`.  This module
adds the three things the row still owed and nothing else:

1. **`phiSingle : ℚ → ℕ`, the row's own profile** — the 41-interval exact single-representation
   profile from `ptqa_refine_probe.out`, half-open `[a, b)`, value `0` off the table.  It is a
   LIST of triples (`phiTable`) and a first-match lookup (`List.find?`), so the data is written
   once and the dispatch is a function by construction.  `phiTable_pairwise` proves the 41
   intervals are nonempty and pairwise disjoint in list order, so the first match is the ONLY
   match (`piece_unique`, which the piece clumps asserted but did not prove).
2. **The dispatch, executed** — `carry_ge_of_mem_table` runs a 41-way case split on table
   membership and closes each case with that piece's lemma.  This is where a wrong table row
   is caught: the row's interval must be EXACTLY the lemma's hypotheses (`falsify_carryfold.sh`
   ARM T widens one interval by a hair and the case reds), and its value must be EXACTLY the
   lemma's conclusion (ARM V).
3. **The fold** — `pow_dvd_qnInt_of_termwise`.  `qnInt n` is the SIGNED alternating sum
   `(−1)^{16n+1} Σ_k (−1)^{12n+k−1} · cTerm n k` over the window, and the fold is stated on
   exactly that term, not on `|cTerm|`: `Finset.dvd_sum` needs no sign bookkeeping and no
   nonvanishing, which is why the DIVISIBILITY form `p ^ v ∣ qnInt n` is unconditional.  It is
   the ultrametric inequality `v(Σ) ≥ min v(term)` in the form a consumer of `∣` wants.

## The finding: the cell's `padicValInt` form carries a hidden hypothesis

The row's cell states the target as `phiSingle ({n/p}) ≤ padicValInt p (qnInt n)`.  With
Mathlib's `padicValInt p 0 = 0` that statement is FALSE at any `n` with `qnInt n = 0` and a
`p` whose residue lands on the table, so it is provable only through `qnInt n ≠ 0`
(`padicValInt_dvd_iff : p ^ v ∣ a ↔ a = 0 ∨ v ≤ padicValInt p a`).  No `∀ n, qnInt n ≠ 0` is
landed anywhere in the corpus — the chain's `hrow` is `∃ k, m₀ ≤ k ∧ qn k ≠ 0`, one index, and
`Zeta2L1Asm` supplies it at `4` and `6` by kernel — and the consumer PT-QB wants
`PhiT_dvd_qnInt : (PhiT n : ℤ) ∣ qnInt n`, a divisibility.  So the deliverable here is the
divisibility theorem `pow_phiSingle_dvd_qnInt`, unconditional; `padicValInt_qnInt_ge_phi` is
the cell's statement with the hypothesis it needs made explicit (`hq : qnInt n ≠ 0`), and
`padicValInt_qnInt_ge_phi_or_zero` is the unconditional disjunction.  `ptqa_fold_probe.py`
measures `qnInt n ≠ 0` at every `n ≤ 40` (ARM D), and `qnInt_one_ne_zero` puts the `n = 1`
instance in the kernel for the non-vacuity witness below.

## What was measured before it was proved (`ptqa_fold_probe.py`, `ptqa_fold_probe.out`)

ARM A: the 41 hypotheses in `Zeta2CarryFull.lean`, PARSED from the source, are row for row the
table (`a`, `b`, `v`); ARM B: the 41 intervals are sorted and disjoint; ARM C: at every real
cell `(n, p)` with `n ≤ 40`, `26n+1 < p²`, and EVERY `k` in the window — 3701 cells, 1 069 733
terms, `ord_p` by full Legendre rather than the one-term atom — the dispatched lemma's
hypotheses hold and `phiSingle ≤ ord_p (cTerm n k)`, 0 holes; ARM D: `qnInt n ≠ 0` and
`phiSingle ≤ ord_p (qnInt n)` at all of them; ARM E: `ord_p (qnInt n) ≥ min_k ord_p (cTerm n k)`,
0 violations; ARM F/G (wanted RED, both bite): `phiSingle + 1` fails at 1639 cells, and the
CLOSED-interval table gives away at 8 real cells (`x = k/13`, `k ≤ 6`, plus `1/13`).

## What this file does NOT claim

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  This is the q-side of the
profile at `phiSingle`, the single-representation profile; `phiT` (PT-DEF's `φ̃`) exceeds it by
one on five sub-intervals and lifting to `φ̃` there is PT-QB, through the hat representation
and PAIR.  `PhiT_dvd_qnInt` is PT-QA + PT-QB and is not here.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
API at this pin, measured: `List.Chain'` is `List.IsChain` (`isChain_cons_cons`,
`isChain_iff_pairwise [Trans R R R]` in Batteries); `decide` on a `ℚ` literal built with `/`
does not reduce (`Rat.instDecidableLe` gets stuck on `Rat.div`), so every table fact goes
through `norm_num [phiTable, …]` instead.
-/
import Zeta2CarryFull

namespace Zeta2Arith

open Zeta2Defs Nat Finset

/-! ## The profile, as data -/

/-- **The 41-interval single-representation profile.**  `(a, b, v)` means `phiSingle x = v` on
`[a, b)`; the value off every interval is `0`.  Rows are `ptqa_refine_probe.out`'s proof table
in order, and `ptqa_fold_probe.py` ARM A pins each row to the hypotheses and conclusion of the
piece lemma `Zeta2CarryFull.carry_ge_piece<i>_res` that `carry_ge_of_mem_table` dispatches it
to — Lean itself re-checks that pin at every case of that theorem. -/
def phiTable : List (ℚ × ℚ × ℕ) := [
  (1/15, 1/13, 1), (1/11, 1/9, 2), (1/9, 2/17, 1), (2/17, 1/7, 1), (1/7, 2/13, 2), (2/13, 1/6, 1),
  (1/6, 2/11, 1), (2/11, 1/5, 2), (1/5, 2/9, 1), (2/9, 3/13, 1), (3/11, 4/13, 2), (4/13, 1/3, 1),
  (1/3, 4/11, 1), (4/11, 5/13, 2), (5/13, 2/5, 1), (3/7, 4/9, 1), (4/9, 5/11, 1), (5/11, 6/13, 2),
  (6/13, 7/15, 1), (7/15, 8/17, 1), (8/15, 7/13, 1), (6/11, 5/9, 2), (5/9, 9/16, 1), (9/16, 3/5, 1),
  (3/5, 8/13, 1), (7/11, 11/17, 2), (11/17, 2/3, 1), (2/3, 9/13, 1), (5/7, 8/11, 1), (8/11, 3/4, 2),
  (3/4, 10/13, 2), (10/13, 7/9, 1), (7/9, 4/5, 1), (9/11, 14/17, 2), (14/17, 5/6, 1), (5/6, 11/13, 1),
  (11/13, 8/9, 1), (8/9, 10/11, 1), (10/11, 12/13, 2), (12/13, 14/15, 1), (14/15, 16/17, 1)]

/-- **This row's own profile `φ ≤ φ̃`** (deliberately NOT `phiT`): the value of the first
table interval containing `x`, else `0`.  Half-open on purpose — the closed form gives away 1
at real cells (`ptqa_fold_probe.out` ARM G). -/
def phiSingle (x : ℚ) : ℕ :=
  match phiTable.find? (fun t => decide (t.1 ≤ x ∧ x < t.2.1)) with
  | some t => t.2.2
  | none => 0

/-- The dispatch is total: `phiSingle x` is `0`, or the value of a table row containing `x`. -/
theorem phiSingle_spec (x : ℚ) :
    phiSingle x = 0 ∨ ∃ t ∈ phiTable, t.1 ≤ x ∧ x < t.2.1 ∧ phiSingle x = t.2.2 := by
  unfold phiSingle
  split
  · rename_i t h
    right
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    exact ⟨t, List.mem_of_find?_eq_some h, hp.1, hp.2, rfl⟩
  · left; rfl

/-! ## `piece_unique` — the intervals are nonempty and pairwise disjoint, so the first match is
the only match.  Proved as a CHAIN (40 consecutive checks by `norm_num`) and lifted to
`Pairwise` through transitivity, because `Pairwise` directly is 820 rational comparisons and
times out `simp` at the default heartbeat budget (measured). -/

/-- `s` is a NONEMPTY interval lying entirely before `t`. -/
def Before (s t : ℚ × ℚ × ℕ) : Prop := s.1 < s.2.1 ∧ s.2.1 ≤ t.1

instance : Trans Before Before Before :=
  ⟨fun h1 h2 => ⟨h1.1, h1.2.trans (h2.1.le.trans h2.2)⟩⟩

theorem phiTable_isChain : phiTable.IsChain Before := by
  norm_num [phiTable, List.isChain_cons_cons, Before]

/-- **`piece_unique`.**  Every table row is a nonempty interval, and every row ends at or
before every later row begins: the 41 intervals are pairwise disjoint. -/
theorem phiTable_pairwise : phiTable.Pairwise Before :=
  List.isChain_iff_pairwise.1 phiTable_isChain

/-! ## The dispatch, executed -/

/-- A row's two `ℚ` bounds on `Int.fract ((n:ℚ)/p)`, as the two `ℕ` inequalities every piece
lemma takes (`Zeta2CarryFull.fract_ge_iff` / `fract_lt_iff`). -/
theorem bounds_of_fract (n p c₁ d₁ c₂ d₂ : ℕ) (hp : 0 < p) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hlo : (c₁ : ℚ) / d₁ ≤ Int.fract ((n : ℚ) / p))
    (hhi : Int.fract ((n : ℚ) / p) < (c₂ : ℚ) / d₂) :
    c₁ * p ≤ (n % p) * d₁ ∧ (n % p) * d₂ < c₂ * p :=
  ⟨(fract_ge_iff n p c₁ d₁ hp hd₁).1 hlo, (fract_lt_iff n p c₂ d₂ hp hd₂).1 hhi⟩

/-- **Every table row's value is carried by every window term**, by that row's piece lemma.
One case per row; each case is closed by exactly one `carry_ge_piece<i>_res`, so a row whose
interval or value drifts from its lemma is a red case here, not a silently weaker profile. -/
theorem carry_ge_of_mem_table (a b : ℚ) (v : ℕ) (ht : (a, b, v) ∈ phiTable) (n p k : ℕ)
    [Fact p.Prime] (hk : k ∈ candidateM.window n) (hlo : a ≤ Int.fract ((n : ℚ) / p))
    (hhi : Int.fract ((n : ℚ) / p) < b) (hp2 : 26 * n + 1 < p ^ 2) :
    v ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp only [phiTable, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
  rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- piece 1: [1/15, 1/13), value 1 — PT-Q1's bracket at the residue
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 1 15 1 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece1_res n p k hk (by omega) (by omega) hp2
  · -- piece 2: [1/11, 1/9), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 1 11 1 9 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece2_res n p k hk h1 h2 hp2
  · -- piece 3: [1/9, 2/17), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 1 9 2 17 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece3_res n p k hk h1 h2 hp2
  · -- piece 4: [2/17, 1/7), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 2 17 1 7 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece4_res n p k hk h1 h2 hp2
  · -- piece 5: [1/7, 2/13), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 1 7 2 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece5_res n p k hk h1 h2 hp2
  · -- piece 6: [2/13, 1/6), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 2 13 1 6 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece6_res n p k hk h1 h2 hp2
  · -- piece 7: [1/6, 2/11), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 1 6 2 11 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece7_res n p k hk h1 h2 hp2
  · -- piece 8: [2/11, 1/5), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 2 11 1 5 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece8_res n p k hk h1 h2 hp2
  · -- piece 9: [1/5, 2/9), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 1 5 2 9 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece9_res n p k hk h1 h2 hp2
  · -- piece 10: [2/9, 3/13), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 2 9 3 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece10_res n p k hk h1 h2 hp2
  · -- piece 12: [3/11, 4/13), value 2  (piece 11, [3/13, 3/11), has value 0: off the table)
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 3 11 4 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece12_res n p k hk h1 h2 hp2
  · -- piece 13: [4/13, 1/3), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 4 13 1 3 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece13_res n p k hk h1 h2 hp2
  · -- piece 14: [1/3, 4/11), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 1 3 4 11 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece14_res n p k hk h1 h2 hp2
  · -- piece 15: [4/11, 5/13), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 4 11 5 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece15_res n p k hk h1 h2 hp2
  · -- piece 16: [5/13, 2/5), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 5 13 2 5 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece16_res n p k hk h1 h2 hp2
  · -- piece 17: [3/7, 4/9), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 3 7 4 9 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece17_res n p k hk h1 h2 hp2
  · -- piece 18: [4/9, 5/11), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 4 9 5 11 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece18_res n p k hk h1 h2 hp2
  · -- piece 19: [5/11, 6/13), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 5 11 6 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece19_res n p k hk h1 h2 hp2
  · -- piece 20: [6/13, 7/15), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 6 13 7 15 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece20_res n p k hk h1 h2 hp2
  · -- piece 21: [7/15, 8/17), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 7 15 8 17 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece21_res n p k hk h1 h2 hp2
  · -- piece 22: [8/15, 7/13), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 8 15 7 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece22_res n p k hk h1 h2 hp2
  · -- piece 23: [6/11, 5/9), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 6 11 5 9 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece23_res n p k hk h1 h2 hp2
  · -- piece 24: [5/9, 9/16), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 5 9 9 16 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece24_res n p k hk h1 h2 hp2
  · -- piece 25: [9/16, 3/5), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 9 16 3 5 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece25_res n p k hk h1 h2 hp2
  · -- piece 26: [3/5, 8/13), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 3 5 8 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece26_res n p k hk h1 h2 hp2
  · -- piece 27: [7/11, 11/17), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 7 11 11 17 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece27_res n p k hk h1 h2 hp2
  · -- piece 28: [11/17, 2/3), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 11 17 2 3 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece28_res n p k hk h1 h2 hp2
  · -- piece 29: [2/3, 9/13), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 2 3 9 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece29_res n p k hk h1 h2 hp2
  · -- piece 30: [5/7, 8/11), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 5 7 8 11 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece30_res n p k hk h1 h2 hp2
  · -- piece 31: [8/11, 3/4), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 8 11 3 4 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece31_res n p k hk h1 h2 hp2
  · -- piece 32: [3/4, 10/13), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 3 4 10 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece32_res n p k hk h1 h2 hp2
  · -- piece 33: [10/13, 7/9), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 10 13 7 9 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece33_res n p k hk h1 h2 hp2
  · -- piece 34: [7/9, 4/5), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 7 9 4 5 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece34_res n p k hk h1 h2 hp2
  · -- piece 35: [9/11, 14/17), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 9 11 14 17 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece35_res n p k hk h1 h2 hp2
  · -- piece 36: [14/17, 5/6), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 14 17 5 6 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece36_res n p k hk h1 h2 hp2
  · -- piece 37: [5/6, 11/13), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 5 6 11 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece37_res n p k hk h1 h2 hp2
  · -- piece 38: [11/13, 8/9), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 11 13 8 9 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece38_res n p k hk h1 h2 hp2
  · -- piece 39: [8/9, 10/11), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 8 9 10 11 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece39_res n p k hk h1 h2 hp2
  · -- piece 40: [10/11, 12/13), value 2
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 10 11 12 13 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece40_res n p k hk h1 h2 hp2
  · -- piece 41: [12/13, 14/15), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 12 13 14 15 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece41_res n p k hk h1 h2 hp2
  · -- piece 42: [14/15, 16/17), value 1
    obtain ⟨h1, h2⟩ := bounds_of_fract n p 14 15 16 17 hp (by norm_num) (by norm_num)
      (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    exact carry_ge_piece42_res n p k hk h1 h2 hp2

/-- **The per-term bound at the profile**, every `k` in the window.  Off the table the bound
is `0`; on it, the dispatched piece lemma. -/
theorem phiSingle_le_padicValNat_cTerm (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (hp2 : 26 * n + 1 < p ^ 2) :
    phiSingle (Int.fract ((n : ℚ) / p)) ≤ padicValNat p (cTerm n k) := by
  rcases phiSingle_spec (Int.fract ((n : ℚ) / p)) with h0 | ⟨⟨a, b, v⟩, ht, hlo, hhi, hv⟩
  · rw [h0]; exact Nat.zero_le _
  · rw [hv]; exact carry_ge_of_mem_table a b v ht n p k hk hlo hhi hp2

/-! ## The ultrametric fold, on the signed sum -/

/-- `v ≤ ord_p m` gives `p ^ v ∣ m`, with no nonvanishing side condition. -/
theorem pow_dvd_cTerm_of_le (p n k v : ℕ) [Fact p.Prime] (h : v ≤ padicValNat p (cTerm n k)) :
    p ^ v ∣ cTerm n k :=
  (pow_dvd_pow p h).trans pow_padicValNat_dvd

/-- **The fold.**  A termwise `v ≤ ord_p (cTerm n k)` over the window gives `p ^ v ∣ qnInt n`,
where `qnInt n` is the SIGNED alternating sum exactly as `Zeta2QnInt` defines it — the outer
`(−1)^{16n+1}` and each `(−1)^{12n+k−1}` are absorbed by `Dvd.dvd.mul_left`, and
`Finset.dvd_sum` needs nothing else.  This is `v(Σ) ≥ min v(term)` in divisibility form, which
is sign-agnostic and needs no `Σ ≠ 0`. -/
theorem pow_dvd_qnInt_of_termwise (n p v : ℕ) [Fact p.Prime]
    (h : ∀ k ∈ candidateM.window n, v ≤ padicValNat p (cTerm n k)) :
    (p : ℤ) ^ v ∣ qnInt n := by
  unfold qnInt
  apply Dvd.dvd.mul_left
  apply Finset.dvd_sum
  intro k hk
  apply Dvd.dvd.mul_left
  have := pow_dvd_cTerm_of_le p n k v (h k hk)
  exact_mod_cast this

/-- The same, at `padicValInt`, which needs `qnInt n ≠ 0` because `padicValInt p 0 = 0`. -/
theorem padicValInt_qnInt_ge_of_termwise (n p v : ℕ) [Fact p.Prime] (hq : qnInt n ≠ 0)
    (h : ∀ k ∈ candidateM.window n, v ≤ padicValNat p (cTerm n k)) :
    v ≤ padicValInt p (qnInt n) :=
  ((padicValInt_dvd_iff v (qnInt n)).1 (pow_dvd_qnInt_of_termwise n p v h)).resolve_left hq

/-! ## The row's theorems -/

/-- **PT-QA, the deliverable: `p ^ phiSingle({n/p}) ∣ qₙ` at every prime above the line.**
Unconditional in `n`; this is the shape PT-QB's `PhiT_dvd_qnInt` consumes. -/
theorem pow_phiSingle_dvd_qnInt (n p : ℕ) [Fact p.Prime] (hp2 : 26 * n + 1 < p ^ 2) :
    (p : ℤ) ^ phiSingle (Int.fract ((n : ℚ) / p)) ∣ qnInt n :=
  pow_dvd_qnInt_of_termwise n p _ (fun k hk => phiSingle_le_padicValNat_cTerm n p k hk hp2)

/-- **The cell's statement, with the hypothesis it needs made explicit.**  `padicValInt p 0 = 0`,
so `phiSingle ≤ padicValInt p (qnInt n)` is false wherever `qnInt n = 0` and the residue is on
the table; nothing landed proves `∀ n, qnInt n ≠ 0`, and the chain's own `hrow` asks for one
index only. -/
theorem padicValInt_qnInt_ge_phi (n p : ℕ) [Fact p.Prime] (hp2 : 26 * n + 1 < p ^ 2)
    (hq : qnInt n ≠ 0) :
    phiSingle (Int.fract ((n : ℚ) / p)) ≤ padicValInt p (qnInt n) :=
  padicValInt_qnInt_ge_of_termwise n p _ hq
    (fun k hk => phiSingle_le_padicValNat_cTerm n p k hk hp2)

/-- The unconditional form of the cell's statement: the disjunction `padicValInt_dvd_iff`
actually delivers. -/
theorem padicValInt_qnInt_ge_phi_or_zero (n p : ℕ) [Fact p.Prime] (hp2 : 26 * n + 1 < p ^ 2) :
    qnInt n = 0 ∨ phiSingle (Int.fract ((n : ℚ) / p)) ≤ padicValInt p (qnInt n) :=
  (padicValInt_dvd_iff _ (qnInt n)).1 (pow_phiSingle_dvd_qnInt n p hp2)

/-! ## Non-vacuity and edges (LEAN.md §5) -/

/-- The profile is not identically zero: `1/7` is piece 5, value 2. -/
theorem phiSingle_one_seventh : phiSingle (1 / 7) = 2 := by
  norm_num [phiSingle, phiTable, List.find?]

/-- A right endpoint is OFF its interval — `1/13` is piece 1's `b`, and the value there is `0`
(the closed form would say `1`, and `ptqa_fold_probe.out` ARM G shows `(n, p) = (1, 13)` has
`ord_13 (cTerm 1 k) = 0` at some window term, so `1` would be FALSE). -/
theorem phiSingle_one_thirteenth : phiSingle (1 / 13) = 0 := by
  norm_num [phiSingle, phiTable, List.find?]

/-- Below the first interval the profile is `0`, as at every `p > 15n`. -/
theorem phiSingle_zero : phiSingle 0 = 0 := by
  norm_num [phiSingle, phiTable, List.find?]

/-- `qnInt 1 ≠ 0`, in the kernel, so the cell `(1, 7)` below is a real `padicValInt` bound. -/
theorem qnInt_one_ne_zero : qnInt 1 ≠ 0 := by
  simp only [qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- **The theorem at a real cell.**  `(n, p) = (1, 7)`: `27 < 49`, `{1/7} = 1/7` is piece 5, so
`7² ∣ q₁` and `2 ≤ ord_7 q₁` — the value-2 piece nearest the origin the cell named as its
second probe, discharged by the composed theorem rather than by a kernel computation. -/
theorem fract_one_seventh : Int.fract (((1 : ℕ) : ℚ) / ((7 : ℕ) : ℚ)) = 1 / 7 := by
  rw [Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]
  norm_num

theorem seven_sq_dvd_qnInt_one : (7 : ℤ) ^ 2 ∣ qnInt 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := pow_phiSingle_dvd_qnInt 1 7 (by norm_num)
  rw [fract_one_seventh, phiSingle_one_seventh] at h
  exact_mod_cast h

theorem two_le_padicValInt_seven_qnInt_one : 2 ≤ padicValInt 7 (qnInt 1) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := padicValInt_qnInt_ge_phi 1 7 (by norm_num) qnInt_one_ne_zero
  rw [fract_one_seventh, phiSingle_one_seventh] at h
  exact h

/-- **The half-open endpoint is load-bearing at the FOLD, not only per term.**  At
`(n, p) = (1, 13)` the residue is exactly `1/13`, piece 1's right endpoint; the closed table
would put `1` there, and `13 ∤ q₁` (`q₁ = −9923952931816770`, `ord₁₃ = 0`, `ptqa_fold_probe.py`),
so that `1` would be a FALSE theorem.  `phiSingle_one_thirteenth` says the profile puts `0`. -/
theorem qnInt_one_emod_thirteen : qnInt 1 % 13 ≠ 0 := by
  simp only [qnInt, cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem not_thirteen_dvd_qnInt_one : ¬ (13 : ℤ) ∣ qnInt 1 :=
  fun h => qnInt_one_emod_thirteen (Int.emod_eq_zero_of_dvd h)

end Zeta2Arith

#print axioms Zeta2Arith.phiSingle_spec
#print axioms Zeta2Arith.phiTable_isChain
#print axioms Zeta2Arith.phiTable_pairwise
#print axioms Zeta2Arith.bounds_of_fract
#print axioms Zeta2Arith.carry_ge_of_mem_table
#print axioms Zeta2Arith.phiSingle_le_padicValNat_cTerm
#print axioms Zeta2Arith.pow_dvd_cTerm_of_le
#print axioms Zeta2Arith.pow_dvd_qnInt_of_termwise
#print axioms Zeta2Arith.padicValInt_qnInt_ge_of_termwise
#print axioms Zeta2Arith.pow_phiSingle_dvd_qnInt
#print axioms Zeta2Arith.padicValInt_qnInt_ge_phi
#print axioms Zeta2Arith.padicValInt_qnInt_ge_phi_or_zero
#print axioms Zeta2Arith.phiSingle_one_seventh
#print axioms Zeta2Arith.phiSingle_one_thirteenth
#print axioms Zeta2Arith.phiSingle_zero
#print axioms Zeta2Arith.qnInt_one_ne_zero
#print axioms Zeta2Arith.fract_one_seventh
#print axioms Zeta2Arith.seven_sq_dvd_qnInt_one
#print axioms Zeta2Arith.two_le_padicValInt_seven_qnInt_one
#print axioms Zeta2Arith.qnInt_one_emod_thirteen
#print axioms Zeta2Arith.not_thirteen_dvd_qnInt_one
