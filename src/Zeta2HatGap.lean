/-
# PT-QB clump 2, the SHAPE TEST — one gap cell's carry lemma, end to end

Row PT-QB of `docs/future/zeta2-lean-chain.md` (registry `2B0.AW`).  `ptqb_gap_probe.py`
measured that `φ̃ > φ` on exactly five intervals and that the hat's four-bit carry-min reaches
`φ̃` on all of them; `ptqb_cover_probe.py` measured the case structure — 4 essential branches
for each `v = 2` cell, 3 for the one `v = 1` cell.  Neither is a Lean proof.

This module does the `v = 1` cell, `[3/13, 4/17)`, the smallest of the five, as the shape test
the row's cell names as its next probe: if the branch structure does not go through here, the
other four do not either.

## The three reusable pieces, and where they came from

`Zeta2CarryFull` has the tale-1 versions of two of these (`mul_mod_small`, `bit4_sum_mod`).
Both are SPECIALISED — `mul_mod_small` needs `a * (n % p) < p`, which is false for the hat's
`17n` on every one of the five cells, and `bit4_sum_mod` is stated at the tale-1 window's own
two offsets.  So this module proves the general forms rather than importing and working around
them, and a later clump should re-point the tale-1 call sites at these:

* `mul_mod_congr` — `a * n % p = a * (n % p) % p`, no size condition at all.
* `mod_eq_sub_mul` — `a % p = a − k·p` when `k·p ≤ a` and `a − k·p < p`.  This is the piece
  `mul_mod_small` cannot do and every hat cell needs: on `[3/13, 4/17)`, `17n % p = 17r − 3p`
  and `11n % p = 11r − 2p`, both genuinely wrapped.
* `carry_iff_of_add` — **a complementary-pair carry bit is a comparison of ONE residue with the
  sum's**: for `A + B = S`, `p ≤ A%p + B%p ↔ S%p < A%p`.  Two of the hat's four bits are
  complementary pairs summing to `11n` (`(3n+j) + (8n−j)` and `(n+j) + (10n−j)`), so this turns
  both into inequalities in `r = n % p` and `u = j % p`, which is what makes the branches
  `omega`-closable.  `Zeta2CarryFull.bit4_sum_mod` is this fact at one instance.

## The cell, and why it has three branches

`r/p ∈ [3/13, 4/17)` is `3p ≤ 13r` and `17r < 4p`.  There `17r ∈ (3p, 4p)`, `11r ∈ (2p, 3p)`
and `3r < p`, so bit 1 fires unless `(2u)%p < 4p − 17r` — a window of width at most `p/13`.
`ptqb_cover_probe.out` reports the greedy cover as `{bit1}, {bit2}, {bit3}` with all three
essential, and that is exactly this proof: on the low half of that narrow window `3r + u < p`
and bit 2 fires (because `11r − 2p < 3r` already, from `4r < p`); on the high half `u ≥ p/2`,
`r + u < p`, and bit 3 fires (because `10r − 2p < p/2 ≤ u`).  Bit 4 is not used here, which is
why the probe's cover has three members and not four.

**And the proof turns out to hold on more than the cell.**  Its five lap facts are implied by
`p < 5r` alone, not by `3p ≤ 13r`, and the statement itself is true on all of `(1/5, 4/17)`
(measured: `ptqb_cover_probe.py` ARM H, 0 failures above `1/5`, 211 below it, the largest
failing residue `123/677`).  So `hat_carry_lowcell` is stated at `p < 5·(n%p)` and
`hat_carry_gap2` is the cell's instance of it, one `omega` away.  The falsifier's ARM L found
that gap — it weakened `3/13` to `3/14` and came back GREEN, which is the only way a statement
weaker than its proof gets noticed.

## What this file does NOT claim

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  This is ONE of the five
gap cells.  The other four — all `v = 2`, all needing four branches and two bits each — and the
`φ̃ ≤ max(φ, φ̂)` dispatch over the 52-cell refinement, and `PhiT_dvd_qnInt`, are not here.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2HatCarry
-- for `Zeta2Arith.phiSingle` in the non-vacuity section only: this cell is a GAP in PT-QA's
-- 41-row table, and saying so needs that table.
import Zeta2CarryFold

namespace Zeta2HatGap

open Zeta2Defs Zeta2Hat Nat

/-! ## The three reusable residue pieces -/

/-- `a * n % p = a * (n % p) % p`, with NO size condition — the general form of
`Zeta2CarryFull.mul_mod_small`, which additionally needs `a * (n % p) < p` and is therefore
unavailable for the hat's `17n` on every one of the five gap cells. -/
theorem mul_mod_congr (a n p : ℕ) : a * n % p = a * (n % p) % p :=
  (Nat.ModEq.mul_left a (Nat.mod_modEq n p)).symm

/-- `a % p = a − k·p` when `a` lies in the `k`-th lap.  The piece the hat needs and the tale-1
machinery does not have: its residues genuinely wrap. -/
theorem mod_eq_sub_mul (a p k : ℕ) (h1 : k * p ≤ a) (h2 : a - k * p < p) : a % p = a - k * p := by
  conv_lhs => rw [show a = (a - k * p) + k * p from by omega]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt h2

/-- **A complementary-pair carry bit is a comparison with the sum's residue.**  If `A + B = S`
then `A % p + B % p` is either `S % p` or `S % p + p`, and the carry fires exactly in the second
case — which happens exactly when `A`'s own residue exceeds `S`'s.  `Zeta2CarryFull.bit4_sum_mod`
is this at the tale-1 window's instance; the hat has TWO such pairs, both summing to `11n`. -/
theorem carry_iff_of_add (p A B : ℕ) (hp : 0 < p) :
    (p ≤ A % p + B % p) ↔ (A + B) % p < A % p := by
  have ha : A % p < p := Nat.mod_lt _ hp
  have hb : B % p < p := Nat.mod_lt _ hp
  have hs : (A + B) % p = (A % p + B % p) % p := Nat.add_mod A B p
  rcases lt_or_ge (A % p + B % p) p with h | h
  · rw [hs, Nat.mod_eq_of_lt h]
    constructor <;> intro _ <;> omega
  · have hw : (A % p + B % p) % p = A % p + B % p - p := by
      simpa using mod_eq_sub_mul (A % p + B % p) p 1 (by omega) (by omega)
    rw [hs, hw]
    constructor <;> intro _ <;> omega

/-! ## Gap cell 2 of 5: `[3/13, 4/17)`, where `φ = 0` and `φ̃ = 1` -/

/-- **The bound at its TRUE domain, `(1/5, 4/17)`, which strictly contains the cell.**

Stated at `p < 5·(n%p)` rather than at the cell's own `3p ≤ 13·(n%p)`, and that is a
MEASUREMENT, not a generalisation for its own sake.  `falsify_hatgap.sh`'s first draft weakened
the cell's left bound `3/13 → 3/14` and came back GREEN: the five lap facts this proof runs on
(`2p ≤ 11r`, `p < 5r`, `3p ≤ 17r`, `4r < p`, `11r < 3p`) are all implied by something much
weaker than `3/13`, and the binding one is `p < 5r`.  So the arm had found a real gap between
the theorem and its statement.  `domain.py` (folded into `ptqb_cover_probe.py` ARM H) then
measured the statement itself over `[1/8, 4/17)`: **0 failures above `1/5`, 211 below it, the
largest failing residue `123/677 ≈ 0.18168`** — so `1/5` is where the bound really gives way
and this is the honest hypothesis.  Stating it here rather than at `3/13` is what lets ARM L
bite on TRUTH (it widens to `p < 6·(n%p)`, which admits `123/677`) instead of on proof
mechanics.

At EVERY `j ≤ 8n`, at least one of the hat's four one-term carry bits fires. -/
theorem hat_carry_lowcell (n p j : ℕ) [hp : Fact p.Prime] (hj : j ≤ 8 * n)
    (hlo : p < 5 * (n % p)) (hhi : 17 * (n % p) < 4 * p) :
    1 ≤ (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0)
      + (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0)
      + (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0)
      + (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0) := by
  have hp0 : 0 < p := hp.out.pos
  have hr : n % p < p := Nat.mod_lt _ hp0
  have hu : j % p < p := Nat.mod_lt _ hp0
  -- `3r < p` (from `17r < 4p`), `2p < 11r` and `3p ≤ 17r` (from `3p ≤ 13r`): the three
  -- lap facts this cell runs on, all linear in `r` and `p`.
  have h3r : 3 * (n % p) < p := by omega
  have e17 : (17 * n) % p = 17 * (n % p) - 3 * p := by
    rw [mul_mod_congr 17 n p]
    exact mod_eq_sub_mul _ p 3 (by omega) (by omega)
  have e11 : (11 * n) % p = 11 * (n % p) - 2 * p := by
    rw [mul_mod_congr 11 n p]
    exact mod_eq_sub_mul _ p 2 (by omega) (by omega)
  have e2j : (2 * j) % p = (2 * (j % p)) % p := mul_mod_congr 2 j p
  have e3n : (3 * n) % p = 3 * (n % p) := by
    rw [mul_mod_congr 3 n p]; exact Nat.mod_eq_of_lt h3r
  have e3nj : (3 * n + j) % p = (3 * (n % p) + j % p) % p := by
    rw [Nat.add_mod, e3n]
  have enj : (n + j) % p = (n % p + j % p) % p := Nat.add_mod n j p
  have b2iff := carry_iff_of_add p (3 * n + j) (8 * n - j) hp0
  have b3iff := carry_iff_of_add p (n + j) (10 * n - j) hp0
  rw [show 3 * n + j + (8 * n - j) = 11 * n from by omega] at b2iff
  rw [show n + j + (10 * n - j) = 11 * n from by omega] at b3iff
  -- ORDER MATTERS, measured: folding the two complementary bits and the residue rewrites into
  -- one `simp only` leaves the bits UNCONVERTED — `e3nj` fires inside the `p ≤ _ + _` first and
  -- `b2iff`'s left-hand side then no longer matches, so the goal keeps the two-residue form and
  -- `omega` sees `(8n−j) % p` as an atom it knows nothing about.  Two passes, bits first.
  -- `2u` is in lap 0 or lap 1, and that is the only case split bit 1 needs.
  have h2m : (2 * (j % p)) % p < p := Nat.mod_lt _ hp0
  have ht : (2 * (j % p)) % p = 2 * (j % p) ∨ (2 * (j % p)) % p + p = 2 * (j % p) := by
    rcases lt_or_ge (2 * (j % p)) p with h | h
    · exact Or.inl (Nat.mod_eq_of_lt h)
    · have := mod_eq_sub_mul (2 * (j % p)) p 1 (by omega) (by omega)
      exact Or.inr (by omega)
  -- THE COVER, as a disjunction in the GOAL'S OWN vocabulary, proved before anything touches
  -- the goal.  Rewriting the goal instead does not work: `simp` re-normalises mod expressions
  -- (`2 * (j%p) % p` back to `2 * j % p`, `(n%p + j%p) % p` back to `(n+j) % p`), so a `have`
  -- stated in the `(r, u)` language stops matching the `ite` it was meant to discharge —
  -- measured here 2026-09-19, three unsolved goals.  Proving the disjunction first and letting
  -- `simp [h]` close ONE `ite` sidesteps the normal form entirely.
  have key : (p ≤ (2 * j) % p + (17 * n) % p)
      ∨ (p ≤ (3 * n + j) % p + (8 * n - j) % p)
      ∨ (p ≤ (n + j) % p + (10 * n - j) % p) := by
    rw [b2iff, b3iff, e11, e3nj, enj, e2j, e17]
    rcases lt_or_ge ((2 * (j % p)) % p + (17 * (n % p) - 3 * p)) p with hb1 | hb1
    · -- bit 1 does NOT fire: `(2u)%p < 4p − 17r`, a window of width at most `p/13`.
      rcases ht with h | h
      · -- lap 0: `2u < 4p − 17r`, so `3r + u < p` (which needs `2p < 11r`) and bit 2 fires
        -- (which needs `4r < p`, i.e. `11r − 2p < 3r` — true on the whole cell).
        refine Or.inr (Or.inl ?_)
        have hlt : 3 * (n % p) + j % p < p := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
      · -- lap 1: `2u ≥ p` and `2u < 5p − 17r`, so `r + u < p` (needs `p < 5r`) and bit 3
        -- fires (needs `10r − 2p < u`, which `2u ≥ p` gives because `4r < p`).
        refine Or.inr (Or.inr ?_)
        have hlt : n % p + j % p < p := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
    · exact Or.inl hb1
  rcases key with h | h | h
  · have hA : (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0) = 1 := by simp [h]
    omega
  · have hB : (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0) = 1 := by simp [h]
    omega
  · have hC : (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0) = 1 := by simp [h]
    omega

/-- **GAP CELL 2 OF 5, at its own bounds**: `[3/13, 4/17)`, which is `3p ≤ 13·(n%p)` and
`17·(n%p) < 4p` — exactly `Int.fract (n/p) ∈ [3/13, 4/17)` through
`Zeta2CarryFull.fract_ge_iff`/`fract_lt_iff`.  One `omega` away from `hat_carry_lowcell`,
because `3p ≤ 13r` gives `5r ≥ 15p/13 > p`.  This is the instance the profile dispatch will
consume; the theorem above is what is actually true. -/
theorem hat_carry_gap2 (n p j : ℕ) [Fact p.Prime] (hj : j ≤ 8 * n)
    (hlo : 3 * p ≤ 13 * (n % p)) (hhi : 17 * (n % p) < 4 * p) :
    1 ≤ (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0)
      + (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0)
      + (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0)
      + (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0) :=
  hat_carry_lowcell n p j hj (by omega) hhi

/-- **The cell, folded: `p ∣ qₙ` at every prime whose residue lands on `[3/13, 4/17)`.**  This
is the gap-cell lemma composed with `Zeta2HatCarry.pow_dvd_hatQ_of_bits`; PAIR then carries it
to `qnInt` (`Zeta2HatQnInt.pow_dvd_qnInt_of_hat_bits`, not imported here so that this module
stays on the cheap olean store). -/
theorem p_dvd_hatQ_gap2 (n p : ℕ) [Fact p.Prime]
    (hlo : 3 * p ≤ 13 * (n % p)) (hhi : 17 * (n % p) < 4 * p) :
    (p : ℤ) ∣ hatQ n := by
  have h := Zeta2HatCarry.pow_dvd_hatQ_of_bits n p 1
    (fun j hj => hat_carry_gap2 n p j hj hlo hhi)
  simpa using h

/-! ## Gap cell 1 of 5: `[1/9, 2/17)`, where `φ = 1` and `φ̃ = 2` — the first `v = 2` cell

Four branches, which is what `ptqb_cover_probe.out` measures for every `v = 2` cell, and the
`u`-order is forced: `0 ≤ p−5r < p−3r < 2p−10r < p`, with the pair `(bit2, bit4)`, `(bit2,
bit3)`, `(bit1, bit3)`, `(bit1, bit4)` in turn.  Two boundaries are the cell's own hypotheses
and not conveniences: `2p−10r ≤ p−r` is `p ≤ 9r`, the LEFT bound, and it is what stops the
third and fourth branches from leaving a hole; `11r ≥ p` (also the left bound) is what makes
bit 1 fire from `p−3r` onwards.  The right bound `17r < 2p` puts `17r` and `11r` in lap 1, and
`3r`, `5r`, `8r` below `p`. -/

/-- **Gap cell 1: `[1/9, 2/17)`, `φ̃ = 2`.**  On `p ≤ 9·(n%p)` and `17·(n%p) < 2p`, at least
TWO of the hat's four one-term carry bits fire, at every `j ≤ 8n`.  PT-QA's profile is `1`
there (`phiSingle` on `[1/9, 2/17)`), so this cell is a genuine `+1` and not a gap in the
41-row table — the other kind of rescue. -/
theorem hat_carry_gap1 (n p j : ℕ) [hp : Fact p.Prime] (hj : j ≤ 8 * n)
    (hlo : p ≤ 9 * (n % p)) (hhi : 17 * (n % p) < 2 * p) :
    2 ≤ (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0)
      + (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0)
      + (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0)
      + (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0) := by
  have hp0 : 0 < p := hp.out.pos
  have hr : n % p < p := Nat.mod_lt _ hp0
  have hu : j % p < p := Nat.mod_lt _ hp0
  have h3r : 3 * (n % p) < p := by omega
  have h5r : 5 * (n % p) < p := by omega
  -- `simpa`, not `exact`: `mod_eq_sub_mul`'s conclusion is `a - k * p`, and at `k = 1` that is
  -- `a - 1 * p`, which does not unify with `a - p` — the `_` then stays a metavariable and the
  -- side-condition `omega`s fire on an unknown `a` (measured here 2026-09-19).
  have e17 : (17 * n) % p = 17 * (n % p) - p := by
    rw [mul_mod_congr 17 n p]
    simpa using mod_eq_sub_mul (17 * (n % p)) p 1 (by omega) (by omega)
  have e11 : (11 * n) % p = 11 * (n % p) - p := by
    rw [mul_mod_congr 11 n p]
    simpa using mod_eq_sub_mul (11 * (n % p)) p 1 (by omega) (by omega)
  have e2j : (2 * j) % p = (2 * (j % p)) % p := mul_mod_congr 2 j p
  have e3n : (3 * n) % p = 3 * (n % p) := by
    rw [mul_mod_congr 3 n p]; exact Nat.mod_eq_of_lt h3r
  have e5n : (5 * n) % p = 5 * (n % p) := by
    rw [mul_mod_congr 5 n p]; exact Nat.mod_eq_of_lt h5r
  have e3nj : (3 * n + j) % p = (3 * (n % p) + j % p) % p := by rw [Nat.add_mod, e3n]
  have e5nj : (5 * n + j) % p = (5 * (n % p) + j % p) % p := by rw [Nat.add_mod, e5n]
  have enj : (n + j) % p = (n % p + j % p) % p := Nat.add_mod n j p
  have b2iff := carry_iff_of_add p (3 * n + j) (8 * n - j) hp0
  have b3iff := carry_iff_of_add p (n + j) (10 * n - j) hp0
  rw [show 3 * n + j + (8 * n - j) = 11 * n from by omega] at b2iff
  rw [show n + j + (10 * n - j) = 11 * n from by omega] at b3iff
  have h2m : (2 * (j % p)) % p < p := Nat.mod_lt _ hp0
  have ht : (2 * (j % p)) % p = 2 * (j % p) ∨ (2 * (j % p)) % p + p = 2 * (j % p) := by
    rcases lt_or_ge (2 * (j % p)) p with h | h
    · exact Or.inl (Nat.mod_eq_of_lt h)
    · have := mod_eq_sub_mul (2 * (j % p)) p 1 (by omega) (by omega)
      exact Or.inr (by omega)
  -- The four branches, as a disjunction of PAIRS in the goal's own vocabulary.  Same reason as
  -- in `hat_carry_lowcell`: rewriting the goal loses to `simp`'s mod normal form.
  have key :
      ((p ≤ (3 * n + j) % p + (8 * n - j) % p) ∧ (p ≤ (5 * n) % p + (5 * n + j) % p))
      ∨ ((p ≤ (3 * n + j) % p + (8 * n - j) % p) ∧ (p ≤ (n + j) % p + (10 * n - j) % p))
      ∨ ((p ≤ (2 * j) % p + (17 * n) % p) ∧ (p ≤ (n + j) % p + (10 * n - j) % p))
      ∨ ((p ≤ (2 * j) % p + (17 * n) % p) ∧ (p ≤ (5 * n) % p + (5 * n + j) % p)) := by
    rw [b2iff, b3iff, e11, e3nj, enj, e2j, e17, e5n, e5nj]
    rcases lt_or_ge (j % p + 5 * (n % p)) p with h1 | h1
    · -- u < p − 5r: bit 4 from `p ≤ 10r`, bit 2 from `8r < p`
      refine Or.inl ⟨?_, ?_⟩
      · rw [Nat.mod_eq_of_lt (show 3 * (n % p) + j % p < p by omega)]; omega
      · rw [Nat.mod_eq_of_lt (show 5 * (n % p) + j % p < p by omega)]; omega
    · rcases lt_or_ge (j % p + 3 * (n % p)) p with h2 | h2
      · -- p − 5r ≤ u < p − 3r: bit 2 still in lap 0, bit 3 from `15r < 2p`
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [Nat.mod_eq_of_lt (show 3 * (n % p) + j % p < p by omega)]; omega
        · rw [Nat.mod_eq_of_lt (show n % p + j % p < p by omega)]; omega
      · rcases lt_or_ge (j % p + 10 * (n % p)) (2 * p) with h3 | h3
        · -- p − 3r ≤ u < 2p − 10r: bit 1 fires (needs `11r ≥ p`), bit 3 still in lap 0
          -- (needs `p ≤ 9r`, the cell's LEFT bound — this is where it is load-bearing)
          refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
          · omega
          · rw [Nat.mod_eq_of_lt (show n % p + j % p < p by omega)]; omega
        · -- u ≥ 2p − 10r: bit 1 (needs `3r ≤ p`), bit 4 now in lap 1
          refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
          · omega
          · have hw : (5 * (n % p) + j % p) % p = 5 * (n % p) + j % p - p := by
              simpa using mod_eq_sub_mul (5 * (n % p) + j % p) p 1 (by omega) (by omega)
            rw [hw]
            omega
  -- Each branch turns its two conditions into `= 1` equations about the goal's OWN `ite`
  -- terms, which `omega` then adds up; the other two `ite`s stay atoms and are only ever
  -- known to be `≥ 0`, which is all that is needed.
  have hB2 : ∀ _h : p ≤ (3 * n + j) % p + (8 * n - j) % p,
      (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0) = 1 := fun h => by simp [h]
  have hB3 : ∀ _h : p ≤ (n + j) % p + (10 * n - j) % p,
      (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0) = 1 := fun h => by simp [h]
  have hB1 : ∀ _h : p ≤ (2 * j) % p + (17 * n) % p,
      (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0) = 1 := fun h => by simp [h]
  have hB4 : ∀ _h : p ≤ (5 * n) % p + (5 * n + j) % p,
      (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0) = 1 := fun h => by simp [h]
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have := hB2 ha; have := hB4 hb; omega
  · have := hB2 ha; have := hB3 hb; omega
  · have := hB1 ha; have := hB3 hb; omega
  · have := hB1 ha; have := hB4 hb; omega

/-- The cell folded: `p² ∣ hatQ n` wherever the residue lands on `[1/9, 2/17)`. -/
theorem sq_dvd_hatQ_gap1 (n p : ℕ) [Fact p.Prime]
    (hlo : p ≤ 9 * (n % p)) (hhi : 17 * (n % p) < 2 * p) :
    (p : ℤ) ^ 2 ∣ hatQ n :=
  Zeta2HatCarry.pow_dvd_hatQ_of_bits n p 2 (fun j hj => hat_carry_gap1 n p j hj hlo hhi)

/-! ## Gap cell 5 of 5: `[12/13, 14/15)`, the cell nearest `1`

Taken third on purpose: its lap constants are the largest of the five (`17r/p ∈ [15.69, 15.87)`,
`11r/p ∈ [10.15, 10.27)`, `5r/p ∈ [4.615, 4.667)`), so it is the likeliest to need something
the three shared pieces do not supply.  It does not — the only new phenomenon is that `r + u`
and `3r − 2p + u` now WRAP in the last two branches, which `mod_eq_sub_mul` handles exactly as
it handles `17r`.

Five branches rather than four, and the `u`-order is again forced:
`0 ≤ p−r ≤ 3p−3r ≤ 10r−9p ≤ 8r−7p < p`, with pairs `(2,3) (2,4) (1,4) (1,3) (2,3)`.  The
middle boundary `3p−3r ≤ 10r−9p` IS the cell's left bound `12p ≤ 13r`, and `5r−4p+u < p` in
the third branch IS its right bound `15r < 14p`: both hypotheses are load-bearing at a named
step, which is what `falsify_hatgap.sh` ARMs L5 and H5 check. -/

/-- **Gap cell 5: `[12/13, 14/15)`, `φ̃ = 2`.**  On `12p ≤ 13·(n%p)` and `15·(n%p) < 14p`, at
least TWO of the hat's four one-term carry bits fire, at every `j ≤ 8n`. -/
theorem hat_carry_gap5 (n p j : ℕ) [hp : Fact p.Prime] (hj : j ≤ 8 * n)
    (hlo : 12 * p ≤ 13 * (n % p)) (hhi : 15 * (n % p) < 14 * p) :
    2 ≤ (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0)
      + (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0)
      + (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0)
      + (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0) := by
  have hp0 : 0 < p := hp.out.pos
  have hr : n % p < p := Nat.mod_lt _ hp0
  have hu : j % p < p := Nat.mod_lt _ hp0
  have e17 : (17 * n) % p = 17 * (n % p) - 15 * p := by
    rw [mul_mod_congr 17 n p]
    exact mod_eq_sub_mul _ p 15 (by omega) (by omega)
  have e11 : (11 * n) % p = 11 * (n % p) - 10 * p := by
    rw [mul_mod_congr 11 n p]
    exact mod_eq_sub_mul _ p 10 (by omega) (by omega)
  have e5n : (5 * n) % p = 5 * (n % p) - 4 * p := by
    rw [mul_mod_congr 5 n p]
    exact mod_eq_sub_mul _ p 4 (by omega) (by omega)
  have e3n : (3 * n) % p = 3 * (n % p) - 2 * p := by
    rw [mul_mod_congr 3 n p]
    exact mod_eq_sub_mul _ p 2 (by omega) (by omega)
  have e2j : (2 * j) % p = (2 * (j % p)) % p := mul_mod_congr 2 j p
  have e3nj : (3 * n + j) % p = (3 * (n % p) - 2 * p + j % p) % p := by rw [Nat.add_mod, e3n]
  have e5nj : (5 * n + j) % p = (5 * (n % p) - 4 * p + j % p) % p := by rw [Nat.add_mod, e5n]
  have enj : (n + j) % p = (n % p + j % p) % p := Nat.add_mod n j p
  have b2iff := carry_iff_of_add p (3 * n + j) (8 * n - j) hp0
  have b3iff := carry_iff_of_add p (n + j) (10 * n - j) hp0
  rw [show 3 * n + j + (8 * n - j) = 11 * n from by omega] at b2iff
  rw [show n + j + (10 * n - j) = 11 * n from by omega] at b3iff
  have key :
      ((p ≤ (3 * n + j) % p + (8 * n - j) % p) ∧ (p ≤ (n + j) % p + (10 * n - j) % p))
      ∨ ((p ≤ (3 * n + j) % p + (8 * n - j) % p) ∧ (p ≤ (5 * n) % p + (5 * n + j) % p))
      ∨ ((p ≤ (2 * j) % p + (17 * n) % p) ∧ (p ≤ (5 * n) % p + (5 * n + j) % p))
      ∨ ((p ≤ (2 * j) % p + (17 * n) % p) ∧ (p ≤ (n + j) % p + (10 * n - j) % p)) := by
    rw [b2iff, b3iff, e11, e3nj, enj, e2j, e17, e5n, e5nj]
    rcases lt_or_ge (j % p + n % p) p with h1 | h1
    · -- u < p − r: bits 2 and 3, both still in their low lap
      refine Or.inl ⟨?_, ?_⟩
      · rw [Nat.mod_eq_of_lt (show 3 * (n % p) - 2 * p + j % p < p by omega)]; omega
      · rw [Nat.mod_eq_of_lt (show n % p + j % p < p by omega)]; omega
    · rcases lt_or_ge (j % p + 3 * (n % p)) (3 * p) with h2 | h2
      · -- p − r ≤ u < 3p − 3r: bit 3 has wrapped out, bit 4 comes in
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [Nat.mod_eq_of_lt (show 3 * (n % p) - 2 * p + j % p < p by omega)]; omega
        · rw [Nat.mod_eq_of_lt (show 5 * (n % p) - 4 * p + j % p < p by omega)]; omega
      -- `le_or_lt` is not an identifier at this pin (measured); `lt_or_ge` is, so the two
      -- branches come out in the opposite order.
      · rcases lt_or_ge (10 * (n % p)) (j % p + 9 * p) with h3 | h3
        · rcases lt_or_ge (8 * (n % p)) (j % p + 7 * p) with h4 | h4
          · -- u > 8r − 7p: bits 2 and 3, both wrapped
            refine Or.inl ⟨?_, ?_⟩
            · have hw : (3 * (n % p) - 2 * p + j % p) % p = 3 * (n % p) - 2 * p + j % p - p := by
                simpa using
                  mod_eq_sub_mul (3 * (n % p) - 2 * p + j % p) p 1 (by omega) (by omega)
              rw [hw]; omega
            · have hw : (n % p + j % p) % p = n % p + j % p - p := by
                simpa using mod_eq_sub_mul (n % p + j % p) p 1 (by omega) (by omega)
              rw [hw]; omega
          · -- 10r − 9p < u ≤ 8r − 7p: bit 1 still fires; bit 3 comes back, now WRAPPED
            refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
            · rw [Nat.mod_eq_of_lt (show 2 * (j % p) < p by omega)]; omega
            · have hw : (n % p + j % p) % p = n % p + j % p - p := by
                simpa using mod_eq_sub_mul (n % p + j % p) p 1 (by omega) (by omega)
              rw [hw]; omega
        · -- 3p − 3r ≤ u ≤ 10r − 9p: bit 2 is out too; bit 1 fires (needs `11r ≥ 10p`) and
          -- bit 4 is still in lap 0 (needs `15r < 14p`, the cell's RIGHT bound)
          refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
          · rw [Nat.mod_eq_of_lt (show 2 * (j % p) < p by omega)]; omega
          · rw [Nat.mod_eq_of_lt (show 5 * (n % p) - 4 * p + j % p < p by omega)]; omega
  have hB2 : ∀ _h : p ≤ (3 * n + j) % p + (8 * n - j) % p,
      (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0) = 1 := fun h => by simp [h]
  have hB3 : ∀ _h : p ≤ (n + j) % p + (10 * n - j) % p,
      (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0) = 1 := fun h => by simp [h]
  have hB1 : ∀ _h : p ≤ (2 * j) % p + (17 * n) % p,
      (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0) = 1 := fun h => by simp [h]
  have hB4 : ∀ _h : p ≤ (5 * n) % p + (5 * n + j) % p,
      (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0) = 1 := fun h => by simp [h]
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have := hB2 ha; have := hB3 hb; omega
  · have := hB2 ha; have := hB4 hb; omega
  · have := hB1 ha; have := hB4 hb; omega
  · have := hB1 ha; have := hB3 hb; omega

/-- The cell folded: `p² ∣ hatQ n` wherever the residue lands on `[12/13, 14/15)`. -/
theorem sq_dvd_hatQ_gap5 (n p : ℕ) [Fact p.Prime]
    (hlo : 12 * p ≤ 13 * (n % p)) (hhi : 15 * (n % p) < 14 * p) :
    (p : ℤ) ^ 2 ∣ hatQ n :=
  Zeta2HatCarry.pow_dvd_hatQ_of_bits n p 2 (fun j hj => hat_carry_gap5 n p j hj hlo hhi)

/-! ## Non-vacuity: the cells are inhabited, and PT-QA is short on both (LEAN.md §5) -/

/-- `(10, 43)`: `10/43 ≈ 0.2326 ∈ [3/13, 4/17)`, one of the thirteen rescue cells of
`hat_carry_probe.out` (line 114: `φ̃ = 1`, hat carry-min 1, tale-1 carry-min 0). -/
theorem gap2_inhabited : 3 * 43 ≤ 13 * (10 % 43) ∧ 17 * (10 % 43) < 4 * 43 := by norm_num

theorem forty_three_dvd_hatQ_ten : (43 : ℤ) ∣ hatQ 10 := by
  have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  exact p_dvd_hatQ_gap2 10 43 (by norm_num) (by norm_num)

/-- `(12, 103)`, the cell the ROW named as its probe, lies in gap cell 1: `12/103 ≈ 0.11650`
and `[1/9, 2/17) = [0.1111, 0.11765)`. -/
theorem gap1_contains_twelve_103 : 103 ≤ 9 * (12 % 103) ∧ 17 * (12 % 103) < 2 * 103 := by
  norm_num

/-- **THE ROW'S NAMED CELL, NOW A THEOREM RATHER THAN A KERNEL COMPUTATION.**
`Zeta2HatCarry.sq_103_dvd_hatQ_twelve` proved `103² ∣ hatQ 12` by evaluating a 97-term sum of
`C(204+2j, 2j)`-class binomials in the kernel.  This proves the SAME fact from the general
carry analysis of gap cell 1, at symbolic `n` and `p`, with no kernel arithmetic at all — so
the cell's own probe is now a corollary of the row's machinery, and the two routes agree. -/
theorem sq_103_dvd_hatQ_twelve_via_gap1 : (103 : ℤ) ^ 2 ∣ hatQ 12 := by
  have : Fact (Nat.Prime 103) := ⟨by norm_num⟩
  exact sq_dvd_hatQ_gap1 12 103 (by norm_num) (by norm_num)

/-- **PT-QA's profile is ZERO on this cell** — `[3/13, 4/17)` is a GAP in the 41-row table, not
a lower value there, so the tale-1 half gives `43 ^ 0 ∣ q₁₀` and nothing else.  This is the
sharpest of the five cells in that sense. -/
theorem phiSingle_ten_43 : Zeta2Arith.phiSingle (10 / 43) = 0 := by
  norm_num [Zeta2Arith.phiSingle, Zeta2Arith.phiTable, List.find?]

end Zeta2HatGap

#print axioms Zeta2HatGap.mul_mod_congr
#print axioms Zeta2HatGap.mod_eq_sub_mul
#print axioms Zeta2HatGap.carry_iff_of_add
#print axioms Zeta2HatGap.hat_carry_lowcell
#print axioms Zeta2HatGap.hat_carry_gap2
#print axioms Zeta2HatGap.p_dvd_hatQ_gap2
#print axioms Zeta2HatGap.hat_carry_gap1
#print axioms Zeta2HatGap.sq_dvd_hatQ_gap1
#print axioms Zeta2HatGap.hat_carry_gap5
#print axioms Zeta2HatGap.sq_dvd_hatQ_gap5
#print axioms Zeta2HatGap.gap2_inhabited
#print axioms Zeta2HatGap.forty_three_dvd_hatQ_ten
#print axioms Zeta2HatGap.phiSingle_ten_43
#print axioms Zeta2HatGap.gap1_contains_twelve_103
#print axioms Zeta2HatGap.sq_103_dvd_hatQ_twelve_via_gap1
