/-
# PT-QB clump 2d — the LAST TWO gap cells, `[6/13, 7/15)` and `[5/9, 9/16)`

Row PT-QB of `docs/future/zeta2-lean-chain.md` (registry `2B0.AW`).  `Zeta2HatGap` proved three
of the five gap cells and landed the three reusable residue pieces (`mul_mod_congr`,
`mod_eq_sub_mul`, `carry_iff_of_add`).  This module does the remaining two, both `v = 2`, and
with them **all five `φ̂`-only intervals are proved**.

**A separate module, on purpose**: kernel cost is GLOBAL to a `lean` call, and this corpus has
measured separate theorems beating folded slices 7.5×.  So the two cells go here rather than
being appended to `Zeta2HatGap`, which is already 469 lines.

## What the row's cell predicted, and what happened

The cell recorded, after cell 5 (the riskiest, taken third) needed nothing new, that "the shape
is now mechanical — `mul_mod_congr` + `mod_eq_sub_mul` for the lap residues, `carry_iff_of_add`
for the two complementary bits, a `u`-ordered branch chain, `omega` at every leaf".  **That
held**: neither cell here introduced a new piece, and both elaborated on the first attempt.

**The one thing that did not hold is the branch count, and the probe caught it rather than the
proof.**  Cell 4's first draft had FIVE branches: `u` leaves the `(bit2, bit3)` window at
`2p−3r`, and bit 3 comes back at `10r−5p`, so the draft split the tail again and sent the far
tail back to `(bit2, bit3)`.  `ptqb_gap2_probe.py` ARM D then reported that branch
**over-covered** — `(2,4)` and `(3,4)` close it too — and that is the signal that the split was
redundant, not that the pair was lucky: bit 2's and bit 4's wrapped laps are uniform on the
whole of `u > 8r−4p` (`3r−p+u < 3r < 2p` and `5r−2p+u < 5r−p < 2p`), so ONE branch closes the
tail.  Four branches, and ARM D is now clean on all four.  The lesson is the sibling of the one
`falsify_hatgap.sh` ARM L taught: **a passing arm asks whether the theorem is too weak; an
over-covering arm asks whether the proof is doing too much.**

## The branch chains, both forced by the `u`-order

`ptqb_gap2_probe.py` (archived `ptqb_gap2_probe.out`) validated the exact assignment below —
ARM A: 0 routing failures over 43 135 `(p, r, u)` with `p < 400`, ARM B: 0 failures of any lap
fact the proofs assert, ARM C: enumerated = scored, ARM D: every branch's pair swapped to each
of the other five leaves measured holes.  The carry-min over each box is exactly `2`, so the
`2 ≤` conclusions are tight and the sharpness arms bite; `ord_13 (hatQ 6)` and
`ord_43 (hatQ 24)` are 2 exactly, so the non-vacuity arms do too.

* **Cell 3, `[6/13, 7/15)`** — `6p ≤ 13r` and `15r < 7p`.  Laps `17r ∈ [7p, 8p)`,
  `11r ∈ [5p, 6p)`, `5r ∈ [2p, 3p)`, `3r ∈ [p, 2p)`.  Order `0 ≤ p−r < 2p−3r ≤ 10r−4p < p`,
  pairs `(2,3) (2,4) (1,4) (1,3)`.  The LEFT bound is load-bearing at the order itself
  (`2p−3r ≤ 10r−4p` IS `6p ≤ 13r`) and the RIGHT bound at branch 3's bit 4
  (`5r−2p+u < p` there IS `15r < 7p`).
* **Cell 4, `[5/9, 9/16)`** — `5p ≤ 9r` and `16r < 9p`.  Laps `17r ∈ [9p, 10p)`,
  `11r ∈ [6p, 7p)`, `5r ∈ [2p, 3p)`, `3r ∈ [p, 2p)`.  Order `0 ≤ 2p−3r < p−r ≤ 8r−4p < p`,
  pairs `(2,3) (1,3) (1,4) (2,4)`.  The LEFT bound is load-bearing twice — `p−r ≤ 8r−4p` IS
  `5p ≤ 9r`, and branches 3 and 4 need `u ≥ 6p−10r` which comes from it — and the RIGHT bound
  at branches 2–3's bit 1, where `2u ≤ 16r−8p < p` IS `16r < 9p` and is what keeps `(2u) % p`
  UNWRAPPED.  That is the opposite of every earlier cell, where bit 1 always wrapped.

## What this file does NOT claim

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  These are two of the five
gap cells.  The `φ̃ ≤ max(φ, φ̂)` dispatch over the refinement and `PhiT_dvd_qnInt` are not
here; `Zeta2HatAssemble` has them.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2HatGap

namespace Zeta2HatGap2

open Zeta2Defs Zeta2Hat Zeta2HatGap Nat

/-! ## Gap cell 3 of 5: `[6/13, 7/15)`, `φ = 1` and `φ̃ = 2`

Four branches.  `u` starts inside the `(bit2, bit3)` window, walks out of bit 3 at `p−r`, out of
bit 2 at `2p−3r`, and bit 4 covers the middle until `15r < 7p` pushes it over at `10r−4p`, from
where bit 3 is back — wrapped. -/

/-- **Gap cell 3: `[6/13, 7/15)`, `φ̃ = 2`.**  On `6p ≤ 13·(n%p)` and `15·(n%p) < 7p`, at least
TWO of the hat's four one-term carry bits fire, at every `j ≤ 8n`. -/
theorem hat_carry_gap3 (n p j : ℕ) [hp : Fact p.Prime] (hj : j ≤ 8 * n)
    (hlo : 6 * p ≤ 13 * (n % p)) (hhi : 15 * (n % p) < 7 * p) :
    2 ≤ (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0)
      + (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0)
      + (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0)
      + (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0) := by
  have hp0 : 0 < p := hp.out.pos
  have hr : n % p < p := Nat.mod_lt _ hp0
  have hu : j % p < p := Nat.mod_lt _ hp0
  have e17 : (17 * n) % p = 17 * (n % p) - 7 * p := by
    rw [mul_mod_congr 17 n p]
    exact mod_eq_sub_mul _ p 7 (by omega) (by omega)
  have e11 : (11 * n) % p = 11 * (n % p) - 5 * p := by
    rw [mul_mod_congr 11 n p]
    exact mod_eq_sub_mul _ p 5 (by omega) (by omega)
  have e5n : (5 * n) % p = 5 * (n % p) - 2 * p := by
    rw [mul_mod_congr 5 n p]
    exact mod_eq_sub_mul _ p 2 (by omega) (by omega)
  -- `simpa`, not `exact`: at `k = 1` the conclusion is `a - 1 * p`, which does not unify with
  -- `a - p`, and the `_` then stays a metavariable (measured in `Zeta2HatGap`, 2026-09-19).
  have e3n : (3 * n) % p = 3 * (n % p) - p := by
    rw [mul_mod_congr 3 n p]
    simpa using mod_eq_sub_mul (3 * (n % p)) p 1 (by omega) (by omega)
  have e2j : (2 * j) % p = (2 * (j % p)) % p := mul_mod_congr 2 j p
  have e3nj : (3 * n + j) % p = (3 * (n % p) - p + j % p) % p := by rw [Nat.add_mod, e3n]
  have e5nj : (5 * n + j) % p = (5 * (n % p) - 2 * p + j % p) % p := by rw [Nat.add_mod, e5n]
  have enj : (n + j) % p = (n % p + j % p) % p := Nat.add_mod n j p
  have b2iff := carry_iff_of_add p (3 * n + j) (8 * n - j) hp0
  have b3iff := carry_iff_of_add p (n + j) (10 * n - j) hp0
  rw [show 3 * n + j + (8 * n - j) = 11 * n from by omega] at b2iff
  rw [show n + j + (10 * n - j) = 11 * n from by omega] at b3iff
  -- The four branches, as a disjunction of PAIRS in the goal's own vocabulary.  Rewriting the
  -- goal instead loses to `simp`'s mod normal form, which un-rewrites `(r + u) % p` back to
  -- `(n + j) % p` — measured in `Zeta2HatGap.hat_carry_lowcell`.
  have key :
      ((p ≤ (3 * n + j) % p + (8 * n - j) % p) ∧ (p ≤ (n + j) % p + (10 * n - j) % p))
      ∨ ((p ≤ (3 * n + j) % p + (8 * n - j) % p) ∧ (p ≤ (5 * n) % p + (5 * n + j) % p))
      ∨ ((p ≤ (2 * j) % p + (17 * n) % p) ∧ (p ≤ (5 * n) % p + (5 * n + j) % p))
      ∨ ((p ≤ (2 * j) % p + (17 * n) % p) ∧ (p ≤ (n + j) % p + (10 * n - j) % p)) := by
    rw [b2iff, b3iff, e11, e3nj, enj, e2j, e17, e5n, e5nj]
    rcases lt_or_ge (j % p + n % p) p with h1 | h1
    · -- branch 1, `u < p − r`: bits 2 and 3, both unwrapped, both firing from `2r < p`
      refine Or.inl ⟨?_, ?_⟩
      · rw [Nat.mod_eq_of_lt (show 3 * (n % p) - p + j % p < p by omega)]; omega
      · rw [Nat.mod_eq_of_lt (show n % p + j % p < p by omega)]; omega
    · rcases lt_or_ge (j % p + 3 * (n % p)) (2 * p) with h2 | h2
      · -- branch 2, `p − r ≤ u < 2p − 3r`: bit 3 has wrapped out, bit 4 comes in — and bit 4
        -- needs `u ≥ 5p − 10r`, which `u ≥ p − r` gives because `4p ≤ 9r`
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [Nat.mod_eq_of_lt (show 3 * (n % p) - p + j % p < p by omega)]; omega
        · rw [Nat.mod_eq_of_lt (show 5 * (n % p) - 2 * p + j % p < p by omega)]; omega
      · rcases lt_or_ge (10 * (n % p)) (j % p + 4 * p) with h3 | h3
        · -- branch 4, `u > 10r − 4p`: bit 1 (its `2u` wrapped), bit 3 back and wrapped too
          refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
          · have hw : (2 * (j % p)) % p = 2 * (j % p) - p := by
              simpa using mod_eq_sub_mul (2 * (j % p)) p 1 (by omega) (by omega)
            rw [hw]; omega
          · have hw : (n % p + j % p) % p = n % p + j % p - p := by
              simpa using mod_eq_sub_mul (n % p + j % p) p 1 (by omega) (by omega)
            rw [hw]; omega
        · -- branch 3, `2p − 3r ≤ u ≤ 10r − 4p`: bit 2 is out, bit 1 comes in wrapped, and
          -- bit 4 is still UNWRAPPED — which is exactly the cell's right bound `15r < 7p`
          refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
          · have hw : (2 * (j % p)) % p = 2 * (j % p) - p := by
              simpa using mod_eq_sub_mul (2 * (j % p)) p 1 (by omega) (by omega)
            rw [hw]; omega
          · rw [Nat.mod_eq_of_lt (show 5 * (n % p) - 2 * p + j % p < p by omega)]; omega
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

/-- The cell folded: `p² ∣ hatQ n` wherever the residue lands on `[6/13, 7/15)`. -/
theorem sq_dvd_hatQ_gap3 (n p : ℕ) [Fact p.Prime]
    (hlo : 6 * p ≤ 13 * (n % p)) (hhi : 15 * (n % p) < 7 * p) :
    (p : ℤ) ^ 2 ∣ hatQ n :=
  Zeta2HatCarry.pow_dvd_hatQ_of_bits n p 2 (fun j hj => hat_carry_gap3 n p j hj hlo hhi)

/-! ## Gap cell 4 of 5: `[5/9, 9/16)`, `φ = 1` and `φ̃ = 2`

The novelty here is that **bit 1 is UNWRAPPED on its whole window** — `2u ≤ 16r−8p < p` IS the
cell's right bound `16r < 9p` — where on every earlier cell bit 1's `2u` wrapped.  A reader
carrying cell 3's habits gets branch 3 backwards: there bit 1 wraps and bit 4 does not, here
bit 4 wraps and bit 1 does not.  `falsify_hatgap2.sh` ARM W4 is that arm.

Four branches.  The header records why the first draft had five and why the fifth was
redundant; the tail's two laps are uniform, so one branch closes it. -/

/-- **Gap cell 4: `[5/9, 9/16)`, `φ̃ = 2`.**  On `5p ≤ 9·(n%p)` and `16·(n%p) < 9p`, at least
TWO of the hat's four one-term carry bits fire, at every `j ≤ 8n`. -/
theorem hat_carry_gap4 (n p j : ℕ) [hp : Fact p.Prime] (hj : j ≤ 8 * n)
    (hlo : 5 * p ≤ 9 * (n % p)) (hhi : 16 * (n % p) < 9 * p) :
    2 ≤ (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0)
      + (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0)
      + (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0)
      + (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0) := by
  have hp0 : 0 < p := hp.out.pos
  have hr : n % p < p := Nat.mod_lt _ hp0
  have hu : j % p < p := Nat.mod_lt _ hp0
  have e17 : (17 * n) % p = 17 * (n % p) - 9 * p := by
    rw [mul_mod_congr 17 n p]
    exact mod_eq_sub_mul _ p 9 (by omega) (by omega)
  have e11 : (11 * n) % p = 11 * (n % p) - 6 * p := by
    rw [mul_mod_congr 11 n p]
    exact mod_eq_sub_mul _ p 6 (by omega) (by omega)
  have e5n : (5 * n) % p = 5 * (n % p) - 2 * p := by
    rw [mul_mod_congr 5 n p]
    exact mod_eq_sub_mul _ p 2 (by omega) (by omega)
  have e3n : (3 * n) % p = 3 * (n % p) - p := by
    rw [mul_mod_congr 3 n p]
    simpa using mod_eq_sub_mul (3 * (n % p)) p 1 (by omega) (by omega)
  have e2j : (2 * j) % p = (2 * (j % p)) % p := mul_mod_congr 2 j p
  have e3nj : (3 * n + j) % p = (3 * (n % p) - p + j % p) % p := by rw [Nat.add_mod, e3n]
  have e5nj : (5 * n + j) % p = (5 * (n % p) - 2 * p + j % p) % p := by rw [Nat.add_mod, e5n]
  have enj : (n + j) % p = (n % p + j % p) % p := Nat.add_mod n j p
  have b2iff := carry_iff_of_add p (3 * n + j) (8 * n - j) hp0
  have b3iff := carry_iff_of_add p (n + j) (10 * n - j) hp0
  rw [show 3 * n + j + (8 * n - j) = 11 * n from by omega] at b2iff
  rw [show n + j + (10 * n - j) = 11 * n from by omega] at b3iff
  have key :
      ((p ≤ (3 * n + j) % p + (8 * n - j) % p) ∧ (p ≤ (n + j) % p + (10 * n - j) % p))
      ∨ ((p ≤ (2 * j) % p + (17 * n) % p) ∧ (p ≤ (n + j) % p + (10 * n - j) % p))
      ∨ ((p ≤ (2 * j) % p + (17 * n) % p) ∧ (p ≤ (5 * n) % p + (5 * n + j) % p))
      ∨ ((p ≤ (3 * n + j) % p + (8 * n - j) % p) ∧ (p ≤ (5 * n) % p + (5 * n + j) % p)) := by
    rw [b2iff, b3iff, e11, e3nj, enj, e2j, e17, e5n, e5nj]
    rcases lt_or_ge (j % p + 3 * (n % p)) (2 * p) with h1 | h1
    · -- branch 1, `u < 2p − 3r`: bits 2 and 3, both unwrapped
      refine Or.inl ⟨?_, ?_⟩
      · rw [Nat.mod_eq_of_lt (show 3 * (n % p) - p + j % p < p by omega)]; omega
      · rw [Nat.mod_eq_of_lt (show n % p + j % p < p by omega)]; omega
    · rcases lt_or_ge (j % p + n % p) p with h2 | h2
      · -- branch 2, `2p − 3r ≤ u < p − r`: bit 2 has wrapped out, bit 1 comes in and its `2u`
        -- is still below `p` (`2u < 2p − 2r ≤ p`, which is `p < 2r`)
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [Nat.mod_eq_of_lt (show 2 * (j % p) < p by omega)]; omega
        · rw [Nat.mod_eq_of_lt (show n % p + j % p < p by omega)]; omega
      · rcases lt_or_ge (8 * (n % p)) (j % p + 4 * p) with h3 | h3
        · -- branch 4, `u > 8r − 4p`, the WHOLE tail: bit 2 is back and bit 4 is on, both in
          -- their wrapped laps, and both laps are uniform to `u = p − 1` — `3r − p + u < 3r
          -- < 2p` and `5r − 2p + u < 5r − p < 2p` — which is why ONE branch closes the tail.
          refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
          · have hw : (3 * (n % p) - p + j % p) % p = 3 * (n % p) - p + j % p - p := by
              simpa using mod_eq_sub_mul (3 * (n % p) - p + j % p) p 1 (by omega) (by omega)
            rw [hw]; omega
          · have hw : (5 * (n % p) - 2 * p + j % p) % p = 5 * (n % p) - 2 * p + j % p - p := by
              simpa using mod_eq_sub_mul (5 * (n % p) - 2 * p + j % p) p 1 (by omega) (by omega)
            rw [hw]; omega
        · -- branch 3, `p − r ≤ u ≤ 8r − 4p`: bit 3 has wrapped out, bit 4 comes in wrapped,
          -- and bit 1's `2u` is UNWRAPPED precisely because `2u ≤ 16r − 8p < p`
          refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
          · rw [Nat.mod_eq_of_lt (show 2 * (j % p) < p by omega)]; omega
          · have hw : (5 * (n % p) - 2 * p + j % p) % p = 5 * (n % p) - 2 * p + j % p - p := by
              simpa using mod_eq_sub_mul (5 * (n % p) - 2 * p + j % p) p 1 (by omega) (by omega)
            rw [hw]; omega
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
  · have := hB1 ha; have := hB3 hb; omega
  · have := hB1 ha; have := hB4 hb; omega
  · have := hB2 ha; have := hB4 hb; omega

/-- The cell folded: `p² ∣ hatQ n` wherever the residue lands on `[5/9, 9/16)`. -/
theorem sq_dvd_hatQ_gap4 (n p : ℕ) [Fact p.Prime]
    (hlo : 5 * p ≤ 9 * (n % p)) (hhi : 16 * (n % p) < 9 * p) :
    (p : ℤ) ^ 2 ∣ hatQ n :=
  Zeta2HatCarry.pow_dvd_hatQ_of_bits n p 2 (fun j hj => hat_carry_gap4 n p j hj hlo hhi)

/-! ## Non-vacuity (LEAN.md §5): both cells are inhabited, and PT-QA is one short on each -/

/-- `(6, 13)`: `6/13` is the cell's own left endpoint, and `13² > 26·6 + 1 = 157`, so this is a
real cell of the window and not just an arithmetic instance. -/
theorem gap3_inhabited : 6 * 13 ≤ 13 * (6 % 13) ∧ 15 * (6 % 13) < 7 * 13 := by norm_num

theorem sq_thirteen_dvd_hatQ_six : (13 : ℤ) ^ 2 ∣ hatQ 6 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact sq_dvd_hatQ_gap3 6 13 (by norm_num) (by norm_num)

/-- **PT-QA is exactly one short here**: `φ(6/13) = 1` (table row 19, `[6/13, 7/15)`), while
`φ̃ = 2`.  So the tale-1 half gives `13 ∣ q₆` and the hat gives `13²`. -/
theorem phiSingle_six_13 : Zeta2Arith.phiSingle (6 / 13) = 1 := by
  norm_num [Zeta2Arith.phiSingle, Zeta2Arith.phiTable, List.find?]

/-- `(24, 43)`: `24/43 ≈ 0.5581 ∈ [5/9, 9/16) = [0.5556, 0.5625)`, and `43² > 26·24 + 1 = 625`.
This is the `(p, r)` `ptqb_cover_probe.out`'s ARM P decomposes for this cell. -/
theorem gap4_inhabited : 5 * 43 ≤ 9 * (24 % 43) ∧ 16 * (24 % 43) < 9 * 43 := by norm_num

theorem sq_fortythree_dvd_hatQ_twentyfour : (43 : ℤ) ^ 2 ∣ hatQ 24 := by
  have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  exact sq_dvd_hatQ_gap4 24 43 (by norm_num) (by norm_num)

/-- PT-QA is one short here too: `φ(24/43) = 1` (table row 23, `[5/9, 9/16)`). -/
theorem phiSingle_twentyfour_43 : Zeta2Arith.phiSingle (24 / 43) = 1 := by
  norm_num [Zeta2Arith.phiSingle, Zeta2Arith.phiTable, List.find?]

end Zeta2HatGap2

#print axioms Zeta2HatGap2.hat_carry_gap3
#print axioms Zeta2HatGap2.sq_dvd_hatQ_gap3
#print axioms Zeta2HatGap2.hat_carry_gap4
#print axioms Zeta2HatGap2.sq_dvd_hatQ_gap4
#print axioms Zeta2HatGap2.gap3_inhabited
#print axioms Zeta2HatGap2.sq_thirteen_dvd_hatQ_six
#print axioms Zeta2HatGap2.phiSingle_six_13
#print axioms Zeta2HatGap2.gap4_inhabited
#print axioms Zeta2HatGap2.sq_fortythree_dvd_hatQ_twentyfour
#print axioms Zeta2HatGap2.phiSingle_twentyfour_43
