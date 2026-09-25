/-
# PT-QB clump 4 — the DISPATCH and `PhiT_dvd_qnInt`: the row's acceptance

Row PT-QB of `docs/future/zeta2-lean-chain.md` (registry `2B0.AW`).  The five gap cells are
proved (`Zeta2HatGap`, `Zeta2HatGap2`) and PT-QA's 41-row profile is proved
(`Zeta2Arith.pow_phiSingle_dvd_qnInt`).  What was missing is the PROFILE ALGEBRA that combines
them, and the row's deliverable on top of it:

    theorem PhiT_dvd_qnInt (n : ℕ) : ((PhiT n : ℕ) : ℤ) ∣ qnInt n

and `hQ` at `ΔT`, which is what the chain's binder actually consumes.

## The refinement is 42 cells, not 52 — and the difference is not a correction

The row's cell priced "the `φ̃ ≤ max(φ, φ̂)` dispatch over the 52-cell refinement".  52 is the
common refinement of the two tables over the WHOLE line; the dispatch only ever runs inside a
`candidateProfile` row, because `phiT` is `0` off the table and `p ^ 0 ∣ qₙ` needs nothing.
Restricted to the 26 rows the refinement has **42 cells** — `ptqb_refine_probe.py`, derived
from the two landed Lean tables and from no third copy — of which **37 are carried by PT-QA**
(`φ ≥ φ̃` there) and **5 by the hat**, and those five are exactly the five gap intervals the
carry lemmas prove.  No row has more than four subcells.  So the dispatch is 26 cases with 42
leaves, and every leaf is one `exact`.

## The three pieces it rests on, and where each came from

* **`Zeta2HatDispatch.phiSingle_of_mem`** — membership in ANY of PT-QA's 41 rows gives the
  value of `φ`.  Landed as clump 3 precisely for this; PT-QA proved the disjointness and drew
  no consequence from it.
* **`phiT_spec`** — the same `find?` fact for the SECOND profile, proved here.  It is the
  weaker direction (`phiT x` is `0` or SOME containing row's value) and needs no `Pairwise`,
  which `candidateProfile` still does not have: the dispatch goes FROM `phiT`'s own value and
  never has to come back to it, so clump 3's note that `candidateProfile`'s `Pairwise` is the
  last unmeasured piece of the uniqueness layer turns out not to bind here.
* **`Zeta2HatQnInt.pow_dvd_qnInt_of_hat_bits`** — PAIR, executed, carrying a hat carry-bit
  statement to the chain's own `qₙ`.

## Why the product step needs coprimality and not just a fold

`Φ̃ₙ = ∏_{p ∈ window} p ^ φ̃({n/p})` is a product over DISTINCT primes, and `a ∣ m` and `b ∣ m`
give `a·b ∣ m` only when `a` and `b` are coprime.  `Finset.prod_dvd_of_coprime` is that step;
the pairwise hypothesis is `Nat.coprime_primes` transported to `ℤ` and raised to the exponents.

## What this file does NOT claim

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  `hQ` is ONE of the chain's
binders; `hP` (PT-P), `hdecay`, `hgrowth` and the rest are elsewhere and mostly open.  Nothing
here says `Φ̃` is the BEST clearing, only that it divides.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2HatGap2
import Zeta2HatQnInt
import Zeta2HatDispatch

namespace Zeta2HatAssemble

-- `qnInt` lives in `Zeta2Arith`, not `Zeta2Defs`: without it on this line `autoImplicit`
-- silently binds `qnInt` as a variable and every theorem below elaborates to `sorryAx` while
-- `#print axioms` still prints (LEAN.md §1 — measured in `Zeta2HatQnInt`, 2026-09-19).
open Zeta2Defs Zeta2Arith Zeta2Hat Zeta2PhiT

/-! ## `phiT`'s own `find?` spec -/

/-- The dispatch is total on the candidate profile: `φ̃ x` is `0`, or the value of a
`candidateProfile` row containing `x`.  The twin of `Zeta2Arith.phiSingle_spec`, and the weaker
of the two directions — it goes FROM `find?` to a row, so it needs no disjointness.

Stated with the row's three components SEPARATE rather than as a `t ∈ …` pair.  That is not
cosmetic: with `⟨t, …⟩` the 26 substituted hypotheses read `(1/11, 2/17, 2).1 ≤ x`, projections
`linarith` has to `whnf` at every one of the 42 leaves, and the last leaf died of the
declaration's shared heartbeat budget (measured here 2026-09-19, `whnf` timeout at row 26).
Separate binders substitute to `1/11 ≤ x` and the projections never appear. -/
theorem phiT_spec (x : ℚ) :
    phiT x = 0 ∨ ∃ a b v : ℚ, (a, b, v) ∈ Zeta2Profile.candidateProfile ∧
      a ≤ x ∧ x < b ∧ phiT x = v.num.toNat := by
  unfold phiT
  split
  · rename_i t h
    right
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    exact ⟨t.1, t.2.1, t.2.2, List.mem_of_find?_eq_some h, hp.1, hp.2, rfl⟩
  · left; rfl

/-- The exponent `phiT` produces is a `ℚ.num.toNat`; every leaf below proves its divisibility
at a `ℕ` literal and this carries it across.  `hq` comes SECOND so that `v` is already fixed by
`h` when the conversion is elaborated. -/
theorem dvd_of_val {n p : ℕ} {q : ℚ} {v : ℕ}
    (h : (p : ℤ) ^ v ∣ qnInt n) (hq : q.num.toNat = v) : (p : ℤ) ^ q.num.toNat ∣ qnInt n := by
  rw [hq]; exact h

/-- `norm_num` reduces `(2 : ℚ).num` to `(2 : ℤ)` and then STOPS, leaving `Int.toNat 2 = 2`
unsolved — measured here 2026-09-19, on all thirteen `φ̃ = 2` rows at once while every `φ̃ = 1`
row passed.  So the conversion is pinned as two lemmas rather than re-derived 42 times. -/
theorem num_toNat_one : ((1 : ℚ)).num.toNat = 1 := by decide +kernel

theorem num_toNat_two : ((2 : ℚ)).num.toNat = 2 := by decide +kernel

/-! ## Route A — the 37 cells PT-QA carries -/

/-- On a subcell where PT-QA's profile is at least `φ̃`, the tale-1 half already gives the
power.  `phiSingle_of_mem` is what turns membership in the subcell's phiTable row into the
VALUE of `φ` there. -/
theorem viaQA (n p : ℕ) [Fact p.Prime] (hp2 : 26 * n + 1 < p ^ 2) {c d : ℚ} {vs v : ℕ}
    (ht : (c, d, vs) ∈ phiTable)
    (hlo : c ≤ Int.fract ((n : ℚ) / p)) (hhi : Int.fract ((n : ℚ) / p) < d)
    (hv : v ≤ vs) : (p : ℤ) ^ v ∣ qnInt n := by
  have hs : phiSingle (Int.fract ((n : ℚ) / p)) = vs :=
    Zeta2HatDispatch.phiSingle_of_mem ht hlo hhi
  have h := pow_phiSingle_dvd_qnInt n p hp2
  rw [hs] at h
  exact dvd_trans (pow_dvd_pow _ hv) h

/-! ## Route B — the five cells only the hat carries

Each is its gap lemma composed with PAIR.  `Zeta2Arith.bounds_of_fract` is the bridge from the
`Int.fract` bounds the dispatch has to the `(n % p, p)` inequalities the carry lemmas take; no
gap lemma needs the Legendre line, because a units-digit carry bit is a lower bound on
`ord_p` at EVERY prime (`Zeta2HatCarry.carry_bit_le_padicValNat_choose`). -/

theorem viaGap1 (n p : ℕ) [Fact p.Prime]
    (hlo : (1 : ℚ) / 9 ≤ Int.fract ((n : ℚ) / p)) (hhi : Int.fract ((n : ℚ) / p) < 2 / 17) :
    (p : ℤ) ^ 2 ∣ qnInt n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h1, h2⟩ := bounds_of_fract n p 1 9 2 17 hp (by norm_num) (by norm_num)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  exact Zeta2HatQnInt.pow_dvd_qnInt_of_hat_bits n p 2
    (fun j hj => Zeta2HatGap.hat_carry_gap1 n p j hj (by omega) (by omega))

theorem viaGap2 (n p : ℕ) [Fact p.Prime]
    (hlo : (3 : ℚ) / 13 ≤ Int.fract ((n : ℚ) / p)) (hhi : Int.fract ((n : ℚ) / p) < 4 / 17) :
    (p : ℤ) ^ 1 ∣ qnInt n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h1, h2⟩ := bounds_of_fract n p 3 13 4 17 hp (by norm_num) (by norm_num)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  exact Zeta2HatQnInt.pow_dvd_qnInt_of_hat_bits n p 1
    (fun j hj => Zeta2HatGap.hat_carry_gap2 n p j hj (by omega) (by omega))

theorem viaGap3 (n p : ℕ) [Fact p.Prime]
    (hlo : (6 : ℚ) / 13 ≤ Int.fract ((n : ℚ) / p)) (hhi : Int.fract ((n : ℚ) / p) < 7 / 15) :
    (p : ℤ) ^ 2 ∣ qnInt n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h1, h2⟩ := bounds_of_fract n p 6 13 7 15 hp (by norm_num) (by norm_num)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  exact Zeta2HatQnInt.pow_dvd_qnInt_of_hat_bits n p 2
    (fun j hj => Zeta2HatGap2.hat_carry_gap3 n p j hj (by omega) (by omega))

theorem viaGap4 (n p : ℕ) [Fact p.Prime]
    (hlo : (5 : ℚ) / 9 ≤ Int.fract ((n : ℚ) / p)) (hhi : Int.fract ((n : ℚ) / p) < 9 / 16) :
    (p : ℤ) ^ 2 ∣ qnInt n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h1, h2⟩ := bounds_of_fract n p 5 9 9 16 hp (by norm_num) (by norm_num)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  exact Zeta2HatQnInt.pow_dvd_qnInt_of_hat_bits n p 2
    (fun j hj => Zeta2HatGap2.hat_carry_gap4 n p j hj (by omega) (by omega))

theorem viaGap5 (n p : ℕ) [Fact p.Prime]
    (hlo : (12 : ℚ) / 13 ≤ Int.fract ((n : ℚ) / p)) (hhi : Int.fract ((n : ℚ) / p) < 14 / 15) :
    (p : ℤ) ^ 2 ∣ qnInt n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h1, h2⟩ := bounds_of_fract n p 12 13 14 15 hp (by norm_num) (by norm_num)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  exact Zeta2HatQnInt.pow_dvd_qnInt_of_hat_bits n p 2
    (fun j hj => Zeta2HatGap.hat_carry_gap5 n p j hj (by omega) (by omega))

/-! ## The dispatch, executed: 26 rows, 42 leaves

Rows and subcells are `ptqb_refine_probe.out`'s, in the table's own order.  A row whose
interval or value drifts from the piece lemma it is dispatched to is a red case HERE, exactly
as in `Zeta2Arith.carry_ge_of_mem_table`. -/

-- The 42 leaves share ONE heartbeat budget, and at the default 200 000 the LAST leaf is the
-- one that dies — the same "cost is global to the call" the row met at the kernel level.  The
-- doc comment goes INSIDE the `set_option … in`, or the parser rejects it.
set_option maxHeartbeats 1000000 in
/-- **The per-prime half of the row's deliverable**: `p ^ φ̃({n/p}) ∣ qₙ` at every prime above
the Legendre line.  Unconditional in `n`; the `hp2` is PT-DEF's `26n + 1 < p²`, which the hat
route does not use and the PT-QA route does. -/
theorem pow_phiT_dvd_qnInt (n p : ℕ) [Fact p.Prime] (hp2 : 26 * n + 1 < p ^ 2) :
    (p : ℤ) ^ phiT (Int.fract ((n : ℚ) / p)) ∣ qnInt n := by
  rcases phiT_spec (Int.fract ((n : ℚ) / p)) with h0 | ⟨a, b, v, ht, hlo, hhi, hv⟩
  · rw [h0]; simp
  rw [hv]
  simp only [Zeta2Profile.candidateProfile, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at ht
  rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- row 1 of 26: [1/15, 1/13), φ̃ = 1 — 1 subcell(s): QA[1/15,1/13)
    exact dvd_of_val (viaQA n p hp2 (c := 1/15) (d := 1/13) (vs := 1) (v := 1)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_one
  · -- row 2 of 26: [1/11, 2/17), φ̃ = 2 — 2 subcell(s): QA[1/11,1/9) GAP[1/9,2/17)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((1/9 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 1/11) (d := 1/9) (vs := 2) (v := 2)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_two
    · exact dvd_of_val (viaGap1 n p (by linarith) (by linarith)) num_toNat_two
  · -- row 3 of 26: [2/17, 1/7), φ̃ = 1 — 1 subcell(s): QA[2/17,1/7)
    exact dvd_of_val (viaQA n p hp2 (c := 2/17) (d := 1/7) (vs := 1) (v := 1)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_one
  · -- row 4 of 26: [1/7, 2/13), φ̃ = 2 — 1 subcell(s): QA[1/7,2/13)
    exact dvd_of_val (viaQA n p hp2 (c := 1/7) (d := 2/13) (vs := 2) (v := 2)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_two
  · -- row 5 of 26: [2/13, 2/11), φ̃ = 1 — 2 subcell(s): QA[2/13,1/6) QA[1/6,2/11)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((1/6 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 2/13) (d := 1/6) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
    · exact dvd_of_val (viaQA n p hp2 (c := 1/6) (d := 2/11) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
  · -- row 6 of 26: [2/11, 1/5), φ̃ = 2 — 1 subcell(s): QA[2/11,1/5)
    exact dvd_of_val (viaQA n p hp2 (c := 2/11) (d := 1/5) (vs := 2) (v := 2)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_two
  · -- row 7 of 26: [1/5, 4/17), φ̃ = 1 — 3 subcell(s): QA[1/5,2/9) QA[2/9,3/13) GAP[3/13,4/17)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((2/9 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 1/5) (d := 2/9) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
    · rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((3/13 : ℚ)) with h1 | h1
      · exact dvd_of_val (viaQA n p hp2 (c := 2/9) (d := 3/13) (vs := 1) (v := 1)
          (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
          (by norm_num)) num_toNat_one
      · exact dvd_of_val (viaGap2 n p (by linarith) (by linarith)) num_toNat_one
  · -- row 8 of 26: [3/11, 4/13), φ̃ = 2 — 1 subcell(s): QA[3/11,4/13)
    exact dvd_of_val (viaQA n p hp2 (c := 3/11) (d := 4/13) (vs := 2) (v := 2)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_two
  · -- row 9 of 26: [4/13, 4/11), φ̃ = 1 — 2 subcell(s): QA[4/13,1/3) QA[1/3,4/11)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((1/3 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 4/13) (d := 1/3) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
    · exact dvd_of_val (viaQA n p hp2 (c := 1/3) (d := 4/11) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
  · -- row 10 of 26: [4/11, 5/13), φ̃ = 2 — 1 subcell(s): QA[4/11,5/13)
    exact dvd_of_val (viaQA n p hp2 (c := 4/11) (d := 5/13) (vs := 2) (v := 2)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_two
  · -- row 11 of 26: [5/13, 2/5), φ̃ = 1 — 1 subcell(s): QA[5/13,2/5)
    exact dvd_of_val (viaQA n p hp2 (c := 5/13) (d := 2/5) (vs := 1) (v := 1)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_one
  · -- row 12 of 26: [3/7, 5/11), φ̃ = 1 — 2 subcell(s): QA[3/7,4/9) QA[4/9,5/11)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((4/9 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 3/7) (d := 4/9) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
    · exact dvd_of_val (viaQA n p hp2 (c := 4/9) (d := 5/11) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
  · -- row 13 of 26: [5/11, 7/15), φ̃ = 2 — 2 subcell(s): QA[5/11,6/13) GAP[6/13,7/15)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((6/13 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 5/11) (d := 6/13) (vs := 2) (v := 2)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_two
    · exact dvd_of_val (viaGap3 n p (by linarith) (by linarith)) num_toNat_two
  · -- row 14 of 26: [7/15, 8/17), φ̃ = 1 — 1 subcell(s): QA[7/15,8/17)
    exact dvd_of_val (viaQA n p hp2 (c := 7/15) (d := 8/17) (vs := 1) (v := 1)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_one
  · -- row 15 of 26: [8/15, 7/13), φ̃ = 1 — 1 subcell(s): QA[8/15,7/13)
    exact dvd_of_val (viaQA n p hp2 (c := 8/15) (d := 7/13) (vs := 1) (v := 1)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_one
  · -- row 16 of 26: [6/11, 9/16), φ̃ = 2 — 2 subcell(s): QA[6/11,5/9) GAP[5/9,9/16)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((5/9 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 6/11) (d := 5/9) (vs := 2) (v := 2)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_two
    · exact dvd_of_val (viaGap4 n p (by linarith) (by linarith)) num_toNat_two
  · -- row 17 of 26: [9/16, 8/13), φ̃ = 1 — 2 subcell(s): QA[9/16,3/5) QA[3/5,8/13)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((3/5 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 9/16) (d := 3/5) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
    · exact dvd_of_val (viaQA n p hp2 (c := 3/5) (d := 8/13) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
  · -- row 18 of 26: [7/11, 11/17), φ̃ = 2 — 1 subcell(s): QA[7/11,11/17)
    exact dvd_of_val (viaQA n p hp2 (c := 7/11) (d := 11/17) (vs := 2) (v := 2)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_two
  · -- row 19 of 26: [11/17, 9/13), φ̃ = 1 — 2 subcell(s): QA[11/17,2/3) QA[2/3,9/13)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((2/3 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 11/17) (d := 2/3) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
    · exact dvd_of_val (viaQA n p hp2 (c := 2/3) (d := 9/13) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
  · -- row 20 of 26: [5/7, 8/11), φ̃ = 1 — 1 subcell(s): QA[5/7,8/11)
    exact dvd_of_val (viaQA n p hp2 (c := 5/7) (d := 8/11) (vs := 1) (v := 1)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_one
  · -- row 21 of 26: [8/11, 10/13), φ̃ = 2 — 2 subcell(s): QA[8/11,3/4) QA[3/4,10/13)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((3/4 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 8/11) (d := 3/4) (vs := 2) (v := 2)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_two
    · exact dvd_of_val (viaQA n p hp2 (c := 3/4) (d := 10/13) (vs := 2) (v := 2)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_two
  · -- row 22 of 26: [10/13, 4/5), φ̃ = 1 — 2 subcell(s): QA[10/13,7/9) QA[7/9,4/5)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((7/9 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 10/13) (d := 7/9) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
    · exact dvd_of_val (viaQA n p hp2 (c := 7/9) (d := 4/5) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
  · -- row 23 of 26: [9/11, 14/17), φ̃ = 2 — 1 subcell(s): QA[9/11,14/17)
    exact dvd_of_val (viaQA n p hp2 (c := 9/11) (d := 14/17) (vs := 2) (v := 2)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_two
  · -- row 24 of 26: [14/17, 10/11), φ̃ = 1 — 4 subcell(s): QA[14/17,5/6) QA[5/6,11/13) QA[11/13,8/9) QA[8/9,10/11)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((5/6 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 14/17) (d := 5/6) (vs := 1) (v := 1)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_one
    · rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((11/13 : ℚ)) with h1 | h1
      · exact dvd_of_val (viaQA n p hp2 (c := 5/6) (d := 11/13) (vs := 1) (v := 1)
          (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
          (by norm_num)) num_toNat_one
      · rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((8/9 : ℚ)) with h2 | h2
        · exact dvd_of_val (viaQA n p hp2 (c := 11/13) (d := 8/9) (vs := 1) (v := 1)
            (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
            (by norm_num)) num_toNat_one
        · exact dvd_of_val (viaQA n p hp2 (c := 8/9) (d := 10/11) (vs := 1) (v := 1)
            (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
            (by norm_num)) num_toNat_one
  · -- row 25 of 26: [10/11, 14/15), φ̃ = 2 — 2 subcell(s): QA[10/11,12/13) GAP[12/13,14/15)
    rcases lt_or_ge (Int.fract ((n : ℚ) / p)) ((12/13 : ℚ)) with h0 | h0
    · exact dvd_of_val (viaQA n p hp2 (c := 10/11) (d := 12/13) (vs := 2) (v := 2)
        (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
        (by norm_num)) num_toNat_two
    · exact dvd_of_val (viaGap5 n p (by linarith) (by linarith)) num_toNat_two
  · -- row 26 of 26: [14/15, 16/17), φ̃ = 1 — 1 subcell(s): QA[14/15,16/17)
    exact dvd_of_val (viaQA n p hp2 (c := 14/15) (d := 16/17) (vs := 1) (v := 1)
      (by norm_num [Zeta2Arith.phiTable]) (by linarith) (by linarith)
      (by norm_num)) num_toNat_one

/-! ## The product over the window -/

/-- **THE ROW'S DELIVERABLE: `Φ̃ₙ ∣ qₙ`.**  `Δ`-free, as cas-b1's measurement asked for.

The fold is `Finset.prod_dvd_of_coprime` and not a plain induction: `a ∣ m` and `b ∣ m` give
`a·b ∣ m` only for coprime `a, b`, and here that is `Nat.coprime_primes` transported to `ℤ`
and raised to the two exponents.  Vacuity-free by construction — this is a divisibility, so it
says something at every `n` whatever `qₙ` is. -/
theorem PhiT_dvd_qnInt (n : ℕ) : ((PhiT n : ℕ) : ℤ) ∣ qnInt n := by
  unfold PhiT
  push_cast
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro x hx y hy hxy
    have hxp : x.Prime := prime_of_mem_phiWindow (Finset.mem_coe.mp hx)
    have hyp : y.Prime := prime_of_mem_phiWindow (Finset.mem_coe.mp hy)
    exact IsCoprime.pow (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hxp hyp).mpr hxy))
  · intro q hq
    have : Fact q.Prime := ⟨prime_of_mem_phiWindow hq⟩
    exact pow_phiT_dvd_qnInt n q (sq_gt_of_mem_phiWindow hq)

/-- The `padicValInt` spelling, which `qnInt_ne_zero` makes safe.  The row's cell records that
the two forms agree rather than one being the honest one; this is the one that is not. -/
theorem padicValInt_qnInt_ge_phiT (n p : ℕ) [Fact p.Prime] (hp2 : 26 * n + 1 < p ^ 2) :
    phiT (Int.fract ((n : ℚ) / p)) ≤ padicValInt p (qnInt n) :=
  ((padicValInt_dvd_iff _ (qnInt n)).1 (pow_phiT_dvd_qnInt n p hp2)).resolve_left
    (Zeta2HatQnInt.qnInt_ne_zero n)

/-! ## `hQ` at `Δ̃`, which is what the chain's binder consumes -/

/-- `Q n = Δ(16n)·D(15n)·qₙ / Φ̃ₙ`, an EXACT `ℤ`-division: `PhiT_dvd_qnInt` is what makes it
exact, and without it this definition would silently truncate. -/
def QT (n : ℕ) : ℤ := ((Zeta2Arith.Δ 16 15 n : ℕ) : ℤ) * qnInt n / ((PhiT n : ℕ) : ℤ)

/-- The division is exact. -/
theorem PhiT_mul_QT (n : ℕ) :
    ((PhiT n : ℕ) : ℤ) * QT n = ((Zeta2Arith.Δ 16 15 n : ℕ) : ℤ) * qnInt n := by
  obtain ⟨c, hc⟩ : ((PhiT n : ℕ) : ℤ) ∣ ((Zeta2Arith.Δ 16 15 n : ℕ) : ℤ) * qnInt n :=
    Dvd.dvd.mul_left (PhiT_dvd_qnInt n) _
  have hne : ((PhiT n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast PhiT_ne_zero n
  have : QT n = c := by unfold QT; rw [hc]; exact Int.mul_ediv_cancel_left c hne
  rw [this, hc]

/-- **The chain's `hQ`, at `Δ := Δ̃` and at the candidate's own `qₙ`.**  `hQ_of_qn_int` is
`Δ`-generic and takes an INTEGER sequence; `Φ̃` is what makes `Δ̃ₙ · qₙ` one, which is the whole
content of row PT-QB.  This is the application (LEAN.md §3: the acceptance is the executed
composition, not a proof "with the others as hypotheses"). -/
theorem hQ_at_ΔT : ∀ n, ((QT n : ℤ) : ℝ) = ΔT n * ((candidateM.qn n : ℚ) : ℝ) := by
  intro n
  have hR : ((PhiT n : ℕ) : ℝ) ≠ 0 := PhiT_cast_ne_zero n
  have hq : ((candidateM.qn n : ℚ) : ℝ) = ((qnInt n : ℤ) : ℝ) := by
    rw [← Zeta2Arith.qnInt_cast n]; push_cast; ring
  have hmul : ((PhiT n : ℕ) : ℝ) * ((QT n : ℤ) : ℝ)
      = ((Zeta2Arith.Δ 16 15 n : ℕ) : ℝ) * ((qnInt n : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (PhiT_mul_QT n)
  rw [hq]
  unfold ΔT
  field_simp
  linarith [hmul]

/-! ## Non-vacuity and edges (LEAN.md §5) -/

/-- `Φ̃₁ = 5929 = 7²·11²`, the landed `Zeta2PhiT.PhiT_one`, so the deliverable at `n = 1` is a
FOUR-prime-power statement and not a vacuous `1 ∣ _`.  PT-QA's own `7² ∣ q₁` is the 7-part of
it; the 11-part is new here. -/
theorem PhiT_one_dvd_qnInt : (5929 : ℤ) ∣ qnInt 1 := by
  have h := PhiT_dvd_qnInt 1
  rw [PhiT_one] at h
  exact_mod_cast h

/-- The window is not empty at `n = 12` — 34 primes (`Zeta2PhiT.phiWindow_twelve_card`) — so
the product at the row's named index really is a product. -/
theorem twelve_window_nonempty : (phiWindow 12).Nonempty := by
  rw [← Finset.card_pos, phiWindow_twelve_card]
  norm_num

/-- `103 ∈` the window at `n = 12`, and `φ̃(12/103) = 2`, so `103²` is one of `Φ̃₁₂`'s factors —
the row's named cell, now reached through the product rather than beside it. -/
theorem sq_103_dvd_qnInt_twelve_via_dispatch : (103 : ℤ) ^ 2 ∣ qnInt 12 := by
  have : Fact (Nat.Prime 103) := ⟨by norm_num⟩
  have h := pow_phiT_dvd_qnInt 12 103 (by norm_num)
  rwa [show Int.fract (((12 : ℕ) : ℚ) / ((103 : ℕ) : ℚ)) = 12 / 103 from
    Zeta2HatQnInt.fract_twelve_103, Zeta2HatQnInt.phiT_twelve_103] at h

end Zeta2HatAssemble

#print axioms Zeta2HatAssemble.phiT_spec
#print axioms Zeta2HatAssemble.dvd_of_val
#print axioms Zeta2HatAssemble.num_toNat_one
#print axioms Zeta2HatAssemble.num_toNat_two
#print axioms Zeta2HatAssemble.viaQA
#print axioms Zeta2HatAssemble.viaGap1
#print axioms Zeta2HatAssemble.viaGap2
#print axioms Zeta2HatAssemble.viaGap3
#print axioms Zeta2HatAssemble.viaGap4
#print axioms Zeta2HatAssemble.viaGap5
#print axioms Zeta2HatAssemble.pow_phiT_dvd_qnInt
#print axioms Zeta2HatAssemble.PhiT_dvd_qnInt
#print axioms Zeta2HatAssemble.padicValInt_qnInt_ge_phiT
#print axioms Zeta2HatAssemble.PhiT_mul_QT
#print axioms Zeta2HatAssemble.hQ_at_ΔT
#print axioms Zeta2HatAssemble.PhiT_one_dvd_qnInt
#print axioms Zeta2HatAssemble.twelve_window_nonempty
#print axioms Zeta2HatAssemble.sq_103_dvd_qnInt_twelve_via_dispatch
