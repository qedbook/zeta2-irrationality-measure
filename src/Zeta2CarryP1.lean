/-
# PT-Q1 — profile piece 1, symbolically: every window term carries at least once

Row PT-Q1 of `docs/future/zeta2-lean-chain.md` (registry `2B0.AU`).  For a prime in the
bracket `13n < p ≤ 15n`, above the Legendre line `p² > 26n+1`, the FIRST of the landed
atom's four carry bits fires at every `k` in the pole window, so `ord_p (cTerm n k) ≥ 1`.

The derivation is three lines by hand: `13n < p` makes `(13n) % p = 13n`; the window's
right edge `k ≤ 26n+1` makes `k − 13n − 1 ≤ 13n < p`, so `(k − 13n − 1) % p = k − 13n − 1`;
their sum is `k − 1 ≥ 15n ≥ p`.  The only risk the row carried was the `%`-rewriting idiom,
and it is real: `omega` treats `a % p` with a VARIABLE modulus `p` as an opaque atom
(measured, `out_carryp1_modidiom.txt` ARM A — it reports a counterexample in which `a % p` is
unconstrained).  `Nat.mod_eq_of_lt` first, `omega` after, is the remedy and it works.

## What this row does NOT give PT-QA, measured rather than assumed

PT-QA dispatches on `x = {n/p}` and its first case is `x ∈ [1/15, 1/13)`.  The bracket
`13n < p ≤ 15n` is STRICTLY STRONGER than that interval condition:

* forward it is sound — `fract_mem_piece1` below proves `13n < p ≤ 15n → {n/p} ∈ [1/15, 1/13)`;
* backwards it FAILS, and the failure is inside `PhiT`'s own product.  `piece1_scope_probe.out`
  enumerates every `(n, p)` that `PhiT` contains with `{n/p} ∈ [1/15, 1/13)` for `n ≤ 300`:
  **11558 cells, of which 97 (0.84%) have `p ≤ 13n`** — exactly the cells with `p < n`, the
  smallest being `(n, p) = (31, 29)` with `{31/29} = 2/29 ∈ [1/15, 1/13)`.
* and on those cells THIS ROW'S ROUTE genuinely does not reach: in all 40 sampled gap cells
  the first carry bit is `0` somewhere in the window (the four-bit SUM is never `0`, so the
  profile claim survives — by a different bit).  `piece1_offbracket_route_fails` ships that
  as a theorem at the smallest witness, so PT-QA cannot inherit the bracket by mistake.

So PT-QA's piece-1 case is `PT-Q1` **plus** an argument for `p < n`; PT-Q1 covers exactly the
sub-case `n < p`, which is where `Int.fract ((n:ℚ)/p) = (n:ℚ)/p`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2QnInt
import Zeta2Legendre
-- `Nat.Prime 29` in the non-vacuity witnesses is a `norm_num` extension, and it lives in its
-- own module: without this import `by norm_num` leaves `⊢ Nat.Prime 29` unsolved (measured).
import Mathlib.Tactic.NormNum.Prime

namespace Zeta2Arith

open Zeta2Defs Nat

/-! ## The carry bit -/

/-- **The first carry bit's argument, with both `% p` resolved.**  This is the whole content
of the row: `13n < p` and `k − 13n − 1 ≤ 13n < p` make both residues trivial, after which the
inequality is `p ≤ k − 1`, which the window's LEFT edge `k ≥ 15n + 1` gives from `p ≤ 15n`.

`omega` cannot do this on its own — with a variable modulus `a % p` is an opaque atom to it
(`out_carryp1_modidiom.txt` ARM A).  The two `Nat.mod_eq_of_lt` rewrites are load-bearing. -/
theorem carry_bit1_piece1 (n p k : ℕ) (hk : k ∈ candidateM.window n)
    (h1 : 13 * n < p) (h2 : p ≤ 15 * n) :
    p ≤ (13 * n) % p + (k - 13 * n - 1) % p := by
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (show k - 13 * n - 1 < p by omega)]
  omega

/-- **PT-Q1.**  Above the Legendre line, for `13n < p ≤ 15n`, every term of the window
carries at least once. -/
theorem carry_ge_piece1 (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 13 * n < p) (h2 : p ≤ 15 * n) (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  rw [padicValNat_cTerm p n k hk hp2]
  have hb := carry_bit1_piece1 n p k hk h1 h2
  -- the other three bits stay opaque: only the first is needed, and `omega` discharges the
  -- eight branches in which it is `false` from `hb`.
  split_ifs <;> omega

/-- The divisibility form, for a consumer folding over the window with `Nat` divisibility
rather than with `padicValNat`. -/
theorem dvd_cTerm_piece1 (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 13 * n < p) (h2 : p ≤ 15 * n) (hp2 : 26 * n + 1 < p ^ 2) :
    p ∣ cTerm n k := by
  by_contra hnd
  have h0 := padicValNat.eq_zero_of_not_dvd hnd
  have hge := carry_ge_piece1 n p k hk h1 h2 hp2
  omega

/-! ## The bridge to PT-QA's dispatcher, and the scope gap -/

/-- **Forward containment**: the bracket lands inside the profile's first interval.  This is
the object PT-QA dispatches on, so it is the statement that makes PT-Q1 usable there. -/
theorem fract_mem_piece1 (n p : ℕ) (h1 : 13 * n < p) (h2 : p ≤ 15 * n) :
    1 / 15 ≤ Int.fract ((n : ℚ) / p) ∧ Int.fract ((n : ℚ) / p) < 1 / 13 := by
  have hn : 1 ≤ n := by omega
  have hp : 0 < p := by omega
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hlt : (n : ℚ) / p < 1 := by
    rw [div_lt_one hpQ]; exact_mod_cast (by omega : n < p)
  have hge : (0 : ℚ) ≤ (n : ℚ) / p := by positivity
  rw [Int.fract_eq_self.2 ⟨hge, hlt⟩]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hpQ]
    have : (p : ℚ) ≤ 15 * n := by exact_mod_cast h2
    linarith
  · rw [div_lt_iff₀ hpQ]
    have : (13 : ℚ) * n < p := by exact_mod_cast h1
    linarith

/-- **Reverse containment FAILS, and the witness is inside `PhiT`'s own product.**  At
`n = 31`, `p = 29`: `{n/p} = 2/29` is in piece 1's interval, `p ≤ 15n`, and `p² > 26n+1` —
so `PhiT 31` contains this prime at profile value ≥ 1 — yet `13n < p` is FALSE.

Measured population (`piece1_scope_probe.out`, `n ≤ 300`): 97 such cells out of 11558. -/
theorem piece1_bracket_lt_interval :
    Int.fract ((31 : ℚ) / 29) = 2 / 29
      ∧ (1 : ℚ) / 15 ≤ 2 / 29 ∧ (2 : ℚ) / 29 < 1 / 13
      ∧ 29 ≤ 15 * 31 ∧ 26 * 31 + 1 < 29 ^ 2 ∧ ¬ (13 * 31 < 29) := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [Int.fract]
  norm_num

/-- **And on that cell PT-Q1's ROUTE provably does not reach.**  `k = 491` is in the window
of `n = 31` and the first carry bit is `0` there, so a PT-QA piece stated on `{n/p}` alone
cannot be discharged by `carry_bit1_piece1`.  (The four-bit SUM is still ≥ 1 there — the
profile claim survives by a different bit; see `piece1_scope_probe.out` ARM C.) -/
theorem piece1_offbracket_route_fails :
    491 ∈ candidateM.window 31
      ∧ ¬ (29 ≤ (13 * 31) % 29 + (491 - 13 * 31 - 1) % 29) := by
  refine ⟨(mem_window_iff 31 491).2 ⟨by norm_num, by norm_num⟩, by decide⟩

/-! ## Non-vacuity (LEAN.md §5) — the hypotheses are satisfiable, and at a real cell -/

/-- The smallest cell satisfying every hypothesis of `carry_ge_piece1`: `n = 2`, `p = 29`,
`k = 31`.  Stated so that a later edit that made the hypotheses contradictory would red. -/
theorem piece1_hypotheses_satisfiable :
    Nat.Prime 29 ∧ 13 * 2 < 29 ∧ 29 ≤ 15 * 2 ∧ 26 * 2 + 1 < 29 ^ 2
      ∧ 31 ∈ candidateM.window 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  exact (mem_window_iff 2 31).2 ⟨by norm_num, by norm_num⟩

/-- The theorem APPLIED at that cell — the conclusion is not vacuous, and `cTerm 2 31 ≠ 0`. -/
theorem piece1_witness : 1 ≤ padicValNat 29 (cTerm 2 31) := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact carry_ge_piece1 2 29 31 ((mem_window_iff 2 31).2 ⟨by norm_num, by norm_num⟩)
    (by norm_num) (by norm_num) (by norm_num)

/-- `n = 0` is EXCLUDED by the hypotheses, not handled by them: `13·0 < p ≤ 15·0` is
unsatisfiable.  The edge case compiles (LEAN.md §5) because the row never meets it. -/
theorem piece1_excludes_zero (p : ℕ) : ¬ (13 * 0 < p ∧ p ≤ 15 * 0) := by omega

end Zeta2Arith

#print axioms Zeta2Arith.carry_bit1_piece1
#print axioms Zeta2Arith.carry_ge_piece1
#print axioms Zeta2Arith.dvd_cTerm_piece1
#print axioms Zeta2Arith.fract_mem_piece1
#print axioms Zeta2Arith.piece1_bracket_lt_interval
#print axioms Zeta2Arith.piece1_offbracket_route_fails
#print axioms Zeta2Arith.piece1_hypotheses_satisfiable
#print axioms Zeta2Arith.piece1_witness
#print axioms Zeta2Arith.piece1_excludes_zero
