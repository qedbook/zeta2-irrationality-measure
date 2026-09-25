/-
# Row PT-P, layer 4 — the cells with NO SHORT TERM, and why the open congruence never sees them

`ptp_dropped_probe.py` re-priced PT-P's dropped-index selection at **12 strata** over the five
run-carrying profile pieces, measured "the dropped index is constant on a stratum" — and flagged,
in its own cell, that the green covered only 5 of the 12:

    "every cell of the box lands in ONE stratum per piece, so 'constant on the piece' has never
     been tested on the other seven strata"

`ptp_stratum_probe.py` / `.out` scores all twelve and the answer is a DICHOTOMY, not a bigger
census: the seven unscored strata carry **no short term at all** — 5251 `(r, p)` pairs enumerated
at `p ≤ 300`, 3722 of them in those seven, ZERO with a short run, and the same verdict certified
symbolically for every `p` at once (the four no-carry sets are cyclic arcs whose endpoints are
exact rationals in `x = r/p` once the stratum fixes the six floors `⌊c·x⌋`; the closed real arc
intersection is empty on every sub-interval of the stratum's own endpoint-crossing refinement).
The remaining five strata are the exact complement — every `(r, p)` there carries a run — and on
each of those five the dropped index is constant over all 1529 run-carrying `(r, p)`, which is a
strictly larger population than the window cells of `n ≤ 44` that arm D3 could see.

**THIS FILE IS THE CELL-LEVEL LEAN FORM OF THAT DICHOTOMY'S EASY SIDE.**  On a cell with no short
term every window term is INDIVIDUALLY divisible by `p^φ̃`, so any signed sum over any subset of
the window is too, and the open congruence `Zeta2PtpPolar.AHalfOpen` has nothing to prove there.
Two things are proved:

* **`carries_eq_of_residues`** — `carries p n k` depends on `(n, k)` only through `r = n % p` and
  `u = (k − 4n − 1) % p`, **with no prime and no window hypothesis**.  The landed
  `Zeta2PtpRun.vp_cTerm_residue_invariant` says this about the VALUATION and therefore needs
  `p ∈ phiWindow n` twice, because it routes through `vp_cTerm_eq_units`; at the level of the
  carry bits themselves the Legendre line is not spent at all.  That is what lets a future
  per-stratum argument quantify over `u < p` rather than over the window's `k`.
* **`pow_dvd_signed_sum`** — the bridge: `NoShort p n v` makes `(p:ℤ)^v` divide every signed sum
  over the window, termwise, via `Zeta2PtpRun.pow_dvd_cTerm_of_units`.

and then **seven kernel pins**, one window cell per run-free stratum, each `decide`d on the carry
bits alone (small residue arithmetic — never on `cTerm`, whose binomials at `n = 34` are
astronomically large):

    piece  1 [1/11, 1/9)      n = 1,  p = 11,  φ̃ = 2      piece 12 [5/11, 6/13)   n = 17, p = 37, φ̃ = 2
    piece  6 [1/5, 2/9)       n = 4,  p = 19,  φ̃ = 1      piece 15 [6/11, 5/9)    n = 16, p = 29, φ̃ = 2
    piece  6 [2/9, 5/22)      n = 7,  p = 31,  φ̃ = 1      piece 24 [10/11, 12/13) n = 34, p = 37, φ̃ = 2
    piece  6 [5/22, 3/13)     n = 14, p = 61,  φ̃ = 1

**AND ONE NEGATIVE PIN, because a predicate that cannot go red attests nothing.**
`not_noShort_at_3_13` is the smallest RUN-CARRYING cell (`n = 3`, `p = 13`, `φ̃ = 1`, run
`u ∈ [8, 12]`, `Zeta2PtpRun.run_at_3_13`'s own cell): `NoShort 13 3 1` is FALSE there.  So
`NoShort` separates the two sides of the dichotomy rather than holding everywhere, and the seven
green pins are not seven instances of a vacuous predicate.

**WHAT THIS DOES NOT DO, and the row is NOT closed.**  It is a statement about SEVEN CELLS, one
per run-free stratum, and NOT about the strata — the per-stratum statement quantifies over all
`(r, p)` in the stratum and is not proved here in any of the seven.  The open congruence itself,
`Zeta2PtpPolar.AHalfOpen` (the per-cell run congruence on the five run-carrying strata), is
UNTOUCHED, and so is `Zeta2PtpPolar.PolyHalfOpen`.  Nothing here is wired to `AHalfOpen`: that
would need `harmA`'s block decomposition, which this file deliberately does not import.  PT-P
stays OPEN and `Zeta2Target.zeta2_not_liouvilleWith` stays `sorry`.

Probe: `ptp_stratum_probe.py` / `.out` (9 arms, 4 kill controls, 1 recorded inert).
Falsifier: `falsify_ptpstratum.sh` / `out_ptpstratum_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2Profile
import Zeta2PhiT
import Zeta2HatGap
import Zeta2PtpRun

set_option maxRecDepth 20000

namespace Zeta2PtpStratum

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpRun Nat Finset

/-! ## 1. The four units-carry bits as one number -/

/-- **The carry count of `cTerm n k` in the units digit**, exactly the right-hand side of
`Zeta2PtpRun.vp_cTerm_eq_units`.  It is a pure residue computation: no binomial is ever formed,
which is what makes the kernel pins below cheap at `n = 34`. -/
def carries (p n k : ℕ) : ℕ :=
  cb p (k - 1) (13 * n) + cb p (k - 2 * n - 1) (9 * n)
    + cb p (k - 4 * n - 1) (5 * n) + cb p (11 * n) (k - 15 * n - 1)

/-- At a window prime the carry count IS the valuation — `vp_cTerm_eq_units`, renamed onto this
file's vocabulary so the pins below are about the same object the row's reduction consumes. -/
theorem carries_eq_vp {n k p : ℕ} (hp : p ∈ phiWindow n) (hk : k ∈ candidateM.window n) :
    padicValNat p (cTerm n k) = carries p n k :=
  vp_cTerm_eq_units hp hk

/-- **The carry count sees only two residues — and needs NO prime and NO window.**
`Zeta2PtpRun.vp_cTerm_residue_invariant` is this fact about the VALUATION, and it has to assume
`p ∈ phiWindow n` twice because it goes through `vp_cTerm_eq_units`.  At the level of the bits
the Legendre line is not spent, so the hypotheses are exactly the window's index inequalities —
which is what lets a per-stratum argument quantify over `u < p` instead of over `k`. -/
theorem carries_eq_of_residues {n k n' k' p : ℕ}
    (hk : k ∈ candidateM.window n) (hk' : k' ∈ candidateM.window n')
    (hr : n % p = n' % p) (hu : (k - 4 * n - 1) % p = (k' - 4 * n' - 1) % p) :
    carries p n k = carries p n' k' := by
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  obtain ⟨h1', h2'⟩ := (mem_window_iff n' k').1 hk'
  have mul_r : ∀ c : ℕ, (c * n) % p = (c * n') % p := by
    intro c; rw [Nat.mul_mod, hr, ← Nat.mul_mod]
  have e1 : (k - 1) % p = (k' - 1) % p := by
    have a : k - 1 = (k - 4 * n - 1) + 4 * n := by omega
    have b : k' - 1 = (k' - 4 * n' - 1) + 4 * n' := by omega
    rw [a, b, Nat.add_mod, hu, mul_r 4, ← Nat.add_mod]
  have e2 : (k - 2 * n - 1) % p = (k' - 2 * n' - 1) % p := by
    have a : k - 2 * n - 1 = (k - 4 * n - 1) + 2 * n := by omega
    have b : k' - 2 * n' - 1 = (k' - 4 * n' - 1) + 2 * n' := by omega
    rw [a, b, Nat.add_mod, hu, mul_r 2, ← Nat.add_mod]
  have e4 : (k - 15 * n - 1) % p = (k' - 15 * n' - 1) % p := by
    refine mod_cancel (mul_r 11) ?_
    have a : (k - 15 * n - 1) + 11 * n = k - 4 * n - 1 := by omega
    have b : (k' - 15 * n' - 1) + 11 * n' = k' - 4 * n' - 1 := by omega
    rw [a, b]; exact hu
  simp only [carries, cb, e1, e2, e4, hu, mul_r 13, mul_r 9, mul_r 5, mul_r 11]

/-! ## 2. A cell with no short term, and the bridge it gives the open congruence -/

/-- **The cell has NO SHORT TERM at exponent `v`**: every term of the window already carries `v`
units carries, hence `p^v`.  The probe's seven run-free strata are exactly where this holds with
`v = φ̃`; the five run-carrying strata are exactly where it fails. -/
def NoShort (p n v : ℕ) : Prop := ∀ k ∈ candidateM.window n, v ≤ carries p n k

/-- `NoShort` from a bound on any `Finset.Icc` containing the window — the shape the `decide`
pins below produce, with the window's own endpoints left to `omega`. -/
theorem noShort_of_Icc {n p v a b : ℕ} (ha : a ≤ 15 * n + 1) (hb : 26 * n + 1 ≤ b)
    (h : ∀ k ∈ Finset.Icc a b, v ≤ carries p n k) : NoShort p n v := by
  intro k hk
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  exact h k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)

/-- Termwise divisibility on a cell with no short term. -/
theorem pow_dvd_of_noShort {n p v : ℕ} (hp : p ∈ phiWindow n) (h : NoShort p n v)
    {k : ℕ} (hk : k ∈ candidateM.window n) : p ^ v ∣ cTerm n k := by
  refine pow_dvd_cTerm_of_units hp hk ?_
  simpa [carries] using h k hk

/-- **THE BRIDGE.**  On a cell with no short term, ANY signed sum over ANY subset of the window
is divisible by `p^v` — termwise, with no cancellation argument anywhere.  This is the sense in
which the seven run-free strata are not part of PT-P's open obligation: the congruence
`Σ_k (−1)^{k−1} cTerm(n,k) ≡ 0 mod p^φ̃` holds there for a reason that never looks at the sum. -/
theorem pow_dvd_signed_sum {n p v : ℕ} (hp : p ∈ phiWindow n) (h : NoShort p n v)
    (S : Finset ℕ) (hS : ∀ k ∈ S, k ∈ candidateM.window n) (ε : ℕ → ℤ) :
    (p : ℤ) ^ v ∣ ∑ k ∈ S, ε k * (cTerm n k : ℤ) := by
  refine Finset.dvd_sum fun k hk => ?_
  have hd : p ^ v ∣ cTerm n k := pow_dvd_of_noShort hp h (hS k hk)
  have hz : ((p ^ v : ℕ) : ℤ) ∣ ((cTerm n k : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hd
  rw [Nat.cast_pow] at hz
  exact hz.mul_left _

/-! ## 3. The seven run-free strata, one window cell each, by kernel computation -/

theorem bits_1_11 : ∀ k ∈ Finset.Icc 16 27, 2 ≤ carries 11 1 k := by decide
theorem bits_4_19 : ∀ k ∈ Finset.Icc 61 105, 1 ≤ carries 19 4 k := by decide
theorem bits_7_31 : ∀ k ∈ Finset.Icc 106 183, 1 ≤ carries 31 7 k := by decide
theorem bits_14_61 : ∀ k ∈ Finset.Icc 211 365, 1 ≤ carries 61 14 k := by decide
theorem bits_17_37 : ∀ k ∈ Finset.Icc 256 443, 2 ≤ carries 37 17 k := by decide
theorem bits_16_29 : ∀ k ∈ Finset.Icc 241 417, 2 ≤ carries 29 16 k := by decide
theorem bits_34_37 : ∀ k ∈ Finset.Icc 511 885, 2 ≤ carries 37 34 k := by decide

/-- piece 1, stratum `[1/11, 1/9)`. -/
theorem noShort_1_11 : NoShort 11 1 2 := noShort_of_Icc (by norm_num) (by norm_num) bits_1_11
/-- piece 6, stratum `[1/5, 2/9)`. -/
theorem noShort_4_19 : NoShort 19 4 1 := noShort_of_Icc (by norm_num) (by norm_num) bits_4_19
/-- piece 6, stratum `[2/9, 5/22)`. -/
theorem noShort_7_31 : NoShort 31 7 1 := noShort_of_Icc (by norm_num) (by norm_num) bits_7_31
/-- piece 6, stratum `[5/22, 3/13)`. -/
theorem noShort_14_61 : NoShort 61 14 1 := noShort_of_Icc (by norm_num) (by norm_num) bits_14_61
/-- piece 12, stratum `[5/11, 6/13)`. -/
theorem noShort_17_37 : NoShort 37 17 2 := noShort_of_Icc (by norm_num) (by norm_num) bits_17_37
/-- piece 15, stratum `[6/11, 5/9)`. -/
theorem noShort_16_29 : NoShort 29 16 2 := noShort_of_Icc (by norm_num) (by norm_num) bits_16_29
/-- piece 24, stratum `[10/11, 12/13)`. -/
theorem noShort_34_37 : NoShort 37 34 2 := noShort_of_Icc (by norm_num) (by norm_num) bits_34_37

/-! ## 4. The negative pin — `NoShort` can go red, so the seven greens are not vacuous -/

/-- **The smallest RUN-CARRYING cell fails `NoShort`.**  `n = 3`, `p = 13`, `φ̃ = 1`: the run
`u ∈ [8, 12]` of `Zeta2PtpRun.run_at_3_13` is exactly the `k` whose carry count is `0`, so
`NoShort 13 3 1` is FALSE.  Without this the seven pins above would be seven instances of a
predicate nothing distinguishes. -/
theorem not_bits_3_13 : ¬ (∀ k ∈ Finset.Icc 46 79, 1 ≤ carries 13 3 k) := by decide

theorem not_noShort_3_13 : ¬ NoShort 13 3 1 := by
  intro h
  exact not_bits_3_13 fun k hk => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hk
    exact h k ((mem_window_iff 3 k).2 ⟨by omega, by omega⟩)

end Zeta2PtpStratum

-- LEAN.md §1: `#print axioms` CANNOT see an undischarged hypothesis — a binder is not an axiom —
-- so acceptance is the receipt AND the printed TYPE, every binder read one by one.  Paired here
-- so the archive cannot carry one without the other.
#print axioms Zeta2PtpStratum.carries_eq_vp
#check @Zeta2PtpStratum.carries_eq_vp
#print axioms Zeta2PtpStratum.carries_eq_of_residues
#check @Zeta2PtpStratum.carries_eq_of_residues
#print axioms Zeta2PtpStratum.noShort_of_Icc
#check @Zeta2PtpStratum.noShort_of_Icc
#print axioms Zeta2PtpStratum.pow_dvd_of_noShort
#check @Zeta2PtpStratum.pow_dvd_of_noShort
#print axioms Zeta2PtpStratum.pow_dvd_signed_sum
#check @Zeta2PtpStratum.pow_dvd_signed_sum
#print axioms Zeta2PtpStratum.noShort_1_11
#check @Zeta2PtpStratum.noShort_1_11
#print axioms Zeta2PtpStratum.noShort_4_19
#check @Zeta2PtpStratum.noShort_4_19
#print axioms Zeta2PtpStratum.noShort_7_31
#check @Zeta2PtpStratum.noShort_7_31
#print axioms Zeta2PtpStratum.noShort_14_61
#check @Zeta2PtpStratum.noShort_14_61
#print axioms Zeta2PtpStratum.noShort_17_37
#check @Zeta2PtpStratum.noShort_17_37
#print axioms Zeta2PtpStratum.noShort_16_29
#check @Zeta2PtpStratum.noShort_16_29
#print axioms Zeta2PtpStratum.noShort_34_37
#check @Zeta2PtpStratum.noShort_34_37
#print axioms Zeta2PtpStratum.not_noShort_3_13
#check @Zeta2PtpStratum.not_noShort_3_13
