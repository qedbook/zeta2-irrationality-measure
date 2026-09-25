/-
# PT-QB clump 1 — the hat summand's Kummer atom, its ultrametric fold, and `hatQ n ≠ 0`

Row PT-QB of `docs/future/zeta2-lean-chain.md` (registry `2B0.AW`).  PT-QA
(`Zeta2CarryFold.pow_phiSingle_dvd_qnInt`, landed 2026-09-19) delivers the tale-1 half of the
`Φ̃` clearing at the SINGLE-representation profile `phiSingle`.  `phiT` (PT-DEF's `φ̃`) exceeds
`phiSingle` on exactly five intervals (`ptqb_gap_probe.py` ARM A, re-derived from both landed
tables rather than taken from the cell), and this file builds the machinery the hat half needs
there.  It adds four things and nothing else:

1. **`carry_bit_le_padicValNat_choose` — the units-digit carry bit is a LOWER bound on
   `ord_p C(a+b, b)` for EVERY prime `p`**, with no Legendre validity line.  Kummer counts all
   carries; the units digit is one of them.  This is what lets the hat reuse PT-DEF's cutoff
   `26n+1 < p²` instead of needing its own exact line `p² > 33n` (the largest hat binomial is
   `C(17n+2j, 2j)` with `17n + 2j ≤ 33n`).  `Zeta2Legendre.padicValNat_choose_carry` is the
   EQUALITY under that line; this is the inequality without it, and the two are different
   theorems, not two spellings of one.
2. **`padicValNat_hatA_ge` — the four one-term carry bits of `hatA n j`.**
   `hatA n j = C(17n+2j, 2j)·C(11n, 3n+j)·C(11n, n+j)·C(10n+j, 5n)`, so the bits are
   `[17n%p + 2j%p ≥ p] + [(3n+j)%p + (8n−j)%p ≥ p] + [(n+j)%p + (10n−j)%p ≥ p]
    + [5n%p + (5n+j)%p ≥ p]`.
3. **`pow_dvd_hatQ_of_termwise` — the fold.**  `hatQ n = −Σ_{j ≤ 8n} hatA n j`, an UNSIGNED sum
   under one outer sign, so `Finset.dvd_sum` and `dvd_neg` are the whole proof.  PT-QA's fold had
   to carry an alternating sum through `Dvd.dvd.mul_left`; this one does not.
4. **`hatQ_ne_zero`, unconditional in `n`** — `hatQ n < 0`, a negated sum of positive terms.
   PT-QA's `padicValInt_qnInt_ge_phi` carries a hypothesis `qnInt n ≠ 0` that its own header
   records as unproved anywhere in the corpus (`∀ n, qnInt n ≠ 0`); through PAIR's
   `Zeta2Pair8Close.pairing_q` this discharges it.  That composition is EXECUTED in
   `Zeta2HatQnInt.lean`, not asserted here — this file does not import PAIR.

## The measured probe this file banks: the cell `(12, 103)`

The row's cell names `2 ≤ padicValInt 103 (hatQ 12)` as its next probe — the hardest of the
thirteen cells where the tale-1 carry-min is strictly below `φ̃` (`hat_carry_probe.out` line
174: `φ̃ = 2`, hat carry-min 2, tale-1 carry-min 1) and the largest `n` the 2026-09-11 sweep
reached.  `hatQ 12` is a 97-term sum of `C(204+2j, 2j)`-class binomials.  MEASURED-buildbox
2026-09-19: the whole file elaborates in **5.1 s / 3.4 GB**, so the n = 12 data-scaling point
is not a wall for this row.

## What this file does NOT claim

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  There is no profile here:
the five gap intervals' carry lemmas and `PhiT_dvd_qnInt` are PT-QB's remaining work.  Nothing
here mentions `qnInt`, so nothing here is about the chain's `qₙ` until PAIR is applied.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
API at this pin, measured: `Nat.Prime 103` needs `import Mathlib.Tactic.NormNum.Prime` (the
bare `norm_num` closes `Nat.Prime` only with it; without, `unsolved goals ⊢ Nat.Prime 103`).
-/
import Zeta2Hat
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum.Prime

namespace Zeta2HatCarry

open Zeta2Defs Zeta2Hat Nat Finset

/-! ## The atom: a units-digit carry is a lower bound on `ord_p` of a binomial, at EVERY `p` -/

/-- **Kummer, as an inequality with no validity line.**  `ord_p C(a+b, b)` is the number of
carries when `a` and `b` are added in base `p`; the units-digit carry `p ≤ b % p + a % p` is one
of them, so it is a lower bound whatever `a + b` is relative to `p²`.

This is the difference between PT-QA's atom and PT-QB's.  `Zeta2Legendre.padicValNat_cTerm`
needs `26n+1 < p²` because it states the carry count EXACTLY (one Legendre term).  The hat's
largest binomial is `C(17n+2j, 2j)` with `17n + 2j ≤ 33n`, which `26n+1 < p²` does not put
below `p²` — but a lower bound does not care, so PT-DEF's window stands unchanged. -/
theorem carry_bit_le_padicValNat_choose (p a b : ℕ) [hp : Fact p.Prime] :
    (if p ≤ b % p + a % p then 1 else 0) ≤ padicValNat p ((a + b).choose b) := by
  split_ifs with h
  · have hp1 : 1 < p := hp.out.one_lt
    have hb : b % p ≤ b := Nat.mod_le _ _
    have ha : a % p ≤ a := Nat.mod_le _ _
    have hab : p ≤ a + b := by omega
    -- `Nat.pow_le_iff_le_log` does not exist at this pin (measured); `Nat.log_pos` does.
    have hlog : 1 ≤ Nat.log p (a + b) := Nat.log_pos hp1 hab
    rw [padicValNat_choose' (b := Nat.log p (a + b) + 1) (Nat.lt_succ_self _)]
    refine Finset.card_pos.2 ⟨1, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_Ico, pow_one]
    exact ⟨⟨le_refl 1, by omega⟩, h⟩
  · exact Nat.zero_le _

/-! ## The hat summand -/

/-- Every hat summand in `hatQ`'s range is positive.  `j ≤ 8n` is load-bearing and is exactly
that range: `C(11n, 3n+j)` vanishes for `j > 8n`. -/
theorem hatA_pos (n j : ℕ) (hj : j ≤ 8 * n) : 0 < hatA n j := by
  unfold hatA
  refine Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ?_ ?_) ?_) ?_
  · exact Nat.choose_pos (by omega)
  · exact Nat.choose_pos (by omega)
  · exact Nat.choose_pos (by omega)
  · exact Nat.choose_pos (by omega)

theorem hatA_ne_zero (n j : ℕ) (hj : j ≤ 8 * n) : hatA n j ≠ 0 := (hatA_pos n j hj).ne'

/-- **The hat's four one-term Kummer carry bits.**  One bit per binomial factor, each written
as `C(a + b, b)` with the split the window makes a genuine sum:
`C(17n+2j, 2j)` at `(17n, 2j)`, `C(11n, 3n+j)` at `(8n−j, 3n+j)`, `C(11n, n+j)` at
`(10n−j, n+j)`, `C(10n+j, 5n)` at `(5n+j, 5n)`.

No validity line: every bit is a LOWER bound (`carry_bit_le_padicValNat_choose`), so the hat
half of PT-QB runs inside PT-DEF's `phiWindow` without a second cutoff. -/
theorem padicValNat_hatA_ge (p n j : ℕ) [Fact p.Prime] (hj : j ≤ 8 * n) :
    (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0)
      + (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0)
      + (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0)
      + (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0)
    ≤ padicValNat p (hatA n j) := by
  have f1 : (17 * n + 2 * j).choose (2 * j) = ((17 * n) + 2 * j).choose (2 * j) := rfl
  have f2 : (11 * n).choose (3 * n + j) = ((8 * n - j) + (3 * n + j)).choose (3 * n + j) := by
    congr 1; omega
  have f3 : (11 * n).choose (n + j) = ((10 * n - j) + (n + j)).choose (n + j) := by
    congr 1; omega
  have f4 : (10 * n + j).choose (5 * n) = ((5 * n + j) + 5 * n).choose (5 * n) := by
    congr 1; omega
  have n1 : (17 * n + 2 * j).choose (2 * j) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n2 : (11 * n).choose (3 * n + j) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n3 : (11 * n).choose (n + j) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n4 : (10 * n + j).choose (5 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  rw [hatA, padicValNat.mul (mul_ne_zero (mul_ne_zero n1 n2) n3) n4,
    padicValNat.mul (mul_ne_zero n1 n2) n3, padicValNat.mul n1 n2]
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) ?_
  · rw [f1]; exact carry_bit_le_padicValNat_choose p (17 * n) (2 * j)
  · rw [f2]; exact carry_bit_le_padicValNat_choose p (8 * n - j) (3 * n + j)
  · rw [f3]; exact carry_bit_le_padicValNat_choose p (10 * n - j) (n + j)
  · rw [f4]; exact carry_bit_le_padicValNat_choose p (5 * n + j) (5 * n)

/-! ## `hatQ n ≠ 0`, unconditionally -/

/-- `hatQ n < 0` — a negated sum of positive terms, with `j = 0` in range at every `n`. -/
theorem hatQ_neg (n : ℕ) : hatQ n < 0 := by
  have hs : 0 < ∑ j ∈ range (8 * n + 1), (hatA n j : ℤ) := by
    refine Finset.sum_pos' (fun i _ => Int.natCast_nonneg _)
      ⟨0, Finset.mem_range.2 (by omega), ?_⟩
    exact_mod_cast hatA_pos n 0 (by omega)
  simpa [hatQ] using hs

/-- **`hatQ n ≠ 0` at every `n`.**  Through `Zeta2Pair8Close.pairing_q` this is
`∀ n, qnInt n ≠ 0` — the hypothesis `Zeta2CarryFold.padicValInt_qnInt_ge_phi` carries and whose
absence that file records ("nothing landed proves `∀ n, qnInt n ≠ 0`").  The composition is in
`Zeta2HatQnInt.lean`. -/
theorem hatQ_ne_zero (n : ℕ) : hatQ n ≠ 0 := (hatQ_neg n).ne

/-! ## The ultrametric fold, on an unsigned sum -/

/-- **The fold.**  A termwise `v ≤ ord_p (hatA n j)` over `j ≤ 8n` gives `p ^ v ∣ hatQ n`.
`hatQ` is `−Σ` of NONNEGATIVE terms, so `dvd_neg` and `Finset.dvd_sum` are the whole argument:
no sign bookkeeping inside the sum, and no `Σ ≠ 0`. -/
theorem pow_dvd_hatQ_of_termwise (n p v : ℕ) [Fact p.Prime]
    (h : ∀ j, j ≤ 8 * n → v ≤ padicValNat p (hatA n j)) :
    (p : ℤ) ^ v ∣ hatQ n := by
  rw [hatQ]
  refine dvd_neg.2 (Finset.dvd_sum ?_)
  intro j hj
  have hj' : j ≤ 8 * n := by
    have := Finset.mem_range.1 hj
    omega
  have hd : p ^ v ∣ hatA n j := (pow_dvd_pow p (h j hj')).trans pow_padicValNat_dvd
  exact_mod_cast hd

/-- The fold at the four bits, in the shape the five gap-interval lemmas produce. -/
theorem pow_dvd_hatQ_of_bits (n p v : ℕ) [Fact p.Prime]
    (h : ∀ j, j ≤ 8 * n →
      v ≤ (if p ≤ (2 * j) % p + (17 * n) % p then 1 else 0)
        + (if p ≤ (3 * n + j) % p + (8 * n - j) % p then 1 else 0)
        + (if p ≤ (n + j) % p + (10 * n - j) % p then 1 else 0)
        + (if p ≤ (5 * n) % p + (5 * n + j) % p then 1 else 0)) :
    (p : ℤ) ^ v ∣ hatQ n :=
  pow_dvd_hatQ_of_termwise n p v
    (fun j hj => (h j hj).trans (padicValNat_hatA_ge p n j hj))

/-! ## The banked cell: `(12, 103)` (LEAN.md §5 — the edge case compiles, so state it) -/

/-- **The cell the row named as its next probe.**  `φ̃({12/103}) = 2`, the tale-1 carry-min is
`1` and the hat carry-min is `2`, so `103² ∣ q₁₂` is exactly what the hat half has to deliver
and the tale-1 half cannot.  Here on `hatQ`; `Zeta2HatQnInt.lean` transports it to `qnInt`. -/
theorem hatQ_twelve_emod : hatQ 12 % 10609 = 0 := by
  simp only [hatQ, hatA, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem sq_103_dvd_hatQ_twelve : (103 : ℤ) ^ 2 ∣ hatQ 12 := by
  have h : (10609 : ℤ) ∣ hatQ 12 := Int.dvd_of_emod_eq_zero hatQ_twelve_emod
  norm_num at h ⊢
  exact h

/-- The `padicValInt` form the cell states, with the nonvanishing supplied rather than assumed. -/
theorem two_le_padicValInt_103_hatQ_twelve : 2 ≤ padicValInt 103 (hatQ 12) := by
  have : Fact (Nat.Prime 103) := ⟨by norm_num⟩
  exact ((padicValInt_dvd_iff 2 (hatQ 12)).1 sq_103_dvd_hatQ_twelve).resolve_left (hatQ_ne_zero 12)

end Zeta2HatCarry

#print axioms Zeta2HatCarry.carry_bit_le_padicValNat_choose
#print axioms Zeta2HatCarry.hatA_pos
#print axioms Zeta2HatCarry.hatA_ne_zero
#print axioms Zeta2HatCarry.padicValNat_hatA_ge
#print axioms Zeta2HatCarry.hatQ_neg
#print axioms Zeta2HatCarry.hatQ_ne_zero
#print axioms Zeta2HatCarry.pow_dvd_hatQ_of_termwise
#print axioms Zeta2HatCarry.pow_dvd_hatQ_of_bits
#print axioms Zeta2HatCarry.hatQ_twelve_emod
#print axioms Zeta2HatCarry.sq_103_dvd_hatQ_twelve
#print axioms Zeta2HatCarry.two_le_padicValInt_103_hatQ_twelve
