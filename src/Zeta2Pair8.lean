/-
# ROW PAIR-8 — the crossing and the strong induction

`docs/future/zeta2-lean-chain.md` row PAIR-8.

**READ THE HEADLINE FIRST: the row's two theorems are NOT proved here, and this file does not
claim them.**  What is proved is `pairing_q_of_chain_rec` and `pairing_p_of_chain_rec`:

    ∀ n, hatQ n = qnInt n            GIVEN the CHAIN-side recurrence at `candidateM.qn`
    ∀ n, hatP n = candidateM.pn n    GIVEN the CHAIN-side recurrence at `candidateM.pn`
                                     and the `n < N₀ + 3` base on the p coordinate

The missing hypothesis is **L1-ASM's `hrecq_rat` / `hrecp_rat`**, and it is `not started` —
it sits behind STAR, STAR-ID, PHI-REP, PHI-BDY and PHI-EVAL, every one of them open.  It was
named in this row's own column 2 all along (`in: PAIR-VAL, PAIR-6, PAIR-7, L1-ASM (hrecq_rat,
hrecp_rat …), STAR-ID (ii)`); the PAIR-6/PAIR-7/PAIR-N landings of 2026-09-14 discharged the
HAT side of the row and left the CHAIN side untouched.  `Zeta2Target.zeta2_not_liouvilleWith`
is still `sorry`, and this file changes nothing about that.  The same hypothesis is already
carried, in its ℝ cast, by `Zeta2L9L11Instantiate`'s `hrecq`/`hrecp` binders: the whole chain
is parametric in it, so taking it as a hypothesis here is the house shape, not a shortcut.

**What IS new, and unconditional:**

  * `lamDen_ne_zero` — PAIR-8's own deg-58 nonvanishing, from `Zeta2Pair8Lam`.
  * `hat_rec_of_chain_rec` — THE CROSSING.  A four-term relation in the CHAIN's operator `γ`
    becomes one in the HAT's `β̂`, for an ARBITRARY sequence `f : ℕ → ℚ`.  This is the step the
    row exists to perform, and it consumes exactly PAIR-7 (`Zeta2Pair8Tie.pair7N`), the
    operator tie (`Zeta2Pair8Tie.betaHat_tie`) and `λden ≠ 0`.  It needs NO `λnum ≠ 0` and no
    `L_t1 ≠ 0`: the division goes the one way, from `γ` to `β̂`.
  * `lamNum_ne_zero` and `gammaN_three_ne_zero` — DERIVED from `betaHat_three_ne_zero` and
    `λden ≠ 0` through PAIR-7 at `j = 3`, with no new data and no new scan.  They are what says
    the conditional theorems below are not vacuous, and they make the crossing REVERSIBLE.
  * `hatQ_chain_rec` / `hatP_chain_rec` — UNCONDITIONAL: the HAT sequences satisfy the CHAIN
    solve's own recurrence for every `n ≥ 2`.  PAIR-6 carried across the seam this row owns.
  * `seq_zero_of_rec` — the strong induction, over an abstract `d` and an abstract operator.
  * `sum4_of_written` and `chain_rec_of_scaled` — the two shape adapters L1-ASM will need.

**THE BASE, AND ITS ARITHMETIC, CHECKED HERE RATHER THAN INHERITED.**  PAIR-6's recurrence
holds for `n ≥ 2`; L1-ASM's holds for `n ≥ N₀`.  So the difference `d` satisfies a four-term
relation exactly for `n ≥ max 2 N₀`, the induction determines `d(n+3)` from `d n, d(n+1),
d(n+2)`, and the cells it can never reach are `n < N₀ + 3`.  That is the base, and it is
PARAMETRIC: this file takes `N₀` as an argument with `2 ≤ N₀` rather than writing down a
number.  The row's own cell has carried `N₀ = 9` and `N₀ = 6` at different times and its
PAIR-VAL sibling closed at `n ≤ 8` after `N₀ = 9` turned out to be a misread `max` over a
differently-indexed family; the honest thing is to take whatever L1-ASM exports.  The q half
then needs `N₀ ≤ 9`, which is exactly the reach of the landed
`Zeta2PairVal.hatQ_eq_qnInt_base` (`∀ n < 12`).  The p half takes its base as a hypothesis,
discharged cell by cell by `Zeta2Hat.hatP_eq_pn_zero` and `Zeta2PairP{1..11}.hatP_eq_pn`
(receipted through n = 10; the n = 11 cell is generated and unreceipted, so an L1-ASM that
exports `N₀ = 9` owes that one receipt and an `N₀ ≤ 8` does not).

**TWO nonvanishings, and they are different theorems.**  `Zeta2PairNTie.betaHat_three_ne_zero`
(`al3`, deg 154) is what the INDUCTION divides by; `Zeta2Pair8Lam.lden_eval_ne_zero` (λden,
deg 58) is what the CROSSING divides by.  Neither discharges the other.

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2Pair8.lean

Receipts: `out_axioms_pair8.txt`.  Falsifier: `falsify_pair8.sh --lean`.  Second
implementation, in exact ℚ: `pair8_check.py` → `pair8_check.out`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Pair8Tie
import Zeta2Pair8Lam
import Zeta2PairNTie
import Zeta2PairVal

-- FILE-LEVEL on purpose: placed between a docstring and its theorem a `set_option` is a parse
-- error Lean silently RECOVERS from — the file does not parse, the option is dropped, and every
-- receipt still prints clean (zeta2-lean-chain.md, PAIR-7's and PAIR-6's landings).
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Zeta2Pair8

open Zeta2Defs Zeta2Arith Zeta2Hat

/-! ## 1. `λden ≠ 0`, in the shape PAIR-7's modules write it -/

/-- `Zeta2Pair8Lam.lden_eval_ne_zero` read at `Zeta2Pair7J0.lamDen`, which is
`hornerQ lden n / (dld : ℚ)` with `dld = 1`. -/
theorem lamDen_ne_zero (n : ℕ) : Zeta2Pair7J0.lamDen n ≠ 0 := by
  rw [Zeta2Pair7J0.lamDen]
  refine div_ne_zero (Zeta2Pair8Lam.lden_eval_ne_zero n) ?_
  rw [Zeta2Pair7Lam.dld]
  norm_num

/-! ## 2. The crossing — from the CHAIN's operator to the HAT's -/

/--
**THE CROSSING.**  If an arbitrary sequence `f` satisfies the four-term relation in the CHAIN
solve's operator `γ` at `n`, it satisfies it in the HAT solve's operator `β̂` at `n`.

The whole content is PAIR-7's proportionality `β̂ⱼ·λden = γⱼ·λnum` (at PAIR-6's own operator,
via the tie) plus `λden(n) ≠ 0`.  Note the ASYMMETRY: this direction needs only `λden ≠ 0`.
Going the other way — from a relation in `β̂` to one in `γ` — would need `λnum ≠ 0`, which
this row does not own and does not need.
-/
theorem hat_rec_of_chain_rec (f : ℕ → ℚ) (n : ℕ)
    (h : ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * f (n + j) = 0) :
    ∑ j ∈ Finset.range 4, Zeta2Pair6.betaHat n j * f (n + j) = 0 := by
  have hd := lamDen_ne_zero n
  have e0 := Zeta2Pair8Tie.pair7N n 0 (by omega)
  have e1 := Zeta2Pair8Tie.pair7N n 1 (by omega)
  have e2 := Zeta2Pair8Tie.pair7N n 2 (by omega)
  have e3 := Zeta2Pair8Tie.pair7N n 3 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero] at h ⊢
  have key : (Zeta2Pair6.betaHat n 0 * f n + Zeta2Pair6.betaHat n 1 * f (n + 1)
      + Zeta2Pair6.betaHat n 2 * f (n + 2) + Zeta2Pair6.betaHat n 3 * f (n + 3))
      * Zeta2Pair7J0.lamDen n = 0 := by
    linear_combination f n * e0 + f (n + 1) * e1 + f (n + 2) * e2 + f (n + 3) * e3
      + Zeta2Pair7J0.lamNum n * h
  exact (mul_eq_zero.mp key).resolve_right hd

/-! ## 2b. The crossing is NOT vacuous, and that is a theorem rather than a measurement

A conditional theorem is worth exactly as much as the satisfiability of its hypothesis, and a
crossing that divided by something zero, or an operator `γ` that were identically zero, would
make section 5 read fine and say nothing.  Neither can happen, and the proof is already in
hand: `betaHat_three_ne_zero` (PAIR-N) and `lamDen_ne_zero` (this row) make the LEFT side of
`pair7N` at `j = 3` nonzero, so its RIGHT side is too — which forces BOTH `λnum(n) ≠ 0` and
`γ₃(n) ≠ 0`, at every `n`, with no new data and no new scan.  PAIR-6's own non-vacuity check
lives only in its exact-ℚ second implementation (`pair6_check.py` §5); this one is carried by
a Lean receipt. -/

theorem pair7N_three_ne_zero (n : ℕ) :
    Zeta2Pair8Tie.gammaN n 3 * Zeta2Pair7J0.lamNum n ≠ 0 := by
  rw [← Zeta2Pair8Tie.pair7N n 3 (by omega)]
  exact mul_ne_zero (Zeta2PairNTie.betaHat_three_ne_zero n) (lamDen_ne_zero n)

/-- `λnum(n) ≠ 0` — derived, not scanned.  It is what makes the crossing REVERSIBLE. -/
theorem lamNum_ne_zero (n : ℕ) : Zeta2Pair7J0.lamNum n ≠ 0 :=
  fun h => pair7N_three_ne_zero n (by rw [h, mul_zero])

/-- The CHAIN operator's own `j = 3` entry is nonzero at every `n` — the chain-side twin of
`Zeta2PairNTie.betaHat_three_ne_zero`, obtained from it rather than from `L_t1`. -/
theorem gammaN_three_ne_zero (n : ℕ) : Zeta2Pair8Tie.gammaN n 3 ≠ 0 :=
  fun h => pair7N_three_ne_zero n (by rw [h, zero_mul])

/-- **The crossing, the other way.**  Free once `λnum ≠ 0` is a theorem, and it turns PAIR-6's
recurrence into a statement about the CHAIN solve's operator. -/
theorem chain_rec_of_hat_rec (f : ℕ → ℚ) (n : ℕ)
    (h : ∑ j ∈ Finset.range 4, Zeta2Pair6.betaHat n j * f (n + j) = 0) :
    ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * f (n + j) = 0 := by
  have hd := lamNum_ne_zero n
  have e0 := Zeta2Pair8Tie.pair7N n 0 (by omega)
  have e1 := Zeta2Pair8Tie.pair7N n 1 (by omega)
  have e2 := Zeta2Pair8Tie.pair7N n 2 (by omega)
  have e3 := Zeta2Pair8Tie.pair7N n 3 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero] at h ⊢
  have key : (Zeta2Pair8Tie.gammaN n 0 * f n + Zeta2Pair8Tie.gammaN n 1 * f (n + 1)
      + Zeta2Pair8Tie.gammaN n 2 * f (n + 2) + Zeta2Pair8Tie.gammaN n 3 * f (n + 3))
      * Zeta2Pair7J0.lamNum n = 0 := by
    linear_combination (-(f n)) * e0 - f (n + 1) * e1 - f (n + 2) * e2 - f (n + 3) * e3
      + Zeta2Pair7J0.lamDen n * h
  exact (mul_eq_zero.mp key).resolve_right hd

/-- **UNCONDITIONAL.**  The HAT solve's `q` sequence satisfies the CHAIN solve's recurrence for
every `n ≥ 2` — PAIR-6 carried across the seam this row owns.  It is half of what PAIR-8 needs;
the other half is that `candidateM.qn` satisfies the same relation, which is L1-ASM's and is
not proved anywhere. -/
theorem hatQ_chain_rec (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * ((hatQ (n + j) : ℤ) : ℚ) = 0 :=
  chain_rec_of_hat_rec (fun k => ((hatQ k : ℤ) : ℚ)) n (Zeta2Pair6.hatQ_rec n hn)

/-- **UNCONDITIONAL.**  The same on the `p` coordinate. -/
theorem hatP_chain_rec (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * hatP (n + j) = 0 :=
  chain_rec_of_hat_rec (fun k => hatP k) n (Zeta2Pair6.hatP_rec n hn)

/-! ## 3. Two shape adapters for whatever L1-ASM exports

L1-ASM will state its recurrence as a WRITTEN-OUT four-term sum (that is the shape
`Zeta2L9L11`'s `hrecq`/`hrecp` binders already have), and its `αⱼ` is STAR-ID (ii)'s
`clearedⱼ/cleared₃`, which is `γⱼ` up to a `j`-independent scalar rather than `γⱼ` on the
nose.  Both gaps are shape, not mathematics, and both are closed here so that PAIR-8 does not
have to be rewritten when L1-ASM lands. -/

/-- A written-out four-term relation is the `Finset.range 4` sum this file consumes. -/
theorem sum4_of_written (a : ℕ → ℕ → ℚ) (f : ℕ → ℚ) (n : ℕ)
    (h : a n 0 * f n + a n 1 * f (n + 1) + a n 2 * f (n + 2) + a n 3 * f (n + 3) = 0) :
    ∑ j ∈ Finset.range 4, a n j * f (n + j) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]
  linear_combination h

/-- The relation is HOMOGENEOUS in the operator, so any `j`-independent nonzero rescaling of
`γ` carries it.  This is what lets PAIR-8 accept an operator identified with `γ` only up to
normalisation — the seam §6a is about. -/
theorem chain_rec_of_scaled (a : ℕ → ℕ → ℚ) (c : ℕ → ℚ) (f : ℕ → ℚ) (n : ℕ) (hc : c n ≠ 0)
    (ha : ∀ j, j ≤ 3 → a n j = c n * Zeta2Pair8Tie.gammaN n j)
    (h : ∑ j ∈ Finset.range 4, a n j * f (n + j) = 0) :
    ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * f (n + j) = 0 := by
  have h0 := ha 0 (by omega)
  have h1 := ha 1 (by omega)
  have h2 := ha 2 (by omega)
  have h3 := ha 3 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero] at h ⊢
  have key : c n * (Zeta2Pair8Tie.gammaN n 0 * f n + Zeta2Pair8Tie.gammaN n 1 * f (n + 1)
      + Zeta2Pair8Tie.gammaN n 2 * f (n + 2) + Zeta2Pair8Tie.gammaN n 3 * f (n + 3)) = 0 := by
    linear_combination h - f n * h0 - f (n + 1) * h1 - f (n + 2) * h2 - f (n + 3) * h3
  exact (mul_eq_zero.mp key).resolve_left hc

/-! ## 4. The strong induction, abstractly -/

/--
**A four-term recurrence with a nonvanishing leading coefficient propagates zero.**

`b n 3 ≠ 0` lets the relation at `n` be solved for `d (n+3)`, so every cell at or above
`N₀ + 3` is determined by three earlier ones; the cells below that are the base.  Stated over
an abstract `d` and `b` because PAIR-8 uses it twice, on the q and p coordinates, and because
it is the piece with no data in it at all.
-/
theorem seq_zero_of_rec (d : ℕ → ℚ) (b : ℕ → ℕ → ℚ) (N0 : ℕ)
    (hb3 : ∀ n, N0 ≤ n → b n 3 ≠ 0)
    (hrec : ∀ n, N0 ≤ n → ∑ j ∈ Finset.range 4, b n j * d (n + j) = 0)
    (hbase : ∀ n, n < N0 + 3 → d n = 0) :
    ∀ n, d n = 0 := by
  have key : ∀ N : ℕ, ∀ k, k < N → d k = 0 := by
    intro N
    induction N with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ N ih =>
        intro k hk
        rcases Nat.lt_or_ge k (N0 + 3) with h | h
        · exact hbase k h
        · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
          have hm : N0 ≤ m := by omega
          have hr := hrec m hm
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
            Nat.add_zero] at hr
          rw [ih m (by omega), ih (m + 1) (by omega), ih (m + 2) (by omega)] at hr
          simp only [mul_zero, zero_add, add_zero] at hr
          exact (mul_eq_zero.mp hr).resolve_left (hb3 m hm)
  intro n
  exact key (n + 1) n (Nat.lt_succ_self n)

/-! ## 5. Row PAIR-8, conditional on L1-ASM

Both statements land in the types their consumers read: PT-QB consumes `hatQ n = qnInt n` as
an equation in `ℤ` (it takes `padicValInt p` of both sides), and PT-P consumes `hatP n =
candidateM.pn n` as an equation in `ℚ`.  They are PAIR-0's and PAIR-0p's statements with the
`n < 3` / `n = 1, 2` bounds removed, which is what the row's column 1 asks for. -/

/--
**ROW PAIR-8, the q coordinate — CONDITIONAL.**  Given the CHAIN solve's four-term recurrence
at `candidateM.qn` from `N₀` on (L1-ASM's `hrecq_rat`, NOT PROVED anywhere), the hat's `q`
sequence IS the chain's, at every `n`.

`N₀ ≤ 9` is the only bound, and it is the reach of the landed base
`Zeta2PairVal.hatQ_eq_qnInt_base : ∀ n < 12, hatQ n = qnInt n`.
-/
theorem pairing_q_of_chain_rec (N0 : ℕ) (hN2 : 2 ≤ N0) (hN9 : N0 ≤ 9)
    (hrecq : ∀ n, N0 ≤ n →
      ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * candidateM.qn (n + j) = 0) :
    ∀ n, hatQ n = qnInt n := by
  have hz := seq_zero_of_rec (fun k => ((hatQ k : ℤ) : ℚ) - candidateM.qn k)
    Zeta2Pair6.betaHat N0
    (fun n _ => Zeta2PairNTie.betaHat_three_ne_zero n)
    (by
      intro n hn
      have h1 := Zeta2Pair6.hatQ_rec n (by omega)
      have h2 := hat_rec_of_chain_rec candidateM.qn n (hrecq n hn)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.add_zero] at h1 h2 ⊢
      linear_combination h1 - h2)
    (by
      intro n hn
      show ((hatQ n : ℤ) : ℚ) - candidateM.qn n = 0
      rw [Zeta2PairVal.hatQ_eq_qnInt_base n (by omega), qnInt_cast]
      ring)
  intro n
  have h : ((hatQ n : ℤ) : ℚ) - candidateM.qn n = 0 := hz n
  have hq : ((hatQ n : ℤ) : ℚ) = ((qnInt n : ℤ) : ℚ) := by
    rw [qnInt_cast]
    linarith
  exact_mod_cast hq

/--
**ROW PAIR-8, the p coordinate — CONDITIONAL, on two hypotheses rather than one.**  Besides
L1-ASM's `hrecp_rat` this one takes the base explicitly: PAIR-VAL closed the p coordinate cell
by cell (`Zeta2Hat.hatP_eq_pn_zero`, `Zeta2PairP{1..10}.hatP_eq_pn`, all receipted, plus an
unreceipted n = 11) and never assembled the `∀ n < N₀ + 3` statement, so the assembly is a
lookup rather than a proof and is left to the consumer that knows which `N₀` it has.
-/
theorem pairing_p_of_chain_rec (N0 : ℕ) (hN2 : 2 ≤ N0)
    (hbase : ∀ n, n < N0 + 3 → hatP n = candidateM.pn n)
    (hrecp : ∀ n, N0 ≤ n →
      ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * candidateM.pn (n + j) = 0) :
    ∀ n, hatP n = candidateM.pn n := by
  have hz := seq_zero_of_rec (fun k => hatP k - candidateM.pn k)
    Zeta2Pair6.betaHat N0
    (fun n _ => Zeta2PairNTie.betaHat_three_ne_zero n)
    (by
      intro n hn
      have h1 := Zeta2Pair6.hatP_rec n (by omega)
      have h2 := hat_rec_of_chain_rec candidateM.pn n (hrecp n hn)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.add_zero] at h1 h2 ⊢
      linear_combination h1 - h2)
    (by
      intro n hn
      show hatP n - candidateM.pn n = 0
      rw [hbase n hn]
      ring)
  intro n
  have h : hatP n - candidateM.pn n = 0 := hz n
  linarith

end Zeta2Pair8

#print axioms Zeta2Pair8.lamDen_ne_zero
#print axioms Zeta2Pair8.hat_rec_of_chain_rec
#print axioms Zeta2Pair8.pair7N_three_ne_zero
#print axioms Zeta2Pair8.lamNum_ne_zero
#print axioms Zeta2Pair8.gammaN_three_ne_zero
#print axioms Zeta2Pair8.chain_rec_of_hat_rec
#print axioms Zeta2Pair8.hatQ_chain_rec
#print axioms Zeta2Pair8.hatP_chain_rec
#print axioms Zeta2Pair8.sum4_of_written
#print axioms Zeta2Pair8.chain_rec_of_scaled
#print axioms Zeta2Pair8.seq_zero_of_rec
#print axioms Zeta2Pair8.pairing_q_of_chain_rec
#print axioms Zeta2Pair8.pairing_p_of_chain_rec
