/-
# `Zeta2PnHarmDelta.lean` — row PNCLR's LAST obligation, and the row

`Zeta2PnFunc` closed PNCLR's polynomial half (`Δ_mul_Pin_pnPoly_int`) and reduced everything
that was left to ONE divisibility with no sum, no `harm` and no polynomial in it:

    D (k - 4n - 1)² ∣ Δ 16 15 n · cTerm n k        for every k of the window [15n+1, 26n+1]

(`Zeta2PnFunc.harm_cleared_of_dvd`, then `Zeta2PnFunc.pn_cleared_1615_of_harm`).  **This file
proves that divisibility and closes row PNCLR**, at the chain's own constants, unconditionally.

## The mechanism, in one paragraph

Write `m := k - 4n - 1 ∈ [11n, 22n]`, `E := ⌊log_p m⌋`, `q := p^E`.  `ord_p (D j) = ⌊log_p j⌋`
(`Zeta2PhiT.factorization_D`), so at each prime the statement is

    2·⌊log_p m⌋ ≤ ⌊log_p 16n⌋ + ⌊log_p 15n⌋ + ord_p (cTerm n k).

* **If `q ≤ 15n` the two `⌊log_p⌋` terms already pay**: `E ≤ ⌊log_p 15n⌋ ≤ ⌊log_p 16n⌋`, and
  `ord_p (cTerm n k) ≥ 0` finishes it.  Nothing about the term is used.
* **If `q > 15n` the DEFICIT is at most 2** — and that is not a measurement, it is
  `p^{E-1} ≤ m/p ≤ 11n`, so BOTH `⌊log_p 15n⌋` and `⌊log_p 16n⌋` are `≥ E - 1`.
* **And `cTerm` supplies exactly that 2, from TWO Kummer carries in TWO DIFFERENT factors.**
  `cTerm n k = C(k−1,13n)·C(k−2n−1,9n)·C(k−4n−1,5n)·C(11n,k−15n−1)` (`Zeta2QnInt.cTerm`), and
  `q ≤ m` forces `k ≥ q + 4n + 1`, so at position `E`

      13n + (k − 13n − 1) = k − 1    ≥ q ,   both summands `< q`   → a carry in the 1st factor
      9n  + (k − 11n − 1) = k − 2n−1 ≥ q ,   both summands `< q`   → a carry in the 2nd factor

  — two carries in two different factors of a PRODUCT, so their `ord_p`s ADD.  Nothing is needed
  about the other two factors and nothing is needed about any other level: no termwise
  nonnegativity, no Legendre line, no `26n+1 < p²` window.

## What this file does NOT claim

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  This closes ONE row of
the chain (PNCLR).  Its consumer PT-P — `(PhiT n : ℤ) ∣ P n` for the witness `P` this row now
produces — is open, and so are L7ID, L1-ASM, QGROW, RDECAY and T-WIRE.

## The constant, and the two right answers about it

The MECHANISM needs `q > 15n`: `13n < q` and `k − 13n − 1 ≤ 13n < q` are its side conditions,
so the theorem is stated at `Δ 16 15` and that is the pair the row wants anyway.  The least `c`
with `D(16n)·D(cn)` clearing every term is MEASURED as **13** (12 at `n = 4`, the same dip the
polynomial half records) — `pn_harm_carry_probe.py` arm C6.  The two numbers are about
different things and neither refutes the other: a proof at 13 would need a second mechanism on
`q ∈ (13n, 15n]` and the row does not need one.  `D(16n)·D(14n)` was this probe's first
wanted-RED control and came back INERT; the control was moved to `D(16n)·D(12n)` from that
measurement rather than from taste.

## Provenance

* `carry_at_le_padicValNat_choose` **generalizes `Zeta2HatCarry.carry_bit_le_padicValNat_choose`
  from the units digit to an arbitrary position `e`**, by the same idiom (`padicValNat_choose'`
  plus `Finset.card_pos`), with the landed lemma recovered at `e = 1`.  It is proved here rather
  than in `Zeta2HatCarry` only to keep this file's dependency set from dragging
  `Zeta2Hat`/`Zeta2Legendre`/`Zeta2CarryP1`/`Zeta2CarryFull`/`Zeta2CarryFold` in for one lemma;
  `Zeta2HatCarry` is its right long-term home and the units-digit atom should become the `e = 1`
  instance there.
* The four-factor `padicValNat.mul` split and its `Nat.choose_ne_zero (by omega)` side
  conditions are `Zeta2Arith.padicValNat_cTerm`'s, reused verbatim — that lemma itself is NOT
  usable here, because it needs `26n + 1 < p²` and the pressured primes are exactly the ones
  that fails for.

## Evidence

`pn_harm_carry_probe.py` / `.out`: 107 358 `(n, k, p)` triples — every `n ∈ 0..8` plus
`n = 11, 19, 37` out of sample, every `k` of the window, every prime `p ≤ 26n+1`, enumerated
and scored, not sampled.  Max deficit **2**, confined to `p^E ∈ (15n, 22n]` at 107 358/107 358;
both carries present at 9 379/9 379 pressured triples; six wanted-RED controls all fired.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2PhiT
import Zeta2PnHarm
import Zeta2PnCleared
import Zeta2PnFunc

namespace Zeta2PnHarmDelta

open Zeta2Defs Zeta2Arith Nat Finset

/-! ## 1. Kummer at an ARBITRARY position -/

/-- **A carry at position `e` is a lower bound on `ord_p C(a+b, b)`.**  `Zeta2HatCarry.
carry_bit_le_padicValNat_choose` is this at `e = 1`; the pressured level of this row is the TOP
one, `e = ⌊log_p m⌋`, which for `p^e ≤ 22n` is not the units digit. -/
theorem carry_at_le_padicValNat_choose (p a b e : ℕ) [hp : Fact p.Prime]
    (he1 : 1 ≤ e) (he2 : e ≤ Nat.log p (a + b))
    (h : p ^ e ≤ b % p ^ e + a % p ^ e) :
    1 ≤ padicValNat p ((a + b).choose b) := by
  rw [padicValNat_choose' (b := Nat.log p (a + b) + 1) (Nat.lt_succ_self _)]
  refine Finset.card_pos.2 ⟨e, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨he1, by omega⟩, h⟩

/-! ## 2. The pressured level supplies two carries -/

/-- **Two carries at one position, in two different factors of `cTerm`.**  The hypotheses are
exactly what `q ≤ m` and `q > 15n` deliver; no `p²` window and no other level. -/
theorem two_carries (n k p E : ℕ) [hp : Fact p.Prime]
    (hk1 : 15 * n + 1 ≤ k) (hk2 : k ≤ 26 * n + 1)
    (hE1 : 1 ≤ E) (hlo : 15 * n < p ^ E) (hhi : p ^ E ≤ k - 4 * n - 1)
    (hlog1 : E ≤ Nat.log p (k - 1)) (hlog2 : E ≤ Nat.log p (k - 2 * n - 1)) :
    2 ≤ padicValNat p (cTerm n k) := by
  have n1 : (k - 1).choose (13 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n2 : (k - 2 * n - 1).choose (9 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n3 : (k - 4 * n - 1).choose (5 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n4 : (11 * n).choose (k - 15 * n - 1) ≠ 0 := Nat.choose_ne_zero (by omega)
  -- the two indices are genuine sums on the window (`Zeta2Arith.padicValNat_cTerm`'s f1/f2)
  have f1 : (k - 1).choose (13 * n) = ((k - 13 * n - 1) + 13 * n).choose (13 * n) := by
    congr 1; omega
  have f2 : (k - 2 * n - 1).choose (9 * n) = ((k - 11 * n - 1) + 9 * n).choose (9 * n) := by
    congr 1; omega
  -- the four side conditions the mechanism needs, all from `15n < p^E` and the window
  have s1 : 13 * n < p ^ E := by omega
  have s2 : k - 13 * n - 1 < p ^ E := by omega
  have s3 : 9 * n < p ^ E := by omega
  have s4 : k - 11 * n - 1 < p ^ E := by omega
  have hc1 : 1 ≤ padicValNat p ((k - 1).choose (13 * n)) := by
    rw [f1]
    refine carry_at_le_padicValNat_choose p (k - 13 * n - 1) (13 * n) E hE1 ?_ ?_
    · have : (k - 13 * n - 1) + 13 * n = k - 1 := by omega
      rw [this]; exact hlog1
    · rw [Nat.mod_eq_of_lt s1, Nat.mod_eq_of_lt s2]; omega
  have hc2 : 1 ≤ padicValNat p ((k - 2 * n - 1).choose (9 * n)) := by
    rw [f2]
    refine carry_at_le_padicValNat_choose p (k - 11 * n - 1) (9 * n) E hE1 ?_ ?_
    · have : (k - 11 * n - 1) + 9 * n = k - 2 * n - 1 := by omega
      rw [this]; exact hlog2
    · rw [Nat.mod_eq_of_lt s3, Nat.mod_eq_of_lt s4]; omega
  rw [cTerm, padicValNat.mul (mul_ne_zero (mul_ne_zero n1 n2) n3) n4,
    padicValNat.mul (mul_ne_zero n1 n2) n3, padicValNat.mul n1 n2]
  omega

/-! ## 3. The per-prime inequality -/

/-- **The whole content, at one prime.**  `2·⌊log_p m⌋ ≤ ⌊log_p 16n⌋ + ⌊log_p 15n⌋ +
ord_p (cTerm n k)`, by one case split on whether `p^{⌊log_p m⌋}` clears `15n`. -/
theorem vp_bound (n k : ℕ) (hk : k ∈ candidateM.window n) (p : ℕ) (hp : p.Prime) :
    2 * Nat.log p (k - 4 * n - 1)
      ≤ Nat.log p (16 * n) + Nat.log p (15 * n) + padicValNat p (cTerm n k) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  have hp1 : 1 < p := hp.one_lt
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: the window is `{1}`, so `m = 0` and `⌊log_p 0⌋ = 0`
    have : k = 1 := by omega
    subst this
    simp
  have hm11 : 11 * n ≤ k - 4 * n - 1 := by omega
  have hm22 : k - 4 * n - 1 ≤ 22 * n := by omega
  have hm0 : k - 4 * n - 1 ≠ 0 := by omega
  have hqm : p ^ Nat.log p (k - 4 * n - 1) ≤ k - 4 * n - 1 := Nat.pow_log_le_self p hm0
  by_cases hcase : p ^ Nat.log p (k - 4 * n - 1) ≤ 15 * n
  · -- the two `⌊log_p⌋` terms already pay; nothing about the term is used
    have e15 : Nat.log p (k - 4 * n - 1) ≤ Nat.log p (15 * n) :=
      Nat.le_log_of_pow_le hp1 hcase
    have e16 : Nat.log p (k - 4 * n - 1) ≤ Nat.log p (16 * n) :=
      Nat.le_log_of_pow_le hp1 (by omega)
    omega
  · replace hcase : 15 * n < p ^ Nat.log p (k - 4 * n - 1) := Nat.lt_of_not_le hcase
    -- `E ≥ 1`: `p^0 = 1 ≤ 15n` for `n ≥ 1`, so the top level is not the zeroth
    have hE1 : 1 ≤ Nat.log p (k - 4 * n - 1) := by
      rcases Nat.eq_zero_or_pos (Nat.log p (k - 4 * n - 1)) with h0 | h
      · rw [h0, pow_zero] at hcase; omega
      · exact h
    -- `p^{E-1} ≤ m / p ≤ 11n`, so BOTH log terms are `≥ E - 1` — the deficit is at most 2
    have hsplit : p ^ (Nat.log p (k - 4 * n - 1) - 1) * p
        = p ^ Nat.log p (k - 4 * n - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    have hprev : p ^ (Nat.log p (k - 4 * n - 1) - 1) ≤ 11 * n := by
      nlinarith [hsplit, hqm, hm22, hp1,
        Nat.one_le_two_pow (n := Nat.log p (k - 4 * n - 1) - 1)]
    have e15 : Nat.log p (k - 4 * n - 1) - 1 ≤ Nat.log p (15 * n) :=
      Nat.le_log_of_pow_le hp1 (by omega)
    have e16 : Nat.log p (k - 4 * n - 1) - 1 ≤ Nat.log p (16 * n) :=
      Nat.le_log_of_pow_le hp1 (by omega)
    have hlog1 : Nat.log p (k - 4 * n - 1) ≤ Nat.log p (k - 1) :=
      Nat.log_mono_right (by omega)
    have hlog2 : Nat.log p (k - 4 * n - 1) ≤ Nat.log p (k - 2 * n - 1) :=
      Nat.log_mono_right (by omega)
    have := two_carries n k p (Nat.log p (k - 4 * n - 1)) h1 h2 hE1 hcase hqm hlog1 hlog2
    omega

/-! ## 4. The divisibility, and the row -/

/-- **PNCLR's last obligation.**  `D(k−4n−1)² ∣ Δ 16 15 n · cTerm n k` on the window. -/
theorem harm_dvd (n k : ℕ) (hk : k ∈ candidateM.window n) :
    (D (k - 4 * n - 1)) ^ 2 ∣ Δ 16 15 n * cTerm n k := by
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  have hct : cTerm n k ≠ 0 := by
    rw [cTerm]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Nat.choose_ne_zero (by omega))
      (Nat.choose_ne_zero (by omega))) (Nat.choose_ne_zero (by omega)))
      (Nat.choose_ne_zero (by omega))
  have hlhs : (D (k - 4 * n - 1)) ^ 2 ≠ 0 := pow_ne_zero _ (D_ne_zero _)
  have hrhs : Δ 16 15 n * cTerm n k ≠ 0 := mul_ne_zero (Δ_ne_zero 16 15 n) hct
  rw [← Nat.factorization_le_iff_dvd hlhs hrhs, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hL : ((D (k - 4 * n - 1)) ^ 2).factorization p
        = 2 * Nat.log p (k - 4 * n - 1) := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Zeta2PhiT.factorization_D _ hp]
    have hR : (Δ 16 15 n * cTerm n k).factorization p
        = Nat.log p (16 * n) + Nat.log p (15 * n) + padicValNat p (cTerm n k) := by
      rw [Nat.factorization_mul (Δ_ne_zero 16 15 n) hct, Finsupp.add_apply, Zeta2Arith.Δ,
        Nat.factorization_mul (D_ne_zero _) (D_ne_zero _), Finsupp.add_apply,
        Zeta2PhiT.factorization_D _ hp, Zeta2PhiT.factorization_D _ hp,
        Nat.factorization_def _ hp]
    rw [hL, hR]
    exact vp_bound n k hk p hp
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- **Row PNCLR.**  `Δ 16 15 n · pₙ ∈ ℤ` for every `n`, with no hypotheses. -/
theorem pn_cleared_1615 : Zeta2PnCleared.PnClearedAt 16 15 :=
  Zeta2PnFunc.pn_cleared_1615_of_harm fun n =>
    Zeta2PnFunc.harm_cleared_of_dvd n fun k hk => harm_dvd n k hk

/-- **The chain's three arithmetic binders at `Δ 16 15`, unconditionally.**  This is the shape
`Zeta2ArithAssemble` consumes, and it is what row PNCLR exists to produce. -/
theorem binders_1615 :
    ∃ (Q P : ℕ → ℤ),
      (∀ n, ((Δ 16 15 n : ℕ) : ℝ) ≠ 0) ∧
      (∀ n, (Q n : ℝ) = ((Δ 16 15 n : ℕ) : ℝ) * ((candidateM.qn n : ℚ) : ℝ)) ∧
      (∀ n, (P n : ℝ) = ((Δ 16 15 n : ℕ) : ℝ) * ((candidateM.pn n : ℚ) : ℝ)) :=
  Zeta2PnCleared.binders_of_pn_cleared_1615 pn_cleared_1615

end Zeta2PnHarmDelta

#print axioms Zeta2PnHarmDelta.carry_at_le_padicValNat_choose
#print axioms Zeta2PnHarmDelta.two_carries
#print axioms Zeta2PnHarmDelta.vp_bound
#print axioms Zeta2PnHarmDelta.harm_dvd
#print axioms Zeta2PnHarmDelta.pn_cleared_1615
#print axioms Zeta2PnHarmDelta.binders_1615
