/-
# Rows PAIR-4R and RESID — the GENERIC partial-fraction lemma both rows need

`docs/future/zeta2-lean-chain.md` rows PAIR-4R and RESID, §PAIR-4R design notes.

Mathlib has **no partial-fraction API** (census 2026-09-12: zero occurrences of
`partialFraction` / `partial_fraction` / `partialFrac` in 8487 `.lean` files).  Both rows are
the same obstacle on two members: PAIR-4R is the hat member's decomposition (simple AND double
poles), RESID is the tale-1 member's (`numPoly %ₘ denPoly`, simple poles only).  This file is
that missing lemma, built so ONE theorem serves both: `partialFractions` takes two DISJOINT
pole sets `S₁` (simple) and `S₂` (double), and RESID is its `S₂ = ∅` instance
(`partialFractions_simple`, derived below, not re-proved).

The route is elementary and needs no residue theory:

  E := N − (the claimed decomposition, cleared by the denominator) is a polynomial;
  it vanishes to order `m k` at each pole; `Σ m k = deg W > deg E`; hence `E = 0`.

The only piece specific to DOUBLE poles is `sq_dvd_of_isRoot_of_derivative` — nine lines.
That is the measurement this file exists to make: the double-pole case is not different in
kind, it is one extra criterion on the same kernel.

`partialFractions_res` (added 2026-09-13 for **PAIR-5**) is the same lemma with the residues
SOLVED FOR instead of supplied.  Its consumer is the (★) antidifference `Ŝ`, whose numerator
carries the degree-120 certificate `x̂` as an unfactored coefficient list — so unlike both
members above, `Ŝ` has NO closed form for any of its residues and cannot meet
`partialFractions`' three local conditions with a formula.  Solving them costs two
nonvanishing facts (`eval_pf1_self_ne_zero`, `eval_pf2_self_ne_zero`: a cofactor does not
vanish at its own pole) and leaves a lemma whose only hypotheses are about the POLE SETS.

`partialFractions_nodes` (added 2026-09-12 for RESID) carries the nodes through an injective
map out of an arbitrary index `Finset` — which is what every consumer has, and it is where the
tale-1 member's SIGN convention (`R_n`'s poles sit at `t = −k`, the lemma's factors are
`X − C k`) is reconciled ONCE rather than at each call site.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Lemmas
-- `field_simp` only, for `partialFractions_res`: the residues there are DIVISIONS by a cofactor
-- evaluation, so the three local conditions are field algebra rather than polynomial algebra.
import Mathlib.Tactic.FieldSimp

namespace Zeta2PF

open Polynomial Finset

set_option profiler true
set_option profiler.threshold 100

/-! ## The two local criteria -/

/-- **Order-2 vanishing.**  `(X − k)² ∣ E` from the value and the formal derivative at `k`.
This is the ONLY place the double-pole case differs from the simple one. -/
theorem sq_dvd_of_isRoot_of_derivative (E : ℚ[X]) (k : ℚ)
    (h0 : E.eval k = 0) (h1 : (derivative E).eval k = 0) : (X - C k) ^ 2 ∣ E := by
  obtain ⟨F, hF⟩ := (dvd_iff_isRoot (a := k) (p := E)).2 h0
  have hd : derivative E = F + (X - C k) * derivative F := by
    rw [hF, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  have hFk : F.eval k = 0 := by
    rw [hd] at h1
    simpa using h1
  obtain ⟨G, hG⟩ := (dvd_iff_isRoot (a := k) (p := F)).2 hFk
  exact ⟨G, by rw [hF, hG]; ring⟩

/-- The converse direction, used on every CROSS term: a factor `(X − k)²` kills both the value
and the derivative at `k`, so a summand belonging to another pole contributes nothing to either
local condition. -/
theorem eval_pair_zero_of_sq_dvd {P : ℚ[X]} {k : ℚ} (h : (X - C k) ^ 2 ∣ P) :
    P.eval k = 0 ∧ (derivative P).eval k = 0 := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨by simp, ?_⟩
  rw [derivative_mul]
  simp [derivative_pow]

/-! ## The kernel — more vanishing than degree forces zero -/

/-- **The kernel.**  A polynomial vanishing to order `m k` at each of finitely many points,
with `Σ m k` exceeding its degree, is zero.  Arbitrary multiplicities, arbitrary `Finset` — this
is the `∀n`-shaped statement; PAIR-4R and RESID differ only in what they feed it. -/
theorem eq_zero_of_local (S : Finset ℚ) (m : ℚ → ℕ) (E : ℚ[X])
    (hdvd : ∀ k ∈ S, (X - C k) ^ m k ∣ E)
    (hdeg : E.natDegree < ∑ k ∈ S, m k) : E = 0 := by
  have hcop : (S : Set ℚ).Pairwise
      (Function.onFun IsCoprime fun k : ℚ => (X - C k) ^ m k) := by
    intro x _ y _ hxy
    exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hxy).isUnit).pow
  have hdvd' : (∏ k ∈ S, (X - C k) ^ m k) ∣ E := Finset.prod_dvd_of_coprime hcop hdvd
  have hmon : ∀ k ∈ S, ((X - C k) ^ m k).Monic := fun k _ => (monic_X_sub_C k).pow (m k)
  have hdegp : (∏ k ∈ S, (X - C k) ^ m k).natDegree = ∑ k ∈ S, m k := by
    rw [natDegree_prod_of_monic _ _ hmon]
    exact Finset.sum_congr rfl fun k _ => by
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  exact eq_zero_of_dvd_of_natDegree_lt hdvd' (by rw [hdegp]; exact hdeg)

/-! ## The cofactors, written EXPLICITLY

Keeping the cofactors explicit products (rather than `W /ₘ (X − k)^m`) is what makes every
cross term a one-line `Finset.prod_eq_zero` / `Finset.dvd_prod_of_mem`. -/

open scoped Classical in
/-- The cofactor at a SIMPLE pole `k ∈ S₁`: `W / (X − k)`. -/
noncomputable def pf1 (S₁ S₂ : Finset ℚ) (k : ℚ) : ℚ[X] :=
  (∏ j ∈ S₁.erase k, (X - C j)) * ∏ j ∈ S₂, (X - C j) ^ 2

open scoped Classical in
/-- The cofactor at a DOUBLE pole `k ∈ S₂`: `W / (X − k)²`. -/
noncomputable def pf2 (S₁ S₂ : Finset ℚ) (k : ℚ) : ℚ[X] :=
  (∏ j ∈ S₁, (X - C j)) * ∏ j ∈ S₂.erase k, (X - C j) ^ 2

theorem pf1_monic (S₁ S₂ : Finset ℚ) (k : ℚ) : (pf1 S₁ S₂ k).Monic := by
  classical
  exact (monic_prod_of_monic _ _ fun j _ => monic_X_sub_C j).mul
    (monic_prod_of_monic _ _ fun j _ => (monic_X_sub_C j).pow 2)

theorem pf2_monic (S₁ S₂ : Finset ℚ) (k : ℚ) : (pf2 S₁ S₂ k).Monic := by
  classical
  exact (monic_prod_of_monic _ _ fun j _ => monic_X_sub_C j).mul
    (monic_prod_of_monic _ _ fun j _ => (monic_X_sub_C j).pow 2)

theorem natDegree_pf1 (S₁ S₂ : Finset ℚ) {k : ℚ} (hk : k ∈ S₁) :
    (pf1 S₁ S₂ k).natDegree = (S₁.card - 1) + 2 * S₂.card := by
  classical
  rw [pf1, (monic_prod_of_monic _ _ fun j _ => monic_X_sub_C j).natDegree_mul
      (monic_prod_of_monic _ _ fun j _ => (monic_X_sub_C j).pow 2),
    natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C j),
    natDegree_prod_of_monic _ _ (fun j _ => (monic_X_sub_C j).pow 2)]
  simp [Finset.card_erase_of_mem hk, Finset.sum_const, mul_comm]

theorem natDegree_pf2 (S₁ S₂ : Finset ℚ) {k : ℚ} (hk : k ∈ S₂) :
    (pf2 S₁ S₂ k).natDegree = S₁.card + 2 * (S₂.card - 1) := by
  classical
  rw [pf2, (monic_prod_of_monic _ _ fun j _ => monic_X_sub_C j).natDegree_mul
      (monic_prod_of_monic _ _ fun j _ => (monic_X_sub_C j).pow 2),
    natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C j),
    natDegree_prod_of_monic _ _ (fun j _ => (monic_X_sub_C j).pow 2)]
  simp [Finset.card_erase_of_mem hk, Finset.sum_const, mul_comm]

/-! ## Cross-term vanishing -/

theorem sq_dvd_pf1 (S₁ S₂ : Finset ℚ) (j : ℚ) {k : ℚ} (hk : k ∈ S₂) :
    (X - C k) ^ 2 ∣ pf1 S₁ S₂ j := by
  classical
  exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun j => (X - C j) ^ 2) hk) _

theorem sq_dvd_pf2 (S₁ S₂ : Finset ℚ) {j k : ℚ} (hk : k ∈ S₂) (hjk : k ≠ j) :
    (X - C k) ^ 2 ∣ pf2 S₁ S₂ j := by
  classical
  exact Dvd.dvd.mul_left
    (Finset.dvd_prod_of_mem (fun j => (X - C j) ^ 2) (Finset.mem_erase.2 ⟨hjk, hk⟩)) _

theorem eval_pf1_cross (S₁ S₂ : Finset ℚ) {j k : ℚ} (hk : k ∈ S₁) (hjk : k ≠ j) :
    (pf1 S₁ S₂ j).eval k = 0 := by
  classical
  rw [pf1, eval_mul, eval_prod]
  rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hjk, hk⟩) (by simp), zero_mul]

theorem eval_pf2_cross (S₁ S₂ : Finset ℚ) (j : ℚ) {k : ℚ} (hk : k ∈ S₁) :
    (pf2 S₁ S₂ j).eval k = 0 := by
  classical
  rw [pf2, eval_mul, eval_prod]
  rw [Finset.prod_eq_zero hk (by simp), zero_mul]

/-! ## The theorem -/

open scoped Classical in
/-- **The generic partial-fraction identity, in cleared (polynomial) form.**

`S₁` the simple poles, `S₂` the double ones, disjoint.  `b k` is the order-1 coefficient at
every pole and `a k` the order-2 coefficient at the double ones.  The hypotheses are exactly
the LOCAL residue conditions — one evaluation per simple pole, one evaluation plus one
derivative per double pole — and the degree bound.

This is the shape both consumers produce: PAIR-4R supplies the hat member's `hatA` / `hatLam` /
`hatBlo` / `hatBhi` as `a` / `b`, RESID supplies `ck` with `S₂ = ∅`. -/
theorem partialFractions (S₁ S₂ : Finset ℚ) (hdisj : Disjoint S₁ S₂)
    (N : ℚ[X]) (b a : ℚ → ℚ)
    (hdeg : N.natDegree < S₁.card + 2 * S₂.card)
    (h₁ : ∀ k ∈ S₁, N.eval k = b k * (pf1 S₁ S₂ k).eval k)
    (h₂ : ∀ k ∈ S₂, N.eval k = a k * (pf2 S₁ S₂ k).eval k)
    (h₃ : ∀ k ∈ S₂, (derivative N).eval k
        = a k * (derivative (pf2 S₁ S₂ k)).eval k + b k * (pf2 S₁ S₂ k).eval k) :
    N = (∑ k ∈ S₁, C (b k) * pf1 S₁ S₂ k)
      + ∑ k ∈ S₂, (C (b k) * ((X - C k) * pf2 S₁ S₂ k) + C (a k) * pf2 S₁ S₂ k) := by
  classical
  set R := (∑ k ∈ S₁, C (b k) * pf1 S₁ S₂ k)
      + ∑ k ∈ S₂, (C (b k) * ((X - C k) * pf2 S₁ S₂ k) + C (a k) * pf2 S₁ S₂ k) with hRdef
  set D := S₁.card + 2 * S₂.card with hD
  -- STEP 1: the degree of `R`.
  have hcard1 : ∀ k ∈ S₁, 1 ≤ S₁.card := fun k hk => Finset.card_pos.2 ⟨k, hk⟩
  have hcard2 : ∀ k ∈ S₂, 1 ≤ S₂.card := fun k hk => Finset.card_pos.2 ⟨k, hk⟩
  have hdegR : R.natDegree < D := by
    have hb1 : ∀ k ∈ S₁, (C (b k) * pf1 S₁ S₂ k).natDegree ≤ D - 1 := by
      intro k hk
      refine le_trans (natDegree_C_mul_le _ _) ?_
      rw [natDegree_pf1 S₁ S₂ hk]
      have := hcard1 k hk
      omega
    have hb2 : ∀ k ∈ S₂,
        (C (b k) * ((X - C k) * pf2 S₁ S₂ k) + C (a k) * pf2 S₁ S₂ k).natDegree ≤ D - 1 := by
      intro k hk
      have h2 := hcard2 k hk
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (natDegree_C_mul_le _ _) ?_
        refine le_trans (natDegree_mul_le) ?_
        rw [natDegree_X_sub_C, natDegree_pf2 S₁ S₂ hk]
        omega
      · refine le_trans (natDegree_C_mul_le _ _) ?_
        rw [natDegree_pf2 S₁ S₂ hk]
        omega
    have hs1 : (∑ k ∈ S₁, C (b k) * pf1 S₁ S₂ k).natDegree ≤ D - 1 :=
      natDegree_sum_le_of_forall_le _ _ hb1
    have hs2 : (∑ k ∈ S₂,
        (C (b k) * ((X - C k) * pf2 S₁ S₂ k) + C (a k) * pf2 S₁ S₂ k)).natDegree ≤ D - 1 :=
      natDegree_sum_le_of_forall_le _ _ hb2
    have : R.natDegree ≤ D - 1 := le_trans (natDegree_add_le _ _) (max_le hs1 hs2)
    have hD1 : 1 ≤ D := by
      rcases Finset.eq_empty_or_nonempty S₁ with h | ⟨k, hk⟩
      · rcases Finset.eq_empty_or_nonempty S₂ with h' | ⟨k, hk⟩
        · exfalso; rw [hD, h, h'] at hdeg; simp at hdeg
        · have := hcard2 k hk; omega
      · have := hcard1 k hk; omega
    omega
  -- STEP 2: the local conditions.
  have hEdeg : (N - R).natDegree < D :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hdeg hdegR)
  set m : ℚ → ℕ := fun k => if k ∈ S₂ then 2 else 1 with hm
  have hsum : ∑ k ∈ S₁ ∪ S₂, m k = D := by
    rw [Finset.sum_union hdisj]
    have e1 : ∑ k ∈ S₁, m k = S₁.card := by
      have h1 : ∀ k ∈ S₁, m k = 1 := fun k hk => by
        rw [hm]; simp [Finset.disjoint_left.1 hdisj hk]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
    have e2 : ∑ k ∈ S₂, m k = 2 * S₂.card := by
      have h2 : ∀ k ∈ S₂, m k = 2 := fun k hk => by rw [hm]; simp [hk]
      rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [e1, e2, hD]
  refine sub_eq_zero.1 (eq_zero_of_local (S₁ ∪ S₂) m (N - R) ?_ (by rw [hsum]; exact hEdeg))
  intro k hk
  rcases Finset.mem_union.1 hk with hk1 | hk2
  · -- SIMPLE pole
    have hnot : k ∉ S₂ := Finset.disjoint_left.1 hdisj hk1
    have hmk : m k = 1 := by rw [hm]; simp [hnot]
    rw [hmk, pow_one, dvd_iff_isRoot]
    show (N - R).eval k = 0
    have hRk : R.eval k = b k * (pf1 S₁ S₂ k).eval k := by
      rw [hRdef, eval_add, eval_finsetSum, eval_finsetSum]
      have t1 : ∑ j ∈ S₁, (C (b j) * pf1 S₁ S₂ j).eval k = b k * (pf1 S₁ S₂ k).eval k := by
        rw [Finset.sum_eq_single_of_mem k hk1]
        · simp
        · intro j _ hjk
          rw [eval_mul, eval_pf1_cross S₁ S₂ hk1 (Ne.symm hjk), mul_zero]
      have t2 : ∑ j ∈ S₂,
          (C (b j) * ((X - C j) * pf2 S₁ S₂ j) + C (a j) * pf2 S₁ S₂ j).eval k = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [eval_add, eval_mul, eval_mul, eval_mul, eval_pf2_cross S₁ S₂ j hk1]
        ring
      rw [t1, t2, add_zero]
    rw [eval_sub, hRk, h₁ k hk1, sub_self]
  · -- DOUBLE pole
    have hmk : m k = 2 := by rw [hm]; simp [hk2]
    rw [hmk]
    refine sq_dvd_of_isRoot_of_derivative _ _ ?_ ?_
    · have hRk : R.eval k = a k * (pf2 S₁ S₂ k).eval k := by
        rw [hRdef, eval_add, eval_finsetSum, eval_finsetSum]
        have t1 : ∑ j ∈ S₁, (C (b j) * pf1 S₁ S₂ j).eval k = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [eval_mul, (eval_pair_zero_of_sq_dvd (sq_dvd_pf1 S₁ S₂ j hk2)).1, mul_zero]
        have t2 : ∑ j ∈ S₂,
            (C (b j) * ((X - C j) * pf2 S₁ S₂ j) + C (a j) * pf2 S₁ S₂ j).eval k
              = a k * (pf2 S₁ S₂ k).eval k := by
          rw [Finset.sum_eq_single_of_mem k hk2]
          · simp
          · intro j _ hjk
            rw [eval_add, eval_mul, eval_mul, eval_mul,
              (eval_pair_zero_of_sq_dvd (sq_dvd_pf2 S₁ S₂ hk2 (Ne.symm hjk))).1]
            ring
        rw [t1, t2, zero_add]
      rw [eval_sub, hRk, h₂ k hk2, sub_self]
    · have hRk : (derivative R).eval k
          = a k * (derivative (pf2 S₁ S₂ k)).eval k + b k * (pf2 S₁ S₂ k).eval k := by
        rw [hRdef, derivative_add, derivative_sum, derivative_sum, eval_add,
          eval_finsetSum, eval_finsetSum]
        have t1 : ∑ j ∈ S₁, (derivative (C (b j) * pf1 S₁ S₂ j)).eval k = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [derivative_C_mul, eval_mul,
            (eval_pair_zero_of_sq_dvd (sq_dvd_pf1 S₁ S₂ j hk2)).2, mul_zero]
        have t2 : ∑ j ∈ S₂, (derivative
            (C (b j) * ((X - C j) * pf2 S₁ S₂ j) + C (a j) * pf2 S₁ S₂ j)).eval k
              = a k * (derivative (pf2 S₁ S₂ k)).eval k + b k * (pf2 S₁ S₂ k).eval k := by
          rw [Finset.sum_eq_single_of_mem k hk2]
          · rw [derivative_add, derivative_C_mul, derivative_C_mul, derivative_mul,
              derivative_sub, derivative_X, derivative_C]
            simp
            ring
          · intro j _ hjk
            have hp := eval_pair_zero_of_sq_dvd (sq_dvd_pf2 S₁ S₂ hk2 (Ne.symm hjk))
            simp [derivative_add, derivative_mul, hp.1, hp.2]
        rw [t1, t2, zero_add]
      rw [derivative_sub, eval_sub, hRk, h₃ k hk2, sub_self]

/-! ## The residues SOLVED FOR — the consumer that has no closed form for them

`partialFractions` takes `b` and `a` as GIVEN and asks for the three local conditions.  Both
landed consumers can do that: the hat member (PAIR-4R) and the tale-1 member (RESID) have
residues in closed form — factorial ratios and harmonic differences — because their numerators
are products of linear forms and every local evaluation telescopes.

**Row PAIR-5's `Ŝ` cannot, and that is a property of the object rather than of the effort
spent.**  The (★) antidifference is `b̂(·−1) · x̂ · û`, and `x̂` is the degree-120 certificate the
solve emits as a COEFFICIENT LIST: it carries no factorisation, so `x̂(k)` has no product form
and no residue of `Ŝ` has a closed form at any pole.  A consumer in that position needs the
residues DEFINED BY the local conditions instead of supplied to them, which costs exactly the
two nonvanishing facts below — a cofactor does not vanish at its OWN pole — and buys a form of
`partialFractions` carrying no residue hypothesis at all, only the degree bound.

Recorded because it was priced as a risk and is not one: PAIR-5's design notes named the
unfactored `x̂` as *"what is genuinely unpriced"* about inheriting PAIR-4R's route.  It costs
`eval_pf1_self_ne_zero`, `eval_pf2_self_ne_zero` and `partialFractions_res`. -/

theorem eval_pf1_self_ne_zero (S₁ S₂ : Finset ℚ) (hdisj : Disjoint S₁ S₂) {k : ℚ}
    (hk : k ∈ S₁) : (pf1 S₁ S₂ k).eval k ≠ 0 := by
  classical
  rw [pf1, eval_mul, eval_prod, eval_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j hj => ?_)
    (Finset.prod_ne_zero_iff.2 fun j hj => ?_)
  · simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase hj))
  · have hkj : k ≠ j := by
      intro h
      subst h
      exact Finset.disjoint_left.1 hdisj hk hj
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    exact pow_ne_zero _ (sub_ne_zero.2 hkj)

theorem eval_pf2_self_ne_zero (S₁ S₂ : Finset ℚ) (hdisj : Disjoint S₁ S₂) {k : ℚ}
    (hk : k ∈ S₂) : (pf2 S₁ S₂ k).eval k ≠ 0 := by
  classical
  rw [pf2, eval_mul, eval_prod, eval_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j hj => ?_)
    (Finset.prod_ne_zero_iff.2 fun j hj => ?_)
  · have hkj : k ≠ j := by
      intro h
      subst h
      exact Finset.disjoint_right.1 hdisj hk hj
    simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.2 hkj
  · simp only [eval_pow, eval_sub, eval_X, eval_C]
    exact pow_ne_zero _ (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase hj)))

open scoped Classical in
/-- The order-2 coefficient at a double pole, read off its own local condition. -/
noncomputable def resA (S₁ S₂ : Finset ℚ) (N : ℚ[X]) (k : ℚ) : ℚ :=
  N.eval k / (pf2 S₁ S₂ k).eval k

open scoped Classical in
/-- The order-1 coefficient at EITHER kind of pole, read off its own local condition — the
derivative one at a double pole, the value one at a simple pole.  The `if` is on the pole set
and not on the shape of `N`, so a caller never has to case-split. -/
noncomputable def resB (S₁ S₂ : Finset ℚ) (N : ℚ[X]) (k : ℚ) : ℚ :=
  if k ∈ S₂ then
    ((derivative N).eval k - resA S₁ S₂ N k * (derivative (pf2 S₁ S₂ k)).eval k)
      / (pf2 S₁ S₂ k).eval k
  else N.eval k / (pf1 S₁ S₂ k).eval k

/-- `resB` at a SIMPLE pole, with the `if` discharged — so no caller ever writes one. -/
theorem resB_simple (S₁ S₂ : Finset ℚ) (N : ℚ[X]) {k : ℚ} (hk : k ∉ S₂) :
    resB S₁ S₂ N k = N.eval k / (pf1 S₁ S₂ k).eval k := by
  classical
  simp [resB, hk]

/-- `resB` at a DOUBLE pole, likewise. -/
theorem resB_double (S₁ S₂ : Finset ℚ) (N : ℚ[X]) {k : ℚ} (hk : k ∈ S₂) :
    resB S₁ S₂ N k
      = ((derivative N).eval k - resA S₁ S₂ N k * (derivative (pf2 S₁ S₂ k)).eval k)
        / (pf2 S₁ S₂ k).eval k := by
  classical
  simp [resB, hk]

/-- **`partialFractions` with the residues solved for.**  The three local conditions are gone;
what is left is the degree bound and disjointness, both of which are statements about the POLE
SETS alone.  For a consumer whose residues have no closed form this is the whole difference
between "inherits PAIR-4R's route" and "cannot use it". -/
theorem partialFractions_res (S₁ S₂ : Finset ℚ) (hdisj : Disjoint S₁ S₂) (N : ℚ[X])
    (hdeg : N.natDegree < S₁.card + 2 * S₂.card) :
    N = (∑ k ∈ S₁, C (resB S₁ S₂ N k) * pf1 S₁ S₂ k)
      + ∑ k ∈ S₂, (C (resB S₁ S₂ N k) * ((X - C k) * pf2 S₁ S₂ k)
          + C (resA S₁ S₂ N k) * pf2 S₁ S₂ k) := by
  classical
  refine partialFractions S₁ S₂ hdisj N (resB S₁ S₂ N) (resA S₁ S₂ N) hdeg ?_ ?_ ?_
  · intro k hk
    have hne := eval_pf1_self_ne_zero S₁ S₂ hdisj hk
    rw [resB_simple S₁ S₂ N (Finset.disjoint_left.1 hdisj hk)]
    field_simp
  · intro k hk
    have hne := eval_pf2_self_ne_zero S₁ S₂ hdisj hk
    rw [resA]
    field_simp
  · intro k hk
    have hne := eval_pf2_self_ne_zero S₁ S₂ hdisj hk
    rw [resB_double S₁ S₂ N hk]
    field_simp
    ring

/-! ## The TOP coefficient of the cleared identity — the residue-at-∞ statement, with no analysis

Row **PAIR-4L** ("the `ln 2` coordinate vanishes") is `Σ_k b_k = 0`, which the PAIR design notes
justify as *the residue at ∞ of a rational function with `deg num ≤ deg den − 2`*.  Read off the
CLEARED identity above it is one `Polynomial.coeff`, and no residue theory is involved at all:

* every `pf1 k` (`k ∈ S₁`) is monic of degree `|S₁| + 2|S₂| − 1` — the denominator with one
  simple factor removed;
* every `(X − k)·pf2 k` (`k ∈ S₂`) is monic of the SAME degree — the denominator with one of a
  double factor's two copies removed;
* every `pf2 k` is one degree lower, so the order-2 coefficients `a k` do not appear at all.

So the coefficient of `X^{|S₁|+2|S₂|−1}` on the right is exactly `Σ_{S₁} b + Σ_{S₂} b`.  On the
LEFT it is `0` precisely when `N` misses the top degree by **two** rather than by the one
`partialFractions` itself needs — hence the sharper `hdeg` here, which is a genuinely stronger
hypothesis and not a restatement.  At the hat member the margin is exactly two (`22n` against
`|S₁| + 2|S₂| = 22n + 2`), which is why PAIR-4L is a corollary of PAIR-4R rather than a row. -/

theorem sum_order1_eq_zero (S₁ S₂ : Finset ℚ) (N : ℚ[X]) (b a : ℚ → ℚ)
    (hdeg : N.natDegree + 1 < S₁.card + 2 * S₂.card)
    (heq : N = (∑ k ∈ S₁, C (b k) * pf1 S₁ S₂ k)
      + ∑ k ∈ S₂, (C (b k) * ((X - C k) * pf2 S₁ S₂ k) + C (a k) * pf2 S₁ S₂ k)) :
    (∑ k ∈ S₁, b k) + ∑ k ∈ S₂, b k = 0 := by
  classical
  have e1 : ∀ k ∈ S₁, (C (b k) * pf1 S₁ S₂ k).coeff (S₁.card + 2 * S₂.card - 1) = b k := by
    intro k hk
    have hc : 1 ≤ S₁.card := Finset.card_pos.2 ⟨k, hk⟩
    have hd : (pf1 S₁ S₂ k).natDegree = S₁.card + 2 * S₂.card - 1 := by
      rw [natDegree_pf1 S₁ S₂ hk]; omega
    have hlc : (pf1 S₁ S₂ k).coeff (S₁.card + 2 * S₂.card - 1) = 1 := by
      have h := (pf1_monic S₁ S₂ k).coeff_natDegree
      rwa [hd] at h
    rw [coeff_C_mul, hlc, mul_one]
  have e2 : ∀ k ∈ S₂,
      (C (b k) * ((X - C k) * pf2 S₁ S₂ k) + C (a k) * pf2 S₁ S₂ k).coeff
        (S₁.card + 2 * S₂.card - 1) = b k := by
    intro k hk
    have hc : 1 ≤ S₂.card := Finset.card_pos.2 ⟨k, hk⟩
    have hm : ((X - C k) * pf2 S₁ S₂ k).Monic := (monic_X_sub_C k).mul (pf2_monic S₁ S₂ k)
    have hd : ((X - C k) * pf2 S₁ S₂ k).natDegree = S₁.card + 2 * S₂.card - 1 := by
      rw [(monic_X_sub_C k).natDegree_mul (pf2_monic S₁ S₂ k), natDegree_X_sub_C,
        natDegree_pf2 S₁ S₂ hk]
      omega
    have hA : ((X - C k) * pf2 S₁ S₂ k).coeff (S₁.card + 2 * S₂.card - 1) = 1 := by
      have h := hm.coeff_natDegree
      rwa [hd] at h
    have hB : (pf2 S₁ S₂ k).coeff (S₁.card + 2 * S₂.card - 1) = 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      rw [natDegree_pf2 S₁ S₂ hk]; omega
    rw [coeff_add, coeff_C_mul, coeff_C_mul, hA, hB, mul_one, mul_zero, add_zero]
  have s1 : ∑ k ∈ S₁, (C (b k) * pf1 S₁ S₂ k).coeff (S₁.card + 2 * S₂.card - 1)
      = ∑ k ∈ S₁, b k := Finset.sum_congr rfl e1
  have s2 : ∑ k ∈ S₂, (C (b k) * ((X - C k) * pf2 S₁ S₂ k)
        + C (a k) * pf2 S₁ S₂ k).coeff (S₁.card + 2 * S₂.card - 1)
      = ∑ k ∈ S₂, b k := Finset.sum_congr rfl e2
  have hN : N.coeff (S₁.card + 2 * S₂.card - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  rw [heq, coeff_add, finsetSum_coeff, finsetSum_coeff, s1, s2] at hN
  exact hN

/-! ## RESID's instance: simple poles only, `S₂ = ∅`

Derived, not re-proved — the measurement this file is for is that the two rows are one lemma. -/

open scoped Classical in
theorem partialFractions_simple (S : Finset ℚ) (N : ℚ[X]) (c : ℚ → ℚ)
    (hdeg : N.natDegree < S.card)
    (heval : ∀ k ∈ S, N.eval k = c k * ∏ j ∈ S.erase k, (k - j)) :
    N = ∑ k ∈ S, C (c k) * ∏ j ∈ S.erase k, (X - C j) := by
  classical
  have hpf1 : ∀ k : ℚ, pf1 S ∅ k = ∏ j ∈ S.erase k, (X - C j) := by
    intro k; rw [pf1]; simp
  have key := partialFractions S ∅ (by simp) N c c (by simpa using hdeg)
    (fun k hk => by
      rw [hpf1, eval_prod]
      simpa using heval k hk)
    (fun k hk => absurd hk (by simp))
    (fun k hk => absurd hk (by simp))
  rw [key]
  simp only [Finset.sum_empty, add_zero]
  exact Finset.sum_congr rfl fun k _ => by rw [hpf1]

/-! ## The REINDEXED form — nodes carried by an arbitrary index `Finset`

`partialFractions_simple` states the nodes as a `Finset ℚ`.  Every consumer instead has a
`Finset ι` of INDICES (`Zeta2Defs.Member.window` is a `Finset ℕ`) and a node map `v` — and for
the tale-1 member that map carries a SIGN, `j ↦ −j`, because the poles of `R_n` sit at `t = −k`
while the lemma's factors are `X − C k`.  Reconciling that at each call site is exactly the
"composes on paper" trap (LEAN.md §3), so it is done ONCE, here.

The left inverse `w` is passed rather than derived: every caller has one in closed form
(`fun x => (−x).num.toNat` for the `j ↦ −j` map), and asking for it keeps this lemma free of
`Function.invFun`'s `Nonempty` plumbing and of a `Classical.choice` on the caller's side. -/

open scoped Classical in
theorem partialFractions_nodes {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (v : ι → ℚ) (w : ℚ → ι) (hw : ∀ k ∈ T, w (v k) = k)
    (N : ℚ[X]) (c : ι → ℚ)
    (hdeg : N.natDegree < T.card)
    (heval : ∀ k ∈ T, N.eval (v k) = c k * ∏ j ∈ T.erase k, (v k - v j)) :
    N = ∑ k ∈ T, C (c k) * ∏ j ∈ T.erase k, (X - C (v j)) := by
  classical
  have hinj : ∀ x ∈ T, ∀ y ∈ T, v x = v y → x = y := by
    intro x hx y hy hxy
    rw [← hw x hx, ← hw y hy, hxy]
  have hcard : (T.image v).card = T.card :=
    Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)
  have herase : ∀ k ∈ T, (T.image v).erase (v k) = (T.erase k).image v := by
    intro k hk
    ext x
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hx, j, hj, rfl⟩
      exact ⟨j, ⟨fun h => hx (by rw [h]), hj⟩, rfl⟩
    · rintro ⟨j, ⟨hjk, hjT⟩, rfl⟩
      exact ⟨fun h => hjk (hinj j hjT k hk h), j, hjT, rfl⟩
  have hinj' : ∀ k : ι, ∀ x ∈ T.erase k, ∀ y ∈ T.erase k, v x = v y → x = y :=
    fun k x hx y hy h =>
      hinj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) h
  have hev : ∀ x ∈ T.image v, N.eval x
      = (fun z => c (w z)) x * ∏ j ∈ (T.image v).erase x, (x - j) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    show N.eval (v k) = c (w (v k)) * ∏ j ∈ (T.image v).erase (v k), (v k - j)
    rw [hw k hk, herase k hk, Finset.prod_image (hinj' k)]
    exact heval k hk
  have key := partialFractions_simple (T.image v) N (fun z => c (w z))
    (by rw [hcard]; exact hdeg) hev
  rw [key, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun k hk => ?_
  show C (c (w (v k))) * ∏ x ∈ (T.image v).erase (v k), (X - C x)
      = C (c k) * ∏ j ∈ T.erase k, (X - C (v j))
  rw [hw k hk, herase k hk, Finset.prod_image (hinj' k)]

/-! ## Rung-0: a worked instance whose CONCLUSION is checkable

`partialFractions` is green; that is not yet evidence it says anything, because a theorem with
unsatisfiable hypotheses is also green (PHILOSOPHY §6: a green that cannot be made red attests
nothing).  So here it is DISCHARGED on the smallest mixed instance — one simple pole at `1`, one
double pole at `2`, `N = X²` — and the identity it delivers is one `norm_num` can refute.  The
residue data is `b 1 = 1`, `a 2 = 4`, `b 2 = 0`, read off the local conditions; the conclusion
`X² = (X−2)² + 4(X−1)` is TRUE, and a perturbed residue makes this file red rather than
producing a different theorem (falsifier arm: `a 2 := 5`, recorded in the design notes). -/

theorem pf1_worked : pf1 {(1:ℚ)} {(2:ℚ)} 1 = (X - C (2:ℚ)) ^ 2 := by
  classical
  simp [pf1]

theorem pf2_worked : pf2 {(1:ℚ)} {(2:ℚ)} 2 = X - C (1:ℚ) := by
  classical
  simp [pf2]

theorem worked_instance :
    (X : ℚ[X]) ^ 2 = (X - C (2:ℚ)) ^ 2 + C (4:ℚ) * (X - C (1:ℚ)) := by
  classical
  have key := partialFractions {(1:ℚ)} {(2:ℚ)} (by simp) ((X : ℚ[X]) ^ 2)
      (fun k => if k = (1:ℚ) then 1 else 0) (fun _ => (4:ℚ))
      (by simp)
      (by
        intro k hk
        simp only [Finset.mem_singleton] at hk
        subst hk
        rw [pf1_worked]
        norm_num)
      (by
        intro k hk
        simp only [Finset.mem_singleton] at hk
        subst hk
        rw [pf2_worked]
        norm_num)
      (by
        intro k hk
        simp only [Finset.mem_singleton] at hk
        subst hk
        rw [pf2_worked]
        norm_num)
  simp only [Finset.sum_singleton, pf1_worked, pf2_worked] at key
  rw [key]
  norm_num

/-! ### The same instance for `sum_order1_eq_zero`, where the margin IS two

`worked_instance` above has `deg N = 2` against `|S₁| + 2|S₂| = 3` — margin ONE, so the order-1
sum there is `1 + 0 = 1`, NOT zero, and `sum_order1_eq_zero` correctly does not apply to it.
Dropping to `N = X` restores the margin to two, and then the residues are `b 1 = 1`, `a 2 = 2`,
`b 2 = −1`: `X = (X−2)² − (X−2)(X−1) + 2(X−1)`.  So this instance is what says the new lemma's
hypotheses are jointly SATISFIABLE (a theorem with unsatisfiable hypotheses is also green), and
`b 2` is pinned by the derivative condition — typing `0` there reds the `partialFractions` call
rather than delivering a different theorem. -/

/-- The order-1 residues of `X / ((X−1)(X−2)²)`, named so the rung-0 statements carry the
actual numbers rather than an anonymous `fun`. -/
def bWorked : ℚ → ℚ := fun k => if k = (1 : ℚ) then 1 else -1

theorem worked_order1_key :
    (X : ℚ[X]) = (∑ k ∈ ({1} : Finset ℚ), C (bWorked k) * pf1 {(1:ℚ)} {(2:ℚ)} k)
      + ∑ k ∈ ({2} : Finset ℚ), (C (bWorked k) * ((X - C k) * pf2 {(1:ℚ)} {(2:ℚ)} k)
        + C (2:ℚ) * pf2 {(1:ℚ)} {(2:ℚ)} k) := by
  classical
  refine partialFractions {(1:ℚ)} {(2:ℚ)} (by simp) X bWorked (fun _ => (2:ℚ)) (by simp)
    ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_singleton] at hk
    subst hk
    rw [pf1_worked]
    norm_num [bWorked]
  · intro k hk
    simp only [Finset.mem_singleton] at hk
    subst hk
    rw [pf2_worked]
    norm_num
  · intro k hk
    simp only [Finset.mem_singleton] at hk
    subst hk
    rw [pf2_worked]
    norm_num [bWorked]

/-- **Non-vacuity for `sum_order1_eq_zero`**: it fires at that instance, and the number it
delivers is the checkable `1 + (−1) = 0`. -/
theorem worked_order1_sum : bWorked 1 + bWorked 2 = 0 := by
  have h := sum_order1_eq_zero {(1:ℚ)} {(2:ℚ)} X bWorked (fun _ => (2:ℚ)) (by simp)
    worked_order1_key
  simpa using h

/-! ### …and the same instance with NOTHING supplied

`partialFractions_res` is green, which is not yet evidence that the residues it solves for are
the right ones: a wrong `resA`/`resB` would still be a theorem about whatever they are.  So they
are pinned against the numbers this file already carries by hand — `bWorked` and the `2` of
`worked_order1_key` — and then the hypothesis-free route is run through `sum_order1_eq_zero` to
deliver a rational a `norm_num` can refute.  Perturbing either literal below reds this file. -/

theorem res_worked :
    resB {(1:ℚ)} {(2:ℚ)} X 1 = bWorked 1 ∧ resB {(1:ℚ)} {(2:ℚ)} X 2 = bWorked 2
      ∧ resA {(1:ℚ)} {(2:ℚ)} X 2 = 2 := by
  classical
  have hA : resA {(1:ℚ)} {(2:ℚ)} X 2 = 2 := by
    rw [resA, pf2_worked]
    norm_num
  refine ⟨?_, ?_, hA⟩
  · rw [resB_simple _ _ _ (by norm_num : (1:ℚ) ∉ ({2} : Finset ℚ)), pf1_worked]
    norm_num [bWorked]
  · rw [resB_double _ _ _ (by norm_num : (2:ℚ) ∈ ({2} : Finset ℚ)), hA, pf2_worked]
    norm_num [bWorked]

/-- **Non-vacuity for `partialFractions_res`**: the degree bound alone delivers the identity,
and the order-1 sum it then hands `sum_order1_eq_zero` is the checkable `1 + (−1) = 0`. -/
theorem worked_res_order1_sum :
    resB {(1:ℚ)} {(2:ℚ)} X 1 + resB {(1:ℚ)} {(2:ℚ)} X 2 = 0 := by
  classical
  have h := sum_order1_eq_zero {(1:ℚ)} {(2:ℚ)} X (resB {(1:ℚ)} {(2:ℚ)} X)
    (resA {(1:ℚ)} {(2:ℚ)} X) (by simp)
    (partialFractions_res {(1:ℚ)} {(2:ℚ)} (by simp) X (by simp))
  simpa using h

end Zeta2PF

#print axioms Zeta2PF.sq_dvd_of_isRoot_of_derivative
#print axioms Zeta2PF.eval_pair_zero_of_sq_dvd
#print axioms Zeta2PF.eq_zero_of_local
#print axioms Zeta2PF.partialFractions
#print axioms Zeta2PF.eval_pf1_self_ne_zero
#print axioms Zeta2PF.eval_pf2_self_ne_zero
#print axioms Zeta2PF.partialFractions_res
#print axioms Zeta2PF.res_worked
#print axioms Zeta2PF.worked_res_order1_sum
#print axioms Zeta2PF.sum_order1_eq_zero
#print axioms Zeta2PF.worked_order1_key
#print axioms Zeta2PF.worked_order1_sum
#print axioms Zeta2PF.partialFractions_simple
#print axioms Zeta2PF.partialFractions_nodes
#print axioms Zeta2PF.worked_instance
