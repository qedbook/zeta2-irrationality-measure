/-
# Row PAIR-3, second half — `rep̂_injective`, and the bridge PAIR-6 consumes

`docs/future/zeta2-lean-chain.md` row PAIR-3: *two elements of `Rep̂` whose `evalRep`s agree off
finitely many points are equal*.  This is what lifts a POINTWISE identity between hat members
into an identity in `Rep̂`, where `Zeta2HatLinear`'s linearity can then push it through `Φ̂`.
Without it, PAIR-6 has a relation between rational FUNCTIONS and no way to reach the
coefficients `Φ̂` reads.

**The argument, and why it is short here.**  Clear denominators over the common
`W = ∏_{j∈S}(X + j)²`, `S` the union of the two supports: the numerator is

    clr r S = Σ_{k∈S} (B_k·(X + k) + A_k)·cof S k,     cof S k = ∏_{j ∈ S \ {k}} (X + j)²

and `clr r S` evaluates to `evalRep r t · W(t)` off the poles.  A polynomial that vanishes at
all but finitely many rationals is zero, so `clr r S = 0`; then at `t = −k₀` every term but the
diagonal is divisible by `(X + k₀)²` and therefore contributes NOTHING to the value **and
nothing to the derivative** — that is `Zeta2PF.eval_pair_zero_of_sq_dvd`, landed by PAIR-4R for
exactly this shape — so the value reads off `A_{k₀}` and, once `A_{k₀} = 0` is known, the
derivative reads off `B_{k₀}`.  Order 2 is the whole reason the derivative is needed; PHI-REP's
tale-1 twin is one order lower and can stop at the value.

**No poles in `Zeta2HatLinear`, finitely many here.**  The exceptional set is an arbitrary
`Finset ℚ`, not the pole set: a caller that knows its identity only off its own denominators
should not have to prove those are the poles of `evalRep` as well.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2HatLinear
import Zeta2PartialFractions

namespace Zeta2HatInj

open Zeta2Defs Zeta2HatRep Zeta2HatLinear Polynomial Finset

/-! ## The cleared numerator -/

/-- The cofactor at `k`: the common denominator with `(X + k)²` removed. -/
noncomputable def cof (S : Finset ℕ) (k : ℕ) : ℚ[X] :=
  ∏ j ∈ S.erase k, (X + C ((j : ℚ))) ^ 2

/-- `evalRep r · ∏_{j∈S}(X + j)²`, as a polynomial. -/
noncomputable def clr (r : Rephat) (S : Finset ℕ) : ℚ[X] :=
  ∑ k ∈ S, (C (r.1 k) * (X + C ((k : ℚ))) + C (r.2 k)) * cof S k

theorem cof_eval_ne (S : Finset ℕ) (k : ℕ) : (cof S k).eval (-(k : ℚ)) ≠ 0 := by
  rw [cof, eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
  have hne : -(k : ℚ) + (j : ℚ) ≠ 0 := by
    intro hc
    exact hjk (by exact_mod_cast (by linarith : (j : ℚ) = (k : ℚ)))
  simpa using pow_ne_zero 2 hne

/-- A term other than the diagonal one carries `(X + k₀)²`, so it kills BOTH local conditions at
`−k₀` (`Zeta2PF.eval_pair_zero_of_sq_dvd`). -/
theorem sq_dvd_cof (S : Finset ℕ) {k k₀ : ℕ} (hk₀ : k₀ ∈ S) (hne : k ≠ k₀) :
    (X - C (-(k₀ : ℚ))) ^ 2 ∣ cof S k := by
  have hmem : k₀ ∈ S.erase k := Finset.mem_erase.2 ⟨Ne.symm hne, hk₀⟩
  have h := Finset.dvd_prod_of_mem (fun j : ℕ => (X + C ((j : ℚ))) ^ 2) hmem
  simpa [cof, map_neg, sub_neg_eq_add] using h

/-- Off the poles, the cleared numerator IS `evalRep` times the common denominator. -/
theorem clr_eval (r : Rephat) (S : Finset ℕ) (hS1 : r.1.support ⊆ S) (hS2 : r.2.support ⊆ S)
    (t : ℚ) (ht : ∀ j ∈ S, t + (j : ℚ) ≠ 0) :
    (clr r S).eval t = evalRep r t * ∏ j ∈ S, (t + (j : ℚ)) ^ 2 := by
  have hev : evalRep r t
      = (∑ k ∈ S, r.1 k / (t + (k : ℚ))) + ∑ k ∈ S, r.2 k / (t + (k : ℚ)) ^ 2 := by
    rw [evalRep,
      Finsupp.sum_of_support_subset r.1 hS1 (fun k b => b / (t + (k : ℚ)))
        (fun i _ => zero_div _),
      Finsupp.sum_of_support_subset r.2 hS2 (fun k a => a / (t + (k : ℚ)) ^ 2)
        (fun i _ => zero_div _)]
  rw [hev, clr, eval_finsetSum, add_mul, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hW : ∏ j ∈ S, (t + (j : ℚ)) ^ 2
      = (t + (k : ℚ)) ^ 2 * ∏ j ∈ S.erase k, (t + (j : ℚ)) ^ 2 :=
    (Finset.mul_prod_erase S (fun j : ℕ => (t + (j : ℚ)) ^ 2) hk).symm
  have hk0 : t + (k : ℚ) ≠ 0 := ht k hk
  rw [hW, cof, eval_mul, eval_prod]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
  field_simp

/-! ## Reading the coefficients off a vanishing numerator -/

theorem clr_eval_at (r : Rephat) (S : Finset ℕ) {k₀ : ℕ} (hk₀ : k₀ ∈ S) :
    (clr r S).eval (-(k₀ : ℚ)) = r.2 k₀ * (cof S k₀).eval (-(k₀ : ℚ)) := by
  rw [clr, eval_finsetSum, Finset.sum_eq_single k₀]
  · simp
  · intro k _ hne
    exact (Zeta2PF.eval_pair_zero_of_sq_dvd
      (Dvd.dvd.mul_left (sq_dvd_cof S hk₀ hne) _)).1
  · intro hc; exact absurd hk₀ hc

theorem clr_deriv_at (r : Rephat) (S : Finset ℕ) {k₀ : ℕ} (hk₀ : k₀ ∈ S) (h2 : r.2 k₀ = 0) :
    (derivative (clr r S)).eval (-(k₀ : ℚ)) = r.1 k₀ * (cof S k₀).eval (-(k₀ : ℚ)) := by
  rw [clr, derivative_sum, eval_finsetSum, Finset.sum_eq_single k₀]
  · rw [derivative_mul, derivative_add, derivative_mul, derivative_C, derivative_add,
      derivative_X, derivative_C]
    simp [h2]
  · intro k _ hne
    exact (Zeta2PF.eval_pair_zero_of_sq_dvd
      (Dvd.dvd.mul_left (sq_dvd_cof S hk₀ hne) _)).2
  · intro hc; exact absurd hk₀ hc

/-! ## The row's statement -/

/-- A representation whose evaluation vanishes off a finite set is the zero representation. -/
theorem eq_zero_of_evalRep_vanishes (r : Rephat) (E : Finset ℚ)
    (h : ∀ t : ℚ, t ∉ E → evalRep r t = 0) : r = 0 := by
  classical
  set S : Finset ℕ := r.1.support ∪ r.2.support with hSdef
  have hS1 : r.1.support ⊆ S := Finset.subset_union_left
  have hS2 : r.2.support ⊆ S := Finset.subset_union_right
  have hzero : clr r S = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    have hfin : ((E ∪ S.image (fun j : ℕ => -(j : ℚ)) : Finset ℚ) : Set ℚ).Finite :=
      Finset.finite_toSet _
    refine Set.Infinite.mono ?_ hfin.infinite_compl
    intro t htc
    simp only [Set.mem_compl_iff, Finset.coe_union, Set.mem_union, Finset.mem_coe,
      Finset.mem_image, not_or, not_exists] at htc
    obtain ⟨hE, hpol⟩ := htc
    have hpole : ∀ j ∈ S, t + (j : ℚ) ≠ 0 := by
      intro j hj hc
      exact (hpol j) ⟨hj, by linarith⟩
    show (clr r S).IsRoot t
    rw [Polynomial.IsRoot, clr_eval r S hS1 hS2 t hpole, h t hE, zero_mul]
  have hall : ∀ k ∈ S, r.1 k = 0 ∧ r.2 k = 0 := by
    intro k hk
    have hc := cof_eval_ne S k
    have h2 : r.2 k = 0 := by
      have h0 : (0 : ℚ) = r.2 k * (cof S k).eval (-(k : ℚ)) := by
        rw [← clr_eval_at r S hk, hzero, eval_zero]
      exact (mul_eq_zero.1 h0.symm).resolve_right hc
    have h1 : r.1 k = 0 := by
      have h0 : (0 : ℚ) = r.1 k * (cof S k).eval (-(k : ℚ)) := by
        rw [← clr_deriv_at r S hk h2, hzero, derivative_zero, eval_zero]
      exact (mul_eq_zero.1 h0.symm).resolve_right hc
    exact ⟨h1, h2⟩
  have hz1 : r.1 = 0 := by
    ext k
    by_cases hk : k ∈ S
    · simpa using (hall k hk).1
    · have hns : k ∉ r.1.support := fun hcc => hk (hS1 hcc)
      simpa [Finsupp.mem_support_iff] using hns
  have hz2 : r.2 = 0 := by
    ext k
    by_cases hk : k ∈ S
    · simpa using (hall k hk).2
    · have hns : k ∉ r.2.support := fun hcc => hk (hS2 hcc)
      simpa [Finsupp.mem_support_iff] using hns
  exact Prod.ext hz1 hz2

/-- **`rep̂_injective`** — row PAIR-3.  Two representations whose evaluations agree off ANY
finite set are the same representation: the partial-fraction data of a rational function with
poles of order ≤ 2 at negative integers is unique. -/
theorem evalRep_inj (r s : Rephat) (E : Finset ℚ)
    (h : ∀ t : ℚ, t ∉ E → evalRep r t = evalRep s t) : r = s := by
  have hz : r - s = 0 :=
    eq_zero_of_evalRep_vanishes (r - s) E fun t ht => by
      rw [evalRep_sub, h t ht, sub_self]
  exact sub_eq_zero.1 hz

/-- **The bridge PAIR-6 consumes**, both halves of PAIR-3 in one statement: a linear relation
that holds between the EVALUATIONS off a finite set holds between the `Φ̂` images.  The (★)
telescoping delivers the hypothesis pointwise; the recurrence on `(hatP, hatQ)` is the
conclusion, read coordinatewise. -/
theorem Phihat_of_evalRep {ι : Type*} (N : ℕ) (s : Finset ι) (α : ι → ℚ) (rf : ι → Rephat)
    (ρ : Rephat) (E : Finset ℚ)
    (h : ∀ t : ℚ, t ∉ E → ∑ i ∈ s, α i * evalRep (rf i) t = evalRep ρ t) :
    ∑ i ∈ s, α i • Phihat N (rf i) = Phihat N ρ := by
  have hrep : ∑ i ∈ s, α i • rf i = ρ :=
    evalRep_inj _ _ E fun t ht => by rw [evalRep_sum]; exact h t ht
  rw [← Phihat_sum, hrep]

/-! ## Rung 0 — the hypothesis is not vacuous

`evalRep_inj` would be worthless if `evalRep` were constant on `Rep̂`: the theorem would be true
and say nothing.  A single order-1 coefficient at `k = 1` already separates two representations,
so the map it claims to be injective does distinguish points. -/

theorem evalRep_single_one : evalRep ((Finsupp.single 1 (1 : ℚ), 0) : Rephat) 1 = 1 / 2 := by
  show (Finsupp.single 1 (1 : ℚ)).sum _ + (0 : ℕ →₀ ℚ).sum _ = _
  rw [Finsupp.sum_single_index (by simp)]
  norm_num

theorem evalRep_nonconstant :
    evalRep ((Finsupp.single 1 (1 : ℚ), 0) : Rephat) 1 ≠ evalRep (0 : Rephat) 1 := by
  rw [evalRep_single_one, evalRep_zero]
  norm_num

end Zeta2HatInj

#print axioms Zeta2HatInj.cof_eval_ne
#print axioms Zeta2HatInj.sq_dvd_cof
#print axioms Zeta2HatInj.clr_eval
#print axioms Zeta2HatInj.clr_eval_at
#print axioms Zeta2HatInj.clr_deriv_at
#print axioms Zeta2HatInj.eq_zero_of_evalRep_vanishes
#print axioms Zeta2HatInj.evalRep_inj
#print axioms Zeta2HatInj.Phihat_of_evalRep
#print axioms Zeta2HatInj.evalRep_nonconstant
