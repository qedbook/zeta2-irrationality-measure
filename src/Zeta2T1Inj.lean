/-
# Row PHI-REP — `Φ` linear on tale-1's `Rep`, and `rep_injective`

`docs/future/zeta2-lean-chain.md` row PHI-REP: *`Φ` on the representation, ℚ×ℚ-valued, linear,
with `Φ_add`, `Φ_smul`; `rep_injective`; and `rec_of_telescoping_of_linear` RESTATED at
`Φ : Rep → ℚ × ℚ`.*

**Three of the row's four deliverables were already on `main` when this file was written, and
one of them is the whole of its definitional half.**  `Zeta2T1Shift` (row PHI-BDY, landed
2026-09-14) declares `Rep`, `evalRep`, `Φ`, `shiftRep`, `repDelta` *exactly as this row states
them*, and proves `Φ_sub` and `evalRep_shiftRep`.  So this file adds the three pieces that were
missing — `Φ`'s ADD and SMUL halves, `rep_injective`, and the restatement — and states nothing
twice.

## What `rep_injective` costs here, and why the polynomial part is not the obstacle it reads as

The row's cell says tale-1's `Rep` carries a POLYNOMIAL part that `Rep̂` has not, *"so the
clearing here has a numerator of degree ≥ the denominator and `clr`'s shape must gain a
polynomial summand before `Polynomial.eq_zero_of_infinite_isRoot` can be applied"*.  The first
half is true and the summand is here; the second half — read as an obstacle — is **measurably
backwards**.  Clearing over `W = ∏_{j∈S}(X + j)` gives

    clr (P, c) S = P·W + Σ_{k∈S} C(c_k)·cof S k,      cof S k = ∏_{j ∈ S \ {k}} (X + j)

and the extra summand `P·W` **vanishes at every pole**, because `W` does.  So the residue
extraction never sees it: at `t = −k₀` the value reads off `c_{k₀}` exactly as in the hat, and
`P` is then recovered by ONE cancellation in the domain `ℚ[X]` — `clr = P·W = 0` with `W ≠ 0`
(a product of monics).  The polynomial part costs two lemmas, `denom_monic` and `denom_eval_at`,
and buys back the entire order-2 apparatus: `Zeta2HatInj`'s `clr_deriv_at`, its
`Zeta2PF.eval_pair_zero_of_sq_dvd` dependency and its `sq_dvd_cof` are all DELETED here, because
tale-1's poles are simple (`Zeta2T1Shift`'s header; `../zeta2_star_b1/t1_bdy_probe.py` §D
measures it at both landed members).  **This row is strictly cheaper than its order-2 twin, not
dearer.**

`Polynomial.modByMonic` is named nowhere in this file and is not owed by it.  The row's cell
imports that need from PHI-BDY's census, where it is real — `Zeta2HatRepOf.evalRep_repOf`
presumes a proper fraction, so the CONSTRUCTION of `repS n` must split off the improper part.
Injectivity has no such presumption: `clr_eval` is stated for an arbitrary `(P, c)`.

**PAIR-5's structural lesson holds verbatim and is why this file is short.** `clr_eval_at` SOLVES
for `c_{k₀}`; it never argues that a pole is uncancelled.  A key whose coefficient the numerator
kills simply gets `0`, unproved and unmentioned, and `S := r.2.support` is the WRITTEN support,
not a computed pole set.

## Reuse, and the one thing restated rather than imported

`eq_zero_of_evalRep_vanishes` and `evalRep_inj` are `Zeta2HatInj`'s skeleton instantiated at pole
order 1 (PHILOSOPHY §5a: build it from the landed component, do not re-derive it); the exceptional
set stays an arbitrary `Finset ℚ` for the same reason it is arbitrary there — a caller that knows
its identity only off its own denominators should not have to prove those are the poles as well.
`Phi_of_evalRep` is `Zeta2HatInj.Phihat_of_evalRep` at `Φ`.

`sum_smul` below is `Zeta2HatLinear.sum_smul` **restated, not imported**, and that is a deliberate
four-line duplication: importing `Zeta2HatLinear` would drag `Zeta2Hat`'s member data and
`Zeta2QnInt` into tale-1's stack — which `Zeta2T1Shift` deliberately kept clear, importing only
`Mathlib.Data.Finsupp.Basic` and `Zeta2Moments` — to obtain two generic `ℕ →₀ ℚ` facts, one of
which (`sum_add`) this file does not restate at all because `Finsupp.sum_add_index'` serves
directly.  Logged as `docs/future/found_arch/2026-09-14-finsupp-sum-smul-twin.md`.

## Rung 0 (LEAN.md §5)

§5 carries a GREEN/RED PAIR ON ONE OBJECT: `clr_eval_worked_instance` proves the clearing
identity at `r = (1, 0)`, `S = {1}`, `t = 0`, and `clr_needs_polynomial_summand` proves that the
SAME identity at the SAME point is FALSE when the `P·W` summand is dropped — i.e. that the hat's
`clr`, transplanted unchanged, would not satisfy `clr_eval`.  Plus: `evalRep` separates on the
pole family AND on the polynomial part (the hat can only exhibit the first), and `Φ` is not
constant.

**How to elaborate it** (LEAN.md §0 — Lean never runs on the laptop):

    sh external_tests/zeta2_arith/run_probe.sh Zeta2T1Inj.lean

Falsifier: `sh external_tests/zeta2_arith/falsify_t1inj.sh`.  Archived output:
`out_axioms_t1inj.txt`, `out_t1inj_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2T1Shift

namespace Zeta2T1Inj

open Zeta2Moments Zeta2T1Shift Polynomial Finset

/-! ## §1 — the one `Finsupp` fact this file needs on top of Mathlib

`Finsupp.sum_add_index'` is used directly below; only the SMUL half needs the `Finset.mul_sum`
pull-out, so only it is named.  See the header for why this is restated rather than imported. -/

theorem sum_smul (g : ℕ → ℚ → ℚ) (h0 : ∀ k, g k 0 = 0)
    (hsmul : ∀ k (c b : ℚ), g k (c * b) = c * g k b) (c : ℚ) (f : ℕ →₀ ℚ) :
    (c • f).sum g = c * f.sum g := by
  rw [Finsupp.sum_smul_index' h0]
  simp only [smul_eq_mul, hsmul]
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]

/-- `ℒ` is homogeneous.  `Zeta2Moments` proves `Lpoly_zero`/`_add`/`_sum`/`_shift` but not this
one, and `Φ_smul` needs it on the polynomial coordinate. -/
theorem Lpoly_smul (M : ℤ) (c : ℚ) (p : Polynomial ℚ) :
    Lpoly M (c • p) = c * Lpoly M p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [smul_add, Lpoly_add, Lpoly_add, hp, hq]; ring
  | monomial j a =>
      rw [Polynomial.smul_monomial, Lpoly_monomial, Lpoly_monomial, smul_eq_mul]; ring

/-- `p ↦ (c • p).eval t` is `c ·` the evaluation.  Mathlib's `Polynomial.eval_smul` is not
available at this import set (censused 2026-09-14), and the monomial induction is three lines. -/
theorem eval_smul_rat (c t : ℚ) (p : Polynomial ℚ) : (c • p).eval t = c * p.eval t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [smul_add, eval_add, eval_add, hp, hq]; ring
  | monomial j a =>
      rw [Polynomial.smul_monomial, eval_monomial, eval_monomial, smul_eq_mul]; ring

/-! ## §2 — `evalRep` and `Φ` are linear on `Rep`

`Zeta2T1Shift` already proves `Phi_sub`; the ADD and SMUL halves the row names as `Φ_add` /
`Φ_smul` are here, and `evalRep`'s matching four are what `rep_injective`'s consumers need to
put a relation between EVALUATIONS into `Rep`. -/

theorem evalRep_zero (t : ℚ) : evalRep (0 : Rep) t = 0 := by
  show (0 : Polynomial ℚ).eval t + (0 : ℕ →₀ ℚ).sum (fun k c => c / (t + (k : ℚ))) = 0
  simp

theorem evalRep_add (r s : Rep) (t : ℚ) :
    evalRep (r + s) t = evalRep r t + evalRep s t := by
  show (r.1 + s.1).eval t + (r.2 + s.2).sum (fun k c => c / (t + (k : ℚ))) = _
  rw [Finsupp.sum_add_index' (fun _ => zero_div _) (fun _ b₁ b₂ => add_div b₁ b₂ _), eval_add]
  show _ = (r.1.eval t + r.2.sum (fun k c => c / (t + (k : ℚ))))
      + (s.1.eval t + s.2.sum (fun k c => c / (t + (k : ℚ))))
  ring

theorem evalRep_smul (c : ℚ) (r : Rep) (t : ℚ) :
    evalRep (c • r) t = c * evalRep r t := by
  show (c • r.1).eval t + (c • r.2).sum (fun k b => b / (t + (k : ℚ))) = _
  rw [sum_smul (g := fun k b => b / (t + (k : ℚ))) (fun _ => zero_div _)
        (fun _ c' b => mul_div_assoc c' b _), eval_smul_rat]
  show _ = c * (r.1.eval t + r.2.sum (fun k b => b / (t + (k : ℚ))))
  ring

theorem evalRep_sub (r s : Rep) (t : ℚ) :
    evalRep (r - s) t = evalRep r t - evalRep s t := by
  have h : r - s = r + (-1 : ℚ) • s := by rw [neg_one_smul]; abel
  rw [h, evalRep_add, evalRep_smul]
  ring

/-- **`Σᵢ αᵢ · evalRep rᵢ = evalRep (Σᵢ αᵢ · rᵢ)`** — the form a (★) relation arrives in. -/
theorem evalRep_sum {ι : Type*} (s : Finset ι) (α : ι → ℚ) (rf : ι → Rep) (t : ℚ) :
    evalRep (∑ i ∈ s, α i • rf i) t = ∑ i ∈ s, α i * evalRep (rf i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalRep_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, evalRep_add, evalRep_smul, ih]

theorem Phi_zero (m : ℕ) : Phi m (0 : Rep) = 0 := by
  show ((0 : ℕ →₀ ℚ).sum (fun _ c => c),
      Lpoly (-(m : ℤ) - 1) (0 : Polynomial ℚ)
        - (0 : ℕ →₀ ℚ).sum (fun k c => c * harm 2 (k - m - 1))) = 0
  rw [Lpoly_zero]
  simp

/-- **`Φ_add`** — the row's first named linearity half. -/
theorem Phi_add (m : ℕ) (r s : Rep) : Phi m (r + s) = Phi m r + Phi m s := by
  unfold Phi
  have h1 : (r + s).2.sum (fun _ c => c)
      = r.2.sum (fun _ c => c) + s.2.sum (fun _ c => c) :=
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  have h2 : (r + s).2.sum (fun k c => c * harm 2 (k - m - 1))
      = r.2.sum (fun k c => c * harm 2 (k - m - 1))
        + s.2.sum (fun k c => c * harm 2 (k - m - 1)) :=
    Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
  have h3 : (r + s).1 = r.1 + s.1 := rfl
  rw [h3, Lpoly_add, h1, h2, Prod.mk_add_mk, Prod.mk.injEq]
  exact ⟨rfl, by ring⟩

/-- **`Φ_smul`** — the row's second named linearity half. -/
theorem Phi_smul (m : ℕ) (c : ℚ) (r : Rep) : Phi m (c • r) = c • Phi m r := by
  unfold Phi
  have h1 : (c • r).2.sum (fun _ b => b) = c * r.2.sum (fun _ b => b) :=
    sum_smul (g := fun _ b => b) (fun _ => rfl) (fun _ _ _ => rfl) c r.2
  have h2 : (c • r).2.sum (fun k b => b * harm 2 (k - m - 1))
      = c * r.2.sum (fun k b => b * harm 2 (k - m - 1)) :=
    sum_smul (g := fun k b => b * harm 2 (k - m - 1)) (fun _ => zero_mul _)
      (fun _ _ _ => by ring) c r.2
  have h3 : (c • r).1 = c • r.1 := rfl
  rw [h3, Lpoly_smul, h1, h2, Prod.smul_mk]
  refine Prod.ext ?_ ?_
  · show c * r.2.sum (fun _ b => b) = c • r.2.sum (fun _ b => b)
    rw [smul_eq_mul]
  · show c * Lpoly (-(m : ℤ) - 1) r.1 - c * r.2.sum (fun k b => b * harm 2 (k - m - 1))
        = c • (Lpoly (-(m : ℤ) - 1) r.1 - r.2.sum (fun k b => b * harm 2 (k - m - 1)))
    rw [smul_eq_mul]
    ring

/-- **`Σᵢ αᵢ · Φ rᵢ = Φ (Σᵢ αᵢ · rᵢ)`** — the row's headline linearity, in the form §4 uses. -/
theorem Phi_sum {ι : Type*} (m : ℕ) (s : Finset ι) (α : ι → ℚ) (rf : ι → Rep) :
    Phi m (∑ i ∈ s, α i • rf i) = ∑ i ∈ s, α i • Phi m (rf i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Phi_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Phi_add, Phi_smul, ih]

/-! ## §3 — the cleared numerator, and `rep_injective`

Order 1, so `W = ∏_{j∈S}(X + j)` is the FIRST power and `cof` its cofactor; the hat's `^2` and
its derivative step are gone.  The polynomial part rides as `r.1 * denom S`, which vanishes at
every pole and is recovered afterwards by cancellation in `ℚ[X]`. -/

/-- The common denominator over the pole set `S`. -/
noncomputable def denom (S : Finset ℕ) : ℚ[X] := ∏ j ∈ S, (X + C ((j : ℚ)))

/-- The cofactor at `k`: the common denominator with `(X + k)` removed. -/
noncomputable def cof (S : Finset ℕ) (k : ℕ) : ℚ[X] := ∏ j ∈ S.erase k, (X + C ((j : ℚ)))

/-- `evalRep r · ∏_{j∈S}(X + j)`, as a polynomial.  **The first summand is what `Rep̂` has no
counterpart for** — and it is the summand that vanishes at every pole. -/
noncomputable def clr (r : Rep) (S : Finset ℕ) : ℚ[X] :=
  r.1 * denom S + ∑ k ∈ S, C (r.2 k) * cof S k

theorem denom_monic (S : Finset ℕ) : (denom S).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_add_C ((j : ℚ))

/-- The one fact the polynomial summand needs that the hat never had to state. -/
theorem denom_ne_zero (S : Finset ℕ) : denom S ≠ 0 := (denom_monic S).ne_zero

/-- …and the other: the polynomial summand is ANNIHILATED at every pole, which is why the
residue extraction below never mentions it. -/
theorem denom_eval_at (S : Finset ℕ) {k₀ : ℕ} (hk₀ : k₀ ∈ S) :
    (denom S).eval (-(k₀ : ℚ)) = 0 := by
  rw [denom, eval_prod]
  exact Finset.prod_eq_zero hk₀ (by simp)

theorem cof_eval_ne (S : Finset ℕ) (k : ℕ) : (cof S k).eval (-(k : ℚ)) ≠ 0 := by
  rw [cof, eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
  have hne : -(k : ℚ) + (j : ℚ) ≠ 0 := by
    intro hc
    exact hjk (by exact_mod_cast (by linarith : (j : ℚ) = (k : ℚ)))
  simpa using hne

theorem cof_eval_at_other (S : Finset ℕ) {k k₀ : ℕ} (hk₀ : k₀ ∈ S) (hne : k ≠ k₀) :
    (cof S k).eval (-(k₀ : ℚ)) = 0 := by
  have hmem : k₀ ∈ S.erase k := Finset.mem_erase.2 ⟨Ne.symm hne, hk₀⟩
  rw [cof, eval_prod]
  exact Finset.prod_eq_zero hmem (by simp)

/-- Off the poles, the cleared numerator IS `evalRep` times the common denominator — for an
ARBITRARY `Rep`, polynomial part included. -/
theorem clr_eval (r : Rep) (S : Finset ℕ) (hS : r.2.support ⊆ S)
    (t : ℚ) (ht : ∀ j ∈ S, t + (j : ℚ) ≠ 0) :
    (clr r S).eval t = evalRep r t * ∏ j ∈ S, (t + (j : ℚ)) := by
  have hev : evalRep r t = r.1.eval t + ∑ k ∈ S, r.2 k / (t + (k : ℚ)) := by
    show r.1.eval t + r.2.sum (fun k c => c / (t + (k : ℚ))) = _
    rw [Finsupp.sum_of_support_subset r.2 hS (fun k c => c / (t + (k : ℚ)))
        (fun i _ => zero_div _)]
  have hden : (denom S).eval t = ∏ j ∈ S, (t + (j : ℚ)) := by
    rw [denom, eval_prod]; simp
  rw [hev, clr, eval_add, eval_mul, hden, eval_finsetSum, add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hW : ∏ j ∈ S, (t + (j : ℚ)) = (t + (k : ℚ)) * ∏ j ∈ S.erase k, (t + (j : ℚ)) :=
    (Finset.mul_prod_erase S (fun j : ℕ => (t + (j : ℚ))) hk).symm
  have hk0 : t + (k : ℚ) ≠ 0 := ht k hk
  rw [hW, cof, eval_mul, eval_prod, eval_C]
  simp only [eval_add, eval_X, eval_C]
  field_simp

/-- At `t = −k₀` every term but the diagonal one vanishes — **the polynomial summand among
them**, by `denom_eval_at` — so the value reads off `c_{k₀}`.  Order 1, so there is no
derivative step: this is where `Zeta2HatInj.clr_deriv_at` and its `sq_dvd_cof` would be. -/
theorem clr_eval_at (r : Rep) (S : Finset ℕ) {k₀ : ℕ} (hk₀ : k₀ ∈ S) :
    (clr r S).eval (-(k₀ : ℚ)) = r.2 k₀ * (cof S k₀).eval (-(k₀ : ℚ)) := by
  rw [clr, eval_add, eval_mul, denom_eval_at S hk₀, mul_zero, zero_add, eval_finsetSum,
    Finset.sum_eq_single k₀]
  · simp
  · intro k _ hne
    rw [eval_mul, cof_eval_at_other S hk₀ hne, mul_zero]
  · intro hc; exact absurd hk₀ hc

/-- A representation whose evaluation vanishes off a finite set is the zero representation —
**both coordinates**, the pole family by residue extraction and the polynomial part by one
cancellation in the domain `ℚ[X]`. -/
theorem eq_zero_of_evalRep_vanishes (r : Rep) (E : Finset ℚ)
    (h : ∀ t : ℚ, t ∉ E → evalRep r t = 0) : r = 0 := by
  classical
  have hS : r.2.support ⊆ r.2.support := subset_rfl
  have hzero : clr r r.2.support = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    have hfin : ((E ∪ r.2.support.image (fun j : ℕ => -(j : ℚ)) : Finset ℚ) : Set ℚ).Finite :=
      Finset.finite_toSet _
    refine Set.Infinite.mono ?_ hfin.infinite_compl
    intro t htc
    simp only [Set.mem_compl_iff, Finset.coe_union, Set.mem_union, Finset.mem_coe,
      Finset.mem_image, not_or, not_exists] at htc
    obtain ⟨hE, hpol⟩ := htc
    have hpole : ∀ j ∈ r.2.support, t + (j : ℚ) ≠ 0 := by
      intro j hj hc
      exact (hpol j) ⟨hj, by linarith⟩
    show (clr r r.2.support).IsRoot t
    rw [Polynomial.IsRoot, clr_eval r r.2.support hS t hpole, h t hE, zero_mul]
  have hc : ∀ k ∈ r.2.support, r.2 k = 0 := by
    intro k hk
    have hcof := cof_eval_ne r.2.support k
    have h0 : (0 : ℚ) = r.2 k * (cof r.2.support k).eval (-(k : ℚ)) := by
      rw [← clr_eval_at r r.2.support hk, hzero, eval_zero]
    exact (mul_eq_zero.1 h0.symm).resolve_right hcof
  have hz2 : r.2 = 0 := by
    ext k
    by_cases hk : k ∈ r.2.support
    · simpa using hc k hk
    · simpa using Finsupp.notMem_support_iff.1 hk
  have hz1 : r.1 = 0 := by
    have hsum : ∑ k ∈ r.2.support, C (r.2 k) * cof r.2.support k = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [hc k hk]
    have hcl : r.1 * denom r.2.support = 0 := by
      have hz := hzero
      rw [clr, hsum, add_zero] at hz
      exact hz
    exact (mul_eq_zero.1 hcl).resolve_right (denom_ne_zero _)
  exact Prod.ext hz1 hz2

/-- **`rep_injective`** — row PHI-REP's content lemma.  Two representations whose evaluations
agree off ANY finite set are the same representation: the partial-fraction data of a rational
function with a polynomial part and SIMPLE poles at negative integers is unique.  This is
`Zeta2HatInj.evalRep_inj` one pole order down. -/
theorem evalRep_inj (r s : Rep) (E : Finset ℚ)
    (h : ∀ t : ℚ, t ∉ E → evalRep r t = evalRep s t) : r = s := by
  have hz : r - s = 0 :=
    eq_zero_of_evalRep_vanishes (r - s) E fun t ht => by
      rw [evalRep_sub, h t ht, sub_self]
  exact sub_eq_zero.1 hz

/-! ## §4 — `rec_of_telescoping_of_linear`, RESTATED at `Φ : Rep → ℚ × ℚ`

`Zeta2XL1B.rec_of_telescoping_of_linear` is typed `Φ : (ℝ → ℝ) → ℝ` with linearity hypotheses on
FUNCTIONS; the chain doc's Status header (§"Φ is DECIDED ℚ×ℚ-valued") supersedes that signature
and asks for it here.  The restatement differs in three ways, all of them the point: the
functional is the concrete `Zeta2T1Shift.Phi` and its two linearity hypotheses are DISCHARGED
rather than assumed; the telescoping identity is only required OFF a finite set, which is what a
(★) family delivers; and `hbdy` is stated at `repDelta`, which is `Zeta2T1Shift.hbdy`'s own
conclusion. -/

theorem evalRep_repDelta (r : Rep) (t : ℚ) :
    evalRep (repDelta r) t = evalRep r (t + 1) - evalRep r t := by
  rw [repDelta, evalRep_sub, evalRep_shiftRep]

/-- `Zeta2HatInj.Phihat_of_evalRep` at `Φ`: a linear relation that holds between the
EVALUATIONS off a finite set holds between the `Φ` images. -/
theorem Phi_of_evalRep {ι : Type*} (m : ℕ) (s : Finset ι) (α : ι → ℚ) (rf : ι → Rep)
    (ρ : Rep) (E : Finset ℚ)
    (h : ∀ t : ℚ, t ∉ E → ∑ i ∈ s, α i * evalRep (rf i) t = evalRep ρ t) :
    ∑ i ∈ s, α i • Phi m (rf i) = Phi m ρ := by
  have hrep : ∑ i ∈ s, α i • rf i = ρ :=
    evalRep_inj _ _ E fun t ht => by rw [evalRep_sum]; exact h t ht
  rw [← Phi_sum, hrep]

/-- **The row's restatement.**  A pointwise four-term telescoping off a finite set, plus the
boundary vanishing, gives the recurrence on the `Φ` images — with no linearity hypothesis to
supply, because `Φ_add` and `Φ_smul` are theorems above. -/
theorem rec_of_telescoping_of_linear (m : ℕ) (ρ₀ ρ₁ ρ₂ ρ₃ Sr : Rep) (a₀ a₁ a₂ a₃ : ℚ)
    (E : Finset ℚ)
    (htel : ∀ t : ℚ, t ∉ E →
      a₀ * evalRep ρ₀ t + a₁ * evalRep ρ₁ t + a₂ * evalRep ρ₂ t + a₃ * evalRep ρ₃ t
        = evalRep Sr (t + 1) - evalRep Sr t)
    (hbdy : Phi m (repDelta Sr) = 0) :
    a₀ • Phi m ρ₀ + a₁ • Phi m ρ₁ + a₂ • Phi m ρ₂ + a₃ • Phi m ρ₃ = 0 := by
  have hrep : a₀ • ρ₀ + a₁ • ρ₁ + a₂ • ρ₂ + a₃ • ρ₃ = repDelta Sr := by
    refine evalRep_inj _ _ E fun t ht => ?_
    rw [evalRep_add, evalRep_add, evalRep_add, evalRep_smul, evalRep_smul, evalRep_smul,
      evalRep_smul, evalRep_repDelta]
    exact htel t ht
  have hΦ := congrArg (Phi m) hrep
  rw [Phi_add, Phi_add, Phi_add, Phi_smul, Phi_smul, Phi_smul, Phi_smul, hbdy] at hΦ
  exact hΦ

/-- **The composition executed**, the tale-1 twin of `Zeta2XL1B.hL_at_one_n_of_star`: this row's
`rep_injective` and PHI-BDY's landed `Zeta2T1Shift.hbdy` compose with nothing between them, so
the assembly L1-ASM performs is this theorem with `ρⱼ`, `Sr` supplied. -/
theorem rec_of_telescoping (m : ℕ) (ρ₀ ρ₁ ρ₂ ρ₃ Sr : Rep) (a₀ a₁ a₂ a₃ : ℚ) (E : Finset ℚ)
    (hsupp : ∀ k ∈ Sr.2.support, m + 1 ≤ k)
    (hz : (derivative Sr.1).eval (-(m : ℚ))
            = Sr.2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2))
    (htel : ∀ t : ℚ, t ∉ E →
      a₀ * evalRep ρ₀ t + a₁ * evalRep ρ₁ t + a₂ * evalRep ρ₂ t + a₃ * evalRep ρ₃ t
        = evalRep Sr (t + 1) - evalRep Sr t) :
    a₀ • Phi m ρ₀ + a₁ • Phi m ρ₁ + a₂ • Phi m ρ₂ + a₃ • Phi m ρ₃ = 0 :=
  rec_of_telescoping_of_linear m ρ₀ ρ₁ ρ₂ ρ₃ Sr a₀ a₁ a₂ a₃ E htel
    (Zeta2T1Shift.hbdy m Sr hsupp hz)

/-! ## §5 — rung 0: the maps separate, and the polynomial summand is load-bearing

LEAN.md §5 — `evalRep_inj` would be worthless if `evalRep` were constant on `Rep`, and
`clr_eval` would be worthless if it held with the `P·W` summand deleted.  The last two theorems
are a GREEN/RED PAIR ON ONE OBJECT: the same instance, the same point, the identity TRUE with
the summand and FALSE without it. -/

theorem evalRep_single_one :
    evalRep (((0 : Polynomial ℚ), Finsupp.single 1 (1 : ℚ)) : Rep) 1 = 1 / 2 := by
  show (0 : Polynomial ℚ).eval 1
      + (Finsupp.single (1 : ℕ) (1 : ℚ)).sum (fun k c => c / ((1 : ℚ) + (k : ℚ))) = 1 / 2
  rw [Polynomial.eval_zero, Finsupp.sum_single_index (by simp)]
  norm_num

/-- The pole family is separated — the hat's own rung-0, transplanted. -/
theorem evalRep_nonconstant :
    evalRep (((0 : Polynomial ℚ), Finsupp.single 1 (1 : ℚ)) : Rep) 1 ≠ evalRep (0 : Rep) 1 := by
  rw [evalRep_single_one, evalRep_zero]
  norm_num

/-- **The POLYNOMIAL part is separated too** — and this half has no twin at the hat, where
`Rep̂` carries no polynomial part at all.  Without it, `evalRep_inj`'s conclusion `r = s` would
be unjustified in its first coordinate. -/
theorem evalRep_separates_polynomial :
    evalRep ((Polynomial.X, (0 : ℕ →₀ ℚ)) : Rep) 2 ≠ evalRep (0 : Rep) 2 := by
  have hx : evalRep ((Polynomial.X, (0 : ℕ →₀ ℚ)) : Rep) 2 = 2 := by
    show (Polynomial.X : Polynomial ℚ).eval 2
        + (0 : ℕ →₀ ℚ).sum (fun k c => c / ((2 : ℚ) + (k : ℚ))) = 2
    simp
  rw [hx, evalRep_zero]
  norm_num

theorem Phi_single_fst :
    (Phi 0 (((0 : Polynomial ℚ), Finsupp.single 1 (1 : ℚ)) : Rep)).1 = 1 := by
  show (Finsupp.single 1 (1 : ℚ)).sum (fun _ c => c) = 1
  rw [Finsupp.sum_single_index rfl]

/-- `Φ` is not constant, so its linearity above is not linearity of the zero map. -/
theorem Phi_nonconstant :
    Phi 0 (((0 : Polynomial ℚ), Finsupp.single 1 (1 : ℚ)) : Rep) ≠ Phi 0 (0 : Rep) := by
  intro hcon
  have h := congrArg Prod.fst hcon
  rw [Phi_single_fst, Phi_zero] at h
  simp at h

/-- **The GREEN half of the pair.**  `clr_eval` at `r = (1, 0)`, `S = {1}`, `t = 0`. -/
theorem clr_eval_worked_instance :
    (clr (((1 : Polynomial ℚ), (0 : ℕ →₀ ℚ)) : Rep) {1}).eval 0
      = evalRep (((1 : Polynomial ℚ), (0 : ℕ →₀ ℚ)) : Rep) 0
          * ∏ j ∈ ({1} : Finset ℕ), ((0 : ℚ) + (j : ℚ)) := by
  refine clr_eval _ _ (by simp) 0 ?_
  intro j hj
  rw [Finset.mem_singleton] at hj
  subst hj
  norm_num

/-- **The RED half, on the SAME object at the SAME point.**  Drop the `r.1 * denom S` summand —
i.e. transplant `Zeta2HatInj.clr` unchanged, which has no such summand because `Rep̂` has no
polynomial part — and `clr_eval`'s conclusion is FALSE here: the pole sum is `0` and the
right-hand side is `1`.  So the summand the row's cell calls an obstacle is a REQUIREMENT, and
`clr_eval` above is not true by accident of the instance. -/
theorem clr_needs_polynomial_summand :
    (∑ k ∈ ({1} : Finset ℕ),
        C ((((1 : Polynomial ℚ), (0 : ℕ →₀ ℚ)) : Rep).2 k) * cof {1} k).eval 0
      ≠ evalRep (((1 : Polynomial ℚ), (0 : ℕ →₀ ℚ)) : Rep) 0
          * ∏ j ∈ ({1} : Finset ℕ), ((0 : ℚ) + (j : ℚ)) := by
  have hl : (∑ k ∈ ({1} : Finset ℕ),
      C ((((1 : Polynomial ℚ), (0 : ℕ →₀ ℚ)) : Rep).2 k) * cof {1} k).eval 0 = 0 := by
    simp
  have hr : evalRep (((1 : Polynomial ℚ), (0 : ℕ →₀ ℚ)) : Rep) 0
      * ∏ j ∈ ({1} : Finset ℕ), ((0 : ℚ) + (j : ℚ)) = 1 := by
    have he : evalRep (((1 : Polynomial ℚ), (0 : ℕ →₀ ℚ)) : Rep) 0 = 1 := by
      show (1 : Polynomial ℚ).eval 0
          + (0 : ℕ →₀ ℚ).sum (fun k c => c / ((0 : ℚ) + (k : ℚ))) = 1
      simp
    rw [he]
    simp
  rw [hl, hr]
  norm_num

/-! ## §6 — receipts (`LEAN.md` §1 — exit 0 is not an attestation) -/

#print axioms Zeta2T1Inj.sum_smul
#print axioms Zeta2T1Inj.Lpoly_smul
#print axioms Zeta2T1Inj.eval_smul_rat
#print axioms Zeta2T1Inj.evalRep_zero
#print axioms Zeta2T1Inj.evalRep_add
#print axioms Zeta2T1Inj.evalRep_smul
#print axioms Zeta2T1Inj.evalRep_sub
#print axioms Zeta2T1Inj.evalRep_sum
#print axioms Zeta2T1Inj.Phi_zero
#print axioms Zeta2T1Inj.Phi_add
#print axioms Zeta2T1Inj.Phi_smul
#print axioms Zeta2T1Inj.Phi_sum
#print axioms Zeta2T1Inj.denom_monic
#print axioms Zeta2T1Inj.denom_ne_zero
#print axioms Zeta2T1Inj.denom_eval_at
#print axioms Zeta2T1Inj.cof_eval_ne
#print axioms Zeta2T1Inj.cof_eval_at_other
#print axioms Zeta2T1Inj.clr_eval
#print axioms Zeta2T1Inj.clr_eval_at
#print axioms Zeta2T1Inj.eq_zero_of_evalRep_vanishes
#print axioms Zeta2T1Inj.evalRep_inj
#print axioms Zeta2T1Inj.evalRep_repDelta
#print axioms Zeta2T1Inj.Phi_of_evalRep
#print axioms Zeta2T1Inj.rec_of_telescoping_of_linear
#print axioms Zeta2T1Inj.rec_of_telescoping
#print axioms Zeta2T1Inj.evalRep_single_one
#print axioms Zeta2T1Inj.evalRep_nonconstant
#print axioms Zeta2T1Inj.evalRep_separates_polynomial
#print axioms Zeta2T1Inj.Phi_single_fst
#print axioms Zeta2T1Inj.Phi_nonconstant
#print axioms Zeta2T1Inj.clr_eval_worked_instance
#print axioms Zeta2T1Inj.clr_needs_polynomial_summand

end Zeta2T1Inj
