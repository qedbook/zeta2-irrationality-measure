/-
# Row PAIR-4R — the hat member's POLE SETS, and the generic lemma's two structural hypotheses

`docs/future/zeta2-lean-chain.md` row PAIR-4R, §PAIR-4R design notes.

This file is the row's **named next probe** (LEAN.md §9 — test the load-bearing assumption
first): instantiate `Zeta2PF.partialFractions` at the hat member's pole sets at **symbolic `n`**
and discharge ONLY `hdisj` and `hdeg` — the two hypotheses that are pure index bookkeeping —
before touching the residue conditions.  The design notes named exactly this chunk as the
one nothing had executed.

The hat member is

    R̂ₙ/Π̂ = ∏_{l=3n+2}^{20n+1}(2t+l)·∏_{l=1}^{5n}(t+l) / [∏_{l=7n+1}^{18n+1}(t+l)·∏_{l=9n+1}^{20n+1}(t+l)]

whose WRITTEN denominator has roots at `t = −k`, `k ∈ [7n+1, 20n+1]`, doubled exactly on the two
blocks' overlap `[9n+1, 18n+1]`.  So, as a `Finset ℚ` of nodes (the generic lemma's factors are
`X − C k`, and `X − C (−k) = X + C k`):

    S₁ = (Icc (7n+1) (9n) ∪ Icc (18n+2) (20n+1)).image (−·)     card 4n
    S₂ = (Icc (9n+1) (18n+1)).image (−·)                        card 9n+1

and `S₁.card + 2·S₂.card = 4n + 2(9n+1) = 22n+2 > 22n = natDegree (Π̂·Û)` — the degree bound
closes with two to spare, at every `n` including `n = 0`, where `S₁ = ∅` and `S₂ = {−1}` and the
statement degenerates to `Zeta2HatRep.hat_rep_zero`'s `2 > 0` (LEAN.md §5: the edge case is
checked against the real data, not assumed).

The two polynomial objects are introduced here because `hatMember` is a RATIONAL function and
the generic lemma is about `ℚ[X]`; `hatMember_eq_div` is the one bridge between them, and it is
stated with no side condition (a plain quotient of two evaluations) so the nonvanishing
hypothesis travels only where it is actually needed.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Hat
import Zeta2HatRep
import Zeta2PartialFractions
import Zeta2ProdEval

namespace Zeta2HatPoles

open Zeta2Defs Zeta2Hat Zeta2HatRep Polynomial Finset

set_option profiler true
set_option profiler.threshold 100

/-! ## The numerator and the WRITTEN denominator as polynomials -/

/-- `Û` — the hat member's numerator, `natDegree 22n`.  `C 2 * X + C l` rather than
`C 2 * (X + C (l/2))`: the factor is how the member is written, and halving it would put a
rational node into a file whose whole point is integer index bookkeeping. -/
noncomputable def hatNum (n : ℕ) : ℚ[X] :=
  (∏ l ∈ Icc (3 * n + 2) (20 * n + 1), (C (2 : ℚ) * X + C ((l : ℕ) : ℚ)))
    * ∏ l ∈ Icc 1 (5 * n), (X + C ((l : ℕ) : ℚ))

/-- `Ŵ` — the WRITTEN denominator, `natDegree 22n+2`.  Written, not reduced: the `(2t+l)` zeros
cancel `2n` of its roots, and PAIR-6's hypothesis shape is about the written roots (design notes
R4), so nothing here may quietly reduce it. -/
noncomputable def hatDen (n : ℕ) : ℚ[X] :=
  (∏ l ∈ Icc (7 * n + 1) (18 * n + 1), (X + C ((l : ℕ) : ℚ)))
    * ∏ l ∈ Icc (9 * n + 1) (20 * n + 1), (X + C ((l : ℕ) : ℚ))

theorem hatNum_eval (n : ℕ) (t : ℚ) :
    (hatNum n).eval t
      = (∏ l ∈ Icc (3 * n + 2) (20 * n + 1), (2 * t + (l : ℚ)))
        * ∏ l ∈ Icc 1 (5 * n), (t + (l : ℚ)) := by
  rw [hatNum, eval_mul, eval_prod, eval_prod]
  simp

theorem hatDen_eval (n : ℕ) (t : ℚ) :
    (hatDen n).eval t
      = (∏ l ∈ Icc (7 * n + 1) (18 * n + 1), (t + (l : ℚ)))
        * ∏ l ∈ Icc (9 * n + 1) (20 * n + 1), (t + (l : ℚ)) := by
  rw [hatDen, eval_mul, eval_prod, eval_prod]
  simp

/-- The bridge from the rational function to the two polynomials.  No side condition: both
sides are `_ / _` in ℚ, and `x / 0 = 0` on both. -/
theorem hatMember_eq_div (n : ℕ) (t : ℚ) :
    hatMember n t = (hatNum n).eval t / (hatDen n).eval t := by
  rw [hatNum_eval, hatDen_eval, hatMember]

/-! ## The pole sets -/

/-- The node map: the poles sit at `t = −k`, the generic lemma's factors are `X − C k`. -/
theorem neg_cast_inj : Function.Injective (fun k : ℕ => -((k : ℕ) : ℚ)) := by
  intro a b h
  simpa using h

/-- The indices of the SIMPLE poles: the cancelled run `[7n+1, 9n]` (where the residue is `0`)
and the hi run `[18n+2, 20n+1]` (second denominator block only). -/
def idxS1 (n : ℕ) : Finset ℕ := Icc (7 * n + 1) (9 * n) ∪ Icc (18 * n + 2) (20 * n + 1)

/-- The indices of the DOUBLE poles: the two blocks' overlap.  The lo sub-run `[9n+1, 10n]` has
order-2 coefficient `0` — the lemma never asks a double pole to be genuinely double (design
notes R2). -/
def idxS2 (n : ℕ) : Finset ℕ := Icc (9 * n + 1) (18 * n + 1)

noncomputable def poleS1 (n : ℕ) : Finset ℚ := (idxS1 n).image (fun k : ℕ => -((k : ℕ) : ℚ))

noncomputable def poleS2 (n : ℕ) : Finset ℚ := (idxS2 n).image (fun k : ℕ => -((k : ℕ) : ℚ))

theorem mem_idxS1 (n k : ℕ) : k ∈ idxS1 n ↔ (7 * n + 1 ≤ k ∧ k ≤ 9 * n) ∨
    (18 * n + 2 ≤ k ∧ k ≤ 20 * n + 1) := by
  simp [idxS1, Finset.mem_union, Finset.mem_Icc]

theorem mem_idxS2 (n k : ℕ) : k ∈ idxS2 n ↔ 9 * n + 1 ≤ k ∧ k ≤ 18 * n + 1 := by
  simp [idxS2, Finset.mem_Icc]

theorem idxS1_disjoint_idxS2 (n : ℕ) : Disjoint (idxS1 n) (idxS2 n) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [mem_idxS1] at hx
  rw [mem_idxS2] at hy
  omega

theorem card_idxS1 (n : ℕ) : (idxS1 n).card = 4 * n := by
  have hd : Disjoint (Icc (7 * n + 1) (9 * n)) (Icc (18 * n + 2) (20 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  rw [idxS1, Finset.card_union_of_disjoint hd, Nat.card_Icc, Nat.card_Icc]
  omega

theorem card_idxS2 (n : ℕ) : (idxS2 n).card = 9 * n + 1 := by
  rw [idxS2, Nat.card_Icc]
  omega

theorem card_poleS1 (n : ℕ) : (poleS1 n).card = 4 * n := by
  rw [poleS1, Finset.card_image_of_injective _ neg_cast_inj, card_idxS1]

theorem card_poleS2 (n : ℕ) : (poleS2 n).card = 9 * n + 1 := by
  rw [poleS2, Finset.card_image_of_injective _ neg_cast_inj, card_idxS2]

/-- **`hdisj`** — the first of the two structural hypotheses. -/
theorem poles_disjoint (n : ℕ) : Disjoint (poleS1 n) (poleS2 n) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [poleS1, Finset.mem_image] at hx
  rw [poleS2, Finset.mem_image] at hy
  obtain ⟨k, hk, hkx⟩ := hx
  obtain ⟨j, hj, hjx⟩ := hy
  have : k = j := neg_cast_inj (show -((k : ℕ) : ℚ) = -((j : ℕ) : ℚ) by rw [hkx, hjx])
  subst this
  exact (Finset.disjoint_left.1 (idxS1_disjoint_idxS2 n)) hk hj

/-! ## The degree count -/

theorem natDegree_hatNum (n : ℕ) : (hatNum n).natDegree ≤ 22 * n := by
  have h1 : (∏ l ∈ Icc (3 * n + 2) (20 * n + 1),
      (C (2 : ℚ) * X + C ((l : ℕ) : ℚ))).natDegree ≤ 17 * n := by
    refine le_trans (natDegree_prod_le _ _) ?_
    have hb : ∀ l ∈ Icc (3 * n + 2) (20 * n + 1),
        (C (2 : ℚ) * X + C ((l : ℕ) : ℚ)).natDegree ≤ 1 := by
      intro l _
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · exact le_trans (natDegree_C_mul_le _ _) (by simp)
      · simp
    refine le_trans (Finset.sum_le_sum hb) ?_
    rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
    omega
  have h2 : (∏ l ∈ Icc 1 (5 * n), (X + C ((l : ℕ) : ℚ))).natDegree ≤ 5 * n := by
    refine le_trans (natDegree_prod_le _ _) ?_
    have hb : ∀ l ∈ Icc 1 (5 * n), (X + C ((l : ℕ) : ℚ)).natDegree ≤ 1 := by
      intro l _
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_) <;> simp
    refine le_trans (Finset.sum_le_sum hb) ?_
    rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
    omega
  refine le_trans (natDegree_mul_le) ?_
  omega

/-- **`hdeg`** — the second structural hypothesis, with margin 2 at every `n`.
`22n < 4n + 2(9n+1) = 22n+2`. -/
theorem hat_hdeg (n : ℕ) :
    (C (hatPi n) * hatNum n).natDegree < (poleS1 n).card + 2 * (poleS2 n).card := by
  rw [card_poleS1, card_poleS2]
  have h1 := natDegree_hatNum n
  have h2 := natDegree_C_mul_le (hatPi n) (hatNum n)
  omega

/-- **The margin is TWO, and row PAIR-4L is what needs the second one.**  `hat_hdeg` states the
strict inequality `partialFractions` consumes; `Zeta2PF.sum_order1_eq_zero` needs `deg + 1 <`,
which is a genuinely stronger hypothesis and is exactly what the hat member has
(`22n + 1 < 22n + 2`).  Same three facts, one different `omega` goal — not a restatement. -/
theorem hat_hdeg_two (n : ℕ) :
    (C (hatPi n) * hatNum n).natDegree + 1 < (poleS1 n).card + 2 * (poleS2 n).card := by
  rw [card_poleS1, card_poleS2]
  have h1 := natDegree_hatNum n
  have h2 := natDegree_C_mul_le (hatPi n) (hatNum n)
  omega

/-! ## The instantiation — the probe's actual verdict

`partialFractions` applied at the hat's pole sets with the two structural hypotheses
DISCHARGED and the residue conditions left as named hypotheses.  This is what the probe
was for: the index bookkeeping composes at symbolic `n`, and what remains is arithmetic about
`hatA` / `hatLam` / `hatBlo` / `hatBhi` and nothing structural. -/

open scoped Classical in
theorem hat_partialFractions (n : ℕ) (b a : ℚ → ℚ)
    (h₁ : ∀ k ∈ poleS1 n, (C (hatPi n) * hatNum n).eval k
      = b k * (Zeta2PF.pf1 (poleS1 n) (poleS2 n) k).eval k)
    (h₂ : ∀ k ∈ poleS2 n, (C (hatPi n) * hatNum n).eval k
      = a k * (Zeta2PF.pf2 (poleS1 n) (poleS2 n) k).eval k)
    (h₃ : ∀ k ∈ poleS2 n, (derivative (C (hatPi n) * hatNum n)).eval k
      = a k * (derivative (Zeta2PF.pf2 (poleS1 n) (poleS2 n) k)).eval k
        + b k * (Zeta2PF.pf2 (poleS1 n) (poleS2 n) k).eval k) :
    C (hatPi n) * hatNum n
      = (∑ k ∈ poleS1 n, C (b k) * Zeta2PF.pf1 (poleS1 n) (poleS2 n) k)
        + ∑ k ∈ poleS2 n, (C (b k) * ((X - C k) * Zeta2PF.pf2 (poleS1 n) (poleS2 n) k)
          + C (a k) * Zeta2PF.pf2 (poleS1 n) (poleS2 n) k) :=
  Zeta2PF.partialFractions (poleS1 n) (poleS2 n) (poles_disjoint n) _ b a (hat_hdeg n) h₁ h₂ h₃

/-! ## The cofactors in the hat's OWN index vocabulary

`pf1` / `pf2` are stated over `Finset ℚ` of nodes.  Every consumer — the residue conditions, and
`Zeta2Hat`'s closed forms — speaks in ℕ indices, so the translation is done ONCE here rather than
at each of the five conditions (LEAN.md §3, and the same reason `partialFractions_nodes` exists
on the simple side). -/

theorem image_erase_comm (s : Finset ℕ) (κ : ℕ) :
    (s.image (fun j : ℕ => -((j : ℕ) : ℚ))).erase (-((κ : ℕ) : ℚ))
      = (s.erase κ).image (fun j : ℕ => -((j : ℕ) : ℚ)) := by
  classical
  ext x
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hx, j, hj, hjx⟩
    refine ⟨j, ⟨fun h => hx ?_, hj⟩, hjx⟩
    rw [← hjx, h]
  · rintro ⟨j, ⟨hjk, hjT⟩, hjx⟩
    refine ⟨fun h => hjk ?_, j, hjT, hjx⟩
    exact neg_cast_inj (show -((j : ℕ) : ℚ) = -((κ : ℕ) : ℚ) from hjx.trans h)

theorem prod_image_sub (s : Finset ℕ) (t : ℚ) :
    ∏ j ∈ s.image (fun j : ℕ => -((j : ℕ) : ℚ)), (t - j) = ∏ j ∈ s, (t + ((j : ℕ) : ℚ)) := by
  classical
  rw [Finset.prod_image (fun x _ y _ h => neg_cast_inj h)]
  exact Finset.prod_congr rfl fun j _ => by ring

theorem prod_image_sub_sq (s : Finset ℕ) (t : ℚ) :
    ∏ j ∈ s.image (fun j : ℕ => -((j : ℕ) : ℚ)), (t - j) ^ 2
      = ∏ j ∈ s, (t + ((j : ℕ) : ℚ)) ^ 2 := by
  classical
  rw [Finset.prod_image (fun x _ y _ h => neg_cast_inj h)]
  exact Finset.prod_congr rfl fun j _ => by ring

theorem poly_prod_image (s : Finset ℕ) :
    ∏ j ∈ s.image (fun j : ℕ => -((j : ℕ) : ℚ)), (X - C j)
      = ∏ j ∈ s, (X + C ((j : ℕ) : ℚ)) := by
  classical
  rw [Finset.prod_image (fun x _ y _ h => neg_cast_inj h)]
  exact Finset.prod_congr rfl fun j _ => by rw [map_neg, sub_neg_eq_add]

theorem poly_prod_image_sq (s : Finset ℕ) :
    ∏ j ∈ s.image (fun j : ℕ => -((j : ℕ) : ℚ)), (X - C j) ^ 2
      = (∏ j ∈ s, (X + C ((j : ℕ) : ℚ))) ^ 2 := by
  classical
  rw [Finset.prod_image (fun x _ y _ h => neg_cast_inj h), ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ => by rw [map_neg, sub_neg_eq_add]

/-- The simple-pole cofactor, as a polynomial in the hat's index vocabulary. -/
theorem pf1_eq (n κ : ℕ) :
    Zeta2PF.pf1 (poleS1 n) (poleS2 n) (-((κ : ℕ) : ℚ))
      = (∏ j ∈ (idxS1 n).erase κ, (X + C ((j : ℕ) : ℚ)))
        * (∏ j ∈ idxS2 n, (X + C ((j : ℕ) : ℚ))) ^ 2 := by
  classical
  rw [Zeta2PF.pf1, poleS1, poleS2, image_erase_comm, poly_prod_image, poly_prod_image_sq]

/-- The double-pole cofactor, likewise. -/
theorem pf2_eq (n κ : ℕ) :
    Zeta2PF.pf2 (poleS1 n) (poleS2 n) (-((κ : ℕ) : ℚ))
      = (∏ j ∈ idxS1 n, (X + C ((j : ℕ) : ℚ)))
        * (∏ j ∈ (idxS2 n).erase κ, (X + C ((j : ℕ) : ℚ))) ^ 2 := by
  classical
  rw [Zeta2PF.pf2, poleS1, poleS2, image_erase_comm, poly_prod_image, poly_prod_image_sq]

/-! ## The three numbers the residue conditions are about

`polePf1 n κ`, `polePf2 n κ` and `poleLam n κ` are the cofactor value at a simple pole, at a
double pole, and the double pole's LOG-DERIVATIVE — the last is where `Zeta2Hat.hatLam`'s
harmonic differences must come from.  Naming them is what lets the residue conditions be
stated without a single `Finset ℚ` appearing (LEAN.md §3: state each lemma with exactly the
hypotheses its callers produce). -/

def polePf1 (n κ : ℕ) : ℚ :=
  (∏ j ∈ (idxS1 n).erase κ, ((j : ℚ) - (κ : ℚ))) * (∏ j ∈ idxS2 n, ((j : ℚ) - (κ : ℚ))) ^ 2

def polePf2 (n κ : ℕ) : ℚ :=
  (∏ j ∈ idxS1 n, ((j : ℚ) - (κ : ℚ))) * (∏ j ∈ (idxS2 n).erase κ, ((j : ℚ) - (κ : ℚ))) ^ 2

def poleLam (n κ : ℕ) : ℚ :=
  (∑ j ∈ idxS1 n, 1 / ((j : ℚ) - (κ : ℚ)))
    + 2 * ∑ j ∈ (idxS2 n).erase κ, 1 / ((j : ℚ) - (κ : ℚ))

theorem pf1_eval_at (n κ : ℕ) :
    (Zeta2PF.pf1 (poleS1 n) (poleS2 n) (-((κ : ℕ) : ℚ))).eval (-((κ : ℕ) : ℚ))
      = polePf1 n κ := by
  rw [pf1_eq, polePf1, eval_mul, eval_pow, eval_prod, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  rw [Finset.prod_congr rfl (fun j _ => by ring :
    ∀ j ∈ (idxS1 n).erase κ, -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) = ((j : ℚ) - (κ : ℚ)))]
  rw [Finset.prod_congr rfl (fun j _ => by ring :
    ∀ j ∈ idxS2 n, -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) = ((j : ℚ) - (κ : ℚ)))]

theorem pf2_eval_at (n κ : ℕ) :
    (Zeta2PF.pf2 (poleS1 n) (poleS2 n) (-((κ : ℕ) : ℚ))).eval (-((κ : ℕ) : ℚ))
      = polePf2 n κ := by
  rw [pf2_eq, polePf2, eval_mul, eval_pow, eval_prod, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  rw [Finset.prod_congr rfl (fun j _ => by ring :
    ∀ j ∈ idxS1 n, -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) = ((j : ℚ) - (κ : ℚ)))]
  rw [Finset.prod_congr rfl (fun j _ => by ring :
    ∀ j ∈ (idxS2 n).erase κ, -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) = ((j : ℚ) - (κ : ℚ)))]

/-- The derivative of the double-pole cofactor at its own node is the cofactor times a
LOG-DERIVATIVE — a sum of reciprocals over the other poles, each double pole counted twice.
This is the statement `Zeta2Hat.hatLam` has to be shown equal to, and it is where the harmonic
numbers enter; Mathlib's `logDeriv` is analytic and does not serve (design-notes census), so it
goes through `Zeta2PE.eval_derivative_prod_linear`. -/
theorem pf2_derivative_eval_at (n κ : ℕ) (hκ : κ ∈ idxS2 n) :
    (derivative (Zeta2PF.pf2 (poleS1 n) (poleS2 n) (-((κ : ℕ) : ℚ)))).eval (-((κ : ℕ) : ℚ))
      = polePf2 n κ * poleLam n κ := by
  classical
  have hne1 : ∀ j ∈ idxS1 n, (1 : ℚ) * -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) ≠ 0 := by
    intro j hj
    have hjk : j ≠ κ := fun h => (Finset.disjoint_left.1 (idxS1_disjoint_idxS2 n)) hj (h ▸ hκ)
    have : ((j : ℕ) : ℚ) ≠ ((κ : ℕ) : ℚ) := fun h => hjk (Nat.cast_injective h)
    intro hz
    exact this (by linarith [hz])
  have hne2 : ∀ j ∈ (idxS2 n).erase κ, (1 : ℚ) * -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) ≠ 0 := by
    intro j hj
    have hjk : j ≠ κ := (Finset.mem_erase.1 hj).1
    have : ((j : ℕ) : ℚ) ≠ ((κ : ℕ) : ℚ) := fun h => hjk (Nat.cast_injective h)
    intro hz
    exact this (by linarith [hz])
  have hP : (∏ j ∈ idxS1 n, (X + C ((j : ℕ) : ℚ)))
      = ∏ j ∈ idxS1 n, (C (1 : ℚ) * X + C ((j : ℕ) : ℚ)) :=
    Finset.prod_congr rfl fun j _ => by simp
  have hR : (∏ j ∈ (idxS2 n).erase κ, (X + C ((j : ℕ) : ℚ)))
      = ∏ j ∈ (idxS2 n).erase κ, (C (1 : ℚ) * X + C ((j : ℕ) : ℚ)) :=
    Finset.prod_congr rfl fun j _ => by simp
  have hPd := Zeta2PE.eval_derivative_prod_linear (idxS1 n) (fun _ => (1 : ℚ))
    (fun j => ((j : ℕ) : ℚ)) (-((κ : ℕ) : ℚ)) hne1
  have hRd := Zeta2PE.eval_derivative_prod_linear ((idxS2 n).erase κ) (fun _ => (1 : ℚ))
    (fun j => ((j : ℕ) : ℚ)) (-((κ : ℕ) : ℚ)) hne2
  rw [← hP] at hPd
  rw [← hR] at hRd
  simp only [one_mul] at hPd hRd
  -- `R ^ 2` is written `R * R` so the product rule applies twice and no `C (2 : ℚ)` and no
  -- `2 - 1` exponent ever enters the goal.
  rw [pf2_eq, sq, derivative_mul, derivative_mul]
  simp only [eval_add, eval_mul, eval_prod, eval_C, eval_X]
  rw [hPd, hRd]
  rw [Finset.prod_congr rfl (fun j _ => by ring :
    ∀ j ∈ idxS1 n, -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) = ((j : ℚ) - (κ : ℚ)))]
  rw [Finset.prod_congr rfl (fun j _ => by ring :
    ∀ j ∈ (idxS2 n).erase κ, -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) = ((j : ℚ) - (κ : ℚ)))]
  rw [Finset.sum_congr rfl (fun j _ => by
      rw [show -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) = ((j : ℚ) - (κ : ℚ)) by ring] :
    ∀ j ∈ idxS1 n, (1 : ℚ) / (-((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ)) = 1 / ((j : ℚ) - (κ : ℚ)))]
  rw [Finset.sum_congr rfl (fun j _ => by
      rw [show -((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ) = ((j : ℚ) - (κ : ℚ)) by ring] :
    ∀ j ∈ (idxS2 n).erase κ, (1 : ℚ) / (-((κ : ℕ) : ℚ) + ((j : ℕ) : ℚ))
      = 1 / ((j : ℚ) - (κ : ℚ)))]
  rw [polePf2, poleLam]
  ring

/-! ## The written denominator, grouped by pole order -/

theorem idxS1_union_idxS2 (n : ℕ) : idxS1 n ∪ idxS2 n = Icc (7 * n + 1) (20 * n + 1) := by
  ext x
  simp only [idxS1, idxS2, Finset.mem_union, Finset.mem_Icc]
  omega

theorem hatDen_eval_eq (n : ℕ) (t : ℚ) :
    (hatDen n).eval t
      = (∏ κ ∈ idxS1 n, (t + (κ : ℚ))) * (∏ κ ∈ idxS2 n, (t + (κ : ℚ))) ^ 2 := by
  have hs1 : Icc (7 * n + 1) (18 * n + 1) = Icc (7 * n + 1) (9 * n) ∪ idxS2 n := by
    ext x
    simp only [idxS2, Finset.mem_union, Finset.mem_Icc]
    omega
  have hs2 : Icc (9 * n + 1) (20 * n + 1) = idxS2 n ∪ Icc (18 * n + 2) (20 * n + 1) := by
    ext x
    simp only [idxS2, Finset.mem_union, Finset.mem_Icc]
    omega
  have hd1 : Disjoint (Icc (7 * n + 1) (9 * n)) (idxS2 n) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [idxS2, Finset.mem_Icc] at hx hy
    omega
  have hd2 : Disjoint (idxS2 n) (Icc (18 * n + 2) (20 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [idxS2, Finset.mem_Icc] at hx hy
    omega
  have hdS : Disjoint (Icc (7 * n + 1) (9 * n)) (Icc (18 * n + 2) (20 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  rw [hatDen_eval, hs1, hs2, Finset.prod_union hd1, Finset.prod_union hd2, idxS1,
    Finset.prod_union hdS]
  ring

/-! ## The `Finsupp` → `Finset` reindex of `repHat`

`repHat` is a pair of `Finsupp`s built as sums of `single`s; the pole sets are `Finset`s.  This
block is the bridge: the VALUE of each family at a node, its support, and the evaluation map
rewritten as two `Finset` sums over the pole sets.  PAIR-4's `repHatA_sum`/`repHatB_sum` say
what happens to a functional APPLIED to the family; what is needed here is the family's
coefficient AT one pole, which is a different question and has no landed answer. -/

theorem sum_single_apply (c m : ℕ) (v : ℕ → ℚ) (κ : ℕ) :
    (∑ j ∈ range m, Finsupp.single (c + j) (v j)) κ
      = if c ≤ κ ∧ κ < c + m then v (κ - c) else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem (κ - c) (Finset.mem_range.2 (by omega))]
    · simp [show c + (κ - c) = κ from by omega]
    · intro j _ hj
      simp only [ite_eq_right_iff]
      exact fun hcj => absurd (show j = κ - c from by omega) hj
  · refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [ite_eq_right_iff]
    exact fun hcj => absurd hcj (by omega)

theorem repHatA_apply (n κ : ℕ) :
    repHatA n κ
      = if 10 * n + 1 ≤ κ ∧ κ < 10 * n + 1 + (8 * n + 1)
        then ((hatA n (κ - (10 * n + 1)) : ℕ) : ℚ) else 0 := by
  rw [repHatA, sum_single_apply]

theorem repHatB_apply (n κ : ℕ) :
    repHatB n κ
      = (if 10 * n + 1 ≤ κ ∧ κ < 10 * n + 1 + (8 * n + 1)
          then ((hatA n (κ - (10 * n + 1)) : ℕ) : ℚ) * hatLam n (κ - (10 * n + 1)) else 0)
        + (if 9 * n + 1 ≤ κ ∧ κ < 9 * n + 1 + n then hatBlo n (κ - (9 * n + 1)) else 0)
        + (if 18 * n + 2 ≤ κ ∧ κ < 18 * n + 2 + 2 * n
            then hatBhi n (κ - (18 * n + 2)) else 0) := by
  rw [repHatB, Finsupp.add_apply, Finsupp.add_apply, sum_single_apply, sum_single_apply,
    sum_single_apply]

theorem repHatA_support (n : ℕ) : (repHatA n).support ⊆ idxS2 n := by
  intro κ hκ
  by_contra hno
  rw [mem_idxS2] at hno
  refine (Finsupp.mem_support_iff.1 hκ) ?_
  rw [repHatA_apply]
  simp only [ite_eq_right_iff]
  exact fun h => absurd h (by omega)

theorem repHatB_support (n : ℕ) : (repHatB n).support ⊆ Icc (7 * n + 1) (20 * n + 1) := by
  intro κ hκ
  by_contra hno
  rw [Finset.mem_Icc] at hno
  refine (Finsupp.mem_support_iff.1 hκ) ?_
  rw [repHatB_apply]
  rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)),
    ite_eq_right_iff.2 (fun h => absurd h (by omega)),
    ite_eq_right_iff.2 (fun h => absurd h (by omega))]
  ring

/-- **The reindex.**  `evalRep` of the hat's family, as two `Finset` sums over the pole index
sets — the shape the cleared identity delivers. -/
theorem evalRep_repHat_eq (n : ℕ) (t : ℚ) :
    evalRep (repHat n) t
      = (∑ κ ∈ Icc (7 * n + 1) (20 * n + 1), repHatB n κ / (t + (κ : ℚ)))
        + ∑ κ ∈ idxS2 n, repHatA n κ / (t + (κ : ℚ)) ^ 2 := by
  show (repHatB n).sum (fun k b => b / (t + (k : ℚ)))
      + (repHatA n).sum (fun k a => a / (t + (k : ℚ)) ^ 2) = _
  rw [Finsupp.sum_of_support_subset _ (repHatB_support n) _ (fun i _ => by simp),
    Finsupp.sum_of_support_subset _ (repHatA_support n) _ (fun i _ => by simp)]

/-! ## The clearing — PAIR-4R modulo the residue conditions

Everything structural is discharged here.  What is left is THREE hypotheses, which across the
four-row pole table are SIX local statements about `hatA`, `hatLam`, `hatBlo` and `hatBhi` at a
pole — one per simple run, two per double run — and nothing else.  Same shape as RESID's
`partial_fractions_of_residues`, for the same reason. -/

/-- The node sums, back in index vocabulary.  Stated with `g` ABSTRACT so that unfolding
`poleS1` touches only the summation index and never the `pf1`/`pf2` arguments — rewriting the
whole occurrence set at the use site was measured to leave the cofactor lemmas unmatchable. -/
theorem sum_poleS1 (n : ℕ) (g : ℚ → ℚ) :
    ∑ x ∈ poleS1 n, g x = ∑ κ ∈ idxS1 n, g (-((κ : ℕ) : ℚ)) := by
  classical
  rw [poleS1]
  exact Finset.sum_image (fun x _ y _ h => neg_cast_inj h)

theorem sum_poleS2 (n : ℕ) (g : ℚ → ℚ) :
    ∑ x ∈ poleS2 n, g x = ∑ κ ∈ idxS2 n, g (-((κ : ℕ) : ℚ)) := by
  classical
  rw [poleS2]
  exact Finset.sum_image (fun x _ y _ h => neg_cast_inj h)

/-- The coefficient functions on ℚ NODES, read off the `Finsupp` families through the node map's
left inverse `x ↦ (−x).num.toNat`.  Named rather than `set` inside one proof: PAIR-4L reads the
TOP COEFFICIENT of the same cleared identity, so both consumers must be talking about the same
two functions. -/
noncomputable def bhat (n : ℕ) (x : ℚ) : ℚ := repHatB n ((-x).num.toNat)

/-- The order-2 twin of `bhat`. -/
noncomputable def ahat (n : ℕ) (x : ℚ) : ℚ := repHatA n ((-x).num.toNat)

theorem bhat_at (n κ : ℕ) : bhat n (-((κ : ℕ) : ℚ)) = repHatB n κ := by simp [bhat]

theorem ahat_at (n κ : ℕ) : ahat n (-((κ : ℕ) : ℚ)) = repHatA n κ := by simp [ahat]

open scoped Classical in
/-- **The CLEARED identity at the hat member**, from the three residue hypotheses — the polynomial
statement `hat_rep_of_residues` divides by the written denominator, and the one PAIR-4L reads the
top coefficient off.  Extracted rather than duplicated: the only content here is the translation
of the three index-vocabulary conditions to the ℚ nodes, and doing it twice is how the two
consumers would drift apart. -/
theorem hat_cleared (n : ℕ)
    (h₁ : ∀ κ ∈ idxS1 n, hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ))
      = repHatB n κ * polePf1 n κ)
    (h₂ : ∀ κ ∈ idxS2 n, hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ))
      = repHatA n κ * polePf2 n κ)
    (h₃ : ∀ κ ∈ idxS2 n, hatPi n * (derivative (hatNum n)).eval (-((κ : ℕ) : ℚ))
      = repHatA n κ * (polePf2 n κ * poleLam n κ) + repHatB n κ * polePf2 n κ) :
    C (hatPi n) * hatNum n
      = (∑ k ∈ poleS1 n, C (bhat n k) * Zeta2PF.pf1 (poleS1 n) (poleS2 n) k)
        + ∑ k ∈ poleS2 n, (C (bhat n k) * ((X - C k) * Zeta2PF.pf2 (poleS1 n) (poleS2 n) k)
          + C (ahat n k) * Zeta2PF.pf2 (poleS1 n) (poleS2 n) k) := by
  classical
  refine hat_partialFractions n (bhat n) (ahat n) ?_ ?_ ?_
  · -- h₁ at the ℚ nodes
    intro k hk
    rw [poleS1, Finset.mem_image] at hk
    obtain ⟨κ, hκ, rfl⟩ := hk
    rw [eval_mul, eval_C, bhat_at n κ, pf1_eval_at]
    exact h₁ κ hκ
  · -- h₂ at the ℚ nodes
    intro k hk
    rw [poleS2, Finset.mem_image] at hk
    obtain ⟨κ, hκ, rfl⟩ := hk
    rw [eval_mul, eval_C, ahat_at n κ, pf2_eval_at]
    exact h₂ κ hκ
  · -- h₃ at the ℚ nodes
    intro k hk
    rw [poleS2, Finset.mem_image] at hk
    obtain ⟨κ, hκ, rfl⟩ := hk
    rw [derivative_C_mul, eval_mul, eval_C, ahat_at n κ, bhat_at n κ, pf2_eval_at,
      pf2_derivative_eval_at n κ hκ]
    exact h₃ κ hκ

theorem hat_rep_of_residues (n : ℕ)
    (h₁ : ∀ κ ∈ idxS1 n, hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ))
      = repHatB n κ * polePf1 n κ)
    (h₂ : ∀ κ ∈ idxS2 n, hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ))
      = repHatA n κ * polePf2 n κ)
    (h₃ : ∀ κ ∈ idxS2 n, hatPi n * (derivative (hatNum n)).eval (-((κ : ℕ) : ℚ))
      = repHatA n κ * (polePf2 n κ * poleLam n κ) + repHatB n κ * polePf2 n κ)
    (t : ℚ) (ht : ∀ k ∈ Icc (7 * n + 1) (20 * n + 1), t + (k : ℚ) ≠ 0) :
    evalRep (repHat n) t = hatPi n * hatMember n t := by
  classical
  have hbv : ∀ κ : ℕ, bhat n (-((κ : ℕ) : ℚ)) = repHatB n κ := bhat_at n
  have hav : ∀ κ : ℕ, ahat n (-((κ : ℕ) : ℚ)) = repHatA n κ := ahat_at n
  have key := hat_cleared n h₁ h₂ h₃
  -- evaluate the cleared identity at `t` and divide by the written denominator
  have hne : ∀ κ ∈ idxS1 n ∪ idxS2 n, t + (κ : ℚ) ≠ 0 := by
    rw [idxS1_union_idxS2]; exact ht
  have hne1 : ∀ κ ∈ idxS1 n, t + (κ : ℚ) ≠ 0 :=
    fun κ hκ => hne κ (Finset.mem_union_left _ hκ)
  have hne2 : ∀ κ ∈ idxS2 n, t + (κ : ℚ) ≠ 0 :=
    fun κ hκ => hne κ (Finset.mem_union_right _ hκ)
  set P1 : ℚ := ∏ κ ∈ idxS1 n, (t + (κ : ℚ)) with hP1
  set P2 : ℚ := ∏ κ ∈ idxS2 n, (t + (κ : ℚ)) with hP2
  have hP1ne : P1 ≠ 0 := Finset.prod_ne_zero_iff.2 hne1
  have hP2ne : P2 ≠ 0 := Finset.prod_ne_zero_iff.2 hne2
  have hDne : (hatDen n).eval t ≠ 0 := by
    rw [hatDen_eval_eq]
    exact mul_ne_zero hP1ne (pow_ne_zero _ hP2ne)
  -- the cofactor values at a general `t`
  have hE1 : ∀ κ ∈ idxS1 n,
      (Zeta2PF.pf1 (poleS1 n) (poleS2 n) (-((κ : ℕ) : ℚ))).eval t
        = (∏ j ∈ (idxS1 n).erase κ, (t + (j : ℚ))) * P2 ^ 2 := by
    intro κ _
    rw [pf1_eq, eval_mul, eval_pow, eval_prod, eval_prod, hP2]
    simp
  have hE2 : ∀ κ ∈ idxS2 n,
      (Zeta2PF.pf2 (poleS1 n) (poleS2 n) (-((κ : ℕ) : ℚ))).eval t
        = P1 * (∏ j ∈ (idxS2 n).erase κ, (t + (j : ℚ))) ^ 2 := by
    intro κ _
    rw [pf2_eq, eval_mul, eval_pow, eval_prod, eval_prod, hP1]
    simp
  have hD1 : ∀ κ ∈ idxS1 n,
      (hatDen n).eval t = (t + (κ : ℚ)) * ((∏ j ∈ (idxS1 n).erase κ, (t + (j : ℚ))) * P2 ^ 2) := by
    intro κ hκ
    rw [hatDen_eval_eq, ← hP1, ← hP2, hP1, ← Finset.mul_prod_erase _ _ hκ]
    ring
  have hD2 : ∀ κ ∈ idxS2 n,
      (hatDen n).eval t
        = (t + (κ : ℚ)) ^ 2 * (P1 * (∏ j ∈ (idxS2 n).erase κ, (t + (j : ℚ))) ^ 2) := by
    intro κ hκ
    rw [hatDen_eval_eq, ← hP1, ← hP2, hP2, ← Finset.mul_prod_erase _ _ hκ]
    ring
  have hev := congrArg (fun p : ℚ[X] => p.eval t) key
  simp only [eval_add, eval_mul, eval_C, eval_finsetSum, eval_sub, eval_X] at hev
  rw [sum_poleS1, sum_poleS2] at hev
  -- both sides, multiplied by the written denominator
  have hmain : evalRep (repHat n) t * (hatDen n).eval t = hatPi n * (hatNum n).eval t := by
    rw [evalRep_repHat_eq, ← idxS1_union_idxS2,
      Finset.sum_union (idxS1_disjoint_idxS2 n), add_mul, add_mul,
      Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, add_assoc]
    rw [hev]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun κ hκ => ?_
      have hκne : t + (κ : ℚ) ≠ 0 := hne1 κ hκ
      rw [hD1 κ hκ, hE1 κ hκ, hbv κ]
      field_simp
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun κ hκ => ?_
      have hκne : t + (κ : ℚ) ≠ 0 := hne2 κ hκ
      rw [hD2 κ hκ, hE2 κ hκ, hbv κ, hav κ]
      field_simp
      ring
  rw [hatMember_eq_div, ← mul_div_assoc, eq_div_iff hDne]
  exact hmain

/-! ## The residue conditions the `(2t+l)` zeros make free

Two of the five cost no arithmetic at all, and both for the same reason: wherever `2κ` lands
inside `[3n+2, 20n+1]`, the numerator's own `(2t + 2κ)` factor vanishes at `t = −κ`, so the left
side of the condition is `0` — and on those runs the coefficient the right side asks for is `0`
too.  That is the design notes' claim that rows 1 and 2 of the pole table "cost nothing", as a
theorem rather than a plan.

Both are stated as the row's OWN conditions, not as a weaker statement about a vanishing
product: they are applied, not admired. -/

/-- The numerator vanishes at `t = −κ` whenever `2κ` is one of its `(2t+l)` indices. -/
theorem hatNum_eval_neg_zero (n κ : ℕ) (h1 : 3 * n + 2 ≤ 2 * κ) (h2 : 2 * κ ≤ 20 * n + 1) :
    (hatNum n).eval (-((κ : ℕ) : ℚ)) = 0 := by
  rw [hatNum_eval]
  refine mul_eq_zero_of_left ?_ _
  refine Finset.prod_eq_zero (i := 2 * κ) (Finset.mem_Icc.2 ⟨h1, h2⟩) ?_
  push_cast
  ring

/-- **`h₁` on the CANCELLED run `[7n+1, 9n]`** — half of the `4n` simple poles.  `repHatB n κ`
is `0` there because none of the three runs it is built from reaches that far left. -/
theorem hat_res_cancelled (n κ : ℕ) (hκ : κ ∈ Icc (7 * n + 1) (9 * n)) :
    hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ)) = repHatB n κ * polePf1 n κ := by
  rw [Finset.mem_Icc] at hκ
  have hB : repHatB n κ = 0 := by
    rw [repHatB_apply]
    rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)),
      ite_eq_right_iff.2 (fun h => absurd h (by omega)),
      ite_eq_right_iff.2 (fun h => absurd h (by omega))]
    ring
  rw [hatNum_eval_neg_zero n κ (by omega) (by omega), hB, mul_zero, zero_mul]

/-- **`h₂` on the LO run `[9n+1, 10n]`** — the sub-run of the DOUBLE pole set where the pole is
not genuinely double.  `2κ ∈ [18n+2, 20n]` is still inside the numerator's index range, and
`repHatA n κ = 0` because the order-2 family's support starts at `10n+1`.  The generic lemma
never asks a double pole to be genuinely double (design notes R2); this is that refutation
discharged. -/
theorem hat_res_lo_double (n κ : ℕ) (hκ : κ ∈ Icc (9 * n + 1) (10 * n)) :
    hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ)) = repHatA n κ * polePf2 n κ := by
  rw [Finset.mem_Icc] at hκ
  have hA : repHatA n κ = 0 := by
    rw [repHatA_apply]
    exact ite_eq_right_iff.2 (fun h => absurd h (by omega))
  rw [hatNum_eval_neg_zero n κ (by omega) (by omega), hA, mul_zero, zero_mul]

end Zeta2HatPoles

#print axioms Zeta2HatPoles.hatMember_eq_div
#print axioms Zeta2HatPoles.neg_cast_inj
#print axioms Zeta2HatPoles.card_poleS1
#print axioms Zeta2HatPoles.card_poleS2
#print axioms Zeta2HatPoles.poles_disjoint
#print axioms Zeta2HatPoles.natDegree_hatNum
#print axioms Zeta2HatPoles.hat_hdeg
#print axioms Zeta2HatPoles.hat_hdeg_two
#print axioms Zeta2HatPoles.hat_partialFractions
#print axioms Zeta2HatPoles.pf1_eq
#print axioms Zeta2HatPoles.pf2_eq
#print axioms Zeta2HatPoles.pf1_eval_at
#print axioms Zeta2HatPoles.pf2_eval_at
#print axioms Zeta2HatPoles.pf2_derivative_eval_at
#print axioms Zeta2HatPoles.hatDen_eval_eq
#print axioms Zeta2HatPoles.repHatA_apply
#print axioms Zeta2HatPoles.repHatB_apply
#print axioms Zeta2HatPoles.evalRep_repHat_eq
#print axioms Zeta2HatPoles.sum_poleS1
#print axioms Zeta2HatPoles.sum_poleS2
#print axioms Zeta2HatPoles.bhat_at
#print axioms Zeta2HatPoles.ahat_at
#print axioms Zeta2HatPoles.hat_cleared
#print axioms Zeta2HatPoles.hat_rep_of_residues
#print axioms Zeta2HatPoles.hatNum_eval_neg_zero
#print axioms Zeta2HatPoles.hat_res_cancelled
#print axioms Zeta2HatPoles.hat_res_lo_double
