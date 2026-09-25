/-
# Row PAIR-3, first half — `evalRep` and `Φ̂` are LINEAR AS MAPS

`docs/future/zeta2-lean-chain.md` row PAIR-3.  PAIR-4 landed `Rep̂`, `evalRep` and `Φ̂`, and
PAIR-4L/4C consumed `Φ̂` only COORDINATEWISE — through `repHatA_sum`/`repHatB_sum`, which are
additivity in the coefficient VALUE at a fixed family.  Neither needed `Φ̂` to be additive as a
MAP `Rep̂ → ℚ³`, which is why PAIR-3 stayed at MED when the whole PAIR-4 block closed.

`Σⱼ αⱼ · Φ̂ rⱼ = Φ̂ (Σⱼ αⱼ · rⱼ)` is what PAIR-6 applies: the (★) telescoping gives a linear
relation among the hat MEMBERS, and the recurrence on `(hatP, hatQ)` is that relation pushed
through `Φ̂`.  This file proves it, and the same three facts for `evalRep`, which is what carries
the relation from the members to `Rep̂` in the first place (with PAIR-3's other half,
`rep̂_injective`).

**No poles anywhere in this file.**  `evalRep` divides by `t + k`, and in ℚ `b / 0 = 0`, so
`evalRep · t` is linear at EVERY `t`, pole or not — the hypothesis-free form is the true one and
the callers are spared a side condition they would otherwise thread.  That is a property of
Lean's division, stated here because it looks like an oversight and is not.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2HatRep

namespace Zeta2HatLinear

open Zeta2Defs Zeta2Hat Zeta2HatRep Finset

/-! ## The two `Finsupp.sum` facts every coordinate uses

Both are one line on top of Mathlib; they are named here because the five functionals `evalRep`
and `Φ̂` apply differ only in their weight, and stating the hypotheses once is what keeps the
five proofs below to two lines each. -/

theorem sum_add (g : ℕ → ℚ → ℚ) (h0 : ∀ k, g k 0 = 0)
    (hadd : ∀ k b₁ b₂, g k (b₁ + b₂) = g k b₁ + g k b₂) (f₁ f₂ : ℕ →₀ ℚ) :
    (f₁ + f₂).sum g = f₁.sum g + f₂.sum g :=
  Finsupp.sum_add_index' h0 hadd

theorem sum_smul (g : ℕ → ℚ → ℚ) (h0 : ∀ k, g k 0 = 0)
    (hsmul : ∀ k (c b : ℚ), g k (c * b) = c * g k b) (c : ℚ) (f : ℕ →₀ ℚ) :
    (c • f).sum g = c * f.sum g := by
  rw [Finsupp.sum_smul_index' h0]
  simp only [smul_eq_mul, hsmul]
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]

/-! ## `evalRep` -/

theorem evalRep_add (r s : Rephat) (t : ℚ) :
    evalRep (r + s) t = evalRep r t + evalRep s t := by
  show (r.1 + s.1).sum _ + (r.2 + s.2).sum _ = _
  rw [sum_add (g := fun k b => b / (t + (k : ℚ))) (fun _ => zero_div _)
        (fun _ b₁ b₂ => add_div b₁ b₂ _),
      sum_add (g := fun k a => a / (t + (k : ℚ)) ^ 2) (fun _ => zero_div _)
        (fun _ b₁ b₂ => add_div b₁ b₂ _)]
  unfold evalRep
  ring

theorem evalRep_smul (c : ℚ) (r : Rephat) (t : ℚ) :
    evalRep (c • r) t = c * evalRep r t := by
  show (c • r.1).sum _ + (c • r.2).sum _ = _
  rw [sum_smul (g := fun k b => b / (t + (k : ℚ))) (fun _ => zero_div _)
        (fun _ c' b => mul_div_assoc c' b _),
      sum_smul (g := fun k a => a / (t + (k : ℚ)) ^ 2) (fun _ => zero_div _)
        (fun _ c' b => mul_div_assoc c' b _)]
  unfold evalRep
  ring

theorem evalRep_zero (t : ℚ) : evalRep (0 : Rephat) t = 0 := by
  show (0 : ℕ →₀ ℚ).sum _ + (0 : ℕ →₀ ℚ).sum _ = 0
  simp

theorem evalRep_sub (r s : Rephat) (t : ℚ) :
    evalRep (r - s) t = evalRep r t - evalRep s t := by
  have h : r - s = r + (-1 : ℚ) • s := by
    rw [neg_one_smul]; abel
  rw [h, evalRep_add, evalRep_smul]
  ring

/-- **`Σᵢ αᵢ · evalRep rᵢ = evalRep (Σᵢ αᵢ · rᵢ)`** — the form PAIR-6's (★) relation arrives in. -/
theorem evalRep_sum {ι : Type*} (s : Finset ι) (α : ι → ℚ) (r : ι → Rephat) (t : ℚ) :
    evalRep (∑ i ∈ s, α i • r i) t = ∑ i ∈ s, α i * evalRep (r i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalRep_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, evalRep_add, evalRep_smul, ih]

/-! ## `Φ̂`

The ζ(2) and ln 2 coordinates apply `fun _ a => a`, whose three hypotheses are all `rfl`; the
rational coordinate applies two weighted functionals and carries the `2 *`. -/

theorem Phihat_add (N : ℕ) (r s : Rephat) :
    Phihat N (r + s) = Phihat N r + Phihat N s := by
  have h1 : ∀ (w : ℕ → ℚ) (f₁ f₂ : ℕ →₀ ℚ),
      (f₁ + f₂).sum (fun k b => b * w k)
        = f₁.sum (fun k b => b * w k) + f₂.sum (fun k b => b * w k) :=
    fun w => sum_add _ (fun k => zero_mul (w k)) (fun k b₁ b₂ => add_mul b₁ b₂ (w k))
  have h2 : ∀ f₁ f₂ : ℕ →₀ ℚ,
      (f₁ + f₂).sum (fun _ b => b) = f₁.sum (fun _ b => b) + f₂.sum (fun _ b => b) :=
    sum_add (g := fun _ b => b) (fun _ => rfl) (fun _ _ _ => rfl)
  simp only [Phihat, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]
  rw [h1, h1, h2, h2]
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  simp only []
  ring

theorem Phihat_smul (N : ℕ) (c : ℚ) (r : Rephat) :
    Phihat N (c • r) = c • Phihat N r := by
  have h1 : ∀ (w : ℕ → ℚ) (f : ℕ →₀ ℚ),
      (c • f).sum (fun k b => b * w k) = c * f.sum (fun k b => b * w k) :=
    fun w => sum_smul _ (fun k => zero_mul (w k)) (fun k c' b => by ring) c
  have h2 : ∀ f : ℕ →₀ ℚ, (c • f).sum (fun _ b => b) = c * f.sum (fun _ b => b) :=
    sum_smul (g := fun _ b => b) (fun _ => rfl) (fun _ _ _ => rfl) c
  simp only [Phihat, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [h1, h1, h2, h2]
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  simp only []
  ring

theorem Phihat_zero (N : ℕ) : Phihat N (0 : Rephat) = 0 := by
  simp [Phihat, Prod.ext_iff]

/-- The twin of `evalRep_sub`, and it lives here for the same reason that one does: PAIR-5's
`repDelta r = shiftRep r − r` is a DIFFERENCE of representations, and a second derivation of
`Φ̂ (r − s)` in the row that needs it would be exactly the drift this file exists to prevent. -/
theorem Phihat_sub (N : ℕ) (r s : Rephat) :
    Phihat N (r - s) = Phihat N r - Phihat N s := by
  have h : r - s = r + (-1 : ℚ) • s := by
    rw [neg_one_smul]; abel
  rw [h, Phihat_add, Phihat_smul, neg_one_smul]
  abel

/-- **`Σᵢ αᵢ · Φ̂ rᵢ = Φ̂ (Σᵢ αᵢ · rᵢ)`** — row PAIR-3's headline, and what PAIR-6 pushes the
(★) relation through to get the recurrence on `(hatP, hatQ)`. -/
theorem Phihat_sum {ι : Type*} (N : ℕ) (s : Finset ι) (α : ι → ℚ) (r : ι → Rephat) :
    Phihat N (∑ i ∈ s, α i • r i) = ∑ i ∈ s, α i • Phihat N (r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Phihat_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Phihat_add, Phihat_smul, ih]

end Zeta2HatLinear

#print axioms Zeta2HatLinear.sum_add
#print axioms Zeta2HatLinear.sum_smul
#print axioms Zeta2HatLinear.evalRep_add
#print axioms Zeta2HatLinear.evalRep_smul
#print axioms Zeta2HatLinear.evalRep_sub
#print axioms Zeta2HatLinear.evalRep_sum
#print axioms Zeta2HatLinear.Phihat_add
#print axioms Zeta2HatLinear.Phihat_smul
#print axioms Zeta2HatLinear.Phihat_sub
#print axioms Zeta2HatLinear.Phihat_sum
