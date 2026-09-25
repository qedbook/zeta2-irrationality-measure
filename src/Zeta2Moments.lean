/-
# Rows A2 and B2 of the μ(ζ(2)) ≤ 5.0495243 chain

A2 — the moment recursion `I` of `docs/future/zeta2-integral-free.md` §5.2, and
B2 — the SHIFT LEMMA of §2.1/§2.2, on both bases the evaluator uses.

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox;
Lean never runs on the laptop (owner ruling 2026-09-07).
-/
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp

namespace Zeta2Moments

open Finset

/-! ## A2 — the moment recursion `I` -/

/-- **A2 — the in-cell moment recursion.**  `momI M j` is the moment `I_j(C)` of the
Mellin–Barnes evaluator's cell `M`, i.e. the value the contour functional takes on the
monomial `t ↦ t^j`.  This is the four-line recursion of `zeta2-integral-free.md` §5.2,
transcribed with the index shift `j ↦ j−1` that makes it a recursion on `j` itself:

`I_j = (M+1)^j − (1/(j+1)) · Σ_{i<j} C(j+1, i) · I_i`,

which at `j = 0` reads `I_0 = 1` (`momI_zero`). -/
noncomputable def momI (M : ℤ) : ℕ → ℚ
  | j => ((M : ℚ) + 1) ^ j -
      (1 / (j + 1 : ℚ)) * ∑ i : Fin j, ((j + 1).choose (i : ℕ) : ℚ) * momI M (i : ℕ)
  decreasing_by exact i.isLt

/-- The defining equation of `momI`, with the recursive sum written over `Finset.range`. -/
theorem momI_eq (M : ℤ) (j : ℕ) :
    momI M j = ((M : ℚ) + 1) ^ j -
      (1 / (j + 1 : ℚ)) * ∑ i ∈ range j, ((j + 1).choose i : ℚ) * momI M i := by
  rw [momI, Fin.sum_univ_eq_sum_range (fun i => ((j + 1).choose i : ℚ) * momI M i) j]

/-- `I 0 = 1` — the initial condition named in `zeta2-integral-free.md` §5.2.  It is not an
extra axiom of the definition: the recursion's own empty sum delivers it. -/
theorem momI_zero (M : ℤ) : momI M 0 = 1 := by
  rw [momI_eq]; simp

/-- The recursion in cleared binomial form: `Σ_{i≤j} C(j+1,i) I_i = (j+1)(M+1)^j`.  This is
the shape every consumer wants, and the whole of B2's monomial half falls out of it. -/
theorem momI_binom_sum (M : ℤ) (j : ℕ) :
    ∑ i ∈ range (j + 1), ((j + 1).choose i : ℚ) * momI M i
      = ((j : ℚ) + 1) * ((M : ℚ) + 1) ^ j := by
  have hne : ((j : ℚ) + 1) ≠ 0 := by positivity
  have h := momI_eq M j
  have hS : ∑ i ∈ range j, ((j + 1).choose i : ℚ) * momI M i
      = ((j : ℚ) + 1) * (((M : ℚ) + 1) ^ j - momI M j) := by
    field_simp at h
    linarith
  rw [Finset.sum_range_succ, hS, Nat.choose_succ_self_right]
  push_cast
  ring

/-- **The moments are Bernoulli polynomial values** — `I_j(M) = B_j(M+1)`.

A `LEAN.md` §2 find, not a construction: the object A2 asks for is already in Mathlib, and
`Polynomial.sum_bernoulli` is *the same recursion*.  Recording the identification buys the
chain the whole `Polynomial.bernoulli` API for free. -/
theorem momI_eq_bernoulli (M : ℤ) (j : ℕ) :
    momI M j = (Polynomial.bernoulli j).eval ((M : ℚ) + 1) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have h := congrArg (Polynomial.eval ((M : ℚ) + 1)) (Polynomial.sum_bernoulli j)
    rw [Polynomial.eval_finsetSum, Polynomial.eval_monomial] at h
    have hB : ∑ k ∈ range (j + 1), ((j + 1).choose k : ℚ) *
        (Polynomial.bernoulli k).eval ((M : ℚ) + 1) = ((j : ℚ) + 1) * ((M : ℚ) + 1) ^ j := by
      rw [← h]
      exact Finset.sum_congr rfl fun k _ => by simp
    have hI := momI_binom_sum M j
    rw [Finset.sum_range_succ] at hB hI
    have hrest : ∑ k ∈ range j, ((j + 1).choose k : ℚ) * momI M k
        = ∑ k ∈ range j, ((j + 1).choose k : ℚ) *
            (Polynomial.bernoulli k).eval ((M : ℚ) + 1) :=
      Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_range.mp hk)]
    rw [hrest] at hI
    have hc : ((j + 1).choose j : ℚ) = (j : ℚ) + 1 := by
      rw [Nat.choose_succ_self_right]; push_cast; ring
    rw [hc] at hB hI
    have hne : ((j : ℚ) + 1) ≠ 0 := by positivity
    have hcancel : ((j : ℚ) + 1) * momI M j
        = ((j : ℚ) + 1) * (Polynomial.bernoulli j).eval ((M : ℚ) + 1) := by linarith
    exact mul_left_cancel₀ hne hcancel

/-! ## B2 — the shift lemma, monomial basis -/

/-- **B2, monomial basis.**  `ℒ(ρ(·+1)) − ℒ(ρ) = ρ′(M+1)` for `ρ = t^j`: the left side is the
binomial expansion of the shifted monomial against the moments, the right side is the strip
residue at the one integer `M+1` of the cell `(C, C+1)`.

`zeta2-integral-free.md` §2.1: *"on the basis `{t^j}` the moment recursion IS the shift
identity"* — and that is literally what this proof is, `momI_binom_sum` re-indexed. -/
theorem shift_monomial (M : ℤ) (j : ℕ) :
    (∑ i ∈ range (j + 1), (j.choose i : ℚ) * momI M i) - momI M j
      = (j : ℚ) * ((M : ℚ) + 1) ^ (j - 1) := by
  cases j with
  | zero => simp [momI_zero]
  | succ k =>
    have hexp : k + 1 - 1 = k := rfl
    rw [Finset.sum_range_succ, Nat.choose_self, hexp]
    have h := momI_binom_sum M k
    push_cast
    linarith

/-! ## B2 — the shift lemma, polynomial parts -/

/-- The moment functional on polynomial parts: `ℒ(∑ a_i t^i) = ∑ a_i I_i`. -/
noncomputable def Lpoly (M : ℤ) (p : Polynomial ℚ) : ℚ :=
  p.sum fun i a => a * momI M i

/-- `ℒ` on a monomial. -/
theorem Lpoly_monomial (M : ℤ) (j : ℕ) (a : ℚ) :
    Lpoly M (Polynomial.monomial j a) = a * momI M j := by
  simp [Lpoly, Polynomial.sum_monomial_index]

/-- `ℒ` kills `0`. -/
theorem Lpoly_zero (M : ℤ) : Lpoly M 0 = 0 := by
  simp [Lpoly]

/-- `ℒ` is additive. -/
theorem Lpoly_add (M : ℤ) (p q : Polynomial ℚ) :
    Lpoly M (p + q) = Lpoly M p + Lpoly M q :=
  Polynomial.sum_add_index p q _ (fun i => by ring) (fun a b₁ b₂ => by ring)

/-- `ℒ` commutes with finite sums. -/
theorem Lpoly_sum (M : ℤ) {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) :
    Lpoly M (∑ i ∈ s, f i) = ∑ i ∈ s, Lpoly M (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Lpoly_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Lpoly_add, ih, Finset.sum_insert hi]

/-- **B2 — THE SHIFT LEMMA on polynomial parts.**

`ℒ(ρ(·+1)) − ℒ(ρ) = ρ′(M+1)` for every `ρ ∈ ℚ[t]`.  This is the §2.2 statement
`ℒ(ρ(·+1)) − ℒ(ρ) = ρ′(0)` at the chain's cell `M = −1` (`C = −1/2`), stated at a general
cell: `M+1` is the one integer of the open strip `(C, C+1)`, and the right-hand side is the
residue of `ρ·w` there, `w = (π/sin πt)²` having principal part `(t−(M+1))^{-2}`.

No Cauchy theorem, no decay estimate, no contour: finite algebra, exactly as §2.1 claims. -/
theorem Lpoly_shift (M : ℤ) (p : Polynomial ℚ) :
    Lpoly M (p.comp (Polynomial.X + 1)) - Lpoly M p
      = (Polynomial.derivative p).eval ((M : ℚ) + 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, Lpoly_add, Lpoly_add, Polynomial.derivative_add,
        Polynomial.eval_add]
      linarith
  | monomial j a =>
      have hcomp : (Polynomial.monomial j a).comp (Polynomial.X + 1)
          = ∑ i ∈ range (j + 1), Polynomial.monomial i (a * (j.choose i : ℚ)) := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
          Polynomial.X_pow_comp, add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_eq_natCast]
        rw [Polynomial.C_mul, one_pow]
        ring
      have hsum : Lpoly M (∑ i ∈ range (j + 1), Polynomial.monomial i (a * (j.choose i : ℚ)))
          = a * ∑ i ∈ range (j + 1), (j.choose i : ℚ) * momI M i := by
        rw [Lpoly_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Lpoly_monomial]; ring
      have hd : (Polynomial.derivative (Polynomial.monomial j a)).eval ((M : ℚ) + 1)
          = a * ((j : ℚ) * ((M : ℚ) + 1) ^ (j - 1)) := by
        simp [Polynomial.derivative_monomial, Polynomial.eval_monomial]; ring
      rw [hcomp, hsum, Lpoly_monomial, hd, ← mul_sub, shift_monomial]

/-! ## B2 — the shift lemma, pole basis -/

/-- The truncated `s`-th order harmonic number `H^{(s)}_k = Σ_{i=1}^{k} 1/i^s`. -/
def harm (s k : ℕ) : ℚ := ∑ i ∈ range k, 1 / ((i : ℚ) + 1) ^ s

/-- Telescoping of `H^{(s)}` — the identity `zeta2-integral-free.md` §2.1 names as the shift
lemma's content on the pole basis. -/
theorem harm_succ_sub (s k : ℕ) : harm s (k + 1) - harm s k = 1 / ((k : ℚ) + 1) ^ s := by
  simp [harm, Finset.sum_range_succ]

/-- `W₁(−k; C) = ζ(2) − H^{(2)}_{k+⌊C⌋}` at the chain's cell `C = −1/2` (`⌊C⌋ = −1`), with
ζ(2) carried abstractly as `z`: the shift lemma below never uses its value, which is exactly
why the pole half of B2 is finite algebra. -/
def Wone (z : ℚ) (k : ℕ) : ℚ := z - harm 2 (k - 1)

/-- **B2, pole basis.**  `ℒ(ρ(·+1)) − ℒ(ρ) = ρ′(0) = −1/k²` for `ρ = 1/(t+k)`, `k ≥ 1`.
ζ(2) cancels, leaving a telescoping of `H^{(2)}`. -/
theorem Wone_shift (z : ℚ) (k : ℕ) (hk : 1 ≤ k) :
    Wone z (k + 1) - Wone z k = -(1 / (k : ℚ) ^ 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : 1 + m + 1 - 1 = m + 1 := by omega
  have h2 : 1 + m - 1 = m := by omega
  rw [Wone, Wone, h1, h2]
  have h := harm_succ_sub 2 m
  push_cast
  ring_nf
  ring_nf at h
  linarith

/-- The analytic side of `Wone_shift`, so that "`= ρ′(0)`" is a proved statement and not a
comment: `ρ(t) = 1/(t+k)` really does have derivative `−1/k²` at `0`, for `k ≥ 1`. -/
theorem hasDerivAt_pole_basis (k : ℕ) (hk : 1 ≤ k) :
    HasDerivAt (fun t : ℝ => 1 / (t + (k : ℝ))) (-(1 / (k : ℝ) ^ 2)) 0 := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hne : (0 : ℝ) + (k : ℝ) ≠ 0 := by rw [zero_add]; exact ne_of_gt hk'
  have hbase : HasDerivAt (fun t : ℝ => t + (k : ℝ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).add_const ((k : ℝ))
  have h := HasDerivAt.inv hbase hne
  rw [zero_add] at h
  have hfun : (fun t : ℝ => 1 / (t + (k : ℝ))) = (fun t : ℝ => t + (k : ℝ))⁻¹ := by
    funext t; simp [one_div]
  have hval : -(1 / (k : ℝ) ^ 2) = -1 / (k : ℝ) ^ 2 := by ring
  rw [hfun, hval]
  exact h

/-! ## Controls and falsifiers (MEASURED off-Lean in §2.2, re-checked here) -/

/-- MB-K0 control: `I₀ = 1` at the chain's cell `M = −1`. -/
theorem momI_control_zero : momI (-1) 0 = 1 := by
  rw [momI_eq]; norm_num

/-- MB-K0 control: `I₁ = −1/2`. -/
theorem momI_control_one : momI (-1) 1 = -(1 / 2) := by
  rw [momI_eq]; norm_num [Finset.sum_range_succ, momI_zero]

/-- MB-K0 control: `I₂ = 1/6`. -/
theorem momI_control_two : momI (-1) 2 = 1 / 6 := by
  rw [momI_eq]
  norm_num [Finset.sum_range_succ, momI_zero, momI_control_one]

/-- MB-K0 control: `W₁(−1; −1/2) = ζ(2) − H^{(2)}_0 = ζ(2)`. -/
theorem Wone_control_one (z : ℚ) : Wone z 1 = z := by
  simp [Wone, harm]

/-- MB-K0 control: `W₁(−2; −1/2) = ζ(2) − 1`. -/
theorem Wone_control_two (z : ℚ) : Wone z 2 = z - 1 := by
  norm_num [Wone, harm, Finset.sum_range_succ]

/-- MB-K0 control: `W₁(−5; −1/2) = ζ(2) − 205/144`. -/
theorem Wone_control_five (z : ℚ) : Wone z 5 = z - 205 / 144 := by
  norm_num [Wone, harm, Finset.sum_range_succ]

/-- **Falsifier (K-SHIFT, "corrupting the W index by one breaks the lemma").**  A theorem,
not a failed tactic: the off-by-one form is refuted at `k = 1`. -/
theorem Wone_shift_off_by_one_false :
    ¬ ∀ (z : ℚ) (k : ℕ), 1 ≤ k → Wone z (k + 1) - Wone z k = -(1 / ((k : ℚ) + 1) ^ 2) := by
  intro h
  have := h 0 1 le_rfl
  rw [Wone_control_two, Wone_control_one] at this
  norm_num at this

/-- **Falsifier.**  The moments are not the naive `I_j = (M+1)^j`: the recursive correction
is real already at `j = 1`. -/
theorem momI_ne_naive_pow : momI (-1) 1 ≠ ((-1 : ℚ) + 1) ^ 1 := by
  rw [momI_control_one]; norm_num

/-- **Edge case (`LEAN.md` §5), recorded rather than assumed away.**  `Wone_shift`'s
hypothesis `1 ≤ k` is mathematically necessary — `ρ = 1/t` has its pole AT the strip integer,
so the functional is not defined there — but it is Lean-VACUOUS: at `k = 0` both sides
collapse to `0` by junk values (`0 - 1 = 0` in ℕ and `1/0 = 0` in ℚ), so a version of the
lemma stated without the hypothesis would elaborate green and mean nothing.  The hypothesis
is kept because the caller must supply it, not because Lean forces it. -/
theorem Wone_shift_zero_is_junk (z : ℚ) :
    Wone z (0 + 1) - Wone z 0 = 0 ∧ -(1 / (0 : ℚ) ^ 2) = 0 := by
  constructor
  · simp [Wone, harm]
  · norm_num

/-! ## Receipts (`LEAN.md` §1 — exit 0 is not an attestation) -/

#print axioms momI_zero
#print axioms momI_eq
#print axioms momI_binom_sum
#print axioms momI_eq_bernoulli
#print axioms shift_monomial
#print axioms Lpoly_shift
#print axioms harm_succ_sub
#print axioms Wone_shift
#print axioms hasDerivAt_pole_basis
#print axioms momI_control_zero
#print axioms momI_control_one
#print axioms momI_control_two
#print axioms Wone_control_one
#print axioms Wone_control_two
#print axioms Wone_control_five
#print axioms Wone_shift_off_by_one_false
#print axioms momI_ne_naive_pow
#print axioms Wone_shift_zero_is_junk

end Zeta2Moments
