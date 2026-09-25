/-
# Row PAIR-4R — the PRODUCT-EVALUATION atoms the residue conditions consume

`docs/future/zeta2-lean-chain.md` row PAIR-4R, §PAIR-4R design notes.

`Zeta2PartialFractions.partialFractions` reduces PAIR-4R to LOCAL residue conditions — one
evaluation per simple pole, one evaluation and one derivative per double pole.  Each of those
conditions is a product of linear factors over an `Icc` whose endpoints are linear in `n`,
evaluated at `t = −k`.  Every such product is one of exactly TWO shapes:

    ∏_{l ∈ Icc a b} (m + l)     (the factors that stay positive)
    ∏_{l ∈ Icc a b} (k − l)     (the factors that go negative, `b < k`)

and both collapse to a factorial ratio.  This file is the SIZING probe for those two atoms: the
question the row's remaining grade is about is not whether they are true but what they COST at
symbolic `n`, because the hat's four sub-products are four instances of them.

Stated multiplicatively (`… * (…)! = (…)!`) rather than as a division, so no nonvanishing side
condition travels with them and `field_simp` never has to see a factorial.

**Since 2026-09-12 this file also holds the RECIPROCAL-SUM twins of those atoms** (§Atom 2c), so
the module name `Zeta2PE` / "prod eval" now under-describes it: the same `Icc` runs appear once
as products (the residue VALUE) and once as sums of `1/(j−κ)` (the LOG-DERIVATIVE), they split
and reflect identically, and separating them would have put two halves of one bookkeeping problem
in two files.  The name is kept because every consumer cites `Zeta2PE.*` by name and a rename
buys nothing the header does not.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp

namespace Zeta2PE

open Finset Nat

set_option profiler true
set_option profiler.threshold 100

/-! ## Atom 0 — the side condition every clearing step needs -/

/-- A factorial cast is never `0`.  It lives HERE rather than beside its first caller because
every consumer of these atoms divides by one eventually: `Zeta2HatResidues` needs it a dozen
times, and `Zeta2Resid` currently spells `Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)` inline at
five sites — those are the ones to fold into this when that file is next touched, which is why
the lemma is here and not in the file that first wanted it. -/
theorem cast_factorial_ne_zero (m : ℕ) : (((m)! : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero m

/-! ## Atom 1 — the ascending product -/

/-- `∏_{l=a}^{b} (m + l) = (m+b)! / (m+a−1)!`, in cleared form.  Induction on `b`; the base is
the empty `Icc` and the step is `Finset.prod_Icc_succ_top`. -/
theorem prod_Icc_add_mul_factorial (m : ℕ) (a : ℕ) (ha : 1 ≤ a) :
    ∀ b : ℕ, a ≤ b + 1 → (∏ l ∈ Icc a b, (m + l)) * (m + a - 1)! = (m + b)! := by
  intro b
  induction b with
  | zero =>
    intro hab
    have : a = 1 := le_antisymm hab ha
    subst this
    simp
  | succ b ih =>
    intro hab
    rcases Nat.lt_or_ge b (a - 1) with h | h
    · -- `a = b + 2`: the interval is empty and both sides are `(m + b + 1)!`
      have hae : a = b + 2 := by omega
      subst hae
      rw [Finset.Icc_eq_empty (by omega)]
      simp
    · have hab' : a ≤ b + 1 := by omega
      rw [Finset.prod_Icc_succ_top hab', mul_right_comm, ih hab']
      rw [show m + (b + 1) = (m + b) + 1 by omega, Nat.factorial_succ]
      ring

/-- The ℚ-valued form, which is what the residue conditions actually meet. -/
theorem prod_Icc_add_cast (m a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∏ l ∈ Icc a b, ((m : ℚ) + (l : ℚ))) * (((m + a - 1)! : ℕ) : ℚ) = (((m + b)! : ℕ) : ℚ) := by
  have hcast : ∏ l ∈ Icc a b, ((m : ℚ) + (l : ℚ)) = ((∏ l ∈ Icc a b, (m + l) : ℕ) : ℚ) := by
    push_cast
    rfl
  rw [hcast, ← Nat.cast_mul, prod_Icc_add_mul_factorial m a ha b hab]

/-! ## Atom 2 — the descending product, where the SIGNS come from

`∏_{l=a}^{b} (k − l)` with `b < k` is the reflected ascending product.  This is the atom the hat
uses four times, and it is where a sign error would be silent: the hat's own residue is a
PRODUCT of four such reflections whose signs cancel to `+1` (PAIR-0 design notes), so an atom
that got one sign wrong would still produce a plausible closed form. -/

/-- Reflection: `∏_{l ∈ Icc a b} (k − l) = ∏_{l ∈ Icc (k−b) (k−a)} l`, over ℕ. -/
theorem prod_Icc_reflect (k a b : ℕ) (hab : a ≤ b) (hbk : b ≤ k) :
    (∏ l ∈ Icc a b, (k - l)) = ∏ l ∈ Icc (k - b) (k - a), l := by
  refine Finset.prod_nbij' (fun l => k - l) (fun l => k - l) ?_ ?_ ?_ ?_ ?_ <;>
    intro l hl <;> simp only [Finset.mem_Icc] at hl ⊢ <;> omega

/-- **The atom, in the form the residue conditions consume**: `b < k`, so every factor `k − l`
is a positive natural and the cast is faithful. -/
theorem prod_Icc_sub_cast (k a b : ℕ) (hab : a ≤ b) (hbk : b < k) :
    (∏ l ∈ Icc a b, ((k : ℚ) - (l : ℚ))) * (((k - b - 1)! : ℕ) : ℚ) = (((k - a)! : ℕ) : ℚ) := by
  have hcast : ∏ l ∈ Icc a b, ((k : ℚ) - (l : ℚ)) = ((∏ l ∈ Icc a b, (k - l) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun l hl => ?_
    simp only [Finset.mem_Icc] at hl
    rw [Nat.cast_sub (by omega)]
  rw [hcast, prod_Icc_reflect k a b hab (le_of_lt hbk), ← Nat.cast_mul]
  have h1 : 1 ≤ k - b := by omega
  have h2 : k - b ≤ (k - a) + 1 := by omega
  have := prod_Icc_add_mul_factorial 0 (k - b) h1 (k - a) h2
  simp only [Nat.zero_add] at this
  rw [Nat.cast_inj]
  exact this

/-- **The signed form**: `∏_{l=a}^{b} (l − k) = (−1)^(b+1−a) · ∏_{l=a}^{b} (k − l)`.  Every sign
in the hat's four sub-products is an instance of this, and the four cancel to `+1`.

Measured while writing it: this needs **no hypothesis at all** — not `a ≤ b`, not `b < k`.  The
first draft carried both (copied from the atom below, where `b < k` is genuinely needed for the
factorial collapse) and Lean's unused-variable linter reported them.  They are removed rather
than underscored: a lemma with decorative hypotheses tells its caller it proved something
narrower than it did, and the caller then discharges them for nothing. -/
theorem prod_Icc_sub_rev (k a b : ℕ) :
    (∏ l ∈ Icc a b, ((l : ℚ) - (k : ℚ)))
      = (-1) ^ (b + 1 - a) * (∏ l ∈ Icc a b, ((k : ℚ) - (l : ℚ))) := by
  rw [Finset.prod_congr rfl (fun l _ => by ring :
    ∀ l ∈ Icc a b, ((l : ℚ) - (k : ℚ)) = (-1) * ((k : ℚ) - (l : ℚ)))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]

/-! ## Atom 2b — splitting a run of consecutive integers AT one of its own members

Added 2026-09-12 for row RESID, and placed HERE rather than in `Zeta2Resid.lean` because the
split is generic: a product `∏_{j ∈ Icc A B, j ≠ k} (j − k)` with `A ≤ k ≤ B` is one reflected
descending run and one ascending one.  RESID meets it once, at the tale-1 member's pole window;
PAIR-4R's pole table is FOUR such runs.  Whose window it is, is the caller's business. -/

/-- `Icc a b` translated down by `k`, over ℕ.  The translation twin of `prod_Icc_reflect`, same
`prod_nbij'` shape; both hypotheses are load-bearing (at `k > b` the right-hand `Icc` would be
`Icc (a−k) 0`, which is nonempty when `a = k`). -/
theorem prod_Icc_shift (k a b : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    (∏ j ∈ Icc a b, (j - k)) = ∏ l ∈ Icc (a - k) (b - k), l := by
  refine Finset.prod_nbij' (fun j => j - k) (fun l => l + k) ?_ ?_ ?_ ?_ ?_ <;>
    intro l hl <;> simp only [Finset.mem_Icc] at hl ⊢ <;> omega

/-- **The general run BELOW the pole** — `Icc a b` lying entirely under `k`, cleared.  The top is
a PARAMETER rather than `k−1`: row PAIR-4R's pole table ends four such runs at four different
places (the numerator's `(2t+l)` range, the cancelled run, the double run, the lo run), and only
one of them stops just short of the pole.  The EMPTY case (`a = b+1`) is checked against the
arithmetic rather than excluded — there `k − b − 1 = k − a` and the sign exponent is `0`, so both
sides are `(k−a)!` on the nose. -/
theorem prod_Icc_sub_below (k a b : ℕ) (hab : a ≤ b + 1) (hbk : b < k) :
    (∏ j ∈ Icc a b, ((j : ℚ) - (k : ℚ))) * (((k - b - 1)! : ℕ) : ℚ)
      = (-1) ^ (b + 1 - a) * (((k - a)! : ℕ) : ℚ) := by
  rcases Nat.lt_or_ge b a with hlt | hge
  · have hae : a = b + 1 := by omega
    subst hae
    rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty, one_mul,
      show b + 1 - (b + 1) = 0 from by omega, pow_zero, one_mul,
      show k - (b + 1) = k - b - 1 from by omega]
  · rw [prod_Icc_sub_rev k a b, mul_assoc,
      prod_Icc_sub_cast k a b (by omega : a ≤ b) hbk]

/-- The members BELOW `k` up to `k−1`: the `b = k−1` case, where the cleared factor is `0! = 1`.
`1 ≤ A` is real — at `A = k = 0` the "empty" `Icc A (k−1)` is `Icc 0 0`, a singleton, and the
statement is false. -/
theorem prod_Icc_lt_sub (A k : ℕ) (hA1 : 1 ≤ A) (hA : A ≤ k) :
    ∏ j ∈ Icc A (k - 1), ((j : ℚ) - (k : ℚ)) = (-1) ^ (k - A) * (((k - A)! : ℕ) : ℚ) := by
  have h := prod_Icc_sub_below k A (k - 1) (by omega) (by omega)
  rw [show k - (k - 1) - 1 = 0 from by omega, Nat.factorial_zero, Nat.cast_one, mul_one,
    show k - 1 + 1 - A = k - A from by omega] at h
  exact h

/-- **The general run ABOVE the pole** — `Icc a b` lying entirely over `k`, cleared.  Every factor
is a positive natural, so no sign appears; the twin of `sum_Icc_sub_inv_above` below. -/
theorem prod_Icc_sub_above (k a b : ℕ) (hka : k < a) (hab : a ≤ b + 1) :
    (∏ j ∈ Icc a b, ((j : ℚ) - (k : ℚ))) * (((a - k - 1)! : ℕ) : ℚ) = (((b - k)! : ℕ) : ℚ) := by
  have hcast : ∏ j ∈ Icc a b, ((j : ℚ) - (k : ℚ))
      = ((∏ j ∈ Icc a b, (j - k) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [Finset.mem_Icc] at hj
    rw [Nat.cast_sub (by omega)]
  have hshift := prod_Icc_shift k a b (by omega) (by omega)
  have hfac := prod_Icc_add_mul_factorial 0 (a - k) (by omega) (b - k) (by omega)
  simp only [Nat.zero_add] at hfac
  rw [hcast, hshift, ← Nat.cast_mul, hfac]

/-- The members ABOVE `k` from `k+1`: the `a = k+1` case, where the cleared factor is `0! = 1`. -/
theorem prod_Icc_gt_sub (k B : ℕ) (hkB : k ≤ B) :
    ∏ j ∈ Icc (k + 1) B, ((j : ℚ) - (k : ℚ)) = (((B - k)! : ℕ) : ℚ) := by
  have h := prod_Icc_sub_above k (k + 1) B (by omega) (by omega)
  rw [show k + 1 - k - 1 = 0 from by omega, Nat.factorial_zero, Nat.cast_one, mul_one] at h
  exact h

/-! ## Atom 2c — the RECIPROCAL sums the log-derivative produces

Added 2026-09-12 for row PAIR-4R.  `Zeta2HatPoles.poleLam` — the log-derivative of the hat's
double-pole cofactor at its own node — is `Σ_{j ∈ S₁} 1/(j−κ) + 2·Σ_{j ∈ S₂\{κ}} 1/(j−κ)`, and
every one of those runs is an `Icc` lying entirely on ONE side of `κ`.  These are the sum twins
of atom 2's products: the same reflection and the same shift with `1/m` in place of `m`,
collapsing a run of reciprocals to a difference of harmonic numbers.  They are what
`Zeta2Hat.hatLam`'s four harmonic differences must be shown equal to.

The harmonic number is WRITTEN OUT as `∑ i ∈ range k, 1/(i+1)` so this file keeps no dependency:
`Zeta2Defs.harm 1 k` is that sum after `pow_one`, and the caller does the one rewrite. -/

/-- The harmonic number as a run of reciprocals.  Induction, not a reindex: the `Icc`-top step
lemma is the same one atom 1 uses. -/
theorem sum_range_inv_eq_Icc (k : ℕ) :
    (∑ i ∈ range k, (1 : ℚ) / ((i : ℚ) + 1)) = ∑ m ∈ Icc 1 k, (1 : ℚ) / (m : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    push_cast
    ring

/-- A run of reciprocals is a DIFFERENCE of harmonic numbers.  `1 ≤ A` is load-bearing: at
`A = 0` the left side would carry the `1/0 = 0` term and `A - 1` would truncate. -/
theorem sum_Icc_inv (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B + 1) :
    ∑ m ∈ Icc A B, (1 : ℚ) / (m : ℚ)
      = (∑ i ∈ range B, (1 : ℚ) / ((i : ℚ) + 1))
        - ∑ i ∈ range (A - 1), (1 : ℚ) / ((i : ℚ) + 1) := by
  rw [sum_range_inv_eq_Icc, sum_range_inv_eq_Icc]
  have hsplit : Icc 1 B = Icc 1 (A - 1) ∪ Icc A B := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Icc 1 (A - 1)) (Icc A B) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  rw [hsplit, Finset.sum_union hdisj]
  ring

/-- The translation twin of `prod_Icc_shift`. -/
theorem sum_Icc_shift_inv (k a b : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    (∑ j ∈ Icc a b, (1 : ℚ) / (((j - k : ℕ) : ℚ)))
      = ∑ m ∈ Icc (a - k) (b - k), (1 : ℚ) / (m : ℚ) := by
  refine Finset.sum_nbij' (fun j => j - k) (fun m => m + k) ?_ ?_ ?_ ?_ ?_ <;>
    intro l hl <;> simp only [Finset.mem_Icc] at hl ⊢ <;> omega

/-- The reflection twin of `prod_Icc_reflect`. -/
theorem sum_Icc_reflect_inv (k a b : ℕ) (hab : a ≤ b) (hbk : b ≤ k) :
    (∑ j ∈ Icc a b, (1 : ℚ) / (((k - j : ℕ) : ℚ)))
      = ∑ m ∈ Icc (k - b) (k - a), (1 : ℚ) / (m : ℚ) := by
  refine Finset.sum_nbij' (fun j => k - j) (fun m => k - m) ?_ ?_ ?_ ?_ ?_ <;>
    intro l hl <;> simp only [Finset.mem_Icc] at hl ⊢ <;> omega

/-- **The run ABOVE the pole**, in the form `poleLam` meets it.  `k < a` makes every `j − k` a
positive natural, so the cast is faithful and no sign appears. -/
theorem sum_Icc_sub_inv_above (k a b : ℕ) (hka : k < a) (hab : a ≤ b + 1) :
    ∑ j ∈ Icc a b, (1 : ℚ) / ((j : ℚ) - (k : ℚ))
      = (∑ i ∈ range (b - k), (1 : ℚ) / ((i : ℚ) + 1))
        - ∑ i ∈ range (a - k - 1), (1 : ℚ) / ((i : ℚ) + 1) := by
  have hcast : ∑ j ∈ Icc a b, (1 : ℚ) / ((j : ℚ) - (k : ℚ))
      = ∑ j ∈ Icc a b, (1 : ℚ) / (((j - k : ℕ) : ℚ)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_Icc] at hj
    rw [Nat.cast_sub (by omega)]
  rw [hcast, sum_Icc_shift_inv k a b (by omega) (by omega),
    sum_Icc_inv (a - k) (b - k) (by omega) (by omega)]

/-- **The run BELOW the pole**, where the sign lives.  The empty case (`a = b + 1`) is checked
against the arithmetic rather than assumed: `k − a` and `k − b − 1` coincide there, so the
right-hand side is `0` on the nose. -/
theorem sum_Icc_sub_inv_below (k a b : ℕ) (hab : a ≤ b + 1) (hbk : b < k) :
    ∑ j ∈ Icc a b, (1 : ℚ) / ((j : ℚ) - (k : ℚ))
      = -((∑ i ∈ range (k - a), (1 : ℚ) / ((i : ℚ) + 1))
        - ∑ i ∈ range (k - b - 1), (1 : ℚ) / ((i : ℚ) + 1)) := by
  rcases Nat.lt_or_ge b a with hlt | hge
  · have hae : a = b + 1 := by omega
    subst hae
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Nat.sub_sub]
    ring
  · have hneg : ∀ j ∈ Icc a b, (1 : ℚ) / ((j : ℚ) - (k : ℚ))
        = -((1 : ℚ) / (((k - j : ℕ) : ℚ))) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      rw [Nat.cast_sub (by omega : j ≤ k),
        show ((j : ℚ) - (k : ℚ)) = -(((k : ℚ) - (j : ℚ))) by ring, div_neg]
    rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib,
      sum_Icc_reflect_inv k a b hge (by omega),
      sum_Icc_inv (k - b) (k - a) (by omega) (by omega)]

/-! ## Atom 3 — the formal log-derivative of a product of LINEAR FORMS

The order-1 condition at a double pole is `N' (−k) = a·V'(−k) + b·V(−k)`, and `V` is a product
of linear factors, so `b` is read off from `V'(−k)/V(−k)` — a log-derivative.  Mathlib's
`logDeriv` (census 2026-09-12) is an ANALYSIS object (`Analysis/Calculus/LogDeriv.lean`, over a
differentiable `𝕜 → 𝕜'`) and `FieldTheory/Differential`'s is a derivation on a field; **neither
is a formal log-derivative of a `Polynomial ℚ`**, and going through either would drag an
analytic structure onto an identity that is pure ℚ-algebra.  So it is this, from
`Polynomial.derivative_prod_finset`.

Both factor shapes the hat member has are covered by the ONE lemma: `c i = 1` gives the `(t+l)`
factors, `c i = 2` the `(2t+l)` ones — and it is the `c i` in the numerator of the summand that
becomes the `−2·(H − H)` of `Zeta2Hat.hatLam`'s first term. -/

theorem eval_derivative_prod_linear {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c d : ι → ℚ) (t : ℚ) (h : ∀ i ∈ s, c i * t + d i ≠ 0) :
    (Polynomial.derivative (∏ i ∈ s, (Polynomial.C (c i) * Polynomial.X + Polynomial.C (d i)))).eval t
      = (∏ i ∈ s, (c i * t + d i)) * ∑ i ∈ s, c i / (c i * t + d i) := by
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    Polynomial.derivative_C, add_zero, mul_one, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]
  have hi' : c i * t + d i ≠ 0 := h i hi
  -- `field_simp` on the whole goal was measured to FAIL here: it `ring_nf`s the product BODY to
  -- `t * c x + d x`, which no longer matches `hi'`, and leaves the inverse standing.  Cancelling
  -- the one factor by hand keeps the product opaque.
  have key : (c i * t + d i) * (c i / (c i * t + d i)) = c i := by field_simp
  rw [← Finset.mul_prod_erase s (fun i => c i * t + d i) hi,
    mul_comm (c i * t + d i) (∏ x ∈ s.erase i, (c x * t + d x)), mul_assoc, key]

end Zeta2PE

#print axioms Zeta2PE.cast_factorial_ne_zero
#print axioms Zeta2PE.prod_Icc_add_mul_factorial
#print axioms Zeta2PE.prod_Icc_add_cast
#print axioms Zeta2PE.prod_Icc_reflect
#print axioms Zeta2PE.prod_Icc_sub_cast
#print axioms Zeta2PE.prod_Icc_sub_rev
#print axioms Zeta2PE.prod_Icc_shift
#print axioms Zeta2PE.prod_Icc_sub_below
#print axioms Zeta2PE.prod_Icc_lt_sub
#print axioms Zeta2PE.prod_Icc_sub_above
#print axioms Zeta2PE.prod_Icc_gt_sub
#print axioms Zeta2PE.sum_range_inv_eq_Icc
#print axioms Zeta2PE.sum_Icc_inv
#print axioms Zeta2PE.sum_Icc_shift_inv
#print axioms Zeta2PE.sum_Icc_reflect_inv
#print axioms Zeta2PE.sum_Icc_sub_inv_above
#print axioms Zeta2PE.sum_Icc_sub_inv_below
#print axioms Zeta2PE.eval_derivative_prod_linear
