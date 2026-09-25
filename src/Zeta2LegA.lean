/-
# D5 leg A — the clearing-denominator limit `(1/n)·log(D_{γ₁n}·D_{γ₂n}) → γ₁ + γ₂`

D5 is the pair of PNT-class limits L10 consumes.  Leg B (the profile-density limit,
`Zeta2LegBComplete.legB_candidate_from_psi`) is closed.  **Leg A had no Lean artifact at all** —
`zeta2-integral-free.md` §5.3 row D5 graded it "cite `PrimeNumberTheoremAnd`" and nothing was
built.  This file builds it, and the build is small because Mathlib turns out to carry the one
bridge that makes it small.

**Leg A is `lim (1/n)·log(D_{16n}·D_{15n}) = 31`** for the candidate `γ = (16, 15)`
(`zeta2-soft-links.md` §2), where `D_m = lcm(1,…,m)`.

**Three measured findings, in the order they change the row's size.**

1. **`Nat.lcmUpto` IS `D_m`, and `Chebyshev.psi_eq_log_lcmUpto` is the bridge** —
   `ψ n = log (lcmUpto n)` is already in current Mathlib
   (`Mathlib/NumberTheory/Chebyshev.lean`).  So leg A never has to reason about `lcm` at all:
   it is a statement about `ψ` from the first line.  Row D5 recorded `lcmUpto`'s presence but
   not this identity, which is the part that removes the work.  ⟦Namespace trap, measured: the
   file is `NumberTheory/Chebyshev.lean` but `lcmUpto` lives in an interleaved `namespace Nat`
   block, so it is **`Nat.lcmUpto`** — `Chebyshev.lcmUpto` is an unknown identifier.  Costed one
   probe cycle; the neighbouring `psi_eq_log_lcmUpto` IS `Chebyshev.`-qualified.⟧
2. **Leg A needs only `ψ(x)/x → 1`** — bare PNT.  Leg B's §1 refutation (bare PNT is NOT enough
   there, because the harmonic sum over `√n` blocks eats a logarithm) is a fact about leg B and
   does not transfer: leg A has no block decomposition and no harmonic sum.
3. **AND THAT INPUT IS ALREADY DISCHARGED.**  `psiAsymptotic_of_psiErrorBound` derives
   `ψ(x)/x → 1` from the very hypothesis leg B consumes — `PsiErrorBound.psiErrorBoundStatement`,
   proved on `PrimeNumberTheoremAnd` from `MediumPNT` with an archived
   `#print axioms` receipt (`out_axioms_psi_error_bound.txt`).  **So leg A adds no external
   citation to the campaign**: both legs of D5 rest on the same one, and it already has a
   receipt.  That is a stronger statement than "cite PNT+", and it is the reason this row is a
   short file rather than a second cross-toolchain interface.

Everything below is proved against CURRENT Mathlib alone (LEAN.md §7 — the external result
enters as a hypothesis stated in shared `Chebyshev` vocabulary, never as an import).

Probe: `bash run_probe.sh Zeta2LegA.lean`.  Lean never runs on the laptop (owner rule
2026-09-07).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace Zeta2LegA

/-! ## §1. The two interface statements

Both are written out here as `def`s rather than inlined, so the kernel can be asked whether the
statement this file consumes is the statement the other project proves (LEAN.md §1 — the D5 fork
was once answered about the wrong theorem). -/

/-- **Leg B's interface statement, written out a third time.**  Byte-identical to
`PsiErrorBound.psiErrorBoundStatement` (PNT+, `v4.32.2`) and to
`Zeta2PsiInterface.psiErrorBoundStatement` (current Mathlib).  It is `MediumPNT`'s rate on `ψ`. -/
def psiErrorBoundStatement : Prop := ∃ c > 0, ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
    |Chebyshev.psi x - x| ≤ C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x

/-- **Leg A's own input: bare PNT in the `ψ` normalisation, `ψ(x)/x → 1`.**  Strictly weaker than
`psiErrorBoundStatement` (§2 proves the implication), and it is all leg A uses. -/
def psiAsymptoticStatement : Prop :=
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)

/-! ## §2. Leg A's input is implied by leg B's — so D5 rests on ONE citation, not two -/

/--
**Leg A needs no citation of its own.**  `MediumPNT`'s rate — the hypothesis leg B already
consumes and which is discharged on `PrimeNumberTheoremAnd` with an axiom receipt — gives
`ψ(x)/x → 1` outright: dividing `|ψ x − x| ≤ C·e(x)·x` by `x > 0` leaves `|ψ x/x − 1| ≤ C·e(x)`,
and `e(x) = exp(−c(log x)^{1/10}) → 0` because `(log x)^{1/10} → ∞`.
-/
theorem psiAsymptotic_of_psiErrorBound (h : psiErrorBoundStatement) : psiAsymptoticStatement := by
  obtain ⟨c, hc, C, hC⟩ := h
  have hrpow : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hcy : Tendsto (fun x : ℝ => c * (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc hrpow
  have hneg : Tendsto (fun x : ℝ => -c * (Real.log x) ^ ((1 : ℝ) / 10)) atTop atBot := by
    simpa using hcy
  have hexp : Tendsto (fun x : ℝ => C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul C
  have key : Tendsto (fun x : ℝ => Chebyshev.psi x / x - 1) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    have e : Chebyshev.psi x / x - 1 = (Chebyshev.psi x - x) / x := by
      field_simp
    rw [Real.norm_eq_abs, e, abs_div, abs_of_pos hxpos, div_le_iff₀ hxpos]
    exact hx
  have final : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := by
    simpa using key.add_const 1
  exact final

/-! ## §3. The limit, for an arbitrary positive scale -/

/--
**One scale.**  `ψ(γ·n)/n → γ` for every `γ > 0`, from `ψ(x)/x → 1` along the subsequence
`x = γ·n`.  The division is by `n`, NOT by `γ·n`: that is what makes the limit `γ` rather
than `1`, and it is the normalisation L10 uses.
-/
theorem psi_scaled_tendsto (hpsi : psiAsymptoticStatement) {γ : ℕ} (hγ : 0 < γ) :
    Tendsto (fun n : ℕ => Chebyshev.psi ((γ : ℝ) * (n : ℝ)) / (n : ℝ)) atTop
      (nhds (γ : ℝ)) := by
  have hγ0 : (0 : ℝ) < (γ : ℝ) := by exact_mod_cast hγ
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => (γ : ℝ) * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hγ0 hnat
  have h1 : Tendsto (fun n : ℕ => Chebyshev.psi ((γ : ℝ) * (n : ℝ)) / ((γ : ℝ) * (n : ℝ)))
      atTop (nhds 1) := hpsi.comp hmul
  have h2 := h1.const_mul (γ : ℝ)
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/--
**Two scales.**  `(ψ(γ₁n) + ψ(γ₂n))/n → γ₁ + γ₂`.  This is leg A in `ψ` vocabulary, for an
arbitrary member's `γ` pair rather than only the candidate's.
-/
theorem legA_psi_sum (hpsi : psiAsymptoticStatement) {γ₁ γ₂ : ℕ} (h₁ : 0 < γ₁) (h₂ : 0 < γ₂) :
    Tendsto (fun n : ℕ =>
        (Chebyshev.psi ((γ₁ : ℝ) * (n : ℝ)) + Chebyshev.psi ((γ₂ : ℝ) * (n : ℝ))) / (n : ℝ))
      atTop (nhds ((γ₁ : ℝ) + (γ₂ : ℝ))) := by
  refine ((psi_scaled_tendsto hpsi h₁).add (psi_scaled_tendsto hpsi h₂)).congr fun n => ?_
  rw [add_div]

/--
**Leg A, in the chain's own `D` vocabulary.**  `(1/n)·log(D_{γ₁n}·D_{γ₂n}) → γ₁ + γ₂`, where
`D_m = Nat.lcmUpto m = lcm(1,…,m)` is exactly the clearing denominator L10 divides by.

The whole step from §3's `ψ` statement is `Chebyshev.psi_eq_log_lcmUpto` plus `Real.log_mul`,
whose two nonvanishing side conditions come from `Nat.lcmUpto_ne_zero`.
-/
theorem legA_lcmUpto (hpsi : psiAsymptoticStatement) {γ₁ γ₂ : ℕ} (h₁ : 0 < γ₁) (h₂ : 0 < γ₂) :
    Tendsto (fun n : ℕ =>
        Real.log ((Nat.lcmUpto (γ₁ * n) : ℝ) * (Nat.lcmUpto (γ₂ * n) : ℝ)) / (n : ℝ))
      atTop (nhds ((γ₁ : ℝ) + (γ₂ : ℝ))) := by
  refine (legA_psi_sum hpsi h₁ h₂).congr fun n => ?_
  have e₁ : Chebyshev.psi ((γ₁ : ℝ) * (n : ℝ))
      = Real.log ((Nat.lcmUpto (γ₁ * n) : ℕ) : ℝ) := by
    rw [← Nat.cast_mul]
    exact Chebyshev.psi_eq_log_lcmUpto _
  have e₂ : Chebyshev.psi ((γ₂ : ℝ) * (n : ℝ))
      = Real.log ((Nat.lcmUpto (γ₂ * n) : ℕ) : ℝ) := by
    rw [← Nat.cast_mul]
    exact Chebyshev.psi_eq_log_lcmUpto _
  have hne₁ : ((Nat.lcmUpto (γ₁ * n) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero _)
  have hne₂ : ((Nat.lcmUpto (γ₂ * n) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero _)
  rw [e₁, e₂, ← Real.log_mul hne₁ hne₂]

/-! ## §4. At the candidate — `γ = (16, 15)`, so the limit is 31 -/

/--
**LEG A AT THE CANDIDATE.**  `(1/n)·log(D_{16n}·D_{15n}) → 31`, from bare PNT.

`γ₁ = 16`, `γ₂ = 15` are the candidate's Prop-1 clearing exponents
(`zeta2-soft-links.md` §2, `extract_profile.py`'s `gamma = (16, 15)`), and `31 = 16 + 15` is the
constant L10 consumes.
-/
theorem legA_candidate (hpsi : psiAsymptoticStatement) :
    Tendsto (fun n : ℕ =>
        Real.log ((Nat.lcmUpto (16 * n) : ℝ) * (Nat.lcmUpto (15 * n) : ℝ)) / (n : ℝ))
      atTop (nhds 31) := by
  have h := legA_lcmUpto hpsi (γ₁ := 16) (γ₂ := 15) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/--
**LEG A, CLOSED FROM THE INPUT THE CAMPAIGN ALREADY HAS.**  No hypothesis of leg A's own: the
`ψ` bound here is leg B's, discharged on `PrimeNumberTheoremAnd` from `MediumPNT` with an
archived axiom receipt.  D5 therefore rests on ONE external citation covering both legs.
-/
theorem legA_candidate_from_psi (h : psiErrorBoundStatement) :
    Tendsto (fun n : ℕ =>
        Real.log ((Nat.lcmUpto (16 * n) : ℝ) * (Nat.lcmUpto (15 * n) : ℝ)) / (n : ℝ))
      atTop (nhds 31) :=
  legA_candidate (psiAsymptotic_of_psiErrorBound h)

/-! ## §5. Edges — LEAN.md §5

A statement that is true for an uninteresting reason elaborates exactly like one that is true
for the reason you meant.  Each of these is a positive theorem, so nobody can weaken the
surrounding statements without turning a green file red. -/

/--
**The `n = 0` value is junk, so leg A must be a LIMIT and can never be a `∀ n` bound.**
`lcmUpto 0 = 1`, so the numerator is `log 1 = 0`, and Lean's `0 / 0 = 0`: the sequence's value
at `0` is `0`, not `31`.  An `atTop` statement is immune; a pointwise one would be false.
-/
theorem legA_at_zero_is_junk :
    Real.log ((Nat.lcmUpto (16 * 0) : ℝ) * (Nat.lcmUpto (15 * 0) : ℝ))
      / ((0 : ℕ) : ℝ) = 0 := by
  simp

/--
**The limit is `31` and nothing else — the conclusion pins a NUMBER.**  A limit statement whose
value could be anything would attest nothing about `γ₁ + γ₂`; here `32` is refuted from the same
hypothesis by uniqueness of limits.  This is leg A's containment arm.
-/
theorem legA_candidate_not_32 (hpsi : psiAsymptoticStatement) :
    ¬ Tendsto (fun n : ℕ =>
        Real.log ((Nat.lcmUpto (16 * n) : ℝ) * (Nat.lcmUpto (15 * n) : ℝ)) / (n : ℝ))
      atTop (nhds 32) := by
  intro h
  have : (31 : ℝ) = 32 := tendsto_nhds_unique (legA_candidate hpsi) h
  norm_num at this

/-! ## §6. Receipts — LEAN.md §1: exit 0 attests nothing, `#print axioms` does. -/

#print axioms psiAsymptotic_of_psiErrorBound
#print axioms psi_scaled_tendsto
#print axioms legA_psi_sum
#print axioms legA_lcmUpto
#print axioms legA_candidate
#print axioms legA_candidate_from_psi
#print axioms legA_at_zero_is_junk
#print axioms legA_candidate_not_32

end Zeta2LegA

/-! The interface statement, printed, so it can be diffed against the two existing copies. -/
#print Zeta2LegA.psiErrorBoundStatement
#print Chebyshev.psi
