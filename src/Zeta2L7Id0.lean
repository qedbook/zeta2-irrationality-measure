/-
# Row L7ID-0 — the row's target theorem is FALSE, machine-checked, and the shape half it needs

`docs/future/zeta2-lean-chain.md` row L7ID-0 (and L7ID, which uses it as its template).

**WHAT THIS FILE REFUTES.**  The row as landed asked for

    theorem rn_eq_rLine_zero : Zeta2Defs.candidateM.rn 0 = L7MidM5.rLine 0

and `row_target_is_false` below proves its negation, with NO side condition — not "under
integrability", not "for the intended contour", not modulo a convention.  The proof is a sign
sandwich: `candidateM.rn 0 = −ζ(2) < 0` on the arithmetic side, and `0 ≤ rLine 0` on the MB side
in BOTH branches of the only case split there is (the integrand is integrable and the integral of
a pointwise-positive function is `≥ 0`; or it is not and Lean's `∫` is the junk value `0`).

**WHAT IS TRUE INSTEAD** — `candidateM.rn n = −L7MidM5.rLine n`, and at `n = 0` that is

    theorem rn_eq_neg_rLine_zero : Zeta2Defs.candidateM.rn 0 = -L7MidM5.rLine 0

which this file does NOT prove: `rn 0 = −ζ(2)` is proved here, `rLine 0 = +ζ(2)` is the VALUE half
and is not (it is the row's remaining work — see the row's cell and the L7ID-0 design notes).
What is measured numerically, at three `n` and to 161 / 131 / 100 agreeing digits, is
`l7id0_sign_check.py` → `l7id0_sign_check.out`.  `n = 1` and `n = 2` were MEASURED rather than
extrapolated, because `zeta2-integral-free.md` §3.5 records that `sign(rₙ)` is not eventually
constant, so a ratio read off `n = 0` alone would have been a guess.

**WHY THE ROW WAS WRONG — a convention clash between two layers that had never met.**  Two sign
factors, each constant at the candidate and each correct in its own corpus:

  * `Zeta2Defs.Member.sgn n = (−1)^(dsum·n + 1)` with `dsum = 13+11+9+15 − (2+4+26) = 16`, so
    `sgn n ≡ −1` at every `n`.  That is the ENGINE's convention (`z2a.linear_form`), and landed
    `decide` rows cross-check it (`candidate n = 0 qn = −1`; `qn_zero` below re-proves it here).
  * `L7MidM123.Hn`'s leading sign is `(−1)^(b₁+b₂+b₃) = (−1)^(6n+3) ≡ −1`, and
    `L7MidM123.Hn_eq_kernel_form` exhibits `Hn = Π(n)·Rₙ(t)·(π/sin πt)²` — the write-up's POSITIVE
    convention.  `L7MidM5.rIntC` is `zeta2-l7-proof.md` §1's `(1/2πi)∮ … dt` at the standard
    upward orientation.

Nothing in the chain had touched both layers before: the scope audit's §4.2 grep records that
`Zeta2Defs`, `Member.rn` and `candidateM` appear in NO L7 file.  This row is the first contact,
and the defect a first-contact row exists to find fired on the first contact.

**THE FIX IS AT THE STATEMENT, NOT AT EITHER DEFINITION**, and that is a deliberate choice with a
blast radius behind it.  `L7MidM5.rIntC` sits under the 162 landed receipts of
`Zeta2RouteBL7.routeB_l7_rate_sigmaTilde`; `Zeta2Defs.Member.sgn` is consumed by `qn`, by `pn` and
by landed engine cross-checks.  Re-signing either is a wide edit for zero gain, because the
identification row is the ONE place the two conventions have to meet.  So the minus sign lives
here.  Downstream cost is zero: RDECAY consumes `|ΔT n * candidateM.rn n|` and
`routeB_l7_rate_sigmaTilde` delivers `|rLine n| ≤ …`, and a single `abs_neg` absorbs the flip.

**THE ROW'S OWN EVIDENCE ALREADY CONTAINED THE CONTRADICTION.**  The row's input cell names
`n0_identity.out` as a 30-digit numeric pin.  That probe's docstring line 1 reads *"the MB line
integral of H_0 on Re t = -1/2 **vs r_0 = -zeta(2)**"* while its own last line predicts the same
integral equals `+ζ(2)`.  Both sentences, one docstring, unread since the pin was filed — and the
row's prose gloss inherited both halves, asserting `−ζ(2) = (1/2π)·Re ∫ H₀` and, in the same
sentence, that the integral is `π²/6 = +ζ(2)`.

**WHAT THIS FILE DOES PROVE**, and it is the whole SHAPE half of the row:

  * `lineB_zero` — the contour at `n = 0` is `−1/2 + is` (`L7MidM5.lineB` at `n = 0`, not assumed);
  * `sin_pi_lineB_zero` — `sin(π · lineB 0 s) = −cosh(πs)`, so the kernel has no pole on it;
  * `Hn_zero_collapse` — the `n = 0` kernel collapse `H₀(t) = π²/((t+1)·sin²(πt))`, through
    `L7MidM123.Hn_eq_kernel_form`, `Complex.Gamma_add_one` and `Complex.Gamma_ne_zero`;
  * `Hn_zero_line_re_pos` — `Re H₀(lineB 0 s) > 0` pointwise;
  * `rn_zero` — the arithmetic side, `rn 0 = −ζ(2)`, assembled from the corpus's OWN `n = 0`
    lemmas (`Zeta2Defs.Member.qn_zero`, which is `q₀ = −1` for every member, and
    `Zeta2Hat.candidate_pn_zero`) rather than from a private re-derivation: the first draft of
    this file re-proved both by hand, which is 20 lines of twin for facts already landed;
  * `rLine_zero_nonneg` — the junk-value case split, which is what makes the refutation
    unconditional rather than conditional on an integrability fact the corpus does not supply at
    `n = 0` (every M4/M5 support lemma — `integrable_Hn_lineB`, `norm_Hn_lineB_le`,
    `norm_rIntC_le`, `lineB_eq_contourB` — is gated `1 ≤ n`).

**`Hn` IS `L7MidM123.Hn`, NOT `L7MidM5.Hn`** — the row's input cell spells it wrong, and so do the
sibling names `Zeta2SupScheme.sigT`, `L7MidM4.C_B`, `L7MidM123.kappaPi`.  `L7MidM5.lean` is the
consolidated module and carries all three namespaces, so the import is right and only the
qualification was wrong; it is `#check`-verified below rather than asserted.

**`import Mathlib` is deliberate here and is not the corpus norm.**  This is a first-contact file
across two corpora with disjoint import sets (`Zeta2Defs` brings the polynomial/Bernoulli half,
`L7MidM5` the Gamma/MeasureTheory half), and it needs `ContinuousLinearMap.integral_comp_comm`
from neither.  The refutation was proved under the wholesale import and the receipt in
`out_axioms_l7id0.txt` was re-taken from THESE bytes; narrowing the import would be a different
file needing a fresh receipt, for no gain on a box where `L7MidM5.olean` is already resident.

Falsifier: `falsify_l7id0.sh` → `out_l7id0_falsify.txt` (four sed arms RED, the receipt-predicate
arm, control GREEN, restore byte-verified).  Re-run it after ANY edit to this file, to
`Zeta2Defs.Member.sgn/qn/pn/rn`, or to `L7MidM5.lineB/rIntC/rLine` / `L7MidM123.Hn`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2 (from `mathlib-current`'s `lean-toolchain`, NOT
         elan's default 4.33.1 — both are installed on the buildbox and report different
         versions), mathlib 5aedf732, buildbox.
-/
import Mathlib
import Zeta2Defs
import Zeta2Hat
import L7MidM5

open MeasureTheory Complex

set_option maxHeartbeats 1000000

namespace Zeta2L7Id0

/-! ## 1. The contour at `n = 0`, and the sine on it

`L7MidM5.lineB n s` is the cell contour; at `n = 0` the shift `sigT · n` vanishes and it is the
bare line `Re t = −1/2`.  Nothing below assumes that — `lineB_zero` computes it. -/

theorem lineB_zero (s : ℝ) :
    L7MidM5.lineB 0 s = ((-(1/2) : ℝ) : ℂ) + (s : ℂ) * Complex.I := by
  simp [L7MidM5.lineB]

/-- On `Re t = −1/2` the kernel's sine is real and never zero: `sin(π(−1/2 + is)) = −cosh(πs)`.
The MINUS is real and is measured, not decorative — `falsify_l7id0.sh` arm A2 reds without it —
even though `Hn` squares it, because the same identity is what `L7ID` will meet at general `n`
with the sign no longer squared away. -/
theorem sin_pi_lineB_zero (s : ℝ) :
    Complex.sin ((Real.pi : ℂ) * L7MidM5.lineB 0 s)
      = -((Real.cosh (Real.pi * s) : ℝ) : ℂ) := by
  rw [lineB_zero]
  have hexp : (Real.pi : ℂ) * (((-(1/2) : ℝ) : ℂ) + (s : ℂ) * Complex.I)
      = ((-(Real.pi/2) : ℝ) : ℂ) + ((Real.pi * s : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hexp, Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
  rw [show Real.sin (-(Real.pi/2)) = -1 by simp,
      show Real.cos (-(Real.pi/2)) = 0 by simp]
  rw [← Complex.ofReal_cosh]
  push_cast
  ring

/-! ## 2. The `n = 0` kernel collapse

At `n = 0` the candidate's four Gamma factors collapse: `a = (1,1,1,1)`, `b = (1,1,1,2)`, so
`Γ(t+1)⁴ / (Γ(t+1)³ Γ(t+2)) = 1/(t+1)` and `Π(0) = 1`.  `R₀` is ONE simple pole, against twelve
window poles and a degree-15 polynomial part at `n = 1` — which is exactly why `n = 0` is decisive
for the SIGN and a poor template for `L7ID`. -/

theorem Hn_zero_collapse (t : ℂ) (ht : Complex.sin ((Real.pi : ℂ) * t) ≠ 0)
    (ht1 : ∀ m : ℕ, t + 1 ≠ -(m : ℂ)) :
    L7MidM123.Hn 0 t
      = ((Real.pi : ℂ) ^ 2) / ((t + 1) * Complex.sin ((Real.pi : ℂ) * t) ^ 2) := by
  have hg : Complex.Gamma (t + 1) ≠ 0 := Complex.Gamma_ne_zero ht1
  have ht0 : t + 1 ≠ 0 := by simpa using ht1 0
  have h2 : Complex.Gamma (t + 2) = (t + 1) * Complex.Gamma (t + 1) := by
    have h := Complex.Gamma_add_one (t + 1) ht0
    rw [show t + 1 + 1 = t + 2 by ring] at h
    exact h
  rw [L7MidM123.Hn_eq_kernel_form 0 t ht]
  simp only [L7MidM123.Pi_n, L7MidM123.a₁, L7MidM123.a₂, L7MidM123.a₃, L7MidM123.a₄,
    L7MidM123.b₁, L7MidM123.b₂, L7MidM123.b₃, L7MidM123.b₄, Nat.mul_zero, Nat.zero_add,
    Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat, mul_one]
  norm_num
  rw [h2]
  field_simp

/-- The collapse's Gamma side condition, discharged on the contour: `t + 1` has real part `1/2`,
so it is never a non-positive integer. -/
theorem lineB_zero_add_one_ne (s : ℝ) (m : ℕ) : L7MidM5.lineB 0 s + 1 ≠ -(m : ℂ) := by
  intro h
  have hre : (L7MidM5.lineB 0 s + 1).re = (-(m : ℂ)).re := by rw [h]
  rw [lineB_zero] at hre
  simp at hre
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- …and the sine side condition, from `cosh > 0`. -/
theorem sin_lineB_zero_ne (s : ℝ) :
    Complex.sin ((Real.pi : ℂ) * L7MidM5.lineB 0 s) ≠ 0 := by
  rw [sin_pi_lineB_zero]
  simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
  exact ne_of_gt (Real.cosh_pos _)

/-! ## 3. The integrand's real part is strictly positive on the contour

`H₀(−1/2 + is) = π² / ((1/2 + is)·cosh²(πs))`, whose real part is
`π²·cosh²(πs)/2` over a positive normSq.  This is the half of the refutation that lives on the MB
side, and it needs no integrability. -/

theorem Hn_zero_line_re_pos (s : ℝ) :
    0 < (L7MidM123.Hn 0 (L7MidM5.lineB 0 s)).re := by
  have hc : (0 : ℝ) < Real.cosh (Real.pi * s) := Real.cosh_pos _
  have hc2 : (0 : ℝ) < Real.cosh (Real.pi * s) ^ 2 := pow_pos hc 2
  rw [Hn_zero_collapse _ (sin_lineB_zero_ne s) (lineB_zero_add_one_ne s),
      sin_pi_lineB_zero, lineB_zero]
  have hw : (((-(1/2) : ℝ) : ℂ) + (s : ℂ) * Complex.I + 1)
        * (-((Real.cosh (Real.pi * s) : ℝ) : ℂ)) ^ 2
      = (((Real.cosh (Real.pi * s) ^ 2 / 2 : ℝ)) : ℂ)
        + ((s * Real.cosh (Real.pi * s) ^ 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hw]
  have hpi : ((Real.pi : ℂ)) ^ 2 = ((Real.pi ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hpi, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply,
    mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, zero_div]
  have hD : 0 < (Real.cosh (Real.pi * s) ^ 2 / 2) * (Real.cosh (Real.pi * s) ^ 2 / 2)
      + (s * Real.cosh (Real.pi * s) ^ 2) * (s * Real.cosh (Real.pi * s) ^ 2) := by
    nlinarith [mul_self_nonneg (s * Real.cosh (Real.pi * s) ^ 2)]
  have hN : 0 < Real.pi ^ 2 * (Real.cosh (Real.pi * s) ^ 2 / 2) :=
    mul_pos (pow_pos Real.pi_pos 2) (by linarith)
  exact div_pos hN hD

/-! ## 4. The arithmetic side: `rₙ` at `n = 0`

`rₙ = qₙ·ζ(2) − pₙ`, and both halves at `n = 0` are ALREADY LANDED, so this section is an
assembly and not a computation:

  * `Zeta2Defs.Member.qn_zero : ∀ m, m.qn 0 = -1` — and note it is member-INDEPENDENT, because
    `sgn m 0 = (−1)^(dsum·0 + 1) = −1` whatever `dsum` is.  At general `n` the candidate's
    `dsum = 16` keeps `sgn n = (−1)^(16n+1) ≡ −1`, so the clash is not an `n = 0` artefact.
  * `Zeta2Hat.candidate_pn_zero : candidateM.pn 0 = 0` — `Ppol 0 = 1 /ₘ (X + 1) = 0` and
    `harm 2 0 = 0`. -/

/-- **`rₙ` at `n = 0` is `−ζ(2)`.**  This is the ENGINE side of the convention clash: had `q₀`
been `+1`, the row's target theorem would have been TRUE, so this equation's sign is the
load-bearing number in the file and `falsify_l7id0.sh` arm A3 perturbs it. -/
theorem rn_zero : Zeta2Defs.candidateM.rn 0 = -Zeta2Defs.zeta2 := by
  rw [Zeta2Defs.Member.rn, Zeta2Defs.Member.qn_zero, Zeta2Hat.candidate_pn_zero]
  push_cast
  ring

theorem rn_zero_neg : Zeta2Defs.candidateM.rn 0 < 0 := by
  rw [rn_zero, Zeta2Defs.zeta2]
  nlinarith [Real.pi_gt_three, Real.pi_pos]

/-! ## 5. The MB side's sign, with NO integrability hypothesis

The corpus supplies integrability of `Hn ∘ lineB n` only for `1 ≤ n`
(`L7MidM5.integrable_Hn_lineB` and every other M4/M5 support lemma carry that binder), so an
`n = 0` statement that needed it would be conditional on a fact this row would first have to
re-derive.  The case split removes the need: on the other branch Lean's `∫` is `0` by
`MeasureTheory.integral_undef`, and `0 ≤ 0`.  A refutation must not rest on an unproved
hypothesis, or the row could answer it by disputing the hypothesis. -/

/-- `rLine 0` is NEVER negative: either the integrand is integrable and the integral of a
strictly positive function is `≥ 0`, or it is not and Lean's `∫` is the junk value `0`. -/
theorem rLine_zero_nonneg : 0 ≤ L7MidM5.rLine 0 := by
  have hprefix : (0 : ℝ) < 1 / (2 * Real.pi) := by
    have := Real.pi_pos; positivity
  have hre : L7MidM5.rLine 0
      = (1 / (2 * Real.pi)) * (∫ s : ℝ, L7MidM123.Hn 0 (L7MidM5.lineB 0 s)).re := by
    rw [L7MidM5.rLine, L7MidM5.rIntC,
      show ((1 / (2 * Real.pi) : ℂ)) = (((1 / (2 * Real.pi)) : ℝ) : ℂ) by push_cast; ring]
    simp [Complex.mul_re]
  rw [hre]
  by_cases hint : Integrable (fun s : ℝ => L7MidM123.Hn 0 (L7MidM5.lineB 0 s)) volume
  · -- `Complex.re` through a real-line integral has NO named lemma in Mathlib
    -- (`MeasureTheory.integral_re`, `Complex.re_integral`, `RCLike.re_integral` are all unknown
    -- identifiers and `exact?` fails).  This is the three-line route, and its price is the
    -- `Integrable` hypothesis — which is why the case split above exists.
    have hswap : (∫ s : ℝ, L7MidM123.Hn 0 (L7MidM5.lineB 0 s)).re
        = ∫ s : ℝ, (L7MidM123.Hn 0 (L7MidM5.lineB 0 s)).re := by
      have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hint
      simpa using h.symm
    rw [hswap]
    have hnn : 0 ≤ ∫ s : ℝ, (L7MidM123.Hn 0 (L7MidM5.lineB 0 s)).re :=
      integral_nonneg (fun s => (Hn_zero_line_re_pos s).le)
    positivity
  · rw [MeasureTheory.integral_undef hint]
    simp

/-! ## 6. The verdict -/

/-- **THE VERDICT.**  Row L7ID-0's target theorem `rn_eq_rLine_zero` is FALSE, with no side
condition: `candidateM.rn 0 < 0 ≤ rLine 0`.  The corrected statement is
`candidateM.rn 0 = -L7MidM5.rLine 0`; its VALUE half (`rLine 0 = +ζ(2)`) is the row's remaining
work and is not proved here. -/
theorem row_target_is_false : Zeta2Defs.candidateM.rn 0 ≠ L7MidM5.rLine 0 := by
  have h1 := rn_zero_neg
  have h2 := rLine_zero_nonneg
  intro h
  rw [h] at h1
  linarith

/-! ## 7. The names this file resolved against the landed olean

`Hn` is `L7MidM123.Hn` — the row's input cell says `L7MidM5.Hn`, which does not exist.  These
`#check`s fail the elaboration if that ever stops being true, so the correction is executed rather
than written down.  The three names the row's risk cell would have needed and that do NOT exist —
`MeasureTheory.integral_re`, `Complex.re_integral`, `RCLike.re_integral` — cannot be `#check`ed;
their absence is recorded in the L7ID-0 design notes and in §5's comment above. -/
section Names
#check @L7MidM123.Hn
#check @L7MidM123.Hn_eq_kernel_form
#check @L7MidM5.lineB
#check @L7MidM5.rIntC
#check @L7MidM5.rLine
#check @MeasureTheory.integral_undef
#check @MeasureTheory.integral_nonneg
#check @ContinuousLinearMap.integral_comp_comm
end Names

end Zeta2L7Id0

#print axioms Zeta2L7Id0.lineB_zero
#print axioms Zeta2L7Id0.sin_pi_lineB_zero
#print axioms Zeta2L7Id0.Hn_zero_collapse
#print axioms Zeta2L7Id0.lineB_zero_add_one_ne
#print axioms Zeta2L7Id0.sin_lineB_zero_ne
#print axioms Zeta2L7Id0.Hn_zero_line_re_pos
#print axioms Zeta2L7Id0.rn_zero
#print axioms Zeta2L7Id0.rn_zero_neg
#print axioms Zeta2L7Id0.rLine_zero_nonneg
#print axioms Zeta2L7Id0.row_target_is_false
