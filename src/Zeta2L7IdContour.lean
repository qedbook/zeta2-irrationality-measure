/-
Row L7ID, OBLIGATION 5 of 5: the σ̃ contour moved to the CELL contour — `docs/future/zeta2-lean-chain.md`.

WHAT THIS FILE PROVES.  `L7MidM5.rIntC n`, the chain's `r_n` as `zeta2-l7-proof.md` §1 defines it
(the line integral of `H_n` over `Re t = −σ̃n − ½`), IS the same integral over the ROUTE-A / cell
contour `Re t = −4n − ½`:

    Zeta2L7IdContour.rIntC_eq_lineA (hn : 1 ≤ n) :
      L7MidM5.rIntC n = (1 / (2π)) * ∫ s, L7MidM123.Hn n (Zeta2L7IdMoment.lineA n s)

and its real twin `rLine_eq_lineA` on `L7MidM5.rLine`, the sequence the chain's rate is stated
for.  Everything else here is that identity's consequences: the integrand is INTEGRABLE on the
cell contour with no hypothesis but `1 ≤ n` (`integrable_Hn_lineA`), and the `Ppol`/residue split
and its termwise RESID expansion are transported to that contour, where the `Ppol` arm's kernel
collapses to the REAL elementary `(π / cosh π s)²` (`PpolArm_lineA`).

WHY IT IS A PREREQUISITE AND NOT TIDY-UP.  The row's two arms are CONTOUR-DEPENDENT where `Hn`
is not: each arm of `Zeta2L7IdSplit.Hn_eq_PpolArm_add_ResidArm` has poles where `Hn` has none, so
at `n = 1` the σ̃-line and route-A `Ppol` moments differ by `−2π(Ppol′(−5) + Ppol′(−6)) ≈ 1.12e24`
(`l7id_moment_check.py` ARM 7, residues exact in ℚ).  The moment arm therefore CANNOT be stated
on the σ̃ line at all, and nothing downstream of the split is well posed until the contour is
moved.  This file is that move, executed.

THE OBSTACLE WAS MODULE TOPOLOGY, NOT MATHEMATICS, and it is worth recording because row L7-WIRE
(2026-09-18) looked like it had removed it.  Lemma 9 is proved and axiom-free, but both artifacts
carrying it — `L7MidM6.lean` and `Zeta2RouteBL7Capstone.lean` — re-embed M123/M4/M5 as SECTIONS,
while every `Zeta2L7Id*` file imports the `L7MidM5` MODULE.  Measured on the buildbox 2026-09-20:

    import Zeta2RouteBL7Capstone
    import L7MidM5
    → error: import L7MidM5 failed, environment already contains 'L7MidM123.Hn'
             from Zeta2RouteBL7Capstone

so `L7MidM6.lemma9` and `Zeta2L7IdSplit.Hn_eq_PpolArm_add_ResidArm` could not appear in one
elaboration.  L7-WIRE made `lemma9_contourB` importable FROM THE CAPSTONE; it did not make it
importable BESIDE the split.  The fix is `L7MidM6Mod.lean` (`m6mod.consolidate`), the SAME
`m6_glue.lean` bytes over `import L7MidM5` instead of over re-embedded sections — 24 clean
receipts, 9.8 s, 1.44 MB olean, nothing copied by hand (LEAN.md §10).

WHAT IS NOT PROVED HERE, so the row does not close on this file:
  * obligation 2, the estimate — untouched.  L7ID-0's `|m|^{−3/2}` majorant was computed against
    a single `|t+1|` factor; this contour carries `11n+1` window poles and a degree-`16n−1`
    polynomial part.
  * obligation 3, the `∫Σ` interchange on the RESID arm.  Its family exists here
    (`ResidArm_lineA_eq_tsum`) and `integral_tsum_of_summable_integral_norm`'s hypotheses are
    MEASURED to hold on it; hypothesis (b), `Summable (fun m => ∫‖F_m‖)`, is not proved.
  * the `Ppol` arm's VALUE.  `Zeta2L7IdMoment` reduced it to the one `n`-free analytic
    obligation `SechMomentTable`, which is still a `Prop` and not a theorem.
  * `candidateM.rn`.  NOTHING in this file mentions it, so RDECAY gains nothing: `hdecay` is
    stated on `‖Δ n * candidateM.rn n‖` at `Zeta2PhiT.ΔT` and the identification `rn = −rLine`
    is the row's target, still open.

ACCEPTANCE (LEAN.md §1, as sharpened 2026-09-20): the receipt AND the printed TYPE.  `#print
axioms` cannot see an undischarged hypothesis, so every theorem below is followed by BOTH, and
the only binders any of them carries are `n : ℕ`, `s : ℝ` and `hn : 1 ≤ n`.

Elaborate: sh external_tests/zeta2_arith/run_probe.sh Zeta2L7IdContour.lean
Falsifier:  bash external_tests/zeta2_arith/falsify_l7idcontour.sh
Second implementation: external_tests/zeta2_arith/l7id_contour_check.py

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2
         mathlib   5aedf732b6987e8c26ab3c9ebc855314f82b045f
-/
import Mathlib
import L7MidM6Mod
import Zeta2L7IdSplit
import Zeta2L7IdMoment

namespace Zeta2L7IdContour

open Zeta2Defs MeasureTheory

/-! ## §1. The cell contour lies in M2's strip, and `H_n` is continuous on it

`Zeta2L7IdMoment.lineA` is the RIGHT EDGE of `L7MidM123.Strip n σ` for every `σ ≥ 4`, which is
what makes M2's analyticity apply to it with no new work.  Stated at `σ = 9`, the largest value
`differentiableOn_Hn` admits, so nothing here depends on `σ̃`. -/

/-- The route-A line is inside M2's closed strip at every `n`. -/
theorem lineA_mem_Strip (n : ℕ) (s : ℝ) :
    Zeta2L7IdMoment.lineA n s ∈ L7MidM123.Strip n 9 := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- `Set.mem_setOf_eq` is DEPRECATED at this pin (it still compiles, which is the dangerous
  -- kind — LEAN.md §8); `Set.mem_ofPred_eq` is the current name.
  simp only [L7MidM123.Strip, Set.mem_ofPred_eq, Zeta2L7IdMoment.lineA_re]
  constructor
  · nlinarith
  · linarith

/-- `lineA n` is continuous — the measurability half of "the cell-contour integral is a genuine
integral and not Lean's junk value". -/
theorem continuous_lineA (n : ℕ) : Continuous (Zeta2L7IdMoment.lineA n) := by
  unfold Zeta2L7IdMoment.lineA
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- `H_n` restricted to the cell contour is continuous, straight from M2. -/
theorem continuous_Hn_lineA (n : ℕ) :
    Continuous fun s : ℝ => L7MidM123.Hn n (Zeta2L7IdMoment.lineA n s) :=
  ((L7MidM123.differentiableOn_Hn n (le_refl (9 : ℝ))).continuousOn).comp_continuous
    (continuous_lineA n) (lineA_mem_Strip n)

/-! ## §2. THE CONTOUR MOVE — obligation 5

`L7MidM6.lemma9` is the proved statement `∫ H_n(−σ̃n−½+is) ds = ∫ H_n(−4n−½+is) ds`.  Both sides
are spelled in the raw `((… : ℝ) : ℂ) + (s : ℂ) * I` form; `L7MidM5.lineB` and
`Zeta2L7IdMoment.lineA` are definitionally those two spellings, so the only content of the two
lemmas below is the unfolding — which is exactly the point: the chain's `r_n` and the arms'
contour are now the SAME object, and no consumer has to re-derive it. -/

/-- The two line integrals of `H_n` agree, in the contours' own names. -/
theorem integral_lineB_eq_lineA {n : ℕ} (hn : 1 ≤ n) :
    (∫ s : ℝ, L7MidM123.Hn n (L7MidM5.lineB n s))
      = ∫ s : ℝ, L7MidM123.Hn n (Zeta2L7IdMoment.lineA n s) := by
  have h := L7MidM6.lemma9 hn
  simp only [L7MidM5.lineB, Zeta2L7IdMoment.lineA]
  exact h

/-- **ROW L7ID'S FIFTH OBLIGATION, DISCHARGED AT EVERY `n ≥ 1`.**  The chain's `r_n` — M5's
`rIntC`, the σ̃-contour integral — IS the cell-contour integral, where the `Ppol` arm's kernel is
elementary and the moment arm is stateable. -/
theorem rIntC_eq_lineA {n : ℕ} (hn : 1 ≤ n) :
    L7MidM5.rIntC n
      = (1 / (2 * Real.pi) : ℂ) * ∫ s : ℝ, L7MidM123.Hn n (Zeta2L7IdMoment.lineA n s) := by
  rw [L7MidM5.rIntC, integral_lineB_eq_lineA hn]

/-- The same for `L7MidM5.rLine`, the REAL sequence the chain's rate
(`routeB_l7_rate_sigmaTilde`) is stated for and the one L7ID's target names. -/
theorem rLine_eq_lineA {n : ℕ} (hn : 1 ≤ n) :
    L7MidM5.rLine n
      = (1 / (2 * Real.pi))
          * (∫ s : ℝ, L7MidM123.Hn n (Zeta2L7IdMoment.lineA n s)).re := by
  have hcast : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [L7MidM5.rLine, rIntC_eq_lineA hn, hcast]
  simp [Complex.mul_re]

/-! ## §3. The cell-contour integrand is INTEGRABLE

M5's `integrable_Hn_lineB` is conditional on the phase hypotheses `hc₀`/`hsup`/`htail`; on THIS
contour the decay estimate is M6's own `norm_Hn_decay`, whose strip `−6n−½ ≤ Re t ≤ −4n−½` has
the cell contour as its right edge, so the only hypothesis left is `1 ≤ n`. -/

/-- **`s ↦ H_n(−4n−½+is)` is integrable on ℝ**, hypothesis-free at `1 ≤ n`. -/
theorem integrable_Hn_lineA {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun s : ℝ => L7MidM123.Hn n (Zeta2L7IdMoment.lineA n s)) := by
  refine L7MidM6.integrable_of_exp_decay (continuous_Hn_lineA n)
    (K := L7MidM6.Kn n) (c := 5) (by norm_num) ?_
  intro y hy
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL : -6 * (n : ℝ) - 1 / 2 ≤ (Zeta2L7IdMoment.lineA n y).re := by
    rw [Zeta2L7IdMoment.lineA_re]
    nlinarith
  have hR : (Zeta2L7IdMoment.lineA n y).re ≤ -4 * (n : ℝ) - 1 / 2 :=
    le_of_eq (Zeta2L7IdMoment.lineA_re n y)
  have him : (1 : ℝ) ≤ |(Zeta2L7IdMoment.lineA n y).im| := by
    rw [Zeta2L7IdMoment.lineA_im]
    exact hy
  have h := L7MidM6.norm_Hn_decay hn hL hR him
  rwa [Zeta2L7IdMoment.lineA_im] at h

/-! ## §4. The split, transported to the cell contour

`Zeta2L7IdSplit`'s statements are contour-free (`Im t ≠ 0` is their only hypothesis), so the
transport is free — but it has to be DONE, because a consumer that re-spells the arm at
`lineA n s` every time is how two copies of one object appear (LEAN.md §6). -/

/-- The split on the cell contour. -/
theorem Hn_lineA_eq_PpolArm_add_ResidArm (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    L7MidM123.Hn n (Zeta2L7IdMoment.lineA n s)
      = Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s)
        + Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s) :=
  Zeta2L7IdSplit.Hn_eq_PpolArm_add_ResidArm n (Zeta2L7IdMoment.lineA_im_ne_zero hs)

/-- **The `Ppol` arm on the cell contour is a polynomial against a REAL elementary kernel.**
This is the whole reason the contour had to move: `Zeta2L7IdMoment.kernel_lineA` turns
`(π / sin π t)²` into `(π / cosh π s)²` exactly, at every `n`, because `4n` is even.  No `s ≠ 0`
is needed — the collapse holds on the whole line, including the real point. -/
theorem PpolArm_lineA (n : ℕ) (s : ℝ) :
    Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s)
      = ((candidateM.Pin n : ℚ) : ℂ)
          * Polynomial.aeval (Zeta2L7IdMoment.lineA n s) (candidateM.Ppol n)
          * (((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ) : ℂ) := by
  rw [Zeta2L7IdSplit.PpolArm]
  exact Zeta2L7IdMoment.arm_lineA _ n s

/-- The RESID arm's kernel collapses on the cell contour too — same `kernel_lineA`, applied at
the residue sum's coefficient. -/
theorem ResidArm_lineA (n : ℕ) (s : ℝ) :
    Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s)
      = (∑ k ∈ candidateM.window n,
            ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
              / (Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ)))
          * (((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ) : ℂ) := by
  rw [Zeta2L7IdSplit.ResidArm]
  exact Zeta2L7IdMoment.arm_lineA _ n s

/-- The RESID arm on the cell contour, termwise — the family obligation 3 consumes, now on the
contour the row is actually going to integrate over.  Terms decay like `|t|^{−3}`. -/
theorem ResidArm_lineA_eq_tsum (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s)
      = ∑' m : ℤ, ∑ k ∈ candidateM.window n,
          ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
            / ((Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ))
                * (Zeta2L7IdMoment.lineA n s + (m : ℂ)) ^ 2) :=
  Zeta2L7IdSplit.ResidArm_eq_tsum n (Zeta2L7IdMoment.lineA_im_ne_zero hs)

/-- `H_n` on the cell contour, fully split and expanded: one polynomial arm against
`(π / cosh π s)²`, one `tsum` of `|t|^{−3}` terms.  This is the statement obligations 2 and 3
start from, and the first one in the chain stated on the contour both of them need. -/
theorem Hn_lineA_split_expanded (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    L7MidM123.Hn n (Zeta2L7IdMoment.lineA n s)
      = ((candidateM.Pin n : ℚ) : ℂ)
            * Polynomial.aeval (Zeta2L7IdMoment.lineA n s) (candidateM.Ppol n)
            * (((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ) : ℂ)
        + ∑' m : ℤ, ∑ k ∈ candidateM.window n,
            ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
              / ((Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ))
                  * (Zeta2L7IdMoment.lineA n s + (m : ℂ)) ^ 2) := by
  rw [Hn_lineA_eq_PpolArm_add_ResidArm n hs, PpolArm_lineA, ResidArm_lineA_eq_tsum n hs]

/-! ## §5. The row-level consequence — `r_n` as an integral of the two arms

`Zeta2L7IdHinge.ae_ne_zero` is what makes the single real point of the contour free, and
`integral_congr_ae` is the consumer.  No integrability is spent here: the integrand is rewritten
under one integral sign, not split into two. -/

/-- **`r_n` is the cell-contour integral of the two arms.**  The chain's linear-form integral,
on the contour where the polynomial arm is a moment of `sech²` and the residue arm is a
`|t|^{−3}` family. -/
theorem rIntC_cell_split {n : ℕ} (hn : 1 ≤ n) :
    L7MidM5.rIntC n
      = (1 / (2 * Real.pi) : ℂ)
          * ∫ s : ℝ, (Zeta2L7IdSplit.PpolArm n (Zeta2L7IdMoment.lineA n s)
              + Zeta2L7IdSplit.ResidArm n (Zeta2L7IdMoment.lineA n s)) := by
  rw [rIntC_eq_lineA hn]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Zeta2L7IdHinge.ae_ne_zero] with s hs
  exact Hn_lineA_eq_PpolArm_add_ResidArm n hs

/-- The same with both arms' kernels collapsed and the RESID arm expanded — the exact integrand
obligations 2 and 3 have to estimate. -/
theorem rIntC_cell_expanded {n : ℕ} (hn : 1 ≤ n) :
    L7MidM5.rIntC n
      = (1 / (2 * Real.pi) : ℂ)
          * ∫ s : ℝ, (((candidateM.Pin n : ℚ) : ℂ)
                * Polynomial.aeval (Zeta2L7IdMoment.lineA n s) (candidateM.Ppol n)
                * (((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ) : ℂ)
              + ∑' m : ℤ, ∑ k ∈ candidateM.window n,
                  ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
                    / ((Zeta2L7IdMoment.lineA n s + ((k : ℕ) : ℂ))
                        * (Zeta2L7IdMoment.lineA n s + (m : ℂ)) ^ 2)) := by
  rw [rIntC_eq_lineA hn]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Zeta2L7IdHinge.ae_ne_zero] with s hs
  exact Hn_lineA_split_expanded n hs

/-! ## §6. EDGES (LEAN.md §5) — asked of the real data, not assumed

`n = 0` is where M6's Lemma 9 has no content (`L7MidM6.contours_coincide_at_zero`: the two
abscissae are the SAME number there, `σ̃ · 0 = 4 · 0 = 0`).  So the contour move at `n = 0` is
not a special case to prove — it is an identity of the two contour FUNCTIONS, and the `1 ≤ n` of
`rIntC_eq_lineA` can be dropped there.  Recorded because it is the one `n` at which the row's
whole route is different, and because it is what L7ID-0 was proved on. -/

/-- At `n = 0` the two contours are the same function of `s`, pointwise. -/
theorem lineB_zero_eq_lineA_zero (s : ℝ) :
    L7MidM5.lineB 0 s = Zeta2L7IdMoment.lineA 0 s := by
  simp [L7MidM5.lineB, Zeta2L7IdMoment.lineA]

/-- So `rIntC_eq_lineA` holds at `n = 0` with NO hypothesis, by the contours coinciding rather
than by Lemma 9 — which is how the `1 ≤ n` in every other statement here is shown to be about
the contour MOVE and not about the identification. -/
theorem rIntC_eq_lineA_zero :
    L7MidM5.rIntC 0
      = (1 / (2 * Real.pi) : ℂ) * ∫ s : ℝ, L7MidM123.Hn 0 (Zeta2L7IdMoment.lineA 0 s) := by
  have h : (fun s : ℝ => L7MidM123.Hn 0 (L7MidM5.lineB 0 s))
      = fun s : ℝ => L7MidM123.Hn 0 (Zeta2L7IdMoment.lineA 0 s) := by
    funext s
    rw [lineB_zero_eq_lineA_zero]
  rw [L7MidM5.rIntC, h]

/-- **The EDGE that is NOT free, recorded as a theorem rather than as prose.**  At `n = 0` the
`Ppol` arm vanishes (`Zeta2L7IdSplit.PpolArm_zero`, from `Ppol 0 = 0`), so the cell-contour
split says the whole of `H_0` is the RESID arm — and the moment arm, the thing this contour move
exists to make stateable, is EMPTY there.  That is the arithmetic reason `n = 0` was measured a
poor template for this row. -/
theorem cell_split_zero_is_resid_only {s : ℝ} (hs : s ≠ 0) :
    L7MidM123.Hn 0 (Zeta2L7IdMoment.lineA 0 s)
      = Zeta2L7IdSplit.ResidArm 0 (Zeta2L7IdMoment.lineA 0 s) := by
  rw [Hn_lineA_eq_PpolArm_add_ResidArm 0 hs, Zeta2L7IdSplit.PpolArm_zero, zero_add]

end Zeta2L7IdContour

/-! ## RECEIPTS — LEAN.md §1: exit 0 attests nothing, and neither does a receipt on its own.

Each theorem is printed TWICE: `#print axioms` for soundness of what it states, `#check @` for
WHAT it states — because a receipt is byte-identical whether or not the theorem is conditional
(LEAN.md §1, the 2026-09-20 sharpening).  The only binders in this file are `n : ℕ`, `s : ℝ`,
`hn : 1 ≤ n` and `hs : s ≠ 0`; there is no hypothesis from anywhere else in the chain. -/

#print axioms Zeta2L7IdContour.lineA_mem_Strip
#check @Zeta2L7IdContour.lineA_mem_Strip
#print axioms Zeta2L7IdContour.continuous_lineA
#check @Zeta2L7IdContour.continuous_lineA
#print axioms Zeta2L7IdContour.continuous_Hn_lineA
#check @Zeta2L7IdContour.continuous_Hn_lineA
#print axioms Zeta2L7IdContour.integral_lineB_eq_lineA
#check @Zeta2L7IdContour.integral_lineB_eq_lineA
#print axioms Zeta2L7IdContour.rIntC_eq_lineA
#check @Zeta2L7IdContour.rIntC_eq_lineA
#print axioms Zeta2L7IdContour.rLine_eq_lineA
#check @Zeta2L7IdContour.rLine_eq_lineA
#print axioms Zeta2L7IdContour.integrable_Hn_lineA
#check @Zeta2L7IdContour.integrable_Hn_lineA
#print axioms Zeta2L7IdContour.Hn_lineA_eq_PpolArm_add_ResidArm
#check @Zeta2L7IdContour.Hn_lineA_eq_PpolArm_add_ResidArm
#print axioms Zeta2L7IdContour.PpolArm_lineA
#check @Zeta2L7IdContour.PpolArm_lineA
#print axioms Zeta2L7IdContour.ResidArm_lineA
#check @Zeta2L7IdContour.ResidArm_lineA
#print axioms Zeta2L7IdContour.ResidArm_lineA_eq_tsum
#check @Zeta2L7IdContour.ResidArm_lineA_eq_tsum
#print axioms Zeta2L7IdContour.Hn_lineA_split_expanded
#check @Zeta2L7IdContour.Hn_lineA_split_expanded
#print axioms Zeta2L7IdContour.rIntC_cell_split
#check @Zeta2L7IdContour.rIntC_cell_split
#print axioms Zeta2L7IdContour.rIntC_cell_expanded
#check @Zeta2L7IdContour.rIntC_cell_expanded
#print axioms Zeta2L7IdContour.lineB_zero_eq_lineA_zero
#check @Zeta2L7IdContour.lineB_zero_eq_lineA_zero
#print axioms Zeta2L7IdContour.rIntC_eq_lineA_zero
#check @Zeta2L7IdContour.rIntC_eq_lineA_zero
#print axioms Zeta2L7IdContour.cell_split_zero_is_resid_only
#check @Zeta2L7IdContour.cell_split_zero_is_resid_only
