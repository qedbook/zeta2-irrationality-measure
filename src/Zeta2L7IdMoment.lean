/-
ROW L7ID — THE `Ppol` MOMENT ARM: the kernel collapse on the route-A line, and the moment's
target named in the chain's own vocabulary.

WHAT THIS FILE IS FOR.  `Zeta2L7IdSplit` separates `Hn` into a `Ppol` arm and a RESID arm and
deliberately does not evaluate the `Ppol` arm.  Evaluating it was graded the row's top risk,
because `Ppol n` has degree `16n − 1`, so the hinge expansion is unavailable to it: every term
`Ppol(t)/(t+m)²` grows and `integral_tsum_of_summable_integral_norm`'s first hypothesis is
outright false.  The arm therefore has to meet the FULL kernel `(π / sin π t)²`.

THE FINDING THIS FILE PROVES (`l7id_moment_check.py`, 28 arms / 6 falsifiers, measures it first):
**on the route-A line the full kernel is `π² sech²(π s)` — real, positive and elementary.**
`L7MidM6.lemma9_contourB`'s right-hand side is `Re t = −4n − 1/2`, `4n` is EVEN, and
`sin(π(−4n − 1/2 + is)) = −cosh(π s)` with no sign left to track.  So the `Ppol` moment needs
NO residue theorem, NO Mittag-Leffler, NO complex logarithm and no branch: it is a real integral
of a polynomial against `sech²`.  That is a reduction in KIND, not in size, and it is why the
route sentence's "recognise the per-`n` integrals as `Ppol`-moments" is reachable at all.

WHAT IT DOES NOT PROVE, stated so the green is not read as more than it is.  The moment's VALUE
is not proved here.  Measured (`l7id_moment_check.py` ARM 5, exact ℚ against numerics at
n = 0,1,2,3):

    ∫_{Re t = −4n−1/2} Ppol_n(t) (π / sin π t)² dt  =  2πi · pnPoly n        (NOT proved)

and it does NOT vanish at any `n ≥ 1` — `pnPoly 1 = −31098482130308598631825920/13`.  It
vanishes only at `n = 0`, where `Ppol 0 = 0`, which is exactly why row L7ID-0 never met this arm
and why its file is a poor template here.

Given ONE `n`-independent analytic input — the even `sech²` moment table, `SechMomentTable`
below — the rest of that identity is ALGEBRA over ℚ: binomial expansion plus the Bernoulli
addition theorem, run exactly at 96 identities in `l7id_moment_check.py` ARM 3.  Two census
results decide the next unit's price and are recorded here as findings
(`Zeta2L7IdMomentCensus.lean`, run against the pin, its errors read as its verdict):

  * **`Polynomial.bernoulli_eval_add` is ABSENT.**  Mathlib has `bernoulli_eval_one_add` and
    `bernoulli_eval_one_sub` only, so the addition theorem `B_j(x+y) = Σ C(j,k) B_k(x) y^{j−k}`
    is the next unit's to build.  It is `Polynomial.bernoulli_generating_function` (PRESENT)
    away, or an induction on `bernoulli_eval_one_add`.
  * **`Real.hasDerivAt_tanh` and `Real.tendsto_tanh_atTop` are ABSENT**, so the antiderivative
    route to the table has no Mathlib head start; `MeasureTheory.integral_of_hasDerivAt_of_tendsto`
    (PRESENT, and it is the two-sided improper FTC over all of ℝ) still makes it the cheaper of
    the two routes, the other being `riemannZeta_two_mul_nat` (PRESENT, exact signature recorded
    in the census log) through `η(2m)`.

AND WHAT IT CHANGES FOR RDECAY: NOTHING.  `hdecay` is stated on `|Δ n * candidateM.rn n|`, and
nothing in this file or anywhere else in the chain mentions `candidateM.rn`.  This file is about
the `Ppol` arm of `Hn`'s line integral, which reaches `rn` only after the whole of L7ID closes.
Recording the non-move is the point.

VINTAGE: leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f.
-/
import Mathlib
import Zeta2Defs
import Zeta2Moments

namespace Zeta2L7IdMoment

open Complex Polynomial

/-! ## §1. The route-A line

`lineA n s` is spelled to match `L7MidM6.lemma9_contourB`'s right-hand side character for
character: `((-4 * (n : ℝ) - 1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I`.  M6 is not imported —
it is the capstone-sized module and this file needs one expression from it, not its theory —
so `lineA_re` and `lineA_im` pin the shape instead of a docstring's say-so. -/

/-- The ROUTE-A contour point, `t = −4n − ½ + i s`. -/
noncomputable def lineA (n : ℕ) (s : ℝ) : ℂ :=
  ((-4 * (n : ℝ) - 1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I

@[simp] theorem lineA_re (n : ℕ) (s : ℝ) : (lineA n s).re = -4 * (n : ℝ) - 1 / 2 := by
  simp [lineA]

@[simp] theorem lineA_im (n : ℕ) (s : ℝ) : (lineA n s).im = s := by
  simp [lineA]

/-- The contour meets the real axis at exactly one point, and that point is `volume`-null —
the same single-point caveat `Zeta2L7IdHinge.ae_ne_zero` carries for the σ̃ line. -/
theorem lineA_im_ne_zero {n : ℕ} {s : ℝ} (hs : s ≠ 0) : (lineA n s).im ≠ 0 := by
  simpa using hs

/-! ## §2. THE COLLAPSE — the full kernel is `π² sech²(π s)` on this line

This is the file's content.  `4n` is an even integer, so the whole `n`-dependence of the
abscissa is a multiple of `2π` inside `sin` and disappears; what is left is `sin(−π/2 + iπs)`,
which is `−cosh(π s)`.  Nothing here is asymptotic, approximate, or `n ≥ 1`. -/

/-- **`sin(π t) = −cosh(π s)` on the route-A line, at every `n` and every `s`.**  Exact, with
no sign to track: `4n` is even. -/
theorem sin_pi_lineA (n : ℕ) (s : ℝ) :
    Complex.sin ((Real.pi : ℂ) * lineA n s) = -((Real.cosh (Real.pi * s) : ℝ) : ℂ) := by
  have hsplit : (Real.pi : ℂ) * lineA n s
      = -((Real.pi : ℂ) / 2 - ((Real.pi * s : ℝ) : ℂ) * Complex.I)
        + ((-(2 * (n : ℤ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ)) := by
    simp only [lineA]
    push_cast
    ring
  rw [hsplit, Complex.sin_add_int_mul_two_pi, Complex.sin_neg,
    Complex.sin_pi_div_two_sub, Complex.cos_mul_I, Complex.ofReal_cosh]

/-- The kernel is therefore never zero on the contour — the side condition
`L7MidM123.Hn_eq_kernel_form` asks for, discharged here without a pole census. -/
theorem sin_pi_lineA_ne_zero (n : ℕ) (s : ℝ) :
    Complex.sin ((Real.pi : ℂ) * lineA n s) ≠ 0 := by
  rw [sin_pi_lineA, neg_ne_zero]
  -- `simpa` here rewrites the cast to `Complex.cosh (↑π * ↑s)` through `Complex.ofReal_cosh`
  -- and then the real hypothesis no longer matches; the explicit `ofReal_ne_zero` does not
  -- give simp the chance.  (Measured on this file's first elaboration.)
  exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos (Real.pi * s)).ne'

/-- **THE COLLAPSE.**  `(π / sin π t)²` on the route-A line is the REAL number
`(π / cosh π s)²` — positive, elementary, and with the minus of `sin_pi_lineA` squared away.
The `Ppol` arm therefore meets no complex analysis at all. -/
theorem kernel_lineA (n : ℕ) (s : ℝ) :
    ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * lineA n s)) ^ 2
      = (((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ) : ℂ) := by
  rw [sin_pi_lineA, div_neg, neg_sq]
  push_cast
  ring

/-- The kernel's value on the contour is a NONNEGATIVE real. -/
theorem kernel_lineA_nonneg (s : ℝ) :
    0 ≤ (Real.pi / Real.cosh (Real.pi * s)) ^ 2 := sq_nonneg _

/-- The shape `Zeta2L7IdSplit.PpolArm` takes on this line, stated for an ARBITRARY coefficient
`w` so that no second copy of `PpolArm` is spelled here (LEAN.md §6) and this file does not
import a module that was still in the landing queue when it was written.  A consumer applies it
at `w = Π(n) · aeval (lineA n s) (candidateM.Ppol n)`, which is `PpolArm n (lineA n s)`. -/
theorem arm_lineA (w : ℂ) (n : ℕ) (s : ℝ) :
    w * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * lineA n s)) ^ 2
      = w * (((Real.pi / Real.cosh (Real.pi * s)) ^ 2 : ℝ) : ℂ) := by
  rw [kernel_lineA]

/-! ## §3. The moment's TARGET, in the chain's vocabulary

`Zeta2Defs.momI M j = (Polynomial.bernoulli j).eval (M+1)` at the cell `M = ⌊C⌋`, and
`Zeta2Defs.Member.cell n = −4n − 1`.  The route-A abscissa is `C = −4n − ½`, so
`⌊C⌋ + 1 = C + ½ = −4n`: the cell index and the contour are the same number, and the moment law
this arm needs reads `∫ (C+is)^j π² sech²(π s) ds = 2π · B_j(C + ½) = 2π · momI (cell n) j`.
The off-by-one is the whole arm, which is why it is a theorem here and not a comment — and
`l7id_moment_check.py` FALSIFY-B scores the wrong-cell spelling red at every cell the chain
uses (with `M = 0`, where the two coincide, recorded as an INERT arm rather than a pass). -/

/-- **The cell index IS the route-A abscissa plus a half.**  Pure arithmetic, and the statement
that makes `momI` the right object to identify the moment with. -/
theorem cell_add_one (n : ℕ) : ((Zeta2Defs.candidateM.cell n : ℤ) : ℚ) + 1 = -(4 * n : ℚ) := by
  -- `simp` closes this outright; a trailing `push_cast; ring` errors "No goals" (LEAN.md §8,
  -- and it did, on this file's first elaboration).
  simp [Zeta2Defs.Member.cell, Zeta2Defs.candidateM]

/-- `momI` at the chain's cell, evaluated where the contour puts it. -/
theorem momI_cell_eq (n j : ℕ) :
    Zeta2Defs.momI (Zeta2Defs.candidateM.cell n) j
      = (Polynomial.bernoulli j).eval (-(4 * n : ℚ)) := by
  rw [Zeta2Defs.momI, cell_add_one]

/-- The same statement against A2's RECURSION rather than against the Bernoulli spelling —
`Zeta2Moments.momI_eq_bernoulli` is receipted, so this EXECUTES the composition (LEAN.md §3)
instead of asserting that the two `momI`s are the same object. -/
theorem momI_recursion_cell_eq (n j : ℕ) :
    Zeta2Moments.momI (Zeta2Defs.candidateM.cell n) j
      = (Polynomial.bernoulli j).eval (-(4 * n : ℚ)) := by
  rw [Zeta2Moments.momI_eq_bernoulli, cell_add_one]

/-- The route-A abscissa, as a rational, and its half-shift — the `C + ½` the moment law
evaluates `B_j` at.  Stated in ℚ because `momI` is rational; `lineA_re` is its ℝ twin. -/
theorem lineA_abscissa_add_half (n : ℕ) :
    (-4 * (n : ℚ) - 1 / 2) + 1 / 2 = -(4 * n : ℚ) := by ring

/-! ## §4. The ONE remaining analytic obligation, named

Everything else in the arm is algebra over ℚ.  This is the whole of what is left, it is
`n`-INDEPENDENT, and it is stated once so the next unit does not re-spell it.  Measured for
`m = 0..8` in `l7id_moment_check.py` ARM 4 against an exact prediction; odd moments vanish by
parity (ARM 4b), which is `B_k(½) = 0` at odd `k`. -/

/-- **`SechMomentTable`** — the even moments of `π² sech²(π s)` are `(−1)^m · 2π · B_{2m}(½)`.
Given this, the per-monomial moment law and hence `∫ PpolArm = 2πi · Π(n) · pnPoly n` are
binomial expansion plus the Bernoulli addition theorem, with no analysis left anywhere.
`T(0) = 2π` and `T(2) = π/6` are its two smallest instances. -/
def SechMomentTable : Prop :=
  ∀ m : ℕ, (∫ s : ℝ, s ^ (2 * m) * (Real.pi ^ 2 / Real.cosh (Real.pi * s) ^ 2))
    = (-1 : ℝ) ^ m * (2 * Real.pi)
        * (((Polynomial.bernoulli (2 * m)).eval (1 / 2 : ℚ) : ℚ) : ℝ)

/-- The table's `m = 0` instance, written out: `∫ π² sech²(π s) ds = 2π`.  Recorded as a
`Prop` rather than proved — `Real.hasDerivAt_tanh` is ABSENT at this pin (census), so even this
instance needs `tanh`'s derivative built first. -/
def SechMomentTableZero : Prop :=
  (∫ s : ℝ, Real.pi ^ 2 / Real.cosh (Real.pi * s) ^ 2) = 2 * Real.pi

/-- The table's head really is the `m = 0` case of the family, so the two names cannot drift
apart (LEAN.md §6).  `B_0(½) = 1`. -/
theorem sechMomentTable_zero_of (h : SechMomentTable) : SechMomentTableZero := by
  have h0 := h 0
  norm_num at h0
  unfold SechMomentTableZero
  exact h0

/-! ## §5. EDGES (LEAN.md §5) — asked of the real data

At `n = 0` the route-A line is `Re t = −½`, which is L7ID-0's OWN contour, and the cell is
`−1`, which is the cell `Zeta2Moments.momI_control_one`/`_two` are pinned at.  So the `n = 0`
instance of this file agrees with the two landed control values rather than merely resembling
them — and it is ALSO the instance at which the arm is empty, since `Ppol 0 = 0`. -/

/-- At `n = 0` the route-A line is `Re t = −½`. -/
theorem lineA_zero_re (s : ℝ) : (lineA 0 s).re = -(1 / 2 : ℝ) := by
  simp

/-- At `n = 0` the cell is `−1` — the cell `Zeta2Moments`' three control values are pinned at. -/
theorem cell_zero : Zeta2Defs.candidateM.cell 0 = -1 := by
  simp [Zeta2Defs.Member.cell, Zeta2Defs.candidateM]

/-- And this file's `momI_cell_eq` reproduces `Zeta2Moments.momI_control_one`'s value at that
cell: `B_1(0) = −½`.  The agreement is EXECUTED, not asserted. -/
theorem momI_cell_zero_one :
    Zeta2Moments.momI (Zeta2Defs.candidateM.cell 0) 1 = -(1 / 2 : ℚ) := by
  rw [cell_zero]
  exact Zeta2Moments.momI_control_one

/-- The `j = 0` moment is the cell-independent one: `B_0 = 1`, so the constant term of any
`Ppol` contributes `2π` times its coefficient whatever `n` is. -/
theorem momI_cell_zeroth (n : ℕ) :
    Zeta2Defs.momI (Zeta2Defs.candidateM.cell n) 0 = 1 := by
  rw [momI_cell_eq]
  simp

/-! ## §6. Receipts (LEAN.md §1) -/

#print axioms lineA_re
#print axioms lineA_im
#print axioms lineA_im_ne_zero
#print axioms sin_pi_lineA
#print axioms sin_pi_lineA_ne_zero
#print axioms kernel_lineA
#print axioms kernel_lineA_nonneg
#print axioms arm_lineA
#print axioms cell_add_one
#print axioms momI_cell_eq
#print axioms momI_recursion_cell_eq
#print axioms lineA_abscissa_add_half
#print axioms sechMomentTable_zero_of
#print axioms lineA_zero_re
#print axioms cell_zero
#print axioms momI_cell_zero_one
#print axioms momI_cell_zeroth

end Zeta2L7IdMoment
