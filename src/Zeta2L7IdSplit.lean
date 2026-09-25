/-
# Row L7ID — the `Ppol`/residue SPLIT of `R_n`, at every `n`, off the real axis

Row L7ID has five non-inherited obligations.  `Zeta2L7IdHinge.lean` closed the first (the hinge
off `ℍₒ`) on 2026-09-19 **and the same pass corrected the row's route sentence**: the `Ppol` /
residue split has to come BEFORE the termwise integration, not after it, because `R_n` has
degree `16n − 1 > 0` at every `n ≥ 1` and its hinge terms are then not integrable at all.  This
file discharges the split.

## What is proved here

    Hn n t  =  PpolArm n t  +  ResidArm n t          (Im t ≠ 0, every n)

with

    PpolArm  n t = Π(n) · Ppol_n(t)                        · (π / sin π t)²
    ResidArm n t = Π(n) · Σ_{k ∈ window n} c_k / (t + k)   · (π / sin π t)²

`Ppol` and `c_k` are `Zeta2Defs.Member.Ppol` and `Member.ck` — the chain's own objects at
`candidateM`, not restatements — so RESID's landed `Zeta2Resid.Ppol_partial_fractions` is
CONSUMED rather than quoted (LEAN.md §3).  The two arms are then exactly the two the route
names, and the residue arm alone is expanded by the hinge:

    ResidArm n t = ∑'_{m ∈ ℤ} ∑_{k ∈ window n} Π(n)·c_k / ((t + k)(t + m)²)

whose terms decay like `|t|^{-3}` — which is the shape `integral_tsum_of_summable_integral_norm`
can consume and which the unsplit family could not.

## The bridge this needed, and it is the file's real content

`Zeta2L7IdHinge.Rfac` is a ratio of eight `Γ`'s; `Zeta2Defs.Member.numPoly/denPoly` are
`Polynomial ℚ`.  Nothing in the chain related them — the four shifts pair up as

    Γ(t+13n+1)/Γ(t+1)     = (t+1)_{13n}        = block 1 (13n)
    Γ(t+11n+1)/Γ(t+2n+1)  = (t+2n+1)_{9n}      = block (2n+1) (9n)
    Γ(t+9n+1)/Γ(t+4n+1)   = (t+4n+1)_{5n}      = block (4n+1) (5n)
    Γ(t+15n+1)/Γ(t+26n+2) = 1/(t+15n+1)_{11n+1} = 1/(block (15n+1) (11n+1))

and `Rfac_eq_ratio` below proves it.  `Complex.Gamma_nat_add` is ABSENT at this pin (measured),
so `Gamma_add_natCast` builds the shift by induction on `Complex.Gamma_add_one`.

**`Im t ≠ 0` discharges every side condition in the file** — the `Γ` non-vanishing
(`Complex.Gamma_ne_zero` wants `t + c ≠ -m` and `-m` is real), the `Gamma_add_one` hypotheses,
and the twelve window poles `t + k ≠ 0` — because a shift by a real number does not change
`Im`.  That is why the statements are contour-free and free in `n`, exactly like the hinge's.

## What this file does NOT do

* It does not integrate anything.  The interchange (obligation 3) now has its family and its
  decay, and neither is proved here.
* The `Ppol` arm is stated, not evaluated: the moment arm against the FULL kernel
  (`Zeta2Moments.momI_eq_bernoulli`, the translation law, the `sech²` expansion) is the rest of
  obligation 4 and is untouched.
* It says nothing about `candidateM.rn`, so row L7ID is NOT closed by it.

## The chain cell's `9n / 9n / 9n` is NOT a defect — checked, because it looks like one

The cell and `Zeta2L7IdHinge.lean`'s header both spell `R_n` as
`(t+1)_{9n}·(t+2n+1)_{9n}·(t+4n+1)_{9n}/(t+15n+1)_{11n+1}`, where the shifts give `13n`, `9n`,
`5n`.  A first pass of `l7id_split_check.py` filed that as a doc defect; **its own falsifier
refuted the filing**.  The two are the same multiset of integer roots — `[1,2n]` once,
`[2n+1,4n]` twice, `[4n+1,9n]` three times, `[9n+1,11n]` twice, `[11n+1,13n]` once, either way
— so they are the same function, checked at `n = 0..6` as multisets and exactly at `t = 7/3`
(ARM 1E), with `9n/9n/8n` confirming the test can go red (ARM 1F).  The file's own `block`
decomposition is the `13n/9n/5n` one because that is what `Member.numPoly` is written in.

Receipts: 25, all `[propext, Classical.choice, Quot.sound]`.  `lean` rc read separately.
Falsifier: `falsify_l7idsplit.sh` → `out_l7idsplit_falsify.txt`.
Second implementation: `l7id_split_check.py` / `.out` (13 arms, 3 of them falsifiers, exact
`Fraction` and exact Gaussian-rational arithmetic; the float version of two of its arms
"refuted" true statements and is documented in its header).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732, buildbox.
-/
import Mathlib
import Zeta2Defs
import Zeta2Resid
import Zeta2SinSqSeries
import L7MidM5
import Zeta2L7IdHinge

open Polynomial Complex

namespace Zeta2L7IdSplit

open Zeta2Defs

/-! ## §1. `Im t ≠ 0` discharges every side condition

Three lemmas, one hypothesis.  Each is the reason a later statement carries no contour and no
`1 ≤ n`: a shift by a REAL number leaves `Im` alone, and every obstruction in this file — a
vanishing denominator, a vanishing `Γ`, a `Gamma_add_one` side condition — is the vanishing of
such a shift. -/

/-- A point off the real axis is not cancelled by any real shift. -/
theorem add_ne_zero {t c : ℂ} (ht : t.im ≠ 0) (hc : c.im = 0) : t + c ≠ 0 := by
  intro h
  apply ht
  have := congrArg Complex.im h
  simp [hc] at this
  exact this

/-- `Γ` does not vanish at a real shift of a non-real point.  `Complex.Gamma_ne_zero` asks for
`s ≠ -m` at every natural `m`, and `-m` is real. -/
theorem Gamma_shift_ne_zero {t : ℂ} (ht : t.im ≠ 0) (c : ℂ) (hc : c.im = 0) :
    Complex.Gamma (t + c) ≠ 0 := by
  refine Complex.Gamma_ne_zero ?_
  intro m h
  apply ht
  have := congrArg Complex.im h
  simp [hc] at this
  exact this

/-- **The Pochhammer shift of `Γ` by a natural number.**  `Complex.Gamma_nat_add` is ABSENT at
this pin (measured, `Census7.lean`), so this is an induction on `Complex.Gamma_add_one`, whose
`≠ 0` side condition is `add_ne_zero` at every step. -/
theorem Gamma_add_natCast {t : ℂ} (ht : t.im ≠ 0) (L : ℕ) :
    Complex.Gamma (t + (L : ℂ)) = (∏ i ∈ Finset.range L, (t + (i : ℂ))) * Complex.Gamma t := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hne : t + (L : ℂ) ≠ 0 := add_ne_zero ht (by simp)
    have hstep : (t : ℂ) + ((L + 1 : ℕ) : ℂ) = (t + (L : ℂ)) + 1 := by push_cast; ring
    rw [hstep, Complex.Gamma_add_one _ hne, ih, Finset.prod_range_succ]
    ring

/-! ## §2. `Zeta2Defs.block` under `aeval` -/

/-- `block c len` evaluated at a complex point.  `Polynomial.aeval_prod` is PRESENT at this pin
and is NOT this lemma — it is about `A × B` product types, not `Finset.prod` — so the transfer
goes through `map_prod` on the `AlgHom`. -/
theorem aeval_block (c len : ℕ) (t : ℂ) :
    aeval t (Zeta2Defs.block c len) = ∏ i ∈ Finset.range len, (t + ((c + i : ℕ) : ℂ)) := by
  rw [Zeta2Defs.block, map_prod]
  exact Finset.prod_congr rfl fun i _ => by simp

/-- A `block` does not vanish off the real axis: every factor is a real shift of `t`. -/
theorem aeval_block_ne_zero {t : ℂ} (ht : t.im ≠ 0) (c len : ℕ) :
    aeval t (Zeta2Defs.block c len) ≠ 0 := by
  rw [aeval_block]
  exact Finset.prod_ne_zero_iff.2 fun i _ => add_ne_zero ht (by simp)

/-- **`Γ(t + (c+len)) = block c len (t) · Γ(t + c)`** — the shift stated at the SHAPE
`Zeta2Defs.block` is written in, so the four `Γ` pairings below are one rewrite each. -/
theorem Gamma_block_shift {t : ℂ} (ht : t.im ≠ 0) (c len : ℕ) :
    Complex.Gamma (t + ((c + len : ℕ) : ℂ))
      = aeval t (Zeta2Defs.block c len) * Complex.Gamma (t + (c : ℂ)) := by
  have him : (t + (c : ℂ)).im ≠ 0 := by simpa using ht
  have h : (t : ℂ) + ((c + len : ℕ) : ℂ) = (t + (c : ℂ)) + (len : ℂ) := by push_cast; ring
  rw [h, Gamma_add_natCast him len, aeval_block]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by push_cast; ring

/-! ## §3. The candidate's shifts pair up

The four arithmetic facts that make `L7MidM123`'s eight `Γ` shifts into `Zeta2Defs`' three
numerator blocks and one denominator block.  They are `omega` facts and they are stated rather
than inlined because each names WHICH pairing is meant. -/

theorem a₁_eq (n : ℕ) : L7MidM123.a₁ n = 1 + 13 * n := by simp only [L7MidM123.a₁]; omega
theorem a₂_eq (n : ℕ) : L7MidM123.a₂ n = (2 * n + 1) + 9 * n := by simp only [L7MidM123.a₂]; omega
theorem a₃_eq (n : ℕ) : L7MidM123.a₃ n = (4 * n + 1) + 5 * n := by simp only [L7MidM123.a₃]; omega
theorem b₄_eq (n : ℕ) : L7MidM123.b₄ n = (15 * n + 1) + (11 * n + 1) := by
  simp only [L7MidM123.b₄]; omega

/-- `candidateM.numPoly` spelled in the three blocks the `Γ` pairings produce. -/
theorem numPoly_eq (n : ℕ) :
    candidateM.numPoly n
      = Zeta2Defs.block 1 (13 * n) * Zeta2Defs.block (2 * n + 1) (9 * n)
          * Zeta2Defs.block (4 * n + 1) (5 * n) := by
  simp [Member.numPoly, candidateM]

/-- `candidateM.denPoly` is the single block the `b₄`/`a₄` pairing produces. -/
theorem denPoly_eq (n : ℕ) :
    candidateM.denPoly n = Zeta2Defs.block (15 * n + 1) (11 * n + 1) := by
  simp [Member.denPoly, candidateM]

/-- `L7MidM123.Pi_n` (a real) and `Zeta2Defs.Member.Pin` (a rational) are the SAME prefactor
`(11n)!/((13n)!(9n)!(5n)!)`.  No second definition of `Π(n)` is introduced by this file. -/
theorem Pi_n_eq (n : ℕ) : ((L7MidM123.Pi_n n : ℝ) : ℂ) = ((candidateM.Pin n : ℚ) : ℂ) := by
  simp only [L7MidM123.Pi_n, Member.Pin, candidateM]
  push_cast
  ring

/-! ## §4. THE BRIDGE — the eight `Γ`'s ARE the chain's rational function -/

/-- **`R_n` is `Π(n)·numPoly/denPoly`.**  The step nothing in the chain had: `Zeta2L7IdHinge.Rfac`
is a ratio of eight `Γ`'s and `Member.numPoly`/`denPoly` are `Polynomial ℚ`, and until this
lemma no theorem related them.  Off the real axis, and at every `n`. -/
theorem Rfac_eq_ratio (n : ℕ) {t : ℂ} (ht : t.im ≠ 0) :
    Zeta2L7IdHinge.Rfac n t
      = ((candidateM.Pin n : ℚ) : ℂ) * aeval t (candidateM.numPoly n)
          / aeval t (candidateM.denPoly n) := by
  have hb1 : Complex.Gamma (t + ((L7MidM123.b₁ n : ℕ) : ℂ)) ≠ 0 :=
    Gamma_shift_ne_zero ht _ (by simp)
  have hb2 : Complex.Gamma (t + ((L7MidM123.b₂ n : ℕ) : ℂ)) ≠ 0 :=
    Gamma_shift_ne_zero ht _ (by simp)
  have hb3 : Complex.Gamma (t + ((L7MidM123.b₃ n : ℕ) : ℂ)) ≠ 0 :=
    Gamma_shift_ne_zero ht _ (by simp)
  have ha4 : Complex.Gamma (t + ((L7MidM123.a₄ n : ℕ) : ℂ)) ≠ 0 :=
    Gamma_shift_ne_zero ht _ (by simp)
  have hD : aeval t (Zeta2Defs.block (15 * n + 1) (11 * n + 1)) ≠ 0 :=
    aeval_block_ne_zero ht _ _
  have G1 : Complex.Gamma (t + ((L7MidM123.a₁ n : ℕ) : ℂ))
      = aeval t (Zeta2Defs.block 1 (13 * n))
          * Complex.Gamma (t + ((L7MidM123.b₁ n : ℕ) : ℂ)) := by
    rw [a₁_eq n, show L7MidM123.b₁ n = 1 from rfl]
    exact Gamma_block_shift ht 1 (13 * n)
  have G2 : Complex.Gamma (t + ((L7MidM123.a₂ n : ℕ) : ℂ))
      = aeval t (Zeta2Defs.block (2 * n + 1) (9 * n))
          * Complex.Gamma (t + ((L7MidM123.b₂ n : ℕ) : ℂ)) := by
    rw [a₂_eq n, show L7MidM123.b₂ n = 2 * n + 1 from rfl]
    exact Gamma_block_shift ht (2 * n + 1) (9 * n)
  have G3 : Complex.Gamma (t + ((L7MidM123.a₃ n : ℕ) : ℂ))
      = aeval t (Zeta2Defs.block (4 * n + 1) (5 * n))
          * Complex.Gamma (t + ((L7MidM123.b₃ n : ℕ) : ℂ)) := by
    rw [a₃_eq n, show L7MidM123.b₃ n = 4 * n + 1 from rfl]
    exact Gamma_block_shift ht (4 * n + 1) (5 * n)
  have G4 : Complex.Gamma (t + ((L7MidM123.b₄ n : ℕ) : ℂ))
      = aeval t (Zeta2Defs.block (15 * n + 1) (11 * n + 1))
          * Complex.Gamma (t + ((L7MidM123.a₄ n : ℕ) : ℂ)) := by
    rw [b₄_eq n, show L7MidM123.a₄ n = 15 * n + 1 from rfl]
    exact Gamma_block_shift ht (15 * n + 1) (11 * n + 1)
  rw [Zeta2L7IdHinge.Rfac, Pi_n_eq n, G1, G2, G3, G4, numPoly_eq n, denPoly_eq n]
  simp only [map_mul]
  -- `field_simp` CLOSES this one outright; a trailing `ring` errors with "No goals"
  -- (LEAN.md §8 — read the error, do not cargo-cult the pair).
  field_simp

/-! ## §5. THE SPLIT, over ℂ

`Zeta2Resid.member_eq_Ppol_add_residues` is the same statement over `ℚ`.  It cannot be used
here — L7ID's `t` is a point of a vertical CONTOUR — and it is not restated either: the two
polynomial identities it rests on (`Zeta2Resid.denPoly_eq_prod_window` and
`Zeta2Resid.Ppol_partial_fractions`, both `Polynomial ℚ` facts carrying no side condition) are
transported by `aeval t`, which is a ring hom, and the rest of the argument is repeated at the
new scalars.  That is the whole reason RESID's primary statement was stated as a polynomial
identity rather than an evaluated one. -/

/-- The denominator as the product over the pole window, at a complex point. -/
theorem aeval_denPoly (m : Member) (hm : m.WF) (n : ℕ) (t : ℂ) :
    aeval t (m.denPoly n) = ∏ k ∈ m.window n, (t + ((k : ℕ) : ℂ)) := by
  rw [Zeta2Resid.denPoly_eq_prod_window m hm n, map_prod]
  exact Finset.prod_congr rfl fun k _ => by simp

/-- **The `Ppol`/residue split over ℂ, for any member, off the real axis.** -/
theorem aeval_ratio_eq_Ppol_add_residues (m : Member) (hm : m.WF) (n : ℕ) {t : ℂ}
    (ht : t.im ≠ 0) :
    aeval t (m.numPoly n) / aeval t (m.denPoly n)
      = aeval t (m.Ppol n)
        + ∑ k ∈ m.window n, ((m.ck n k : ℚ) : ℂ) / (t + ((k : ℕ) : ℂ)) := by
  have hne : ∀ k ∈ m.window n, t + ((k : ℕ) : ℂ) ≠ 0 := fun _ _ => add_ne_zero ht (by simp)
  have hden := aeval_denPoly m hm n t
  have hdne : aeval t (m.denPoly n) ≠ 0 := by
    rw [hden]; exact Finset.prod_ne_zero_iff.2 hne
  have hrem : aeval t (m.numPoly n %ₘ m.denPoly n) / aeval t (m.denPoly n)
      = ∑ k ∈ m.window n, ((m.ck n k : ℚ) : ℂ) / (t + ((k : ℕ) : ℂ)) := by
    rw [Zeta2Resid.Ppol_partial_fractions m hm n, map_sum, hden, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hEne : (∏ j ∈ (m.window n).erase k, (t + ((j : ℕ) : ℂ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => hne j (Finset.mem_of_mem_erase hj)
    have hkne : t + ((k : ℕ) : ℂ) ≠ 0 := hne k hk
    rw [map_mul, map_prod,
      Finset.prod_congr rfl (fun j _ => by simp :
        ∀ j ∈ (m.window n).erase k, aeval t (X + C ((j : ℕ) : ℚ)) = t + ((j : ℕ) : ℂ)),
      ← Finset.mul_prod_erase _ _ hk]
    simp only [aeval_C, eq_ratCast]
    field_simp
  have hspec := congrArg (aeval t) (m.Ppol_spec n)
  simp only [map_add, map_mul] at hspec
  rw [← hspec, add_div, mul_comm (aeval t (m.denPoly n)), mul_div_assoc, div_self hdne, mul_one,
    hrem, add_comm]

/-- **`R_n` split.**  The bridge composed with the split, at the candidate. -/
theorem Rfac_eq_Ppol_add_residues (n : ℕ) {t : ℂ} (ht : t.im ≠ 0) :
    Zeta2L7IdHinge.Rfac n t
      = ((candidateM.Pin n : ℚ) : ℂ) * aeval t (candidateM.Ppol n)
        + ∑ k ∈ candidateM.window n,
            ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ) / (t + ((k : ℕ) : ℂ)) := by
  rw [Rfac_eq_ratio n ht, mul_div_assoc,
    aeval_ratio_eq_Ppol_add_residues candidateM candidateM_wf n ht, mul_add, Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  push_cast
  ring

/-! ## §6. THE TWO ARMS

The route's two halves, named.  They are `def`s rather than `let`s inside a statement so that
obligation 3 and the moment arm can be stated ABOUT them — a consumer that has to re-spell the
arm every time is how two copies of one object appear (LEAN.md §6). -/

/-- The `Ppol` arm: the polynomial part against the FULL kernel `(π/sin πt)²`.  This one never
meets the hinge — `Ppol` has degree `16n − 1`, so its `m`-th hinge terms are not integrable at
any `n ≥ 1` (`l7id_split_check.py` ARM 8) — and goes through the moments instead. -/
noncomputable def PpolArm (n : ℕ) (t : ℂ) : ℂ :=
  ((candidateM.Pin n : ℚ) : ℂ) * aeval t (candidateM.Ppol n)
    * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * t)) ^ 2

/-- The RESID arm: the residue part against the full kernel.  This one decays like `|t|^{-1}`,
so its hinge terms decay like `|t|^{-3}` and the interchange is available on it. -/
noncomputable def ResidArm (n : ℕ) (t : ℂ) : ℂ :=
  (∑ k ∈ candidateM.window n,
      ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ) / (t + ((k : ℕ) : ℂ)))
    * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * t)) ^ 2

/-- **ROW L7ID'S FOURTH OBLIGATION, THE SPLIT, DISCHARGED AT EVERY `n`.**  `Hn` is the `Ppol`
arm plus the RESID arm, off the real axis.  Contour-free and free in `n`, like the hinge. -/
theorem Hn_eq_PpolArm_add_ResidArm (n : ℕ) {t : ℂ} (ht : t.im ≠ 0) :
    L7MidM123.Hn n t = PpolArm n t + ResidArm n t := by
  have hker : L7MidM123.Hn n t
      = Zeta2L7IdHinge.Rfac n t
          * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * t)) ^ 2 := by
    -- the two spellings are syntactically equal once `Rfac` is unfolded; no `ring` is needed,
    -- and a trailing one errors "No goals" (LEAN.md §8).
    rw [L7MidM123.Hn_eq_kernel_form n t (Zeta2L7IdHinge.sin_pi_ne_zero_of_im_ne_zero ht),
      Zeta2L7IdHinge.Rfac]
  rw [hker, Rfac_eq_Ppol_add_residues n ht, PpolArm, ResidArm]
  ring

/-- The split on the σ̃ contour, at every `n` — the instance `Zeta2L7IdHinge.hinge_on_lineB`'s
consumers meet.  `s ≠ 0` is the single real point of the contour, `volume`-null
(`Zeta2L7IdHinge.ae_ne_zero`). -/
theorem Hn_lineB_eq_PpolArm_add_ResidArm (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    L7MidM123.Hn n (L7MidM5.lineB n s)
      = PpolArm n (L7MidM5.lineB n s) + ResidArm n (L7MidM5.lineB n s) :=
  Hn_eq_PpolArm_add_ResidArm n (by rw [Zeta2L7IdHinge.lineB_im]; exact hs)

/-! ## §7. The RESID arm expanded by the hinge — the shape the interchange consumes

This is the step the route calls "expand the kernel by the hinge, then integrate termwise", now
applied to the arm on which it is AVAILABLE.  The unsplit family could not take it: `Rfac` grows
like `|s|^{16n−3}` and `integral_tsum_of_summable_integral_norm`'s first hypothesis is false at
every `n ≥ 1` (`Zeta2L7IdHinge`'s header; `l7id_ratfun_check.py` ARM 4).  Here every term is
`c/((t+k)(t+m)²)`, which decays like `|t|^{-3}`. -/

/-- **The RESID arm, termwise.**  `tsum_mul_left` is unconditional over a division ring, so no
summability hypothesis is created by pushing the finite `k`-sum and the constant inside. -/
theorem ResidArm_eq_tsum (n : ℕ) {t : ℂ} (ht : t.im ≠ 0) :
    ResidArm n t
      = ∑' m : ℤ, ∑ k ∈ candidateM.window n,
          ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
            / ((t + ((k : ℕ) : ℂ)) * (t + (m : ℂ)) ^ 2) := by
  rw [ResidArm, div_pow, Zeta2L7IdHinge.hinge_off_axis ht, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [Finset.sum_mul]
  -- `ring` does NOT close `a/b * (1/c) = a/(b*c)` here: it normalises `(t+m)^2` and then has
  -- two inverses of non-atoms.  `div_mul_div_comm` is the identity that is actually meant.
  exact Finset.sum_congr rfl fun k _ => by rw [div_mul_div_comm, mul_one]

/-- The same on the σ̃ contour. -/
theorem ResidArm_lineB_eq_tsum (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    ResidArm n (L7MidM5.lineB n s)
      = ∑' m : ℤ, ∑ k ∈ candidateM.window n,
          ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
            / ((L7MidM5.lineB n s + ((k : ℕ) : ℂ)) * (L7MidM5.lineB n s + (m : ℂ)) ^ 2) :=
  ResidArm_eq_tsum n (by rw [Zeta2L7IdHinge.lineB_im]; exact hs)

/-- **`Hn` fully split and expanded**, the statement obligation 3 starts from: one arm that must
go through the moments, one arm that is a `tsum` of `|t|^{-3}` terms. -/
theorem Hn_lineB_split_expanded (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    L7MidM123.Hn n (L7MidM5.lineB n s)
      = PpolArm n (L7MidM5.lineB n s)
        + ∑' m : ℤ, ∑ k ∈ candidateM.window n,
            ((candidateM.Pin n * candidateM.ck n k : ℚ) : ℂ)
              / ((L7MidM5.lineB n s + ((k : ℕ) : ℂ))
                  * (L7MidM5.lineB n s + (m : ℂ)) ^ 2) := by
  rw [Hn_lineB_eq_PpolArm_add_ResidArm n hs, ResidArm_lineB_eq_tsum n hs]

/-! ## §8. Edge cases, checked rather than assumed (LEAN.md §5)

`n = 0` is where the window is the single pole `k = 1` and `Ppol 0 = 0`; the split still holds,
and it says the `Ppol` arm VANISHES there.  That is the arithmetic reason L7ID-0 never met the
non-integrability this row's route was re-ordered for. -/

/-- `Ppol 0 = 0`, derived from `Ppol_spec` and RESID's own `n = 0` corollary rather than from a
second computation of the division: at `n = 0` the remainder is the whole numerator, so
`denPoly 0 * Ppol 0 = 0` and `denPoly` is monic, hence nonzero. -/
theorem Ppol_zero : candidateM.Ppol 0 = 0 := by
  have hnum : candidateM.numPoly 0 = 1 := by simp [Member.numPoly, Zeta2Defs.block, candidateM]
  have hspec := candidateM.Ppol_spec 0
  rw [Zeta2Resid.candidate_partial_fractions_zero, hnum] at hspec
  have hz : candidateM.denPoly 0 * candidateM.Ppol 0 = 0 := by linear_combination hspec
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h (candidateM.denPoly_monic 0).ne_zero
  · exact h

/-- At `n = 0` the `Ppol` arm is identically zero. -/
theorem PpolArm_zero (t : ℂ) : PpolArm 0 t = 0 := by
  rw [PpolArm, Ppol_zero]
  simp

/-- So at `n = 0` the whole of `Hn` is the RESID arm, and every term of its expansion decays
like `|t|^{-3}`.  This is L7ID-0's situation, DERIVED from the general split. -/
theorem Hn_zero_eq_ResidArm {t : ℂ} (ht : t.im ≠ 0) :
    L7MidM123.Hn 0 t = ResidArm 0 t := by
  rw [Hn_eq_PpolArm_add_ResidArm 0 ht, PpolArm_zero, zero_add]

end Zeta2L7IdSplit

#print axioms Zeta2L7IdSplit.add_ne_zero
#print axioms Zeta2L7IdSplit.Gamma_shift_ne_zero
#print axioms Zeta2L7IdSplit.Gamma_add_natCast
#print axioms Zeta2L7IdSplit.aeval_block
#print axioms Zeta2L7IdSplit.aeval_block_ne_zero
#print axioms Zeta2L7IdSplit.Gamma_block_shift
#print axioms Zeta2L7IdSplit.a₁_eq
#print axioms Zeta2L7IdSplit.a₂_eq
#print axioms Zeta2L7IdSplit.a₃_eq
#print axioms Zeta2L7IdSplit.b₄_eq
#print axioms Zeta2L7IdSplit.numPoly_eq
#print axioms Zeta2L7IdSplit.denPoly_eq
#print axioms Zeta2L7IdSplit.Pi_n_eq
#print axioms Zeta2L7IdSplit.Rfac_eq_ratio
#print axioms Zeta2L7IdSplit.aeval_denPoly
#print axioms Zeta2L7IdSplit.aeval_ratio_eq_Ppol_add_residues
#print axioms Zeta2L7IdSplit.Rfac_eq_Ppol_add_residues
#print axioms Zeta2L7IdSplit.Hn_eq_PpolArm_add_ResidArm
#print axioms Zeta2L7IdSplit.Hn_lineB_eq_PpolArm_add_ResidArm
#print axioms Zeta2L7IdSplit.ResidArm_eq_tsum
#print axioms Zeta2L7IdSplit.ResidArm_lineB_eq_tsum
#print axioms Zeta2L7IdSplit.Hn_lineB_split_expanded
#print axioms Zeta2L7IdSplit.Ppol_zero
#print axioms Zeta2L7IdSplit.PpolArm_zero
#print axioms Zeta2L7IdSplit.Hn_zero_eq_ResidArm
