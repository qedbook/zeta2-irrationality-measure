/-
# Row STAR-ID — the COMPOSITION: (i) spelled into `Phi_rho`'s `hr`, and (★) executed at the member

`docs/future/zeta2-lean-chain.md` row STAR-ID.  Added 2026-09-17 by the row's closing unit.

**HEADLINE: `Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.**  This file
discharges two of the three things the row still owed — the `hr` spelling and the composition
with STAR.  The third, part (iii)'s `'alt'` sign, is `Zeta2StarIdSign.lean`.

**WHAT THIS FILE PAYS, and why neither half was free.**

1. **The `hr` spelling.**  `Zeta2T1Eval.Phi_rho` (row PHI-EVAL, closed) quantifies over an
   ARBITRARY representing `Rep` under a hypothesis about the FUNCTION.  `Zeta2StarId`
   (row STAR-ID (i), closed) proves that function.  Spelling one into the other is not a
   rewrite, because the two exceptional sets differ: `rho_eq_member` holds only where
   `denPoly n` and the rebase denominator `D_n = afProd pa0Facs` are ALSO nonzero, and for
   `j > 0` neither zero set is inside `mem.window (n+j)`.  So `Phi_rho` as landed could not be
   applied at all.  `Zeta2T1Eval.Phi_rho_off` — the same theorem off a caller-supplied extra
   `Finset ℚ` — was added in that file for this, and `Phi_rho` is now its `E := ∅` corollary,
   so there is ONE proof and not two.  `badK` below is that extra set, read off the `prI` run
   form `Zeta2StarId` proves rather than off a docstring: three runs for `D_n` and one pole
   window per index.

2. **The composition with STAR.**  `StarForallCandt1.star_forall` is a statement about the
   engine's `F`; `Zeta2StarB1.star_telescopes` is B1's abstract interface.  `star_identity`
   below EXECUTES the first into the second's `StarIdentity` shape at `v = n`, and
   `star_telescopes_member` discharges all six of its hypotheses from landed theorems —
   `hu` from `Zeta2StarId.star_u`, `hρ` from `Zeta2StarId.rho_eq_member`, `hc`/`hc1` from
   `cFacs = []`, `hS` from the definition of the antidifference.  The conclusion is in TARGET
   vocabulary: the sum is over `candidateM.numPoly (n+j) / candidateM.denPoly (n+j)`, not over
   the engine's `ρ j`.  LEAN.md §3 is why this is a theorem and not a remark: composition has
   failed on casts and indexing BOTH times it was left to paper in this program.

**WHAT THIS FILE DOES NOT DO.**  It does not apply the contour functional to the telescoping —
turning `∑ⱼ Ãⱼ · Φ(ρ_{n+j}) = 0` into `hrecq` is row **L1-ASM**.  It says nothing about the
cleared `cⱼ` (that is (ii), landed) nor about the sign (that is (iii)).  Nothing here transports
to ℝ; that is row **L4-BR**.

**NON-VACUITY IS PROVED, not assumed.**  `repR_satisfies` exhibits a `Rep` meeting `star_phi_rho`'s
hypothesis, so the theorem is not green-because-empty.  §6's `bad_is_inhabited` and
`badK_not_everything` pin the exceptional set from both sides: it is nonempty (so it is doing
work) and it is not all of ℚ (so the theorems have content).

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2StarIdPhi.lean

It imports the GENERATED `StarForallCandt1Base` AND `StarForallCandt1Assemble` (the module
carrying `star_forall`), pinned by `modules/MANIFEST-cand-t1-kernel.sha256`, so a wrong-flavoured
base REFUSES rather than skips.  Receipts: `out_axioms_staridphi.txt`.
Falsifier: `falsify_staridphi.sh --lean`, arms named by `routea_error_at.py`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2T1Eval
import Zeta2StarId
import Zeta2StarB1
import StarForallCandt1Assemble

namespace Zeta2StarIdPhi

open Polynomial Finset Zeta2PrI Zeta2Defs Zeta2T1Shift Zeta2StarId StarForallCandt1

/-! ## 1. The exceptional set — every `t` at which the (★) rebase is not a statement

`rho_eq_member` divides by three things.  Each is a `prI` run, so its zero set is
`{−k : k ∈ Icc a b}` and the union is one `Finset ℕ`.  The bounds are the ones
`Zeta2StarId.mDen` / `.dPr` carry, and `window_eq` ties the pole window to them by `rfl` rather
than by a reading of `Zeta2Defs`. -/

/-- `candidateM.window m` in numerals: `α₄ = 15`, `β₄ = 26`. -/
theorem window_eq (m : ℕ) : candidateM.window m = Icc (15 * m + 1) (26 * m + 1) := rfl

/-- The forbidden `k`: the three runs of `D_n`, and the pole windows of `denPoly (n+j)` for
every `j ≤ 3` (which includes `denPoly n` at `j = 0`). -/
def badK (n : ℕ) : Finset ℕ :=
  Icc (2 * n + 1) (2 * n + 6) ∪ Icc (4 * n + 1) (4 * n + 12)
    ∪ Icc (26 * n + 2) (26 * n + 79)
    ∪ candidateM.window n ∪ candidateM.window (n + 1)
    ∪ candidateM.window (n + 2) ∪ candidateM.window (n + 3)

/-- The same set as forbidden values of `t`. -/
noncomputable def bad (n : ℕ) : Finset ℚ := (badK n).image (fun k : ℕ => -(k : ℚ))

theorem ne_of_not_bad {n : ℕ} {t : ℚ} (ht : t ∉ bad n) : ∀ k ∈ badK n, t + (k : ℚ) ≠ 0 := by
  intro k hk hc
  exact ht (Finset.mem_image.2 ⟨k, hk, by linarith⟩)

theorem d2_sub (n : ℕ) : Icc (2 * n + 1) (2 * n + 6) ⊆ badK n := by
  intro k hk; simp only [badK, Finset.mem_union]; tauto

theorem d4_sub (n : ℕ) : Icc (4 * n + 1) (4 * n + 12) ⊆ badK n := by
  intro k hk; simp only [badK, Finset.mem_union]; tauto

theorem d26_sub (n : ℕ) : Icc (26 * n + 2) (26 * n + 79) ⊆ badK n := by
  intro k hk; simp only [badK, Finset.mem_union]; tauto

theorem win_sub (n j : ℕ) (hj : j ≤ 3) : candidateM.window (n + j) ⊆ badK n := by
  intro k hk
  simp only [badK, Finset.mem_union]
  interval_cases j
  · exact Or.inl (Or.inl (Or.inl (Or.inr hk)))
  · exact Or.inl (Or.inl (Or.inr hk))
  · exact Or.inl (Or.inr hk)
  · exact Or.inr hk

/-- A `prI` run is nonzero exactly when no `t + k` in it is. -/
theorem prI_ne_zero (t : ℚ) (a b : ℕ) (h : ∀ k ∈ Icc a b, t + (k : ℚ) ≠ 0) : prI t a b ≠ 0 := by
  simp only [prI]
  exact Finset.prod_ne_zero_iff.2 h

theorem den_ne (n j : ℕ) (hj : j ≤ 3) (t : ℚ) (ht : t ∉ bad n) :
    (candidateM.denPoly (n + j)).eval t ≠ 0 := by
  rw [denPoly_eval, mDen]
  refine prI_ne_zero t _ _ fun k hk => ne_of_not_bad ht k (win_sub n j hj ?_)
  rw [window_eq]; exact hk

theorem dPr_ne (n : ℕ) (t : ℚ) (ht : t ∉ bad n) : (afProd pa0Facs t).eval (n : ℚ) ≠ 0 := by
  rw [pa0_prI, paPr_zero, dPr]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact prI_ne_zero t _ _ fun k hk => ne_of_not_bad ht k (d2_sub n hk)
  · exact prI_ne_zero t _ _ fun k hk => ne_of_not_bad ht k (d4_sub n hk)
  · exact prI_ne_zero t _ _ fun k hk => ne_of_not_bad ht k (d26_sub n hk)

/-! ## 2. The (★) datum and the member's function, as functions of `t` -/

/-- `u` — the (★) rebased member `ρₙ / D_n`, at the chain's own `numPoly`/`denPoly`. -/
noncomputable def uStar (n : ℕ) (t : ℚ) : ℚ :=
  (candidateM.numPoly n).eval t
    / ((candidateM.denPoly n).eval t * (afProd pa0Facs t).eval (n : ℚ))

/-- `Pa j` at `v = n`, indexed by the engine's own list. -/
noncomputable def PaE (n j : ℕ) (t : ℚ) : ℚ := (afProd (paF j) t).eval (n : ℚ)

/-- The (★) datum `ρ j = u · Pa j` — the object `star_forall` is about. -/
noncomputable def rhoStar (n j : ℕ) (t : ℚ) : ℚ := uStar n t * PaE n j t

/-- The MEMBER's function `R_{n+j}/Π(n+j)` — the object `Phi_rho`'s `hr` is about. -/
noncomputable def rhoMem (n j : ℕ) (t : ℚ) : ℚ :=
  (candidateM.numPoly (n + j)).eval t / (candidateM.denPoly (n + j)).eval t

/-- **(i), off the finite set where it is a statement at all.**  `Zeta2StarId.rho_eq_member`
with its three side conditions discharged from `t ∉ bad n`. -/
theorem rhoStar_eq_rhoMem (n j : ℕ) (hj : j ≤ 3) (t : ℚ) (ht : t ∉ bad n) :
    rhoStar n j t = rhoMem n j t := by
  have h0 : (candidateM.denPoly n).eval t ≠ 0 := by
    have := den_ne n 0 (by omega) t ht
    simpa using this
  exact rho_eq_member n j hj t h0 (dPr_ne n t ht) (den_ne n j hj t ht)

/-! ## 3. THE `hr` SPELLING, EXECUTED -/

/-- **STAR-ID's delivery into row PHI-EVAL.**  Any `Rep` whose value off `bad n` is the (★)
datum `ρ j` is evaluated by `Φ` to the member's coordinates `(q_{n+j}, p_{n+j})`.

This is `Zeta2T1Eval.Phi_rho_off` at `mem := candidateM`, `n := n + j`, `E := bad n`, with the
hypothesis produced by `rhoStar_eq_rhoMem` — the composition RUN, not asserted. -/
theorem star_phi_rho (n j : ℕ) (hj : j ≤ 3) (r : Rep)
    (hrho : ∀ t : ℚ, t ∉ bad n → evalRep r t = rhoStar n j t) :
    (candidateM.sgn (n + j) * candidateM.Pin (n + j) * (Phi (candidateM.b3 * (n + j)) r).1,
      -(candidateM.sgn (n + j) * candidateM.Pin (n + j)) * (Phi (candidateM.b3 * (n + j)) r).2)
      = (candidateM.qn (n + j), candidateM.pn (n + j)) := by
  refine Zeta2T1Eval.Phi_rho_off candidateM candidateM_wf (n + j) r (bad n) ?_
  intro t ht _
  rw [hrho t ht, rhoStar_eq_rhoMem n j hj t ht, rhoMem]

/-- **Expected-GREEN control: `star_phi_rho`'s hypothesis is SATISFIABLE.**  `Zeta2T1Eval.repR`
at `n + j` meets it, so the theorem above is not green because its hypothesis is empty. -/
theorem repR_satisfies (n j : ℕ) (hj : j ≤ 3) :
    ∀ t : ℚ, t ∉ bad n → evalRep (Zeta2T1Eval.repR candidateM (n + j)) t = rhoStar n j t := by
  intro t ht
  rw [rhoStar_eq_rhoMem n j hj t ht, rhoMem]
  exact Zeta2T1Eval.evalRep_repR candidateM candidateM_wf (n + j) t
    fun k hk => ne_of_not_bad ht k (win_sub n j hj hk)

/-! ## 4. (★) in `Zeta2StarB1`'s `StarIdentity` shape -/

noncomputable def aE (n : ℕ) (t : ℚ) : ℚ := (afProd aFacs t).eval (n : ℚ)
noncomputable def bE (n : ℕ) (t : ℚ) : ℚ := (afProd bFacs t).eval (n : ℚ)
noncomputable def cE (n : ℕ) (t : ℚ) : ℚ := (afProd cFacs t).eval (n : ℚ)
noncomputable def xE (n : ℕ) (t : ℚ) : ℚ := (polB2 xCoeffs t).eval (n : ℚ)

/-- The coords' operator list, indexed the way `Zeta2StarId.paF` indexes the `Pa`s. -/
noncomputable def alL : ℕ → List ℚ
  | 0 => al0
  | 1 => al1
  | 2 => al2
  | _ => al3

/-- `Ãⱼ(n)` — the recurrence coefficient of the (★) solve at index `j`. -/
noncomputable def Atil (n j : ℕ) : ℚ := (polB (alL j)).eval (n : ℚ)

noncomputable def PaV (n : ℕ) (j : Fin 4) (t : ℚ) : ℚ := PaE n (j : ℕ) t
noncomputable def AtilV (n : ℕ) (j : Fin 4) : ℚ := Atil n (j : ℕ)
noncomputable def rhoV (n : ℕ) (j : Fin 4) (t : ℚ) : ℚ := rhoMem n (j : ℕ) t

/-- The Gosper antidifference `b(·−1) · x · u / c`, with `c ≡ 1`. -/
noncomputable def SE (n : ℕ) (s : ℚ) : ℚ := bE n (s - 1) * xE n s * uStar n s

/-- cand-t1's `c` is the EMPTY factor list, so `c ≡ 1`.  Stated rather than inlined because
`star_telescopes` divides by it twice. -/
theorem cE_one (n : ℕ) (t : ℚ) : cE n t = 1 := by
  rw [cE, cFacs_nil]
  simp [afProd]

/-- **(★) EXECUTED into B1's interface shape.**  `star_forall t` is `∀ v, (F t).eval v = 0`;
evaluating at `v = n` and unfolding the base's own `F_def` gives exactly `StarIdentity`. -/
theorem star_identity (n : ℕ) :
    Zeta2StarB1.StarIdentity (aE n) (bE n) (cE n) (xE n) (PaV n) (AtilV n) := by
  intro t
  have h := star_forall t (n : ℚ)
  rw [F_def] at h
  simp only [eval_sub, eval_mul, eval_add] at h
  simp only [Fin.sum_univ_four, aE, bE, cE, xE, PaV, AtilV, PaE, Atil, alL, paF,
    Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  show (afProd aFacs t).eval (n : ℚ) * (polB2 xCoeffs (t + 1)).eval (n : ℚ)
      - (afProd bFacs (t - 1)).eval (n : ℚ) * (polB2 xCoeffs t).eval (n : ℚ)
    = (afProd cFacs t).eval (n : ℚ)
      * ((polB al0).eval (n : ℚ) * (afProd pa0Facs t).eval (n : ℚ)
        + (polB al1).eval (n : ℚ) * (afProd pa1Facs t).eval (n : ℚ)
        + (polB al2).eval (n : ℚ) * (afProd pa2Facs t).eval (n : ℚ)
        + (polB al3).eval (n : ℚ) * (afProd pa3Facs t).eval (n : ℚ))
  linarith [h]

/-! ## 5. THE COMPOSITION WITH STAR, EXECUTED -/

/-- **ROW STAR-ID's composition with STAR.**  For every `n` and every `t` at which the rebase is
a statement — `t` and `t + 1` both off `bad n` — the coords' operator applied to the MEMBER's
functions telescopes:

    ∑ⱼ Ãⱼ(n) · (numPoly (n+j) / denPoly (n+j))(t) = S(t+1) − S(t).

Every hypothesis of `Zeta2StarB1.star_telescopes` is discharged from a landed theorem; nothing
is assumed. -/
theorem star_telescopes_member (n : ℕ) (t : ℚ) (ht : t ∉ bad n) (ht1 : t + 1 ∉ bad n) :
    ∑ j : Fin 4, AtilV n j * rhoV n j t = SE n (t + 1) - SE n t := by
  have hd0 : (candidateM.denPoly n).eval t ≠ 0 := by
    have := den_ne n 0 (by omega) t ht; simpa using this
  have hD0 : (afProd pa0Facs t).eval (n : ℚ) ≠ 0 := dPr_ne n t ht
  have hd1 : (candidateM.denPoly n).eval (t + 1) ≠ 0 := by
    have := den_ne n 0 (by omega) (t + 1) ht1; simpa using this
  have hD1 : (afProd pa0Facs (t + 1)).eval (n : ℚ) ≠ 0 := dPr_ne n (t + 1) ht1
  refine Zeta2StarB1.star_telescopes (aE n) (bE n) (cE n) (xE n) (uStar n) (SE n)
    (PaV n) (rhoV n) (AtilV n) t ?_ ?_ ?_ ?_ ?_ (star_identity n t)
  · rw [cE_one]; exact one_ne_zero
  · rw [cE_one]; exact one_ne_zero
  · -- `hu`: the Gosper normal form, cleared.
    rw [cE_one, cE_one, uStar, uStar]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_div_iff (mul_ne_zero hd1 hD1) (mul_ne_zero hd0 hD0)]
    have hs := star_u n t
    rw [aE, bE]
    linear_combination hs
  · -- `hρ`: the rebase, at this `t`.
    intro j
    have hj : (j : ℕ) ≤ 3 := by omega
    rw [rhoV, PaV]
    exact (rhoStar_eq_rhoMem n (j : ℕ) hj t ht).symm
  · -- `hS`: the antidifference, cleared of a denominator that is `1`.
    intro s
    rw [cE_one, SE, mul_one]

/-! ## 6. The exceptional set is neither empty nor everything -/

/-- `bad n` is NONEMPTY, so the exclusion in §3 and §5 is doing work rather than decorating. -/
theorem bad_nonempty (n : ℕ) : (bad n).Nonempty := by
  refine ⟨-((2 * n + 1 : ℕ) : ℚ), Finset.mem_image.2 ⟨2 * n + 1, ?_, rfl⟩⟩
  exact d2_sub n (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)

/-- …and it is a FINITE set of rationals, so §5's conclusion is about cofinitely many `t`.
`0` is not in it: every excluded `t` is a negative integer. -/
theorem zero_not_bad (n : ℕ) : (0 : ℚ) ∉ bad n := by
  intro h
  obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h
  have : ((k : ℚ)) = 0 := by linarith [hke]
  have hk0 : k = 0 := by exact_mod_cast this
  subst hk0
  simp only [badK, Finset.mem_union, Finset.mem_Icc, window_eq] at hk
  omega

/-! ## 7. The row's two halves, on ONE object

LEAN.md §1 and PAIR-2's lesson: a receipt on the parts attests nothing about the assembly, so
the composed statement gets its own name and its own `#print axioms`. -/

/-- **ROW STAR-ID — what this file delivers, as one theorem.** -/
theorem star_id_phi (n : ℕ) :
    (∀ j : ℕ, j ≤ 3 → ∀ r : Rep, (∀ t : ℚ, t ∉ bad n → evalRep r t = rhoStar n j t) →
        (candidateM.sgn (n + j) * candidateM.Pin (n + j) * (Phi (candidateM.b3 * (n + j)) r).1,
          -(candidateM.sgn (n + j) * candidateM.Pin (n + j))
            * (Phi (candidateM.b3 * (n + j)) r).2)
          = (candidateM.qn (n + j), candidateM.pn (n + j)))
      ∧ (∀ t : ℚ, t ∉ bad n → t + 1 ∉ bad n →
          ∑ j : Fin 4, AtilV n j * rhoV n j t = SE n (t + 1) - SE n t) :=
  ⟨fun j hj r hrho => star_phi_rho n j hj r hrho, fun t ht ht1 =>
    star_telescopes_member n t ht ht1⟩

/-! ## 8. Receipts (LEAN.md §1 — exit 0 is not an attestation, and neither is a receipt alone)

Read with `python3 tools/lean_falsifier_restore.py audit-probe <log> <file>` AND read `lean`'s
own rc separately: the predicate scores a parse-broken file GREEN (found_bugs 2026-09-14). -/

#print axioms window_eq
#print axioms ne_of_not_bad
#print axioms d2_sub
#print axioms d4_sub
#print axioms d26_sub
#print axioms win_sub
#print axioms prI_ne_zero
#print axioms den_ne
#print axioms dPr_ne
#print axioms rhoStar_eq_rhoMem
#print axioms star_phi_rho
#print axioms repR_satisfies
#print axioms cE_one
#print axioms star_identity
#print axioms star_telescopes_member
#print axioms bad_nonempty
#print axioms zero_not_bad
#print axioms star_id_phi

end Zeta2StarIdPhi
