/-
# ROW PAIR-6 — the hat recurrences at the hat's own coordinates

`docs/future/zeta2-lean-chain.md` row PAIR-6 (§PAIR-6 design notes, 2026-09-14).

**The row's two theorems**, `∀ n ≥ 2`, over ℚ:

    hatQ_rec : Σ_{j<4} β̂_j(n) · hatQ(n+j) = 0
    hatP_rec : Σ_{j<4} β̂_j(n) · hatP(n+j) = 0,     β̂_j(n) = α̃_j(n) · Π̂(n)/Π̂(n+j)

**THE OPERATOR IS `β̂`, and that is a decision, not an accident.**  PAIR-8's column-2 correction
(2026-09-14) established that running its induction in `β̂` costs ONE nonvanishing (PAIR-N's
`L ≠ 0`) where `c3_ne_zero` costs two, and `β̂` is what this row actually reaches: `repHat`'s
coefficients carry `Π̂` (`Zeta2HatRep`'s header) while `hatMember` is `R̂ₙ/Π̂`, so the rebase
exponent is **−1**, measured.  There is **no `(−1)^j`** anywhere in this file: that sign belongs to
the chain's `cleared_j`, not to the (★) alphas (PAIR-7's column-1 correction (b)).  Both
conventions are falsifier arms in `pair6_check.py` (A1, A2) and both RED, so neither is asserted.

**The composition, and where each step comes from.**  Every input is a landed theorem:

  * PAIR-2 `StarForallCandt2.star_forall`   — (★) at every `n`, as `(F t).eval n = 0`  → `hstar`
  * PAIR-6's own `Zeta2Pair6Runs`           — `hρ`/`hu`, cross-multiplied     → `hu_at`, `hrho_at`
  * B1 `Zeta2StarB1.star_telescopes`        — the abstract telescoping, at one `t`
  * PAIR-4R `Zeta2HatResidues.hat_rep`      — `evalRep (repHat m) t = Π̂(m)·hatMember m t`
  * PAIR-5 `Zeta2HatStarBridge.evalRep_repS_star` — read TWICE, at `t+1` and at `t`, where the
    two `C₀` offsets cancel identically (phase 5I); and `hbdy_hat_star` for the vanishing
  * PAIR-3 `Zeta2HatInj.Phihat_of_evalRep`  — evaluations off a finite set ⟹ the `Φ̂` images
  * PAIR-4C `Zeta2HatBelt.Phihat_member`    — `Φ̂ n (repHat (n+j)) = (hatP(n+j), −hatQ(n+j), 0)`

**The exceptional set is deliberately crude.**  `Phihat_of_evalRep` takes an ARBITRARY `Finset ℚ`
(phase 5I measured this), so the row needs no reduced pole support and `Zeta2HatCancel` acquires
no consumer here: `badE n` is simply every half-integer `−k/2` below a generous bound, and `GoodT`
is the single predicate every factor's nonvanishing is read off.

**What this row does NOT discharge.**  It needs nothing from PAIR-7 and therefore does NOT owe
`λden(n) ≠ 0`: `λ` enters only where PAIR-7's `β̂ⱼ·λden = γⱼ·λnum` is used to cross to the chain's
operator, which is PAIR-8's step.  **PAIR-N (`L ≠ 0`, deg 154) is untouched.**  `hatQ n = qnInt n`
is PAIR-8, and `Zeta2Target.zeta2_not_liouvilleWith` is still `sorry`.

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2Pair6.lean

It imports the GENERATED `StarForallCandt2Base` **and** `StarForallCandt2Assemble`, i.e. all 278
`h0` shards, so the case carries the manifest prerequisite and REFUSES rather than skips.
Receipts: `out_axioms_pair6.txt`.  Falsifier: `falsify_pair6.sh`.  Second implementation, in
exact ℚ and a different language: `pair6_check.py` → `pair6_check.out`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic
import Zeta2StarB1
import Zeta2HatStarBridge
import Zeta2HatInj
import Zeta2HatResidues
import Zeta2Pair6Runs
import StarForallCandt2Assemble

namespace Zeta2Pair6

-- `F_def`'s right-hand side carries `polB2 xCoeffs`, a 121-entry Horner chain, so rewriting with
-- it exceeds the default recursion budget.  The option is FILE-LEVEL on purpose: placed between a
-- docstring and its theorem it is a parse error Lean silently recovers from, and every receipt
-- still prints clean (zeta2-lean-chain.md, PAIR-7's landing).
set_option maxRecDepth 100000

open Polynomial Finset StarForallCandt2 Zeta2Pair6Runs
open Zeta2HatRep (evalRep Phihat repHat hatMember)

/-! ## 1. The exceptional set, and what avoiding it buys -/

/-- `t` avoids every root of every affine factor this row multiplies by.  One predicate, because
every such factor is `2t + k` or `t + k` with `k` a natural number below the bound. -/
def GoodT (n : ℕ) (t : ℚ) : Prop := ∀ k : ℕ, k ≤ 60 * n + 400 → 2 * t + (k : ℚ) ≠ 0

/-- The finite set `Phihat_of_evalRep`'s `E` is instantiated at. -/
noncomputable def badE (n : ℕ) : Finset ℚ :=
  (Finset.range (60 * n + 401)).image (fun k : ℕ => -(k : ℚ) / 2)

theorem good_of_not_mem (n : ℕ) (t : ℚ) (h : t ∉ badE n) : GoodT n t := by
  intro k hk hz
  refine h ?_
  simp only [badE, Finset.mem_image, Finset.mem_range]
  exact ⟨k, by omega, by linarith⟩

theorem good_t (n : ℕ) (t : ℚ) (hg : GoodT n t) (l : ℕ) (hl : 2 * l ≤ 60 * n + 400) :
    t + (l : ℚ) ≠ 0 := by
  intro h
  refine hg (2 * l) hl ?_
  push_cast
  linarith

theorem prI_t_ne (n : ℕ) (t : ℚ) (hg : GoodT n t) (a b : ℕ) (hb : 2 * b ≤ 60 * n + 400) :
    prI t a b ≠ 0 := by
  rw [prI]
  refine Finset.prod_ne_zero_iff.2 ?_
  intro l hl
  rw [Finset.mem_Icc] at hl
  exact good_t n t hg l (by omega)

theorem prI_2t_ne (n : ℕ) (t : ℚ) (hg : GoodT n t) (a b : ℕ) (hb : b ≤ 60 * n + 400) :
    prI (2 * t) a b ≠ 0 := by
  rw [prI]
  refine Finset.prod_ne_zero_iff.2 ?_
  intro l hl
  rw [Finset.mem_Icc] at hl
  exact hg l (by omega)

theorem hmDen_ne (n m : ℕ) (hm : m ≤ n + 3) (t : ℚ) (hg : GoodT n t) : hmDen m t ≠ 0 := by
  rw [hmDen]
  exact mul_ne_zero (prI_t_ne n t hg _ _ (by omega)) (prI_t_ne n t hg _ _ (by omega))

theorem dPr_ne (n : ℕ) (t : ℚ) (hg : GoodT n t) : dPr n t ≠ 0 := by
  rw [dPr]
  exact mul_ne_zero (mul_ne_zero (prI_t_ne n t hg _ _ (by omega))
    (prI_t_ne n t hg _ _ (by omega))) (prI_2t_ne n t hg _ _ (by omega))

/-- Shifting the argument by one only moves the run bounds, so `GoodT n t` covers `t + 1` too. -/
theorem prI_shift1 (t : ℚ) (a b : ℕ) : prI (t + 1) a b = prI t (a + 1) (b + 1) := by
  rw [show t + 1 = t + ((1 : ℕ) : ℚ) from by push_cast; ring, prI_shift]

theorem prI_shift2 (t : ℚ) (a b : ℕ) : prI (2 * (t + 1)) a b = prI (2 * t) (a + 2) (b + 2) := by
  rw [show 2 * (t + 1) = 2 * t + ((2 : ℕ) : ℚ) from by push_cast; ring, prI_shift]

theorem hmDen_shift_ne (n m : ℕ) (hm : m ≤ n + 3) (t : ℚ) (hg : GoodT n t) :
    hmDen m (t + 1) ≠ 0 := by
  rw [hmDen, prI_shift1, prI_shift1]
  exact mul_ne_zero (prI_t_ne n t hg _ _ (by omega)) (prI_t_ne n t hg _ _ (by omega))

theorem dPr_shift_ne (n : ℕ) (t : ℚ) (hg : GoodT n t) : dPr n (t + 1) ≠ 0 := by
  rw [dPr, prI_shift1, prI_shift1, prI_shift2]
  exact mul_ne_zero (mul_ne_zero (prI_t_ne n t hg _ _ (by omega))
    (prI_t_ne n t hg _ _ (by omega))) (prI_2t_ne n t hg _ _ (by omega))

theorem dBlock_eval (n : ℕ) (t : ℚ) :
    (Zeta2HatShatForm.dBlock n).eval t = prI (2 * t) (3 * n + 2) (3 * n + 10) := by
  simp only [Zeta2HatShatForm.dBlock, prI, eval_prod, eval_add, eval_mul, eval_X, eval_C]

theorem hatPi_ne (m : ℕ) : Zeta2Hat.hatPi m ≠ 0 := by
  rw [Zeta2Hat.hatPi]
  refine div_ne_zero ?_ ?_ <;>
    simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero, not_or] <;>
    exact ⟨Nat.factorial_ne_zero _, Nat.factorial_ne_zero _⟩

/-! ## 2. The (★) instance, in `star_telescopes`' own vocabulary -/

noncomputable def aFn (n : ℕ) (t : ℚ) : ℚ := (afProd aFacs t).eval (n : ℚ)
noncomputable def bFn (n : ℕ) (t : ℚ) : ℚ := (afProd bFacs t).eval (n : ℚ)
noncomputable def xFn (n : ℕ) (t : ℚ) : ℚ := (polB2 xCoeffs t).eval (n : ℚ)
noncomputable def uFn (n : ℕ) (t : ℚ) : ℚ := hatMember n t / dPr n t
noncomputable def sFn (n : ℕ) (t : ℚ) : ℚ := bFn n (t - 1) * xFn n t * uFn n t

/-- The four cleared recurrence coefficients, ℕ-indexed. -/
noncomputable def alN (n j : ℕ) : ℚ :=
  (polB (match j with | 0 => al0 | 1 => al1 | 2 => al2 | _ => al3)).eval (n : ℚ)

/-- The four rebased numerators, ℕ-indexed. -/
noncomputable def paN (n j : ℕ) (t : ℚ) : ℚ :=
  (afProd (match j with | 0 => pa0Facs | 1 => pa1Facs | 2 => pa2Facs | _ => pa3Facs) t).eval (n : ℚ)

theorem paN_prI (n j : ℕ) (hj : j ≤ 3) (t : ℚ) : paN n j t = paPr j n t := by
  interval_cases j
  · exact pa0_prI n t
  · exact pa1_prI n t
  · exact pa2_prI n t
  · exact pa3_prI n t

/-- **(★) at the candidate, at a fixed `n`, in the abstract theorem's own shape.**  The only
input is PAIR-2's `star_forall`; `c ≡ 1` because the landed FACSYM's `c` is the empty multiset. -/
theorem hstar (n : ℕ) :
    Zeta2StarB1.StarIdentity (aFn n) (bFn n) (fun _ => (1 : ℚ)) (xFn n)
      (fun j : Fin 4 => fun t => paN n (j : ℕ) t) (fun j : Fin 4 => alN n (j : ℕ)) := by
  intro t
  have h := StarForallCandt2.star_forall t (n : ℚ)
  rw [F_def] at h
  -- `cFacs` is the EMPTY multiset (measured: the landed FACSYM's `c`), so `afProd cFacs t` is the
  -- literal `1` and the (★) residual's third term loses its prefactor here rather than in `ring`.
  simp only [eval_sub, eval_mul, eval_add, cFacs, afProd, one_mul] at h
  simp only [aFn, bFn, xFn, alN, paN, Fin.sum_univ_four, one_mul]
  linear_combination h

/-! ## 3. `hu` and `hρ` — the identification half, divided through -/

theorem hu_at (n : ℕ) (t : ℚ) (hg : GoodT n t) :
    uFn n (t + 1) * (bFn n t * 1) = uFn n t * (aFn n t * 1) := by
  have hd1 := hmDen_ne n n (by omega) t hg
  have hd2 := hmDen_shift_ne n n (by omega) t hg
  have hD1 := dPr_ne n t hg
  have hD2 := dPr_shift_ne n t hg
  rw [uFn, uFn, bFn, aFn, aPr_eq, bPr_eq, hatMember_eq, hatMember_eq]
  field_simp
  linear_combination hu_cross n t

theorem hrho_at (n j : ℕ) (hj : j ≤ 3) (t : ℚ) (hg : GoodT n t) :
    hatMember (n + j) t = uFn n t * paN n j t := by
  have hd1 := hmDen_ne n n (by omega) t hg
  have hd2 := hmDen_ne n (n + j) (by omega) t hg
  have hD1 := dPr_ne n t hg
  rw [uFn, hatMember_eq, hatMember_eq, paN_prI n j hj]
  field_simp
  linear_combination rho_cross n j hj t

/-! ## 4. The pointwise relation `Phihat_of_evalRep` consumes -/

/-- The operator PAIR-6 reaches, and the one PAIR-8's induction runs in: the CLEARED `α̃ⱼ`
rebased by the hat's own `Π̂`.  Written with `Zeta2Hat.hatPi` and the base module's own `alⱼ`,
so `Zeta2Pair7Pi`'s `polB_eval`/`qeval` bridge identifies it with PAIR-7's `betaHat`. -/
noncomputable def betaHat (n j : ℕ) : ℚ :=
  alN n j * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + j))

theorem evalRep_sum_eq (n : ℕ) (hn : 2 ≤ n) (t : ℚ) (hg : GoodT n t) :
    ∑ j ∈ Finset.range 4, betaHat n j * evalRep (repHat (n + j)) t
      = evalRep (Zeta2Hat.hatPi n •
          Zeta2HatShift.repDelta (Zeta2HatRepS.repS n (Zeta2HatStarBridge.bHat n)
            (Zeta2HatStarBridge.xHat n))) t := by
  have hidx : ∀ k ∈ Zeta2HatRawPoles.idxS1 n ∪ Zeta2HatRawPoles.idxS2 n,
      t + ((k : ℕ) : ℚ) ≠ 0 := by
    intro k hk
    simp only [Zeta2HatRawPoles.idxS1, Zeta2HatRawPoles.idxS2, Finset.mem_union,
      Finset.mem_Icc] at hk
    exact good_t n t hg k (by omega)
  have hidx1 : ∀ k ∈ Zeta2HatRawPoles.idxS1 n ∪ Zeta2HatRawPoles.idxS2 n,
      (t + 1) + ((k : ℕ) : ℚ) ≠ 0 := by
    intro k hk
    simp only [Zeta2HatRawPoles.idxS1, Zeta2HatRawPoles.idxS2, Finset.mem_union,
      Finset.mem_Icc] at hk
    have hne := good_t n t hg (k + 1) (by omega)
    intro hz
    exact hne (by push_cast at hz ⊢; linarith)
  have hblk : (Zeta2HatShatForm.dBlock n).eval t ≠ 0 := by
    rw [dBlock_eval]; exact prI_2t_ne n t hg _ _ (by omega)
  have hblk1 : (Zeta2HatShatForm.dBlock n).eval (t + 1) ≠ 0 := by
    rw [dBlock_eval, prI_shift2]; exact prI_2t_ne n t hg _ _ (by omega)
  -- the (★) telescoping, at this `t`
  have htelF : ∑ j : Fin 4, alN n (j : ℕ) * hatMember (n + (j : ℕ)) t
      = sFn n (t + 1) - sFn n t :=
    Zeta2StarB1.star_telescopes (aFn n) (bFn n) (fun _ => (1 : ℚ)) (xFn n) (uFn n) (sFn n)
      (fun j : Fin 4 => fun t => paN n (j : ℕ) t)
      (fun j : Fin 4 => fun t => hatMember (n + (j : ℕ)) t)
      (fun j : Fin 4 => alN n (j : ℕ)) t one_ne_zero one_ne_zero (hu_at n t hg)
      (fun j => hrho_at n (j : ℕ) (by omega) t hg) (fun s => by rw [sFn]; ring) (hstar n t)
  have htel : ∑ j ∈ Finset.range 4, alN n j * hatMember (n + j) t = sFn n (t + 1) - sFn n t := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => alN n i * hatMember (n + i) t) 4]
    exact htelF
  -- the left side, through PAIR-4R
  have hL : ∑ j ∈ Finset.range 4, betaHat n j * evalRep (repHat (n + j)) t
      = Zeta2Hat.hatPi n * ∑ j ∈ Finset.range 4, alN n j * hatMember (n + j) t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_range] at hj
    have hrep : evalRep (repHat (n + j)) t
        = Zeta2Hat.hatPi (n + j) * hatMember (n + j) t := by
      refine Zeta2HatResidues.hat_rep (n + j) t ?_
      intro k hk
      rw [Finset.mem_Icc] at hk
      exact good_t n t hg k (by omega)
    have hpi := hatPi_ne (n + j)
    rw [hrep, betaHat]
    field_simp
  -- the right side, through PAIR-5
  have hR : evalRep (Zeta2Hat.hatPi n •
        Zeta2HatShift.repDelta (Zeta2HatRepS.repS n (Zeta2HatStarBridge.bHat n)
          (Zeta2HatStarBridge.xHat n))) t
      = Zeta2Hat.hatPi n * (sFn n (t + 1) - sFn n t) := by
    have hD1 := dPr_ne n t hg
    have hD2 := dPr_shift_ne n t hg
    rw [Zeta2HatLinear.evalRep_smul, Zeta2HatShift.evalRep_repDelta,
      Zeta2HatStarBridge.evalRep_repS_star n (by omega) (t + 1) hidx1 hblk1,
      Zeta2HatStarBridge.evalRep_repS_star n (by omega) t hidx hblk,
      dPr_eq n t, dPr_eq n (t + 1)]
    simp only [sFn, bFn, xFn, uFn]
    field_simp
    ring
  rw [hL, hR, htel]

/-! ## 5. THE ROW -/

theorem pair6_Phihat (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range 4, betaHat n j • Phihat n (repHat (n + j)) = 0 := by
  have h := Zeta2HatInj.Phihat_of_evalRep (ι := ℕ) n (Finset.range 4)
    (betaHat n) (fun j => repHat (n + j))
    (Zeta2Hat.hatPi n • Zeta2HatShift.repDelta (Zeta2HatRepS.repS n
      (Zeta2HatStarBridge.bHat n) (Zeta2HatStarBridge.xHat n))) (badE n)
    (fun t ht => evalRep_sum_eq n hn t (good_of_not_mem n t ht))
  rw [h, Zeta2HatLinear.Phihat_smul, Zeta2HatStarBridge.hbdy_hat_star n hn, smul_zero]

/-- **ROW PAIR-6, the ζ(2) coordinate.** -/
theorem hatQ_rec (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range 4, betaHat n j * (Zeta2Hat.hatQ (n + j) : ℚ) = 0 := by
  have h := pair6_Phihat n hn
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [Zeta2HatBelt.Phihat_member n j (by rw [Finset.mem_range] at hj; omega) hn] :
      ∀ j ∈ Finset.range 4, betaHat n j • Phihat n (repHat (n + j))
        = betaHat n j • ((Zeta2Hat.hatP (n + j), -(Zeta2Hat.hatQ (n + j) : ℚ), (0 : ℚ)) :
            ℚ × ℚ × ℚ))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Prod.smul_mk, smul_eq_mul,
    Prod.mk_add_mk, zero_add, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linear_combination -h.2.1

/-- **ROW PAIR-6, the rational coordinate.** -/
theorem hatP_rec (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range 4, betaHat n j * Zeta2Hat.hatP (n + j) = 0 := by
  have h := pair6_Phihat n hn
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [Zeta2HatBelt.Phihat_member n j (by rw [Finset.mem_range] at hj; omega) hn] :
      ∀ j ∈ Finset.range 4, betaHat n j • Phihat n (repHat (n + j))
        = betaHat n j • ((Zeta2Hat.hatP (n + j), -(Zeta2Hat.hatQ (n + j) : ℚ), (0 : ℚ)) :
            ℚ × ℚ × ℚ))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Prod.smul_mk, smul_eq_mul,
    Prod.mk_add_mk, zero_add, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linear_combination h.1

end Zeta2Pair6

#print axioms Zeta2Pair6.hstar
#print axioms Zeta2Pair6.hu_at
#print axioms Zeta2Pair6.hrho_at
#print axioms Zeta2Pair6.evalRep_sum_eq
#print axioms Zeta2Pair6.pair6_Phihat
#print axioms Zeta2Pair6.hatQ_rec
#print axioms Zeta2Pair6.hatP_rec
