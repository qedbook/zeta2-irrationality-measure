/-
# Row PAIR-5 — the CONNECTION: `numS/denS` really is `Ŝ`, and `D` really is the FACSYM's `D`

`docs/future/zeta2-lean-chain.md` row PAIR-5, §PAIR-5 design notes attempt 5.

**What the row owed that this file pays.**  `Zeta2HatRawPoles` proves things about two polynomials
`numS` and `denS`, and `Zeta2HatRepS` proves the row's theorem about the `Rep̂` built from them.
Neither is the row unless that quotient is the (★) antidifference

    Ŝ = b̂(t−1) · x̂ · hatMember n / D_n ,      D_n = dRuns n * dBlock n ,   ĉ = 1

which is what `shat_eq` states and proves, off the finitely many roots of `D`'s lead-2 block.  The
route takes exactly ONE cancellation and this is where it happens: `hatNum_split` splits the
member's `(2t+l)` run at `3n+11`, and the bottom piece IS `dBlock`.  `1 ≤ n` is what makes the
split legal (`3n+10 ≤ 20n+1`), and it fails at `n = 0` — which is also where attempt 3 measured `Ŝ`
itself to be different (order-3 poles at half-integers, the member empty).

**Why the block has to go and cannot simply be kept.**  `dBlock`'s roots are HALF-INTEGERS and
`Rep̂`'s keys are ℕ, so a `Rep̂` cannot hold that pole at all.  This is the one place where the
route's genuine hazard lives, and it is not absorbed silently:
`../zeta2_star_b1/hat_raw_route_probe.py --falsify`'s `num2-lo-off`
arm constructs exactly the uncancelled case and reds the representation checks while leaving every
integer-pole SUPPORT check green — a measured insensitivity worth carrying, since it says a support
check cannot see this class of error and only `evalRep` can.

**What this file does NOT do, and it is the row's one soundness-bearing residual.**  `dBlock` and
`dRuns` are a TRANSCRIPTION of the landed FACSYM (`external_tests/zeta2_star_b1/coords/
starcoords_cand-t2.txt`: `D` = 9 factors `2t + 3n + b`, `b ∈ [2,10]`; 54 factors `t + 18n + b`,
`b ∈ [2,55]`; 60 factors `t + 20n + b`, `b ∈ [2,61]`; `c` empty).  A theorem can be true about a
mis-transcribed object, and nothing in Lean can tell.  The generated cross-check is
`external_tests/zeta2_star_b1/facsym_d_check.py` → `facsym_d_check.out`, which reads the engine's
own coordinate file and asserts these three runs factor for factor with six falsifier arms; it runs
in `regen_all.sh`.  **Read a green here as attesting the algebra and that script as attesting the
constants — neither attests both.**

It also does not name the row's actual `b̂` and `x̂`.  The two degree facts below are stated for an
ARBITRARY coefficient family precisely so that `x̂`'s 121 `n`-dependent coefficients never have to
be reasoned about, only counted; instantiating at the real pair is PAIR-1's emission and the row's
remaining phase (5H), not a proof obligation.

**Elaborate with the corpus oleans on the path** — it imports `Zeta2HatRawPoles`:

    sh external_tests/zeta2_arith/run_probe.sh Zeta2HatShatForm.lean

Without `LEAN_PATH` pointing at the probes directory the import fails, the run TRUNCATES, and NO
`#print axioms` line is printed at all — which is not a green.

**Receipts** `out_axioms_hatshatform.txt`; falsifier arms `C1`–`C2` in `falsify_hatreps.sh` →
`out_hatreps_falsify.txt` (the lead-2 block one factor long; `D`'s `20n` run one factor short).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic
import Zeta2HatRawPoles

namespace Zeta2HatShatForm

open Polynomial Finset Zeta2HatRawPoles

/-- `D`'s lead-2 block, `(2t + 3n + b)` for `b ∈ [2,10]` — read off the landed FACSYM, where it is
the ONLY `lead = 2` entry of `D`.  Its roots are half-integers, which is why it cannot stay in a
denominator a `Rep̂` has to hold. -/
noncomputable def dBlock (n : ℕ) : ℚ[X] :=
  ∏ l ∈ Icc (3 * n + 2) (3 * n + 10), (C (2 : ℚ) * X + C (l : ℚ))

/-- `D`'s two INTEGER runs. -/
noncomputable def dRuns (n : ℕ) : ℚ[X] :=
  (∏ l ∈ Icc (18 * n + 2) (18 * n + 55), (X + C (l : ℚ)))
    * ∏ l ∈ Icc (20 * n + 2) (20 * n + 61), (X + C (l : ℚ))

/-- `denS` IS the member's written denominator times `D`'s integer runs — definitional bookkeeping,
stated so that nothing downstream has to unfold `denS`. -/
theorem denS_eq_hatDen_mul (n : ℕ) : denS n = Zeta2HatPoles.hatDen n * dRuns n := by
  rw [denS, dRuns, Zeta2HatPoles.hatDen]

/-- **The one cancellation**: the member's `(2t+l)` run splits at `3n+11`, and the bottom piece IS
`D`'s lead-2 block.  `1 ≤ n` is what makes the split legal (`3n+10 ≤ 20n+1`). -/
theorem hatNum_split (n : ℕ) (hn : 1 ≤ n) :
    Zeta2HatPoles.hatNum n
      = dBlock n * ((∏ l ∈ Icc (3 * n + 11) (20 * n + 1), (C (2 : ℚ) * X + C (l : ℚ)))
        * ∏ l ∈ Icc 1 (5 * n), (X + C (l : ℚ))) := by
  classical
  have hsplit : Icc (3 * n + 2) (20 * n + 1)
      = Icc (3 * n + 2) (3 * n + 10) ∪ Icc (3 * n + 11) (20 * n + 1) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Icc (3 * n + 2) (3 * n + 10)) (Icc (3 * n + 11) (20 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  rw [Zeta2HatPoles.hatNum, hsplit, Finset.prod_union hdisj, dBlock, mul_assoc]

/-- **`numS` times the block is the raw numerator.** -/
theorem numS_mul_dBlock (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X]) :
    numS n bh xh * dBlock n = bh * xh * Zeta2HatPoles.hatNum n := by
  rw [numS, hatNum_split n hn]
  ring

/-- **`denS` times the block is the raw denominator.** -/
theorem denS_mul_dBlock (n : ℕ) :
    denS n * dBlock n = Zeta2HatPoles.hatDen n * (dRuns n * dBlock n) := by
  rw [denS_eq_hatDen_mul]
  ring

/-- **`Ŝ = numS/denS` off the block's roots.**  `Ŝ` is written here exactly as the probe's
`shat_parts` writes it: `b̂(t−1) · x̂ · hatMember n / D_n`, with `D_n = dRuns · dBlock` (`c = 1`,
measured — the landed FACSYM's `c` is the empty multiset). -/
theorem shat_eq (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X]) (t : ℚ)
    (hblk : (dBlock n).eval t ≠ 0) (hden : (denS n).eval t ≠ 0) :
    bh.eval t * xh.eval t * Zeta2HatRep.hatMember n t / (dRuns n * dBlock n).eval t
      = (numS n bh xh).eval t / (denS n).eval t := by
  have hd : (denS n).eval t = (Zeta2HatPoles.hatDen n).eval t * (dRuns n).eval t := by
    rw [denS_eq_hatDen_mul, eval_mul]
  have hHD : (Zeta2HatPoles.hatDen n).eval t ≠ 0 := fun h => hden (by rw [hd, h, zero_mul])
  have hDR : (dRuns n).eval t ≠ 0 := fun h => hden (by rw [hd, h, mul_zero])
  have hnum : (numS n bh xh).eval t * (dBlock n).eval t
      = bh.eval t * xh.eval t * (Zeta2HatPoles.hatNum n).eval t := by
    simpa only [eval_mul] using congrArg (fun p : ℚ[X] => p.eval t) (numS_mul_dBlock n hn bh xh)
  have step : bh.eval t * xh.eval t * Zeta2HatRep.hatMember n t / (dRuns n * dBlock n).eval t
      = ((numS n bh xh).eval t * (dBlock n).eval t)
        / ((Zeta2HatPoles.hatDen n).eval t * (dRuns n).eval t * (dBlock n).eval t) := by
    rw [Zeta2HatPoles.hatMember_eq_div, eval_mul, hnum]
    field_simp
  rw [step, hd]
  field_simp

/-! ## The two degree facts a caller supplies, for an ARBITRARY coefficient family

`x̂`'s 121 coefficients are rational functions of `n` and the design never reads one.  What it needs
is that there are 121 of them — so the degree bounds `Zeta2HatRepS` consumes are discharged for
ANY such family, and the row's own instance costs an instantiation rather than a proof. -/

theorem natDegree_coeffs_le (c : ℕ → ℚ) (m : ℕ) :
    (∑ k ∈ range (m + 1), C (c k) * X ^ k).natDegree ≤ m := by
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine le_trans (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)

/-- `b̂(t−1)` is `b̂.comp (X − 1)`, and shifting the argument never raises the degree. -/
theorem natDegree_comp_shift_le (p : ℚ[X]) (a : ℚ) (h : p.natDegree ≤ 5) :
    (p.comp (X - C a)).natDegree ≤ 5 := by
  refine le_trans (natDegree_comp_le) ?_
  rw [natDegree_X_sub_C, mul_one]
  exact h

end Zeta2HatShatForm

#print axioms Zeta2HatShatForm.denS_eq_hatDen_mul
#print axioms Zeta2HatShatForm.hatNum_split
#print axioms Zeta2HatShatForm.numS_mul_dBlock
#print axioms Zeta2HatShatForm.denS_mul_dBlock
#print axioms Zeta2HatShatForm.shat_eq
#print axioms Zeta2HatShatForm.natDegree_coeffs_le
#print axioms Zeta2HatShatForm.natDegree_comp_shift_le
