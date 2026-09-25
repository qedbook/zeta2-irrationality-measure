/-
# `Zeta2PpolVal.lean` — row PNCLR's next probe, reduced to ONE integer divisibility

**HEADLINE: `Δ·Π·Ppol(t) ∈ ℤ` is NOT proved here.**  What is proved is the reduction the
measurement asked for (`pn_halves_probe.out` arm E: `Π·Ppol` is not integer-valued at integers,
but `Δ 16 15 n` cleared every failing value at every sampled `t`), plus both of its integer
ingredients:

  * **`Pin_mul_numPoly_int`** — `Π(n)·numPoly_n(t) ∈ ℤ` at EVERY integer `t`.  `numPoly` is three
    blocks of consecutive integers, of lengths `13n`, `9n`, `5n`, and `Π(n) =
    (11n)!/((13n)!(9n)!(5n)!)`, so this is three applications of Mathlib's
    `Nat.factorial_coe_dvd_prod` — "`k!` divides the product of any `k` consecutive integers",
    which is in current Mathlib and which this row had priced as work.
  * **`denInt_mul_Pin_Ppol_int`** — `den(t)·(Π·Ppol(t)) ∈ ℤ` at every integer `t`, where
    `den(t) = ∏_{k ∈ window}(t+k)`.  This is RESID's partial fractions (`candidate_partial_
    fractions`) plus `Ppol_spec`, multiplied by `Π` and evaluated: the residue side is integral
    because `Π·c_k = ±cTerm n k` (row 3's landed `Pin_mul_ckAbs_eq_cTerm`).  **No division and no
    side condition** — it holds at the poles too, where both sides are `0 = 0`.
  * **`cleared_of_denInt_dvd`** — the remaining obligation, stated on INTEGERS alone: if
    `den(t) ∣ Δ 16 15 n · z` for the witness `z` above, then `Δ·Π·Ppol(t) ∈ ℤ`.

So the row's next probe is now exactly: **`∏_{k ∈ window}(t+k)` divides `Δ 16 15 n · N_n(t)`**,
with `N_n(t) = Π·numPoly(t) − Σ_k (Π·c_k)·∏_{j ≠ k}(t+j)` the integer this file constructs.
Measured true at every sampled `t` for `n ≤ 3` (`ppol_value_probe.out`), and measured LOOSE:
the lcm of the denominators over the whole sampled range is `2²·13`, `2³·5²·23`, `3·13·37` at
`n = 1, 2, 3`, so `D(15n)` alone clears the sample — `Δ` is not the sharp constant here.

**Two things this file does NOT do.**  (1) It does not prove the divisibility — that is the open
statement, and `PpolValueCleared` names it.  (2) The reduction is vacuous at the `11n+1` POLE
integers `t = −k`, `k ∈ window`, where `den(t) = 0`: there `denInt_mul_Pin_Ppol_int` says `0 = 0`
and `cleared_of_denInt_dvd`'s `hne` fails.  Those values need the separate argument that a
polynomial integral at enough non-pole integers is integral everywhere (Newton's forward-
difference basis — NOT built here, and not in the corpus).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2Resid

namespace Zeta2PpolVal

open Zeta2Defs Zeta2Arith Zeta2Resid Finset Polynomial

/-! ## 1. A block of consecutive integers, and its factorial -/

/-- `block c len` at an integer argument IS the product of `len` consecutive integers. -/
theorem block_eval_int (c len : ℕ) (t : ℤ) :
    (block c len).eval ((t : ℚ)) = ((∏ i ∈ range len, (t + (c : ℤ) + (i : ℤ)) : ℤ) : ℚ) := by
  rw [block, eval_prod, Int.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [eval_add, eval_X, eval_C]
  push_cast
  ring

/-- **`len ! ∣` a block's integer value** — Mathlib's `Nat.factorial_coe_dvd_prod`, "`k!` divides
the product of any `k` consecutive integers".  Censused 2026-09-16: it exists
(`Mathlib/Data/Nat/Factorial/BigOperators.lean`) and this row had priced it as work. -/
theorem factorial_dvd_block_int (c len : ℕ) (t : ℤ) :
    ((Nat.factorial len : ℕ) : ℤ) ∣ ∏ i ∈ range len, (t + (c : ℤ) + (i : ℤ)) := by
  have h := Nat.factorial_coe_dvd_prod len (t + (c : ℤ))
  simpa [add_assoc] using h

/-- The block's value as `len !` times an integer, in ℚ. -/
theorem block_eval_factorial_mul (c len : ℕ) (t : ℤ) :
    ∃ z : ℤ, (block c len).eval ((t : ℚ)) = ((Nat.factorial len : ℕ) : ℚ) * (z : ℚ) := by
  obtain ⟨z, hz⟩ := factorial_dvd_block_int c len t
  exact ⟨z, by rw [block_eval_int, hz]; push_cast; ring⟩

/-! ## 2. The numerator half: `Π · numPoly(t) ∈ ℤ` -/

/-- The candidate's `numPoly`, its three block lengths written out. -/
theorem candidate_numPoly (n : ℕ) :
    candidateM.numPoly n
      = block 1 (13 * n) * block (2 * n + 1) (9 * n) * block (4 * n + 1) (5 * n) := rfl

/-- **`Π(n)·numPoly_n(t) ∈ ℤ` at every integer `t`.**  The three blocks contribute `(13n)!`,
`(9n)!` and `(5n)!`, which are exactly `Π`'s denominator; `(11n)!` is left over as an integer
factor. -/
theorem Pin_mul_numPoly_int (n : ℕ) (t : ℤ) :
    ∃ z : ℤ, candidateM.Pin n * (candidateM.numPoly n).eval ((t : ℚ)) = (z : ℚ) := by
  obtain ⟨zA, hA⟩ := block_eval_factorial_mul 1 (13 * n) t
  obtain ⟨zB, hB⟩ := block_eval_factorial_mul (2 * n + 1) (9 * n) t
  obtain ⟨zC, hC⟩ := block_eval_factorial_mul (4 * n + 1) (5 * n) t
  refine ⟨(Nat.factorial (11 * n) : ℤ) * zA * zB * zC, ?_⟩
  have h13 : ((Nat.factorial (13 * n) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have h9 : ((Nat.factorial (9 * n) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have h5 : ((Nat.factorial (5 * n) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  rw [candidate_Pin, candidate_numPoly, eval_mul, eval_mul, hA, hB, hC]
  push_cast
  field_simp

/-! ## 3. The residues, as integers -/

/-- `Π·c_k` as an explicit integer: the landed `cTerm` with the alternating sign. -/
def ckInt (n k : ℕ) : ℤ := (-1) ^ (12 * n + k - 1) * (cTerm n k : ℤ)

theorem ckInt_cast (n k : ℕ) (hk : k ∈ candidateM.window n) :
    ((ckInt n k : ℤ) : ℚ) = candidateM.Pin n * candidateM.ck n k := by
  have h := Pin_mul_ckAbs_eq_cTerm n k hk
  rw [candidate_ck, ckInt]
  push_cast
  rw [← h]
  ring

/-! ## 4. The reduction -/

/-- `denPoly` at an integer argument, as an integer: the window product. -/
def denInt (n : ℕ) (t : ℤ) : ℤ := ∏ k ∈ candidateM.window n, (t + (k : ℤ))

theorem denInt_cast (n : ℕ) (t : ℤ) :
    ((denInt n t : ℤ) : ℚ) = (candidateM.denPoly n).eval ((t : ℚ)) := by
  rw [denPoly_eq_prod_window candidateM candidateM_wf n, eval_prod, denInt]
  push_cast
  exact Finset.prod_congr rfl fun k _ => by simp

/-- **The reduction, with its witness written out.**  `den(t)·(Π·Ppol(t))` is the integer
`Π·numPoly(t) − Σ_k (Π·c_k)·∏_{j≠k}(t+j)`.  No division, no side condition: at a pole both sides
are `0`. -/
theorem denInt_mul_Pin_Ppol_int (n : ℕ) (t : ℤ) :
    ∃ z : ℤ, ((denInt n t : ℤ) : ℚ)
      * (candidateM.Pin n * (candidateM.Ppol n).eval ((t : ℚ))) = (z : ℚ) := by
  obtain ⟨zn, hzn⟩ := Pin_mul_numPoly_int n t
  refine ⟨zn - ∑ k ∈ candidateM.window n,
      ckInt n k * ∏ j ∈ (candidateM.window n).erase k, (t + (j : ℤ)), ?_⟩
  have hspec := congrArg (fun p : ℚ[X] => p.eval ((t : ℚ))) (candidateM.Ppol_spec n)
  rw [candidate_partial_fractions n] at hspec
  simp only [eval_add, eval_mul, eval_finsetSum, eval_prod, eval_C, eval_X] at hspec
  -- `hspec : Σ_k ck · ∏_{j≠k}(t+j) + denPoly(t)·Ppol(t) = numPoly(t)`
  have hmul := congrArg (fun q : ℚ => candidateM.Pin n * q) hspec
  simp only [mul_add, Finset.mul_sum] at hmul
  rw [hzn] at hmul
  have hres : ∀ k ∈ candidateM.window n,
      candidateM.Pin n * (candidateM.ck n k * ∏ j ∈ (candidateM.window n).erase k,
          ((t : ℚ) + (j : ℚ)))
        = ((ckInt n k * ∏ j ∈ (candidateM.window n).erase k, (t + (j : ℤ)) : ℤ) : ℚ) := by
    intro k hk
    push_cast
    rw [ckInt_cast n k hk]
    ring
  rw [Finset.sum_congr rfl hres] at hmul
  rw [denInt_cast]
  push_cast at hmul ⊢
  linear_combination hmul

/-! ## 5. What remains, stated on integers alone -/

/-- **The row's next probe.**  `Δ 16 15 n · Π(n) · Ppol_n(t) ∈ ℤ` for every `n` and every integer
`t` — measured true for `n ≤ 5` and NOT proved. -/
def PpolValueCleared : Prop :=
  ∀ (n : ℕ) (t : ℤ), ∃ w : ℤ,
    ((Δ 16 15 n : ℕ) : ℚ) * (candidateM.Pin n * (candidateM.Ppol n).eval ((t : ℚ))) = (w : ℚ)

/-- **The reduction to ONE integer divisibility.**  Off the poles, the probe follows from
`den(t) ∣ Δ · z` with `z` the integer of `denInt_mul_Pin_Ppol_int` — a statement with no
rationals, no polynomials and no `Π` in it. -/
theorem cleared_of_denInt_dvd (n : ℕ) (t : ℤ) (z : ℤ)
    (hz : ((denInt n t : ℤ) : ℚ)
      * (candidateM.Pin n * (candidateM.Ppol n).eval ((t : ℚ))) = (z : ℚ))
    (hne : denInt n t ≠ 0) (hd : denInt n t ∣ (Δ 16 15 n : ℤ) * z) :
    ∃ w : ℤ, ((Δ 16 15 n : ℕ) : ℚ)
      * (candidateM.Pin n * (candidateM.Ppol n).eval ((t : ℚ))) = (w : ℚ) := by
  obtain ⟨w, hw⟩ := hd
  refine ⟨w, ?_⟩
  have hneq : ((denInt n t : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hne
  have h : ((denInt n t : ℤ) : ℚ) * (((Δ 16 15 n : ℕ) : ℚ)
      * (candidateM.Pin n * (candidateM.Ppol n).eval ((t : ℚ))))
      = ((denInt n t : ℤ) : ℚ) * (w : ℚ) := by
    have : ((Δ 16 15 n : ℤ) : ℚ) * (z : ℚ) = ((denInt n t : ℤ) : ℚ) * (w : ℚ) := by
      exact_mod_cast congrArg (fun x : ℤ => (x : ℚ)) hw
    calc ((denInt n t : ℤ) : ℚ) * (((Δ 16 15 n : ℕ) : ℚ)
            * (candidateM.Pin n * (candidateM.Ppol n).eval ((t : ℚ))))
        = ((Δ 16 15 n : ℕ) : ℚ) * (((denInt n t : ℤ) : ℚ)
            * (candidateM.Pin n * (candidateM.Ppol n).eval ((t : ℚ)))) := by ring
      _ = ((Δ 16 15 n : ℕ) : ℚ) * (z : ℚ) := by rw [hz]
      _ = ((Δ 16 15 n : ℤ) : ℚ) * (z : ℚ) := by push_cast; ring
      _ = ((denInt n t : ℤ) : ℚ) * (w : ℚ) := this
  exact mul_left_cancel₀ hneq h

end Zeta2PpolVal

#print axioms Zeta2PpolVal.block_eval_int
#print axioms Zeta2PpolVal.factorial_dvd_block_int
#print axioms Zeta2PpolVal.block_eval_factorial_mul
#print axioms Zeta2PpolVal.candidate_numPoly
#print axioms Zeta2PpolVal.Pin_mul_numPoly_int
#print axioms Zeta2PpolVal.ckInt_cast
#print axioms Zeta2PpolVal.denInt_cast
#print axioms Zeta2PpolVal.denInt_mul_Pin_Ppol_int
#print axioms Zeta2PpolVal.cleared_of_denInt_dvd
