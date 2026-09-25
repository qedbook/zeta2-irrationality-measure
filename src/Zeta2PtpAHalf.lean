/-
# Row PT-P, layer 11 — `AHalfOpen` COMPOSED over every profile piece, HYPOTHESIS-FREE, and the
# row's output binder `hP` at `ΔT` from the two halves: conditional on `PolyHalfOpen`, NOTHING ELSE

Every window cell `(n, p)` has its residue `x = {n/p}` either in one of the 26 rows of
`candidateProfile` or in none.  In a row, `φ̃ = v` (`Zeta2PtpS7.phiT_of_mem`) and the row's own
theorem gives `p^v ∣ blockSum n p t` at every block — the five run-carrying pieces through
`Zeta2PtpS7` (piece 7) and `Zeta2PtpS2a/b/c/d` (pieces 2, 16, 13, 25, conditional on Anton),
the 21 run-free pieces through `Zeta2PtpRunFree` (termwise).  In no row, `φ̃ = 0`
(`phiT_eq_zero_of_forall`) and `p^0 ∣ _` is `one_dvd`.  `Zeta2PtpBlock.AHalfOpen_of_blocks`
then gives `AHalfOpen`, and `Zeta2PtpPolar.hP_at_ΔT_of_two_halves` the row's output binder from
`PolyHalfOpen` and `AHalfOpen`.

READ THE TYPES (LEAN.md §1: a binder is not an axiom).  The stratum files `Zeta2PtpS2a/b/c/d`
state their pieces with `AntonOneCarry p` as a binder; this file discharges it once, at every
prime, from `Zeta2Anton.choose_div_p_modEq_of_one_carry` (`anton_all`).  So `aHalfOpen : AHalfOpen`
carries NO hypothesis and `hP_at_ΔT_of_poly` carries exactly one, `PolyHalfOpen`.  The 26 rows,
the twelve strata of the five run-carrying pieces and the 29 strata of the 21 run-free ones are all
theorems.  `PolyHalfOpen` — `v_p(Δ·Π·pnPoly) ≥ φ̃`, measured 366 of 366 — is the whole of what
PT-P still owes.  The `_of_anton` forms stay as the composition's conditional statement.

Falsifier: `falsify_ptpahalf.sh` / `out_ptpahalf_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2Profile
import Zeta2PhiT
import Zeta2PhiTDvd
import Zeta2PtpPolar
import Zeta2PtpRun
import Zeta2PtpStratum
import Zeta2PtpCong
import Zeta2PtpBlock
import Zeta2PtpS7
import Zeta2PtpS2Kit
import Zeta2PtpS2a
import Zeta2PtpS2b
import Zeta2PtpS2c
import Zeta2PtpS2d
import Zeta2PtpRunFree
import Zeta2CarryFull
import Zeta2Anton

set_option maxRecDepth 20000

namespace Zeta2PtpAHalf

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpPolar Zeta2PtpBlock Zeta2PtpS7 Zeta2PtpRunFree
  Nat Finset

/-- Off every row, `φ̃ = 0`. -/
theorem phiT_eq_zero_of_forall {x : ℚ}
    (h : ∀ tr ∈ Zeta2Profile.candidateProfile, ¬ (tr.1 ≤ x ∧ x < tr.2.1)) : phiT x = 0 := by
  apply phiT_of_find_none
  rw [List.find?_eq_none]
  intro tr htr
  simp only [decide_eq_true_eq]
  exact h tr htr

/-- **Every block of every window cell carries `p^φ̃`**, given Anton at every prime. -/
theorem blocks_all (hanton : ∀ p : ℕ, [Fact p.Prime] → Zeta2PtpS2a.AntonOneCarry p) :
    ∀ n p, p ∈ phiWindow n →
      ∀ t, (p : ℤ) ^ (phiT (Int.fract ((n : ℚ) / (p : ℚ)))) ∣ blockSum n p t := by
  intro n p hp t
  have hpp := prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 := hpp.pos
  by_cases hex : ∃ tr ∈ Zeta2Profile.candidateProfile,
      tr.1 ≤ Int.fract ((n : ℚ) / (p : ℚ)) ∧ Int.fract ((n : ℚ) / (p : ℚ)) < tr.2.1
  · obtain ⟨tr, htr, h1, h2⟩ := hex
    simp only [Zeta2Profile.candidateProfile, List.mem_cons, List.not_mem_nil, or_false] at htr
    rcases htr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> dsimp only at h1 h2
    · have hlo := (fract_ge_iff n p 1 15 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 1 13 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece1_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 1 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 2 17 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact Zeta2PtpS2a.piece2_blocks (hanton p) hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 2 17 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 1 7 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece3_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 1 7 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 2 13 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece4_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 2 13 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 2 11 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece5_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 2 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 1 5 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece6_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 1 5 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 4 17 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact Zeta2PtpS7.piece7_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 3 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 4 13 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece8_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 4 13 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 4 11 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece9_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 4 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 5 13 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece10_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 5 13 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 2 5 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece11_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 3 7 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 5 11 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece12_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 5 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 7 15 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact Zeta2PtpS2c.piece13_blocks (hanton p) hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 7 15 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 8 17 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece14_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 8 15 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 7 13 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece15_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 6 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 9 16 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact Zeta2PtpS2b.piece16_blocks (hanton p) hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 9 16 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 8 13 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece17_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 7 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 11 17 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece18_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 11 17 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 9 13 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece19_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 5 7 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 8 11 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece20_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 8 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 10 13 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece21_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 10 13 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 4 5 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece22_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 9 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 14 17 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece23_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 14 17 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 10 11 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece24_blocks hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 10 11 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 14 15 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact Zeta2PtpS2d.piece25_blocks (hanton p) hp (by omega) (by omega) t
    · have hlo := (fract_ge_iff n p 14 15 hp0 (by norm_num)).1 (by exact_mod_cast h1)
      have hhi := (fract_lt_iff n p 16 17 hp0 (by norm_num)).1 (by exact_mod_cast h2)
      exact piece26_blocks hp (by omega) (by omega) t
  · rw [phiT_eq_zero_of_forall (fun tr htr h => hex ⟨tr, htr, h⟩), pow_zero]
    exact one_dvd _

/-- **`AHalfOpen`, conditional on Anton alone.** -/
theorem AHalfOpen_of_anton (hanton : ∀ p : ℕ, [Fact p.Prime] → Zeta2PtpS2a.AntonOneCarry p) :
    AHalfOpen :=
  AHalfOpen_of_blocks (blocks_all hanton)

/-- **ROW PT-P's OUTPUT BINDER, conditional on `PolyHalfOpen` and Anton — and on nothing else.**
`P n = ΔT n · pₙ` is an integer for every `n`. -/
theorem hP_at_ΔT_of_poly_of_anton (hpoly : PolyHalfOpen)
    (hanton : ∀ p : ℕ, [Fact p.Prime] → Zeta2PtpS2a.AntonOneCarry p) :
    ∃ P : ℕ → ℤ, ∀ n, ((P n : ℤ) : ℝ) = ΔT n * ((candidateM.pn n : ℚ) : ℝ) :=
  hP_at_ΔT_of_two_halves hpoly (AHalfOpen_of_anton hanton)

/-! ## The Anton binder, discharged

`Zeta2Anton.AntonOneCarry` is stated with exactly `Zeta2PtpS2a.AntonOneCarry`'s body, so the
proved one-carry congruence closes the consumer's binder by unfolding both definitions. -/

/-- **Anton's one-carry congruence at every prime** — a theorem, `Zeta2Anton`'s. -/
theorem anton_all : ∀ p : ℕ, [Fact p.Prime] → Zeta2PtpS2a.AntonOneCarry p :=
  fun p hp => @Zeta2Anton.choose_div_p_modEq_of_one_carry p hp

/-- **`AHalfOpen`, HYPOTHESIS-FREE**: `v_p(A_n) ≥ φ̃({n/p})` at every window cell `(n, p)`. -/
theorem aHalfOpen : AHalfOpen :=
  AHalfOpen_of_anton anton_all

/-- **ROW PT-P's OUTPUT BINDER, conditional on `PolyHalfOpen` ALONE.** -/
theorem hP_at_ΔT_of_poly (hpoly : PolyHalfOpen) :
    ∃ P : ℕ → ℤ, ∀ n, ((P n : ℤ) : ℝ) = ΔT n * ((candidateM.pn n : ℚ) : ℝ) :=
  hP_at_ΔT_of_two_halves hpoly aHalfOpen

end Zeta2PtpAHalf

#print axioms Zeta2PtpAHalf.phiT_eq_zero_of_forall
#check @Zeta2PtpAHalf.phiT_eq_zero_of_forall
#print axioms Zeta2PtpAHalf.blocks_all
#check @Zeta2PtpAHalf.blocks_all
#print axioms Zeta2PtpAHalf.AHalfOpen_of_anton
#check @Zeta2PtpAHalf.AHalfOpen_of_anton
#print axioms Zeta2PtpAHalf.hP_at_ΔT_of_poly_of_anton
#check @Zeta2PtpAHalf.hP_at_ΔT_of_poly_of_anton
#print axioms Zeta2PtpAHalf.anton_all
#check @Zeta2PtpAHalf.anton_all
#print axioms Zeta2PtpAHalf.aHalfOpen
#check @Zeta2PtpAHalf.aHalfOpen
#print axioms Zeta2PtpAHalf.hP_at_ΔT_of_poly
#check @Zeta2PtpAHalf.hP_at_ΔT_of_poly
