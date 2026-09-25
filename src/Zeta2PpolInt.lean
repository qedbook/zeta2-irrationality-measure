/-
# `Zeta2PpolInt.lean` — row PNCLR: **`Ppol` has INTEGER coefficients**, and what that deletes

`Zeta2PpolVal.lean` reduced the row's value statement `Δ·Π·Ppol(t) ∈ ℤ` to one integer
divisibility `den(t) ∣ Δ·N(t)` — with two costs it could not pay:

  (i)  the reduction is stated THROUGH `den(t)`, so it degenerates to `0 = 0` at the `11n+1`
       POLE integers `t = −k`, `k ∈ window n`, and the row carried a named `[E] ~80–150 line`
       gap for "integral at enough non-pole integers ⇒ integral everywhere" (Newton's
       forward-difference basis, not in the corpus);
  (ii) the row read the division by `den`'s `11n+1` linear factors as `11n+1` SUCCESSIVE
       divided-difference steps (`Zeta2DividedDiff.sub_dvd_D_mul_choose_sub` prices one), and
       its open research question was "the `11n+1` steps must not COMPOUND".

**Both costs are an artefact of dividing at all.**  `numPoly` and `denPoly` are products of
`X + C c` with `c : ℕ`, so both are MONIC and both have INTEGER coefficients; division by a
monic polynomial over ℤ stays in ℤ[X], and `Polynomial.map_divByMonic` says the ℚ-division
this chain defines IS that ℤ-division mapped.  So

    `Ppol_eval_int : (candidateM.Ppol n).eval (t : ℚ) = ((PpolZ n).eval t : ℤ)`

at EVERY integer `t` — poles included, no side condition, no iteration, nothing to compound.
`Ppol_eval_int_at_pole` states both halves of (i) in one theorem: at a pole `denInt n t = 0`,
so `Zeta2PpolVal.denInt_mul_Pin_Ppol_int` says `0 = 0` there, while `Ppol_eval_int` still
returns an integer.  The `[E]` Newton-basis gap is not deferred; it is **not needed**.

What is left of the row's value statement is then `cleared_of_dvd_PpolZ`: a single divisibility
among integers with no `t`-side condition, no window, no polynomials over ℚ and no `Π`,

    `(13n)!·(9n)!·(5n)! ∣ Δ 16 15 n · (11n)! · PpolZ_n(t)`,

and `ppolValueCleared_of_dvd` discharges `Zeta2PpolVal.PpolValueCleared` from it — so this file
SUPERSEDES `cleared_of_denInt_dvd` as the row's reduction rather than sitting beside it.

**MEASURED, NOT PROVED (this file proves none of it).**  `ppol_content_probe.py` /
`pnclr_invariant_probe.py` (exact rationals, `n ≤ 5`) turn the remaining divisibility into ONE
number per `n`, because `PpolZ ∈ ℤ[X]` makes the `t`-quantifier collapse onto the polynomial's
fixed divisor `g n = gcd { PpolZ n (t) : t ∈ ℤ }`:

    need n := q n / gcd (q n, g n)   where q n = den(Π n);   the statement is `need n ∣ Δ n`.

`need n` = 52, 4600, 1443, 447440, 5470480 at `n = 1..5`; the least `c` with `need n ∣ D(c·n)`
is 13, 13, 13, **12**, 13 — reproducing, over EVERY integer `t` rather than a sample, the `13`
(and the `n = 4` dip to 12) that `ppol_value_probe.out` had measured by sampling.

**AND THE NON-COMPOUNDING INVARIANT IS FOUND AND IS TERMWISE** (`termwise_probe2.py`,
`leibniz_probe.py`).  With `Y = t + 26n + 1`, `L₀ = 11n+1`, `H(Y) = C(Y−13n−1, 13n)·
C(Y−15n−1, 9n)·C(Y−17n−1, 5n)` integer-valued and `H = Σ_m h_m C(Y,m)`, `h_m = Δ^m H(0) ∈ ℤ`:

    Π·Ppol(t) = Σ_{r ≥ 0}  h_{L₀+r} · C(Y − L₀, r) / ( L₀ · C(L₀+r, L₀) )          (exact)
    INVARIANT:  L₀ · C(L₀+r, L₀)  ∣  D(13n) · h_{L₀+r}   for EVERY r               (measured)

0 of 16 / 32 / 48 / 64 / 80 terms fail at `n = 1..5`; with `D(13n)` deleted 13/16 … 73/80 fail,
and with `D(12n)` in its place 10/16, 12/32, 31/48, 55/80 fail (`n = 4` is the dip, green).  So
NOTHING COMPOUNDS because there is no iteration: the whole division is one identity whose
coefficients are individually cleared by one `D(13n)`.  The invariant is not special to this
member — `L₀·C(L₀+r,L₀) ∣ D(max(max_s L_s, L₀))·h_{L₀+r}` held in 300/300 random block
configurations, sharp in 114 of them, and at the RECORD member `(7,6,5,8;1,2,14)` the measured
constant is 7 = its own longest block.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2PpolVal

namespace Zeta2PpolInt

open Zeta2Defs Zeta2Arith Finset Polynomial

/-! ## 1. The integer twins of `block`, `numPoly`, `denPoly` -/

/-- The integer twin of `Zeta2Defs.block`: the same product, over ℤ. -/
noncomputable def blockZ (c len : ℕ) : Polynomial ℤ :=
  ∏ i ∈ range len, (X + C ((c + i : ℕ) : ℤ))

theorem blockZ_monic (c len : ℕ) : (blockZ c len).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

/-- The twin maps onto the landed ℚ-side `block` — this is the lemma that makes every statement
below about `Zeta2Defs`' own objects rather than about a retyped copy. -/
theorem blockZ_map (c len : ℕ) :
    (blockZ c len).map (Int.castRingHom ℚ) = block c len := by
  rw [blockZ, block, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

/-- `numPoly` over ℤ. -/
noncomputable def numPolyZ (n : ℕ) : Polynomial ℤ :=
  blockZ 1 (13 * n) * blockZ (2 * n + 1) (9 * n) * blockZ (4 * n + 1) (5 * n)

/-- `denPoly` over ℤ — the window block, MONIC. -/
noncomputable def denPolyZ (n : ℕ) : Polynomial ℤ := blockZ (15 * n + 1) (11 * n + 1)

theorem denPolyZ_monic (n : ℕ) : (denPolyZ n).Monic := blockZ_monic _ _

theorem numPolyZ_map (n : ℕ) :
    (numPolyZ n).map (Int.castRingHom ℚ) = candidateM.numPoly n := by
  rw [numPolyZ, Polynomial.map_mul, Polynomial.map_mul, blockZ_map, blockZ_map, blockZ_map]
  rfl

theorem denPolyZ_map (n : ℕ) :
    (denPolyZ n).map (Int.castRingHom ℚ) = candidateM.denPoly n := by
  rw [denPolyZ, blockZ_map]
  rfl

/-! ## 2. `Ppol` over ℤ -/

/-- **`Ppol` over ℤ.**  `denPolyZ` is monic, so this division stays inside `ℤ[X]`. -/
noncomputable def PpolZ (n : ℕ) : Polynomial ℤ := numPolyZ n /ₘ denPolyZ n

/-- The chain's `Ppol` IS this integer polynomial, mapped.  `Polynomial.map_divByMonic`. -/
theorem PpolZ_map (n : ℕ) :
    (PpolZ n).map (Int.castRingHom ℚ) = candidateM.Ppol n := by
  rw [PpolZ, Polynomial.map_divByMonic _ (denPolyZ_monic n), numPolyZ_map, denPolyZ_map]
  rfl

/-- **THE STRUCTURAL FACT.**  `Ppol` takes an INTEGER value at every integer `t` — no
hypothesis, no window, no pole condition, no divided difference. -/
theorem Ppol_eval_int (n : ℕ) (t : ℤ) :
    (candidateM.Ppol n).eval ((t : ℚ)) = (((PpolZ n).eval t : ℤ) : ℚ) := by
  rw [← PpolZ_map n]
  simp

/-- **The pole gap is CLOSED, not deferred.**  At `t = −k` with `k` in the window the old
route's `denInt n t` is `0`, so `Zeta2PpolVal.denInt_mul_Pin_Ppol_int` degenerates to `0 = 0`
there; `Ppol_eval_int` is unaffected and still returns an integer.  Both halves in one
statement, so the `[E]` "integral at enough non-pole integers ⇒ integral everywhere" step the
row carried is not needed. -/
theorem Ppol_eval_int_at_pole (n k : ℕ) (hk : k ∈ candidateM.window n) :
    Zeta2PpolVal.denInt n (-(k : ℤ)) = 0 ∧
      (candidateM.Ppol n).eval ((-(k : ℤ) : ℚ))
        = (((PpolZ n).eval (-(k : ℤ)) : ℤ) : ℚ) := by
  refine ⟨?_, ?_⟩
  · rw [Zeta2PpolVal.denInt]
    exact Finset.prod_eq_zero hk (by ring)
  · have h := Ppol_eval_int n (-(k : ℤ))
    push_cast at h ⊢
    exact h

/-! ## 3. The reduction, with no side condition -/

/-- `Π`'s numerator, `(11n)!`. -/
def PinNum (n : ℕ) : ℕ := Nat.factorial (11 * n)

/-- `Π`'s denominator, `(13n)!(9n)!(5n)!`. -/
def PinDen (n : ℕ) : ℕ :=
  Nat.factorial (13 * n) * Nat.factorial (9 * n) * Nat.factorial (5 * n)

theorem PinDen_ne_zero (n : ℕ) : ((PinDen n : ℕ) : ℚ) ≠ 0 := by
  have h : PinDen n ≠ 0 := by
    simp [PinDen, Nat.factorial_ne_zero]
  exact_mod_cast h

/-- **THE REDUCTION, superseding `Zeta2PpolVal.cleared_of_denInt_dvd`.**  One divisibility among
integers — no `t ≠ pole`, no window, no `Π`, no polynomial over ℚ:

`(13n)!(9n)!(5n)! ∣ Δ 16 15 n · (11n)! · PpolZ_n(t)`  ⟹  `Δ·Π·Ppol(t) ∈ ℤ`. -/
theorem cleared_of_dvd_PpolZ (n : ℕ) (t : ℤ)
    (hd : ((PinDen n : ℕ) : ℤ)
      ∣ ((Δ 16 15 n : ℕ) : ℤ) * ((PinNum n : ℕ) : ℤ) * (PpolZ n).eval t) :
    ∃ w : ℤ, ((Δ 16 15 n : ℕ) : ℚ)
      * (candidateM.Pin n * (candidateM.Ppol n).eval ((t : ℚ))) = (w : ℚ) := by
  obtain ⟨w, hw⟩ := hd
  refine ⟨w, ?_⟩
  have hcast : ((Δ 16 15 n : ℕ) : ℚ) * ((PinNum n : ℕ) : ℚ) * (((PpolZ n).eval t : ℤ) : ℚ)
      = ((PinDen n : ℕ) : ℚ) * (w : ℚ) := by exact_mod_cast hw
  have hne := PinDen_ne_zero n
  have hPin : candidateM.Pin n = ((PinNum n : ℕ) : ℚ) / ((PinDen n : ℕ) : ℚ) := rfl
  rw [hPin, Ppol_eval_int]
  field_simp
  linear_combination hcast

/-- **The row's open probe, discharged from the divisibility.**  `PpolValueCleared` — the exact
statement `Zeta2PpolVal` left open — follows from the single integer divisibility, at EVERY `n`
and EVERY integer `t`, poles included. -/
theorem ppolValueCleared_of_dvd
    (h : ∀ (n : ℕ) (t : ℤ), ((PinDen n : ℕ) : ℤ)
      ∣ ((Δ 16 15 n : ℕ) : ℤ) * ((PinNum n : ℕ) : ℤ) * (PpolZ n).eval t) :
    Zeta2PpolVal.PpolValueCleared :=
  fun n t => cleared_of_dvd_PpolZ n t (h n t)

end Zeta2PpolInt

#print axioms Zeta2PpolInt.blockZ_monic
#print axioms Zeta2PpolInt.blockZ_map
#print axioms Zeta2PpolInt.numPolyZ_map
#print axioms Zeta2PpolInt.denPolyZ_map
#print axioms Zeta2PpolInt.PpolZ_map
#print axioms Zeta2PpolInt.Ppol_eval_int
#print axioms Zeta2PpolInt.Ppol_eval_int_at_pole
#print axioms Zeta2PpolInt.cleared_of_dvd_PpolZ
#print axioms Zeta2PpolInt.ppolValueCleared_of_dvd
