/-
# §4.2's hinge — `π²/sin²(πz) = Σ_{n∈ℤ} 1/(z+n)²`, from Mathlib's cot-derivative expansion

The scope audit's §4.2 (the MB line integral ↔ residue sum) is the riskiest unbuilt construction
in the chain.  There is no residue theorem in Mathlib, so the route is series-then-line-integrals:
expand the kernel's `(π/sin πt)²` as `Σ_n 1/(t+n)²` and integrate termwise.  Mathlib carries that
expansion only as `iteratedDerivWithin 1 (π cot(π·)) ℍₒ z = -1! · Σ' n:ℤ, 1/(z+n)²` on the open
upper half-plane.  THIS file turns it into the function the chain integrates.  If this lemma
does not go through, §4.2 is a different order of project; if it does, everything above it is
bookkeeping (dominated convergence + rational line integrals + `hasSum_zeta_two`).

Fail-fast increment MB-1.  ~seconds.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

open Real Complex
open scoped UpperHalfPlane

namespace Zeta2MB

local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

/-- `d/dz [π cot(πz)] = −π²/sin²(πz)` wherever `sin(πz) ≠ 0` — Mathlib has no `hasDerivAt_cot`,
so this is `cos/sin` differentiated by the quotient rule. -/
theorem hasDerivAt_pi_mul_cot_pi_mul (z : ℂ) (hz : Complex.sin (π * z) ≠ 0) :
    HasDerivAt (fun x : ℂ => (π : ℂ) * Complex.cot (π * x))
      (-(π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2) z := by
  have hlin : HasDerivAt (fun x : ℂ => (π : ℂ) * x) (π : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  have hs : HasDerivAt (fun x : ℂ => Complex.sin (π * x)) (Complex.cos (π * z) * π) z :=
    (Complex.hasDerivAt_sin (π * z)).comp z hlin
  have hc : HasDerivAt (fun x : ℂ => Complex.cos (π * x)) (-Complex.sin (π * z) * π) z :=
    (Complex.hasDerivAt_cos (π * z)).comp z hlin
  have hq := (hc.div hs hz).const_mul (π : ℂ)
  have hfun : (fun x : ℂ => (π : ℂ) * Complex.cot (π * x))
      = fun x : ℂ => (π : ℂ) * (Complex.cos (π * x) / Complex.sin (π * x)) := by
    funext x
    rw [Complex.cot_eq_cos_div_sin]
  rw [hfun]
  have h1 := Complex.sin_sq_add_cos_sq (π * z)
  have hnum : -Complex.sin (π * z) * π * Complex.sin (π * z)
      - Complex.cos (π * z) * (Complex.cos (π * z) * π) = -(π : ℂ) := by
    linear_combination (-(π : ℂ)) * h1
  refine hq.congr_deriv ?_
  rw [hnum]
  ring

/-- **The hinge.**  On the open upper half-plane, `π²/sin²(πz) = Σ'_{n∈ℤ} 1/(z+n)²`. -/
theorem pi_sq_div_sin_sq_eq_tsum {z : ℂ} (hz : z ∈ ℍₒ) :
    (π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 = ∑' n : ℤ, 1 / (z + n) ^ 2 := by
  have h := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 1) le_rfl hz
  rw [iteratedDerivWithin_one, derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz]
    at h
  have hsin : Complex.sin (π * z) ≠ 0 :=
    sin_pi_mul_ne_zero (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩)
  rw [(hasDerivAt_pi_mul_cot_pi_mul z hsin).deriv] at h
  norm_num at h
  simp only [one_div]
  linear_combination -h

end Zeta2MB

#print axioms Zeta2MB.hasDerivAt_pi_mul_cot_pi_mul
#print axioms Zeta2MB.pi_sq_div_sin_sq_eq_tsum
