/-
# PNCLR's ASSEMBLY — the Newton-basis identity, and `cleared_of_dvd_PpolZ`'s hypothesis

Row PNCLR of `docs/future/zeta2-lean-chain.md` was left owing exactly two things:

  1. the exact identity, as a Lean statement —

         Π·Ppol(t) = Σ_r  h_{L₀+r} · C(Y − L₀, r) / (L₀ · C(L₀+r, L₀)),   Y = t + 26n + 1,

     with `L₀ = 11n+1` and `h_m = Δ^m H(0)` the Newton coefficients of
     `H(Y) = C(Y−13n−1,13n)·C(Y−15n−1,9n)·C(Y−17n−1,5n)` (`Zeta2NewtonCarry.memberBlocks`);

  2. the discharge of `Zeta2PpolInt.cleared_of_dvd_PpolZ`'s hypothesis
     `(13n)!(9n)!(5n)! ∣ Δ 16 15 n · (11n)! · PpolZ_n(t)` from
     `Zeta2NewtonCarry.termwise_invariant_member`.

Both are here.  The identity is `Ppol_eq_Qpoly` (as polynomials over ℚ, which is STRONGER than
the value form the row recorded) read together with `Qpoly_eval`, which is the row's own value
form at every integer `t`, poles included; the discharge is `asm_dvd`, and `ppolValueCleared` is
`Zeta2PpolVal.PpolValueCleared` — `Δ 16 15 n · Π(n) · Ppol_n(t) ∈ ℤ` — proved.

## What is NOT here, said plainly

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  PNCLR's ROW statement is
`Zeta2PnCleared.PnClearedAt 16 15`, i.e. `Δ·pₙ ∈ ℤ`, and this file does not reach it:
`candidateM.pnPoly` is `Σ_j (Ppol n).coeff j · momI (cell n) j` — a sum over the polynomial's
COEFFICIENTS against Bernoulli moments — while what is proved here is integrality of
`Δ·Π·Ppol` at integer ARGUMENTS.  No lemma in this corpus takes the second to the first, and
this file adds none.  So the row's two recorded remaining obligations close and the row does not.

## The three steps, and where each comes from

* **Newton's forward-difference expansion** (`newton_expansion`) — built here: a function
  `f : ℤ → ℤ` with `DegLE N f` satisfies `f y = Σ_{m ≤ N} Δ^m f(0) · C(y, m)` at every integer
  `y`.  Mathlib has no `Polynomial.binomialPolynomial` and no Newton basis (censused
  2026-09-18, re-derived at this pin by `Zeta2AsmCensus` before this file was written), so the
  basis is built: `nbp s m` over ℚ, whose value at an integer node IS `Ring.choose`.
* **The division** — `Polynomial.div_modByMonic_unique` against the monic `denPoly`, with the
  quotient `Qpoly` and remainder `Rpoly` exhibited.  The identity `Rpoly + denPoly·Qpoly =
  numPoly` is proved by `Polynomial.eq_of_infinite_eval_eq` from agreement at every INTEGER,
  which is where the absorption `Ring.choose_smul_choose` (at general `k`, not the `k = 1`
  `Zeta2DividedDiff.choose_absorb` already consumes) does its work.
* **The divisibility** — `Zeta2NewtonCarry.termwise_invariant_member` termwise, plus
  `D (13n) ∣ Δ 16 15 n` (`Zeta2Arith.D_dvd_D` at `13n ≤ 15n`).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2PpolVal
import Zeta2PpolInt
import Zeta2NewtonCarry

namespace Zeta2NewtonAssemble

open Zeta2Defs Zeta2Arith Zeta2NewtonCarry Finset Polynomial

/-! ## 1. The ascending-product law for `Ring.choose` -/

/-- `len` consecutive integers starting at `c`, as `len ! · C(c + len − 1, len)`.  Proved from
Mathlib's absorption at `k = 1`, so no `descPochhammer` reflection is needed. -/
theorem prod_asc (c : ℤ) (len : ℕ) :
    ∏ i ∈ range len, (c + (i : ℤ))
      = (Nat.factorial len : ℤ) * Ring.choose (c + (len : ℤ) - 1) len := by
  induction len with
  | zero => simp
  | succ L ih =>
    rw [Finset.prod_range_succ, ih]
    have habs := Ring.choose_smul_choose (R := ℤ) (c + (L : ℤ)) (n := L + 1) (k := 1)
      (by omega)
    rw [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right] at habs
    have hL1 : (L + 1) - 1 = L := by omega
    rw [hL1] at habs
    have hfs : ((Nat.factorial (L + 1) : ℕ) : ℤ)
        = ((L : ℤ) + 1) * ((Nat.factorial L : ℕ) : ℤ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hidx : c + ((L + 1 : ℕ) : ℤ) - 1 = c + (L : ℤ) := by push_cast; ring
    rw [hfs, hidx]
    push_cast at habs ⊢
    linear_combination (-((Nat.factorial L : ℕ) : ℤ)) * habs

/-! ## 2. The Newton basis over ℚ — built, because Mathlib has none -/

/-- `nbp s m` is the polynomial whose value at `t` is `C(t + s, m)`: the Newton basis, shifted
by `s`.  `Polynomial.binomialPolynomial` is ABSENT at this pin (re-censused here), and the
basis cannot live in `ℤ[X]` — `C(X,2) = (X²−X)/2` — so it is built over ℚ. -/
noncomputable def nbp (s : ℚ) (m : ℕ) : Polynomial ℚ :=
  C ((Nat.factorial m : ℕ) : ℚ)⁻¹ * ∏ i ∈ range m, (X + C (s - (i : ℚ)))

theorem nbp_eval (s : ℚ) (m : ℕ) (t : ℚ) :
    (nbp s m).eval t = (∏ i ∈ range m, (t + s - (i : ℚ))) / ((Nat.factorial m : ℕ) : ℚ) := by
  rw [nbp, eval_mul, eval_prod, eval_C, div_eq_inv_mul]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by simp only [eval_add, eval_X, eval_C]; ring

theorem nbp_degree (s : ℚ) (m : ℕ) : (nbp s m).degree = (m : ℕ) := by
  have hne : (((Nat.factorial m : ℕ) : ℚ))⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero, Nat.cast_eq_zero]
    exact Nat.factorial_ne_zero m
  rw [nbp, Polynomial.degree_C_mul hne, Polynomial.degree_prod]
  have hsum : ∑ i ∈ range m, (X + C (s - (i : ℚ))).degree = ∑ _i ∈ range m, (1 : WithBot ℕ) :=
    Finset.sum_congr rfl fun i _ => Polynomial.degree_X_add_C _
  rw [hsum]
  simp

/-- **The basis at an integer node IS `Ring.choose`** — the bridge between the ℚ polynomial and
`Zeta2NewtonCarry`'s ℤ-valued objects. -/
theorem nbp_eval_nat (s m : ℕ) (t : ℤ) :
    (nbp ((s : ℕ) : ℚ) m).eval ((t : ℚ)) = ((Ring.choose (t + (s : ℤ)) m : ℤ) : ℚ) := by
  rw [nbp_eval]
  have hf : (((Nat.factorial m : ℕ) : ℚ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Nat.factorial_ne_zero m
  rw [div_eq_iff hf]
  have h := prod_asc (t + (s : ℤ) - (m : ℤ) + 1) m
  have hidx : (t + (s : ℤ) - (m : ℤ) + 1) + (m : ℤ) - 1 = t + (s : ℤ) := by ring
  rw [hidx] at h
  have hcast : (∏ i ∈ range m, ((t : ℚ) + ((s : ℕ) : ℚ) - (i : ℚ)))
      = ((∏ i ∈ range m, ((t + (s : ℤ) - (m : ℤ) + 1) + ((m - 1 - i : ℕ) : ℤ)) : ℤ) : ℚ) := by
    push_cast
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < m := Finset.mem_range.mp hi
    have : ((m - 1 - i : ℕ) : ℚ) = (m : ℚ) - 1 - (i : ℚ) := by
      have h1 : (1 : ℕ) + i ≤ m := by omega
      push_cast [Nat.cast_sub (by omega : i ≤ m - 1), Nat.cast_sub (by omega : 1 ≤ m)]
      ring
    rw [this]
    ring
  rw [hcast, Finset.prod_range_reflect (fun i => (t + (s : ℤ) - (m : ℤ) + 1) + (i : ℤ)) m, h]
  push_cast
  ring

/-! ## 3. Newton's forward-difference expansion -/

/-- A function whose forward difference vanishes everywhere is constant on ALL of ℤ — the
negative half is where `Int.induction_on` earns its keep. -/
theorem eq_of_fwd_zero {f : ℤ → ℤ} (h : ∀ x, fwd f x = 0) (y : ℤ) : f y = f 0 := by
  have hstep : ∀ x : ℤ, f (x + 1) = f x := by
    intro x
    have hx : f (x + 1) - f x = 0 := h x
    omega
  induction y using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [hstep]; exact ih
  | pred k ih =>
      have hk := hstep (-(k : ℤ) - 1)
      rw [show (-(k : ℤ) - 1 + 1) = -(k : ℤ) by ring] at hk
      rw [← hk]; exact ih

/-- **Newton's forward-difference expansion.**  `f y = Σ_{m ≤ N} Δ^m f(0) · C(y, m)` for any
`f : ℤ → ℤ` of finite-difference degree `≤ N`, at EVERY integer `y`.  Not in Mathlib. -/
theorem newton_expansion : ∀ (N : ℕ) (f : ℤ → ℤ), DegLE N f → ∀ y : ℤ,
    f y = ∑ m ∈ range (N + 1), fwdIter m f 0 * Ring.choose y m := by
  intro N
  induction N with
  | zero =>
    intro f hf y
    have h0 : ∀ x, fwd f x = 0 := fun x => hf x
    rw [Finset.sum_range_one]
    have hy := eq_of_fwd_zero h0 y
    simpa [fwdIter, Ring.choose_zero_right] using hy
  | succ N ih =>
    intro f hf y
    have hg : DegLE N (fwd f) := by
      intro x
      have he : fwdIter (N + 1) (fwd f) x = fwdIter (N + 1 + 1) f x :=
        congrFun (fwdIter_add (N + 1) 1 f) x
      rw [he]
      exact hf x
    have hgexp := ih (fwd f) hg
    have hcoef : ∀ j : ℕ, fwdIter j (fwd f) 0 = fwdIter (j + 1) f 0 :=
      fun j => congrFun (fwdIter_add j 1 f) 0
    have hFfwd : ∀ x : ℤ,
        (∑ m ∈ range (N + 1 + 1), fwdIter m f 0 * Ring.choose (x + 1) m)
          - (∑ m ∈ range (N + 1 + 1), fwdIter m f 0 * Ring.choose x m) = fwd f x := by
      intro x
      rw [← Finset.sum_sub_distrib]
      have e1 : ∀ m ∈ range (N + 1 + 1),
          fwdIter m f 0 * Ring.choose (x + 1) m - fwdIter m f 0 * Ring.choose x m
            = fwdIter m f 0 * (Ring.choose (x + 1) m - Ring.choose x m) :=
        fun m _ => by ring
      rw [Finset.sum_congr rfl e1,
        Finset.sum_range_succ'
          (fun m => fwdIter m f 0 * (Ring.choose (x + 1) m - Ring.choose x m)) (N + 1)]
      have hz : fwdIter 0 f 0 * (Ring.choose (x + 1) 0 - Ring.choose x 0) = 0 := by
        simp
      rw [hz, add_zero]
      have hterm : ∀ j ∈ range (N + 1),
          fwdIter (j + 1) f 0 * (Ring.choose (x + 1) (j + 1) - Ring.choose x (j + 1))
            = fwdIter j (fwd f) 0 * Ring.choose x j := by
        intro j _
        rw [Ring.choose_succ_succ, hcoef j]
        ring
      rw [Finset.sum_congr rfl hterm]
      exact (hgexp x).symm
    have hF0 : (∑ m ∈ range (N + 1 + 1), fwdIter m f 0 * Ring.choose (0 : ℤ) m) = f 0 := by
      have h0 : ∀ m ∈ range (N + 1 + 1), m ≠ 0 →
          fwdIter m f 0 * Ring.choose (0 : ℤ) m = 0 := by
        intro m _ hm
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        rw [Ring.choose_zero_succ]
        ring
      rw [Finset.sum_eq_single 0 h0
        (by intro hcon; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) hcon)]
      simp [fwdIter]
    have hdiff : ∀ x : ℤ,
        fwd (fun z => f z - ∑ m ∈ range (N + 1 + 1), fwdIter m f 0 * Ring.choose z m) x = 0 := by
      intro x
      have h1 := hFfwd x
      have h2 : f (x + 1) - f x = fwd f x := rfl
      show (f (x + 1) - ∑ m ∈ range (N + 1 + 1), fwdIter m f 0 * Ring.choose (x + 1) m)
          - (f x - ∑ m ∈ range (N + 1 + 1), fwdIter m f 0 * Ring.choose x m) = 0
      omega
    have hy : f y - (∑ m ∈ range (N + 1 + 1), fwdIter m f 0 * Ring.choose y m)
        = f 0 - (∑ m ∈ range (N + 1 + 1), fwdIter m f 0 * Ring.choose (0 : ℤ) m) :=
      eq_of_fwd_zero hdiff y
    rw [hF0] at hy
    omega

/-! ## 4. The member's `H` has finite-difference degree `27n` -/

theorem degLE_mul {a b : ℕ} {f g : ℤ → ℤ} (hf : DegLE a f) (hg : DegLE b g) :
    DegLE (a + b) (fun y => f y * g y) := by
  intro x
  rw [fwdIter_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases Nat.lt_or_ge a i with h | h
  · rw [fwdIter_eq_zero_of_degLE hf h]; ring
  · have hb : b < a + b + 1 - i := by omega
    rw [fwdIter_eq_zero_of_degLE hg hb]; ring

theorem degLE_one : DegLE 0 (fun _ : ℤ => (1 : ℤ)) := by
  intro x
  show fwdIter 1 (fun _ : ℤ => (1 : ℤ)) x = 0
  rw [fwdIter_succ_apply]
  simp [fwdIter]

/-- `H = C(Y−13n−1,13n)·C(Y−15n−1,9n)·C(Y−17n−1,5n)` has degree `13n + 9n + 5n = 27n`.  The
`27n` is the SUM of the block lengths — `Zeta2NewtonCarry.memberBlocks_degLE`'s `13n` is the
`max`, which is what the invariant's `K` needs and is NOT what Newton's expansion needs. -/
theorem H_degLE (n : ℕ) : DegLE (27 * n) (listProd (memberBlocks n)) := by
  have h1 : DegLE (13 * n) (fun y : ℤ => Ring.choose (y - (13 * (n : ℤ) + 1)) (13 * n)) :=
    degLE_ringChoose_sub _ _
  have h2 : DegLE (9 * n) (fun y : ℤ => Ring.choose (y - (15 * (n : ℤ) + 1)) (9 * n)) :=
    degLE_ringChoose_sub _ _
  have h3 : DegLE (5 * n) (fun y : ℤ => Ring.choose (y - (17 * (n : ℤ) + 1)) (5 * n)) :=
    degLE_ringChoose_sub _ _
  have h6 := degLE_mul h1 (degLE_mul h2 (degLE_mul h3 degLE_one))
  have he : 13 * n + (9 * n + (5 * n + 0)) = 27 * n := by omega
  rw [he] at h6
  exact h6

/-! ## 5. The member's blocks, evaluated -/

/-- A `Zeta2Defs.block` at an integer argument, as `len ! · C(t + c + len − 1, len)`. -/
theorem block_eval_choose (c len : ℕ) (t : ℤ) :
    (block c len).eval ((t : ℚ))
      = (((Nat.factorial len : ℕ) : ℤ)
          * Ring.choose (t + (c : ℤ) + (len : ℤ) - 1) len : ℤ) := by
  rw [Zeta2PpolVal.block_eval_int, prod_asc (t + (c : ℤ)) len]

/-- `H` as the member's own object, spelled with `listProd`. -/
noncomputable def Hfun (n : ℕ) : ℤ → ℤ := listProd (memberBlocks n)

/-- **`numPoly` at an integer `t` is `(13n)!(9n)!(5n)! · H(Y)`**, `Y = t + 26n + 1`.  This is
what makes every statement below about the chain's own `numPoly` and `Zeta2NewtonCarry`'s own
`H`, rather than about retyped twins. -/
theorem numPoly_eval (n : ℕ) (t : ℤ) :
    (candidateM.numPoly n).eval ((t : ℚ))
      = (((Zeta2PpolInt.PinDen n : ℕ) : ℤ) * Hfun n (t + 26 * (n : ℤ) + 1) : ℤ) := by
  rw [Zeta2PpolVal.candidate_numPoly, eval_mul, eval_mul,
    block_eval_choose, block_eval_choose, block_eval_choose, Hfun, listProd_memberBlocks]
  have e1 : t + ((1 : ℕ) : ℤ) + ((13 * n : ℕ) : ℤ) - 1
      = (t + 26 * (n : ℤ) + 1) - (13 * (n : ℤ) + 1) := by push_cast; ring
  have e2 : t + ((2 * n + 1 : ℕ) : ℤ) + ((9 * n : ℕ) : ℤ) - 1
      = (t + 26 * (n : ℤ) + 1) - (15 * (n : ℤ) + 1) := by push_cast; ring
  have e3 : t + ((4 * n + 1 : ℕ) : ℤ) + ((5 * n : ℕ) : ℤ) - 1
      = (t + 26 * (n : ℤ) + 1) - (17 * (n : ℤ) + 1) := by push_cast; ring
  rw [e1, e2, e3, Zeta2PpolInt.PinDen]
  push_cast
  ring

theorem candidate_denPoly (n : ℕ) :
    candidateM.denPoly n = block (15 * n + 1) (11 * n + 1) := rfl

/-- `denPoly` at an integer `t` is `L₀! · C(Y, L₀)`. -/
theorem denPoly_eval (n : ℕ) (t : ℤ) :
    (candidateM.denPoly n).eval ((t : ℚ))
      = (((Nat.factorial (11 * n + 1) : ℕ) : ℤ)
          * Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1) : ℤ) := by
  rw [candidate_denPoly, block_eval_choose]
  have e : t + ((15 * n + 1 : ℕ) : ℤ) + ((11 * n + 1 : ℕ) : ℤ) - 1 = t + 26 * (n : ℤ) + 1 := by
    push_cast; ring
  rw [e]

/-! ## 6. The quotient and the remainder, exhibited -/

/-- The Newton coefficients `h_m = Δ^m H(0)` — `Zeta2NewtonCarry`'s object, not a copy. -/
def hc (n m : ℕ) : ℤ := fwdIter m (listProd (memberBlocks n)) 0

theorem hc_def (n m : ℕ) : hc n m = fwdIter m (listProd (memberBlocks n)) 0 := rfl

/-- **The quotient.**  This IS the row's identity: `Π·Ppol = Σ_r h_{L₀+r}·C(Y−L₀,r) /
(L₀·C(L₀+r,L₀))`, written as a polynomial, with `Π = (11n)!/((13n)!(9n)!(5n)!` folded in as
`PinDen / L₀!` so that the statement is about `Ppol` itself. -/
noncomputable def Qpoly (n : ℕ) : Polynomial ℚ :=
  C (((Zeta2PpolInt.PinDen n : ℕ) : ℚ) / ((Nat.factorial (11 * n + 1) : ℕ) : ℚ)) *
    ∑ r ∈ range (16 * n),
      C (((hc n (11 * n + 1 + r) : ℤ) : ℚ)
          / ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ))
        * nbp ((15 * n : ℕ) : ℚ) r

/-- **The remainder** — the Newton tail below `L₀`, of degree `≤ 11n < 11n+1 = deg denPoly`. -/
noncomputable def Rpoly (n : ℕ) : Polynomial ℚ :=
  C (((Zeta2PpolInt.PinDen n : ℕ) : ℚ)) *
    ∑ m ∈ range (11 * n + 1), C (((hc n m : ℤ) : ℚ)) * nbp ((26 * n + 1 : ℕ) : ℚ) m

theorem degree_C_mul_le' (a : ℚ) (p : Polynomial ℚ) : (C a * p).degree ≤ p.degree := by
  by_cases h : a = 0
  · simp [h]
  · rw [Polynomial.degree_C_mul h]

theorem Rpoly_degree_lt (n : ℕ) : (Rpoly n).degree < (candidateM.denPoly n).degree := by
  have hden : (candidateM.denPoly n).degree = ((11 * n + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (candidateM.denPoly_monic n).ne_zero,
      candidateM.denPoly_natDegree n]
    rfl
  have hR : (Rpoly n).degree ≤ ((11 * n : ℕ) : WithBot ℕ) := by
    rw [Rpoly]
    refine le_trans (degree_C_mul_le' _ _) ?_
    refine le_trans (Polynomial.degree_sum_le _ _) ?_
    refine Finset.sup_le fun m hm => ?_
    refine le_trans (degree_C_mul_le' _ _) ?_
    rw [nbp_degree]
    exact Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
  rw [hden]
  refine lt_of_le_of_lt hR ?_
  exact_mod_cast Nat.lt_succ_self (11 * n)

/-! ## 7. The identity, at every integer and then as polynomials -/

theorem choose_absorb_int (Y : ℤ) (L r : ℕ) :
    ((((L + r).choose L : ℕ)) : ℤ) * Ring.choose Y (L + r)
      = Ring.choose Y L * Ring.choose (Y - (L : ℤ)) r := by
  have h := Ring.choose_smul_choose (R := ℤ) Y (n := L + r) (k := L) (by omega)
  rw [nsmul_eq_mul] at h
  have h2 : L + r - L = r := by omega
  rw [h2] at h
  exact h

/-- `Qpoly` at an integer node — the row's identity in its VALUE form:
`Π·Ppol(t) = Σ_r h_{L₀+r}·C(Y−L₀,r)/(L₀·C(L₀+r,L₀))`, with `Π = PinNum/PinDen` and
`L₀! = L₀·PinNum` the only rearrangement. -/
theorem Qpoly_eval (n : ℕ) (t : ℤ) :
    (Qpoly n).eval ((t : ℚ))
      = ((Zeta2PpolInt.PinDen n : ℕ) : ℚ) / (((Nat.factorial (11 * n + 1) : ℕ)) : ℚ)
        * ∑ r ∈ range (16 * n),
            (((hc n (11 * n + 1 + r) : ℤ) : ℚ)
                / ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ))
              * ((Ring.choose (t + ((15 * n : ℕ) : ℤ)) r : ℤ) : ℚ) := by
  rw [Qpoly, eval_mul, eval_C, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eval_mul, eval_C, nbp_eval_nat]

theorem eval_identity (n : ℕ) (t : ℤ) :
    (Rpoly n).eval ((t : ℚ)) + (candidateM.denPoly n).eval ((t : ℚ)) * (Qpoly n).eval ((t : ℚ))
      = (candidateM.numPoly n).eval ((t : ℚ)) := by
  have hLfac : (((Nat.factorial (11 * n + 1) : ℕ)) : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero _
  -- the Newton expansion of `H` at `Y`, split at `L₀`
  have hnewt := newton_expansion (27 * n) (listProd (memberBlocks n)) (H_degLE n)
    (t + 26 * (n : ℤ) + 1)
  have hsplit : 27 * n + 1 = (11 * n + 1) + 16 * n := by omega
  rw [hsplit, Finset.sum_range_add] at hnewt
  -- the two halves, in ℚ
  have hR : (Rpoly n).eval ((t : ℚ))
      = (((Zeta2PpolInt.PinDen n : ℕ) : ℚ))
        * ∑ m ∈ range (11 * n + 1),
            (((hc n m : ℤ) : ℚ)
              * ((Ring.choose (t + 26 * (n : ℤ) + 1) m : ℤ) : ℚ)) := by
    rw [Rpoly, eval_mul, eval_C, eval_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [eval_mul, eval_C, nbp_eval_nat]
    congr 2
    push_cast
    ring
  have hQ := Qpoly_eval n t
  -- absorption, termwise
  have hterm : ∀ r ∈ range (16 * n),
      ((Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1) : ℤ) : ℚ)
        * ((((hc n (11 * n + 1 + r) : ℤ) : ℚ)
              / ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ))
            * ((Ring.choose (t + ((15 * n : ℕ) : ℤ)) r : ℤ) : ℚ))
      = ((hc n (11 * n + 1 + r) : ℤ) : ℚ)
          * ((Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1 + r) : ℤ) : ℚ) := by
    intro r _
    have hcp : (0 : ℕ) < (11 * n + 1 + r).choose (11 * n + 1) :=
      Nat.choose_pos (by omega)
    have hc0 : ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    have habs := choose_absorb_int (t + 26 * (n : ℤ) + 1) (11 * n + 1) r
    have hshift : (t + 26 * (n : ℤ) + 1) - ((11 * n + 1 : ℕ) : ℤ) = t + ((15 * n : ℕ) : ℤ) := by
      push_cast; ring
    rw [hshift] at habs
    have habsQ : ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ)
        * ((Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1 + r) : ℤ) : ℚ)
        = ((Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1) : ℤ) : ℚ)
          * ((Ring.choose (t + ((15 * n : ℕ) : ℤ)) r : ℤ) : ℚ) := by
      exact_mod_cast habs
    field_simp
    linear_combination (-((hc n (11 * n + 1 + r) : ℤ) : ℚ)) * habsQ
  -- the absorption, summed: `C(Y,L₀)` times the Newton tail IS the tail of the expansion
  have hAT : ((Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1) : ℤ) : ℚ)
      * (∑ r ∈ range (16 * n),
          (((hc n (11 * n + 1 + r) : ℤ) : ℚ)
              / ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ))
            * ((Ring.choose (t + ((15 * n : ℕ) : ℤ)) r : ℤ) : ℚ))
      = ∑ r ∈ range (16 * n),
          (((hc n (11 * n + 1 + r) : ℤ) : ℚ)
            * ((Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1 + r) : ℤ) : ℚ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  -- the two evaluations, in the shape the final `ring` wants
  have hnewt' : Hfun n (t + 26 * (n : ℤ) + 1)
      = (∑ m ∈ range (11 * n + 1), hc n m * Ring.choose (t + 26 * (n : ℤ) + 1) m)
        + ∑ r ∈ range (16 * n),
            hc n (11 * n + 1 + r) * Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1 + r) := hnewt
  have hnum : (candidateM.numPoly n).eval ((t : ℚ))
      = ((Zeta2PpolInt.PinDen n : ℕ) : ℚ)
        * ((∑ m ∈ range (11 * n + 1),
              ((hc n m : ℤ) : ℚ) * ((Ring.choose (t + 26 * (n : ℤ) + 1) m : ℤ) : ℚ))
           + ∑ r ∈ range (16 * n),
              ((hc n (11 * n + 1 + r) : ℤ) : ℚ)
                * ((Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1 + r) : ℤ) : ℚ)) := by
    rw [numPoly_eval, hnewt']
    push_cast
    ring
  have hden' : (candidateM.denPoly n).eval ((t : ℚ))
      = (((Nat.factorial (11 * n + 1) : ℕ)) : ℚ)
        * ((Ring.choose (t + 26 * (n : ℤ) + 1) (11 * n + 1) : ℤ) : ℚ) := by
    rw [denPoly_eval]
    push_cast
    ring
  rw [hR, hQ, hden', hnum, ← hAT]
  field_simp

/-! ## 8. `Ppol` IS the quotient -/

theorem poly_identity (n : ℕ) :
    Rpoly n + candidateM.denPoly n * Qpoly n = candidateM.numPoly n := by
  refine Polynomial.eq_of_infinite_eval_eq _ _
    (Set.infinite_of_injective_forall_mem (f := fun t : ℤ => (t : ℚ)) Int.cast_injective ?_)
  intro t
  show Polynomial.eval ((t : ℚ)) (Rpoly n + candidateM.denPoly n * Qpoly n)
      = Polynomial.eval ((t : ℚ)) (candidateM.numPoly n)
  rw [eval_add, eval_mul]
  exact eval_identity n t

/-- **THE ROW'S IDENTITY, as polynomials.**  `Ppol` IS the Newton quotient — stronger than the
value form the cell recorded, and the statement PNCLR was left owing. -/
theorem Ppol_eq_Qpoly (n : ℕ) : candidateM.Ppol n = Qpoly n :=
  (Polynomial.div_modByMonic_unique (Qpoly n) (Rpoly n) (candidateM.denPoly_monic n)
    ⟨poly_identity n, Rpoly_degree_lt n⟩).1

/-! ## 9. `cleared_of_dvd_PpolZ`'s hypothesis, discharged from the termwise invariant -/

/-- `PpolZ`'s integer value IS the Newton quotient's value. -/
theorem PpolZ_eval_Qpoly (n : ℕ) (t : ℤ) :
    (((Zeta2PpolInt.PpolZ n).eval t : ℤ) : ℚ) = (Qpoly n).eval ((t : ℚ)) := by
  rw [← Zeta2PpolInt.Ppol_eval_int, Ppol_eq_Qpoly]

/-- `D (13n) ∣ Δ 16 15 n` — the second factor is `D (15n)` and `13n ≤ 15n`. -/
theorem D13n_dvd_Δ (n : ℕ) : Zeta2Arith.D (13 * n) ∣ Δ 16 15 n := by
  rw [Zeta2Arith.Δ]
  exact Dvd.dvd.mul_left (Zeta2Arith.D_dvd_D (by omega)) _

/-- **The termwise invariant, at `Δ` rather than at `D (13n)`.** -/
theorem termwise_at_Δ (n r : ℕ) : ∃ z : ℤ,
    ((Δ 16 15 n : ℕ) : ℤ) * hc n (11 * n + 1 + r)
      = (((11 * n + 1) * ((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℤ) * z := by
  obtain ⟨u, hu⟩ := D13n_dvd_Δ n
  obtain ⟨v, hv⟩ := termwise_invariant_member n r
  refine ⟨(u : ℤ) * v, ?_⟩
  have hu' : ((Δ 16 15 n : ℕ) : ℤ) = ((Zeta2Arith.D (13 * n) : ℕ) : ℤ) * (u : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hu
  rw [hu', hc_def]
  linear_combination (u : ℤ) * hv

/-- **THE ROW'S SECOND OBLIGATION, DISCHARGED.**
`(13n)!(9n)!(5n)! ∣ Δ 16 15 n · (11n)! · PpolZ_n(t)` — exactly
`Zeta2PpolInt.cleared_of_dvd_PpolZ`'s hypothesis, at every `n` and every integer `t`, poles
included.  The witness is the termwise quotient summed against the Newton tail. -/
theorem asm_dvd (n : ℕ) (t : ℤ) :
    ((Zeta2PpolInt.PinDen n : ℕ) : ℤ)
      ∣ ((Δ 16 15 n : ℕ) : ℤ) * ((Zeta2PpolInt.PinNum n : ℕ) : ℤ)
          * (Zeta2PpolInt.PpolZ n).eval t := by
  choose w hwe using fun r : ℕ => termwise_at_Δ n r
  refine ⟨∑ r ∈ range (16 * n), w r * Ring.choose (t + ((15 * n : ℕ) : ℤ)) r, ?_⟩
  have hPinNum : ((Zeta2PpolInt.PinNum n : ℕ) : ℚ) = ((Nat.factorial (11 * n) : ℕ) : ℚ) := rfl
  have hfacQ : ((Nat.factorial (11 * n + 1) : ℕ) : ℚ)
      = ((11 * n + 1 : ℕ) : ℚ) * ((Nat.factorial (11 * n) : ℕ) : ℚ) := by
    rw [show Nat.factorial (11 * n + 1) = (11 * n + 1) * Nat.factorial (11 * n) from
      Nat.factorial_succ _]
    push_cast
    ring
  have hmain : ((Δ 16 15 n : ℕ) : ℚ) * ((Zeta2PpolInt.PinNum n : ℕ) : ℚ)
        * (((Zeta2PpolInt.PpolZ n).eval t : ℤ) : ℚ)
      = ((Zeta2PpolInt.PinDen n : ℕ) : ℚ)
          * ∑ r ∈ range (16 * n),
              ((w r : ℤ) : ℚ) * ((Ring.choose (t + ((15 * n : ℕ) : ℤ)) r : ℤ) : ℚ) := by
    rw [PpolZ_eval_Qpoly, Qpoly_eval, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hcb : ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ) ≠ 0 := by
      have := Nat.choose_pos (show 11 * n + 1 ≤ 11 * n + 1 + r by omega)
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hfn : ((Nat.factorial (11 * n) : ℕ) : ℚ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero _
    have hL : ((11 * n + 1 : ℕ) : ℚ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    have hwq : ((Δ 16 15 n : ℕ) : ℚ) * ((hc n (11 * n + 1 + r) : ℤ) : ℚ)
        = ((11 * n + 1 : ℕ) : ℚ) * ((((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℚ)
            * ((w r : ℤ) : ℚ) := by
      have h := hwe r
      have h' := congrArg (fun z : ℤ => (z : ℚ)) h
      push_cast at h' ⊢
      linear_combination h'
    rw [hPinNum, hfacQ]
    field_simp
    linear_combination ((Zeta2PpolInt.PinDen n : ℕ) : ℚ)
      * ((Ring.choose (t + ((15 * n : ℕ) : ℤ)) r : ℤ) : ℚ) * hwq
  exact_mod_cast hmain

/-- **`Zeta2PpolVal.PpolValueCleared` — PROVED.**  `Δ 16 15 n · Π(n) · Ppol_n(t) ∈ ℤ` at every
`n` and every integer `t`.  This was the row's recorded open probe. -/
theorem ppolValueCleared : Zeta2PpolVal.PpolValueCleared :=
  Zeta2PpolInt.ppolValueCleared_of_dvd (fun n t => asm_dvd n t)

end Zeta2NewtonAssemble

#print axioms Zeta2NewtonAssemble.prod_asc
#print axioms Zeta2NewtonAssemble.nbp_eval_nat
#print axioms Zeta2NewtonAssemble.newton_expansion
#print axioms Zeta2NewtonAssemble.H_degLE
#print axioms Zeta2NewtonAssemble.numPoly_eval
#print axioms Zeta2NewtonAssemble.denPoly_eval
#print axioms Zeta2NewtonAssemble.choose_absorb_int
#print axioms Zeta2NewtonAssemble.Qpoly_eval
#print axioms Zeta2NewtonAssemble.Rpoly_degree_lt
#print axioms Zeta2NewtonAssemble.eval_identity
#print axioms Zeta2NewtonAssemble.poly_identity
#print axioms Zeta2NewtonAssemble.Ppol_eq_Qpoly
#print axioms Zeta2NewtonAssemble.PpolZ_eval_Qpoly
#print axioms Zeta2NewtonAssemble.termwise_at_Δ
#print axioms Zeta2NewtonAssemble.asm_dvd
#print axioms Zeta2NewtonAssemble.ppolValueCleared
