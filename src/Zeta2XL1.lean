/-
# Row X-L1 (lemma half) — nine of the fourteen hypotheses, discharged at the real operator

`Zeta2Instantiate.candidate_rn_growth_of_L1` is landed and receipt-clean: it applies the B1/D1
capstone to the REAL `candidateM.rn`.  Its ASSEMBLY was never the open work — its **fourteen
hypotheses** were, and they do not all belong to the same row:

| # | hypothesis | status |
|---|---|---|
| 1 | `hL` — the three-term recurrence at `candidateM.rn` | open, B1–B5 (the `MBSolveResult.coords` work) |
| 2–5 | `h₀`–`h₃` — `Pⱼ.eval n = B.eval n · αⱼ n` | open, same row |
| 6 | `hP₃ : P₃ ≠ 0` | **here**, `degree_lead_of_coeff` (see below) |
| 7–9 | `hd₀`–`hd₂` — equal degrees | **here**, `candidate_rn_growth_of_recurrence` |
| 10–12 | `hA₀`–`hA₂` — leading-coefficient ratio bounds | **here**, `hA0`/`hA1`/`hA2` |
| 13 | `hρ : 0 < ρ` | **here**, `rho_pos` |
| 14 | `hchar` — the majorant cubic | **ALREADY DONE** by the landed `zeta2_L5_char`; bridged, not re-proved |

What is discharged here is everything that depends only on the operator's DEGREE and its four
LEADING COEFFICIENTS, and it is discharged at the certified operator's own exact integers
(`Zeta2XL1Data`, generated from `chain_close_design/results/solution_a.txt`).  The remaining five
are the recurrence itself.

**`hchar` was already proved and is NOT re-proved here.**  It is the landed `zeta2_L5_char` —
D1's 146-digit cleared integer inequality at the certified operator's own leading coefficients —
imported and bridged to the real statement by `char_of_cleared`, whose whole content is one
multiplication by `cden³ > 0`.  A duplicate would be a second thing the next reader has to
reconcile.

**What `hP₃` is and is not — the near-miss in this census.**  `Zeta2L4.c3_ne_zero` is a strictly
STRONGER fact about the same polynomial (`cleared_3` has no natural-number root at all, by a
dominance criterion above `m₀ = 1127` and an exact mod-p scan below it), and reading the census
quickly it looks like `hP₃` already done.  It is not: it is stated about a `List ℤ` through
`Zeta2L4.hornerZ`, and no `List ℤ → ℝ[X]` bridge exists anywhere in this corpus.  X-L1's `hP₃` is
only `P₃ ≠ 0`, which `degree_lead_of_coeff` delivers from the top coefficient directly — so this
file proves it that way rather than building the bridge, and records here that the two facts are
about the same object so nobody proves it twice.

**The degree-510 coefficient data IS in the repo.**  `Zeta2D4.lean`'s header says "the
candidate's own degree-510 cleared coefficients are NOT in the repo, so the instantiation is not
available"; that was true when written and is now stale — `chain_close_design/l4_data.py` rebuilds
all four `cleared_j` from `results/solution_a.txt` in under a second, and `Zeta2L4.lean` already
carries two of them in full.  Only four integers of that quadruple are needed here, and
`gen_xl1_lean.py` extracts them with five cross-checks and a falsifier.

**The conclusion at these constants is a GROWTH bound.**  `ρ ≈ 1.7987e18` is the certified
operator's dominant root modulus, and `one_lt_rhoChar` says so inside the kernel.
`Zeta2Instantiate`'s docstring calls the conclusion "a decay bound on `r_n` itself"; that reading
is wrong for D1's own `ρ`, and the row that needs this growth statement is L9's `hCq`/`hgrowth`,
which is about `qn` — no `candidate_qn_growth_of_L1` exists yet.

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox.
-/
import Zeta2XL1Data
import Zeta2Instantiate
import Zeta2L5Char

namespace Zeta2XL1

open Polynomial Zeta2Defs Zeta2XL1Data

/-! ## §1 The shape bridge — from a top coefficient to `degree` and `leadingCoeff`

The four cleared polynomials have degree 510 with 632–658-digit coefficients.  Reading their
degree off a literal the way `Zeta2L5Deg454.lean` does (`compute_degree!`) costs ~1m27s at degree
164, so this row does not carry the coefficient lists at all: `natDegree ≤ 510` together with a
nonzero coefficient at 510 is everything `hd`, `hA` and `hP₃` need, and both facts are exactly
what any construction of `cleared_j` from its coefficients hands you.
-/

/-- **The whole shape bridge.**  A polynomial with no coefficient above index `d` and a nonzero
coefficient AT `d` is nonzero, has degree `d`, and has that coefficient as its leading one.

This is stated with the hypotheses a caller PRODUCES (LEAN.md §3): whoever builds `cleared_j` from
its 511 coefficients gets `natDegree ≤ 510` and `coeff 510 = …` for free, and never has to run a
degree computation over the literals. -/
theorem degree_lead_of_coeff {P : ℝ[X]} {d : ℕ} {c : ℝ}
    (hle : P.natDegree ≤ d) (hc : P.coeff d = c) (hc0 : c ≠ 0) :
    P ≠ 0 ∧ P.degree = (d : WithBot ℕ) ∧ P.leadingCoeff = c := by
  have hne : P.coeff d ≠ 0 := by rw [hc]; exact hc0
  have hP0 : P ≠ 0 := by
    intro h
    apply hne
    rw [h, Polynomial.coeff_zero]
  have hnd : P.natDegree = d := le_antisymm hle (Polynomial.le_natDegree_of_ne_zero hne)
  refine ⟨hP0, ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hP0, hnd]
  · have hlc : P.leadingCoeff = P.coeff P.natDegree := rfl
    rw [hlc, hnd, hc]

/-! ## §2 D1's majorant constants, as real numbers

`A₀`, `A₁`, `A₂` and `ρ` are rationals over one common denominator — that is exactly the form
`zeta2_L5_char` cleared them into, and `Zeta2XL1Data` carries the five numerators parsed out of
that landed theorem rather than retyped.
-/

/-- D1's `A₀ = |ℓ₀/ℓ₃| · (1 + 10⁻¹²)`. -/
noncomputable def Aco0 : ℝ := (aNum0 : ℝ) / (cden : ℝ)

/-- D1's `A₁ = |ℓ₁/ℓ₃| · (1 + 10⁻¹²)`. -/
noncomputable def Aco1 : ℝ := (aNum1 : ℝ) / (cden : ℝ)

/-- D1's `A₂ = |ℓ₂/ℓ₃| · (1 + 10⁻¹²)`. -/
noncomputable def Aco2 : ℝ := (aNum2 : ℝ) / (cden : ℝ)

/-- D1's `ρ = A₂ · (1 + 10⁻³⁰)`, the growth rate the capstone's conclusion is stated at. -/
noncomputable def rhoChar : ℝ := (rhoNum : ℝ) / (cden : ℝ)

/-- The common denominator, positive in `ℝ`. -/
theorem cden_posR : (0 : ℝ) < (cden : ℝ) := by exact_mod_cast cden_pos

/-- **`hρ`.** -/
theorem rho_pos : 0 < rhoChar := div_pos (by exact_mod_cast rhoNum_pos) cden_posR

/-- `lead₀ ≠ 0` in `ℝ`, the input `degree_lead_of_coeff` needs. -/
theorem lead0_neR : ((lead0 : ℤ) : ℝ) ≠ 0 := by
  have h : (0 : ℝ) < ((lead0 : ℤ) : ℝ) := by exact_mod_cast lead0_pos
  exact h.ne'

/-- `lead₁ ≠ 0` in `ℝ`. -/
theorem lead1_neR : ((lead1 : ℤ) : ℝ) ≠ 0 := by
  have h : (0 : ℝ) < ((lead1 : ℤ) : ℝ) := by exact_mod_cast lead1_pos
  exact h.ne'

/-- `lead₂ ≠ 0` in `ℝ`. -/
theorem lead2_neR : ((lead2 : ℤ) : ℝ) ≠ 0 := by
  have h : (0 : ℝ) < ((lead2 : ℤ) : ℝ) := by exact_mod_cast lead2_pos
  exact h.ne'

/-- `lead₃ ≠ 0` in `ℝ`. -/
theorem lead3_neR : ((lead3 : ℤ) : ℝ) ≠ 0 := by
  have h : (0 : ℝ) < ((lead3 : ℤ) : ℝ) := by exact_mod_cast lead3_pos
  exact h.ne'

/-! ## §3 `hA₀`–`hA₂` — the leading-coefficient ratio bounds -/

/-- A ratio of positive integers, bounded by another ratio of positive integers, decided by one
cross-multiplication.  No division lemma is used: the comparison is transported by multiplying
through by the positive product of the two denominators. -/
theorem abs_ratio_lt_of_int {p q a y : ℤ} (hp : 0 < p) (hq : 0 < q) (hy : 0 < y)
    (h : p * y < a * q) : |(p : ℝ) / (q : ℝ)| < (a : ℝ) / (y : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  have hy0 : (y : ℝ) ≠ 0 := hyR.ne'
  have hR : (p : ℝ) * (y : ℝ) < (a : ℝ) * (q : ℝ) := by exact_mod_cast h
  have hqy : (0 : ℝ) < (q : ℝ) * (y : ℝ) := mul_pos hqR hyR
  rw [abs_div, abs_of_pos hpR, abs_of_pos hqR]
  refine lt_of_mul_lt_mul_right ?_ hqy.le
  have e1 : (p : ℝ) / (q : ℝ) * ((q : ℝ) * (y : ℝ)) = (p : ℝ) * (y : ℝ) := by
    field_simp
  -- `field_simp` closes both of these outright; a trailing `ring` would error with
  -- "No goals to be solved" (LEAN.md §8 — read the error, do not cargo-cult the pair).
  have e2 : (a : ℝ) / (y : ℝ) * ((q : ℝ) * (y : ℝ)) = (a : ℝ) * (q : ℝ) := by
    field_simp
  rw [e1, e2]
  exact hR

/-- The strict inequality `hA` wants, extracted from the EXACT `(1 + 10⁻¹²)` relation the data
file pins.  Keeping the exact form as the primitive and deriving the inequality means a drifted
constant fails at the equality rather than sliding through a slack bound. -/
theorem lt_of_ratio_exact {p q a r : ℤ} (hpq : 0 < p * q)
    (h : a * r * 10 ^ 12 = p * q * (10 ^ 12 + 1)) : p * q < a * r := by
  have h1 : p * q * 10 ^ 12 < a * r * 10 ^ 12 := by
    rw [h]; nlinarith [hpq]
  exact lt_of_mul_lt_mul_right h1 (by norm_num)

/-- `lead₀ · cden < aNum₀ · lead₃`. -/
theorem ratio0_lt : lead0 * cden < aNum0 * lead3 :=
  lt_of_ratio_exact (mul_pos lead0_pos cden_pos) ratio0_exact

/-- `lead₁ · cden < aNum₁ · lead₃`. -/
theorem ratio1_lt : lead1 * cden < aNum1 * lead3 :=
  lt_of_ratio_exact (mul_pos lead1_pos cden_pos) ratio1_exact

/-- `lead₂ · cden < aNum₂ · lead₃`. -/
theorem ratio2_lt : lead2 * cden < aNum2 * lead3 :=
  lt_of_ratio_exact (mul_pos lead2_pos cden_pos) ratio2_exact

/-- **`hA₀` at the certified operator's own leading coefficients.** -/
theorem hA0 : |((lead0 : ℤ) : ℝ) / ((lead3 : ℤ) : ℝ)| < Aco0 :=
  abs_ratio_lt_of_int lead0_pos lead3_pos cden_pos ratio0_lt

/-- **`hA₁` at the certified operator's own leading coefficients.** -/
theorem hA1 : |((lead1 : ℤ) : ℝ) / ((lead3 : ℤ) : ℝ)| < Aco1 :=
  abs_ratio_lt_of_int lead1_pos lead3_pos cden_pos ratio1_lt

/-- **`hA₂` at the certified operator's own leading coefficients.** -/
theorem hA2 : |((lead2 : ℤ) : ℝ) / ((lead3 : ℤ) : ℝ)| < Aco2 :=
  abs_ratio_lt_of_int lead2_pos lead3_pos cden_pos ratio2_lt

/-! ## §4 `hchar` — the landed `zeta2_L5_char`, bridged rather than re-proved -/

/-- **The cleared-to-real bridge for the majorant cubic.**  Generic in the five reals, so no big
literal ever reaches this proof: the whole content is one multiplication by `y³ > 0`. -/
theorem char_of_cleared {a0 a1 a2 x y : ℝ} (hy : 0 < y)
    (h : a2 * x ^ 2 + a1 * x * y + a0 * y ^ 2 ≤ x ^ 3) :
    a2 / y * (x / y) ^ 2 + a1 / y * (x / y) + a0 / y ≤ (x / y) ^ 3 := by
  have hy0 : y ≠ 0 := hy.ne'
  have hy3 : (0 : ℝ) < y ^ 3 := by positivity
  refine le_of_mul_le_mul_right ?_ hy3
  have e1 : (a2 / y * (x / y) ^ 2 + a1 / y * (x / y) + a0 / y) * y ^ 3
      = a2 * x ^ 2 + a1 * x * y + a0 * y ^ 2 := by
    field_simp
  have e2 : (x / y) ^ 3 * y ^ 3 = x ^ 3 := by
    field_simp
  rw [e1, e2]
  exact h

/-- **`hchar`, at D1's certified constants.**  The arithmetic is `zeta2_L5_char`'s — a 146-digit
integer inequality that `norm_num` decides, with its own falsifier — and nothing here re-does it. -/
theorem char_real : Aco2 * rhoChar ^ 2 + Aco1 * rhoChar + Aco0 ≤ rhoChar ^ 3 := by
  have hZ : aNum2 * rhoNum ^ 2 + aNum1 * rhoNum * cden + aNum0 * cden ^ 2 ≤ rhoNum ^ 3 :=
    zeta2_L5_char
  have hR : (aNum2 : ℝ) * (rhoNum : ℝ) ^ 2 + (aNum1 : ℝ) * (rhoNum : ℝ) * (cden : ℝ)
      + (aNum0 : ℝ) * (cden : ℝ) ^ 2 ≤ (rhoNum : ℝ) ^ 3 := by exact_mod_cast hZ
  exact char_of_cleared cden_posR hR

/-! ## §5 Edge checks (LEAN.md §5 — a lemma false at an edge elaborates fine) -/

/-- **`hA` alone cannot see a degree drop, and this is why `hd` is a separate hypothesis.**  A
polynomial whose leading coefficient VANISHED would satisfy every `hA` bound vacuously — the
absolute ratio is then `0`, below any positive `A`.  What excludes that case is `hd`, and `hd`
holds only because `lead₀_pos`–`lead₃_pos` do.  Stated as a theorem rather than a comment because
this corpus has already met four hypotheses that were green and vacuous. -/
theorem hA_admits_a_vanishing_leading_coeff (q A : ℝ) (hA : 0 < A) : |(0 : ℝ) / q| < A := by
  simpa using hA

/-- **The majorant cubic FAILS at `ρ = A₂`, always.**  `A₂·A₂² + A₁·A₂ + A₀ ≤ A₂³` reduces to
`A₁·A₂ + A₀ ≤ 0`, which is false for positive constants — so D1's `(1 + 10⁻³⁰)` inflation of `ρ`
above `A₂` is load-bearing, not decoration.

`Zeta2L5CharFalsify.lean` makes the same point by being a file that must fail to compile; a file
that must go red cannot be checked by anything that only runs green files, so the same content is
recorded here as a theorem. -/
theorem majorant_fails_at_A2 {A0 A1 A2 : ℝ} (h0 : 0 < A0) (h1 : 0 < A1) (h2 : 0 < A2) :
    ¬ (A2 * A2 ^ 2 + A1 * A2 + A0 ≤ A2 ^ 3) := by
  intro h
  nlinarith [mul_pos h1 h2]

/-- `1 < p/q` from `q < p`, without a division lemma. -/
theorem one_lt_div_of_int {p q : ℤ} (hq : 0 < q) (h : q < p) : 1 < (p : ℝ) / (q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  have hR : (q : ℝ) < (p : ℝ) := by exact_mod_cast h
  refine lt_of_mul_lt_mul_right ?_ hqR.le
  have e : (p : ℝ) / (q : ℝ) * (q : ℝ) = (p : ℝ) := by field_simp
  rw [e, one_mul]
  exact hR

/-- `c < p/q` from `c·q < p`, without a division lemma. -/
theorem int_lt_div {c p q : ℤ} (hq : 0 < q) (h : c * q < p) : (c : ℝ) < (p : ℝ) / (q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  refine lt_of_mul_lt_mul_right ?_ hqR.le
  have e : (p : ℝ) / (q : ℝ) * (q : ℝ) = (p : ℝ) := by field_simp
  rw [e]
  exact_mod_cast h

/-- **`1 < ρ`.**  The conclusion X-L1 delivers at D1's constants is a GROWTH bound: `ρ` is the
certified operator's dominant root modulus, ≈ 1.7987e18.  Recorded because the landed
`Zeta2Instantiate` docstring reads it the other way. -/
theorem one_lt_rhoChar : 1 < rhoChar := one_lt_div_of_int cden_pos cden_lt_rhoNum

/-- **`ρ` lies strictly above `Zeta2D4Data.chiOp_root_enclosure`'s upper endpoint.**  That
enclosure brackets the certified operator's dominant root modulus `|λ₁|` between two consecutive
integers; this says D1's `ρ` really is above it, tying two independently landed artifacts together
inside the kernel.  `Zeta2XL1Data.rho_lt_rootHi_loose` bounds the gap the other way, at 10⁻¹¹. -/
theorem rootHi_lt_rhoChar : ((rootHi : ℤ) : ℝ) < rhoChar := int_lt_div cden_pos rootHi_lt_rho

/-! ## §6 The capstone, applied — nine of the fourteen supplied

The theorem below IS the composition executed (LEAN.md §3): the kernel checks that the statements
proved above are the ones `Zeta2Instantiate.candidate_rn_growth_of_L1` assumes, at the real
`candidateM.rn`, with no re-statement anywhere.

Of the capstone's fourteen hypotheses it supplies **nine** — `hP₃`, `hd₀`–`hd₂`, `hA₀`–`hA₂`, `hρ`
and `hchar`.  The **five** that remain are `hL` and `h₀`–`h₃`, the recurrence and the clearing
identity, which are B1–B5 and depend on the `αⱼ` the `MBSolveResult.coords` work emits.  In their
place this row asks for eight facts that are strictly smaller and that any construction of the
`cleared_j` from their coefficients produces directly: `natDegree ≤ 510` and `coeff 510 = leadⱼ`.
-/

/-- **X-L1's degree/leading-coefficient half, composed with the landed capstone.** -/
theorem candidate_rn_growth_of_recurrence
    (α₀ α₁ α₂ α₃ : ℕ → ℝ) (P₀ P₁ P₂ P₃ B : ℝ[X]) (N₀ : ℕ)
    (hL : ∀ n : ℕ, N₀ ≤ n → α₀ n * candidateM.rn n + α₁ n * candidateM.rn (n + 1)
      + α₂ n * candidateM.rn (n + 2) + α₃ n * candidateM.rn (n + 3) = 0)
    (h₀ : ∀ n : ℕ, N₀ ≤ n → P₀.eval (n : ℝ) = B.eval (n : ℝ) * α₀ n)
    (h₁ : ∀ n : ℕ, N₀ ≤ n → P₁.eval (n : ℝ) = B.eval (n : ℝ) * α₁ n)
    (h₂ : ∀ n : ℕ, N₀ ≤ n → P₂.eval (n : ℝ) = B.eval (n : ℝ) * α₂ n)
    (h₃ : ∀ n : ℕ, N₀ ≤ n → P₃.eval (n : ℝ) = B.eval (n : ℝ) * α₃ n)
    (hn₀ : P₀.natDegree ≤ dcl) (hk₀ : P₀.coeff dcl = ((lead0 : ℤ) : ℝ))
    (hn₁ : P₁.natDegree ≤ dcl) (hk₁ : P₁.coeff dcl = ((lead1 : ℤ) : ℝ))
    (hn₂ : P₂.natDegree ≤ dcl) (hk₂ : P₂.coeff dcl = ((lead2 : ℤ) : ℝ))
    (hn₃ : P₃.natDegree ≤ dcl) (hk₃ : P₃.coeff dcl = ((lead3 : ℤ) : ℝ)) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n, N ≤ n → |candidateM.rn n| ≤ C * rhoChar ^ n := by
  obtain ⟨-, hd₀, hl₀⟩ := degree_lead_of_coeff hn₀ hk₀ lead0_neR
  obtain ⟨-, hd₁, hl₁⟩ := degree_lead_of_coeff hn₁ hk₁ lead1_neR
  obtain ⟨-, hd₂, hl₂⟩ := degree_lead_of_coeff hn₂ hk₂ lead2_neR
  obtain ⟨hP₃, hd₃, hl₃⟩ := degree_lead_of_coeff hn₃ hk₃ lead3_neR
  refine Zeta2Instantiate.candidate_rn_growth_of_L1 α₀ α₁ α₂ α₃ P₀ P₁ P₂ P₃ B N₀
    hL h₀ h₁ h₂ h₃ hP₃ (hd₀.trans hd₃.symm) (hd₁.trans hd₃.symm) (hd₂.trans hd₃.symm)
    ?_ ?_ ?_ rho_pos char_real
  · rw [hl₀, hl₃]; exact hA0
  · rw [hl₁, hl₃]; exact hA1
  · rw [hl₂, hl₃]; exact hA2

/-! ### Receipts (LEAN.md §1 — exit 0 is not an attestation) -/

#print axioms degree_lead_of_coeff
#print axioms rho_pos
#print axioms abs_ratio_lt_of_int
#print axioms lt_of_ratio_exact
#print axioms hA0
#print axioms hA1
#print axioms hA2
#print axioms char_of_cleared
#print axioms char_real
#print axioms hA_admits_a_vanishing_leading_coeff
#print axioms majorant_fails_at_A2
#print axioms one_lt_rhoChar
#print axioms rootHi_lt_rhoChar
#print axioms candidate_rn_growth_of_recurrence

end Zeta2XL1
