/-
# The objects of the proof: `qₙ`, `pₙ` and the linear form `rₙ = qₙ·ζ(2) − pₙ`

The construction is that of W. Zudilin, *Two hypergeometric tales and a new irrationality
measure of ζ(2)*, Ann. Math. Québec 38 (2014), arXiv:1310.1526.  A member of its family is
given by parameters `a = (a₁, a₂, a₃, a₄)` and `b = (b₁, b₂, b₃, b₄)`, linear in `n`; `Member`
records their slopes `α`, `β` (`aⱼ = αⱼn + 1`).  Two members are defined:

* `candidateM`, the member the theorem is about: in the paper's notation
  `a = (13n+1, 11n+1, 9n+1, 15n+1)`, `b = (1, 2n+1, 4n+1, 26n+2)`;
* `recordM`, the paper's own member: `a = (7n+1, 6n+1, 5n+1, 8n+1)`, `b = (1, n+1, 2n+1, 14n+2)`.

For a member the file defines `Π(n)`, the residues `c_k` of the rational function `R_n` at its
simple poles (divided by `Π(n)`), its polynomial part `P`, and from them `qₙ`, `pₙ` and `rₙ`,
using factorials, polynomial division and Bernoulli polynomials over ℚ; no integral appears.

**Both members, one definition.**  The sign of `c_k` is `(−1)^{Dn+k−1}`, where
`D = α₁ + (α₂−β₂) + (α₃−β₃) − α₄` is 12 at the candidate and 7 at the paper's member.  A
simplified sign `(−1)^{k−1}` from this project's early notes is valid when `D` is even: it
agrees with the general sign at the candidate, and at the paper's member it differs from the
paper's correct sign for odd `n`.  Defining both members is what exposes the difference, and
`record_sign_form_disagrees` below states it as a theorem.

**What this file does not claim.**  It proves elementary properties of the objects it defines, no
estimate of `rₙ` and nothing about irrationality; the headline is `Zeta2Target`'s.  `zeta2 := π²/6`
is identified with the series `∑ 1/n²` here (`hasSum_zeta2`) and with `riemannZeta 2` in `Zeta2Final`.

Toolchain `leanprover/lean4:v4.34.0-rc2`; Mathlib at commit `5aedf732`.
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.ZetaValues

namespace Zeta2Defs

open Finset Polynomial

/-! ## The member -/

/-- A member of the family, given by the SLOPES of its parameters.  Its parameters are
`a_j = α_j n + 1` and `b = (β₁n+1, β₂n+1, β₃n+1, β₄n+2)` with `β₁ = 0`, which this structure
fixes, so the four `α` slopes and three nonzero `β` slopes determine the member.  These `a` and
`b` are the parameters of the construction in the notation of Zudilin's paper. -/
structure Member where
  /-- `α₁` — the slope of the first numerator Γ. -/
  a1 : ℕ
  /-- `α₂`. -/
  a2 : ℕ
  /-- `α₃`. -/
  a3 : ℕ
  /-- `α₄` — the slope whose Pochhammer block the denominator starts at. -/
  a4 : ℕ
  /-- `β₂`. -/
  b2 : ℕ
  /-- `β₃` — also sets `C = −β₃n − 1/2` and its cell `⌊C⌋ = −β₃n − 1` (`Member.cell`). -/
  b3 : ℕ
  /-- `β₄` — the slope where the pole window ends. -/
  b4 : ℕ
  deriving DecidableEq, Repr

/-- The CANDIDATE `(13,11,9,15;26)`, the member the μ ≤ 5.0495243 bound is about. -/
def candidateM : Member := ⟨13, 11, 9, 15, 2, 4, 26⟩

/-- The RECORD `(7,6,5,8;14)`, the member of Zudilin's paper: `a = (7n+1, 6n+1, 5n+1, 8n+1)`,
`b = (1, n+1, 2n+1, 14n+2)`.  It is carried because its sign depends on the parity of `n`. -/
def recordM : Member := ⟨7, 6, 5, 8, 1, 2, 14⟩

/-- The inequalities the closed form needs in order to mean what it says.  Every one of them
is a statement that some ℕ subtraction below does not truncate; they are collected here rather
than repeated because a missing one does not produce an error, it produces a junk value
(`ck_outside_window_is_junk`). -/
structure Member.WF (m : Member) : Prop where
  /-- `β₂ < α₂` — the second numerator block is nonempty. -/
  b2_lt : m.b2 < m.a2
  /-- `β₃ < α₃` — the third numerator block is nonempty. -/
  b3_lt : m.b3 < m.a3
  /-- `α₄ < β₄` — the pole window is nonempty. -/
  a4_lt : m.a4 < m.b4
  /-- `α₁ ≤ α₄`. -/
  a1_le : m.a1 ≤ m.a4
  /-- `α₂ ≤ α₄`. -/
  a2_le : m.a2 ≤ m.a4
  /-- `α₃ ≤ α₄`. -/
  a3_le : m.a3 ≤ m.a4
  /-- `β₂ ≤ α₄`. -/
  b2_le : m.b2 ≤ m.a4
  /-- `β₃ ≤ α₄`. -/
  b3_le : m.b3 ≤ m.a4
  /-- `α₄` does not exceed the numerator's total degree slope, so `Dpar` does not truncate. -/
  a4_le_deg : m.a4 ≤ m.a1 + (m.a2 - m.b2) + (m.a3 - m.b3)
  /-- `Σβ ≤ Σα`, so `dsum` does not truncate. -/
  b_le : m.b2 + m.b3 + m.b4 ≤ m.a1 + m.a2 + m.a3 + m.a4

theorem candidateM_wf : candidateM.WF := by constructor <;> decide

theorem recordM_wf : recordM.WF := by constructor <;> decide

/-! ## `Pin` — the factorial prefactor `Π(n)` -/

/-- **`Pin`** — `Π(n) = ((β₄−α₄)n)! / ((α₁n)! ((α₂−β₂)n)! ((α₃−β₃)n)!)`, the prefactor of
the residues of `R_n`.  At the candidate this is `(11n)!/((13n)!(9n)!(5n)!)`. -/
def Member.Pin (m : Member) (n : ℕ) : ℚ :=
  ((Nat.factorial ((m.b4 - m.a4) * n) : ℕ) : ℚ) /
    ((Nat.factorial (m.a1 * n) * Nat.factorial ((m.a2 - m.b2) * n)
      * Nat.factorial ((m.a3 - m.b3) * n) : ℕ) : ℚ)

/-! ## `window` — the pole window -/

/-- **The pole window** `k ∈ [α₄n+1, β₄n+1]`.  `R_n`'s poles are simple and sit exactly at
`t = −k` for `k` here — the denominator Pochhammer is `(t+α₄n+1)_{(β₄−α₄)n+1}`. -/
def Member.window (m : Member) (n : ℕ) : Finset ℕ := Finset.Icc (m.a4 * n + 1) (m.b4 * n + 1)

/-! ## `ck` — the factorial closed form of the residues -/

/-- `D = α₁ + (α₂−β₂) + (α₃−β₃) − α₄`: the numerator Pochhammers' total length minus the
denominator's left endpoint.  `D = 12` at the candidate, `D = 7` at the record. -/
def Member.Dpar (m : Member) : ℕ := m.a1 + (m.a2 - m.b2) + (m.a3 - m.b3) - m.a4

/-- `Σα − Σβ`, the slope in `n` of the exponent `d` of the overall sign `sgn`. -/
def Member.dsum (m : Member) : ℕ := m.a1 + m.a2 + m.a3 + m.a4 - (m.b2 + m.b3 + m.b4)

/-- **`sgn`** — the overall sign `(−1)^d` of the linear form, `d = Σ_j a_j − Σ_j b_j = (Σα−Σβ)n − 1`.
`sgn n = +1` iff `d` is even, which is `(−1)^((Σα−Σβ)n + 1)`.
Constant `−1` at the candidate; genuinely `n`-dependent at the record. -/
def Member.sgn (m : Member) (n : ℕ) : ℚ := (-1) ^ (m.dsum * n + 1)

/-- The unsigned part of `ck` — a ratio of factorials, hence strictly positive whatever the
arguments (`ckAbs_pos`).  Splitting the sign off is what makes the alternation and the sign
theorems below statable as theorems rather than as comments. -/
def Member.ckAbs (m : Member) (n k : ℕ) : ℚ :=
  ((Nat.factorial (k - 1) * Nat.factorial (k - m.b2 * n - 1)
      * Nat.factorial (k - m.b3 * n - 1) : ℕ) : ℚ) /
    ((Nat.factorial (k - m.a1 * n - 1) * Nat.factorial (k - m.a2 * n - 1)
      * Nat.factorial (k - m.a3 * n - 1) * Nat.factorial (k - m.a4 * n - 1)
      * Nat.factorial (m.b4 * n + 1 - k) : ℕ) : ℚ)

/-- **`ck`** — the residue of `R_n` at the simple pole `t = −k`, divided by `Pin n`.  The residue
itself is

`C_k = Π(n)·(−1)^{Dn+k−1}·(k−1)!(k−β₂n−1)!(k−β₃n−1)! / [(k−α₁n−1)!(k−α₂n−1)!(k−α₃n−1)!(k−α₄n−1)!(β₄n+1−k)!]`

**The exponent is `Dn + k − 1`, the GENERAL form.**  The simplified `(−1)^{k−1}` of this
project's early notes is its `D` even specialisation: it agrees at the candidate and is wrong at
the paper's member for odd `n` (`sign_form_agrees_of_even`, `record_sign_form_disagrees`). -/
def Member.ck (m : Member) (n k : ℕ) : ℚ :=
  (-1) ^ (m.Dpar * n + k - 1) * m.ckAbs n k

/-! ## `qn` — the ζ(2) coordinate -/

/-- **`qn`** — `q_n = sgn·Π·Σ_{k ∈ window} c_k`.  This is the coefficient of ζ(2) in the
linear form, taken in a formal ζ-basis: no irrationality input is used to isolate it.
-/
def Member.qn (m : Member) (n : ℕ) : ℚ :=
  m.sgn n * m.Pin n * ∑ k ∈ m.window n, m.ck n k

/-! ## `Ppol` — the polynomial part -/

/-- One integer-node Pochhammer block `(t+c)(t+c+1)⋯(t+c+len−1)`.  Equal to
`(ascPochhammer ℚ len).comp (X + C c)`; written out because every degree lemma below then
comes straight from `natDegree_prod`. -/
noncomputable def block (c len : ℕ) : Polynomial ℚ :=
  ∏ i ∈ range len, (X + C ((c + i : ℕ) : ℚ))

/-- The numerator of `R_n/Π(n)`: three integer-node Pochhammer blocks, of total degree
`(α₁ + (α₂−β₂) + (α₃−β₃))n` — `27n` at the candidate. -/
noncomputable def Member.numPoly (m : Member) (n : ℕ) : Polynomial ℚ :=
  block 1 (m.a1 * n) * block (m.b2 * n + 1) ((m.a2 - m.b2) * n)
    * block (m.b3 * n + 1) ((m.a3 - m.b3) * n)

/-- The denominator of `R_n/Π(n)`: the single block `(t+α₄n+1)_{(β₄−α₄)n+1}`, MONIC — which
is what makes `/ₘ` the right division (`denPoly_monic`). -/
noncomputable def Member.denPoly (m : Member) (n : ℕ) : Polynomial ℚ :=
  block (m.a4 * n + 1) ((m.b4 - m.a4) * n + 1)

/-- **`Ppol`** — the polynomial part `P(t) = num div den` of `R_n/Π(n)`, of degree `16n−1` at the
candidate (`Ppol_natDegree`). -/
noncomputable def Member.Ppol (m : Member) (n : ℕ) : Polynomial ℚ :=
  m.numPoly n /ₘ m.denPoly n

/-! ## `pn` — the rational coordinate -/

/-- **The moments, as Bernoulli polynomials.**  `momI M j = I_j(C)` is the moment of the cell
`M = ⌊C⌋`, and `Zeta2Moments.momI_eq_bernoulli` proves that the moments' defining four-line
recursion equals `(Polynomial.bernoulli j).eval (M+1)`.  So this is not a second definition of
`I` — it is that theorem's conclusion, taken as the definition, which keeps the whole
`Polynomial.bernoulli` API. -/
noncomputable def momI (M : ℤ) (j : ℕ) : ℚ := (Polynomial.bernoulli j).eval ((M : ℚ) + 1)

/-- `⌊C⌋` for `C = −β₃n − 1/2`, so the cell is
`−β₃n − 1`. -/
def Member.cell (m : Member) (n : ℕ) : ℤ := -(m.b3 * n : ℤ) - 1

/-- The truncated `s`-th order harmonic number `H^{(s)}_k`.  Same definition as
`Zeta2Moments.harm`; repeated here rather than imported, so that this file imports no other
module of the proof. -/
def harm (s k : ℕ) : ℚ := ∑ i ∈ range k, 1 / ((i : ℚ) + 1) ^ s

/-- The index `k + ⌊C⌋ = k − β₃n − 1` at which the harmonic sum `H^{(2)}` in `pnHarm` is
truncated. -/
def Member.harmIndex (m : Member) (n k : ℕ) : ℕ := k - m.b3 * n - 1

/-- `Σ_k c_k H^{(2)}_{k+⌊C⌋}` — the half of `pn` that lives in the ARITHMETIC layer, and is
therefore computable: it can be `#eval`'d. -/
def Member.pnHarm (m : Member) (n : ℕ) : ℚ :=
  ∑ k ∈ m.window n, m.ck n k * harm 2 (m.harmIndex n k)

/-- `Σ_j P_j I_j(C)` — the half of `pn` that lives in the POLYNOMIAL layer.  `Polynomial ℚ` is
noncomputable in Mathlib, so unlike `pnHarm` this cannot be `#eval`'d.
-/
noncomputable def Member.pnPoly (m : Member) (n : ℕ) : ℚ :=
  ∑ j ∈ range ((m.Ppol n).natDegree + 1), (m.Ppol n).coeff j * momI (m.cell n) j

/-- **`pn`** — `p_n = −sgn·Π·(Σ_j P_j I_j(C) − Σ_k c_k H^{(2)}_{k+⌊C⌋})`. -/
noncomputable def Member.pn (m : Member) (n : ℕ) : ℚ :=
  -(m.sgn n) * m.Pin n * (m.pnPoly n - m.pnHarm n)

/-! ## `rn` — the linear form -/

/-- `ζ(2) = π²/6`.  Mathlib supplies the identification (`riemannZeta_two`,
`hasSum_zeta_two`). -/
noncomputable def zeta2 : ℝ := Real.pi ^ 2 / 6

/-- **`rn`** — `r_n = q_n ζ(2) − p_n`, the linear form the proof is about: the member's
own linear form, not a sequence assumed to satisfy
hypotheses. -/
noncomputable def Member.rn (m : Member) (n : ℕ) : ℝ :=
  ((m.qn n : ℚ) : ℝ) * zeta2 - ((m.pn n : ℚ) : ℝ)

/-- `zeta2` really is ζ(2) and not just a name for `π²/6`: it is the sum of the series
`∑ 1/n²`, by Mathlib's `hasSum_zeta_two`. -/
theorem hasSum_zeta2 : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) zeta2 := by
  rw [zeta2]
  exact hasSum_zeta_two

/-! ## Positivity and the sign structure -/

theorem Member.ckAbs_pos (m : Member) (n k : ℕ) : 0 < m.ckAbs n k := by
  refine div_pos ?_ ?_ <;>
    exact_mod_cast Nat.pos_of_ne_zero (by positivity)

theorem Member.Pin_pos (m : Member) (n : ℕ) : 0 < m.Pin n := by
  refine div_pos ?_ ?_ <;>
    exact_mod_cast Nat.pos_of_ne_zero (by positivity)

theorem Member.ck_ne_zero (m : Member) (n k : ℕ) : m.ck n k ≠ 0 := by
  have h := m.ckAbs_pos n k
  have hs : ((-1 : ℚ)) ^ (m.Dpar * n + k - 1) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  exact mul_ne_zero hs (ne_of_gt h)

/-- The sign ALTERNATES in `k` — a structural fact of the construction, here as a
theorem.  `1 ≤ k` is the real hypothesis: it is what makes
`Dn + (k+1) − 1` equal to `(Dn + k − 1) + 1` in ℕ. -/
theorem Member.ck_sign_alternates (m : Member) (n k : ℕ) (hk : 1 ≤ k) :
    m.ck n (k + 1) * m.ck n k < 0 := by
  have he : m.Dpar * n + (k + 1) - 1 = (m.Dpar * n + k - 1) + 1 := by omega
  have h1 := m.ckAbs_pos n (k + 1)
  have h2 := m.ckAbs_pos n k
  set e := m.Dpar * n + k - 1
  rw [Member.ck, Member.ck, he, pow_succ]
  have hsq : ((-1 : ℚ)) ^ e * ((-1 : ℚ)) ^ e = 1 := by
    rw [← pow_add, ← two_mul]
    simp [pow_mul]
  nlinarith [mul_pos h1 h2, hsq]

/-! ## The sign of `c_k`, as theorems

A simplified closed form from this project's early notes carried `(−1)^{k−1}`.  That is the
`D n` even specialisation of `(−1)^{Dn+k−1}`.  The theorems below say *when* the two forms
agree, and give a witness that they do not agree in general. -/

/-- The simplified `(−1)^{k−1}` form IS correct whenever `D n` is even — which is why it agrees
with the general form at the candidate (`D = 12`). -/
theorem Member.sign_form_agrees_of_even (m : Member) (n k : ℕ) (hk : 1 ≤ k)
    (h : Even (m.Dpar * n)) : m.ck n k = (-1 : ℚ) ^ (k - 1) * m.ckAbs n k := by
  have he : m.Dpar * n + k - 1 = m.Dpar * n + (k - 1) := by omega
  rw [Member.ck, he, pow_add, h.neg_one_pow, one_mul]

/-- The candidate's `D n` is always even, so on the candidate alone the two forms are
indistinguishable — no amount of candidate-only testing could tell them apart. -/
theorem candidate_Dpar_mul_even (n : ℕ) : Even (candidateM.Dpar * n) := by
  have : candidateM.Dpar = 12 := by decide
  rw [this]
  exact ⟨6 * n, by ring⟩

/-- **The two forms differ at the paper's member.**  At `n = 1`, `k = 9` — the left endpoint of
that window — the general form gives `−ckAbs` and the simplified `(−1)^{k−1}` form gives
`+ckAbs`.  They differ, so the simplified form is refuted at the paper's member; the general
form is the one this file uses. -/
theorem record_sign_form_disagrees :
    recordM.ck 1 9 ≠ (-1 : ℚ) ^ (9 - 1) * recordM.ckAbs 1 9 := by
  have hD : recordM.Dpar * 1 + 9 - 1 = 15 := by decide
  have hpos := recordM.ckAbs_pos 1 9
  rw [Member.ck, hD]
  norm_num
  linarith

/-- And the exponent that makes it disagree is exactly the `D n` parity: `D = 7` at the
record, so `D n` is odd at odd `n`. -/
theorem record_Dpar_mul_odd : ¬ Even (recordM.Dpar * 1) := by decide

/-! ## Degrees of the polynomial half -/

theorem block_monic (c len : ℕ) : (block c len).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem block_natDegree (c len : ℕ) : (block c len).natDegree = len := by
  rw [block, natDegree_prod _ _ fun i _ => (monic_X_add_C ((c + i : ℕ) : ℚ)).ne_zero]
  simp only [natDegree_X_add_C]
  simp

theorem Member.denPoly_monic (m : Member) (n : ℕ) : (m.denPoly n).Monic :=
  block_monic _ _

theorem Member.denPoly_natDegree (m : Member) (n : ℕ) :
    (m.denPoly n).natDegree = (m.b4 - m.a4) * n + 1 :=
  block_natDegree _ _

theorem Member.numPoly_monic (m : Member) (n : ℕ) : (m.numPoly n).Monic :=
  ((block_monic _ _).mul (block_monic _ _)).mul (block_monic _ _)

theorem Member.numPoly_natDegree (m : Member) (n : ℕ) :
    (m.numPoly n).natDegree = m.a1 * n + (m.a2 - m.b2) * n + (m.a3 - m.b3) * n := by
  have h1 := block_monic 1 (m.a1 * n)
  have h2 := block_monic (m.b2 * n + 1) ((m.a2 - m.b2) * n)
  have h3 := block_monic (m.b3 * n + 1) ((m.a3 - m.b3) * n)
  rw [Member.numPoly, (h1.mul h2).natDegree_mul h3, h1.natDegree_mul h2,
    block_natDegree, block_natDegree, block_natDegree]

/-- The pole window has `(β₄−α₄)n + 1` members — the `11n+1` simple poles at the candidate. -/
theorem Member.window_card (m : Member) (hm : m.WF) (n : ℕ) :
    (m.window n).card = (m.b4 - m.a4) * n + 1 := by
  have hle : m.a4 * n ≤ m.b4 * n := Nat.mul_le_mul_right _ hm.a4_lt.le
  have hsub : (m.b4 - m.a4) * n = m.b4 * n - m.a4 * n := Nat.sub_mul _ _ _
  rw [Member.window, Nat.card_Icc, hsub]
  omega

/-- **`P(t)` has degree `16n−1`** at the candidate, derived here rather than asserted:
`27n − (11n+1)`. -/
theorem Member.Ppol_natDegree (m : Member) (n : ℕ) :
    (m.Ppol n).natDegree
      = (m.a1 * n + (m.a2 - m.b2) * n + (m.a3 - m.b3) * n) - ((m.b4 - m.a4) * n + 1) := by
  rw [Member.Ppol, natDegree_divByMonic _ (m.denPoly_monic n), m.numPoly_natDegree n,
    m.denPoly_natDegree n]

/-- The candidate specialisation, spelled out. -/
theorem candidate_Ppol_natDegree (n : ℕ) :
    (candidateM.Ppol n).natDegree = 27 * n - (11 * n + 1) := by
  have h := candidateM.Ppol_natDegree n
  simp only [candidateM] at h ⊢
  rw [h]
  omega

/-- The defining property of `Ppol`, free from `modByMonic_add_div`: `num = rem + den · P`.
This is the only thing any consumer of `Ppol` needs.  `denPoly` being MONIC is what makes it
say something: for a non-monic divisor Mathlib's `/ₘ` returns `0` and `%ₘ` returns `p`, so the
identity is true and empty — which is why the denominator is written that way round, and why
`denPoly_monic` is a separate theorem rather than a remark. -/
theorem Member.Ppol_spec (m : Member) (n : ℕ) :
    m.numPoly n %ₘ m.denPoly n + m.denPoly n * m.Ppol n = m.numPoly n :=
  modByMonic_add_div (m.numPoly n) (m.denPoly n)

/-! ## Edges — `n = 0`, the window endpoints, and the ℕ-truncation traps -/

/-- At `n = 0` the window collapses to the single pole `k = 1`. -/
theorem Member.window_zero (m : Member) : m.window 0 = {1} := by
  simp [Member.window]

/-- `Π(0) = 1`. -/
theorem Member.Pin_zero (m : Member) : m.Pin 0 = 1 := by
  simp [Member.Pin]

/-- `c_1(0) = 1`: every factorial in the closed form is `0!` at `n = 0`, `k = 1`. -/
theorem Member.ck_zero (m : Member) : m.ck 0 1 = 1 := by
  simp [Member.ck, Member.ckAbs, Member.Dpar]

/-- **`q_0 = −1` for EVERY member** — the closed form extends to `n = 0`: the window is the single
pole `k = 1`, `Π(0) = 1` and `c_1(0) = 1`, so `q_0 = sgn(0) = −1`.
-/
theorem Member.qn_zero (m : Member) : m.qn 0 = -1 := by
  rw [Member.qn, m.window_zero, m.Pin_zero, Finset.sum_singleton, m.ck_zero]
  simp [Member.sgn]

/-- Inside the window every ℕ subtraction in `ckAbs` is a genuine subtraction — stated as the
exact identities, so a caller can rewrite with them.  Outside it they truncate silently
(`ck_outside_window_is_junk`), which is why `qn`/`pnHarm` sum over `window` and not over a
range. -/
theorem Member.ck_subtractions_exact (m : Member) (hm : m.WF) (n k : ℕ)
    (hk : k ∈ m.window n) :
    (k - 1) + 1 = k ∧
    (k - m.b2 * n - 1) + (m.b2 * n + 1) = k ∧
    (k - m.b3 * n - 1) + (m.b3 * n + 1) = k ∧
    (k - m.a1 * n - 1) + (m.a1 * n + 1) = k ∧
    (k - m.a2 * n - 1) + (m.a2 * n + 1) = k ∧
    (k - m.a3 * n - 1) + (m.a3 * n + 1) = k ∧
    (k - m.a4 * n - 1) + (m.a4 * n + 1) = k ∧
    (m.b4 * n + 1 - k) + k = m.b4 * n + 1 := by
  rw [Member.window, Finset.mem_Icc] at hk
  have h1 : m.a1 * n ≤ m.a4 * n := Nat.mul_le_mul_right _ hm.a1_le
  have h2 : m.a2 * n ≤ m.a4 * n := Nat.mul_le_mul_right _ hm.a2_le
  have h3 : m.a3 * n ≤ m.a4 * n := Nat.mul_le_mul_right _ hm.a3_le
  have h4 : m.b2 * n ≤ m.a4 * n := Nat.mul_le_mul_right _ hm.b2_le
  have h5 : m.b3 * n ≤ m.a4 * n := Nat.mul_le_mul_right _ hm.b3_le
  omega

/-- The harmonic index is a genuine subtraction on the window too, so the harmonic sum in
`pnHarm` is truncated at `k + ⌊C⌋` and not at `0`. -/
theorem Member.harmIndex_exact (m : Member) (hm : m.WF) (n k : ℕ) (hk : k ∈ m.window n) :
    m.harmIndex n k + (m.b3 * n + 1) = k := by
  rw [Member.window, Finset.mem_Icc] at hk
  have h5 : m.b3 * n ≤ m.a4 * n := Nat.mul_le_mul_right _ hm.b3_le
  rw [Member.harmIndex]
  omega

/-- **The ℕ-truncation trap, committed as a theorem so nobody "simplifies" the window away.**

`Wone_shift`'s `1 ≤ k` in `Zeta2Moments.lean` is mathematically necessary but Lean-VACUOUS,
because `0 − 1 = 0` in ℕ.  The same shape is here and it is worse, because it is not vacuous:
outside the window `ck` takes a junk value.  At `k = 8`, one below `recordM`'s window at `n = 1`,
the subtraction `k − α₄n − 1` truncates to `0`, so `ck` has a finite nonzero value at a `k` that
is not a pole of `R_n` at all.  A lemma about `ck` quantified over `k : ℕ` rather than over
`m.window n` would therefore be about junk values and still elaborate. -/
theorem ck_outside_window_is_junk :
    8 ∉ recordM.window 1 ∧ (8 - recordM.a4 * 1 - 1 : ℕ) = 0 ∧ recordM.ck 1 8 ≠ 0 := by
  refine ⟨?_, by decide, recordM.ck_ne_zero 1 8⟩
  decide

/-- The second truncation site, and the reason `ck_sign_alternates` carries `1 ≤ k`: at
`k = 0` the sign EXPONENT truncates, so `ck` reports the sign belonging to `k = 1`.  Recorded
at the record member, `n = 0`, where `Dn = 0` makes it visible. -/
theorem ck_exponent_truncates_at_zero :
    (recordM.Dpar * 0 + 0 - 1 : ℕ) = (recordM.Dpar * 0 + 1 - 1 : ℕ) := by decide

/-! ## Receipts (an exit code of 0 is not an attestation)

Every `#print axioms` below must read `[propext, Classical.choice, Quot.sound]` or a subset.
`sorryAx` must appear nowhere.
-/

#print axioms candidateM_wf
#print axioms recordM_wf
#print axioms hasSum_zeta2
#print axioms Member.ckAbs_pos
#print axioms Member.Pin_pos
#print axioms Member.ck_ne_zero
#print axioms Member.ck_sign_alternates
#print axioms Member.sign_form_agrees_of_even
#print axioms candidate_Dpar_mul_even
#print axioms record_sign_form_disagrees
#print axioms record_Dpar_mul_odd
#print axioms block_monic
#print axioms block_natDegree
#print axioms Member.denPoly_monic
#print axioms Member.denPoly_natDegree
#print axioms Member.numPoly_monic
#print axioms Member.numPoly_natDegree
#print axioms Member.window_card
#print axioms Member.Ppol_natDegree
#print axioms candidate_Ppol_natDegree
#print axioms Member.Ppol_spec
#print axioms Member.window_zero
#print axioms Member.Pin_zero
#print axioms Member.ck_zero
#print axioms Member.qn_zero
#print axioms Member.ck_subtractions_exact
#print axioms Member.harmIndex_exact
#print axioms ck_outside_window_is_junk
#print axioms ck_exponent_truncates_at_zero

end Zeta2Defs
