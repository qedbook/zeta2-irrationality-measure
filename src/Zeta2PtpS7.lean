/-
# Row PT-P, layer 7 — the run congruence on the ONE φ̃ = 1 run-carrying stratum `[3/13, 4/17)`,
# and piece 7 of the profile (`[1/5, 4/17)`, `φ̃ = 1`) closed for the harmonic side

`Zeta2PtpBlock` reduced `AHalfOpen` to one divisibility per `(n, p, t)`,
`p^φ̃ ∣ blockSum n p t`, and proved the toolkit: Lucas per factor (`lucas_factor`), Wilson's
reflection (`signChoose_eq`), the period sum (`dvd_sum_of_poly`).  This file spends them on the
stratum `3/13 ≤ r/p < 4/17`, `r = n mod p`, the only run-carrying stratum with `φ̃ = 1`
(`ptp_mechanism_probe.out`: cells `(3,13)`, `(10,43)`, `(11,47)`, … all `φ̃ = 1`, all in
`[3/13, 4/17)`), and then dispatches the whole of profile piece 7 `[1/5, 4/17)`: its other three
strata `[1/5, 2/9)`, `[2/9, 5/22)`, `[5/22, 3/13)` are `Zeta2PtpCong`'s run-free `S2/S3/S4`.

THE MECHANISM, on this stratum.  With `n = p·n₁ + r` the six floors are fixed —
`⌊2x⌋ = ⌊4x⌋ = 0`, `⌊5x⌋ = ⌊7x⌋ = 1`, `⌊9x⌋ = ⌊11x⌋ = 2`, `⌊13x⌋ = 3`, `⌊22x⌋ = 5` — so the
four binomials' digits are affine in `(r, p, u, t, n₁)`:

    a = 13r − 3p,  b = 9r − 2p,  c = 5r − p,  e = 11r − 2p,      13n = a + (13n₁+3)·p, …

For `u ≥ e` (with `t ≥ E₁ := 11n₁ + 2`, the first block of the window) every one of the four
Lucas decompositions has a `u`-independent top digit — `u + 4r ≥ p` and `u + 2r ≥ p` hold
because `e ≥ p − 2r ⟺ 13r ≥ 3p` — and the signed term is EXACTLY

    (−1)^{t+e} · C(t+4n₁+1, 13n₁+3) · C(t+2n₁+1, 9n₁+2) · C(t, 5n₁+1) · C(E₁, t−E₁)   [κ_t]
      · binPoly a (u+4r) · binPoly b (u+2r) · binPoly c (u) · signChoosePoly e (u−e)     [Π(u)]

with `deg Π ≤ a + b + c + (p−1−e) = 16r − 3p − 1 ≤ p − 2  ⟺  16r < 4p`, true on the stratum.
For `u < e` both the term and `Π(u)` vanish: below `c` through the third binomial, and on
`[c, e)` through the fourth, whose lower argument wraps to `u + p − e > e` because
`c > 2e − p ⟺ 17r < 4p` — the stratum's own upper endpoint, which is why `[3/13, 4/17)` and
not `[3/13, 1/4)` is the stratum.  An off-window `u` on the last block has `C(E₁, t−E₁) = 0`
inside `κ_t`; an off-window `u` on the first block is `u < e`.  So on EVERY block
`Σ_{u<p} term(u) ≡ κ_t · Σ_{u<p} Π(u) ≡ 0 (mod p)`, which is `p ∣ blockSum`.

The identity is UNCONDITIONAL in `u ≥ e`: Lucas needs no carry case, since a carrying binomial
is `0` on both sides.  The run `[⟨7r⟩, p−1]` is never named — it is only where `Π` is nonzero.

WHAT THIS DOES NOT DO.  The φ̃ = 2 run strata (four profile pieces, seven refined strata) need
the ONE-carry unit part (Anton's congruence, absent from Mathlib) and are not here;
`Zeta2PtpPolar.PolyHalfOpen` is untouched; PT-P stays OPEN and
`Zeta2Target.zeta2_not_liouvilleWith` stays `sorry`.

Falsifier: `falsify_ptps7.sh` / `out_ptps7_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2Profile
import Zeta2PhiT
import Zeta2PtpPolar
import Zeta2PtpRun
import Zeta2PtpStratum
import Zeta2PtpCong
import Zeta2PtpBlock
import Zeta2CarryFull

set_option maxRecDepth 20000

namespace Zeta2PtpS7

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpPolar Zeta2PtpBlock Nat Finset Polynomial

/-! ## 1. Digits from an affine decomposition, and casts to `ZMod p` -/

/-- `a = rem + q·p` with `rem < p` pins both digits.  (Named past `Nat.digits`, which `open Nat`
brings into scope — a bare `digits` here would be an overload.) -/
theorem digits_of_decomp {p a q rem : ℕ} (hp : 0 < p) (h : a = rem + q * p) (hrem : rem < p) :
    a / p = q ∧ a % p = rem := by
  subst h
  exact ⟨by rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hrem, zero_add],
    by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem]⟩

theorem cast_of_decomp {p a q rem : ℕ} (h : a = rem + q * p) : (a : ZMod p) = (rem : ZMod p) := by
  subst h
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- Lucas in the raw two-binomial form (for the fourth factor, whose sign goes through
`signChoose_eq` rather than through `binPoly`). -/
theorem lucas_raw {p : ℕ} [Fact p.Prime] (S A : ℕ) :
    ((S.choose A : ℕ) : ZMod p)
      = (((S % p).choose (A % p) : ℕ) : ZMod p) * (((S / p).choose (A / p) : ℕ) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := S) (k := A)
  rw [← ZMod.natCast_eq_natCast_iff] at h
  rw [h, Nat.cast_mul]

/-! ## 2. The polynomial and the block constant -/

/-- `Π(u)` on the stratum: the three uncarried units digits and the reflected fourth. -/
noncomputable def runPoly (p r : ℕ) : (ZMod p)[X] :=
  (binPoly p (13 * r - 3 * p)).comp (X + C ((4 * r : ℕ) : ZMod p))
    * (binPoly p (9 * r - 2 * p)).comp (X + C ((2 * r : ℕ) : ZMod p))
    * binPoly p (5 * r - p)
    * (signChoosePoly p (11 * r - 2 * p)).comp (X - C ((11 * r - 2 * p : ℕ) : ZMod p))

/-- `κ_t`: the sign and the four top-digit binomials, `u`-free. -/
def kappa (p n₁ r t : ℕ) : ZMod p :=
  (-1) ^ t * (-1) ^ (11 * r - 2 * p)
    * (((t + 4 * n₁ + 1).choose (13 * n₁ + 3) : ℕ) : ZMod p)
    * (((t + 2 * n₁ + 1).choose (9 * n₁ + 2) : ℕ) : ZMod p)
    * ((t.choose (5 * n₁ + 1) : ℕ) : ZMod p)
    * (((11 * n₁ + 2).choose (t - (11 * n₁ + 2)) : ℕ) : ZMod p)

theorem runPoly_natDegree_le {p r : ℕ} [Fact p.Prime] (h1 : 3 * p ≤ 13 * r) (h2 : 17 * r < 4 * p) :
    (runPoly p r).natDegree ≤ p - 2 := by
  unfold runPoly
  have hA : ((binPoly p (13 * r - 3 * p)).comp (X + C ((4 * r : ℕ) : ZMod p))).natDegree
      ≤ 13 * r - 3 * p := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact binPoly_natDegree_le _
  have hB : ((binPoly p (9 * r - 2 * p)).comp (X + C ((2 * r : ℕ) : ZMod p))).natDegree
      ≤ 9 * r - 2 * p := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact binPoly_natDegree_le _
  have hC : (binPoly p (5 * r - p)).natDegree ≤ 5 * r - p := binPoly_natDegree_le _
  have hD : ((signChoosePoly p (11 * r - 2 * p)).comp
      (X - C ((11 * r - 2 * p : ℕ) : ZMod p))).natDegree ≤ p - 1 - (11 * r - 2 * p) := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_sub_C, mul_one]
    exact signChoosePoly_natDegree_le _
  -- fully qualified: bare `natDegree_mul_le` is an overload under this file's `open`s (measured,
  -- `out_axioms_ptps7.txt`'s first draft: `124:34 overloaded, errors`).
  refine (Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le hA hB) hC) hD).trans ?_
  omega

/-! ## 3. The identity for `u ≥ e`, on every block from the first -/

/-- **The term IS `κ_t · Π(u)` for `u ≥ e`** — Lucas on all four factors, no carry case. -/
theorem term_eq_of_ge {p : ℕ} [hp : Fact p.Prime] {n n₁ r t' u : ℕ}
    (hn : n = p * n₁ + r) (hr : r < p) (h1 : 3 * p ≤ 13 * r) (h2 : 17 * r < 4 * p)
    (hu : u < p) (hue : 11 * r - 2 * p ≤ u) :
    (((-1 : ℤ) ^ (12 * n + ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1) - 1)
        * (cTerm n ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1) : ℤ) : ℤ) : ZMod p)
      = kappa p n₁ r (t' + (11 * n₁ + 2)) * (runPoly p r).eval (u : ZMod p) := by
  have hp0 := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  -- the four arguments of `cTerm`, and the four lower arguments, as affine decompositions
  -- `k − 1` is stated as `k' := t·p + u + 4n` (not `… + 1 − 1`): the assembly below cancels the
  -- `+ 1 − 1` first, and `push_cast` would do so anyway (measured: draft 2's `213:13`).
  have hk1 : (t' + (11 * n₁ + 2)) * p + u + 4 * n
      = (u + 4 * r - p) + (t' + (11 * n₁ + 2) + 4 * n₁ + 1) * p := by
    have e : (t' + (11 * n₁ + 2) + 4 * n₁ + 1) * p
        = t' * p + 11 * (p * n₁) + 2 * p + 4 * (p * n₁) + p := by ring
    have e' : (t' + (11 * n₁ + 2)) * p = t' * p + 11 * (p * n₁) + 2 * p := by ring
    omega
  have hk2 : (t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 - 2 * n - 1
      = (u + 2 * r - p) + (t' + (11 * n₁ + 2) + 2 * n₁ + 1) * p := by
    have e : (t' + (11 * n₁ + 2) + 2 * n₁ + 1) * p
        = t' * p + 11 * (p * n₁) + 2 * p + 2 * (p * n₁) + p := by ring
    have e' : (t' + (11 * n₁ + 2)) * p = t' * p + 11 * (p * n₁) + 2 * p := by ring
    omega
  have hk3 : (t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 - 4 * n - 1
      = u + (t' + (11 * n₁ + 2)) * p := by omega
  have hk4 : (t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 - 15 * n - 1
      = (u - (11 * r - 2 * p)) + t' * p := by
    have e' : (t' + (11 * n₁ + 2)) * p = t' * p + 11 * (p * n₁) + 2 * p := by ring
    omega
  have h13 : 13 * n = (13 * r - 3 * p) + (13 * n₁ + 3) * p := by
    have e : (13 * n₁ + 3) * p = 13 * (p * n₁) + 3 * p := by ring
    omega
  have h9 : 9 * n = (9 * r - 2 * p) + (9 * n₁ + 2) * p := by
    have e : (9 * n₁ + 2) * p = 9 * (p * n₁) + 2 * p := by ring
    omega
  have h5 : 5 * n = (5 * r - p) + (5 * n₁ + 1) * p := by
    have e : (5 * n₁ + 1) * p = 5 * (p * n₁) + p := by ring
    omega
  have h11 : 11 * n = (11 * r - 2 * p) + (11 * n₁ + 2) * p := by
    have e : (11 * n₁ + 2) * p = 11 * (p * n₁) + 2 * p := by ring
    omega
  -- digits
  obtain ⟨d1q, d1r⟩ := digits_of_decomp hp0 hk1 (by omega)
  obtain ⟨d2q, d2r⟩ := digits_of_decomp hp0 hk2 (by omega)
  obtain ⟨d3q, d3r⟩ := digits_of_decomp hp0 hk3 hu
  obtain ⟨d4q, d4r⟩ := digits_of_decomp hp0 hk4 (by omega)
  obtain ⟨a13q, a13r⟩ := digits_of_decomp hp0 h13 (by omega)
  obtain ⟨a9q, a9r⟩ := digits_of_decomp hp0 h9 (by omega)
  obtain ⟨a5q, a5r⟩ := digits_of_decomp hp0 h5 (by omega)
  obtain ⟨a11q, a11r⟩ := digits_of_decomp hp0 h11 (by omega)
  -- the residue classes of the three top arguments
  have c1 : (((t' + (11 * n₁ + 2)) * p + u + 4 * n : ℕ) : ZMod p)
      = (u : ZMod p) + ((4 * r : ℕ) : ZMod p) := by
    rw [cast_of_decomp hk1, Nat.cast_sub (show p ≤ u + 4 * r by omega)]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have c2 : (((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 - 2 * n - 1 : ℕ) : ZMod p)
      = (u : ZMod p) + ((2 * r : ℕ) : ZMod p) := by
    rw [cast_of_decomp hk2, Nat.cast_sub (show p ≤ u + 2 * r by omega)]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have c3 : (((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 - 4 * n - 1 : ℕ) : ZMod p)
      = (u : ZMod p) := cast_of_decomp hk3
  -- the sign
  have hsign : (-1 : ZMod p) ^ (12 * n + ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1) - 1)
      = (-1) ^ (t' + (11 * n₁ + 2)) * ((-1) ^ (11 * r - 2 * p) * (-1) ^ (u - (11 * r - 2 * p))) := by
    have e : 12 * n + ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1) - 1
        = 2 * (8 * n) + (t' + (11 * n₁ + 2)) * p + ((11 * r - 2 * p) + (u - (11 * r - 2 * p))) := by
      omega
    -- `pow_mul'` with its arguments spelled out: bare, `rw` re-split the `((−1)²)^{8n}` factor it
    -- had just made and never reached `(−1)^{t·p}` (measured, draft 2's `203:78`).
    have hp1 : (-1 : ZMod p) ^ ((t' + (11 * n₁ + 2)) * p) = (-1) ^ (t' + (11 * n₁ + 2)) := by
      rw [pow_mul' (-1 : ZMod p) (t' + (11 * n₁ + 2)) p, hodd.neg_one_pow]
    have hp2 : (-1 : ZMod p) ^ (2 * (8 * n)) = 1 := by
      rw [pow_mul (-1 : ZMod p) 2 (8 * n), neg_one_sq, one_pow]
    rw [e, pow_add, pow_add, pow_add, hp1, hp2]
    ring
  -- the fourth factor through the reflection
  have hsc := signChoose_eq (p := p) (11 * r - 2 * p) (u - (11 * r - 2 * p)) (by omega) (by omega)
  have c4 : ((u - (11 * r - 2 * p) : ℕ) : ZMod p)
      = (u : ZMod p) - ((11 * r - 2 * p : ℕ) : ZMod p) := Nat.cast_sub hue
  rw [c4] at hsc
  -- assemble
  rw [cTerm, Nat.add_sub_cancel (n := (t' + (11 * n₁ + 2)) * p + u + 4 * n) (m := 1)]
  push_cast
  rw [hsign, lucas_factor ((t' + (11 * n₁ + 2)) * p + u + 4 * n) (13 * n),
    lucas_factor ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 - 2 * n - 1) (9 * n),
    lucas_factor ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 - 4 * n - 1) (5 * n),
    lucas_raw (11 * n) ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 - 15 * n - 1),
    d1q, d2q, d3q, d4q, d4r, a13q, a13r, a9q, a9r, a5q, a5r, a11q, a11r, c1, c2, c3]
  unfold kappa runPoly
  simp only [eval_mul, eval_comp, eval_add, eval_sub, eval_X, eval_C]
  rw [← hsc, Nat.add_sub_cancel (n := t') (m := 11 * n₁ + 2)]
  ring

/-! ## 4. Both sides vanish for `u < e` -/

/-- `Π(u) = 0` for `u < e`: through the third factor below `c`, through the reflected fourth on
`[c, e)`, where the wrapped argument `u + p − e` exceeds `e` because `c > 2e − p`. -/
theorem runPoly_eval_eq_zero_of_lt {p : ℕ} [hp : Fact p.Prime] {r u : ℕ} (hr : r < p)
    (h1 : 3 * p ≤ 13 * r) (h2 : 17 * r < 4 * p) (hu : u < p) (hue : u < 11 * r - 2 * p) :
    (runPoly p r).eval (u : ZMod p) = 0 := by
  unfold runPoly
  simp only [eval_mul, eval_comp, eval_add, eval_sub, eval_X, eval_C]
  rcases Nat.lt_or_ge u (5 * r - p) with huc | huc
  · rw [← choose_cast_eq_binPoly u (5 * r - p) (by omega), Nat.choose_eq_zero_of_lt huc]
    simp
  · have hcast : (u : ZMod p) - ((11 * r - 2 * p : ℕ) : ZMod p)
        = ((u + p - (11 * r - 2 * p) : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (show 11 * r - 2 * p ≤ u + p by omega)]
      push_cast
      rw [ZMod.natCast_self]
      ring
    have hz : (11 * r - 2 * p).choose (u + p - (11 * r - 2 * p)) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [hcast, ← signChoose_eq (p := p) (11 * r - 2 * p) (u + p - (11 * r - 2 * p)) (by omega)
      (by omega), hz]
    simp

/-- The in-window term vanishes mod `p` for `u < e`, by the same two factors (Lucas, then the
units binomial is `0`). -/
theorem term_eq_zero_of_lt {p : ℕ} [hp : Fact p.Prime] {n n₁ r t u : ℕ}
    (hn : n = p * n₁ + r) (hr : r < p) (h1 : 3 * p ≤ 13 * r) (h2 : 17 * r < 4 * p)
    (hu : u < p) (hue : u < 11 * r - 2 * p)
    (hk : t * p + u + 4 * n + 1 ∈ candidateM.window n) :
    (((-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
        * (cTerm n (t * p + u + 4 * n + 1) : ℤ) : ℤ) : ZMod p) = 0 := by
  have hp0 := hp.out.pos
  obtain ⟨hw1, hw2⟩ := (mem_window_iff n _).1 hk
  have h5 : 5 * n = (5 * r - p) + (5 * n₁ + 1) * p := by
    have e : (5 * n₁ + 1) * p = 5 * (p * n₁) + p := by ring
    omega
  have h11 : 11 * n = (11 * r - 2 * p) + (11 * n₁ + 2) * p := by
    have e : (11 * n₁ + 2) * p = 11 * (p * n₁) + 2 * p := by ring
    omega
  obtain ⟨a5q, a5r⟩ := digits_of_decomp hp0 h5 (by omega)
  obtain ⟨a11q, a11r⟩ := digits_of_decomp hp0 h11 (by omega)
  have hk3 : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
  obtain ⟨d3q, d3r⟩ := digits_of_decomp hp0 hk3 hu
  rw [cTerm]
  push_cast
  rcases Nat.lt_or_ge u (5 * r - p) with huc | huc
  · rw [lucas_raw (t * p + u + 4 * n + 1 - 4 * n - 1) (5 * n), d3r, a5r,
      Nat.choose_eq_zero_of_lt huc]
    simp
  · -- in-window with `u < e` forces `t ≥ E₁ + 1`, and the fourth lower argument wraps
    have ht : 11 * n₁ + 3 ≤ t := by
      by_contra hcon
      have e' : t * p ≤ (11 * n₁ + 2) * p := Nat.mul_le_mul_right p (by omega)
      have e : (11 * n₁ + 2) * p = 11 * (p * n₁) + 2 * p := by ring
      omega
    have hk4 : t * p + u + 4 * n + 1 - 15 * n - 1
        = (u + p - (11 * r - 2 * p)) + (t - (11 * n₁ + 3)) * p := by
      have e : (t - (11 * n₁ + 3)) * p = t * p - (11 * n₁ + 3) * p := Nat.sub_mul _ _ _
      have e2 : (11 * n₁ + 3) * p = 11 * (p * n₁) + 3 * p := by ring
      have e3 : (11 * n₁ + 3) * p ≤ t * p := Nat.mul_le_mul_right p ht
      omega
    obtain ⟨d4q, d4r⟩ := digits_of_decomp hp0 hk4 (by omega)
    -- the vanishing binomial NAMED: a bare `Nat.choose_eq_zero_of_lt (by omega)` inside `rw`
    -- binds to the first `choose` in the goal, which is the 13n one (measured, draft 2's
    -- `285:35`, an `omega` asked to prove `k' < 13n`).
    have hz : (11 * r - 2 * p).choose (u + p - (11 * r - 2 * p)) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [lucas_raw (11 * n) (t * p + u + 4 * n + 1 - 15 * n - 1), d4r, a11r, hz]
    simp

/-! ## 5. The block congruence on the stratum -/

/-- For `u ≥ e` on a block from the first, the `if` is the term itself: an off-window `u` is
past the window's END, where the fourth binomial is `0` in `ℕ`. -/
theorem if_eq_term_of_ge {n n₁ p r t' u : ℕ} (hn : n = p * n₁ + r)
    (h1 : 3 * p ≤ 13 * r) (hue : 11 * r - 2 * p ≤ u) :
    (if (t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 ∈ candidateM.window n
      then (-1 : ℤ) ^ (12 * n + ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1) - 1)
            * (cTerm n ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1) : ℤ)
      else 0)
    = (-1 : ℤ) ^ (12 * n + ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1) - 1)
        * (cTerm n ((t' + (11 * n₁ + 2)) * p + u + 4 * n + 1) : ℤ) := by
  split_ifs with h
  · rfl
  · rw [mem_window_iff] at h
    have e' : (t' + (11 * n₁ + 2)) * p = t' * p + 11 * (p * n₁) + 2 * p := by ring
    have hlo : 15 * n + 1 ≤ (t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 := by omega
    have hhi : 11 * n < (t' + (11 * n₁ + 2)) * p + u + 4 * n + 1 - 15 * n - 1 := by omega
    rw [cTerm, Nat.choose_eq_zero_of_lt hhi, mul_zero]
    simp

/-- **THE BLOCK CONGRUENCE ON `[3/13, 4/17)`, at every block.** -/
theorem blockSum_dvd {n p : ℕ} (hp : p ∈ phiWindow n)
    (h1 : 3 * p ≤ 13 * (n % p)) (h2 : 17 * (n % p) < 4 * p) (t : ℕ) :
    (p : ℤ) ^ 1 ∣ blockSum n p t := by
  have hpp := prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 := hpp.pos
  have hn : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hr : n % p < p := Nat.mod_lt _ hp0
  generalize n / p = n₁ at hn
  generalize n % p = r at hn hr h1 h2
  rw [pow_one, blockSum_eq_sum_range hp0 t]
  rcases Nat.lt_or_ge t (11 * n₁ + 2) with hlt | hge
  · -- every `u` of this block lies below the window
    have hz : ∀ u ∈ Finset.range p,
        (if t * p + u + 4 * n + 1 ∈ candidateM.window n
          then (-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
                * (cTerm n (t * p + u + 4 * n + 1) : ℤ)
          else 0) = 0 := by
      intro u hu
      have hu' := Finset.mem_range.mp hu
      split_ifs with hmem
      swap
      · rfl
      exfalso
      rw [mem_window_iff] at hmem
      have e1 : (t + 1) * p ≤ (11 * n₁ + 2) * p := Nat.mul_le_mul_right p (by omega)
      have e2 : (t + 1) * p = t * p + p := by ring
      have e3 : (11 * n₁ + 2) * p = 11 * (p * n₁) + 2 * p := by ring
      omega
    rw [Finset.sum_eq_zero hz]
    exact dvd_zero _
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + (11 * n₁ + 2) := ⟨t - (11 * n₁ + 2), by omega⟩
    refine dvd_sum_of_poly _ (kappa p n₁ r (t' + (11 * n₁ + 2))) (runPoly p r)
      (runPoly_natDegree_le h1 h2) ?_
    intro u hu
    rcases Nat.lt_or_ge u (11 * r - 2 * p) with hue | hue
    · rw [runPoly_eval_eq_zero_of_lt hr h1 h2 hu hue, mul_zero]
      split_ifs with hmem
      · exact term_eq_zero_of_lt hn hr h1 h2 hu hue hmem
      · simp
    · rw [if_eq_term_of_ge hn h1 hue]
      exact term_eq_of_ge hn hr h1 h2 hu hue

/-! ## 6. The φ̃ wire on piece 7, and the piece closed for the harmonic side -/

theorem profile_pairwise :
    List.Pairwise (fun s u : ℚ × ℚ × ℚ => s.2.1 ≤ u.1) Zeta2Profile.candidateProfile := by
  decide +kernel

/-- **First match is the only match, on the landed 26-row table**: if `x` lies in the row
`(a, b, v)` then `φ̃ x = v`, whatever row `List.find?` reaches first.  The `candidateProfile` twin
of `Zeta2HatDispatch.phiSingle_of_mem`. -/
theorem phiT_of_mem {x a b v : ℚ} (ht : (a, b, v) ∈ Zeta2Profile.candidateProfile)
    (h1 : a ≤ x) (h2 : x < b) : phiT x = v.num.toNat := by
  have : Std.Symm (fun s t : ℚ × ℚ × ℚ => s.2.1 ≤ t.1 ∨ t.2.1 ≤ s.1) := ⟨fun _ _ h => h.symm⟩
  have hpw : Zeta2Profile.candidateProfile.Pairwise (fun s t => s.2.1 ≤ t.1 ∨ t.2.1 ≤ s.1) :=
    profile_pairwise.imp Or.inl
  unfold phiT
  rcases hf : Zeta2Profile.candidateProfile.find? (fun t => decide (t.1 ≤ x ∧ x < t.2.1))
    with _ | t'
  · exfalso
    have hn := List.find?_eq_none.1 hf (a, b, v) ht
    simp only [decide_eq_true_eq, not_and] at hn
    exact absurd h2 (hn h1)
  · rw [hf]
    have hmem' := List.mem_of_find?_eq_some hf
    have hp' := List.find?_some hf
    simp only [decide_eq_true_eq] at hp'
    by_cases heq : t' = (a, b, v)
    · rw [heq]
    · exfalso
      rcases List.Pairwise.forall hpw hmem' ht heq with h | h
      · have hba : t'.2.1 ≤ a := h
        have := hp'.2
        linarith
      · have hbt : b ≤ t'.1 := h
        have := hp'.1
        linarith

/-- `φ̃ = 1` on piece 7, `[1/5, 4/17)`. -/
theorem phiT_piece7 {x : ℚ} (h1 : 1 / 5 ≤ x) (h2 : x < 4 / 17) : phiT x = 1 := by
  have h := phiT_of_mem (a := 1 / 5) (b := 4 / 17) (v := 1) (by decide +kernel) h1 h2
  exact h

/-- The piece's bounds as residue inequalities, through the landed bridge
`Zeta2Arith.fract_ge_iff` / `fract_lt_iff` (they live in `Zeta2Arith`, stated in
`Zeta2CarryFull.lean` — the first draft looked for them under `Zeta2CarryFull.` and found nothing). -/
theorem phiT_piece7_res {n p : ℕ} (hp : 0 < p) (hlo : p ≤ 5 * (n % p))
    (hhi : 17 * (n % p) < 4 * p) : phiT (Int.fract ((n : ℚ) / (p : ℚ))) = 1 := by
  refine phiT_piece7 ?_ ?_
  · have h := (fract_ge_iff n p 1 5 hp (by norm_num)).2 (by omega)
    exact_mod_cast h
  · have h := (fract_lt_iff n p 4 17 hp (by norm_num)).2 (by omega)
    exact_mod_cast h

/-- **PROFILE PIECE 7 `[1/5, 4/17)` CLOSED for the harmonic side**: at every window prime whose
residue lies in the piece, every block sum carries `p^{φ̃}` with `φ̃ = φ̃({n/p})` itself — the
three run-free strata through `Zeta2PtpCong.noShort_S2/S3/S4`, the run stratum through
`blockSum_dvd`. -/
theorem piece7_blocks {n p : ℕ} (hp : p ∈ phiWindow n) (hlo : p ≤ 5 * (n % p))
    (hhi : 17 * (n % p) < 4 * p) (t : ℕ) :
    (p : ℤ) ^ (phiT (Int.fract ((n : ℚ) / (p : ℚ)))) ∣ blockSum n p t := by
  have hp0 := (prime_of_mem_phiWindow hp).pos
  rw [phiT_piece7_res hp0 hlo hhi]
  rcases Nat.lt_or_ge (13 * (n % p)) (3 * p) with h13 | h13
  · refine blockSum_dvd_of_noShort hp (Zeta2PtpCong.noShort_of_runFreeOne hp0 ?_) t
    unfold Zeta2PtpCong.RunFreeOne
    omega
  · exact blockSum_dvd hp h13 hhi t

/-! ## 7. Non-vacuity and the smallest cell -/

/-- The stratum is inhabited by a window cell: `n = 3`, `p = 13`, `r = 3`. -/
theorem witness_3_13 : 13 ∈ phiWindow 3 ∧ 3 * 13 ≤ 13 * (3 % 13) ∧ 17 * (3 % 13) < 4 * 13 := by
  refine ⟨by decide +kernel, by decide, by decide⟩

/-- The identity's constant at that cell's block `t = 3` (`t' = 1`, `n₁ = 0`): κ is a unit, so
the block's vanishing is the POLYNOMIAL's, not the constant's. -/
theorem kappa_3_13_3_ne_zero : kappa 13 0 3 3 ≠ 0 := by decide

end Zeta2PtpS7

#print axioms Zeta2PtpS7.digits_of_decomp
#check @Zeta2PtpS7.digits_of_decomp
#print axioms Zeta2PtpS7.cast_of_decomp
#check @Zeta2PtpS7.cast_of_decomp
#print axioms Zeta2PtpS7.lucas_raw
#check @Zeta2PtpS7.lucas_raw
#print axioms Zeta2PtpS7.runPoly_natDegree_le
#check @Zeta2PtpS7.runPoly_natDegree_le
#print axioms Zeta2PtpS7.term_eq_of_ge
#check @Zeta2PtpS7.term_eq_of_ge
#print axioms Zeta2PtpS7.runPoly_eval_eq_zero_of_lt
#check @Zeta2PtpS7.runPoly_eval_eq_zero_of_lt
#print axioms Zeta2PtpS7.term_eq_zero_of_lt
#check @Zeta2PtpS7.term_eq_zero_of_lt
#print axioms Zeta2PtpS7.if_eq_term_of_ge
#check @Zeta2PtpS7.if_eq_term_of_ge
#print axioms Zeta2PtpS7.blockSum_dvd
#check @Zeta2PtpS7.blockSum_dvd
#print axioms Zeta2PtpS7.profile_pairwise
#check @Zeta2PtpS7.profile_pairwise
#print axioms Zeta2PtpS7.phiT_of_mem
#check @Zeta2PtpS7.phiT_of_mem
#print axioms Zeta2PtpS7.phiT_piece7
#check @Zeta2PtpS7.phiT_piece7
#print axioms Zeta2PtpS7.phiT_piece7_res
#check @Zeta2PtpS7.phiT_piece7_res
#print axioms Zeta2PtpS7.piece7_blocks
#check @Zeta2PtpS7.piece7_blocks
#print axioms Zeta2PtpS7.witness_3_13
#check @Zeta2PtpS7.witness_3_13
#print axioms Zeta2PtpS7.kappa_3_13_3_ne_zero
#check @Zeta2PtpS7.kappa_3_13_3_ne_zero
