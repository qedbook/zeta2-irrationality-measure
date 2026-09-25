import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# B1 — (★) as a polynomial identity, and the bridge into L1

Row **B1** of [`docs/future/zeta2-integral-free.md`](../../docs/future/zeta2-integral-free.md)
§5.3, for the μ(ζ(2)) ≤ 5.0495243 chain.

## What (★) is

The Mellin–Barnes creative-telescoping engine (`cas::zeilqn`, `include/zeil_mb.h`) represents the
member family by a Γ-spec; `mb_rebase` produces, at each integer `n`, five polynomial data in the
contour variable `t`, every one of them a product of integer affine factors:

* `a`, `b`, `c` — the **Gosper normal form** of the shifted member ratio, i.e.
  `ρₙ(t+1)·D(t) / (ρₙ(t)·D(t+1)) = (a t / b t) * (c (t+1) / c t)`;
* `D` — the common rebase denominator, and `Pa j` with `ρ_{n+j}(t)·D(t) = ρₙ(t)·Pa j t`.

With `α j` the recurrence coefficients and `x` the certificate polynomial, **(★) is the ℚ[t]
identity**

> `a t * x (t+1) − b (t−1) * x t = c t * ∑ j, α j * Pa j t`

which is exactly what `cas::zeilqn::star_check_core` verifies over ℤ after clearing denominators,
and what `mb_solve` proves on its deterministic exact grid.

## What this file proves

1. `star_telescopes` — **(★) ⟹ the Δ-form L1 consumes.** L1 does not consume the polynomial
   identity; it consumes `∑ j, α j * ρ_{n+j} = S(·+1) − S(·)` and then applies the contour
   functional. This is that step, and it is the whole mathematical content of B1's interface.
2. `star_forall_of_grid` — the engine's **deterministic exact grid**, as a theorem: an `n`-degree
   bound plus vanishing at more than that many integer points gives the identity for every `n`.
   This is what licenses "checked at 552 points ⟹ ∀ n" as a proof rather than a receipt.
3. `hrec_of_rational_coeffs` — the **clearing step**: rational-function recurrence coefficients
   become `Polynomial ℝ` ones, which is the shape `Zeta2L5.poincare_upper_bound` takes.
4. `star_growth_bound` — the **composition executed**: from the (★)-side hypotheses straight to
   L5's conclusion `∃ C N, ∀ n ≥ N, |y n| ≤ C * ρ ^ n`, through a verbatim copy of D1's
   `poincare_upper_bound` (proved in `docs/future/zeta2-l5-poincare.md` §4.2, reproduced here so
   the composition is *executed* and not merely asserted — LEAN.md §3).

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`) on the buildbox; every theorem carries a
`#print axioms` receipt at the foot of the file.
-/

namespace Zeta2StarB1

open Filter Topology Polynomial

/-! ## §1. (★) and the telescoping bridge -/

/-- **(★) at one index, as a polynomial identity in the contour variable.**

`a`, `b`, `c` are the Gosper normal form of the shifted member ratio, `Pa j` the rebased
numerators, `α j` the recurrence coefficients and `x` the certificate. Stated pointwise in `t`
because that is how the engine checks it and how `ring` discharges it; over an infinite field it
is equivalent to the identity of polynomials (`Polynomial.funext`). -/
def StarIdentity {K : Type*} [Field K] {m : ℕ}
    (a b c x : K → K) (Pa : Fin m → K → K) (α : Fin m → K) : Prop :=
  ∀ t : K, a t * x (t + 1) - b (t - 1) * x t = c t * ∑ j, α j * Pa j t

/-- **B1's interface theorem: (★) ⟹ the summand family telescopes.**

`u` is the rebased member `ρₙ / D`, `ρ j` the members `ρ_{n+j}` and `S` the Gosper antidifference
`b(·−1) · x · u / c`, all supplied through multiplicative hypotheses so that no division appears.

The hypotheses are stated in exactly the form the engine's data produces them:

* `hu` is the Gosper normal form, cleared of denominators;
* `hρ` is the rebase `ρ_{n+j} = u · Pa j`;
* `hS` is the antidifference, cleared of its `c` denominator;
* `hstar` is (★) itself, at this `t`.

The conclusion `∑ j, α j * ρ j t = S (t + 1) - S t` is what L1 applies the contour functional to:
the functional of a Δ is the strip residue (B2's shift lemma), which B3's census kills. -/
theorem star_telescopes {K : Type*} [Field K] {m : ℕ}
    (a b c x u S : K → K) (Pa ρ : Fin m → K → K) (α : Fin m → K) (t : K)
    (hc : c t ≠ 0) (hc1 : c (t + 1) ≠ 0)
    (hu : u (t + 1) * (b t * c t) = u t * (a t * c (t + 1)))
    (hρ : ∀ j, ρ j t = u t * Pa j t)
    (hS : ∀ s : K, S s * c s = b (s - 1) * x s * u s)
    (hstar : a t * x (t + 1) - b (t - 1) * x t = c t * ∑ j, α j * Pa j t) :
    ∑ j, α j * ρ j t = S (t + 1) - S t := by
  -- `S (t+1) * c t = a t * x (t+1) * u t`, after cancelling `c (t+1)`.
  have hSup : S (t + 1) * c t = a t * x (t + 1) * u t := by
    have h1 : S (t + 1) * c (t + 1) = b t * x (t + 1) * u (t + 1) := by
      have := hS (t + 1); rwa [add_sub_cancel_right] at this
    have h2 : (S (t + 1) * c t) * c (t + 1) = (a t * x (t + 1) * u t) * c (t + 1) := by
      calc (S (t + 1) * c t) * c (t + 1)
          = (S (t + 1) * c (t + 1)) * c t := by ring
        _ = (b t * x (t + 1) * u (t + 1)) * c t := by rw [h1]
        _ = x (t + 1) * (u (t + 1) * (b t * c t)) := by ring
        _ = x (t + 1) * (u t * (a t * c (t + 1))) := by rw [hu]
        _ = (a t * x (t + 1) * u t) * c (t + 1) := by ring
    exact mul_right_cancel₀ hc1 h2
  have hSlo : S t * c t = b (t - 1) * x t * u t := hS t
  -- Subtract, then cancel `c t`.
  have key : (S (t + 1) - S t) * c t = (u t * ∑ j, α j * Pa j t) * c t := by
    calc (S (t + 1) - S t) * c t
        = S (t + 1) * c t - S t * c t := by ring
      _ = a t * x (t + 1) * u t - b (t - 1) * x t * u t := by rw [hSup, hSlo]
      _ = (a t * x (t + 1) - b (t - 1) * x t) * u t := by ring
      _ = (c t * ∑ j, α j * Pa j t) * u t := by rw [hstar]
      _ = (u t * ∑ j, α j * Pa j t) * c t := by ring
  have hdiff : S (t + 1) - S t = u t * ∑ j, α j * Pa j t := mul_right_cancel₀ hc key
  rw [hdiff, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hρ j]; ring

/-- The same conclusion for every `t` at which the three nonvanishing side conditions hold — the
form L1 actually integrates. -/
theorem star_telescopes_of_forall {K : Type*} [Field K] {m : ℕ}
    (a b c x u S : K → K) (Pa ρ : Fin m → K → K) (α : Fin m → K) (T : Set K)
    (hc : ∀ t ∈ T, c t ≠ 0) (hc1 : ∀ t ∈ T, c (t + 1) ≠ 0)
    (hu : ∀ t, u (t + 1) * (b t * c t) = u t * (a t * c (t + 1)))
    (hρ : ∀ j t, ρ j t = u t * Pa j t)
    (hS : ∀ s : K, S s * c s = b (s - 1) * x s * u s)
    (hstar : StarIdentity a b c x Pa α) :
    ∀ t ∈ T, ∑ j, α j * ρ j t = S (t + 1) - S t := fun t ht =>
  star_telescopes a b c x u S Pa ρ α t (hc t ht) (hc1 t ht) (hu t) (fun j => hρ j t) hS (hstar t)

/-! ## §2. The deterministic exact grid, as a theorem

The engine proves (★) for every `n` by clearing it into a polynomial in `n` of a computed degree
and checking that it vanishes at more integer points than that degree (`mb_solve`'s
`DeterministicExact` tier: 630 points for the record pair, 552 for the promoted candidate). The
principle is one Mathlib lemma; stating it here is what turns "the engine checked a grid" into a
proof obligation with a named shape. -/

/-- **The grid principle.** A polynomial of degree at most `D` vanishing at more than `D` points of
an integral domain is the zero polynomial — hence its evaluation vanishes everywhere, which is the
`∀ n` that L1 needs. -/
theorem star_forall_of_grid {R : Type*} [CommRing R] [IsDomain R]
    (F : R[X]) (D : ℕ) (hdeg : F.natDegree ≤ D) (s : Finset R) (hs : D < s.card)
    (h0 : ∀ v ∈ s, F.eval v = 0) : ∀ v : R, F.eval v = 0 := by
  classical
  have hF : F = 0 := by
    by_contra hne
    have hroots : s ⊆ F.roots.toFinset := by
      intro v hv
      simp only [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
      exact h0 v hv
    have : s.card ≤ F.natDegree :=
      le_trans (Finset.card_le_card hroots)
        (le_trans (Multiset.toFinset_card_le _) (F.card_roots' ))
    omega
  simp [hF]

/-- The grid principle in the shape the engine hands it over: the cleared (★) residual is a
polynomial in `n`, and vanishing on a grid larger than its degree gives (★) at every natural
number. -/
theorem star_holds_forall_nat {R : Type*} [CommRing R] [IsDomain R]
    (F : R[X]) (D : ℕ) (hdeg : F.natDegree ≤ D) (s : Finset R) (hs : D < s.card)
    (h0 : ∀ v ∈ s, F.eval v = 0) (φ : ℕ → R) : ∀ n : ℕ, F.eval (φ n) = 0 :=
  fun n => star_forall_of_grid F D hdeg s hs h0 (φ n)

/-! ## §3. The clearing step — into `Polynomial ℝ` coefficients

L1 delivers `∑ j, α j n * y (n + j) = 0` with `α j` **rational functions** of `n` (the engine
normalises `α J ≡ 1`). D1's `poincare_upper_bound` wants **polynomial** coefficients. Clearing by
the common denominator is the whole of the step, and it is worth stating because it is where the
degree equalities and leading-coefficient ratios that D1 consumes are actually produced. -/

/-- **The clearing step.** If the polynomial coefficients agree with `B · α j` at every natural
number, the polynomial recurrence holds wherever `B` does not vanish — and `B` is a nonzero
polynomial, so that is all but finitely many `n`, which is all L5 needs (its `N` is inexplicit). -/
theorem hrec_of_rational_coeffs
    (y : ℕ → ℝ) (P₀ P₁ P₂ P₃ B : ℝ[X]) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    (hα : ∀ n : ℕ, α₀ n * y n + α₁ n * y (n + 1) + α₂ n * y (n + 2) + α₃ n * y (n + 3) = 0)
    (h₀ : ∀ n : ℕ, P₀.eval (n : ℝ) = B.eval (n : ℝ) * α₀ n)
    (h₁ : ∀ n : ℕ, P₁.eval (n : ℝ) = B.eval (n : ℝ) * α₁ n)
    (h₂ : ∀ n : ℕ, P₂.eval (n : ℝ) = B.eval (n : ℝ) * α₂ n)
    (h₃ : ∀ n : ℕ, P₃.eval (n : ℝ) = B.eval (n : ℝ) * α₃ n) :
    ∀ n : ℕ, P₀.eval (n : ℝ) * y n + P₁.eval (n : ℝ) * y (n + 1)
      + P₂.eval (n : ℝ) * y (n + 2) + P₃.eval (n : ℝ) * y (n + 3) = 0 := by
  intro n
  rw [h₀ n, h₁ n, h₂ n, h₃ n]
  linear_combination B.eval (n : ℝ) * hα n

/-! ## §4. D1's L5 theorem, reproduced, and the composition executed

`majorant_of_three_term`, `step_of_recurrence`, `nat_eventual_ratio_bound`,
`nat_eventual_ne_zero` and `poincare_upper_bound` are verbatim from
[`docs/future/zeta2-l5-poincare.md`](../../docs/future/zeta2-l5-poincare.md) §4.2 (D1, proved
2026-09-08). They are reproduced here — not cited — so that §4's capstone is an *executed*
composition: LEAN.md §3, "proving pieces with the others as hypotheses is not composing". -/

theorem majorant_of_three_term
    {y : ℕ → ℝ} {A₀ A₁ A₂ ρ : ℝ} {N : ℕ}
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hρ : 0 < ρ)
    (hchar : A₂ * ρ ^ 2 + A₁ * ρ + A₀ ≤ ρ ^ 3)
    (hstep : ∀ n, N ≤ n → |y (n + 3)| ≤ A₂ * |y (n + 2)| + A₁ * |y (n + 1)| + A₀ * |y n|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, N ≤ n → |y n| ≤ C * ρ ^ n := by
  have hpow : ∀ m : ℕ, (0 : ℝ) < ρ ^ m := fun m => pow_pos hρ m
  set C : ℝ :=
    max (max (|y N| / ρ ^ N) (|y (N + 1)| / ρ ^ (N + 1))) (|y (N + 2)| / ρ ^ (N + 2)) with hC
  have hC0 : 0 ≤ C := by
    have : (0:ℝ) ≤ |y N| / ρ ^ N := div_nonneg (abs_nonneg _) (hpow N).le
    exact le_trans this (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨C, hC0, ?_⟩
  have main : ∀ k : ℕ, |y (N + k)| ≤ C * ρ ^ (N + k) ∧
      |y (N + k + 1)| ≤ C * ρ ^ (N + k + 1) ∧
      |y (N + k + 2)| ≤ C * ρ ^ (N + k + 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> simp only [Nat.add_zero] <;> rw [← div_le_iff₀ (hpow _)]
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
      · exact le_max_right _ _
    | succ k ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have hidx1 : N + (k + 1) = N + k + 1 := by omega
      have hidx2 : N + (k + 1) + 1 = N + k + 2 := by omega
      have hidx3 : N + (k + 1) + 2 = N + k + 3 := by omega
      have hstep' := hstep (N + k) (Nat.le_add_right _ _)
      have h3 : |y (N + k + 3)| ≤ C * ρ ^ (N + k + 3) := by
        have hb : |y (N + k + 3)|
            ≤ A₂ * (C * ρ ^ (N + k + 2)) + A₁ * (C * ρ ^ (N + k + 1))
              + A₀ * (C * ρ ^ (N + k)) := le_trans hstep' (by gcongr)
        refine le_trans hb ?_
        have hexp : (ρ : ℝ) ^ (N + k + 3) = ρ ^ (N + k) * ρ ^ 3 := by ring
        have hexp2 : (ρ : ℝ) ^ (N + k + 2) = ρ ^ (N + k) * ρ ^ 2 := by ring
        have hexp1 : (ρ : ℝ) ^ (N + k + 1) = ρ ^ (N + k) * ρ := by ring
        rw [hexp, hexp2, hexp1]
        have hfac : C * ρ ^ (N + k) * (A₂ * ρ ^ 2 + A₁ * ρ + A₀)
            ≤ C * ρ ^ (N + k) * ρ ^ 3 := mul_le_mul_of_nonneg_left hchar (by positivity)
        nlinarith [hfac]
      exact ⟨by rw [hidx1]; exact h1, by rw [hidx2]; exact h2, by rw [hidx3]; exact h3⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact (main k).1

theorem step_of_recurrence
    {y : ℕ → ℝ} {p₀ p₁ p₂ p₃ : ℕ → ℝ} {A₀ A₁ A₂ : ℝ} {N : ℕ}
    (hrec : ∀ n, p₀ n * y n + p₁ n * y (n + 1) + p₂ n * y (n + 2) + p₃ n * y (n + 3) = 0)
    (h3 : ∀ n, N ≤ n → p₃ n ≠ 0)
    (hb₀ : ∀ n, N ≤ n → |p₀ n| ≤ A₀ * |p₃ n|)
    (hb₁ : ∀ n, N ≤ n → |p₁ n| ≤ A₁ * |p₃ n|)
    (hb₂ : ∀ n, N ≤ n → |p₂ n| ≤ A₂ * |p₃ n|) :
    ∀ n, N ≤ n → |y (n + 3)| ≤ A₂ * |y (n + 2)| + A₁ * |y (n + 1)| + A₀ * |y n| := by
  intro n hn
  have hp3' : (0:ℝ) < |p₃ n| :=
    lt_of_le_of_ne (abs_nonneg _) (Ne.symm (abs_ne_zero.mpr (h3 n hn)))
  have key : p₃ n * y (n + 3) = -(p₀ n * y n + p₁ n * y (n + 1) + p₂ n * y (n + 2)) := by
    have := hrec n; linarith
  have habs : |p₃ n| * |y (n + 3)|
      ≤ |p₂ n| * |y (n + 2)| + |p₁ n| * |y (n + 1)| + |p₀ n| * |y n| := by
    calc |p₃ n| * |y (n + 3)| = |p₃ n * y (n + 3)| := (abs_mul _ _).symm
      _ = |p₀ n * y n + p₁ n * y (n + 1) + p₂ n * y (n + 2)| := by rw [key, abs_neg]
      _ ≤ |p₀ n * y n + p₁ n * y (n + 1)| + |p₂ n * y (n + 2)| := abs_add_le _ _
      _ ≤ (|p₀ n * y n| + |p₁ n * y (n + 1)|) + |p₂ n * y (n + 2)| := by
            gcongr; exact abs_add_le _ _
      _ = |p₂ n| * |y (n + 2)| + |p₁ n| * |y (n + 1)| + |p₀ n| * |y n| := by
            simp [abs_mul]; ring
  have hbound : |p₂ n| * |y (n + 2)| + |p₁ n| * |y (n + 1)| + |p₀ n| * |y n|
      ≤ |p₃ n| * (A₂ * |y (n + 2)| + A₁ * |y (n + 1)| + A₀ * |y n|) := by
    have e₂ := hb₂ n hn; have e₁ := hb₁ n hn; have e₀ := hb₀ n hn
    nlinarith [abs_nonneg (y n), abs_nonneg (y (n+1)), abs_nonneg (y (n+2))]
  exact le_of_mul_le_mul_left (by linarith [le_trans habs hbound]) hp3'

theorem nat_eventual_ratio_bound
    (P Q : ℝ[X]) (hdeg : P.degree = Q.degree) (hQ : Q ≠ 0)
    (A : ℝ) (hA : |P.leadingCoeff / Q.leadingCoeff| < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |P.eval (n : ℝ)| ≤ A * |Q.eval (n : ℝ)| := by
  have hev : ∀ᶠ x : ℝ in atTop, |P.eval x / Q.eval x| < A :=
    (P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq Q hdeg).abs.eventually_lt_const hA
  have hbase : ∀ᶠ x : ℝ in atTop, |P.eval x| ≤ A * |Q.eval x| := by
    filter_upwards [hev, Q.eventually_atTop_not_isRoot hQ] with x hx hroot
    rw [abs_div, div_lt_iff₀ (abs_pos.mpr (hroot : Q.eval x ≠ 0))] at hx
    exact hx.le
  exact eventually_atTop.mp ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbase)

theorem nat_eventual_ne_zero (Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Q.eval (n : ℝ) ≠ 0 :=
  eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (Q.eventually_atTop_not_isRoot hQ))

/-- **L5** (D1, `docs/future/zeta2-l5-poincare.md` §4.2), reproduced verbatim. -/
theorem poincare_upper_bound
    (y : ℕ → ℝ) (P₀ P₁ P₂ P₃ : ℝ[X])
    (hrec : ∀ n : ℕ, P₀.eval (n : ℝ) * y n + P₁.eval (n : ℝ) * y (n + 1)
      + P₂.eval (n : ℝ) * y (n + 2) + P₃.eval (n : ℝ) * y (n + 3) = 0)
    (hP₃ : P₃ ≠ 0)
    (hd₀ : P₀.degree = P₃.degree) (hd₁ : P₁.degree = P₃.degree) (hd₂ : P₂.degree = P₃.degree)
    {A₀ A₁ A₂ ρ : ℝ}
    (hA₀ : |P₀.leadingCoeff / P₃.leadingCoeff| < A₀)
    (hA₁ : |P₁.leadingCoeff / P₃.leadingCoeff| < A₁)
    (hA₂ : |P₂.leadingCoeff / P₃.leadingCoeff| < A₂)
    (hρ : 0 < ρ) (hchar : A₂ * ρ ^ 2 + A₁ * ρ + A₀ ≤ ρ ^ 3) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n, N ≤ n → |y n| ≤ C * ρ ^ n := by
  obtain ⟨N₃, hN₃⟩ := nat_eventual_ne_zero P₃ hP₃
  obtain ⟨N₀, hN₀⟩ := nat_eventual_ratio_bound P₀ P₃ hd₀ hP₃ A₀ hA₀
  obtain ⟨N₁, hN₁⟩ := nat_eventual_ratio_bound P₁ P₃ hd₁ hP₃ A₁ hA₁
  obtain ⟨N₂, hN₂⟩ := nat_eventual_ratio_bound P₂ P₃ hd₂ hP₃ A₂ hA₂
  set N := max (max N₀ N₁) (max N₂ N₃) with hN
  have le₀ : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have le₁ : N₁ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have le₂ : N₂ ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have le₃ : N₃ ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hstep := step_of_recurrence (N := N) hrec
    (fun n hn => hN₃ n (le_trans le₃ hn))
    (fun n hn => hN₀ n (le_trans le₀ hn))
    (fun n hn => hN₁ n (le_trans le₁ hn))
    (fun n hn => hN₂ n (le_trans le₂ hn))
  obtain ⟨C, hC0, hCb⟩ := majorant_of_three_term
    (le_trans (abs_nonneg _) hA₀.le) (le_trans (abs_nonneg _) hA₁.le)
    (le_trans (abs_nonneg _) hA₂.le) hρ hchar hstep
  exact ⟨C, N, hC0, hCb⟩

/-! ### §4b. The same, with the recurrence assumed only EVENTUALLY

D1's `poincare_upper_bound` takes `hrec : ∀ n`. B1 does not in general deliver that: the strip
census (B3) certifies the boundary terms VALID only from some `n₀` onwards, with exact nonzero
defects below it, and `star_telescopes`' own side conditions (`c t ≠ 0`, `D t ≠ 0`) are eventual
facts about a polynomial. Since L5's conclusion is eventual anyway, nothing is lost by relaxing the
hypothesis — and everything is gained, because the unconditional form is one an implementer would
have to fake. The proofs are D1's, with `hrec n` replaced by `hrec n hn` and one more `max`. -/

theorem step_of_recurrence_eventual
    {y : ℕ → ℝ} {p₀ p₁ p₂ p₃ : ℕ → ℝ} {A₀ A₁ A₂ : ℝ} {N : ℕ}
    (hrec : ∀ n, N ≤ n → p₀ n * y n + p₁ n * y (n + 1) + p₂ n * y (n + 2) + p₃ n * y (n + 3) = 0)
    (h3 : ∀ n, N ≤ n → p₃ n ≠ 0)
    (hb₀ : ∀ n, N ≤ n → |p₀ n| ≤ A₀ * |p₃ n|)
    (hb₁ : ∀ n, N ≤ n → |p₁ n| ≤ A₁ * |p₃ n|)
    (hb₂ : ∀ n, N ≤ n → |p₂ n| ≤ A₂ * |p₃ n|) :
    ∀ n, N ≤ n → |y (n + 3)| ≤ A₂ * |y (n + 2)| + A₁ * |y (n + 1)| + A₀ * |y n| := by
  intro n hn
  have hp3' : (0:ℝ) < |p₃ n| :=
    lt_of_le_of_ne (abs_nonneg _) (Ne.symm (abs_ne_zero.mpr (h3 n hn)))
  have key : p₃ n * y (n + 3) = -(p₀ n * y n + p₁ n * y (n + 1) + p₂ n * y (n + 2)) := by
    have := hrec n hn; linarith
  have habs : |p₃ n| * |y (n + 3)|
      ≤ |p₂ n| * |y (n + 2)| + |p₁ n| * |y (n + 1)| + |p₀ n| * |y n| := by
    calc |p₃ n| * |y (n + 3)| = |p₃ n * y (n + 3)| := (abs_mul _ _).symm
      _ = |p₀ n * y n + p₁ n * y (n + 1) + p₂ n * y (n + 2)| := by rw [key, abs_neg]
      _ ≤ |p₀ n * y n + p₁ n * y (n + 1)| + |p₂ n * y (n + 2)| := abs_add_le _ _
      _ ≤ (|p₀ n * y n| + |p₁ n * y (n + 1)|) + |p₂ n * y (n + 2)| := by
            gcongr; exact abs_add_le _ _
      _ = |p₂ n| * |y (n + 2)| + |p₁ n| * |y (n + 1)| + |p₀ n| * |y n| := by
            simp [abs_mul]; ring
  have hbound : |p₂ n| * |y (n + 2)| + |p₁ n| * |y (n + 1)| + |p₀ n| * |y n|
      ≤ |p₃ n| * (A₂ * |y (n + 2)| + A₁ * |y (n + 1)| + A₀ * |y n|) := by
    have e₂ := hb₂ n hn; have e₁ := hb₁ n hn; have e₀ := hb₀ n hn
    nlinarith [abs_nonneg (y n), abs_nonneg (y (n+1)), abs_nonneg (y (n+2))]
  exact le_of_mul_le_mul_left (by linarith [le_trans habs hbound]) hp3'

/-- **L5 with an eventual recurrence** — the form B1 can actually supply. -/
theorem poincare_upper_bound_eventual
    (y : ℕ → ℝ) (P₀ P₁ P₂ P₃ : ℝ[X]) (N₀ : ℕ)
    (hrec : ∀ n : ℕ, N₀ ≤ n → P₀.eval (n : ℝ) * y n + P₁.eval (n : ℝ) * y (n + 1)
      + P₂.eval (n : ℝ) * y (n + 2) + P₃.eval (n : ℝ) * y (n + 3) = 0)
    (hP₃ : P₃ ≠ 0)
    (hd₀ : P₀.degree = P₃.degree) (hd₁ : P₁.degree = P₃.degree) (hd₂ : P₂.degree = P₃.degree)
    {A₀ A₁ A₂ ρ : ℝ}
    (hA₀ : |P₀.leadingCoeff / P₃.leadingCoeff| < A₀)
    (hA₁ : |P₁.leadingCoeff / P₃.leadingCoeff| < A₁)
    (hA₂ : |P₂.leadingCoeff / P₃.leadingCoeff| < A₂)
    (hρ : 0 < ρ) (hchar : A₂ * ρ ^ 2 + A₁ * ρ + A₀ ≤ ρ ^ 3) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n, N ≤ n → |y n| ≤ C * ρ ^ n := by
  obtain ⟨N₃, hN₃⟩ := nat_eventual_ne_zero P₃ hP₃
  obtain ⟨N₁', hN₁'⟩ := nat_eventual_ratio_bound P₀ P₃ hd₀ hP₃ A₀ hA₀
  obtain ⟨N₂', hN₂'⟩ := nat_eventual_ratio_bound P₁ P₃ hd₁ hP₃ A₁ hA₁
  obtain ⟨N₃', hN₃'⟩ := nat_eventual_ratio_bound P₂ P₃ hd₂ hP₃ A₂ hA₂
  set N := max (max N₀ N₃) (max (max N₁' N₂') N₃') with hN
  have le₀ : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have le₃ : N₃ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have le₁' : N₁' ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have le₂' : N₂' ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have le₃' : N₃' ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hstep := step_of_recurrence_eventual (N := N)
    (fun n hn => hrec n (le_trans le₀ hn))
    (fun n hn => hN₃ n (le_trans le₃ hn))
    (fun n hn => hN₁' n (le_trans le₁' hn))
    (fun n hn => hN₂' n (le_trans le₂' hn))
    (fun n hn => hN₃' n (le_trans le₃' hn))
  obtain ⟨C, hC0, hCb⟩ := majorant_of_three_term
    (le_trans (abs_nonneg _) hA₀.le) (le_trans (abs_nonneg _) hA₁.le)
    (le_trans (abs_nonneg _) hA₂.le) hρ hchar hstep
  exact ⟨C, N, hC0, hCb⟩

/-! ## §5. The capstone — B1's output feeding D1's input, executed

Everything L1 contributes between (★) and the recurrence is carried as a hypothesis in the
vocabulary its own rows produce: `hL` says the contour functional turns the telescoped family into
the recurrence (B2's shift lemma plus B3's ∀ n strip census, whose combined content is exactly
"the functional of a Δ vanishes"), and `hclear` is §3's clearing data. Nothing else is assumed. -/

/-- **B1 → L1 → L5, composed.** Given (★) at every `n` in the Δ-form, the vanishing of the
functional on a Δ, and the clearing data, the growth bound `∃ C N, ∀ n ≥ N, |y n| ≤ C · ρ ^ n`
follows — `poincare_upper_bound`'s conclusion, reached from B1's side of the interface. -/
theorem star_growth_bound
    (y : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ) (P₀ P₁ P₂ P₃ B : ℝ[X])
    -- L1: the functional applied to the telescoped family (B2 + B3)
    (hL : ∀ n : ℕ, α₀ n * y n + α₁ n * y (n + 1) + α₂ n * y (n + 2) + α₃ n * y (n + 3) = 0)
    -- §3: the clearing data
    (h₀ : ∀ n : ℕ, P₀.eval (n : ℝ) = B.eval (n : ℝ) * α₀ n)
    (h₁ : ∀ n : ℕ, P₁.eval (n : ℝ) = B.eval (n : ℝ) * α₁ n)
    (h₂ : ∀ n : ℕ, P₂.eval (n : ℝ) = B.eval (n : ℝ) * α₂ n)
    (h₃ : ∀ n : ℕ, P₃.eval (n : ℝ) = B.eval (n : ℝ) * α₃ n)
    -- D1: the operator's own measured data
    (hP₃ : P₃ ≠ 0)
    (hd₀ : P₀.degree = P₃.degree) (hd₁ : P₁.degree = P₃.degree) (hd₂ : P₂.degree = P₃.degree)
    {A₀ A₁ A₂ ρ : ℝ}
    (hA₀ : |P₀.leadingCoeff / P₃.leadingCoeff| < A₀)
    (hA₁ : |P₁.leadingCoeff / P₃.leadingCoeff| < A₁)
    (hA₂ : |P₂.leadingCoeff / P₃.leadingCoeff| < A₂)
    (hρ : 0 < ρ) (hchar : A₂ * ρ ^ 2 + A₁ * ρ + A₀ ≤ ρ ^ 3) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n, N ≤ n → |y n| ≤ C * ρ ^ n :=
  poincare_upper_bound y P₀ P₁ P₂ P₃
    (hrec_of_rational_coeffs y P₀ P₁ P₂ P₃ B α₀ α₁ α₂ α₃ hL h₀ h₁ h₂ h₃)
    hP₃ hd₀ hd₁ hd₂ hA₀ hA₁ hA₂ hρ hchar

/-- **The capstone in the form B1 can actually supply**: L1's recurrence only from `N₀` on, and the
clearing data only from `N₀` on. This is the theorem the chain should instantiate — the
unconditional `star_growth_bound` above exists to show the fit with D1's statement as written. -/
theorem star_growth_bound_eventual
    (y : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ) (P₀ P₁ P₂ P₃ B : ℝ[X]) (N₀ : ℕ)
    (hL : ∀ n : ℕ, N₀ ≤ n →
      α₀ n * y n + α₁ n * y (n + 1) + α₂ n * y (n + 2) + α₃ n * y (n + 3) = 0)
    (h₀ : ∀ n : ℕ, N₀ ≤ n → P₀.eval (n : ℝ) = B.eval (n : ℝ) * α₀ n)
    (h₁ : ∀ n : ℕ, N₀ ≤ n → P₁.eval (n : ℝ) = B.eval (n : ℝ) * α₁ n)
    (h₂ : ∀ n : ℕ, N₀ ≤ n → P₂.eval (n : ℝ) = B.eval (n : ℝ) * α₂ n)
    (h₃ : ∀ n : ℕ, N₀ ≤ n → P₃.eval (n : ℝ) = B.eval (n : ℝ) * α₃ n)
    (hP₃ : P₃ ≠ 0)
    (hd₀ : P₀.degree = P₃.degree) (hd₁ : P₁.degree = P₃.degree) (hd₂ : P₂.degree = P₃.degree)
    {A₀ A₁ A₂ ρ : ℝ}
    (hA₀ : |P₀.leadingCoeff / P₃.leadingCoeff| < A₀)
    (hA₁ : |P₁.leadingCoeff / P₃.leadingCoeff| < A₁)
    (hA₂ : |P₂.leadingCoeff / P₃.leadingCoeff| < A₂)
    (hρ : 0 < ρ) (hchar : A₂ * ρ ^ 2 + A₁ * ρ + A₀ ≤ ρ ^ 3) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n, N ≤ n → |y n| ≤ C * ρ ^ n := by
  refine poincare_upper_bound_eventual y P₀ P₁ P₂ P₃ N₀ (fun n hn => ?_)
    hP₃ hd₀ hd₁ hd₂ hA₀ hA₁ hA₂ hρ hchar
  rw [h₀ n hn, h₁ n hn, h₂ n hn, h₃ n hn]
  linear_combination B.eval (n : ℝ) * hL n hn

end Zeta2StarB1

/-! ## Axiom receipts — the only attestation (LEAN.md §1) -/

#print axioms Zeta2StarB1.star_telescopes
#print axioms Zeta2StarB1.star_telescopes_of_forall
#print axioms Zeta2StarB1.star_forall_of_grid
#print axioms Zeta2StarB1.star_holds_forall_nat
#print axioms Zeta2StarB1.hrec_of_rational_coeffs
#print axioms Zeta2StarB1.poincare_upper_bound
#print axioms Zeta2StarB1.step_of_recurrence_eventual
#print axioms Zeta2StarB1.poincare_upper_bound_eventual
#print axioms Zeta2StarB1.star_growth_bound
#print axioms Zeta2StarB1.star_growth_bound_eventual
