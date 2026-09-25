/-
# Row D3 — **L9 nondegeneracy** and **the L11 measure criterion**

`docs/future/zeta2-rate-lemma.md` §1 writes L9 and L11 and §1-notes(a) writes L11's one-page
proof; `docs/future/zeta2-integral-free.md` §5.1 writes the target `¬ LiouvilleWith p₀ ζ(2)`.
This file proves both links against CURRENT Mathlib, in the shape the chain's other rows
produce and consume.

**Three design decisions, each of which the chain's own prose gets wrong or leaves open.**

1. **No `limsup`.**  The chain phrases L8/L5 as `limsup (1/n)·log|y n| ≤ c`.  That is FALSE as a
   Lean statement over ℝ, twice over (`Real.log 0 = 0` makes a vanishing sequence satisfy every
   rate bound; `sInf` returns junk when the normalised log tends to `-∞`), and both traps are
   committed as positive falsifier theorems elsewhere in this corpus.  L11 here consumes
   `∀ n ≥ N, |y n| ≤ C · ρ ^ n` with `C` carried EXPLICITLY and `ρ` a plain real — the same shape
   `Zeta2L5.poincare_upper_bound` / `Zeta2StarB1.star_growth_bound_eventual` produce, so no
   restatement stands between the rate rows and this one.

2. **The gap hypothesis is `ρq * ρr ^ (p₀ - 1) < 1`, not `1 + v/u < p₀`.**  The two are
   equivalent (`gap_of_rate_bound` below proves the direction the chain needs), but the
   multiplicative form is what the proof actually uses, and stating it that way removes every
   logarithm from the proof body: no `Real.log`, no `u`, no `v`, no division of rates.  This is
   what makes the argument fit in one screen of estimates instead of an ε-chase.

3. **One index is chosen, not an ε-family.**  §1-notes(a) picks
   `n = ⌈(1+ε)·log(2q)/((1−ε)u)⌉` and lets `ε ↓ 0`; the audit fix of 2026-09-07 shows how easy
   that spelling is to get wrong.  Here the index is the LEAST `t` past a base with
   `2·Cr·q·ρr^t ≤ 1`, so the upper bound on `t` comes from minimality rather than from a
   logarithm, and the whole `ε` limit disappears into the single hypothesis `hgap`.

**What is NOT here.**  L9's hypotheses are the chain's inputs, and two of them are not proved
anywhere in the repo: the three-term recurrence for `q`/`p` (rows B1–B5 of
`zeta2-integral-free.md` §5.3, i.e. L1) and the finite exact data `m₀ = 1120/1127` with
`q_1127 ≠ 0` (row D4-L4).  They enter as hypotheses, named in the vocabulary those rows produce.
Nothing here asserts them.

Elaborated against CURRENT Mathlib (`v4.34.0-rc2`, mathlib `5aedf732`) on the buildbox; Lean
never runs on the laptop (owner ruling 2026-09-07).
-/
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Zeta2L9L11

open Filter

/-! ## §0. One cast helper

A natural power and a real power commute through each other.  Used exactly once, to turn
`(ρr ^ i) ^ (p₀ - 1)` — an `rpow` of an `npow` — into `(ρr ^ (p₀ - 1)) ^ i`, an `npow` of the
one `rpow` the statement carries. -/

/-- `(a ^ i) ^ c = (a ^ c) ^ i` for a natural exponent `i` and a real exponent `c`. -/
theorem rpow_natPow_comm {a : ℝ} (ha : 0 ≤ a) (i : ℕ) (c : ℝ) :
    (a ^ i) ^ c = (a ^ c) ^ i := by
  rw [← Real.rpow_natCast a i, ← Real.rpow_mul ha, mul_comm, Real.rpow_mul ha,
    Real.rpow_natCast]

/-! ## §1. L9's two propagation lemmas

Both are pure algebra over the three-term recurrence
`α₀ n · y n + α₁ n · y (n+1) + α₂ n · y (n+2) + α₃ n · y (n+3) = 0`, which is the shape
`Zeta2Instantiate.rn_growth_of_L1` already takes for `rn`.  Forward propagation needs the
LEADING coefficient nonzero (`α₃`, i.e. `P₃` of L4); backward propagation needs the TRAILING
one (`α₀`, i.e. `P₀`), which is exactly why L4 has to produce two thresholds `n₁` and `m₀` and
not one. -/

/-- **Forward propagation.**  Three consecutive zeros at `t`, plus `α₃ ≠ 0` from `t` on, force
`y` to vanish identically from `t` on.

`α₃ n ≠ 0` is L4's `P₃(n) ≠ 0` for `n ≥ n₁`; the recurrence is L1. -/
theorem forward_vanishing (y α₀ α₁ α₂ α₃ : ℕ → ℝ) (N₀ t : ℕ)
    (hrec : ∀ n, N₀ ≤ n →
      α₀ n * y n + α₁ n * y (n + 1) + α₂ n * y (n + 2) + α₃ n * y (n + 3) = 0)
    (ht : N₀ ≤ t) (hα₃ : ∀ n, t ≤ n → α₃ n ≠ 0)
    (h0 : y t = 0) (h1 : y (t + 1) = 0) (h2 : y (t + 2) = 0) :
    ∀ m, t ≤ m → y m = 0 := by
  have key : ∀ k : ℕ, y (t + k) = 0 ∧ y (t + k + 1) = 0 ∧ y (t + k + 2) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1, h2⟩
    | succ k ih =>
        obtain ⟨e0, e1, e2⟩ := ih
        refine ⟨e1, e2, ?_⟩
        have h := hrec (t + k) (le_trans ht (Nat.le_add_right _ _))
        rw [e0, e1, e2] at h
        simp only [mul_zero, zero_add] at h
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (hα₃ (t + k) (Nat.le_add_right _ _))
        · exact h'
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact (key k).1

/-- **Backward propagation.**  If `y` vanishes from `T` on, and `α₀ ≠ 0` from `m₀` on, then `y`
vanishes from `m₀` on — the recurrence read right-to-left.

`α₀ n ≠ 0` is L4's `P₀(n) ≠ 0` for `n ≥ m₀`, and `m₀ = 1120` is the explicit constant row
D4-L4 computes.  This is the step the chain calls "backward-propagates to `q ≡ 0` on `[m₀, ∞)`". -/
theorem backward_vanishing (y α₀ α₁ α₂ α₃ : ℕ → ℝ) (N₀ m₀ T : ℕ)
    (hrec : ∀ n, N₀ ≤ n →
      α₀ n * y n + α₁ n * y (n + 1) + α₂ n * y (n + 2) + α₃ n * y (n + 3) = 0)
    (hm₀ : N₀ ≤ m₀) (hα₀ : ∀ n, m₀ ≤ n → α₀ n ≠ 0)
    (hT : ∀ m, T ≤ m → y m = 0) :
    ∀ k, m₀ ≤ k → y k = 0 := by
  have key : ∀ j k : ℕ, m₀ ≤ k → T ≤ k + j → y k = 0 := by
    intro j
    induction j with
    | zero => intro k _ hk2; exact hT k (by omega)
    | succ j ih =>
        intro k hk hk2
        by_cases hTk : T ≤ k
        · exact hT k hTk
        · have e1 := ih (k + 1) (by omega) (by omega)
          have e2 := ih (k + 2) (by omega) (by omega)
          have e3 := ih (k + 3) (by omega) (by omega)
          have h := hrec k (le_trans hm₀ hk)
          rw [e1, e2, e3] at h
          simp only [mul_zero, add_zero] at h
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' (hα₀ k hk)
          · exact h'
  intro k hk
  exact key T k hk (by omega)

/-! ## §2. L9 — nondegeneracy

The chain's L9: past a threshold, no rational `a/b` can annihilate three consecutive linear
forms.  Its proof is the one written out in `zeta2-rate-lemma.md` §1: forward-propagate the
three zeros, use the decay of `R` to force the integer numerators to vanish from some point on,
then backward-propagate that to `[m₀, ∞)` and contradict one exact nonzero row. -/

/-- The analytic half of L9: if the linear forms `S_m = Q_m a − P_m b` vanish from `t` on, and
`R_m = Q_m ζ − P_m` decays geometrically, then `Q` itself vanishes from some point on.

The mechanism is the one the design states: `b·R_m = Q_m·(bζ − a)`, and `bζ − a ≠ 0` because
`ζ` is irrational, so a nonzero integer `Q_m` pins `|R_m|` away from `0` — which the decay
forbids for large `m`. -/
theorem eventually_num_vanishes {ζ : ℝ} (hirr : Irrational ζ) (Q P : ℕ → ℤ)
    {Cr ρr : ℝ} {Nr : ℕ} (hCr : 0 ≤ Cr) (hρr0 : 0 ≤ ρr) (hρr1 : ρr < 1)
    (hdecay : ∀ n, Nr ≤ n → |(Q n : ℝ) * ζ - (P n : ℝ)| ≤ Cr * ρr ^ n)
    {a b : ℤ} (hb : b ≠ 0) {t : ℕ}
    (hS : ∀ m, t ≤ m → (Q m : ℝ) * (a : ℝ) - (P m : ℝ) * (b : ℝ) = 0) :
    ∃ T, t ≤ T ∧ Nr ≤ T ∧ ∀ m, T ≤ m → Q m = 0 := by
  have hbR : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hd0 : (b : ℝ) * ζ - (a : ℝ) ≠ 0 := by
    intro h
    apply hirr.ne_rational a b
    field_simp at h ⊢
    linarith [h]
  set d : ℝ := |(b : ℝ) * ζ - (a : ℝ)| with hddef
  have hdpos : 0 < d := abs_pos.mpr hd0
  have hbpos : 0 < |(b : ℝ)| := abs_pos.mpr hbR
  -- a threshold past which the decay bound is below `d / |b|`
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one
    (div_pos hdpos (mul_pos hbpos (by linarith : (0:ℝ) < Cr + 1))) hρr1
  refine ⟨max (max t Nr) M, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
  intro m hm
  by_contra hQm
  have hmt : t ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmr : Nr ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hmM : M ≤ m := le_trans (le_max_right _ _) hm
  -- `b * R m = Q m * (b ζ - a)`
  have hkey : (b : ℝ) * ((Q m : ℝ) * ζ - (P m : ℝ)) = (Q m : ℝ) * ((b : ℝ) * ζ - (a : ℝ)) := by
    have := hS m hmt
    nlinarith [this]
  have hQ1 : (1 : ℝ) ≤ |(Q m : ℝ)| := by
    have : (1 : ℤ) ≤ |Q m| := Int.one_le_abs hQm
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|Q m| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |(Q m : ℝ)| := by push_cast; ring
  -- lower bound on `|R m|`
  have hlow : d / |(b : ℝ)| ≤ |(Q m : ℝ) * ζ - (P m : ℝ)| := by
    rw [div_le_iff₀ hbpos]
    calc d = 1 * d := by ring
      _ ≤ |(Q m : ℝ)| * d := by nlinarith
      _ = |(Q m : ℝ) * ((b : ℝ) * ζ - (a : ℝ))| := by rw [abs_mul]
      _ = |(b : ℝ) * ((Q m : ℝ) * ζ - (P m : ℝ))| := by rw [hkey]
      _ = |(Q m : ℝ) * ζ - (P m : ℝ)| * |(b : ℝ)| := by rw [abs_mul]; ring
  -- upper bound on `|R m|`
  have hhigh : |(Q m : ℝ) * ζ - (P m : ℝ)| < d / |(b : ℝ)| := by
    have h1 : ρr ^ m ≤ ρr ^ M := pow_le_pow_of_le_one hρr0 hρr1.le hmM
    have h2 : Cr * ρr ^ m ≤ Cr * ρr ^ M := by nlinarith
    have h3 : Cr * ρr ^ M < d / |(b : ℝ)| := by
      have hcr : Cr < Cr + 1 := by linarith
      calc Cr * ρr ^ M ≤ (Cr + 1) * ρr ^ M := by nlinarith [pow_nonneg hρr0 M]
        _ < (Cr + 1) * (d / (|(b : ℝ)| * (Cr + 1))) :=
            mul_lt_mul_of_pos_left hM (by linarith)
        _ = d / |(b : ℝ)| := by field_simp
    exact lt_of_le_of_lt (le_trans (hdecay m hmr) h2) h3
  linarith

/-- **L9 (nondegeneracy).**  Past `n₁`, for every rational `a/b` (`b ≠ 0`), the three
consecutive integer linear forms `Q_m a − P_m b`, `m = t, t+1, t+2`, are not all zero.

Every hypothesis is one of the chain's own links, in the vocabulary its row produces:

* `hrecq` / `hrecp` — **L1**, the three-term recurrence, for `q` and for `p` separately
  (rows B1–B5; *not* proved anywhere yet).  Same shape as `Zeta2Instantiate.rn_growth_of_L1`.
* `hQ` / `hP` / `hΔ` — **L10's arithmetic clearing**: `Q_n = Δ_n q_n` with `Δ_n ≠ 0`.  The
  cleared integers do NOT satisfy the recurrence (the clearing factor moves with `n`), which is
  exactly why the propagation runs on `q`, `p` and transfers through `Δ`.
* `hα₃` / `hα₀` — **L4**: `P₃(n) ≠ 0` for `n ≥ n₁`, `P₀(n) ≠ 0` for `n ≥ m₀`.
* `hrow` — the finite exact residue: one index `≥ m₀` with `q ≠ 0`.  On the candidate this is
  `q_1127 ≠ 0` (20,567 digits), row D4-L4.
  **CORRECTED 2026-09-09: this line used to end "it is NOT in the repo", and that absence is
  over.**  Row D4-L4 landed `external_tests/chain_close_design/results/solution_a.txt` with its
  generator `l4_data.py` (`533c3b114`, 2026-09-08), and `Zeta2L4.q1127_ne_zero` proves the
  residue in Lean, axiom-clean.  What is NOT yet available is the bridge: `Zeta2L4` states it
  about a `List ℤ` through `Zeta2L4.hornerZ`, while `hrow` below wants `q : ℕ → ℝ`, and
  `Zeta2XL1.lean` records that no `List ℤ → ℝ[X]` bridge exists anywhere in this corpus.  So
  `hrow` is still a hypothesis here — on a missing bridge, not on missing data.
* `hdecay` — **L8 + L10**, the decay of `R_n = Q_n ζ − P_n`.
* `hirr` — `Irrational ζ`, which in the final composition is FREE from
  `LiouvilleWith.irrational` (`zeta2-integral-free.md` §4). -/
theorem nondegenerate {ζ : ℝ} (hirr : Irrational ζ)
    (q p : ℕ → ℝ) (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    {N₀ n₁ m₀ Nr : ℕ} {Cr ρr : ℝ}
    (hrecq : ∀ n, N₀ ≤ n →
      α₀ n * q n + α₁ n * q (n + 1) + α₂ n * q (n + 2) + α₃ n * q (n + 3) = 0)
    (hrecp : ∀ n, N₀ ≤ n →
      α₀ n * p n + α₁ n * p (n + 1) + α₂ n * p (n + 2) + α₃ n * p (n + 3) = 0)
    (hΔ : ∀ n, Δ n ≠ 0)
    (hQ : ∀ n, (Q n : ℝ) = Δ n * q n) (hP : ∀ n, (P n : ℝ) = Δ n * p n)
    (hN₁ : N₀ ≤ n₁) (hM₀ : N₀ ≤ m₀)
    (hα₃ : ∀ n, n₁ ≤ n → α₃ n ≠ 0) (hα₀ : ∀ n, m₀ ≤ n → α₀ n ≠ 0)
    (hrow : ∃ k, m₀ ≤ k ∧ q k ≠ 0)
    (hCr : 0 ≤ Cr) (hρr0 : 0 ≤ ρr) (hρr1 : ρr < 1)
    (hdecay : ∀ n, Nr ≤ n → |(Q n : ℝ) * ζ - (P n : ℝ)| ≤ Cr * ρr ^ n) :
    ∀ t, n₁ ≤ t → ∀ a b : ℤ, b ≠ 0 →
      Q t * a - P t * b ≠ 0 ∨ Q (t + 1) * a - P (t + 1) * b ≠ 0 ∨
        Q (t + 2) * a - P (t + 2) * b ≠ 0 := by
  intro t ht a b hb
  by_contra hcon
  push Not at hcon
  obtain ⟨z0, z1, z2⟩ := hcon
  -- the real combination `s = q a − p b`, and its ℤ-image `Q a − P b = Δ · s`
  set s : ℕ → ℝ := fun n => q n * (a : ℝ) - p n * (b : ℝ) with hsdef
  have hcast : ∀ n, ((Q n * a - P n * b : ℤ) : ℝ) = Δ n * s n := by
    intro n
    push_cast
    rw [hQ n, hP n]
    simp only [hsdef]
    ring
  have hzero : ∀ n, (Q n * a - P n * b : ℤ) = 0 → s n = 0 := by
    intro n hn
    have h := hcast n
    rw [hn] at h
    simp only [Int.cast_zero] at h
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' (hΔ n)
    · exact h'
  have hsrec : ∀ n, N₀ ≤ n →
      α₀ n * s n + α₁ n * s (n + 1) + α₂ n * s (n + 2) + α₃ n * s (n + 3) = 0 := by
    intro n hn
    have hq := hrecq n hn
    have hp := hrecp n hn
    simp only [hsdef]
    linear_combination (a : ℝ) * hq - (b : ℝ) * hp
  -- forward propagation from `t`
  have hfwd : ∀ m, t ≤ m → s m = 0 :=
    forward_vanishing s α₀ α₁ α₂ α₃ N₀ t hsrec (le_trans hN₁ ht)
      (fun n hn => hα₃ n (le_trans ht hn)) (hzero t z0) (hzero (t + 1) z1) (hzero (t + 2) z2)
  have hSreal : ∀ m, t ≤ m → (Q m : ℝ) * (a : ℝ) - (P m : ℝ) * (b : ℝ) = 0 := by
    intro m hm
    have h := hcast m
    rw [hfwd m hm, mul_zero] at h
    push_cast at h
    linarith [h]
  -- the decay forces the integer numerators to vanish from some point on
  obtain ⟨T, _, _, hT⟩ :=
    eventually_num_vanishes hirr Q P hCr hρr0 hρr1 hdecay hb hSreal
  have hqT : ∀ m, T ≤ m → q m = 0 := by
    intro m hm
    have h := hQ m
    rw [hT m hm] at h
    simp only [Int.cast_zero] at h
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' (hΔ m)
    · exact h'
  -- backward propagation contradicts the exact nonzero row
  obtain ⟨k, hk, hqk⟩ := hrow
  exact hqk (backward_vanishing q α₀ α₁ α₂ α₃ N₀ m₀ T hrecq hM₀ hα₀ hqT k hk)

/-! ## §3. L11 — the measure criterion

The hypotheses are exactly what the rate rows produce: an explicit `C · ρ ^ n` decay for
`R_n = Q_n ζ − P_n`, an explicit `C · ρ ^ n` growth for `Q_n`, L9, and the gap. -/

/-- **L11 (the criterion).**  Geometric decay of `R_n = Q_n ζ − P_n` at rate `ρr < 1`,
geometric growth of `Q_n` at rate `ρq ≥ 1`, L9's nondegeneracy, and the gap
`ρq · ρr ^ (p₀ − 1) < 1` give `¬ LiouvilleWith p₀ ζ`.

`ρq · ρr ^ (p₀ − 1) < 1` is `1 + v/u < p₀` written multiplicatively; `gap_of_rate_bound`
converts.  With `ρq = e^v`, `ρr = e^(−u)` and `p₀ > 1 + v/u` it is the chain's
`μ(ζ) ≤ 1 + v/u`.

**No irrationality hypothesis.**  L11 does not need one: the `x ≠ m/n` conjunct inside
`LiouvilleWith` supplies everything the estimate uses.  (L9's PROOF needs it; the criterion
does not.) -/
theorem not_liouvilleWith_of_rates {ζ : ℝ} (Q P : ℕ → ℤ) {p₀ Cr ρr Cq ρq : ℝ} {Nr Nq n₁ : ℕ}
    (hp₀ : 1 < p₀)
    (hCr : 0 < Cr) (hρr0 : 0 < ρr) (hρr1 : ρr < 1)
    (hdecay : ∀ n, Nr ≤ n → |(Q n : ℝ) * ζ - (P n : ℝ)| ≤ Cr * ρr ^ n)
    (hCq : 0 < Cq) (hρq : 1 ≤ ρq)
    (hgrowth : ∀ n, Nq ≤ n → |(Q n : ℝ)| ≤ Cq * ρq ^ n)
    (hnd : ∀ t, n₁ ≤ t → ∀ a b : ℤ, b ≠ 0 →
      Q t * a - P t * b ≠ 0 ∨ Q (t + 1) * a - P (t + 1) * b ≠ 0 ∨
        Q (t + 2) * a - P (t + 2) * b ≠ 0)
    (hgap : ρq * ρr ^ (p₀ - 1) < 1) :
    ¬ LiouvilleWith p₀ ζ := by
  classical
  intro hLiou
  obtain ⟨C, hC₀, hC⟩ := hLiou.exists_pos
  have hp1 : (0:ℝ) < p₀ - 1 := by linarith
  set N₀ : ℕ := max (max Nr Nq) n₁ with hN₀def
  set s : ℝ := ρr ^ (p₀ - 1) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hρr0 _
  have hρqpos : (0:ℝ) < ρq := by linarith
  have hθ0 : (0:ℝ) < ρq * s := mul_pos hρqpos hs0
  have h2Cr : (0:ℝ) < 2 * Cr := by linarith
  have hcrp : (0:ℝ) < (2 * Cr) ^ (p₀ - 1) := Real.rpow_pos_of_pos h2Cr _
  set K : ℝ := 2 * C * Cq * ρq ^ 3 * (2 * Cr) ^ (p₀ - 1) with hKdef
  have hK0 : 0 < K := by
    have h1 : (0:ℝ) < 2 * C * Cq := by positivity
    have h2 : (0:ℝ) < ρq ^ 3 := by positivity
    simp only [hKdef]
    exact mul_pos (mul_pos h1 h2) hcrp
  obtain ⟨I, hI⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hK0) hgap
  set base : ℕ := N₀ + I with hbasedef
  have hρrb : (0:ℝ) < ρr ^ base := pow_pos hρr0 base
  -- the one threshold on the denominator
  obtain ⟨Nth, hNth⟩ := exists_nat_gt (1 / (2 * Cr * ρr ^ base))
  obtain ⟨n, hn, hn1, m, _, hlt⟩ := ((eventually_ge_atTop Nth).and_frequently hC).exists
  have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith
  have hArg : (0:ℝ) < 2 * Cr * ρr ^ base := mul_pos h2Cr hρrb
  have hbig : 1 < (n : ℝ) * (2 * Cr * ρr ^ base) := by
    have h1 : 1 / (2 * Cr * ρr ^ base) < (n : ℝ) :=
      lt_of_lt_of_le hNth (by exact_mod_cast hn)
    exact (div_lt_iff₀ hArg).mp h1
  -- the index: the least `t` past `base` with `2·Cr·n·ρr^t ≤ 1`
  have hcn : (0:ℝ) < 2 * Cr * (n : ℝ) := mul_pos h2Cr hnpos
  have hex : ∃ k : ℕ, 2 * Cr * (n : ℝ) * ρr ^ (base + k + 1) ≤ 1 := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos one_pos hcn) hρr1
    refine ⟨N, le_of_lt ?_⟩
    have h1 : ρr ^ (base + N + 1) ≤ ρr ^ N :=
      pow_le_pow_of_le_one hρr0.le hρr1.le (by omega)
    calc 2 * Cr * (n : ℝ) * ρr ^ (base + N + 1)
        ≤ 2 * Cr * (n : ℝ) * ρr ^ N := mul_le_mul_of_nonneg_left h1 hcn.le
      _ < 2 * Cr * (n : ℝ) * (1 / (2 * Cr * (n : ℝ))) := mul_lt_mul_of_pos_left hN hcn
      _ = 1 := by field_simp
  -- `k₀` is made OPAQUE on purpose: leaving it as the `let`-bound `Nat.find hex` makes every
  -- later `positivity`/`isDefEq` try to unfold a well-founded recursion, and the file times
  -- out at `whnf` (measured, 2026-09-08).
  obtain ⟨k₀, hfind, hminf⟩ :
      ∃ k₀ : ℕ, 2 * Cr * (n : ℝ) * ρr ^ (base + k₀ + 1) ≤ 1 ∧
        ∀ j, j < k₀ → ¬ (2 * Cr * (n : ℝ) * ρr ^ (base + j + 1) ≤ 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  set i : ℕ := base + k₀ with hidef
  have hti : 2 * Cr * (n : ℝ) * ρr ^ (i + 1) ≤ 1 := hfind
  have hmin : 1 < 2 * Cr * (n : ℝ) * ρr ^ i := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
    · have hib : i = base := by omega
      rw [hib]
      linarith [hbig]
    · obtain ⟨j, hj⟩ : ∃ j, k₀ = j + 1 := ⟨k₀ - 1, by omega⟩
      have hnf := hminf j (by omega)
      push Not at hnf
      have hij : i = base + j + 1 := by omega
      rw [hij]
      exact hnf
  have hIi : I ≤ i := by omega
  have hN₀i : N₀ ≤ i := by omega
  -- every one of the three consecutive linear forms vanishes — which L9 forbids
  have hkey : ∀ j : ℕ, i + 1 ≤ j → j ≤ i + 3 → Q j * m - P j * (n : ℤ) = 0 := by
    intro j hj1 hj2
    by_contra hSj
    have hjNr : Nr ≤ j := by omega
    have hjNq : Nq ≤ j := by omega
    -- (1) the decay side
    have hRj : |(Q j : ℝ) * ζ - (P j : ℝ)| ≤ Cr * ρr ^ j := hdecay j hjNr
    have hpj : ρr ^ j ≤ ρr ^ (i + 1) := pow_le_pow_of_le_one hρr0.le hρr1.le hj1
    have hnRj : (n : ℝ) * |(Q j : ℝ) * ζ - (P j : ℝ)| ≤ 1 / 2 := by
      have hRle : |(Q j : ℝ) * ζ - (P j : ℝ)| ≤ Cr * ρr ^ (i + 1) :=
        hRj.trans (mul_le_mul_of_nonneg_left hpj hCr.le)
      have h1 : (n : ℝ) * |(Q j : ℝ) * ζ - (P j : ℝ)| ≤ (n : ℝ) * (Cr * ρr ^ (i + 1)) :=
        mul_le_mul_of_nonneg_left hRle hnpos.le
      nlinarith [hti]
    -- (2) the growth side
    have hQj : |(Q j : ℝ)| ≤ Cq * ρq ^ (i + 3) := by
      have h1 : ρq ^ j ≤ ρq ^ (i + 3) := pow_le_pow_right₀ hρq hj2
      exact (hgrowth j hjNq).trans (mul_le_mul_of_nonneg_left h1 hCq.le)
    -- (3) the integer linear form is at least 1 in absolute value
    have h1S : (1:ℝ) ≤ |(Q j : ℝ) * (m : ℝ) - (P j : ℝ) * (n : ℝ)| := by
      have hz : (1 : ℤ) ≤ |Q j * m - P j * (n : ℤ)| := Int.one_le_abs hSj
      calc (1:ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|Q j * m - P j * (n : ℤ)| : ℤ) : ℝ) := by exact_mod_cast hz
        _ = |(Q j : ℝ) * (m : ℝ) - (P j : ℝ) * (n : ℝ)| := by push_cast; ring_nf
    -- (4) split it
    have hid : (Q j : ℝ) * (m : ℝ) - (P j : ℝ) * (n : ℝ)
        = (-(Q j : ℝ)) * ((n : ℝ) * ζ - (m : ℝ))
          + (n : ℝ) * ((Q j : ℝ) * ζ - (P j : ℝ)) := by ring
    have hnm : (n : ℝ) * ζ - (m : ℝ) = (n : ℝ) * (ζ - (m : ℝ) / (n : ℝ)) := by
      field_simp
    have htri : |(Q j : ℝ) * (m : ℝ) - (P j : ℝ) * (n : ℝ)|
        ≤ |(Q j : ℝ)| * ((n : ℝ) * |ζ - (m : ℝ) / (n : ℝ)|)
          + (n : ℝ) * |(Q j : ℝ) * ζ - (P j : ℝ)| := by
      rw [hid]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hnpos.le, hnm, abs_mul,
        abs_of_nonneg hnpos.le]
    have hhalf : (1:ℝ) / 2 ≤ |(Q j : ℝ)| * ((n : ℝ) * |ζ - (m : ℝ) / (n : ℝ)|) := by
      linarith
    -- (5) feed in the Liouville inequality
    have hWpos : (0:ℝ) < (n : ℝ) ^ (p₀ - 1) := Real.rpow_pos_of_pos hnpos _
    have hW : (n : ℝ) ^ (p₀ - 1) * (n : ℝ) = (n : ℝ) ^ p₀ := by
      have h1 : (n : ℝ) ^ (p₀ - 1) * (n : ℝ) ^ (1:ℝ) = (n : ℝ) ^ (p₀ - 1 + 1) :=
        (Real.rpow_add hnpos _ _).symm
      rw [Real.rpow_one] at h1
      rw [h1]
      congr 1
      ring
    have hupper : (n : ℝ) ^ (p₀ - 1) ≤ 2 * C * |(Q j : ℝ)| := by
      have hlt' : |ζ - (m : ℝ) / (n : ℝ)| ≤ C / ((n : ℝ) ^ (p₀ - 1) * (n : ℝ)) := by
        rw [hW]; exact hlt.le
      have hstep : |(Q j : ℝ)| * ((n : ℝ) * |ζ - (m : ℝ) / (n : ℝ)|)
          ≤ |(Q j : ℝ)| * ((n : ℝ) * (C / ((n : ℝ) ^ (p₀ - 1) * (n : ℝ)))) := by
        gcongr
      have h3 : (n : ℝ) * (C / ((n : ℝ) ^ (p₀ - 1) * (n : ℝ))) = C / (n : ℝ) ^ (p₀ - 1) := by
        field_simp
      rw [h3] at hstep
      have h4 : (1:ℝ) / 2 ≤ |(Q j : ℝ)| * C / (n : ℝ) ^ (p₀ - 1) := by
        rw [mul_div_assoc]
        linarith
      have h5 : (1:ℝ) / 2 * (n : ℝ) ^ (p₀ - 1) ≤ |(Q j : ℝ)| * C := (le_div_iff₀ hWpos).mp h4
      linarith
    -- (6) the lower bound on `n ^ (p₀ - 1)` from minimality of the index
    have hAi : (0:ℝ) < 2 * Cr * ρr ^ i := mul_pos h2Cr (pow_pos hρr0 i)
    have hinvlt : (2 * Cr * ρr ^ i)⁻¹ < (n : ℝ) := by
      rw [inv_lt_iff_one_lt_mul₀ hAi]
      linarith [hmin]
    have hrl : ((2 * Cr * ρr ^ i) ^ (p₀ - 1))⁻¹ < (n : ℝ) ^ (p₀ - 1) := by
      have h1 : ((2 * Cr * ρr ^ i)⁻¹) ^ (p₀ - 1) < (n : ℝ) ^ (p₀ - 1) :=
        Real.rpow_lt_rpow (inv_pos.mpr hAi).le hinvlt hp1
      rwa [Real.inv_rpow hAi.le] at h1
    have hprod : (2 * Cr * ρr ^ i) ^ (p₀ - 1) = (2 * Cr) ^ (p₀ - 1) * s ^ i := by
      rw [Real.mul_rpow h2Cr.le (pow_pos hρr0 i).le, rpow_natPow_comm hρr0.le i (p₀ - 1)]
    -- (7) put the two sides together
    have hspos : (0:ℝ) < (2 * Cr) ^ (p₀ - 1) * s ^ i := mul_pos hcrp (pow_pos hs0 i)
    have hcombine : 1 < K * (ρq * s) ^ i := by
      have hL : ((2 * Cr) ^ (p₀ - 1) * s ^ i)⁻¹ < 2 * C * (Cq * ρq ^ (i + 3)) := by
        rw [hprod] at hrl
        have h2 : 2 * C * |(Q j : ℝ)| ≤ 2 * C * (Cq * ρq ^ (i + 3)) :=
          mul_le_mul_of_nonneg_left hQj (by linarith)
        linarith
      rw [inv_lt_iff_one_lt_mul₀ hspos] at hL
      calc (1:ℝ) < 2 * C * (Cq * ρq ^ (i + 3)) * ((2 * Cr) ^ (p₀ - 1) * s ^ i) := hL
        _ = K * (ρq * s) ^ i := by rw [hKdef, mul_pow]; ring
    have hsmall : K * (ρq * s) ^ i ≤ 1 := by
      have h1 : (ρq * s) ^ i ≤ (ρq * s) ^ I :=
        pow_le_pow_of_le_one hθ0.le hgap.le hIi
      have h2 : K * (ρq * s) ^ i ≤ K * (ρq * s) ^ I := mul_le_mul_of_nonneg_left h1 hK0.le
      have h3 : K * (ρq * s) ^ I < K * K⁻¹ := mul_lt_mul_of_pos_left hI hK0
      have h4 : K * K⁻¹ = 1 := mul_inv_cancel₀ hK0.ne'
      linarith
    linarith
  -- L9 says one of the three is nonzero
  have hbne : (n : ℤ) ≠ 0 := by
    have : 0 < n := hn1
    omega
  have hn₁t : n₁ ≤ i + 1 := by omega
  rcases hnd (i + 1) hn₁t m (n : ℤ) hbne with h | h | h
  · exact h (hkey (i + 1) (le_refl _) (by omega))
  · exact h (hkey (i + 2) (by omega) (by omega))
  · exact h (hkey (i + 3) (by omega) (by omega))

/-! ## §4. The composition — L9 and L11 together, with irrationality free

`zeta2-integral-free.md` §4: proving `¬ LiouvilleWith p₀ ζ` starts by assuming
`LiouvilleWith p₀ ζ`, and `LiouvilleWith.irrational` then hands back `Irrational ζ` in the only
branch that exists.  So L9's irrationality input costs nothing here — it is discharged from the
very hypothesis being refuted. -/

/-- **D3, assembled.**  The chain's own inputs — L1, L4, L10's clearing, the exact row, L8's
decay, L5+L10's growth, and the gap — give `¬ LiouvilleWith p₀ ζ` with NO irrationality
hypothesis, because L9's copy of it is manufactured from the negated goal. -/
theorem not_liouvilleWith_of_chain {ζ : ℝ}
    (q p : ℕ → ℝ) (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) (α₀ α₁ α₂ α₃ : ℕ → ℝ)
    {N₀ n₁ m₀ Nr Nq : ℕ} {p₀ Cr ρr Cq ρq : ℝ}
    (hp₀ : 1 < p₀)
    (hrecq : ∀ n, N₀ ≤ n →
      α₀ n * q n + α₁ n * q (n + 1) + α₂ n * q (n + 2) + α₃ n * q (n + 3) = 0)
    (hrecp : ∀ n, N₀ ≤ n →
      α₀ n * p n + α₁ n * p (n + 1) + α₂ n * p (n + 2) + α₃ n * p (n + 3) = 0)
    (hΔ : ∀ n, Δ n ≠ 0)
    (hQ : ∀ n, (Q n : ℝ) = Δ n * q n) (hP : ∀ n, (P n : ℝ) = Δ n * p n)
    (hN₁ : N₀ ≤ n₁) (hM₀ : N₀ ≤ m₀)
    (hα₃ : ∀ n, n₁ ≤ n → α₃ n ≠ 0) (hα₀ : ∀ n, m₀ ≤ n → α₀ n ≠ 0)
    (hrow : ∃ k, m₀ ≤ k ∧ q k ≠ 0)
    (hCr : 0 < Cr) (hρr0 : 0 < ρr) (hρr1 : ρr < 1)
    (hdecay : ∀ n, Nr ≤ n → |(Q n : ℝ) * ζ - (P n : ℝ)| ≤ Cr * ρr ^ n)
    (hCq : 0 < Cq) (hρq : 1 ≤ ρq)
    (hgrowth : ∀ n, Nq ≤ n → |(Q n : ℝ)| ≤ Cq * ρq ^ n)
    (hgap : ρq * ρr ^ (p₀ - 1) < 1) :
    ¬ LiouvilleWith p₀ ζ := by
  intro hLiou
  have hirr : Irrational ζ := hLiou.irrational hp₀
  have hnd := nondegenerate hirr q p Q P Δ α₀ α₁ α₂ α₃ hrecq hrecp hΔ hQ hP hN₁ hM₀
    hα₃ hα₀ hrow hCr.le hρr0.le hρr1 hdecay
  exact not_liouvilleWith_of_rates Q P hp₀ hCr hρr0 hρr1 hdecay hCq hρq hgrowth hnd hgap hLiou

/-- The headline shape of `zeta2-integral-free.md` §5.1: `mono` upgrades the single exponent to
every larger one, so the chain only ever has to prove ONE statement. -/
theorem measure_le_of_not_liouvilleWith {ζ p₀ : ℝ} (h : ¬ LiouvilleWith p₀ ζ) :
    ∀ p : ℝ, p₀ ≤ p → ¬ LiouvilleWith p ζ :=
  fun _ hp hL => h (hL.mono hp)

/-- **Rate transfer through the arithmetic clearing.**  The chain never has a geometric bound
on `Q_n ζ − P_n` directly: it has one on `r_n = q_n ζ − p_n` (rows L7/L8) and a SEPARATE one on
the clearing factor `Δ_n` (row L10, the PNT-class limits), and `Q_n ζ − P_n = Δ_n · r_n`.  The
two rates multiply, which is the only reason `u = C0 − C2̃` and `v = C1 + C2̃` are the constants
the headline is built from.

Stated for a general product so it serves both the decay leg (`y = r`) and the growth leg
(`y = q`). -/
theorem clearing_rate {y Δ : ℕ → ℝ} {Cy ρy CΔ ρΔ : ℝ} {Ny NΔ : ℕ}
    (hCΔ : 0 ≤ CΔ) (hρΔ : 0 ≤ ρΔ)
    (hy : ∀ n, Ny ≤ n → |y n| ≤ Cy * ρy ^ n)
    (hΔ : ∀ n, NΔ ≤ n → |Δ n| ≤ CΔ * ρΔ ^ n) :
    ∀ n, max Ny NΔ ≤ n → |Δ n * y n| ≤ Cy * CΔ * (ρy * ρΔ) ^ n := by
  intro n hn
  rw [abs_mul, mul_pow]
  calc |Δ n| * |y n| ≤ (CΔ * ρΔ ^ n) * (Cy * ρy ^ n) :=
        mul_le_mul (hΔ n (le_trans (le_max_right _ _) hn))
          (hy n (le_trans (le_max_left _ _) hn)) (abs_nonneg _)
          (mul_nonneg hCΔ (pow_nonneg hρΔ n))
    _ = Cy * CΔ * (ρy ^ n * ρΔ ^ n) := by ring

/-! ## §5. The bridge from the chain's `1 + v/u` vocabulary -/

/-- `1 + v/u < p₀` (the chain's `μ ≤ 1 + v/u`, with strict room) is the multiplicative gap
`e^v · (e^(−u)) ^ (p₀ − 1) < 1` that `not_liouvilleWith_of_rates` consumes.

This is the ONLY place a logarithm/exponential appears in row D3, and it is deliberately
isolated here: the criterion's proof never divides one rate by another. -/
theorem gap_of_rate_bound {u v p₀ : ℝ} (hu : 0 < u) (h : 1 + v / u < p₀) :
    Real.exp v * (Real.exp (-u)) ^ (p₀ - 1) < 1 := by
  have hvu : v < u * (p₀ - 1) := by
    have h1 : v / u < p₀ - 1 := by linarith
    calc v = v / u * u := by field_simp
      _ < (p₀ - 1) * u := mul_lt_mul_of_pos_right h1 hu
      _ = u * (p₀ - 1) := by ring
  have h1 : (Real.exp (-u)) ^ (p₀ - 1) = Real.exp (-u * (p₀ - 1)) := by
    rw [← Real.exp_mul]
  rw [h1, ← Real.exp_add]
  have : v + -u * (p₀ - 1) < 0 := by nlinarith
  calc Real.exp (v + -u * (p₀ - 1)) < Real.exp 0 := Real.exp_lt_exp.mpr this
    _ = 1 := Real.exp_zero

/-! ## §6. Edges — three hypotheses that look droppable and are not

`LEAN.md` §5: a lemma false at an edge point elaborates fine and sits there until something
uses it.  Each of these is a positive theorem, so nobody can "simplify" the hypothesis away
without turning a green file red. -/

/-- **`b ≠ 0` is load-bearing in L9.**  At `a = b = 0` every linear form in the chain vanishes,
whatever `Q` and `P` are — so L9's conclusion is FALSE without a nondegeneracy assumption on the
pair, and `b ≠ 0` (the denominator of a rational) is the form the criterion supplies. -/
theorem l9_needs_b_ne_zero (Q P : ℕ → ℤ) (t : ℕ) :
    Q t * 0 - P t * 0 = 0 ∧ Q (t + 1) * 0 - P (t + 1) * 0 = 0 ∧
      Q (t + 2) * 0 - P (t + 2) * 0 = 0 := by
  refine ⟨by ring, by ring, by ring⟩

/-- **The `n = 0` denominator inside `LiouvilleWith` is vacuous, not dangerous.**  `m / 0 = 0`
and `C / 0 ^ p = C / 0 = 0` in Lean's junk-value convention, so the inner condition asks for
`|x| < 0` and can never hold.  This is why `LiouvilleWith.exists_pos`'s extra `1 ≤ n` — which
`not_liouvilleWith_of_rates` leans on for `n·(ζ − m/n) = nζ − m` — costs nothing. -/
theorem liouville_denominator_zero_vacuous (x C pe : ℝ) (hpe : pe ≠ 0) (m : ℤ) :
    ¬ (x ≠ (m : ℝ) / ((0 : ℕ) : ℝ) ∧ |x - (m : ℝ) / ((0 : ℕ) : ℝ)| < C / ((0 : ℕ) : ℝ) ^ pe) := by
  rintro ⟨-, h2⟩
  rw [Nat.cast_zero, Real.zero_rpow hpe, div_zero, div_zero] at h2
  exact absurd h2 (not_lt.mpr (abs_nonneg _))

/-- **`ρq ≥ 1` is not cosmetic.**  L11 bounds `|Q_j|` for `j` in a three-wide window by its
value at the RIGHT end, which needs the growth base to be at least `1`.  Here is the fact, so
that weakening the hypothesis to `0 < ρq` makes the file red rather than making the proof
subtly wrong. -/
theorem growth_window_needs_one_le (ρq : ℝ) (hρq : 1 ≤ ρq) (i j : ℕ) (hj : j ≤ i + 3) :
    ρq ^ j ≤ ρq ^ (i + 3) :=
  pow_le_pow_right₀ hρq hj

/-! ## Receipts

`LEAN.md` §1: `#print axioms` is the only attestation, and `exit 0` is not.  Every line below
must read `[propext, Classical.choice, Quot.sound]`; a `sorryAx` anywhere is a failed run. -/

#print axioms rpow_natPow_comm
#print axioms forward_vanishing
#print axioms backward_vanishing
#print axioms eventually_num_vanishes
#print axioms nondegenerate
#print axioms not_liouvilleWith_of_rates
#print axioms not_liouvilleWith_of_chain
#print axioms measure_le_of_not_liouvilleWith
#print axioms clearing_rate
#print axioms gap_of_rate_bound
#print axioms l9_needs_b_ne_zero
#print axioms liouville_denominator_zero_vacuous
#print axioms growth_window_needs_one_le

end Zeta2L9L11
