/-
D5 LEG B, part 1: the block decomposition — the combinatorial skeleton.

Leg B is  log Phi~_n = sum_p phi~({n/p}) log p  ~  n * d_phi~,  where the weight is a step
function of the FRACTIONAL PART {n/p}. The whole method rests on partitioning the primes by
k = floor(n/p): on each block the fractional part is n/p - k, an honest real function of p, and
the block's p-range is (n/(k+1), n/k].

Mathlib has no Dirichlet hyperbola method (an explicit `--TODO` in ArithmeticFunction/Misc.lean),
so this decomposition is built here. What it DOES have is `Finset.sum_fiberwise_of_maps_to`,
which is exactly the partition-by-fibre step; the content below is packaging it for `k = n / p`
plus the identification of each fibre as an interval of `p`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Zeta2LegB

open Finset

/-- **Block decomposition.** Any sum over a finite set of `p` splits into the fibres of
`p ↦ n / p` (natural division), i.e. into the blocks on which `⌊n/p⌋` is constant. -/
theorem sum_eq_sum_blocks (n : ℕ) (S : Finset ℕ) (K : ℕ) (f : ℕ → ℝ)
    (hK : ∀ p ∈ S, n / p ≤ K) :
    ∑ p ∈ S, f p
      = ∑ k ∈ Finset.range (K + 1), ∑ p ∈ S.filter (fun p => n / p = k), f p := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => n / p) (t := Finset.range (K + 1))]
  intro p hp
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hK p hp))

/-- **The fibre is an interval.** For `p ≥ 1`, `⌊n/p⌋ = k` exactly when `k·p ≤ n < (k+1)·p`,
i.e. `p` lies in the block `(n/(k+1), n/k]`. -/
theorem mem_block_iff (n p k : ℕ) (hp : 0 < p) :
    n / p = k ↔ k * p ≤ n ∧ n < (k + 1) * p := by
  constructor
  · rintro rfl
    exact ⟨Nat.div_mul_le_self n p, (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)⟩
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 h2

/-- On the block `⌊n/p⌋ = k`, the fractional part is the honest real function `n/p − k`. -/
theorem fract_on_block (n p k : ℕ) (hp : 0 < p) (hk : n / p = k) :
    Int.fract ((n : ℝ) / p) = (n : ℝ) / p - k := by
  have hb := (mem_block_iff n p k hp).mp hk
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hfloor : ⌊(n : ℝ) / (p : ℝ)⌋ = (k : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hppos]
      exact_mod_cast hb.1
    · rw [div_lt_iff₀ hppos]
      push_cast
      exact_mod_cast hb.2
  rw [Int.fract, hfloor]
  push_cast
  ring

/-- **The interval-to-`θ` bridge.** On the block `⌊n/p⌋ = k`, the condition `{n/p} ∈ [a,b)` is
exactly membership of `p` in the interval `(n/(k+b), n/(k+a)]`. This is what turns the step-function
weight into a difference of `θ`-values: the block's contribution to `∑ φ̃({n/p}) log p` is
`v · [θ(n/(k+a)) − θ(n/(k+b))]`. -/
theorem block_fract_iff (n p k : ℕ) (hp : 0 < p) (hk : n / p = k) (a b : ℝ)
    (hka : 0 < (k : ℝ) + a) (hkb : 0 < (k : ℝ) + b) :
    Int.fract ((n : ℝ) / p) ∈ Set.Ico a b ↔
      (n : ℝ) / ((k : ℝ) + b) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) / ((k : ℝ) + a) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hA : (a ≤ (n : ℝ) / (p : ℝ) - (k : ℝ)) ↔ ((k : ℝ) + a) * (p : ℝ) ≤ (n : ℝ) := by
    rw [le_sub_iff_add_le, le_div_iff₀ hppos]
    ring_nf
  have hB : ((n : ℝ) / (p : ℝ) - (k : ℝ) < b) ↔ (n : ℝ) < ((k : ℝ) + b) * (p : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hppos]
    ring_nf
  have hC : ((n : ℝ) / ((k : ℝ) + b) < (p : ℝ)) ↔ (n : ℝ) < ((k : ℝ) + b) * (p : ℝ) := by
    rw [div_lt_iff₀ hkb]
    ring_nf
  have hD : ((p : ℝ) ≤ (n : ℝ) / ((k : ℝ) + a)) ↔ ((k : ℝ) + a) * (p : ℝ) ≤ (n : ℝ) := by
    rw [le_div_iff₀ hka]
    ring_nf
  rw [fract_on_block n p k hp hk, Set.mem_Ico, hA, hB, hC, hD]
  tauto

/-- **The interval alone determines the block** — provided `0 ≤ a` and `b ≤ 1`, which our profile
satisfies (`φ̃` lives on `[0,1)`).

This is a real simplification of the method: the blocks `(n/(k+b), n/(k+a)]` are AUTOMATICALLY
disjoint across `k`, so the sum over `{p : {n/p} ∈ [a,b)}` splits into `θ`-differences with NO
separate `⌊n/p⌋ = k` filter to carry. The fiberwise machinery of `sum_eq_sum_blocks` is then a
convenience rather than a necessity. -/
theorem block_of_mem_interval (n p k : ℕ) (hp : 0 < p) (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (h1 : (n : ℝ) / ((k : ℝ) + b) < (p : ℝ)) (h2 : (p : ℝ) ≤ (n : ℝ) / ((k : ℝ) + a))
    (hka : 0 < (k : ℝ) + a) (hkb : 0 < (k : ℝ) + b) :
    n / p = k := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [mem_block_iff n p k hp]
  constructor
  · -- `k * p ≤ (k+a) * p ≤ n`
    have hle : (p : ℝ) * ((k : ℝ) + a) ≤ (n : ℝ) := (le_div_iff₀ hka).mp h2
    have hgoal : ((k : ℝ)) * (p : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast hgoal
  · -- `n < (k+b) * p ≤ (k+1) * p`
    have hlt : (n : ℝ) < (p : ℝ) * ((k : ℝ) + b) := (div_lt_iff₀ hkb).mp h1
    have hgoal : (n : ℝ) < ((k : ℝ) + 1) * (p : ℝ) := by nlinarith
    exact_mod_cast hgoal

/-! ### The first ANALYTIC step: `p`-intervals become `θ`-differences -/

/-- **`θ`-difference over an interval.** `θ(y) − θ(x)` is the sum of `log p` over the primes in
`(⌊x⌋, ⌊y⌋]`. This is what lets §4's `p`-intervals be fed to the PNT input: the block's
contribution to `∑ φ̃({n/p}) log p` becomes `v · [θ(n/(k+a)) − θ(n/(k+b))]`. -/
theorem theta_sub_theta (x y : ℝ) (hxy : ⌊x⌋₊ ≤ ⌊y⌋₊) :
    Chebyshev.theta y - Chebyshev.theta x
      = ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with p.Prime, Real.log p := by
  rw [Chebyshev.theta, Chebyshev.theta, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊x⌋₊) hxy]
  ring

/-- **The block's `p`-set IS the `θ`-difference's index set.** Combining `block_fract_iff`
(interval ⇒ fract) and `block_of_mem_interval` (interval ⇒ block), membership in the block with
`{n/p} ∈ [a,b)` is exactly `p ∈ (⌊n/(k+b)⌋, ⌊n/(k+a)⌋]` — the index set of `theta_sub_theta`.

With this, item (1) of the design's open list is closed: the block's contribution to
`∑ φ̃({n/p}) log p` is literally `v · [θ(n/(k+a)) − θ(n/(k+b))]`. -/
theorem mem_block_interval_iff (n p k : ℕ) (hp : 0 < p) (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hka : 0 < (k : ℝ) + a) (hkb : 0 < (k : ℝ) + b) :
    (n / p = k ∧ Int.fract ((n : ℝ) / p) ∈ Set.Ico a b)
      ↔ p ∈ Finset.Ioc ⌊(n : ℝ) / ((k : ℝ) + b)⌋₊ ⌊(n : ℝ) / ((k : ℝ) + a)⌋₊ := by
  have hnb : (0 : ℝ) ≤ (n : ℝ) / ((k : ℝ) + b) := by positivity
  have hna : (0 : ℝ) ≤ (n : ℝ) / ((k : ℝ) + a) := by positivity
  rw [Finset.mem_Ioc, Nat.floor_lt hnb, Nat.le_floor_iff hna]
  constructor
  · rintro ⟨hk, hfr⟩
    exact (block_fract_iff n p k hp hk a b hka hkb).mp hfr
  · rintro ⟨h1, h2⟩
    have hk : n / p = k := block_of_mem_interval n p k hp a b ha hb h1 h2 hka hkb
    exact ⟨hk, (block_fract_iff n p k hp hk a b hka hkb).mpr ⟨h1, h2⟩⟩

/-! ### Item (3): the error control

The design doc's §1 shows the error sum over `K ≈ √n` blocks is what forces `E(x) = o(x/log x)`:
the weights `1/(k+a)` sum to a HARMONIC sum, contributing one logarithm. The lemma below isolates
that step exactly — it converts a uniform relative bound on `E` into `δ · n · (harmonic sum)`, and
`Mathlib`'s `harmonic_le_one_add_log` is then what supplies the logarithm to be beaten.

`E` and `δ` are parameters rather than `θ − id` and MediumPNT's rate, because our chain compiles
against CURRENT Mathlib while PNT+ is on a different toolchain — the hypothesis form recorded in
the owner ruling. `MediumPNT` discharges `hE` with `δ = C·exp(−c(log x₀)^{1/10})`. -/

/-- **The block error bound.** A uniform relative bound on `E` above a threshold, applied across
the blocks, costs exactly the harmonic weight `∑ 1/(k+a)`. -/
theorem block_error_bound (n K : ℕ) (a : ℝ) (δ x₀ : ℝ) (E : ℝ → ℝ)
    (hE : ∀ x, x₀ ≤ x → |E x| ≤ δ * x)
    (hlow : ∀ k ∈ Finset.range (K + 1), x₀ ≤ (n : ℝ) / ((k : ℝ) + a)) :
    |∑ k ∈ Finset.range (K + 1), E ((n : ℝ) / ((k : ℝ) + a))|
      ≤ δ * (n : ℝ) * ∑ k ∈ Finset.range (K + 1), 1 / ((k : ℝ) + a) := by
  calc |∑ k ∈ Finset.range (K + 1), E ((n : ℝ) / ((k : ℝ) + a))|
      ≤ ∑ k ∈ Finset.range (K + 1), |E ((n : ℝ) / ((k : ℝ) + a))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (K + 1), δ * ((n : ℝ) / ((k : ℝ) + a)) :=
        Finset.sum_le_sum fun k hk => hE _ (hlow k hk)
    _ = δ * (n : ℝ) * ∑ k ∈ Finset.range (K + 1), 1 / ((k : ℝ) + a) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- **The harmonic weight is the logarithm to beat.** `∑_{k≤K} 1/(k+a) ≤ 1/a + harmonic K`, and
Mathlib's `harmonic_le_one_add_log` gives `harmonic K ≤ 1 + log K`.

Composed with `block_error_bound`, the total error is `≤ δ·n·(1/a + 1 + log K)`. With `K ≈ √n`
that is `≍ δ·n·log n`, which is **exactly** the design's §1 computation: it is `o(n)` iff
`δ·log n → 0`, i.e. iff `E(x) = o(x/log x)`. Bare PNT does not give that; `MediumPNT` does, with
`δ = C·exp(−c(log x₀)^{1/10})` beating every power of `1/log`. -/
theorem harmonic_weight_bound (K : ℕ) (a : ℝ) (ha : 0 < a) :
    ∑ k ∈ Finset.range (K + 1), 1 / ((k : ℝ) + a) ≤ 1 / a + (harmonic K : ℝ) := by
  rw [Finset.sum_range_succ']
  have hharm : (harmonic K : ℝ) = ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by
    rw [harmonic]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [one_div]
  have hterm : ∀ k ∈ Finset.range K,
      1 / (((k : ℕ) + 1 : ℕ) + a : ℝ) ≤ 1 / ((k : ℝ) + 1) := by
    intro k _
    refine one_div_le_one_div_of_le (by positivity) ?_
    push_cast
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [hharm]
  simp only [Nat.cast_zero, zero_add]
  linarith [hsum]

/-- **MediumPNT's error rate beats the logarithm** — the decisive analytic fact for leg B.

`harmonic_weight_bound` shows the error carries a factor `log K ≍ log n`. `MediumPNT` supplies
`δ_n ≍ exp(−c·(log √n)^{1/10})`, so the product to kill is `u · exp(−c·u^{1/10})` at `u = log n`.
This is where bare PNT dies (its `δ` is merely `o(1)`, and `o(1)·log n` need not vanish) and where
MediumPNT survives with room.

Proved in CURRENT Mathlib with no PNT+ dependency: substituting `v = u^{1/10}` turns it into
`v^10·exp(−c·v)`, which is `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`. -/
theorem error_rate_beats_log (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun u : ℝ => u * Real.exp (-c * u ^ ((1 : ℝ) / 10)))
      Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun v : ℝ => v ^ (10 : ℝ) * Real.exp (-c * v))
      Filter.atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 10 c hc
  have hv : Filter.Tendsto (fun u : ℝ => u ^ ((1 : ℝ) / 10)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  refine (hg.comp hv).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
  have hid : (u ^ ((1 : ℝ) / 10)) ^ (10 : ℝ) = u := by
    rw [← Real.rpow_mul hu]
    norm_num
  simp only [Function.comp_apply, hid]

/-! ### The density series

`d_phi~` is `sum_i v_i * S(a_i, b_i)` with `S(a,b) = sum_k [1/(k+a) - 1/(k+b)]`.

NOTE — the digamma closed form `S(a,b) = psi(b) - psi(a)` is NOT needed in Lean. It is how the
NUMBER is computed (exactly, by the landed rational/digamma engine), but the limit statement only
needs the series to converge and to be the limit of the block main terms. That removes a digamma
asymptotic (`psi(a+N) - psi(b+N) -> 0`) that Mathlib does not have.

Convergence is proved WITHOUT comparison to `sum 1/k^2`: the terms are dominated by the
telescoping `1/(k+a) - 1/(k+a+1)`, valid because `b <= a+1` (our profile has `a, b` in `[0,1]`),
whose partial sums are `1/a - 1/(N+a) <= 1/a`. -/

/-- Each term of the density series is nonnegative. -/
theorem density_term_nonneg (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    0 ≤ 1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b) := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : (0 : ℝ) < (k : ℝ) + a := by linarith
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le h1 (by linarith)

/-- Every partial sum of the density series is bounded by `1/a`, via the telescoping
domination `1/(k+a) − 1/(k+b) ≤ 1/(k+a) − 1/(k+1+a)` (valid because `b ≤ a+1`). -/
theorem density_partial_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b)) ≤ 1 / a := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  calc ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b))
        ≤ ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + a) - 1 / (((k : ℝ) + 1) + a)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          have h1 : (0 : ℝ) < (k : ℝ) + b := by linarith
          have h2 : (1 : ℝ) / (((k : ℝ) + 1) + a) ≤ 1 / ((k : ℝ) + b) :=
            one_div_le_one_div_of_le h1 (by linarith)
          linarith
      _ = 1 / a - 1 / ((N : ℝ) + a) := by
          have h := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + a)) N
          simp only [Nat.cast_zero, zero_add] at h
          push_cast at h ⊢
          exact h
      _ ≤ 1 / a := by
          have hN : (0 : ℝ) < (N : ℝ) + a := by
            have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
            linarith
          have := one_div_pos.mpr hN
          linarith

/-- The density series converges. -/
theorem summable_density (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b)) :=
  summable_of_sum_range_le (density_term_nonneg a b ha hab) (density_partial_le a b ha hab hb1)

/-- `S(a,b) ≤ 1/a`. -/
theorem density_tsum_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    ∑' k : ℕ, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b)) ≤ 1 / a :=
  Real.tsum_le_of_sum_range_le (density_term_nonneg a b ha hab)
    (density_partial_le a b ha hab hb1)

/-- **Item (2): the density tail is `O(1/K)`.** Shifting the index by `K+1` turns the tail into a
density series with parameters `(K+1+a, K+1+b)`, whose sum `density_tsum_le` bounds by
`1/(K+1+a)`.

This is what makes the main term work: the block sum's main part is
`n · ∑_{k≤K}[1/(k+a) − 1/(k+b)]`, so the gap from `n · S(a,b)` is `n · tail_K ≤ n/(K+1+a)`. With
`K ≈ √n` that is `O(√n) = o(n)` — comfortably inside budget, and NOT the place where the
logarithm bites (that is the error term, §4's `harmonic_weight_bound`). -/
theorem density_tail_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) (K : ℕ) :
    ∑' k : ℕ, (1 / ((k : ℝ) + ((K : ℝ) + 1 + a)) - 1 / ((k : ℝ) + ((K : ℝ) + 1 + b)))
      ≤ 1 / ((K : ℝ) + 1 + a) := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  refine density_tsum_le _ _ (by linarith) (by linarith) (by linarith)

/-! ### The join: block sums = main term + error

This is where the three strands meet. Writing `θ(x) = x + (θ(x) − x)`, the summed block
contributions split into

* a MAIN TERM `n · ∑_{k≤K}[1/(k+a) − 1/(k+b)]`, whose gap from `n·S(a,b)` is controlled by
  `density_tail_le` at `O(√n)`, and
* an ERROR `∑_{k≤K}[E(n/(k+a)) − E(n/(k+b))]`, controlled by `block_error_bound` ×
  `harmonic_weight_bound` at `δ·n·log K`, which `error_rate_beats_log` kills.

The identity itself is pure rearrangement — no hypothesis on `θ` at all, because `E` is taken as
`θ − id` rather than supplied. -/

/-- **The block-sum decomposition.** -/
theorem block_sum_split (n K : ℕ) (a b : ℝ) :
    ∑ k ∈ Finset.range (K + 1),
        (Chebyshev.theta ((n : ℝ) / ((k : ℝ) + a))
          - Chebyshev.theta ((n : ℝ) / ((k : ℝ) + b)))
      = (n : ℝ) * (∑ k ∈ Finset.range (K + 1), (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b)))
        + ∑ k ∈ Finset.range (K + 1),
            ((Chebyshev.theta ((n : ℝ) / ((k : ℝ) + a)) - (n : ℝ) / ((k : ℝ) + a))
              - (Chebyshev.theta ((n : ℝ) / ((k : ℝ) + b)) - (n : ℝ) / ((k : ℝ) + b))) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The assembled single-interval bound.** The block sum is within `δ·n·(H_a + H_b)` of its main
term `n·∑[1/(k+a) − 1/(k+b)]`, where `H_x = ∑_{k≤K} 1/(k+x)`.

This is `block_sum_split` with `block_error_bound` applied to each of the two legs. Composed with
`harmonic_weight_bound` (giving `H_x ≤ 1/x + 1 + log K`), `density_tail_le` (main term to
`n·S(a,b)`) and `error_rate_beats_log` (killing `δ·log K`), it is leg B for ONE interval of the
profile — item (4) is then the outer loop over the 26 of them. -/
theorem block_sum_close (n K : ℕ) (a b δ x₀ : ℝ)
    (hE : ∀ x, x₀ ≤ x → |Chebyshev.theta x - x| ≤ δ * x)
    (hlowa : ∀ k ∈ Finset.range (K + 1), x₀ ≤ (n : ℝ) / ((k : ℝ) + a))
    (hlowb : ∀ k ∈ Finset.range (K + 1), x₀ ≤ (n : ℝ) / ((k : ℝ) + b)) :
    |(∑ k ∈ Finset.range (K + 1),
        (Chebyshev.theta ((n : ℝ) / ((k : ℝ) + a))
          - Chebyshev.theta ((n : ℝ) / ((k : ℝ) + b))))
       - (n : ℝ) * (∑ k ∈ Finset.range (K + 1), (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b)))|
      ≤ δ * (n : ℝ) * (∑ k ∈ Finset.range (K + 1), 1 / ((k : ℝ) + a))
        + δ * (n : ℝ) * (∑ k ∈ Finset.range (K + 1), 1 / ((k : ℝ) + b)) := by
  rw [block_sum_split n K a b, add_sub_cancel_left, Finset.sum_sub_distrib]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · exact block_error_bound n K a δ x₀ (fun x => Chebyshev.theta x - x) hE hlowa
  · exact block_error_bound n K b δ x₀ (fun x => Chebyshev.theta x - x) hE hlowb

/-- **The quantification over `n`.** A fixed-`n` closeness bound plus two convergences give the
LIMIT statement leg B actually asserts.

`block_sum_close` bounds `|F n − n·M n|` for each `n`; `density_tail_le` gives `M n → S(a,b)`; and
`block_error_bound × harmonic_weight_bound × error_rate_beats_log` give `Err n / n → 0`. This
lemma is what turns those three into `F n / n → S(a,b)` — i.e. into `lim (1/n)·log Φ̃_n = d_φ̃`,
the actual shape of leg B.

Stated abstractly because that is all it is: `|F/n − L| ≤ Err/n + |M − L|`, both terms → 0. -/
theorem tendsto_of_close (F M Err : ℕ → ℝ) (L : ℝ)
    (hclose : ∀ n : ℕ, |F n - (n : ℝ) * M n| ≤ Err n)
    (hM : Filter.Tendsto M Filter.atTop (nhds L))
    (hErr : Filter.Tendsto (fun n : ℕ => Err n / (n : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => F n / (n : ℝ)) Filter.atTop (nhds L) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : Filter.Tendsto (fun n : ℕ => Err n / (n : ℝ) + |M n - L|)
      Filter.atTop (nhds 0) := by
    have h := hErr.add (Filter.Tendsto.abs (hM.sub (tendsto_const_nhds (x := L))))
    simpa using h
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => dist_nonneg) ?_ hbound
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.dist_eq]
  have hsplit : F n / (n : ℝ) - L = (F n - (n : ℝ) * M n) / (n : ℝ) + (M n - L) := by
    field_simp
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(F n - (n : ℝ) * M n) / (n : ℝ)| ≤ Err n / (n : ℝ) := by
    rw [abs_div, abs_of_pos hnpos]
    gcongr
    exact hclose n
  linarith [h1]

/-- **Item (4): the outer loop over the profile's intervals.** `φ̃` is a step function with 26
pieces `[aᵢ, bᵢ)` of value `vᵢ`, so `log Φ̃_n = ∑ᵢ vᵢ·Fᵢ(n)` and `d_φ̃ = ∑ᵢ vᵢ·S(aᵢ,bᵢ)`.

Once each interval converges (`tendsto_of_close` fed by `block_sum_close`), the weighted finite
sum converges to the weighted sum of limits. Mathlib's `tendsto_finsetSum` does the work; the
content here is only pulling `1/n` through the sum.

Stated over an arbitrary `Finset` rather than `Fin 26`: the profile's piece count is data, and
nothing in the argument depends on it. -/
theorem tendsto_profile_sum {ι : Type*} (s : Finset ι) (v : ι → ℝ) (F : ι → ℕ → ℝ) (S : ι → ℝ)
    (hF : ∀ i ∈ s, Filter.Tendsto (fun n : ℕ => F i n / (n : ℝ)) Filter.atTop (nhds (S i))) :
    Filter.Tendsto (fun n : ℕ => (∑ i ∈ s, v i * F i n) / (n : ℝ))
      Filter.atTop (nhds (∑ i ∈ s, v i * S i)) := by
  have h : ∀ n : ℕ, (∑ i ∈ s, v i * F i n) / (n : ℝ)
      = ∑ i ∈ s, v i * (F i n / (n : ℝ)) := by
    intro n
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [h]
  exact tendsto_finsetSum s fun i hi => (hF i hi).const_mul (v i)

/-- **`Err n / n → 0`, the error side's final assembly.**

`block_error_bound` × `harmonic_weight_bound` give `Err n ≤ δ_n · n · (c + log K_n)`, so
`Err n / n ≤ δ_n·c + δ_n·log K_n`. Both terms vanish: the first because `δ_n → 0`, the second
because that is exactly `error_rate_beats_log` at MediumPNT's rate.

This is the hypothesis `tendsto_of_close` needs, so with it the error side is complete up to
supplying the two convergences from a concrete rate. -/
theorem err_over_n_tendsto_zero (δ Lg : ℕ → ℝ) (c : ℝ)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδlog : Filter.Tendsto (fun n => δ n * Lg n) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => δ n * (c + Lg n)) Filter.atTop (nhds 0) := by
  have hrw : ∀ n, δ n * (c + Lg n) = c * δ n + δ n * Lg n := fun n => by ring
  simp only [hrw]
  simpa using (hδ.const_mul c).add hδlog

/-- **The `ψ → θ` transfer — and it needs NO PNT+ at all.**

The design doc listed this as part of the cross-toolchain step. It is not: Mathlib's own
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` gives `|ψ x − θ x| ≤ 2√x·log x` outright, so a `ψ`
error bound transfers to `θ` entirely within current Mathlib.

The `2√x·log x` overhead is far inside budget: relative to `x` it is `2·log x/√x`, and at
`x ≥ √n` that is `≍ log n / n^{1/4}` — which still vanishes after multiplication by `log n`, the
factor `harmonic_weight_bound` contributes. It is not the binding term; MediumPNT's rate is.

**So the last gap is narrower than recorded**: only MediumPNT's rate on `ψ` itself has to cross
the toolchain boundary. -/
theorem theta_error_le {x r : ℝ} (hx : 1 ≤ x) (hψ : |Chebyshev.psi x - x| ≤ r) :
    |Chebyshev.theta x - x| ≤ r + 2 * Real.sqrt x * Real.log x := by
  have htrans := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  have hsplit : Chebyshev.theta x - x
      = -(Chebyshev.psi x - Chebyshev.theta x) + (Chebyshev.psi x - x) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  linarith

/-- **LEG B FOR ONE INTERVAL, ASSEMBLED.**

Given a block-count `K n → ∞` and a rate `δ n` satisfying the two convergences the chain needs,
the normalised block sum converges to the density series `S(a,b) = ∑ₖ[1/(k+a) − 1/(k+b)]`:

> `(1/n)·∑_{k≤K n}[θ(n/(k+a)) − θ(n/(k+b))]  →  ∑'ₖ [1/(k+a) − 1/(k+b)]`

The `hblk` hypothesis is exactly `block_sum_close` composed with `harmonic_weight_bound`; `hδ0`
and `hδlog` are what `MediumPNT`'s rate supplies (via `theta_error_le`, which needs no PNT+).
So this is leg B for one interval of the profile, modulo ONE external input: a `ψ` error bound.

`tendsto_profile_sum` then lifts it over the profile's 26 pieces. -/
theorem legB_one_interval (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1)
    (K : ℕ → ℕ) (hK : Filter.Tendsto K Filter.atTop Filter.atTop)
    (δ : ℕ → ℝ)
    (hδ0 : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδlog : Filter.Tendsto (fun n => δ n * Real.log (K n)) Filter.atTop (nhds 0))
    (hblk : ∀ n : ℕ,
      |(∑ k ∈ Finset.range (K n + 1),
          (Chebyshev.theta ((n : ℝ) / ((k : ℝ) + a))
            - Chebyshev.theta ((n : ℝ) / ((k : ℝ) + b))))
        - (n : ℝ) * (∑ k ∈ Finset.range (K n + 1),
            (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b)))|
        ≤ δ n * (n : ℝ) * (1 / a + 1 + Real.log (K n))
          + δ n * (n : ℝ) * (1 / b + 1 + Real.log (K n))) :
    Filter.Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range (K n + 1),
          (Chebyshev.theta ((n : ℝ) / ((k : ℝ) + a))
            - Chebyshev.theta ((n : ℝ) / ((k : ℝ) + b)))) / (n : ℝ))
      Filter.atTop (nhds (∑' k : ℕ, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b)))) := by
  refine tendsto_of_close _ _
    (fun n => δ n * (n : ℝ) * (1 / a + 1 + Real.log (K n))
      + δ n * (n : ℝ) * (1 / b + 1 + Real.log (K n))) _ hblk ?_ ?_
  · -- the main term: partial sums along `K n + 1 → ∞` converge to the tsum
    have hsum := (summable_density a b ha hab hb1).hasSum.tendsto_sum_nat
    exact hsum.comp (Filter.tendsto_atTop_mono (fun n => Nat.le_succ (K n)) hK)
  · -- the error, divided by `n`
    have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha hab
    have hA := err_over_n_tendsto_zero δ (fun n => Real.log (K n)) (1 / a + 1) hδ0 hδlog
    have hB := err_over_n_tendsto_zero δ (fun n => Real.log (K n)) (1 / b + 1) hδ0 hδlog
    have hsum := hA.add hB
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    field_simp

/-- **The block threshold.** If the block count satisfies `K + a ≤ √n`, then every block's argument
`n/(k+a)` is at least `√n`.

This is what supplies `block_error_bound`'s `hlow` with `x₀ = √n`, and it is why `K ≈ √(n/γ₀)` is
the right block count: the smallest argument, at `k = K`, is `n/(K+a) ≈ √(γ₀ n)` — exactly the
lower edge of the profile's prime range `√(γ₀n) < p`. The bound below is the clean form of that.

The proof is one line of algebra once stated correctly: `n/(k+a) ≥ n/(K+a) ≥ n/√n = √n`. -/
theorem block_lower_bound (n K : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a)
    (hKa : (K : ℝ) + a ≤ Real.sqrt n) :
    ∀ k ∈ Finset.range (K + 1), Real.sqrt n ≤ (n : ℝ) / ((k : ℝ) + a) := by
  intro k hk
  have hkK : (k : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hka : (0 : ℝ) < (k : ℝ) + a := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hka]
  calc Real.sqrt n * ((k : ℝ) + a)
      ≤ Real.sqrt n * Real.sqrt n := by
        have hs : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
        nlinarith
    _ = (n : ℝ) := Real.mul_self_sqrt hnpos.le

/-- **`hblk`, assembled** — `block_sum_close` composed with `harmonic_weight_bound` and Mathlib's
`harmonic_le_one_add_log`, giving exactly the shape `legB_one_interval` (and hence
`legB_candidate_threaded`) takes as its per-piece hypothesis.

With this, the only inputs leg B still needs from outside are `hE` (the `θ` error bound, which
`theta_error_le` derives from `psi_error_bound`) and the two `hlow` threshold facts (which
`block_lower_bound` supplies at `x₀ = √n`). -/
theorem hblk_assembled (n K : ℕ) (a b δ x₀ : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 ≤ δ)
    (hE : ∀ x, x₀ ≤ x → |Chebyshev.theta x - x| ≤ δ * x)
    (hlowa : ∀ k ∈ Finset.range (K + 1), x₀ ≤ (n : ℝ) / ((k : ℝ) + a))
    (hlowb : ∀ k ∈ Finset.range (K + 1), x₀ ≤ (n : ℝ) / ((k : ℝ) + b)) :
    |(∑ k ∈ Finset.range (K + 1),
        (Chebyshev.theta ((n : ℝ) / ((k : ℝ) + a))
          - Chebyshev.theta ((n : ℝ) / ((k : ℝ) + b))))
       - (n : ℝ) * (∑ k ∈ Finset.range (K + 1), (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + b)))|
      ≤ δ * (n : ℝ) * (1 / a + 1 + Real.log K)
        + δ * (n : ℝ) * (1 / b + 1 + Real.log K) := by
  refine (block_sum_close n K a b δ x₀ hE hlowa hlowb).trans ?_
  have hharm : (harmonic K : ℝ) ≤ 1 + Real.log K := harmonic_le_one_add_log K
  have hA : (∑ k ∈ Finset.range (K + 1), 1 / ((k : ℝ) + a)) ≤ 1 / a + 1 + Real.log K := by
    have := harmonic_weight_bound K a ha
    linarith
  have hB : (∑ k ∈ Finset.range (K + 1), 1 / ((k : ℝ) + b)) ≤ 1 / b + 1 + Real.log K := by
    have := harmonic_weight_bound K b hb
    linarith
  have hδn : (0 : ℝ) ≤ δ * (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact mul_nonneg hδ this
  have h1 := mul_le_mul_of_nonneg_left hA hδn
  have h2 := mul_le_mul_of_nonneg_left hB hδn
  linarith

/-! ### A concrete block count

`block_lower_bound` needs `K + a ≤ √n`, and `legB_one_interval` needs `K n → ∞`. `Nat.sqrt n - 1`
satisfies both for every profile piece at once, because every piece has `a ≤ 1`. -/

/-- `⌊√n⌋ ≤ √n` — the cast comparison the block count rests on. -/
theorem natSqrt_le_sqrt (n : ℕ) : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := by
  have h : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
  have h' : ((Nat.sqrt n : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast h
  exact (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr h'

/-- **The concrete block count works.** With `K n = ⌊√n⌋ − 1`, the hypothesis of
`block_lower_bound` holds for every `a ≤ 1` — hence for every piece of the profile at once.

`1 ≤ n` is REQUIRED, not decorative: at `n = 0` the claim reads `0 + a ≤ 0`, false for the `a > 0`
every piece has. Leg B only needs eventual behaviour, so the hypothesis costs nothing. -/
theorem blockCount_le_sqrt (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha1 : a ≤ 1) :
    ((Nat.sqrt n - 1 : ℕ) : ℝ) + a ≤ Real.sqrt n := by
  have hpos : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
  have hc : ((Nat.sqrt n - 1 : ℕ) : ℝ) + 1 = ((Nat.sqrt n : ℕ) : ℝ) := by
    have hs : (Nat.sqrt n - 1 : ℕ) + 1 = Nat.sqrt n := Nat.succ_pred_eq_of_pos hpos
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hs
  have := natSqrt_le_sqrt n
  linarith

/-- The concrete block count tends to infinity. -/
theorem blockCount_tendsto :
    Filter.Tendsto (fun n : ℕ => Nat.sqrt n - 1) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  refine ⟨(b + 1) ^ 2, fun n hn => ?_⟩
  have h : b + 1 ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hn
  omega

/-! ### D5b — the transfer that discharges `hE`

`legB_candidate_final` still carries a `θ` error bound above `√n` as a hypothesis. The external
input available is a `ψ` bound (`PsiErrorBound.psi_error_bound`, proved on PNT+ from `MediumPNT`).
The four items below are what turn one into the other, ENTIRELY IN CURRENT MATHLIB:

* `errRate` — an explicitly ANTITONE relative-error majorant. This is the threshold bookkeeping:
  `hE` reads `∀ x ≥ √n, |θ x − x| ≤ δ n · x`, i.e. ONE number covering the whole tail `[√n, ∞)`,
  and only a DECREASING majorant supplies that from a pointwise rate.
* `theta_rel_le_errRate` — the `ψ → θ` transfer, on Mathlib's own
  `Chebyshev.psi_sub_theta_le_mul_sqrt`. No PNT+ (LEAN.md §2).
* `theta_error_le_self` — the crude global `|θ x − x| ≤ x`, which is what lets `δ` be defined for
  EVERY `n`: `legB_candidate_final`'s `hE` is a `∀ n`, and small `n` are not covered by an
  eventual bound.
* `errRate_sqrt_mul_log_tendsto` — `δ n · log n → 0` at MediumPNT's rate. This is the inequality
  where bare PNT dies, now discharged rather than assumed. -/

/-- The relative-error majorant: MediumPNT's rate plus the `ψ − θ` overhead, both written so that
`y ↦ errRate c C B y` is ANTITONE on `[1, ∞)`. The second summand is `exp(−log y / 2)` rather than
the equal-but-opaque `y^(−1/2)` precisely so the antitonicity is one `exp`/`log` monotonicity step
rather than an `rpow` argument. -/
noncomputable def errRate (c C B : ℝ) (y : ℝ) : ℝ :=
  C * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10)) + B * Real.exp (-(Real.log y) / 2)

theorem errRate_nonneg {c C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (y : ℝ) :
    0 ≤ errRate c C B y := by
  have h1 : 0 ≤ C * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10)) :=
    mul_nonneg hC (Real.exp_pos _).le
  have h2 : 0 ≤ B * Real.exp (-(Real.log y) / 2) := mul_nonneg hB (Real.exp_pos _).le
  unfold errRate
  linarith

/-- **The majorant is antitone above `1`** — the step that turns a tail bound into a single
`δ n`. -/
theorem errRate_antitone {c C B : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hB : 0 ≤ B)
    {y z : ℝ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    errRate c C B z ≤ errRate c C B y := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hlog : Real.log y ≤ Real.log z := Real.log_le_log hy0 hyz
  have h1 : (Real.log y) ^ ((1 : ℝ) / 10) ≤ (Real.log z) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow hlogy hlog (by norm_num)
  have e1 : Real.exp (-c * (Real.log z) ^ ((1 : ℝ) / 10))
      ≤ Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have e2 : Real.exp (-(Real.log z) / 2) ≤ Real.exp (-(Real.log y) / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have m1 := mul_le_mul_of_nonneg_left e1 hC
  have m2 := mul_le_mul_of_nonneg_left e2 hB
  unfold errRate
  linarith

/-- `exp(−log x / 2) · x = √x` — the identity that makes the `ψ − θ` overhead fit the majorant's
shape without introducing a negative `rpow`. -/
theorem exp_neg_half_log_mul_self {x : ℝ} (hx : 0 < x) :
    Real.exp (-(Real.log x) / 2) * x = Real.sqrt x := by
  have hsp : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hl : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  have h1 : Real.exp (-(Real.log x) / 2) = (Real.sqrt x)⁻¹ := by
    rw [show -(Real.log x) / 2 = -(Real.log (Real.sqrt x)) by rw [hl]; ring,
      Real.exp_neg, Real.exp_log hsp]
  rw [h1, inv_mul_eq_div, eq_comm, eq_div_iff (ne_of_gt hsp)]
  exact Real.mul_self_sqrt hx.le

/-- **The `ψ → θ` transfer, in relative form.** Mathlib's own `psi_sub_theta_le_mul_sqrt` supplies
the `O(√x)` overhead — no PNT+ is involved (LEAN.md §2: the design doc had priced this as
cross-toolchain work; it is local). -/
theorem theta_rel_le_errRate {c C B x : ℝ} (hx : 1 ≤ x)
    (hψ : |Chebyshev.psi x - x| ≤ C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x)
    (hpt : Chebyshev.psi x - Chebyshev.theta x ≤ B * Real.sqrt x) :
    |Chebyshev.theta x - x| ≤ errRate c C B x * x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hnn : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
    have := Chebyshev.theta_le_psi x
    linarith
  have key : Real.exp (-(Real.log x) / 2) * x = Real.sqrt x := exp_neg_half_log_mul_self hx0
  have hsplit : Chebyshev.theta x - x
      = -(Chebyshev.psi x - Chebyshev.theta x) + (Chebyshev.psi x - x) := by ring
  have hrw : errRate c C B x * x
      = C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x + B * Real.sqrt x := by
    unfold errRate
    rw [← key]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_of_nonneg hnn, hrw]
  linarith

/-- **The crude global bound `|θ x − x| ≤ x`**, from `theta_nonneg` and `theta_le_log4_mul_x`
(`log 4 ≤ 2`). This is what lets the `δ` built from `errRate` be defined for EVERY `n`, which is
what `legB_candidate_final`'s `∀ n` hypothesis demands — leg B only needs eventual behaviour, but
the statement quantifies over all `n`, and a valid bound for small `n` costs nothing here. -/
theorem theta_error_le_self {x : ℝ} (hx : 0 ≤ x) : |Chebyshev.theta x - x| ≤ x := by
  have h0 : 0 ≤ Chebyshev.theta x := Chebyshev.theta_nonneg x
  have h4 : Chebyshev.theta x ≤ Real.log 4 * x := Chebyshev.theta_le_log4_mul_x hx
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hl : Real.log 4 ≤ 2 := by rw [hlog4]; linarith
  rw [abs_le]
  refine ⟨by linarith, ?_⟩
  nlinarith

/-- **The decisive limit, at the threshold `√n`.** `harmonic_weight_bound` contributes one
`log n`; `errRate` evaluated at the threshold `√n` kills it. Bare PNT dies exactly here — this is
`error_rate_beats_log` carried from the abstract `u` to the concrete threshold. -/
theorem errRate_sqrt_mul_log_tendsto (c C B : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => errRate c C B (Real.sqrt n) * Real.log n)
      Filter.atTop (nhds 0) := by
  have hden : (0 : ℝ) < 2 ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos (by norm_num) _
  have hc' : 0 < c / 2 ^ ((1 : ℝ) / 10) := div_pos hc hden
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto
      (fun u : ℝ => C * (u * Real.exp (-(c / 2 ^ ((1 : ℝ) / 10)) * u ^ ((1 : ℝ) / 10))))
      Filter.atTop (nhds 0) := by
    simpa using (error_rate_beats_log _ hc').const_mul C
  have h2 : Filter.Tendsto (fun u : ℝ => B * (u ^ (1 : ℝ) * Real.exp (-(1 / 4 : ℝ) * u)))
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 4) (by norm_num)).const_mul B
  have hsum := (h1.comp hlog).add (h2.comp hlog)
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hun : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hls : Real.log (Real.sqrt (n : ℝ)) = Real.log (n : ℝ) / 2 :=
    Real.log_sqrt (by positivity)
  have hdiv : (Real.log (n : ℝ) / 2) ^ ((1 : ℝ) / 10)
      = Real.log (n : ℝ) ^ ((1 : ℝ) / 10) / 2 ^ ((1 : ℝ) / 10) :=
    Real.div_rpow hun (by norm_num) _
  have he1 : -c * (Real.log (n : ℝ) / 2) ^ ((1 : ℝ) / 10)
      = -(c / 2 ^ ((1 : ℝ) / 10)) * Real.log (n : ℝ) ^ ((1 : ℝ) / 10) := by
    rw [hdiv]; ring
  have he2 : -(Real.log (n : ℝ) / 2) / 2 = -(1 / 4 : ℝ) * Real.log (n : ℝ) := by ring
  unfold errRate
  simp only [Function.comp_apply, hls, he1, he2, Real.rpow_one]
  ring

/-- `0 ≤ log m` for a natural `m` — true at `m = 0` too, since `log 0 = 0`. -/
theorem log_natCast_nonneg (m : ℕ) : 0 ≤ Real.log (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hm)

/-- `log` is monotone on natural casts — again including `m = 0`. This is what lets
`log (K n)` be squeezed by `log n`. -/
theorem log_natCast_le_log_natCast {m n : ℕ} (hmn : m ≤ n) :
    Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmn)

end Zeta2LegB
