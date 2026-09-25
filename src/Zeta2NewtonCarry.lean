/-
# PNCLR's remaining obligation — the termwise invariant, as a theorem

Row PNCLR's one open statement (chain doc, 2026-09-17) is the TERMWISE divisibility

    L₀ · C(L₀ + r, L₀)  ∣  D(K) · h_{L₀+r}        for every r,

where `h_m = Δ^m H(0)` is the Newton (finite-difference) coefficient of

    H(Y) = C(Y − 13n − 1, 13n) · C(Y − 15n − 1, 9n) · C(Y − 17n − 1, 5n)

and `K = 13n` is the LONGEST BLOCK.  It was measured exact and termwise (0 of 16 … 0 of 80 at
`n = 1..5`; 300/300 random block configurations) and was NOT machine-checked.

**This file proves it, for an arbitrary finite product of integer-valued functions**, by splitting
it at `D m` into two independent halves — neither of which mentions the other's objects:

  (A) `L₀ · C(L₀+r, L₀) ∣ D(L₀+r)`.      Classical.  `L₀·C(m,L₀) = m·C(m−1,L₀−1)`, and Kummer
      says the carries adding `L₀ + r` all sit ABOVE position `ord_p L₀`, so
      `ord_p L₀ + ord_p C(m,L₀) ≤ ⌊log_p m⌋ = ord_p D m`.

  (B) `D m ∣ D K · Δ^m H(x)` for `H` a product of functions of finite-difference degree `≤ K`.
      Induction on the number of factors through the finite-difference Leibniz rule; the whole
      content is the pure-ℕ lemma `D_dvd_choose_mul_D` below — `D m ∣ C(m,i) · D(max i (m−i))` —
      which is again a carry count: for every `t` with `max i (m−i) < p^t ≤ m` the addition
      `i + (m−i)` carries at position `t`, because both summands are then below `p^t`.

  (A) and (B) compose to the invariant at `K = max_s L_s` — SHARPER than the measured general
  conjecture, which carried `K = max(max_s L_s, L₀)`.  The extra strength was itself measured
  before this file was written (`carry_margin_probe.py` arm A6: 400/400 configurations with
  `L₀ > max_s L_s`, where the two constants differ).

WHAT THIS FILE DOES NOT DO.  It proves the invariant.  It does NOT state, in Lean, the exact
identity `Π·Ppol(t) = Σ_r h_{L₀+r}·C(Y−L₀, r) / (L₀·C(L₀+r, L₀))` that turns the invariant into
`Zeta2PpolInt.cleared_of_dvd_PpolZ`'s hypothesis, and it does not instantiate `H` at the member's
three blocks.  Those are PNCLR's remaining ASSEMBLY; see the chain doc's cell.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Arith
import Zeta2PhiT
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Binomial

namespace Zeta2NewtonCarry

open Finset

/-! ## Part 1 — two facts about `D k = lcm(1..k)`, each a Kummer carry count -/

/-- **The carry lemma.**  For `i ≤ m` and `p` prime, every base-`p` position strictly between
`log_p (max i (m−i))` and `log_p m` is a CARRY position of the addition `i + (m − i) = m`: both
summands are below `p^t` there, so the two residues are the summands themselves and their sum is
`m ≥ p^t`.  Hence `ord_p C(m,i) ≥ ⌊log_p m⌋ − ⌊log_p (max i (m−i))⌋`. -/
theorem log_le_padicValNat_choose_add_log (p m i : ℕ) [hp : Fact p.Prime] (h : i ≤ m) :
    Nat.log p m ≤ padicValNat p (m.choose i) + Nat.log p (max i (m - i)) := by
  have hp1 : 1 < p := hp.out.one_lt
  rcases Nat.lt_or_ge (Nat.log p (max i (m - i))) (Nat.log p m) with hEG | hEG
  swap
  · omega
  -- `G < E`, so in particular `E ≥ 1` and `m ≠ 0`.
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hEG
  have hsum : (m - i) + i = m := by omega
  have hlog : Nat.log p ((m - i) + i) < Nat.log p m + 1 := by rw [hsum]; omega
  have hval := padicValNat_choose' (p := p) hlog
  rw [hsum] at hval
  have hsub : Ico (Nat.log p (max i (m - i)) + 1) (Nat.log p m + 1) ⊆
      (Ico 1 (Nat.log p m + 1)).filter (fun t => p ^ t ≤ i % p ^ t + (m - i) % p ^ t) := by
    intro t ht
    rw [mem_Ico] at ht
    rw [mem_filter, mem_Ico]
    have hgi : Nat.log p i ≤ Nat.log p (max i (m - i)) :=
      Nat.log_mono_right (le_max_left _ _)
    have hgmi : Nat.log p (m - i) ≤ Nat.log p (max i (m - i)) :=
      Nat.log_mono_right (le_max_right _ _)
    have hpi : i < p ^ t :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp1 i)
        (Nat.pow_le_pow_right (le_of_lt hp1) (by omega))
    have hpmi : m - i < p ^ t :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp1 (m - i))
        (Nat.pow_le_pow_right (le_of_lt hp1) (by omega))
    have hple : p ^ t ≤ m :=
      le_trans (Nat.pow_le_pow_right (le_of_lt hp1) (by omega : t ≤ Nat.log p m))
        (Nat.pow_log_le_self p hm0)
    refine ⟨⟨by omega, ht.2⟩, ?_⟩
    rw [Nat.mod_eq_of_lt hpi, Nat.mod_eq_of_lt hpmi]
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico, ← hval] at hcard
  omega

/-- **Half (B)'s whole content, as a pure-ℕ statement**: `D m ∣ C(m,i) · D(max i (m−i))`.
Measured before it was proved (`carry_margin_probe.py`); the proof is
`log_le_padicValNat_choose_add_log` at every prime. -/
theorem D_dvd_choose_mul_D (m i : ℕ) (h : i ≤ m) :
    Zeta2Arith.D m ∣ m.choose i * Zeta2Arith.D (max i (m - i)) := by
  have hc : m.choose i ≠ 0 := (Nat.choose_pos h).ne'
  have hne : m.choose i * Zeta2Arith.D (max i (m - i)) ≠ 0 :=
    Nat.mul_ne_zero hc (Zeta2Arith.D_ne_zero _)
  rw [← Nat.factorization_le_iff_dvd (Zeta2Arith.D_ne_zero m) hne, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [Zeta2PhiT.factorization_D m hp, Nat.factorization_mul hc (Zeta2Arith.D_ne_zero _),
      Finsupp.add_apply, Zeta2PhiT.factorization_D _ hp, Nat.factorization_def _ hp]
    exact log_le_padicValNat_choose_add_log p m i h
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- **Half (A).**  `L · C(L+r, L) ∣ D(L+r)` — equivalently `m · C(m−1, L−1) ∣ lcm(1..m)`.
Kummer again: `p^t ∣ L` kills the carry at every position `t ≤ ord_p L`, so all the carries of
`L + r` sit strictly above `ord_p L` and below `⌊log_p m⌋`. -/
theorem padicValNat_mul_choose_le_log (p L r : ℕ) [hp : Fact p.Prime] (hL : 0 < L) :
    padicValNat p L + padicValNat p ((L + r).choose L) ≤ Nat.log p (L + r) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hL0 : L ≠ 0 := hL.ne'
  have hm0 : L + r ≠ 0 := by omega
  -- `ord_p L ≤ log_p (L+r)`
  have hdvd : p ^ padicValNat p L ∣ L := pow_padicValNat_dvd
  have hple : p ^ padicValNat p L ≤ L + r :=
    le_trans (Nat.le_of_dvd hL hdvd) (by omega)
  have haE : padicValNat p L ≤ Nat.log p (L + r) :=
    Nat.le_log_of_pow_le hp1 hple
  -- the carries all sit above `ord_p L`
  have hsum : r + L = L + r := by omega
  have hlog : Nat.log p (r + L) < Nat.log p (L + r) + 1 := by rw [hsum]; omega
  have hval := padicValNat_choose' (p := p) hlog
  rw [hsum] at hval
  have hsub : (Ico 1 (Nat.log p (L + r) + 1)).filter
      (fun t => p ^ t ≤ L % p ^ t + r % p ^ t) ⊆
      Ico (padicValNat p L + 1) (Nat.log p (L + r) + 1) := by
    intro t ht
    rw [mem_filter, mem_Ico] at ht
    rw [mem_Ico]
    refine ⟨?_, ht.1.2⟩
    by_contra hcon0
    have hcon : t ≤ padicValNat p L := by omega
    -- `t ≤ ord_p L`, so `p^t ∣ L` and `L % p^t = 0`, killing the carry at `t`
    have hdt : p ^ t ∣ L := dvd_trans (pow_dvd_pow p (by omega)) hdvd
    obtain ⟨c, hc⟩ := hdt
    have h0 : L % p ^ t = 0 := by rw [hc]; exact Nat.mul_mod_right _ _
    have hr : r % p ^ t < p ^ t := Nat.mod_lt _ (pow_pos (by omega : 0 < p) t)
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico, ← hval] at hcard
  omega

/-- `L · C(L+r, L) ∣ D(L+r)`. -/
theorem mul_choose_dvd_D (L r : ℕ) (hL : 0 < L) :
    L * ((L + r).choose L) ∣ Zeta2Arith.D (L + r) := by
  have hc : (L + r).choose L ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hne : L * ((L + r).choose L) ≠ 0 := Nat.mul_ne_zero hL.ne' hc
  rw [← Nat.factorization_le_iff_dvd hne (Zeta2Arith.D_ne_zero _), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [Zeta2PhiT.factorization_D _ hp, Nat.factorization_mul hL.ne' hc, Finsupp.add_apply,
      Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    exact padicValNat_mul_choose_le_log p L r hL
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-! ## Part 2 — the finite difference, its Leibniz rule, and the product theorem -/

/-- The forward difference `Δf(x) = f(x+1) − f(x)` on `ℤ → ℤ`. -/
def fwd (f : ℤ → ℤ) : ℤ → ℤ := fun x => f (x + 1) - f x

/-- `Δ^n f`. -/
def fwdIter : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f => f
  | (n + 1), f => fwd (fwdIter n f)

theorem fwdIter_succ_apply (n : ℕ) (f : ℤ → ℤ) (x : ℤ) :
    fwdIter (n + 1) f x = fwdIter n f (x + 1) - fwdIter n f x := rfl

theorem fwdIter_zero_fun (n : ℕ) (x : ℤ) : fwdIter n (fun _ => (0 : ℤ)) x = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [fwdIter_succ_apply, ih, ih]; ring

/-- `Δ^a (Δ^b f) = Δ^{a+b} f`. -/
theorem fwdIter_add (a b : ℕ) (f : ℤ → ℤ) : fwdIter a (fwdIter b f) = fwdIter (a + b) f := by
  induction a with
  | zero => simp [fwdIter]
  | succ a ih =>
    show fwd (fwdIter a (fwdIter b f)) = fwdIter (a + 1 + b) f
    rw [ih, show a + 1 + b = (a + b) + 1 from by omega]
    rfl

/-- `f` has finite-difference degree at most `K`. -/
def DegLE (K : ℕ) (f : ℤ → ℤ) : Prop := ∀ x, fwdIter (K + 1) f x = 0

/-- Above the degree, every difference vanishes. -/
theorem fwdIter_eq_zero_of_degLE {K : ℕ} {f : ℤ → ℤ} (h : DegLE K f) {j : ℕ} (hj : K < j)
    (x : ℤ) : fwdIter j f x = 0 := by
  have hj' : j = (j - (K + 1)) + (K + 1) := by omega
  have hz : fwdIter (K + 1) f = fun _ => (0 : ℤ) := funext h
  rw [hj', ← fwdIter_add, hz, fwdIter_zero_fun]

/-- Pascal's rule, summed — the combinatorial half of the Leibniz induction. -/
theorem pascal_sum (m : ℕ) (T : ℕ → ℤ) :
    ∑ i ∈ range (m + 2), ((m + 1).choose i : ℤ) * T i
      = (∑ i ∈ range (m + 1), (m.choose i : ℤ) * T i)
        + ∑ i ∈ range (m + 1), (m.choose i : ℤ) * T (i + 1) := by
  have h1 : ∑ i ∈ range (m + 2), ((m + 1).choose i : ℤ) * T i
      = (∑ i ∈ range (m + 1), ((m + 1).choose (i + 1) : ℤ) * T (i + 1))
        + ((m + 1).choose 0 : ℤ) * T 0 :=
    Finset.sum_range_succ' (fun i => ((m + 1).choose i : ℤ) * T i) (m + 1)
  have h2 : ∑ i ∈ range (m + 2), (m.choose i : ℤ) * T i
      = ∑ i ∈ range (m + 1), (m.choose i : ℤ) * T i := by
    rw [Finset.sum_range_succ]
    simp
  have h3 : ∑ i ∈ range (m + 2), (m.choose i : ℤ) * T i
      = (∑ i ∈ range (m + 1), (m.choose (i + 1) : ℤ) * T (i + 1)) + (m.choose 0 : ℤ) * T 0 :=
    Finset.sum_range_succ' (fun i => (m.choose i : ℤ) * T i) (m + 1)
  have h4 : ∀ i : ℕ, ((m + 1).choose (i + 1) : ℤ) * T (i + 1)
      = (m.choose i : ℤ) * T (i + 1) + (m.choose (i + 1) : ℤ) * T (i + 1) := by
    intro i
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  rw [h1, ← h2, h3]
  simp only [h4]
  rw [Finset.sum_add_distrib]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

/-- **The finite-difference Leibniz rule.**
`Δ^m (fg)(x) = Σ_i C(m,i) · Δ^i f(x) · Δ^{m−i} g(x+i)`. -/
theorem fwdIter_mul (m : ℕ) (f g : ℤ → ℤ) (x : ℤ) :
    fwdIter m (fun y => f y * g y) x
      = ∑ i ∈ range (m + 1), (m.choose i : ℤ) * (fwdIter i f x * fwdIter (m - i) g (x + i)) := by
  induction m generalizing x with
  | zero => simp [fwdIter]
  | succ m ih =>
    rw [fwdIter_succ_apply, ih (x + 1), ih x, ← Finset.sum_sub_distrib]
    have hterm : ∀ i ∈ range (m + 1),
        (m.choose i : ℤ) * (fwdIter i f (x + 1) * fwdIter (m - i) g (x + 1 + i))
          - (m.choose i : ℤ) * (fwdIter i f x * fwdIter (m - i) g (x + i))
        = (m.choose i : ℤ) * (fwdIter i f x * fwdIter (m + 1 - i) g (x + i))
          + (m.choose i : ℤ) * (fwdIter (i + 1) f x
              * fwdIter (m + 1 - (i + 1)) g (x + ((i + 1 : ℕ) : ℤ))) := by
      intro i hi
      rw [mem_range] at hi
      have hi' : i ≤ m := by omega
      have e1 : fwdIter i f (x + 1) = fwdIter i f x + fwdIter (i + 1) f x := by
        rw [fwdIter_succ_apply]; ring
      have e2 : m + 1 - i = (m - i) + 1 := by omega
      have e3 : m + 1 - (i + 1) = m - i := by omega
      have e4 : (x + 1 + ((i : ℕ) : ℤ)) = (x + ((i : ℕ) : ℤ)) + 1 := by push_cast; ring
      have e5 : (x + (((i + 1 : ℕ)) : ℤ)) = (x + ((i : ℕ) : ℤ)) + 1 := by push_cast; ring
      -- the `g`-side succ, named so that `rw` cannot fire on the `f`-side one instead
      have e6 : fwdIter ((m - i) + 1) g (x + ((i : ℕ) : ℤ))
          = fwdIter (m - i) g (x + ((i : ℕ) : ℤ) + 1) - fwdIter (m - i) g (x + ((i : ℕ) : ℤ)) :=
        fwdIter_succ_apply _ _ _
      rw [e1, e2, e3, e4, e5, e6]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    exact (pascal_sum m
      (fun i => fwdIter i f x * fwdIter (m + 1 - i) g (x + (i : ℕ)))).symm

/-- The product of a list of functions. -/
def listProd : List (ℤ → ℤ) → (ℤ → ℤ)
  | [] => fun _ => 1
  | f :: fs => fun x => f x * listProd fs x

/-- **Half (B).**  For a product of functions each of finite-difference degree `≤ K`,
`D m ∣ D K · Δ^m H(x)` — the whole content of "the Newton coefficient absorbs every prime power
between `K` and `m`", and the reason `K` is the LONGEST BLOCK rather than the degree. -/
theorem D_dvd_D_mul_fwdIter_listProd (K : ℕ) : ∀ (fs : List (ℤ → ℤ)),
    (∀ f ∈ fs, DegLE K f) → ∀ (m : ℕ) (x : ℤ),
      (Zeta2Arith.D m : ℤ) ∣ (Zeta2Arith.D K : ℤ) * fwdIter m (listProd fs) x := by
  intro fs
  induction fs with
  | nil =>
    intro _ m x
    have hD0 : Zeta2Arith.D 0 = 1 := by simp [Zeta2Arith.D]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hD0]
      simp
    · have hdeg : DegLE 0 (listProd ([] : List (ℤ → ℤ))) := by
        intro y
        show fwdIter 1 (fun _ => (1 : ℤ)) y = 0
        rw [fwdIter_succ_apply]
        simp [fwdIter]
      rw [fwdIter_eq_zero_of_degLE hdeg (by omega : 0 < m) x]
      simp
  | cons f fs ih =>
    intro hfs m x
    have hf : DegLE K f := hfs f List.mem_cons_self
    have hfs' : ∀ g ∈ fs, DegLE K g := fun g hg => hfs g (List.mem_cons_of_mem _ hg)
    have hprod : listProd (f :: fs) = fun y => f y * listProd fs y := rfl
    rw [hprod, fwdIter_mul, Finset.mul_sum]
    refine Finset.dvd_sum ?_
    intro i hi
    rw [mem_range] at hi
    have him : i ≤ m := by omega
    by_cases hiK : K < i
    · rw [fwdIter_eq_zero_of_degLE hf hiK x]
      simp
    · have hiK' : i ≤ K := by omega
      have hA : (Zeta2Arith.D m : ℤ) ∣ (m.choose i : ℤ) * (Zeta2Arith.D (max i (m - i)) : ℤ) := by
        exact_mod_cast Int.natCast_dvd_natCast.mpr (D_dvd_choose_mul_D m i him)
      have hB : (Zeta2Arith.D (max i (m - i)) : ℤ)
          ∣ (Zeta2Arith.D K : ℤ) * fwdIter (m - i) (listProd fs) (x + i) := by
        rcases max_cases i (m - i) with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he]
          exact Dvd.dvd.mul_right
            (by exact_mod_cast Int.natCast_dvd_natCast.mpr (Zeta2Arith.D_dvd_D hiK')) _
        · rw [he]
          exact ih hfs' (m - i) (x + i)
      have hrw : (Zeta2Arith.D K : ℤ)
            * ((m.choose i : ℤ) * (fwdIter i f x * fwdIter (m - i) (listProd fs) (x + i)))
          = fwdIter i f x * ((m.choose i : ℤ)
              * ((Zeta2Arith.D K : ℤ) * fwdIter (m - i) (listProd fs) (x + i))) := by ring
      rw [hrw]
      exact Dvd.dvd.mul_left (hA.trans (mul_dvd_mul_left _ hB)) _

/-! ## Part 3 — the invariant -/

/-- **PNCLR's termwise invariant, proved.**  For `H` any finite product of integer-valued
functions of finite-difference degree `≤ K`, and `h_m = Δ^m H(0)`,

    L₀ · C(L₀ + r, L₀)  ∣  D K · h_{L₀+r}        for every `r`.

At the member's own objects `K = 13n` (the longest block), `L₀ = 11n + 1`, and this is exactly the
statement the chain doc's PNCLR cell records as FOUND, exact, termwise and open.  It is sharper
than the measured general conjecture, which carried `K = max(max_s L_s, L₀)`. -/
theorem termwise_invariant (K L₀ r : ℕ) (hL : 0 < L₀) (fs : List (ℤ → ℤ))
    (hfs : ∀ f ∈ fs, DegLE K f) (x : ℤ) :
    ((L₀ * ((L₀ + r).choose L₀) : ℕ) : ℤ)
      ∣ (Zeta2Arith.D K : ℤ) * fwdIter (L₀ + r) (listProd fs) x := by
  have h1 : ((L₀ * ((L₀ + r).choose L₀) : ℕ) : ℤ) ∣ ((Zeta2Arith.D (L₀ + r) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (mul_choose_dvd_D L₀ r hL)
  exact h1.trans (D_dvd_D_mul_fwdIter_listProd K fs hfs (L₀ + r) x)

/-! ## Part 4 — the member's own three blocks -/

/-- Degree is monotone in the bound. -/
theorem degLE_mono {K K' : ℕ} {f : ℤ → ℤ} (h : DegLE K f) (hKK : K ≤ K') : DegLE K' f :=
  fun x => fwdIter_eq_zero_of_degLE h (by omega) x

/-- `Δ` of a binomial block lowers its index — Pascal (`Ring.choose_succ_succ`). -/
theorem fwd_ringChoose (γ : ℤ) (k : ℕ) :
    fwd (fun y => Ring.choose (y + γ) (k + 1)) = fun y => Ring.choose (y + γ) k := by
  funext y
  show Ring.choose (y + 1 + γ) (k + 1) - Ring.choose (y + γ) (k + 1) = Ring.choose (y + γ) k
  rw [show y + 1 + γ = (y + γ) + 1 from by ring, Ring.choose_succ_succ]
  ring

/-- A binomial block `C(y + γ, L)` has finite-difference degree `≤ L`. -/
theorem degLE_ringChoose (γ : ℤ) (L : ℕ) : DegLE L (fun y => Ring.choose (y + γ) L) := by
  induction L with
  | zero =>
    intro y
    show fwdIter 1 (fun y => Ring.choose (y + γ) 0) y = 0
    rw [fwdIter_succ_apply]
    simp [fwdIter, Ring.choose_zero_right]
  | succ L ih =>
    intro y
    have h1 := fwdIter_add (L + 1) 1 (fun y => Ring.choose (y + γ) (L + 1))
    show fwdIter (L + 1 + 1) (fun y => Ring.choose (y + γ) (L + 1)) y = 0
    rw [← h1]
    show fwdIter (L + 1) (fwd (fun y => Ring.choose (y + γ) (L + 1))) y = 0
    rw [fwd_ringChoose]
    exact ih y

/-- The same with the block written as `C(y − c, L)`, which is the member's own spelling. -/
theorem degLE_ringChoose_sub (c : ℤ) (L : ℕ) : DegLE L (fun y => Ring.choose (y - c) L) := by
  have h := degLE_ringChoose (-c) L
  have he : (fun y : ℤ => Ring.choose (y + -c) L) = (fun y : ℤ => Ring.choose (y - c) L) := by
    funext y
    rw [← sub_eq_add_neg]
  rwa [he] at h

/-- The member's Newton kernel, as the list of its three blocks:
`H(Y) = C(Y − 13n − 1, 13n) · C(Y − 15n − 1, 9n) · C(Y − 17n − 1, 5n)`. -/
def memberBlocks (n : ℕ) : List (ℤ → ℤ) :=
  [fun y => Ring.choose (y - (13 * (n : ℤ) + 1)) (13 * n),
   fun y => Ring.choose (y - (15 * (n : ℤ) + 1)) (9 * n),
   fun y => Ring.choose (y - (17 * (n : ℤ) + 1)) (5 * n)]

/-- `listProd` of the three blocks IS `H` — so the theorem below is about the member's object
and not about a stand-in (LEAN.md §0a, column 1). -/
theorem listProd_memberBlocks (n : ℕ) (y : ℤ) :
    listProd (memberBlocks n) y
      = Ring.choose (y - (13 * (n : ℤ) + 1)) (13 * n)
        * Ring.choose (y - (15 * (n : ℤ) + 1)) (9 * n)
        * Ring.choose (y - (17 * (n : ℤ) + 1)) (5 * n) := by
  show _ * (_ * (_ * (1 : ℤ))) = _
  ring

/-- Every block has degree at most the LONGEST block `13n`. -/
theorem memberBlocks_degLE (n : ℕ) : ∀ f ∈ memberBlocks n, DegLE (13 * n) f := by
  intro f hf
  fin_cases hf
  · exact degLE_ringChoose_sub _ _
  · exact degLE_mono (degLE_ringChoose_sub _ _) (by omega)
  · exact degLE_mono (degLE_ringChoose_sub _ _) (by omega)

/-- **PNCLR's termwise invariant at the member's own blocks and constants.**
With `L₀ = 11n + 1` and `K = 13n` the longest block,

    (11n+1) · C(11n+1+r, 11n+1)  ∣  D(13n) · h_{11n+1+r},   h_m = Δ^m H(0).

This is, verbatim, the divisibility the chain doc's PNCLR cell records as FOUND, exact, termwise,
measured at `n = 1..5` and OPEN.  It is no longer open. -/
theorem termwise_invariant_member (n r : ℕ) :
    (((11 * n + 1) * ((11 * n + 1 + r).choose (11 * n + 1)) : ℕ) : ℤ)
      ∣ (Zeta2Arith.D (13 * n) : ℤ)
          * fwdIter (11 * n + 1 + r) (listProd (memberBlocks n)) 0 :=
  termwise_invariant (13 * n) (11 * n + 1) r (by omega) (memberBlocks n)
    (memberBlocks_degLE n) 0

#print axioms log_le_padicValNat_choose_add_log
#print axioms D_dvd_choose_mul_D
#print axioms padicValNat_mul_choose_le_log
#print axioms mul_choose_dvd_D
#print axioms fwdIter_eq_zero_of_degLE
#print axioms pascal_sum
#print axioms fwdIter_mul
#print axioms D_dvd_D_mul_fwdIter_listProd
#print axioms termwise_invariant
#print axioms degLE_ringChoose
#print axioms listProd_memberBlocks
#print axioms memberBlocks_degLE
#print axioms termwise_invariant_member

end Zeta2NewtonCarry
