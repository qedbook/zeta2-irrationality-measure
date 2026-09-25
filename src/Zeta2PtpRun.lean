/-
# Row PT-P, layer 2 — the short run's MECHANISM, in the units digit

`Zeta2PhiTDvd.lean` (layer 1) reduced PT-P to ONE inequality per window prime,
`φ̃({n/p}) ≤ v_p(P n)`, and stopped there.  `ptp_cancel_probe.py` then reduced that to ONE
congruence per CELL over a contiguous run of residues `u = m mod p` — and QUOTED the run's two
endpoints as MEASURED numbers (`(3,13) → [8,12]`, `(5,43) → [12,22]`), which is a census entry
and not something Lean can be told.  This file proves the predicate those numbers were samples
of, and it is stronger than "the endpoints": the WHOLE per-term valuation is a function of two
residues.

**THE THEOREM (`vp_cTerm_eq_units`).**  With `m = k − 4n − 1` the four binomials of
`Zeta2Arith.cTerm n k` are four base-`p` additions

    (1) 13n + (m−9n) = m+4n = k−1      (2) 9n + (m−7n) = m+2n = k−2n−1
    (3) 5n  + (m−5n) = m               (4) (m−11n) + (22n−m) = 11n

and at a prime of `Zeta2PhiT.phiWindow n` every one of those four totals is below `p²`
(`k−1 ≤ 26n < 26n+1 < p²`, and the other three are smaller).  Below `p²` a base-`p` addition
cannot carry out of the `p`-digit — a carry there would push the total past `p²` — so Kummer has
only the UNITS position left to count, and

    v_p(cTerm n k) = cb p (k−1) (13n) + cb p (k−2n−1) (9n) + cb p (k−4n−1) (5n)
                       + cb p (11n) (k−15n−1)

with `cb p S A = if S % p < A % p then 1 else 0` — `Zeta2HatGap.carry_iff_of_add`'s shape, the
vocabulary `Zeta2CarryFull`'s residue reframe already speaks.

**WHY THAT IS THE ENDPOINT ANSWER.**  Each summand is a comparison between `(u + c·r) % p` and
`(c'·r) % p` for `r = n % p`, `u = m % p`, so each NO-carry condition is a CYCLIC INTERVAL in
`u` with lower end one of `9r, 7r, 5r, 11r` (mod p) and upper end one of `−4r−1, −2r−1, −1, 22r`
(mod p).  The short set `{u : v_p(cTerm) < φ̃}` is a union of intersections of those four
intervals, so BOTH of its endpoints are drawn from those two four-element lists — a closed form
in `r` and `p` with no `n` and no block index in it.
`ptp_run_endpoint_probe.py` / `.out` scores that at 1744 cells (4.8× `ptp_cancel_probe`'s box):
arm E8a 206/206, arm E4 3488/3488, arm E5 reproducing all 23 of the sibling's measured endpoint
pairs, 5 controls all fired.  **WHICH of the four ends binds at a given cell is MEASURED, not
proved** — u0 by `(11r)%p` at 81 cells, `(7r)%p` at 14, `(5r)%p` at 8; u1 by `(22r)%p` at 57,
`(−4r−1)%p` at 29, `p−1` at 22 — and that selection is the honest remaining gap between this
file and a Lean statement of the endpoints themselves.

**WHAT THIS FILE GIVES THE OPEN CONGRUENCE.**  `pow_dvd_cTerm_of_units` is the half that matters
for it: every term whose units carries reach `φ̃` is already `0 mod p^φ̃`, so the whole open
obligation is supported on the run and nothing outside it has to be looked at.
`vp_cTerm_residue_invariant` is `ptp_cancel_probe`'s arm A10 ("the run is the SAME in every
block of the cell", 84 of 84) as a theorem rather than a sample: `v_p(cTerm n k)` depends on
`(n, k)` only through `n % p` and `(k−4n−1) % p`.

**WHAT IT DOES NOT GIVE, and the row is not closed.**  The congruence itself —
`Σ_{u in the run} (−1)^{k−1} cTerm(n,k) ≡ 0 mod p^φ̃` — is untouched.  PT-P stays OPEN and
`Zeta2Target.zeta2_not_liouvilleWith` stays `sorry`.

**THE WINDOW HYPOTHESIS IS LOAD-BEARING, and there is a theorem saying so.**
`units_eq_needs_the_window` exhibits `n = 1, p = 2, k = 16`: `p² = 4 ≤ 27 = 26n+1`, the four
units carries are all zero, and `2 ∣ cTerm 1 16` — so the identity above is FALSE the instant
the Legendre line is dropped.  That is the probe's control R3 at its smallest witness (the
control fires at 311 of 311 unfiltered primes).

Probe: `ptp_run_endpoint_probe.py` / `.out` (9 arms, 5 kill controls, 2 recorded inert).
Falsifier: `falsify_ptprun.sh` / `out_ptprun_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2Profile
import Zeta2PhiT
import Zeta2HatGap

namespace Zeta2PtpRun

open Zeta2Defs Zeta2Arith Zeta2PhiT Nat Finset

/-! ## 1. The carry bit, and Kummer with only one digit to count -/

/-- **The units-carry bit of a base-`p` addition `A + B = S`**, in `Zeta2HatGap.carry_iff_of_add`'s
shape: the bit is a comparison of the SUM's residue with one summand's, never a statement about
both summands at once.  This is the atom the short run's endpoints are intervals of. -/
def cb (p S A : ℕ) : ℕ := if S % p < A % p then 1 else 0

/-- `carry_iff_of_add` with the summands in the order Kummer's filter presents them. -/
theorem carry_bit (p x j : ℕ) (hp : 0 < p) :
    (p ≤ j % p + x % p) ↔ (x + j) % p < j % p := by
  have h := Zeta2HatGap.carry_iff_of_add p j x hp
  rwa [Nat.add_comm j x] at h

/-- `a < p²` pins `⌊log_p a⌋ ≤ 1`, which is the ONE consequence of the window this file uses.
It needs no hypothesis on `p`: `p ≤ 1` makes `a < p²` force `a = 0`, where `Nat.log` is `0`. -/
theorem log_le_one_of_lt_sq {p a : ℕ} (h : a < p ^ 2) : Nat.log p a ≤ 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · simp
  · have : Nat.log p a < 2 := Nat.log_lt_of_lt_pow (by omega) h
    omega

/-- **Kummer with one digit.**  When `⌊log_p s⌋ ≤ 1` the carry count of `s.choose j` is a single
units bit, because a carry out of the `p`-digit would need `s ≥ p²`. -/
theorem vp_choose_eq_cb {p : ℕ} [Fact p.Prime] {s j : ℕ} (hj : j ≤ s)
    (hlog : Nat.log p s ≤ 1) : padicValNat p (s.choose j) = cb p s j := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨x, rfl⟩ : ∃ x, s = x + j := ⟨s - j, by omega⟩
  rw [padicValNat_choose' (b := 2) (by omega)]
  have hIco : Finset.Ico 1 2 = ({1} : Finset ℕ) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  rw [hIco, Finset.filter_singleton]
  simp only [pow_one, cb]
  -- `rw [← carry_bit …]` is NOT available here: the proposition also sits inside the `ite`'s
  -- `Decidable` instance, so the motive is not type correct.  Discharge both branches instead.
  by_cases h : p ≤ j % p + x % p
  · have h2 : (x + j) % p < j % p := (carry_bit p x j hp0).1 h
    simp [h, h2]
  · have h2 : ¬ ((x + j) % p < j % p) := fun hc => h ((carry_bit p x j hp0).2 hc)
    simp [h, h2]

/-! ## 2. The four additions of `cTerm`, at a window prime -/

/-- **The row's mechanism.**  At a prime of `phiWindow n` the valuation of `cTerm n k` is the
number of UNITS carries in its four additions — no `p`-digit carry can fire, because every one
of the four totals is below `p²`.  This is `ptp_run_endpoint_probe.py` arms E0 + E1 (4668448
and 678167 scorings, both GREEN) as a theorem. -/
theorem vp_cTerm_eq_units {n k p : ℕ} (hp : p ∈ phiWindow n)
    (hk : k ∈ candidateM.window n) :
    padicValNat p (cTerm n k) =
      cb p (k - 1) (13 * n) + cb p (k - 2 * n - 1) (9 * n)
        + cb p (k - 4 * n - 1) (5 * n) + cb p (11 * n) (k - 15 * n - 1) := by
  have hpp := prime_of_mem_phiWindow hp
  have : Fact p.Prime := ⟨hpp⟩
  have hsq : 26 * n + 1 < p ^ 2 := sq_gt_of_mem_phiWindow hp
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  have n1 : (k - 1).choose (13 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n2 : (k - 2 * n - 1).choose (9 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n3 : (k - 4 * n - 1).choose (5 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have n4 : (11 * n).choose (k - 15 * n - 1) ≠ 0 := Nat.choose_ne_zero (by omega)
  have l1 : Nat.log p (k - 1) ≤ 1 := log_le_one_of_lt_sq (by omega)
  have l2 : Nat.log p (k - 2 * n - 1) ≤ 1 := log_le_one_of_lt_sq (by omega)
  have l3 : Nat.log p (k - 4 * n - 1) ≤ 1 := log_le_one_of_lt_sq (by omega)
  have l4 : Nat.log p (11 * n) ≤ 1 := log_le_one_of_lt_sq (by omega)
  rw [cTerm, padicValNat.mul (mul_ne_zero (mul_ne_zero n1 n2) n3) n4,
    padicValNat.mul (mul_ne_zero n1 n2) n3, padicValNat.mul n1 n2,
    vp_choose_eq_cb (by omega) l1, vp_choose_eq_cb (by omega) l2,
    vp_choose_eq_cb (by omega) l3, vp_choose_eq_cb (by omega) l4]

/-! ## 3. What the open congruence gets: the run is its whole support -/

theorem cTerm_ne_zero {n k : ℕ} (hk : k ∈ candidateM.window n) : cTerm n k ≠ 0 := by
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  rw [cTerm]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Nat.choose_ne_zero (by omega))
    (Nat.choose_ne_zero (by omega))) (Nat.choose_ne_zero (by omega)))
    (Nat.choose_ne_zero (by omega))

/-- **Everything OUTSIDE the short run is already `0 mod p^v`.**  So the open congruence
`Σ_k (−1)^{k−1} cTerm(n,k) ≡ 0 mod p^φ̃` only ever has to look at the `k` whose units carries
fall short — which is the run, an interval of residues `u` fixed by `r = n % p`. -/
theorem pow_dvd_cTerm_of_units {n k p v : ℕ} (hp : p ∈ phiWindow n)
    (hk : k ∈ candidateM.window n)
    (hv : v ≤ cb p (k - 1) (13 * n) + cb p (k - 2 * n - 1) (9 * n)
              + cb p (k - 4 * n - 1) (5 * n) + cb p (11 * n) (k - 15 * n - 1)) :
    p ^ v ∣ cTerm n k := by
  have hpp := prime_of_mem_phiWindow hp
  have hne := cTerm_ne_zero hk
  rw [← vp_cTerm_eq_units hp hk] at hv
  rw [hpp.pow_dvd_iff_le_factorization hne, Nat.factorization_def _ hpp]
  exact hv

/-! ## 4. The run is a function of TWO residues — arm A10 as a theorem -/

/-- Cancellation of a common summand, modulo `p`.  `Nat.ModEq` is definitionally the `%`
equation this file's statements are written in. -/
theorem mod_cancel {p a b a' b' : ℕ} (hb : b % p = b' % p)
    (hs : (a + b) % p = (a' + b') % p) : a % p = a' % p :=
  Nat.ModEq.add_right_cancel hb hs

/-- **`ptp_cancel_probe` arm A10, as a theorem.**  `v_p(cTerm n k)` depends on `(n, k)` only
through `r = n % p` and `u = (k − 4n − 1) % p`.  That is exactly why the short residues form
the SAME run in every `p`-block of a cell (measured at 84 of 84 blocks there, and at 216471
(u, block) pairs by `ptp_run_endpoint_probe.py` arm E2) — nothing in the valuation can see
which block `k` sits in. -/
theorem vp_cTerm_residue_invariant {n k n' k' p : ℕ}
    (hp : p ∈ phiWindow n) (hp' : p ∈ phiWindow n')
    (hk : k ∈ candidateM.window n) (hk' : k' ∈ candidateM.window n')
    (hr : n % p = n' % p) (hu : (k - 4 * n - 1) % p = (k' - 4 * n' - 1) % p) :
    padicValNat p (cTerm n k) = padicValNat p (cTerm n' k') := by
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  obtain ⟨h1', h2'⟩ := (mem_window_iff n' k').1 hk'
  -- every coefficient of `n` has the same residue on both sides
  have mul_r : ∀ c : ℕ, (c * n) % p = (c * n') % p := by
    intro c; rw [Nat.mul_mod, hr, ← Nat.mul_mod]
  -- the three totals are `m + c·n`, so their residues follow from `hu` and `mul_r`
  have e1 : (k - 1) % p = (k' - 1) % p := by
    have a : k - 1 = (k - 4 * n - 1) + 4 * n := by omega
    have b : k' - 1 = (k' - 4 * n' - 1) + 4 * n' := by omega
    rw [a, b, Nat.add_mod, hu, mul_r 4, ← Nat.add_mod]
  have e2 : (k - 2 * n - 1) % p = (k' - 2 * n' - 1) % p := by
    have a : k - 2 * n - 1 = (k - 4 * n - 1) + 2 * n := by omega
    have b : k' - 2 * n' - 1 = (k' - 4 * n' - 1) + 2 * n' := by omega
    rw [a, b, Nat.add_mod, hu, mul_r 2, ← Nat.add_mod]
  -- the fourth index is `m − 11n`, recovered by cancelling `11n` from `(m−11n) + 11n = m`
  have e4 : (k - 15 * n - 1) % p = (k' - 15 * n' - 1) % p := by
    refine mod_cancel (mul_r 11) ?_
    have a : (k - 15 * n - 1) + 11 * n = k - 4 * n - 1 := by omega
    have b : (k' - 15 * n' - 1) + 11 * n' = k' - 4 * n' - 1 := by omega
    rw [a, b]; exact hu
  rw [vp_cTerm_eq_units hp hk, vp_cTerm_eq_units hp' hk']
  simp only [cb, e1, e2, e4, hu, mul_r 13, mul_r 9, mul_r 5, mul_r 11]

/-! ## 5. The smallest instance, and the negative that prices the hypothesis -/

/-- **The smallest instance of the run, by kernel computation.**  `n = 3`, `p = 13`,
`φ̃({3/13}) = 1`, window `k ∈ [46, 79]`, `u = (k − 13) % 13`: the short terms are EXACTLY those
with `u ≥ 8`, in all three `p`-blocks of the cell.  `8 = (7·r) % p` at `r = 3` and the run's
upper end is `p − 1 = 12`, so this is the closed form's own `[(7r)%p, p−1]` at its smallest
witness (`ptp_cancel_probe.out`'s A10 row `(3, 13, 1, 3, 8, 12, 3)`). -/
theorem run_at_3_13 : ∀ k ∈ Finset.Icc 46 79, (¬ (13 ∣ cTerm 3 k) ↔ 8 ≤ (k - 13) % 13) := by
  decide

/-- and the two endpoints of that run ARE the closed form's, at `r = 3`, `p = 13`. -/
theorem endpoints_at_3_13 : (7 * (3 % 13)) % 13 = 8 ∧ 13 - 1 = 12 := by decide

/-- **The window hypothesis is LOAD-BEARING.**  `n = 1`, `p = 2`, `k = 16`: `p² = 4 ≤ 27 = 26n+1`
so `2 ∉ phiWindow 1`; the four units carries are ALL ZERO and yet `2 ∣ cTerm 1 16`.  So
`vp_cTerm_eq_units` is FALSE the instant `26n+1 < p²` is dropped — the Legendre line is spent
here and is not decoration.  Probe control R3, which fires at 311 of 311 unfiltered primes. -/
theorem units_eq_needs_the_window :
    ¬ (26 * 1 + 1 < 2 ^ 2)
    ∧ cb 2 (16 - 1) (13 * 1) + cb 2 (16 - 2 * 1 - 1) (9 * 1)
        + cb 2 (16 - 4 * 1 - 1) (5 * 1) + cb 2 (11 * 1) (16 - 15 * 1 - 1) = 0
    ∧ 2 ∣ cTerm 1 16 := by decide

end Zeta2PtpRun

-- LEAN.md §1, 2026-09-20: `#print axioms` CANNOT see an undischarged hypothesis — a binder is
-- not an axiom, and a conditional theorem's footprint is byte-identical to an unconditional
-- one's — so acceptance is the receipt AND the printed TYPE, every binder read one by one.
-- They are paired here so the archive cannot carry one without the other.
#print axioms Zeta2PtpRun.carry_bit
#check @Zeta2PtpRun.carry_bit
#print axioms Zeta2PtpRun.log_le_one_of_lt_sq
#check @Zeta2PtpRun.log_le_one_of_lt_sq
#print axioms Zeta2PtpRun.vp_choose_eq_cb
#check @Zeta2PtpRun.vp_choose_eq_cb
#print axioms Zeta2PtpRun.vp_cTerm_eq_units
#check @Zeta2PtpRun.vp_cTerm_eq_units
#print axioms Zeta2PtpRun.cTerm_ne_zero
#check @Zeta2PtpRun.cTerm_ne_zero
#print axioms Zeta2PtpRun.pow_dvd_cTerm_of_units
#check @Zeta2PtpRun.pow_dvd_cTerm_of_units
#print axioms Zeta2PtpRun.mod_cancel
#check @Zeta2PtpRun.mod_cancel
#print axioms Zeta2PtpRun.vp_cTerm_residue_invariant
#check @Zeta2PtpRun.vp_cTerm_residue_invariant
#print axioms Zeta2PtpRun.run_at_3_13
#check @Zeta2PtpRun.run_at_3_13
#print axioms Zeta2PtpRun.endpoints_at_3_13
#check @Zeta2PtpRun.endpoints_at_3_13
#print axioms Zeta2PtpRun.units_eq_needs_the_window
#check @Zeta2PtpRun.units_eq_needs_the_window
