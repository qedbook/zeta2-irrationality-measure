/-
# Row PT-P, layer 1 — the reduction to `ΔT`, and two measured negatives

PT-P is `(Zeta2PhiT.PhiT n : ℤ) ∣ P n` for PNCLR's witness `P`, and PNCLR closed on
2026-09-19 (`Zeta2PnHarmDelta.pn_cleared_1615`, hypothesis-free), so the witness exists for
the first time.  This file does everything the row needs EXCEPT its per-prime arithmetic, and
states precisely what is left.

**WHICH `Δ` — read this first.**  `Zeta2PnHarmDelta.binders_1615` delivers `hΔne`/`hQ`/`hP` at
the UN-DIVIDED `Zeta2Arith.Δ 16 15`, while the capstone's rate binders are at
`Zeta2PhiT.ΔT = Δ 16 15 / Φ̃` — `Zeta2DRate.ΔT_growth` and `ΔT_clearing_rate` are stated there
and nowhere else, and `Zeta2PhiT.ΔT_one_ne_naive` records that the two are different numbers.
PT-P *is* the division between them.  So this file's deliverable is `hP` AT `ΔT`
(`hP_at_ΔT_of_perPrime`), not at `Δ 16 15`: a row that closed at the un-divided `Δ` would
leave the chain with binders no landed rate covers, which is LEAN.md §0a's binder trap in its
exact original shape (μ ≈ 659 rather than 5.0495).

**1. The reduction.**  `PhiT n` is a product of prime powers over DISTINCT primes, so the
divisibility is equivalent to one inequality per prime of `phiWindow n`.
`PhiT_dvd_of_forall_factorization` is that equivalence's useful direction;
`hP_at_ΔT_of_perPrime` runs it all the way to the binder shape the chain consumes.

**2. A window prime's exact contribution.**  `factorization_Delta_eq_two`: for
`p ∈ phiWindow n` and `n ≥ 1`, `v_p(Δ 16 15 n) = 2` — EXACTLY 2, both `⌊log_p⌋` terms being 1
because `p ≤ 15n < 16n ≤ 26n < 26n+1 < p²`.  This is the row's tight margin in one line: the
clearing factor supplies a fixed 2 at every window prime and the profile asks for up to 2
(`Zeta2PhiTRate.phiT_le_two`), so there is no room anywhere.  `ptp_phit_probe.py` measures the
consequence — slack exactly 0 at 357 of 366 cells.

**3. Two measured negatives, promoted to theorems so nobody re-derives them.**

  * `not_pressured` — **PNCLR's mechanism is INERT on this row's primes, by arithmetic.**
    `Zeta2PnHarmDelta.two_carries` needs `15n < p^E` at `E = ⌊log_p (k−4n−1)⌋`.  For
    `p ∈ phiWindow n` that is unsatisfiable: `k−4n−1 ≤ 22n < 26n+1 < p²` forces `E ≤ 1`, hence
    `p^E ≤ p ≤ 15n`.  PNCLR's pressured regime `p^E ∈ (15n, 22n]` and PT-P's window `p ≤ 15n`
    are DISJOINT sets of prime powers, so the two-carries-in-two-factors observation that
    collapsed PNCLR does not transfer here at all.  Measured first at all 366 cells of
    `ptp_phit_probe.py` arm A5; proved here, so it is a theorem and not a sample.

  * `termwise_route_fails` / `prime_mul_D_sq_not_dvd` — **the obvious next lemma after
    `harm_dvd` is FALSE.**  `Zeta2PnHarmDelta.harm_dvd` gives `D(m)² ∣ Δ·cTerm` on the window;
    the natural PT-P strengthening multiplies the left side by the profile's prime power, and
    the witness `n = 3, p = 13, k = 47` kills it: `φ̃({3/13}) = 1` but `13 ∤ cTerm 3 47`, while
    `v₁₃(Δ 16 15 3) = 2 = 2·⌊log₁₃ 34⌋`, so the term has nothing left to give.
    `ptp_phit_probe.py` finds 23 such cells among 366 and measures that the SUM over the
    window's `k` beats its worst term by EXACTLY 1 at every one of them — so what the termwise
    route leaves open is one unit of cancellation across `k`, never more.

**WHAT IS LEFT, and it is the whole of PT-P's difficulty:** the per-prime inequality
`φ̃({n/p}) ≤ v_p(P n)` for `p ∈ phiWindow n`.  The probe measures it at 366 cells with zero
violations and slack 0 at 357, so it is TRUE and TIGHT.  It is not proved here, and
`Zeta2Target.zeta2_not_liouvilleWith` stays `sorry`.

Probe: `ptp_phit_probe.py` / `ptp_phit_probe.out` (9 arms, 6 kill controls, 5 recorded inert).
Census: `Zeta2PhiTDvdCensus.lean` / `out_phitdvd_census.txt` (both directions, two absences).
Falsifier: `falsify_phitdvd.sh` / `out_phitdvd_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2Profile
import Zeta2PhiT
import Zeta2PnCleared
import Zeta2PnHarmDelta

namespace Zeta2PhiTDvd

open Zeta2Defs Zeta2Arith Zeta2PhiT Nat Finset

/-! ## 1. What membership of `phiWindow` gives -/

/-- `p ∈ phiWindow n → p ≤ 15n`.  `Zeta2PhiT` exports the primality and the Legendre line but
not this; it comes from `Nat.primesLE` (census §6). -/
theorem le_of_mem_phiWindow {n p : ℕ} (hp : p ∈ phiWindow n) : p ≤ 15 * n :=
  Nat.le_of_mem_primesLE (Finset.mem_filter.mp hp).1

/-- **`⌊log_p (c·n)⌋ = 1` at a window prime**, for any `c` with `p ≤ c·n ≤ 26n`.  Both bounds
come from the window: `p ≤ c·n` gives `≥ 1`, and `c·n ≤ 26n < 26n+1 < p²` gives `< 2`. -/
theorem log_eq_one_of_mem_phiWindow {n p c : ℕ} (hp : p ∈ phiWindow n)
    (hle : p ≤ c * n) (hc : c * n ≤ 26 * n) : Nat.log p (c * n) = 1 := by
  have hpp := prime_of_mem_phiWindow hp
  have h1 : 1 < p := hpp.one_lt
  have hsq : 26 * n + 1 < p ^ 2 := sq_gt_of_mem_phiWindow hp
  have hlow : 1 ≤ Nat.log p (c * n) := by
    refine Nat.le_log_of_pow_le h1 ?_
    simpa using hle
  have hhigh : Nat.log p (c * n) < 2 := by
    refine Nat.log_lt_of_lt_pow (by omega) ?_
    omega
  omega

/-- **A window prime's exact contribution to the clearing factor: `v_p(Δ 16 15 n) = 2`.** -/
theorem factorization_Delta_eq_two {n p : ℕ} (hn : 1 ≤ n) (hp : p ∈ phiWindow n) :
    (Δ 16 15 n).factorization p = 2 := by
  have hpp := prime_of_mem_phiWindow hp
  have hle := le_of_mem_phiWindow hp
  have h16 : Nat.log p (16 * n) = 1 :=
    log_eq_one_of_mem_phiWindow hp (by omega) (by omega)
  have h15 : Nat.log p (15 * n) = 1 :=
    log_eq_one_of_mem_phiWindow hp (by omega) (by omega)
  rw [Zeta2Arith.Δ, Nat.factorization_mul (D_ne_zero _) (D_ne_zero _), Finsupp.add_apply,
    Zeta2PhiT.factorization_D _ hpp, Zeta2PhiT.factorization_D _ hpp, h16, h15]

/-! ## 2. PNCLR's mechanism is INERT on this row's primes

`Zeta2PnHarmDelta.two_carries` is the whole of PNCLR's content and its window hypothesis is
`hlo : 15 * n < p ^ E` at `E = Nat.log p (k − 4n − 1)`.  At a prime of `phiWindow n` that is
FALSE, so the lemma is UNAVAILABLE to PT-P — not merely unhelpful.  Measured at all 366 cells
of the probe's arm A5 before it was proved. -/

/-- The top level of `m = k − 4n − 1` at a window prime is at most 1: `m ≤ 22n < p²`. -/
theorem log_window_le_one {n k p : ℕ} (hp : p ∈ phiWindow n)
    (hk : k ∈ candidateM.window n) : Nat.log p (k - 4 * n - 1) ≤ 1 := by
  have hpp := prime_of_mem_phiWindow hp
  have h1 : 1 < p := hpp.one_lt
  have hsq : 26 * n + 1 < p ^ 2 := sq_gt_of_mem_phiWindow hp
  obtain ⟨hk1, hk2⟩ := (mem_window_iff n k).1 hk
  rcases Nat.eq_zero_or_pos (k - 4 * n - 1) with h0 | hpos
  · rw [h0]; simp
  · have h2 : Nat.log p (k - 4 * n - 1) < 2 := by
      refine Nat.log_lt_of_lt_pow (by omega) ?_
      omega
    omega

/-- **The negative, as a theorem.**  `two_carries`'s window hypothesis cannot hold at a prime
of `phiWindow n`, because `p ^ ⌊log_p m⌋ ≤ p ≤ 15n`. -/
theorem not_pressured {n k p : ℕ} (hp : p ∈ phiWindow n)
    (hk : k ∈ candidateM.window n) : ¬ (15 * n < p ^ Nat.log p (k - 4 * n - 1)) := by
  have hle := le_of_mem_phiWindow hp
  have hlog := log_window_le_one hp hk
  have hpp := prime_of_mem_phiWindow hp
  have hbound : p ^ Nat.log p (k - 4 * n - 1) ≤ p := by
    calc p ^ Nat.log p (k - 4 * n - 1) ≤ p ^ 1 :=
          Nat.pow_le_pow_right (le_of_lt hpp.one_lt) hlog
      _ = p := pow_one p
  omega

/-! ## 3. The reduction — the row IS the per-prime family -/

/-- `Φ̃ₙ`'s factorization at a window prime is the profile value there.  The factors are
`p ^ φ̃({n/p})` over DISTINCT primes, so nothing else in the product contributes. -/
theorem factorization_PhiT {n q : ℕ} (hq : q ∈ phiWindow n) :
    (PhiT n).factorization q = phiT (Int.fract ((n : ℚ) / (q : ℚ))) := by
  classical
  have hne : ∀ p ∈ phiWindow n, p ^ phiT (Int.fract ((n : ℚ) / (p : ℚ))) ≠ 0 := fun p hp =>
    pow_ne_zero _ (prime_of_mem_phiWindow hp).pos.ne'
  have hoff : ∀ p ∈ phiWindow n, p ≠ q →
      (Nat.factorization (p ^ phiT (Int.fract ((n : ℚ) / (p : ℚ))))) q = 0 := by
    intro p hp hpq
    have hpp := prime_of_mem_phiWindow hp
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hpp.factorization,
      Finsupp.single_apply]
    simp [hpq]
  rw [PhiT, Nat.factorization_prod hne, Finset.sum_apply',
    Finset.sum_eq_single_of_mem q hq hoff]
  have hqp := prime_of_mem_phiWindow hq
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hqp.factorization,
    Finsupp.single_apply]
  simp

/-- `Φ̃ₙ`'s factorization vanishes off the window. -/
theorem factorization_PhiT_off {n q : ℕ} (hq : q ∉ phiWindow n) :
    (PhiT n).factorization q = 0 := by
  classical
  have hne : ∀ p ∈ phiWindow n, p ^ phiT (Int.fract ((n : ℚ) / (p : ℚ))) ≠ 0 := fun p hp =>
    pow_ne_zero _ (prime_of_mem_phiWindow hp).pos.ne'
  rw [PhiT, Nat.factorization_prod hne, Finset.sum_apply']
  refine Finset.sum_eq_zero ?_
  intro p hp
  have hpp := prime_of_mem_phiWindow hp
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hpp.factorization,
    Finsupp.single_apply]
  simp [hpq]

/-- **The reduction, over ℕ.**  `Φ̃ₙ ∣ z` as soon as the profile value is under `v_p(z)` at
every prime of the window — and there is nothing else to check. -/
theorem PhiT_dvd_of_forall_factorization (n z : ℕ)
    (h : ∀ p ∈ phiWindow n, phiT (Int.fract ((n : ℚ) / (p : ℚ))) ≤ z.factorization p) :
    PhiT n ∣ z := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · exact dvd_zero _
  rw [← Nat.factorization_le_iff_dvd (PhiT_ne_zero n) hz.ne', Finsupp.le_def]
  intro q
  by_cases hq : q ∈ phiWindow n
  · rw [factorization_PhiT hq]; exact h q hq
  · rw [factorization_PhiT_off hq]; exact Nat.zero_le _

/-- **The reduction, in PT-P's own ℤ vocabulary.** -/
theorem PhiT_dvd_int_of_forall_factorization (n : ℕ) (z : ℤ)
    (h : ∀ p ∈ phiWindow n, phiT (Int.fract ((n : ℚ) / (p : ℚ))) ≤ z.natAbs.factorization p) :
    (PhiT n : ℤ) ∣ z :=
  Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (PhiT_dvd_of_forall_factorization n _ h))

/-- **Row PT-P's own statement, reduced to its arithmetic core.**  With PNCLR's witness landed,
`(Φ̃ₙ : ℤ) ∣ P n` is exactly the per-prime family and nothing else. -/
theorem PhiT_dvd_P_of_perPrime
    (hpp : ∀ (P : ℕ → ℤ),
      (∀ m, (P m : ℚ) = ((Δ 16 15 m : ℕ) : ℚ) * candidateM.pn m) →
      ∀ (n : ℕ), ∀ p ∈ phiWindow n,
        phiT (Int.fract ((n : ℚ) / (p : ℚ))) ≤ (P n).natAbs.factorization p) :
    ∃ P : ℕ → ℤ,
      (∀ n, (P n : ℚ) = ((Δ 16 15 n : ℕ) : ℚ) * candidateM.pn n) ∧
      (∀ n, (PhiT n : ℤ) ∣ P n) := by
  obtain ⟨P, hP⟩ := Zeta2PnHarmDelta.pn_cleared_1615
  exact ⟨P, hP, fun n => PhiT_dvd_int_of_forall_factorization n (P n) (hpp P hP n)⟩

/-! ## 4. The row's OUTPUT binder — `hP` at `ΔT`, which is where the chain's rate lives -/

/-- **PT-P's deliverable.**  `Zeta2PnHarmDelta.binders_1615` hands the chain `hP` at the
UN-DIVIDED `Zeta2Arith.Δ 16 15`; `Zeta2DRate.ΔT_growth` and `ΔT_clearing_rate` are stated at
`Zeta2PhiT.ΔT = Δ 16 15 / Φ̃`, and `Zeta2PhiT.ΔT_one_ne_naive` records that those are different
numbers.  This is the bridge, and it is the reason PT-P exists: given the per-prime family, the
cleared numerator `P̃ n = P n / Φ̃ₙ` is an INTEGER and satisfies `hP` at `ΔT`. -/
theorem hP_at_ΔT_of_perPrime
    (hpp : ∀ (P : ℕ → ℤ),
      (∀ m, (P m : ℚ) = ((Δ 16 15 m : ℕ) : ℚ) * candidateM.pn m) →
      ∀ (n : ℕ), ∀ p ∈ phiWindow n,
        phiT (Int.fract ((n : ℚ) / (p : ℚ))) ≤ (P n).natAbs.factorization p) :
    ∃ P : ℕ → ℤ, ∀ n, (P n : ℝ) = ΔT n * ((candidateM.pn n : ℚ) : ℝ) := by
  classical
  obtain ⟨P, hP, hdvd⟩ := PhiT_dvd_P_of_perPrime hpp
  choose c hc using fun n => hdvd n
  refine ⟨c, fun n => ?_⟩
  have hΦ : ((PhiT n : ℕ) : ℝ) ≠ 0 := PhiT_cast_ne_zero n
  have hPn : ((P n : ℤ) : ℝ) = ((Δ 16 15 n : ℕ) : ℝ) * ((candidateM.pn n : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) (hP n)
  have hcn : ((PhiT n : ℕ) : ℝ) * ((c n : ℤ) : ℝ) = ((P n : ℤ) : ℝ) := by
    rw [hc n]; push_cast; ring
  have : ((PhiT n : ℕ) : ℝ) * ((c n : ℤ) : ℝ)
      = ((PhiT n : ℕ) : ℝ) * (ΔT n * ((candidateM.pn n : ℚ) : ℝ)) := by
    rw [hcn, hPn, ← ΔT_mul_PhiT n]
    ring
  exact mul_left_cancel₀ hΦ this

/-! ## 5. The measured negative that kills the obvious route

`Zeta2PnHarmDelta.harm_dvd` proves `D(k−4n−1)² ∣ Δ 16 15 n · cTerm n k` on the window.  The
one-line strengthening PT-P appears to want multiplies the left side by the profile's prime
power — and it is FALSE. -/

/-- **The counterexample, four `decide`-checked facts.**  `n = 3`, `p = 13`, `k = 47`: the prime
is in the window, `k` is in the window, `φ̃({3/13}) = 1`, and `13 ∤ cTerm 3 47`. -/
theorem termwise_route_fails :
    13 ∈ phiWindow 3 ∧
    47 ∈ candidateM.window 3 ∧
    phiT (Int.fract ((3 : ℚ) / (13 : ℚ))) = 1 ∧
    ¬ ((13 : ℕ) ∣ cTerm 3 47) :=
  ⟨by decide +kernel, by decide, by decide +kernel, by decide +kernel⟩

/-- The three `⌊log₁₃⌋` values the cell turns on: the clearing factor's two are spent exactly
on `2·⌊log₁₃ 34⌋`, so the term has nothing left over for `φ̃`. -/
theorem logs_at_the_cell :
    Nat.log 13 (16 * 3) = 1 ∧ Nat.log 13 (15 * 3) = 1 ∧ Nat.log 13 (47 - 4 * 3 - 1) = 1 :=
  ⟨Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num),
   Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num),
   Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)⟩

/-- **The strengthening someone would write, refuted at its own witness.**  `harm_dvd` gives
`D(34)² ∣ Δ 16 15 3 · cTerm 3 47`; multiplying the divisor by the profile's `13` does NOT, and
the reason is exactly `factorization_Delta_eq_two` — the clearing supplies 2 and `2·⌊log₁₃ 34⌋`
consumes all of it.  So the PNCLR-shaped termwise route cannot close PT-P; the probe measures
that the SUM over `k` is what supplies the missing 1, at all 23 short cells. -/
theorem prime_mul_D_sq_not_dvd :
    ¬ ((13 : ℕ) * (D (47 - 4 * 3 - 1)) ^ 2 ∣ Δ 16 15 3 * cTerm 3 47) := by
  obtain ⟨hw, _, _, hnd⟩ := termwise_route_fails
  obtain ⟨_, _, hlm⟩ := logs_at_the_cell
  -- NOT `by norm_num`: the `Nat.Prime` norm_num extension is not in this file's import set,
  -- and it failed here on 2026-09-20 (census §6's lesson, one level down).
  have hp13 : Nat.Prime 13 := by decide
  have hct : cTerm 3 47 ≠ 0 := by decide +kernel
  have hDne : (D (47 - 4 * 3 - 1)) ^ 2 ≠ 0 := pow_ne_zero _ (D_ne_zero _)
  have hLne : (13 : ℕ) * (D (47 - 4 * 3 - 1)) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) hDne
  have hRne : Δ 16 15 3 * cTerm 3 47 ≠ 0 := mul_ne_zero (Δ_ne_zero 16 15 3) hct
  intro hdvd
  have hle := ((Nat.factorization_le_iff_dvd hLne hRne).mpr hdvd)
  have hat := (Finsupp.le_def.mp hle) 13
  -- left: `v₁₃(13) + 2·⌊log₁₃ 34⌋ = 1 + 2 = 3`
  have hL : ((13 : ℕ) * (D (47 - 4 * 3 - 1)) ^ 2).factorization 13 = 3 := by
    rw [Nat.factorization_mul (by norm_num) hDne, Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul, Zeta2PhiT.factorization_D _ hp13, hlm,
      hp13.factorization, Finsupp.single_apply]
    simp
  -- right: `v₁₃(Δ) + v₁₃(cTerm) = 2 + 0 = 2`
  have hR : (Δ 16 15 3 * cTerm 3 47).factorization 13 = 2 := by
    rw [Nat.factorization_mul (Δ_ne_zero 16 15 3) hct, Finsupp.add_apply,
      factorization_Delta_eq_two (by norm_num) hw,
      Nat.factorization_eq_zero_of_not_dvd hnd]
  rw [hL, hR] at hat
  omega

end Zeta2PhiTDvd

#print axioms Zeta2PhiTDvd.le_of_mem_phiWindow
#print axioms Zeta2PhiTDvd.log_eq_one_of_mem_phiWindow
#print axioms Zeta2PhiTDvd.factorization_Delta_eq_two
#print axioms Zeta2PhiTDvd.log_window_le_one
#print axioms Zeta2PhiTDvd.not_pressured
#print axioms Zeta2PhiTDvd.factorization_PhiT
#print axioms Zeta2PhiTDvd.factorization_PhiT_off
#print axioms Zeta2PhiTDvd.PhiT_dvd_of_forall_factorization
#print axioms Zeta2PhiTDvd.PhiT_dvd_int_of_forall_factorization
#print axioms Zeta2PhiTDvd.PhiT_dvd_P_of_perPrime
#print axioms Zeta2PhiTDvd.hP_at_ΔT_of_perPrime
#print axioms Zeta2PhiTDvd.termwise_route_fails
#print axioms Zeta2PhiTDvd.logs_at_the_cell
#print axioms Zeta2PhiTDvd.prime_mul_D_sq_not_dvd
