/-
# Row PAIR-4L — the `ln 2` coordinate vanishes, for EVERY `n` and at EVERY cell

`docs/future/zeta2-lean-chain.md` row PAIR-4L.  `Φ̂`'s third coordinate is `Σ_k B_k`, the sum of
the hat member's ORDER-1 partial-fraction coefficients over all its poles, and the row asserts it
is `0`.  `Zeta2HatRepOne` proved that by kernel computation at `n = 1` (417 ms) and `n = 2`
(1.64 s); `hat_rep_probe.out` §B measures it in exact ℚ at `n ≤ 6`.  This file is the ∀n proof.

**The route is (ii), the leading-coefficient corollary, not (i), the standalone residue lemma.**
The row recorded both and preferred (i) *while (ii)'s input was a pending row*.  It is not pending
any more: PAIR-4R's third pass discharged all six local residue obligations, so `hat_cleared` —
the CLEARED polynomial identity — is available with nothing to carry (`Zeta2HatResidues.hat_h1`
/ `hat_h2` / `hat_h3`).  And the cleared identity already contains the answer:

    Π̂·Û  =  Σ_{k ∈ S₁} b_k·pf1 k  +  Σ_{k ∈ S₂} (b_k·(X − k)·pf2 k  +  a_k·pf2 k)

with every `pf1 k` and every `(X − k)·pf2 k` MONIC of degree `22n + 1` and every `pf2 k` of
degree `22n`, against `natDegree (Π̂·Û) ≤ 22n`.  Reading the coefficient of `X^{22n+1}` gives
`0 = Σ_{S₁} b + Σ_{S₂} b` — the order-2 coefficients `a_k` do not appear at all.  That is the
generic `Zeta2PF.sum_order1_eq_zero`, and this file is its instance.

So the "residue at ∞ of a rational function with deg num ≤ deg den − 2" of the PAIR design notes
is here with no analysis in it: it is one `Polynomial.coeff`, and the **margin two** it needs
(`22n + 1 < 22n + 2`) is `Zeta2HatPoles.hat_hdeg_two`, a strictly stronger statement than the
`hat_hdeg` `partialFractions` itself consumes.  Route (i) was never elaborated; route (ii) needed
no new lemma beyond the generic coefficient read.

**No engine literal is emitted by this row.**  Everything here is degree and index bookkeeping
over objects already in the corpus, so there is no hand-entered datum for a §6 cross-check to
check.  What is load-bearing is instead the DEGREE MARGIN and the COORDINATE INDEX, and both are
made reddable by the two `sed` arms E and F recorded in `out_hatpoles_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2HatResidues

namespace Zeta2HatLn2

open Zeta2Defs Zeta2Hat Zeta2HatRep Zeta2HatPoles Zeta2HatResidues Polynomial Finset

set_option profiler true
set_option profiler.threshold 100

/-- The cleared identity with **nothing left to discharge** — `hat_cleared` at the three residue
hypotheses PAIR-4R landed.  `hat_rep` divides this by the written denominator; this row reads its
top coefficient instead, and the two uses share one statement rather than two copies. -/
theorem hat_cleared_uncond (n : ℕ) :
    C (hatPi n) * hatNum n
      = (∑ k ∈ poleS1 n, C (bhat n k) * Zeta2PF.pf1 (poleS1 n) (poleS2 n) k)
        + ∑ k ∈ poleS2 n, (C (bhat n k) * ((X - C k) * Zeta2PF.pf2 (poleS1 n) (poleS2 n) k)
          + C (ahat n k) * Zeta2PF.pf2 (poleS1 n) (poleS2 n) k) :=
  hat_cleared n (hat_h1 n) (hat_h2 n) (hat_h3 n)

/-- **The top coefficient**, still at the ℚ nodes.  `hat_hdeg_two` is the whole content: with the
margin only ONE this sum would be the leading coefficient of `Π̂·Û` and there would be no
theorem. -/
theorem sum_bhat_zero (n : ℕ) :
    (∑ k ∈ poleS1 n, bhat n k) + ∑ k ∈ poleS2 n, bhat n k = 0 :=
  Zeta2PF.sum_order1_eq_zero (poleS1 n) (poleS2 n) (C (hatPi n) * hatNum n) (bhat n) (ahat n)
    (hat_hdeg_two n) (hat_cleared_uncond n)

/-- The same sum back in the hat's ℕ index vocabulary. -/
theorem sum_repHatB_zero (n : ℕ) :
    (∑ κ ∈ idxS1 n, repHatB n κ) + ∑ κ ∈ idxS2 n, repHatB n κ = 0 := by
  have h := sum_bhat_zero n
  rw [sum_poleS1 n (bhat n), sum_poleS2 n (bhat n)] at h
  simpa only [bhat_at] using h

/-- …and over the WRITTEN denominator's whole root run, which is the index set `repHatB`'s
support sits inside. -/
theorem sum_repHatB_Icc_zero (n : ℕ) :
    ∑ κ ∈ Icc (7 * n + 1) (20 * n + 1), repHatB n κ = 0 := by
  rw [← idxS1_union_idxS2, Finset.sum_union (idxS1_disjoint_idxS2 n)]
  exact sum_repHatB_zero n

/-- **ROW PAIR-4L**: the `ln 2` coordinate of `Φ̂` is `0`, for every `n` and at every cell `N`.

The cell is a FREE variable for the same reason it is in `Phihat_zeta2_coord`: the third
coordinate is a bare coefficient sum and never sees the alternating-sum length `L`.  So PAIR-6
inherits no belt hypothesis from this row either — only the RATIONAL coordinate does, through
PAIR-4C. -/
theorem ln2_coord (N n : ℕ) : (Phihat N (repHat n)).2.2 = 0 := by
  show (repHatB n).sum (fun _ b => b) = 0
  rw [Finsupp.sum_of_support_subset _ (repHatB_support n) _ (fun i _ => rfl)]
  exact sum_repHatB_Icc_zero n

/-- The row's statement in the FAMILIES it is written with: `Σ_j A_j·Λ_j + Σ_i Blo_i + Σ_i Bhi_i
= 0`.  This is the form `Zeta2HatRepOne.ln2_coord_one` / `_two` computed in the kernel at `n = 1`
and `n = 2`, and the form `hat_rep_probe.py` §B measures in exact ℚ at `n ≤ 6` — stated here so
the ∀n theorem and the small-instance evidence are visibly about the same sum. -/
theorem sum_B_eq_zero (n : ℕ) :
    (∑ j ∈ range (8 * n + 1), (hatA n j : ℚ) * hatLam n j)
      + (∑ i ∈ range n, hatBlo n i) + ∑ i ∈ range (2 * n), hatBhi n i = 0 := by
  have h : (repHatB n).sum (fun _ b => b) = 0 := ln2_coord 0 n
  rw [repHatB_sum (g := fun _ b => b) (fun _ => rfl) (fun _ _ _ => rfl)] at h
  -- `repHatB_sum` leaves `(fun _ b => b) k v` redexes; `simp only []` is the beta step alone,
  -- deliberately with an EMPTY lemma set so nothing rewrites the three sums themselves.
  simpa only [] using h

/-- **`Φ̂` at the member's OWN cell, all three coordinates, for every `n`.**
`Zeta2HatRep.Phihat_zero` was this at `n = 0` alone, because the third coordinate was the missing
one.  This is PAIR-4's two coordinates plus PAIR-4L's third; `Φ̂_member` (PAIR-4C) is the same
statement with the cell moved to a NEIGHBOUR's, which is a different theorem and not this one. -/
theorem Phihat_own (n : ℕ) : Phihat n (repHat n) = (hatP n, -(hatQ n : ℚ), 0) := by
  rw [Prod.ext_iff, Prod.ext_iff]
  exact ⟨Phihat_rat_coord n, Phihat_zeta2_coord n n, ln2_coord n n⟩

end Zeta2HatLn2

#print axioms Zeta2HatLn2.hat_cleared_uncond
#print axioms Zeta2HatLn2.sum_bhat_zero
#print axioms Zeta2HatLn2.sum_repHatB_zero
#print axioms Zeta2HatLn2.sum_repHatB_Icc_zero
#print axioms Zeta2HatLn2.ln2_coord
#print axioms Zeta2HatLn2.sum_B_eq_zero
#print axioms Zeta2HatLn2.Phihat_own
