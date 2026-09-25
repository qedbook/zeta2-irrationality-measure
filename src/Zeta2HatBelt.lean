/-
# Row PAIR-4C — belt invariance: `Φ̂_member`'s cell hypothesis, for every `(n, j)`

`docs/future/zeta2-lean-chain.md` row PAIR-4C.  PAIR-6 applies ONE functional to all four members
of the recurrence, so the cell is `Ĉ n` while `hatP (n+j)` is BUILT at `Ĉ (n+j)`.  The row asserts
they agree when `Ĉ n` lies in member `n+j`'s separating belt, and `hat_rep_probe.out` §C measured
that on 22 of 22 `(n,j)` pairs at `n ≤ 6` — 18 agree, 4 fail, and agreement ⟺ the inequality, the
failures in the RATIONAL coordinate alone.  `Zeta2HatRepOne.belt_rat_coord_one_one` proved the
smallest instance with `j > 0` by kernel computation (4.64 s).  This file is the ∀(n,j) proof.

**The mechanism, and it is not a contour argument in Lean.**  Moving the cell from `Ĉ (n+j)` to
`Ĉ n` adds exactly `8j` to EVERY alternating-sum length `L_k = 2k − 8N − 2`, at all three pole
runs and with no other change.  `altH` splits at any length, so the difference is a sum over the
`8j` extra terms; every length in play is EVEN, so the extra signs do not depend on which run the
pole is in; and swapping the two summations turns the whole difference into

    Σ_{u < 8j} (−1)^{u+1} · ½ · evalRep (repHat m) t_u,        t_u = (u − 8m − 1)/2

because at `t_u` the node `t_u + k` is `(L_k + u + 1)/2` for EVERY pole `k` of the member, on all
three runs at once.  That is the whole content: the belt difference is the member's own
representation, sampled at `8j` half-integer points.

**So PAIR-4R is what closes this row.**  `evalRep (repHat m) t_u = Π̂(m)·hatMember m t_u`, and
`hatMember` has the numerator factor `∏_{l=3m+2}^{20m+1} (2t + l)`, which VANISHES at `t_u` as
soon as `8m + 1 − u` lands in `[3m+2, 20m+1]` — i.e. as soon as `u + 1 ≤ 5m`.  Over `u < 8j` that
is `8j ≤ 5(n+j)`, i.e. `3j ≤ 5n`, which `j ≤ 3` and `2 ≤ n` give with room (`9 ≤ 10`).  The row's
recorded belt is `3j ≤ 5n + 1` — one wider, because it also admits the EVEN `u` where the second
numerator run `∏_{l=1}^{5m}(t + l)` vanishes instead.  That extra case is not needed at `j ≤ 3`
and is deliberately not built: the hypothesis this row owes PAIR-6 is `2 ≤ n`, and the sufficient
condition proved here covers all of it.

**No engine literal is emitted by this row** either — every number here is an index, and the
coefficient families come from PAIR-0's landed definitions.  The load-bearing claims are the SHIFT
`8j` and the vanishing INDEX `8m + 1 − u`, and both are made reddable by arms G and H in
`out_hatpoles_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2HatLn2

namespace Zeta2HatBelt

open Zeta2Defs Zeta2Hat Zeta2HatRep Zeta2HatPoles Zeta2HatResidues Zeta2HatLn2 Finset

set_option profiler true
set_option profiler.threshold 100

/-! ## 1. `altH` under a shift of its LENGTH -/

/-- `altH` splits at any length: the extra `C` terms are the run `[L+1, L+C]`. -/
theorem altH_add (s L C : ℕ) :
    altH s (L + C)
      = altH s L + ∑ u ∈ range C, (-1 : ℚ) ^ (L + u + 1) / (((L + u : ℕ) : ℚ) + 1) ^ s := by
  rw [altH, altH, Finset.sum_range_add]

/-- For an EVEN length the extra terms' SIGNS do not depend on `L` — which is what lets the three
pole runs, whose lengths differ, be shifted by one common alternating pattern. -/
theorem altH_add_even (s L C : ℕ) (hL : Even L) :
    altH s (L + C)
      = altH s L + ∑ u ∈ range C, (-1 : ℚ) ^ (u + 1) / (((L + u : ℕ) : ℚ) + 1) ^ s := by
  rw [altH_add]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun u _ => ?_)
  rw [show L + u + 1 = L + (u + 1) from by omega, pow_add, hL.neg_one_pow, one_mul]

/-- **The shift, for a whole coefficient family at once**, with the two summations swapped so the
`u`-slice — not the pole — is the outer index.  This is the step that turns "each pole's
alternating sum grew by `8j` terms" into "the difference is the member evaluated at `8j`
points". -/
theorem shift_family {ι : Type*} (T : Finset ι) (c : ι → ℚ) (L : ι → ℕ) (C s : ℕ)
    (hL : ∀ k ∈ T, Even (L k)) :
    ∑ k ∈ T, c k * altH s (L k + C)
      = (∑ k ∈ T, c k * altH s (L k))
        + ∑ u ∈ range C, (-1 : ℚ) ^ (u + 1) * ∑ k ∈ T, c k / (((L k + u : ℕ) : ℚ) + 1) ^ s := by
  have hstep : ∀ k ∈ T, c k * altH s (L k + C)
      = c k * altH s (L k)
        + ∑ u ∈ range C, (-1 : ℚ) ^ (u + 1) * (c k / (((L k + u : ℕ) : ℚ) + 1) ^ s) := by
    intro k hk
    rw [altH_add_even s (L k) C (hL k hk), mul_add, Finset.mul_sum]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun u _ => ?_)
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) rfl ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]

/-! ## 2. The sample points — one `t_u` serves all three pole runs -/

/-- `t_u = (u − 8m − 1)/2`, the point the `u`-th extra alternating term samples. -/
def beltPt (m u : ℕ) : ℚ := ((u : ℚ) - 8 * m - 1) / 2

theorem beltPt_double (m u j : ℕ) :
    beltPt m u + ((10 * m + 1 + j : ℕ) : ℚ) = (((12 * m + 2 * j + u : ℕ) : ℚ) + 1) / 2 := by
  rw [beltPt]; push_cast; ring

theorem beltPt_lo (m u i : ℕ) :
    beltPt m u + ((9 * m + 1 + i : ℕ) : ℚ) = (((10 * m + 2 * i + u : ℕ) : ℚ) + 1) / 2 := by
  rw [beltPt]; push_cast; ring

theorem beltPt_hi (m u i : ℕ) :
    beltPt m u + ((18 * m + 2 + i : ℕ) : ℚ) = (((28 * m + 2 + 2 * i + u : ℕ) : ℚ) + 1) / 2 := by
  rw [beltPt]; push_cast; ring

theorem div_half (c y : ℚ) : c / (y / 2) = 2 * (c / y) := by
  rw [div_div_eq_mul_div]; ring

theorem div_half_sq (c y : ℚ) : c / (y / 2) ^ 2 = 4 * (c / y ^ 2) := by
  rw [div_pow, div_div_eq_mul_div]; ring

/-- **`evalRep` at a sample point IS the `u`-slice of the belt difference**, up to the factor 2
that the half-integer node introduces.  The three `beltPt_*` identities are what make this one
theorem rather than three: at `t_u` every pole's node is `(L_k + u + 1)/2`, on all three runs. -/
theorem evalRep_beltPt (m u : ℕ) :
    evalRep (repHat m) (beltPt m u)
      = 2 * (((∑ j ∈ range (8 * m + 1),
              (hatA m j : ℚ) * hatLam m j / (((12 * m + 2 * j + u : ℕ) : ℚ) + 1))
            + (∑ i ∈ range m, hatBlo m i / (((10 * m + 2 * i + u : ℕ) : ℚ) + 1))
            + ∑ i ∈ range (2 * m), hatBhi m i / (((28 * m + 2 + 2 * i + u : ℕ) : ℚ) + 1))
          + 2 * ∑ j ∈ range (8 * m + 1),
              (hatA m j : ℚ) / (((12 * m + 2 * j + u : ℕ) : ℚ) + 1) ^ 2) := by
  show (repHatB m).sum (fun k b => b / (beltPt m u + (k : ℚ)))
      + (repHatA m).sum (fun k a => a / (beltPt m u + (k : ℚ)) ^ 2) = _
  rw [repHatB_sum (g := fun k b => b / (beltPt m u + (k : ℚ)))
        (fun _ => zero_div _) (fun _ _ _ => add_div _ _ _),
      repHatA_sum (g := fun k a => a / (beltPt m u + (k : ℚ)) ^ 2)
        (fun _ => zero_div _) (fun _ _ _ => add_div _ _ _)]
  rw [Finset.sum_congr rfl (fun j _ => by rw [beltPt_double, div_half] :
      ∀ j ∈ range (8 * m + 1),
        (hatA m j : ℚ) * hatLam m j / (beltPt m u + ((10 * m + 1 + j : ℕ) : ℚ))
          = 2 * ((hatA m j : ℚ) * hatLam m j / (((12 * m + 2 * j + u : ℕ) : ℚ) + 1)))]
  rw [Finset.sum_congr rfl (fun i _ => by rw [beltPt_lo, div_half] :
      ∀ i ∈ range m, hatBlo m i / (beltPt m u + ((9 * m + 1 + i : ℕ) : ℚ))
          = 2 * (hatBlo m i / (((10 * m + 2 * i + u : ℕ) : ℚ) + 1)))]
  rw [Finset.sum_congr rfl (fun i _ => by rw [beltPt_hi, div_half] :
      ∀ i ∈ range (2 * m), hatBhi m i / (beltPt m u + ((18 * m + 2 + i : ℕ) : ℚ))
          = 2 * (hatBhi m i / (((28 * m + 2 + 2 * i + u : ℕ) : ℚ) + 1)))]
  rw [Finset.sum_congr rfl (fun j _ => by rw [beltPt_double, div_half_sq] :
      ∀ j ∈ range (8 * m + 1),
        (hatA m j : ℚ) / (beltPt m u + ((10 * m + 1 + j : ℕ) : ℚ)) ^ 2
          = 4 * ((hatA m j : ℚ) / (((12 * m + 2 * j + u : ℕ) : ℚ) + 1) ^ 2))]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-! ## 3. The slice VANISHES inside the belt — this is where PAIR-4R is spent -/

/-- At `t_u` the numerator's `(2t + l)` run has the zero `l = 8m + 1 − u`, and that index is
inside `[3m+2, 20m+1]` exactly when `u + 1 ≤ 5m`. -/
theorem hatMember_slice_zero (m u : ℕ) (hu : u + 1 ≤ 5 * m) : hatMember m (beltPt m u) = 0 := by
  rw [hatMember]
  refine div_eq_zero_iff.2 (Or.inl ?_)
  refine mul_eq_zero_of_left ?_ _
  refine Finset.prod_eq_zero (i := 8 * m + 1 - u) ?_ ?_
  · rw [Finset.mem_Icc]; omega
  · rw [beltPt, Nat.cast_sub (by omega : u ≤ 8 * m + 1)]
    push_cast
    ring

/-- …so the whole slice is `0`, by PAIR-4R.  The `ht` side condition is free: every pole of the
written denominator has `k ≥ 7m+1`, and `t_u + k ≥ (6m+1)/2 > 0`. -/
theorem evalRep_slice_zero (m u : ℕ) (hu : u + 1 ≤ 5 * m) :
    evalRep (repHat m) (beltPt m u) = 0 := by
  rw [hat_rep m (beltPt m u) ?_, hatMember_slice_zero m u hu, mul_zero]
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hk1 : ((7 * m + 1 : ℕ) : ℚ) ≤ (k : ℚ) := Nat.cast_le.2 hk.1
  have hu0 : (0 : ℚ) ≤ (u : ℚ) := Nat.cast_nonneg u
  have hm0 : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
  push_cast at hk1
  have hpos : (0 : ℚ) < beltPt m u + (k : ℚ) := by rw [beltPt]; linarith
  exact hpos.ne'

/-- The four families' tails are four separate `u`-sums; the slice is ONE evaluation.  Combining
them is pure `Finset` algebra, and it is a lemma rather than a `rw` chain because the `2 *` in
front of the order-2 family makes `Finset.mul_sum` fire on the wrong occurrence when the whole
goal is in view (measured: it rewrote `hatP_split`'s `2 * Σ` instead). -/
theorem combine_slices (C : ℕ) (V1 V2 V3 V4 : ℕ → ℚ) :
    (∑ u ∈ range C, (-1 : ℚ) ^ (u + 1) * V1 u) + (∑ u ∈ range C, (-1 : ℚ) ^ (u + 1) * V2 u)
        + (∑ u ∈ range C, (-1 : ℚ) ^ (u + 1) * V3 u)
        + 2 * ∑ u ∈ range C, (-1 : ℚ) ^ (u + 1) * V4 u
      = ∑ u ∈ range C, (-1 : ℚ) ^ (u + 1) * (V1 u + V2 u + V3 u + 2 * V4 u) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => by ring

/-! ## 4. The cell shift, assembled -/

/-- `hatP`'s first sum carries `Λ·A(L,1) + 2·A(L,2)` together; the shift acts on the two
alternating sums separately, so split it once here. -/
theorem hatP_split (m : ℕ) :
    hatP m
      = ((∑ j ∈ range (8 * m + 1),
            (hatA m j : ℚ) * hatLam m j * altH 1 (12 * m + 2 * j))
          + (∑ i ∈ range m, hatBlo m i * altH 1 (10 * m + 2 * i))
          + ∑ i ∈ range (2 * m), hatBhi m i * altH 1 (28 * m + 2 + 2 * i))
        + 2 * ∑ j ∈ range (8 * m + 1), (hatA m j : ℚ) * altH 2 (12 * m + 2 * j) := by
  rw [hatP, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ =>
    (by ring : (hatA m j : ℚ) * (hatLam m j * altH 1 (12 * m + 2 * j)
      + 2 * altH 2 (12 * m + 2 * j))
      = (hatA m j : ℚ) * hatLam m j * altH 1 (12 * m + 2 * j)
        + 2 * ((hatA m j : ℚ) * altH 2 (12 * m + 2 * j))))]
  rw [Finset.sum_add_distrib]
  ring

/-- **The exact cell-shift formula**: evaluating member `n+j` at the NEIGHBOUR cell `Ĉ n` differs
from its own-cell value by the member's representation sampled at `8j` points.  No hypothesis at
all — the belt only enters when the samples are shown to vanish. -/
theorem Phihat_rat_shift (n j : ℕ) :
    (Phihat n (repHat (n + j))).1
      = hatP (n + j)
        + ∑ u ∈ range (8 * j),
            (-1 : ℚ) ^ (u + 1) * (evalRep (repHat (n + j)) (beltPt (n + j) u) / 2) := by
  have hLd : ∀ j' : ℕ, Lhat n (10 * (n + j) + 1 + j') = 12 * (n + j) + 2 * j' + 8 * j := by
    intro j'; unfold Lhat; omega
  have hLlo : ∀ i : ℕ, Lhat n (9 * (n + j) + 1 + i) = 10 * (n + j) + 2 * i + 8 * j := by
    intro i; unfold Lhat; omega
  have hLhi : ∀ i : ℕ, Lhat n (18 * (n + j) + 2 + i) = 28 * (n + j) + 2 + 2 * i + 8 * j := by
    intro i; unfold Lhat; omega
  have hA1 := shift_family (range (8 * (n + j) + 1))
      (fun j' => (hatA (n + j) j' : ℚ) * hatLam (n + j) j')
      (fun j' => 12 * (n + j) + 2 * j') (8 * j) 1
      (fun j' _ => ⟨6 * (n + j) + j', by ring⟩)
  have hlo := shift_family (range (n + j)) (fun i => hatBlo (n + j) i)
      (fun i => 10 * (n + j) + 2 * i) (8 * j) 1
      (fun i _ => ⟨5 * (n + j) + i, by ring⟩)
  have hhi := shift_family (range (2 * (n + j))) (fun i => hatBhi (n + j) i)
      (fun i => 28 * (n + j) + 2 + 2 * i) (8 * j) 1
      (fun i _ => ⟨14 * (n + j) + 1 + i, by ring⟩)
  have hA2 := shift_family (range (8 * (n + j) + 1))
      (fun j' => (hatA (n + j) j' : ℚ))
      (fun j' => 12 * (n + j) + 2 * j') (8 * j) 2
      (fun j' _ => ⟨6 * (n + j) + j', by ring⟩)
  simp only [pow_one] at hA1 hlo hhi
  have hU : ∑ u ∈ range (8 * j),
        (-1 : ℚ) ^ (u + 1) * (evalRep (repHat (n + j)) (beltPt (n + j) u) / 2)
      = (∑ u ∈ range (8 * j), (-1 : ℚ) ^ (u + 1)
            * ∑ j' ∈ range (8 * (n + j) + 1),
                (hatA (n + j) j' : ℚ) * hatLam (n + j) j'
                  / (((12 * (n + j) + 2 * j' + u : ℕ) : ℚ) + 1))
        + (∑ u ∈ range (8 * j), (-1 : ℚ) ^ (u + 1)
            * ∑ i ∈ range (n + j), hatBlo (n + j) i / (((10 * (n + j) + 2 * i + u : ℕ) : ℚ) + 1))
        + (∑ u ∈ range (8 * j), (-1 : ℚ) ^ (u + 1)
            * ∑ i ∈ range (2 * (n + j)),
                hatBhi (n + j) i / (((28 * (n + j) + 2 + 2 * i + u : ℕ) : ℚ) + 1))
        + 2 * ∑ u ∈ range (8 * j), (-1 : ℚ) ^ (u + 1)
            * ∑ j' ∈ range (8 * (n + j) + 1),
                (hatA (n + j) j' : ℚ) / (((12 * (n + j) + 2 * j' + u : ℕ) : ℚ) + 1) ^ 2 := by
    rw [combine_slices]
    exact Finset.sum_congr rfl fun u _ => by rw [evalRep_beltPt]; ring
  show (repHatB (n + j)).sum (fun k b => b * altH 1 (Lhat n k))
      + 2 * (repHatA (n + j)).sum (fun k a => a * altH 2 (Lhat n k)) = _
  rw [repHatB_sum (g := fun k b => b * altH 1 (Lhat n k))
        (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
      repHatA_sum (g := fun k a => a * altH 2 (Lhat n k))
        (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  simp only [hLd, hLlo, hLhi]
  rw [hA1, hlo, hhi, hA2, hatP_split, hU]
  ring

/-! ## 5. The row -/

/-- **ROW PAIR-4C, the rational coordinate**: member `n+j` evaluated at the cell `Ĉ n` still reads
off `hatP (n+j)`, for every `j ≤ 3` and every `n ≥ 2`.  `belt_rat_coord_one_one` was this at
`(n, j) = (1, 1)`. -/
theorem Phihat_rat_belt (n j : ℕ) (hj : j ≤ 3) (hn : 2 ≤ n) :
    (Phihat n (repHat (n + j))).1 = hatP (n + j) := by
  rw [Phihat_rat_shift]
  rw [Finset.sum_congr rfl (fun u hu => by
      rw [evalRep_slice_zero (n + j) u (by rw [Finset.mem_range] at hu; omega)]
      ring :
    ∀ u ∈ range (8 * j),
      (-1 : ℚ) ^ (u + 1) * (evalRep (repHat (n + j)) (beltPt (n + j) u) / 2) = 0)]
  rw [Finset.sum_const_zero, add_zero]

/-- **ROW PAIR-4C**: `Φ̂_member`.  The three coordinates come from three different places — the
rational one from the belt computation above, the ζ(2) one from PAIR-4's cell-INDEPENDENT theorem,
the `ln 2` one from PAIR-4L — and only the first needed `2 ≤ n`. -/
theorem Phihat_member (n j : ℕ) (hj : j ≤ 3) (hn : 2 ≤ n) :
    Phihat n (repHat (n + j)) = (hatP (n + j), -(hatQ (n + j) : ℚ), 0) := by
  rw [Prod.ext_iff, Prod.ext_iff]
  exact ⟨Phihat_rat_belt n j hj hn, Phihat_zeta2_coord n (n + j), ln2_coord n (n + j)⟩

end Zeta2HatBelt

#print axioms Zeta2HatBelt.altH_add
#print axioms Zeta2HatBelt.altH_add_even
#print axioms Zeta2HatBelt.shift_family
#print axioms Zeta2HatBelt.evalRep_beltPt
#print axioms Zeta2HatBelt.hatMember_slice_zero
#print axioms Zeta2HatBelt.evalRep_slice_zero
#print axioms Zeta2HatBelt.combine_slices
#print axioms Zeta2HatBelt.hatP_split
#print axioms Zeta2HatBelt.Phihat_rat_shift
#print axioms Zeta2HatBelt.Phihat_rat_belt
#print axioms Zeta2HatBelt.Phihat_member
