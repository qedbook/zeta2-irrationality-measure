/-
# Row PT-RATE — `log Φ̃ₙ` IS leg B's block sum, and `log Φ̃ₙ / n → d_φ̃`

`docs/future/zeta2-lean-chain.md` row **PT-RATE** (registry `2B0.AZ`).  The IDENTIFICATION of
PT-DEF's `Zeta2PhiT.PhiT` with the object leg B's analysis actually estimates,
`Zeta2LegBCandidate.blockSum`, and the limit that DRATE and HC2 consume.

## THE TWO SIDES ARE CUT DIFFERENTLY, AND THAT IS THE WHOLE ROW

* **PT-DEF's side.**  `PhiT n = ∏_{p ∈ phiWindow n} p ^ φ̃({n/p})` with
  `phiWindow n = {p prime : p ≤ 15n ∧ p² > 26n+1}` — cut at the landed atom's Legendre line.
* **Leg B's side.**  `blockSum K i n = ∑_{k ≤ K n} (θ(n/(k+aᵢ)) − θ(n/(k+bᵢ)))` at the concrete
  block count `K n = ⌊√n⌋ − 1`, i.e. cut at `⌊n/p⌋ ≤ ⌊√n⌋ − 1`.

Neither cut implies the other by inspection, and the chain doc's cell asked for "an explicit
`o(n)` term".  What this file proves is sharper than an `o(n)` estimate, and in both parts:

1. `phiWindow_subset_lowSet` — **the second difference set is EMPTY, ∀ n**, not small: a prime
   above the Legendre line ALWAYS has `⌊n/p⌋ ≤ ⌊√n⌋ − 1`.  (`p² > 26n+1 ≥ 26·(⌊√n⌋)²` forces
   `p > 5⌊√n⌋`, and `⌊√n⌋·p > n` follows.)  So the correction is ONE-SIGNED rather than a
   difference of two error terms — which is why `corr_nonneg` is a theorem and not an assumption.
2. `log_PhiT_eq_blockSum` — the correction is not merely bounded, it is IDENTIFIED:
   `corr n = ∑_{p ∈ smallSet n} φ̃({n/p}) log p` over `smallSet n = {p prime : ⌊n/p⌋ ≤ ⌊√n⌋−1 ∧
   p² ≤ 26n+1}`, exactly the primes leg B counts and PT-DEF's window discards.

`corr_le_theta` then bounds it by `2·θ(⌊√(26n+1)⌋)` — the cell's own envelope, at a NATURAL
argument so no `⌊√·⌋₊` bookkeeping enters — and `corr_div_tendsto` makes it `o(n)`.

## WHAT WAS ALREADY PROVED, AND WHAT THIS ROW HAD TO ADD

**The reindexing equivalence is NOT this row's to prove.**  The chain cell names
`{n/p} ∈ [a,b) ∧ ⌊n/p⌋ = k ↔ n/(k+b) < p ≤ n/(k+a)` as the row's central risk — the shape that
PT-Q1 found sound forward and FALSE BACKWARD on 0.84% of cells.  Grepping first (three units this
week were about to re-prove landed lemmas) found it already landed, in both directions, as
`Zeta2LegB.mem_block_interval_iff`, with `block_of_mem_interval` supplying the backward half under
`0 ≤ a` and `b ≤ 1`.  Both hypotheses are load-bearing and `ptrate_reindex_probe.py`'s two
wanted-RED control arms measure that they are: dropping `0 ≤ a` produces 676 backward failures on
n ≤ 12 and dropping `b ≤ 1` produces 520, while the real table has **0 failures in either
direction** over n ≤ 40 (every piece, every block, every prime ≤ 15n, exact ℚ arithmetic).

What this row had to add, beyond the cut reconciliation:

* **The ℚ/ℝ seam.**  PT-DEF's `phiT` takes `Int.fract ((n : ℚ) / p)`; leg B's lemmas are stated at
  `Int.fract ((n : ℝ) / p)`.  Those are different terms in different types and `fract_bridge`
  is what makes them one claim.  This is precisely the cast seam LEAN.md §3 records as having
  broken composition twice in this program.
* **The profile identity** `profile_sum`: `∑ᵢ vᵢ·[x ∈ [aᵢ,bᵢ)] = φ̃(x)` for every `x : ℚ`.  `phiT`
  is a `List.find?` (first match wins) while leg B's sum runs over all 26 pieces, so the two agree
  only because the pieces are pairwise disjoint — `piece_unique`, from a `decide`d
  `List.Pairwise` on the landed table.  Nothing in the corpus had stated that.

## WHICH `Δ` — the binder trap, again

PT-DEF proved `hDne_does_not_pin_Delta`: `hΔne` holds at the WRONG `Δ 13 16` too.  This row is
stated at `Zeta2PhiT.PhiT` and therefore at `ΔT`, and it is one of the rows that DOES pin the
object: `log_PhiT_eq_blockSum` names `PhiT`, whose window and profile are `ΔT`'s denominator.
DRATE consumes this file's `tendsto_log_PhiT_div` together with leg A's rate.

## HEADLINE

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry` after this file.  This row
closes ONE row of 43.  `tendsto_log_PhiT_div` carries leg B's own standing hypothesis — the `ψ`
error bound, proved on PNT+ from `MediumPNT` and NOT on this toolchain — exactly as
`legB_candidate_from_psi` does; the row adds no new hypothesis and discharges none.

## Receipts

`#print axioms` on every theorem at the foot (LEAN.md §1).  Falsifier suite:
`falsify_phitrate.sh`, archived to `out_phitrate_falsify.txt`.  Numeric probe:
`ptrate_reindex_probe.py` -> `ptrate_reindex_probe.out`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox
`~/mathlib-current`.  This is NOT the repo's `tools/lean_probe.sh` / `lean_verify` pin (v4.16.0);
nothing here was checked under that pin.
-/
import Zeta2PhiT
import Zeta2LegBCand

namespace Zeta2PhiTRate

open Finset Filter Zeta2Profile Zeta2PhiT Zeta2LegBCandidate
open scoped Topology

/-- The profile's index type — leg B's own, so `pa`/`pb`/`pv` apply without a cast. -/
abbrev Idx := Fin candidateProfile.length

/-! ## The profile's endpoints, in ℚ

`pa`/`pb`/`pv` are the ℝ-valued endpoints leg B's analysis uses.  `phiT` is a ℚ-valued step
function.  Both read the SAME landed `candidateProfile`, so these three are `rfl`-bridges and no
second copy of the table enters. -/

/-- The `i`-th piece's left endpoint, in ℚ. -/
def qa (i : Idx) : ℚ := (candidateProfile.get i).1
/-- The `i`-th piece's right endpoint, in ℚ. -/
def qb (i : Idx) : ℚ := (candidateProfile.get i).2.1
/-- The `i`-th piece's weight, in ℚ. -/
def qv (i : Idx) : ℚ := (candidateProfile.get i).2.2

theorem pa_eq (i : Idx) : pa i = ((qa i : ℚ) : ℝ) := rfl
theorem pb_eq (i : Idx) : pb i = ((qb i : ℚ) : ℝ) := rfl
theorem pv_eq (i : Idx) : pv i = ((qv i : ℚ) : ℝ) := rfl

/-- `1/15` is the smallest left endpoint in the landed table.  It is what bounds the row's prime
window by `15n`, i.e. what makes leg B's `k = 0` block land inside `Nat.primesLE (15*n)`. -/
theorem qa_lb (i : Idx) : (1 : ℚ) / 15 ≤ qa i := by
  -- `decide +kernel`, NOT bare `decide`: the elaborator's whnf sticks on `Rat.blt` over ℚ
  -- literals while the kernel reduces them.  PT-DEF's falsifier arm R7 measures exactly this,
  -- and the first draft of this line met it (LEAN.md §8).
  have h : ∀ t ∈ candidateProfile, (1 : ℚ) / 15 ≤ t.1 := by decide +kernel
  exact h _ (List.get_mem candidateProfile i)

theorem pa_lb (i : Idx) : (1 : ℝ) / 15 ≤ pa i := by
  have h : ((((1 : ℚ) / 15) : ℚ) : ℝ) ≤ ((qa i : ℚ) : ℝ) := by exact_mod_cast qa_lb i
  push_cast at h
  rw [pa_eq]
  exact h

theorem pa_pos (i : Idx) : 0 < pa i := (piece_valid i).1
theorem pa_le_pb (i : Idx) : pa i ≤ pb i := (piece_valid i).2.1
theorem pb_le_one (i : Idx) : pb i ≤ 1 := (piece_valid i).2.2.2
theorem pb_pos (i : Idx) : 0 < pb i := lt_of_lt_of_le (pa_pos i) (pa_le_pb i)

/-! ## The ℚ/ℝ seam

`Zeta2PhiT.phiT` is applied to `Int.fract ((n : ℚ) / (p : ℚ))`; every leg B lemma speaks of
`Int.fract ((n : ℝ) / (p : ℝ))`.  LEAN.md §3: this is the cast seam, and it gets its own lemma. -/

theorem fract_bridge (n p : ℕ) :
    ((Int.fract ((n : ℚ) / (p : ℚ)) : ℚ) : ℝ) = Int.fract ((n : ℝ) / (p : ℝ)) := by
  rw [Rat.cast_fract]
  push_cast
  ring_nf

/-- Membership of `{n/p}` in the `i`-th piece, stated in ℚ so it is DECIDABLE (leg B's `Set.Ico`
over ℝ is not, and this predicate indexes `Finset.filter`s below). -/
def inPiece (i : Idx) (x : ℚ) : Prop := qa i ≤ x ∧ x < qb i

instance instDecInPiece (i : Idx) (x : ℚ) : Decidable (inPiece i x) :=
  inferInstanceAs (Decidable (qa i ≤ x ∧ x < qb i))

/-- The seam, as an iff: the decidable ℚ predicate IS leg B's `Set.Ico` condition. -/
theorem inPiece_iff (i : Idx) (n p : ℕ) :
    inPiece i (Int.fract ((n : ℚ) / (p : ℚ)))
      ↔ Int.fract ((n : ℝ) / (p : ℝ)) ∈ Set.Ico (pa i) (pb i) := by
  rw [Set.mem_Ico, ← fract_bridge, pa_eq, pb_eq, inPiece]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ## The profile identity — `∑ᵢ vᵢ·[x ∈ pieceᵢ] = φ̃(x)`

`phiT` is a `List.find?`: FIRST match wins.  Leg B's outer sum runs over ALL 26 pieces.  The two
agree exactly because the pieces are pairwise disjoint, which nothing in this corpus had stated. -/

/-- The landed table is sorted and its pieces do not overlap: `bᵢ ≤ aⱼ` for `i < j`.  325 rational
comparisons, by `decide`. -/
theorem profile_pairwise :
    List.Pairwise (fun s u : ℚ × ℚ × ℚ => s.2.1 ≤ u.1) candidateProfile := by decide +kernel

/-- At most one piece contains any given `x`. -/
theorem piece_unique {i j : Idx} {x : ℚ} (hi : inPiece i x) (hj : inPiece j x) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exfalso
    have hle : qb i ≤ qa j := List.pairwise_iff_get.mp profile_pairwise i j h
    have h1 : x < qb i := hi.2
    have h2 : qa j ≤ x := hj.1
    linarith
  · exact h
  · exfalso
    have hle : qb j ≤ qa i := List.pairwise_iff_get.mp profile_pairwise j i h
    have h1 : x < qb j := hj.2
    have h2 : qa i ≤ x := hi.1
    linarith

/-- Every weight in the table is a nonnegative integer, so `Rat.num.toNat` loses nothing.  This is
what `phiT`'s `t.2.2.num.toNat` costs, and it is checked rather than assumed. -/
theorem qv_num (i : Idx) : (((qv i).num.toNat : ℕ) : ℚ) = qv i := by
  have h : ∀ t ∈ candidateProfile, ((t.2.2.num.toNat : ℕ) : ℚ) = t.2.2 := by decide
  exact h _ (List.get_mem candidateProfile i)

/-- Every weight is at most `2` — the envelope `corr ≤ 2·θ(…)` rests on this. -/
theorem phiT_le_two (x : ℚ) : phiT x ≤ 2 := by
  unfold phiT
  cases hf : candidateProfile.find? (fun t => decide (t.1 ≤ x ∧ x < t.2.1)) with
  | none => norm_num
  | some t =>
      have hmem := List.mem_of_find?_eq_some hf
      have h : ∀ u ∈ candidateProfile, u.2.2.num.toNat ≤ 2 := by decide
      exact h t hmem

/-- A successful `find?` names a piece index that really contains `x`. -/
theorem find_gives_piece {x : ℚ} {t : ℚ × ℚ × ℚ}
    (h : candidateProfile.find? (fun t => decide (t.1 ≤ x ∧ x < t.2.1)) = some t) :
    ∃ j : Idx, candidateProfile.get j = t ∧ inPiece j x := by
  have hmem := List.mem_of_find?_eq_some h
  have hsat := List.find?_some h
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
  refine ⟨j, hj, ?_⟩
  rw [inPiece, qa, qb, hj]
  simpa using hsat

/-- **The profile identity.**  Leg B's 26-term weighted indicator sum IS PT-DEF's `φ̃`. -/
theorem profile_sum (x : ℚ) :
    ∑ i : Idx, pv i * (if inPiece i x then (1 : ℝ) else 0) = (phiT x : ℝ) := by
  unfold phiT
  cases hf : candidateProfile.find? (fun t => decide (t.1 ≤ x ∧ x < t.2.1)) with
  | none =>
      have hnone := List.find?_eq_none.mp hf
      have hno : ∀ i : Idx, ¬ inPiece i x := by
        intro i hi
        exact hnone _ (List.get_mem candidateProfile i)
          (by simpa [inPiece, qa, qb] using hi)
      simp [hno]
  | some t =>
      obtain ⟨j, hjt, hj⟩ := find_gives_piece hf
      have hval : ((t.2.2.num.toNat : ℕ) : ℚ) = t.2.2 := by
        have := qv_num j
        rwa [qv, hjt] at this
      rw [Finset.sum_eq_single j]
      · rw [if_pos hj, mul_one, pv_eq, qv, hjt, ← hval]
        push_cast
        ring
      · intro b _ hbj
        rw [if_neg (fun hb => hbj (piece_unique hb hj)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h

/-! ## The two index sets, and their difference -/

/-- The primes leg B's block sum reaches: those with `⌊n/p⌋ ≤ K n = ⌊√n⌋ − 1`. -/
def lowSet (n : ℕ) : Finset ℕ :=
  (Nat.primesLE (15 * n)).filter (fun p => n / p ≤ Nat.sqrt n - 1)

/-- The primes leg B reaches and PT-DEF's window DISCARDS — the whole content of the correction. -/
def smallSet (n : ℕ) : Finset ℕ :=
  (Nat.primesLE (15 * n)).filter (fun p => n / p ≤ Nat.sqrt n - 1 ∧ p ^ 2 ≤ 26 * n + 1)

/-- The primes of `lowSet n` lying in the `i`-th piece. -/
def pieceSet (n : ℕ) (i : Idx) : Finset ℕ :=
  (lowSet n).filter (fun p => inPiece i (Int.fract ((n : ℚ) / (p : ℚ))))

/-- **The second difference set is EMPTY.**  Every prime above PT-DEF's Legendre line already has
`⌊n/p⌋ ≤ ⌊√n⌋ − 1`, so leg B's block truncation discards none of `phiWindow n` and the correction
is one-signed.  `p² > 26n+1 ≥ 26·s²` gives `p > 5s`, and then `s·p ≥ s(5s+1) = 5s²+s > (s+1)² > n`
for `s ≥ 1`. -/
theorem phiWindow_subset_lowSet (n : ℕ) : phiWindow n ⊆ lowSet n := by
  intro p hp
  have hmem : p ∈ Nat.primesLE (15 * n) := (Finset.mem_filter.mp hp).1
  have hsq : 26 * n + 1 < p ^ 2 := sq_gt_of_mem_phiWindow hp
  have hpr : Nat.Prime p := Nat.prime_of_mem_primesLE hmem
  have hp0 : 0 < p := hpr.pos
  rw [lowSet, Finset.mem_filter]
  refine ⟨hmem, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · set s := Nat.sqrt n with hs
    have hs1 : 1 ≤ s := Nat.sqrt_pos.mpr hn
    have hs2 : s ^ 2 ≤ n := Nat.sqrt_le' n
    have hs3 : n < (s + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt' n
      simpa [hs, Nat.succ_eq_add_one] using this
    have h5 : (5 * s) ^ 2 < p ^ 2 := by nlinarith
    have h5' : 5 * s < p := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h5
    have hlt : n < s * p := by nlinarith
    have : n / p < s := (Nat.div_lt_iff_lt_mul hp0).mpr (by linarith [hlt])
    exact Nat.le_sub_one_of_lt this

/-- The difference of the two index sets is exactly `smallSet n`. -/
theorem lowSet_sdiff (n : ℕ) : lowSet n \ phiWindow n = smallSet n := by
  ext p
  simp only [Finset.mem_sdiff, lowSet, smallSet, phiWindow, Finset.mem_filter, not_and, not_lt]
  constructor
  · rintro ⟨⟨hmem, hlo⟩, hnot⟩
    exact ⟨hmem, hlo, by simpa using hnot hmem⟩
  · rintro ⟨hmem, hlo, hsq⟩
    exact ⟨⟨hmem, hlo⟩, fun _ => by simpa using hsq⟩

/-! ## `log Φ̃ₙ` as a sum over primes -/

theorem log_PhiT_eq (n : ℕ) :
    Real.log (PhiT n)
      = ∑ p ∈ phiWindow n, (phiT (Int.fract ((n : ℚ) / (p : ℚ))) : ℝ) * Real.log p := by
  have hne : ∀ p ∈ phiWindow n,
      ((p : ℝ) ^ phiT (Int.fract ((n : ℚ) / (p : ℚ)))) ≠ 0 := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (prime_of_mem_phiWindow hp).pos
    exact pow_ne_zero _ (ne_of_gt hp0)
  rw [PhiT]
  push_cast
  rw [Real.log_prod hne]
  exact Finset.sum_congr rfl fun p _ => Real.log_pow _ _

/-! ## Leg B's side as a sum over primes — the reindexing, APPLIED -/

/-- One block's `θ`-difference is the log-sum over the primes of that block that lie in the piece.
This is `Zeta2LegB.theta_sub_theta` composed with `Zeta2LegB.mem_block_interval_iff` — the
already-landed both-directions reindexing — plus the `p ≤ 15n` bound from `pa_lb`. -/
theorem theta_diff_eq_cell (n : ℕ) (i : Idx) (k : ℕ) :
    Chebyshev.theta ((n : ℝ) / ((k : ℝ) + pa i))
        - Chebyshev.theta ((n : ℝ) / ((k : ℝ) + pb i))
      = ∑ p ∈ (Nat.primesLE (15 * n)).filter
          (fun p => n / p = k ∧ inPiece i (Int.fract ((n : ℚ) / (p : ℚ)))), Real.log p := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hka : (0 : ℝ) < (k : ℝ) + pa i := by linarith [pa_pos i]
  have hkb : (0 : ℝ) < (k : ℝ) + pb i := by linarith [pb_pos i]
  have hxy : (n : ℝ) / ((k : ℝ) + pb i) ≤ (n : ℝ) / ((k : ℝ) + pa i) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg n) hka (by linarith [pa_le_pb i])
  have hfl : ⌊(n : ℝ) / ((k : ℝ) + pb i)⌋₊ ≤ ⌊(n : ℝ) / ((k : ℝ) + pa i)⌋₊ :=
    Nat.floor_le_floor hxy
  rw [Zeta2LegB.theta_sub_theta _ _ hfl]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hpr⟩
    have hp0 : 0 < p := hpr.pos
    have hmem :=
      (Zeta2LegB.mem_block_interval_iff n p k hp0 (pa i) (pb i) (pa_pos i).le (pb_le_one i)
        hka hkb).mpr (Finset.mem_Ioc.mpr ⟨hlo, hhi⟩)
    -- `p ≤ 15n`, from `n/(k+aᵢ) ≤ 15n` and `aᵢ ≥ 1/15`
    have hyle : (n : ℝ) / ((k : ℝ) + pa i) ≤ ((15 * n : ℕ) : ℝ) := by
      rw [div_le_iff₀ hka]
      have h15 := pa_lb i
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith
    have hple : p ≤ 15 * n := by
      have h1 : ⌊(n : ℝ) / ((k : ℝ) + pa i)⌋₊ ≤ ⌊((15 * n : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor hyle
      rw [Nat.floor_natCast] at h1
      exact le_trans hhi h1
    exact ⟨⟨hple, hpr⟩, hmem.1, (inPiece_iff i n p).mpr hmem.2⟩
  · rintro ⟨⟨hple, hpr⟩, hblk, hin⟩
    have hp0 : 0 < p := hpr.pos
    have hmem :=
      (Zeta2LegB.mem_block_interval_iff n p k hp0 (pa i) (pb i) (pa_pos i).le (pb_le_one i)
        hka hkb).mp ⟨hblk, (inPiece_iff i n p).mp hin⟩
    exact ⟨Finset.mem_Ioc.mp hmem, hpr⟩

/-- Leg B's block sum for one piece IS the log-sum over that piece's primes below the block line. -/
theorem blockSum_eq (n : ℕ) (i : Idx) :
    blockSum (fun m => Nat.sqrt m - 1) i n = ∑ p ∈ pieceSet n i, Real.log p := by
  rw [blockSum]
  rw [Finset.sum_congr rfl (fun k _ => theta_diff_eq_cell n i k)]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [pieceSet, lowSet, Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hQ : inPiece i (Int.fract ((n : ℚ) / (p : ℚ)))
  · simp only [hQ, and_true]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  · simp [hQ]

/-- **Leg B's whole weighted side, as one sum over primes, weighted by `φ̃`.** -/
theorem legB_side_eq (n : ℕ) :
    (∑ i : Idx, pv i * blockSum (fun m => Nat.sqrt m - 1) i n)
      = ∑ p ∈ lowSet n, (phiT (Int.fract ((n : ℚ) / (p : ℚ))) : ℝ) * Real.log p := by
  have h1 : ∀ i : Idx, pv i * blockSum (fun m => Nat.sqrt m - 1) i n
      = ∑ p ∈ lowSet n,
          pv i * ((if inPiece i (Int.fract ((n : ℚ) / (p : ℚ))) then (1 : ℝ) else 0)
            * Real.log p) := by
    intro i
    rw [blockSum_eq, pieceSet, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : inPiece i (Int.fract ((n : ℚ) / (p : ℚ))) <;> simp [h]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i), Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← profile_sum (Int.fract ((n : ℚ) / (p : ℚ))), Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## THE ROW'S IDENTITY -/

/-- The small-prime correction: the primes leg B counts and PT-DEF's window discards. -/
noncomputable def corr (n : ℕ) : ℝ :=
  ∑ p ∈ smallSet n, (phiT (Int.fract ((n : ℚ) / (p : ℚ))) : ℝ) * Real.log p

/-- **THE ROW'S IDENTIFICATION.**  `log Φ̃ₙ` IS leg B's weighted block sum, minus an explicitly
identified, one-signed small-prime correction. -/
theorem log_PhiT_eq_blockSum (n : ℕ) :
    Real.log (PhiT n)
      = (∑ i : Idx, pv i * blockSum (fun m => Nat.sqrt m - 1) i n) - corr n := by
  have hsd :
      (∑ p ∈ lowSet n \ phiWindow n,
          (phiT (Int.fract ((n : ℚ) / (p : ℚ))) : ℝ) * Real.log p)
        + (∑ p ∈ phiWindow n,
            (phiT (Int.fract ((n : ℚ) / (p : ℚ))) : ℝ) * Real.log p)
        = ∑ p ∈ lowSet n, (phiT (Int.fract ((n : ℚ) / (p : ℚ))) : ℝ) * Real.log p :=
    Finset.sum_sdiff (phiWindow_subset_lowSet n)
  rw [lowSet_sdiff] at hsd
  rw [legB_side_eq, corr, log_PhiT_eq]
  linarith [hsd]

theorem corr_nonneg (n : ℕ) : 0 ≤ corr n :=
  Finset.sum_nonneg fun p _ =>
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

theorem smallSet_subset (n : ℕ) : smallSet n ⊆ Nat.primesLE (Nat.sqrt (26 * n + 1)) := by
  intro p hp
  rw [smallSet, Finset.mem_filter] at hp
  obtain ⟨hmem, _, hsq⟩ := hp
  have hpr := Nat.prime_of_mem_primesLE hmem
  rw [Nat.mem_primesLE]
  refine ⟨?_, hpr⟩
  by_contra hlt
  push_neg at hlt
  have := Nat.sqrt_lt'.mp hlt
  omega

/-- **The cell's envelope, and at a NATURAL argument** so no `⌊√·⌋₊` bookkeeping enters. -/
theorem corr_le_theta (n : ℕ) :
    corr n ≤ 2 * Chebyshev.theta ((Nat.sqrt (26 * n + 1) : ℕ) : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, corr]
  refine le_trans (Finset.sum_le_sum ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (smallSet_subset n) ?_)
  · intro p _
    have h2 : (phiT (Int.fract ((n : ℚ) / (p : ℚ))) : ℝ) ≤ 2 := by
      exact_mod_cast phiT_le_two (Int.fract ((n : ℚ) / (p : ℚ)))
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    nlinarith
  · intro p _ _
    have := Real.log_natCast_nonneg p
    linarith

theorem corr_le_sqrt (n : ℕ) :
    corr n ≤ 2 * Real.log 4 * Real.sqrt (26 * (n : ℝ) + 1) := by
  have h1 := corr_le_theta n
  have h2 : Chebyshev.theta ((Nat.sqrt (26 * n + 1) : ℕ) : ℝ)
      ≤ Real.log 4 * ((Nat.sqrt (26 * n + 1) : ℕ) : ℝ) :=
    Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
  have h3 : ((Nat.sqrt (26 * n + 1) : ℕ) : ℝ) ≤ Real.sqrt ((26 * n + 1 : ℕ) : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have h5 : Real.sqrt ((26 * n + 1 : ℕ) : ℝ) = Real.sqrt (26 * (n : ℝ) + 1) := by
    congr 1
    push_cast
    ring
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [h5] at h3
  nlinarith

theorem sqrt_nat_atTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨⌈b ^ 2⌉₊, fun n hn => ?_⟩
  rcases le_or_gt b 0 with hb | hb
  · exact le_trans hb (Real.sqrt_nonneg _)
  · have hb2 : b ^ 2 ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    exact (Real.le_sqrt hb.le (Nat.cast_nonneg n)).mpr hb2

/-- **The correction is `o(n)`** — `O(√n)`, in fact, which is what makes the rate survive. -/
theorem corr_div_tendsto : Tendsto (fun n : ℕ => corr n / (n : ℝ)) atTop (𝓝 0) := by
  have hC : Tendsto (fun n : ℕ => (2 * Real.log 4 * Real.sqrt 27) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds sqrt_nat_atTop
  refine squeeze_zero' (Filter.Eventually.of_forall ?_) ?_ hC
  · intro n
    exact div_nonneg (corr_nonneg n) (Nat.cast_nonneg n)
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : Real.sqrt (26 * (n : ℝ) + 1) ≤ Real.sqrt 27 * Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_mul' _ hn0.le]
      exact Real.sqrt_le_sqrt (by linarith)
    have key : corr n ≤ (2 * Real.log 4 * Real.sqrt 27) * Real.sqrt (n : ℝ) := by
      have := corr_le_sqrt n
      nlinarith [Real.sqrt_nonneg (27 : ℝ), Real.sqrt_nonneg (n : ℝ)]
    have step1 : corr n / (n : ℝ)
        ≤ ((2 * Real.log 4 * Real.sqrt 27) * Real.sqrt (n : ℝ)) / (n : ℝ) := by
      gcongr
    rwa [mul_div_assoc, Real.sqrt_div_self', mul_one_div] at step1

/-! ## THE ROW'S LIMIT — what DRATE and HC2 consume

Leg B's own standing hypothesis (the `ψ` error bound, proved on PNT+ from `MediumPNT` and NOT on
this toolchain) is carried across unchanged.  This row adds no hypothesis and discharges none. -/

theorem tendsto_log_PhiT_div
    (hψ : ∃ c > 0, ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) * x) :
    Tendsto (fun n : ℕ => Real.log (PhiT n) / (n : ℝ)) atTop
      (𝓝 (∑ i : Idx, pv i * ∑' k : ℕ, (1 / ((k : ℝ) + pa i) - 1 / ((k : ℝ) + pb i)))) := by
  have hB := legB_candidate_from_psi hψ
  have h := hB.sub corr_div_tendsto
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  rw [log_PhiT_eq_blockSum]
  ring

/-! ## The `n = 12` probe — the cut, made concrete and decidable

PT-DEF measured `log Φ̃/12 = 14.7207` (UNCUT) against `log (PhiT 12)/12 = 13.7314`, the gap being
exactly the discarded factor `7·11²·13² = 143143`.  That gap is THIS ROW'S `corr 12`, and the two
theorems below turn PT-DEF's numeric observation into a kernel fact: the discarded primes are
`{5,7,11,13,17}` and their `φ̃`-weighted product is exactly `143143`. -/

theorem block_count_twelve : Nat.sqrt 12 - 1 = 2 := by decide +kernel

/-- GREEN — the primes leg B counts at `n = 12` that PT-DEF's window discards. -/
theorem smallSet_twelve : smallSet 12 = {5, 7, 11, 13, 17} := by decide +kernel

/-- GREEN — and their `φ̃`-weighted product is PT-DEF's `143143`, to the digit.  `5` and `17` sit
in gaps of the profile (`φ̃ = 0`), which is why five primes give a three-prime product. -/
theorem corr_product_twelve :
    ∏ p ∈ smallSet 12, p ^ phiT (Int.fract ((12 : ℚ) / (p : ℚ))) = 143143 := by
  decide +kernel

/-- RED — proved FALSE, not merely unprovable: the two cuts genuinely differ, so a `Tendsto`
stated without the correction would be stated at the wrong object. -/
theorem corr_product_twelve_ne_one :
    ∏ p ∈ smallSet 12, p ^ phiT (Int.fract ((12 : ℚ) / (p : ℚ))) ≠ 1 := by
  decide +kernel

/-- GREEN — and `PhiT 12 · 143143` is the UNCUT product PT-DEF's probe header prints, so the two
numbers in that cell are one identity rather than two measurements. -/
theorem uncut_twelve :
    PhiT 12 * (∏ p ∈ smallSet 12, p ^ phiT (Int.fract ((12 : ℚ) / (p : ℚ))))
      = 52177105745591414815326392353960723744152562897031405912708000744727341843749 := by
  decide +kernel

/-! ## Receipts — LEAN.md §1: exit 0 attests nothing, `#print axioms` does. -/

#print axioms pa_eq
#print axioms qa_lb
#print axioms pa_lb
#print axioms fract_bridge
#print axioms inPiece_iff
#print axioms profile_pairwise
#print axioms piece_unique
#print axioms qv_num
#print axioms phiT_le_two
#print axioms find_gives_piece
#print axioms profile_sum
#print axioms phiWindow_subset_lowSet
#print axioms lowSet_sdiff
#print axioms log_PhiT_eq
#print axioms theta_diff_eq_cell
#print axioms blockSum_eq
#print axioms legB_side_eq
#print axioms log_PhiT_eq_blockSum
#print axioms corr_nonneg
#print axioms smallSet_subset
#print axioms corr_le_theta
#print axioms corr_le_sqrt
#print axioms sqrt_nat_atTop
#print axioms corr_div_tendsto
#print axioms tendsto_log_PhiT_div
#print axioms block_count_twelve
#print axioms smallSet_twelve
#print axioms corr_product_twelve
#print axioms corr_product_twelve_ne_one
#print axioms uncut_twelve

end Zeta2PhiTRate
