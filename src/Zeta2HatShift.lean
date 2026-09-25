/-
# Row PAIR-5 — the hat boundary vanishing `hbdŷ`, as a shift law on `Rep̂`

`docs/future/zeta2-lean-chain.md` row PAIR-5 (and PHI-BDY, whose shape it answers).

**The row's cell said its SHAPE was unknown and priced the bad branch at "~500+ lines if the
strip statement has to be re-derived as a residue statement".**  There is no residue argument
here and there does not need to be one.  `Φ̂ N` is an algebraic functional on `Rep̂ = (B, A)`
(`Zeta2HatRep.Phihat`) whose only dependence on the cell is through `L_k = 2k − 8N − 2`, so
raising every key by one — which is what `t ↦ t + 1` does to a partial-fraction family — raises
every `L_k` by exactly 2, and `Zeta2HatBelt.shift_family` at `C = 2` turns the difference into
the two-term TAIL of each alternating sum.  By PAIR-4C's own `beltPt` identity that tail is the
representation evaluated at two points:

    Φ̂ N (shiftRep r) − Φ̂ N r  =  ( (evalRep r (beltPt N 1) − evalRep r (beltPt N 0)) / 2, 0, 0 )

and `beltPt N 0 = −4N − 1/2`, `beltPt N 1 = −4N` are EXACTLY the two poles of the kernel
`π/sin 2πt` lying between the cell `Ĉ N = −4N − 3/4` and `Ĉ N + 1 = −4N + 1/4` — the strip the
row's cell describes.  The contour statement and this `Finsupp` computation are the same fact.

**Two of the three coordinates need no hypothesis at all.**  `Φ̂`'s ζ(2) and ln 2 coordinates are
`Σ_k A_k` and `Σ_k B_k`, and a key shift is an injective reindexing, so it does not move them:
`Phihat_zeta2_argshift` and `Phihat_ln2_argshift` below are unconditional in `r` AND in `N`.
That joins `Phihat_zeta2_coord` (cell-free) and PAIR-4L's `ln2_coord`, and it means the only
coordinate of `hbdŷ` that can carry a `2 ≤ n` belt hypothesis is the rational one — which is
what PAIR-6 was told to expect.

**The one hypothesis, and it is load-bearing rather than decorative.**  `Lhat` is written with ℕ
subtraction, so `Lhat N (k+1) = Lhat N k + 2` needs `4N + 1 ≤ k`; below that the truncation makes
both sides `0` and the law is FALSE.  `hat_bdy_probe.py` §C exhibits reps with one key at
`k = 4N` that break it, so the hypothesis is tested where it binds and not only where it holds.

**What this file does NOT do**, stated here because the row is not closed by it: it does not
exhibit `repS n : Rep̂` representing the (★) antidifference `Ŝ`.  What is measured about that
object, in exact rationals on the landed `coords/starcoords_cand-t2.txt`
(`external_tests/zeta2_star_b1/hat_bdy_probe.py`, 54 checks, six falsifier arms RED):

  * `Ŝ`'s poles are at negative INTEGERS, of order ≤ 2, the smallest at `k = 9n+1` — so it is
    `Rep̂`-shaped and clears `4n+1` with room — for every `n ≥ 1`, and NOT at `n = 0`, where the
    hat member is empty and `D`'s own lead-2 block survives at order 3.
  * `Ŝ(−4n) = 0` at every `n`, and `Ŝ(−4n − 1/2) = 0` **exactly when `2 ≤ n`, sharply**: the
    numerator zero `(2t + 8n+1)` is cancelled by `D`'s block `(2t + 3n + b)`, `b ∈ [2, 10]`,
    precisely while `5n ≤ 9`.  The row's stated `2 ≤ n` is what the data hands back, from a third
    direction independent of PAIR-4C's `3j ≤ 5n` and of the engine's defect set.

**AND ONE THING THIS FILE'S FIRST PASS ASSUMED AND DID NOT MEASURE** (`hat_repS_probe.py`,
2026-09-13, 95 checks / seven arms RED): **`Ŝ` IS NOT PROPER.**  `deg num = deg den = 22n + 125`
exactly at every `n` of the ladder — `5` from `b̂` plus `120` from `x̂` plus the member's `22n`,
against the member's `22n+2` plus `D`'s `123` — so `Ŝ(∞) = C₀ ≠ 0`, and since `evalRep` of any
`Rep̂` tends to `0`, **no `Rep̂` represents `Ŝ` at all**.  `repS n` represents `Ŝ − C₀`, whose two
strip samples are `−C₀` and not `0`, so `hbdy_hat`'s `hz0`/`hz1` are BOTH FALSE at the object
this row exists to build.  The law still applies — through `hbdy_hat_eq`, whose strictly weaker
hypothesis is that the two samples are EQUAL, where the two constants cancel.  `hbdy_hat` is kept
as its corollary because `repHat` does satisfy it; the row's own object does not.

So the residual is the CONSTRUCTION of `repS`, not the vanishing argument, and `hbdy_hat_eq`
below is stated so that construction is all it will need.  `hbdy_hat_repHat` discharges every
hypothesis from landed lemmas at the hat member itself, so the composition is executed here and
not left on paper (LEAN.md §3).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2HatBelt
import Zeta2HatLinear

namespace Zeta2HatShift

open Zeta2Defs Zeta2Hat Zeta2HatRep Zeta2HatBelt Zeta2HatLinear Finset

set_option profiler true
set_option profiler.threshold 100
set_option maxHeartbeats 400000

/-! ## 1. `shiftRep` — raising every key by one IS translating the argument by one -/

/-- **`shiftRep r`** — `r` with every pole index raised by one.  `evalRep_shiftRep` is the whole
justification of the name. -/
noncomputable def shiftRep (r : Rephat) : Rephat :=
  (r.1.mapDomain (· + 1), r.2.mapDomain (· + 1))

theorem succ_injective : Function.Injective (fun k : ℕ => k + 1) := fun _ _ h => by simpa using h

/-- A `Finsupp.sum` against a shifted domain is the sum against shifted keys — no
injectivity-of-keys side condition survives, because `(· + 1)` IS injective. -/
theorem sum_shift {N : Type*} [AddCommMonoid N] (f : ℕ →₀ ℚ) (g : ℕ → ℚ → N) :
    (f.mapDomain (· + 1)).sum g = f.sum (fun k b => g (k + 1) b) :=
  Finsupp.sum_mapDomain_index_inj succ_injective

theorem evalRep_shiftRep (r : Rephat) (t : ℚ) : evalRep (shiftRep r) t = evalRep r (t + 1) := by
  have hden : ∀ k : ℕ, t + ((k + 1 : ℕ) : ℚ) = t + 1 + (k : ℚ) := by
    intro k; push_cast; ring
  unfold evalRep shiftRep
  rw [sum_shift, sum_shift]
  refine congrArg₂ (· + ·) (Finsupp.sum_congr fun k _ => ?_) (Finsupp.sum_congr fun k _ => ?_)
  · rw [hden]
  · rw [hden]

/-! ## 2. `Lhat` under a key shift, and the two strip points

`Lhat` is ℕ subtraction, so both facts below are `omega` — but only the first is unconditional.
The second is the row's one hypothesis. -/

/-- `Lhat N k = 2k − (8N+2)` is EVEN at every `k`, truncated or not: below the cutoff it is `0`.
That is what lets `shift_family`'s `hL` be discharged with no hypothesis. -/
theorem Lhat_even (N k : ℕ) : Even (Lhat N k) := ⟨k - (4 * N + 1), by unfold Lhat; omega⟩

/-- …and `4N + 1 ≤ k` is exactly what makes the ℕ subtraction faithful enough for the shift. -/
theorem Lhat_succ (N k : ℕ) (hk : 4 * N + 1 ≤ k) : Lhat N (k + 1) = Lhat N k + 2 := by
  unfold Lhat; omega

/-- The generic twin of `beltPt_double`/`_lo`/`_hi`: at `beltPt N u` the node `t + k` is
`(L_k + u + 1)/2` for EVERY key of a family supported above `4N`, not only for the hat member's
three pole runs. -/
theorem beltPt_node (N u k : ℕ) (hk : 4 * N + 1 ≤ k) :
    beltPt N u + (k : ℚ) = (((Lhat N k + u : ℕ) : ℚ) + 1) / 2 := by
  have h : ((Lhat N k : ℕ) : ℚ) = 2 * (k : ℚ) - (8 * (N : ℚ) + 2) := by
    unfold Lhat
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [beltPt, Nat.cast_add, h]
  ring

/-- `evalRep` at a strip point, for an ARBITRARY family supported above `4N`.  `evalRep_beltPt`
is this for `repHat m`, written out over its three runs; this is the same identity with the
runs replaced by the support, which is what a general `Rep̂` has instead. -/
theorem evalRep_beltPt_gen (N u : ℕ) (r : Rephat)
    (h1 : ∀ k ∈ r.1.support, 4 * N + 1 ≤ k) (h2 : ∀ k ∈ r.2.support, 4 * N + 1 ≤ k) :
    evalRep r (beltPt N u)
      = 2 * (r.1.sum (fun k b => b / (((Lhat N k + u : ℕ) : ℚ) + 1))
             + 2 * r.2.sum (fun k a => a / (((Lhat N k + u : ℕ) : ℚ) + 1) ^ 2)) := by
  have e1 : r.1.sum (fun k b => b / (beltPt N u + (k : ℚ)))
      = r.1.sum (fun k b => 2 * (b / (((Lhat N k + u : ℕ) : ℚ) + 1))) :=
    Finsupp.sum_congr fun k hk => by rw [beltPt_node N u k (h1 k hk), div_half]
  have e2 : r.2.sum (fun k a => a / (beltPt N u + (k : ℚ)) ^ 2)
      = r.2.sum (fun k a => 4 * (a / (((Lhat N k + u : ℕ) : ℚ) + 1) ^ 2)) :=
    Finsupp.sum_congr fun k hk => by rw [beltPt_node N u k (h2 k hk), div_half_sq]
  have s1 : r.1.sum (fun k b => 2 * (b / (((Lhat N k + u : ℕ) : ℚ) + 1)))
      = 2 * r.1.sum (fun k b => b / (((Lhat N k + u : ℕ) : ℚ) + 1)) := by
    rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  have s2 : r.2.sum (fun k a => 4 * (a / (((Lhat N k + u : ℕ) : ℚ) + 1) ^ 2))
      = 4 * r.2.sum (fun k a => a / (((Lhat N k + u : ℕ) : ℚ) + 1) ^ 2) := by
    rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  show r.1.sum (fun k b => b / (beltPt N u + (k : ℚ)))
      + r.2.sum (fun k a => a / (beltPt N u + (k : ℚ)) ^ 2) = _
  rw [e1, e2, s1, s2]
  ring

/-! ## 3. The shift law, coordinate by coordinate -/

/-- **The rational coordinate.**  `shift_family` at `C = 2` — the same lemma PAIR-4C runs at
`C = 8j` for the CELL shift.  The two are genuinely the same computation at different strides,
and `hat_bdy_probe.py` §B pins the arithmetic that ties them: four argument shifts equal one
cell shift, because `Ĉ` moves by 4 per cell. -/
theorem Phihat_rat_argshift (N : ℕ) (r : Rephat)
    (h1 : ∀ k ∈ r.1.support, 4 * N + 1 ≤ k) (h2 : ∀ k ∈ r.2.support, 4 * N + 1 ≤ k) :
    (Phihat N (shiftRep r)).1
      = (Phihat N r).1
        + ∑ u ∈ range 2, (-1 : ℚ) ^ (u + 1) * (evalRep r (beltPt N u) / 2) := by
  have hA1 := shift_family r.1.support (fun k => r.1 k) (fun k => Lhat N k) 2 1
      (fun k _ => Lhat_even N k)
  have hA2 := shift_family r.2.support (fun k => r.2 k) (fun k => Lhat N k) 2 2
      (fun k _ => Lhat_even N k)
  simp only [pow_one] at hA1
  have hU : ∑ u ∈ range 2, (-1 : ℚ) ^ (u + 1) * (evalRep r (beltPt N u) / 2)
      = (∑ u ∈ range 2, (-1 : ℚ) ^ (u + 1)
            * ∑ k ∈ r.1.support, r.1 k / (((Lhat N k + u : ℕ) : ℚ) + 1))
        + 2 * ∑ u ∈ range 2, (-1 : ℚ) ^ (u + 1)
            * ∑ k ∈ r.2.support, r.2 k / (((Lhat N k + u : ℕ) : ℚ) + 1) ^ 2 := by
    have hc := combine_slices 2
        (fun u => ∑ k ∈ r.1.support, r.1 k / (((Lhat N k + u : ℕ) : ℚ) + 1))
        (fun _ => (0 : ℚ)) (fun _ => (0 : ℚ))
        (fun u => ∑ k ∈ r.2.support, r.2 k / (((Lhat N k + u : ℕ) : ℚ) + 1) ^ 2)
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at hc
    rw [hc]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [evalRep_beltPt_gen N u r h1 h2, Finsupp.sum, Finsupp.sum]
    ring
  have hL : (Phihat N (shiftRep r)).1
      = r.1.sum (fun k b => b * altH 1 (Lhat N (k + 1)))
        + 2 * r.2.sum (fun k a => a * altH 2 (Lhat N (k + 1))) := by
    show (r.1.mapDomain (· + 1)).sum (fun k b => b * altH 1 (Lhat N k))
        + 2 * (r.2.mapDomain (· + 1)).sum (fun k a => a * altH 2 (Lhat N k)) = _
    rw [sum_shift, sum_shift]
  have e1 : r.1.sum (fun k b => b * altH 1 (Lhat N (k + 1)))
      = ∑ k ∈ r.1.support, r.1 k * altH 1 (Lhat N k + 2) := by
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun k hk => by rw [Lhat_succ N k (h1 k hk)]
  have e2 : r.2.sum (fun k a => a * altH 2 (Lhat N (k + 1)))
      = ∑ k ∈ r.2.support, r.2 k * altH 2 (Lhat N k + 2) := by
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun k hk => by rw [Lhat_succ N k (h2 k hk)]
  have hP : (Phihat N r).1
      = (∑ k ∈ r.1.support, r.1 k * altH 1 (Lhat N k))
        + 2 * ∑ k ∈ r.2.support, r.2 k * altH 2 (Lhat N k) := by
    show r.1.sum (fun k b => b * altH 1 (Lhat N k))
        + 2 * r.2.sum (fun k a => a * altH 2 (Lhat N k)) = _
    rw [Finsupp.sum, Finsupp.sum]
  rw [hL, e1, e2, hA1, hA2, hP, hU]
  ring

/-- **The ζ(2) coordinate is UNTOUCHED** — `Σ_k A_k` does not read the keys, and the shift is an
injective reindexing.  No hypothesis on `r`, and none on `N`. -/
theorem Phihat_zeta2_argshift (N : ℕ) (r : Rephat) :
    (Phihat N (shiftRep r)).2.1 = (Phihat N r).2.1 := by
  show (r.2.mapDomain (· + 1)).sum (fun _ a => a) = r.2.sum (fun _ a => a)
  exact sum_shift r.2 (fun _ a => a)

/-- **The ln 2 coordinate is UNTOUCHED**, for the same reason. -/
theorem Phihat_ln2_argshift (N : ℕ) (r : Rephat) :
    (Phihat N (shiftRep r)).2.2 = (Phihat N r).2.2 := by
  show (r.1.mapDomain (· + 1)).sum (fun _ b => b) = r.1.sum (fun _ b => b)
  exact sum_shift r.1 (fun _ b => b)

/-! ## 4. The antidifference's representation, and the row -/

/-- **`repDelta r = shiftRep r − r`** — the representation of `t ↦ f(t+1) − f(t)` when `r`
represents `f`.  `evalRep_repDelta` says exactly that, so the name is earned rather than
asserted. -/
noncomputable def repDelta (r : Rephat) : Rephat := shiftRep r - r

theorem evalRep_repDelta (r : Rephat) (t : ℚ) :
    evalRep (repDelta r) t = evalRep r (t + 1) - evalRep r t := by
  rw [repDelta, evalRep_sub, evalRep_shiftRep]

/-- **The exact boundary formula.**  Every coordinate at once: two are `0` outright and the
rational one is the representation sampled at the kernel's two strip poles.  This is the
statement PAIR-5's cell was reaching for when it wrote "the strip residues of `Ŝ·K̂` between
`Ĉ(n)` and `Ĉ(n)+1` vanish". -/
theorem Phihat_repDelta (N : ℕ) (r : Rephat)
    (h1 : ∀ k ∈ r.1.support, 4 * N + 1 ≤ k) (h2 : ∀ k ∈ r.2.support, 4 * N + 1 ≤ k) :
    Phihat N (repDelta r)
      = ((evalRep r (beltPt N 1) - evalRep r (beltPt N 0)) / 2, 0, 0) := by
  rw [repDelta, Phihat_sub]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (Phihat N (shiftRep r)).1 - (Phihat N r).1 = _
    rw [Phihat_rat_argshift N r h1 h2, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    ring
  · show (Phihat N (shiftRep r)).2.1 - (Phihat N r).2.1 = 0
    rw [Phihat_zeta2_argshift]
    ring
  · show (Phihat N (shiftRep r)).2.2 - (Phihat N r).2.2 = 0
    rw [Phihat_ln2_argshift]
    ring

/-- **ROW PAIR-5** — `hbdŷ`, in the form the row's OWN object satisfies.

`hbdy_hat` below asks for the two strip samples to VANISH, and at `repS n` — the (★)
antidifference's representation — they provably do not.  Measured 2026-09-13 in exact ℚ on the
landed coordinates (`external_tests/zeta2_star_b1/hat_repS_probe.py`, 95 checks, seven arms RED):
**`Ŝ` is NOT PROPER.**  `deg num = deg den = 22n + 125` exactly, at every `n` of the ladder —
`5` from `b̂` plus `120` from `x̂` plus the member's `22n`, against the member's `22n+2` plus
`D`'s `123` — so `Ŝ(∞) = C₀ ≠ 0`, while `evalRep` of ANY `Rep̂` tends to `0`.  No `Rep̂`
represents `Ŝ`; what `repS n` represents is `Ŝ − C₀`, and its value at BOTH strip points is
therefore `−C₀ ≠ 0` rather than `0`.

The two constants cancel in `Phihat_repDelta`'s difference, so the hypothesis this row must be
applied through is the strictly weaker EQUALITY of the two samples.  `hbdy_hat` is kept as its
corollary — it is what `repHat` satisfies — but it is NOT the form PAIR-6 can use at `repS`. -/
theorem hbdy_hat_eq (N : ℕ) (r : Rephat)
    (h1 : ∀ k ∈ r.1.support, 4 * N + 1 ≤ k) (h2 : ∀ k ∈ r.2.support, 4 * N + 1 ≤ k)
    (hz : evalRep r (beltPt N 0) = evalRep r (beltPt N 1)) :
    Phihat N (repDelta r) = 0 := by
  rw [Phihat_repDelta N r h1 h2, hz]
  simp [Prod.ext_iff]

/-- The two-zeros form, derived.  Stated on an abstract `Rep̂` because that is the form PAIR-6
applies it in; `hbdy_hat_repHat` below discharges every hypothesis of it at the hat member. -/
theorem hbdy_hat (N : ℕ) (r : Rephat)
    (h1 : ∀ k ∈ r.1.support, 4 * N + 1 ≤ k) (h2 : ∀ k ∈ r.2.support, 4 * N + 1 ≤ k)
    (hz0 : evalRep r (beltPt N 0) = 0) (hz1 : evalRep r (beltPt N 1) = 0) :
    Phihat N (repDelta r) = 0 :=
  hbdy_hat_eq N r h1 h2 (by rw [hz0, hz1])

/-! ## 5. Non-vacuity — every hypothesis discharged, from landed lemmas, at a real object

LEAN.md §3: a theorem whose hypotheses nobody has produced composes on paper.  `repHat m` is the
only `Rep̂` the corpus currently has, and it satisfies all four hypotheses — the support bounds
structurally, and the two strip zeros through PAIR-4R (`evalRep_slice_zero`, which is where the
member's `(2t + l)` numerator run is spent). -/

/-- The key of a `Finset.sum` of `single`s is one of the indices — the only Mathlib step these
two need, and it is `support_finsetSum` (about a `Finset.sum` of `Finsupp`s) rather than
`support_sum` (about a `Finsupp.sum`), which is a different lemma with a similar name and the
one the first draft reached for.  The `_finset_sum` spelling still compiles and is DEPRECATED —
LEAN.md §8's "a deprecated name that still compiles is the dangerous one". -/
theorem key_of_sum_single {ι : Type*} (s : Finset ι) (a : ι → ℕ) (v : ι → ℚ) (k : ℕ)
    (hk : k ∈ (∑ i ∈ s, Finsupp.single (a i) (v i)).support) : ∃ i ∈ s, k = a i := by
  classical
  obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hk)
  exact ⟨i, hi, Finset.mem_singleton.1 (Finsupp.support_single_subset hki)⟩

theorem repHatA_support (n k : ℕ) (hk : k ∈ (repHatA n).support) : 10 * n + 1 ≤ k := by
  rw [repHatA] at hk
  obtain ⟨j, _, hkj⟩ := key_of_sum_single _ _ _ k hk
  omega

theorem repHatB_support (n k : ℕ) (hk : k ∈ (repHatB n).support) : 9 * n + 1 ≤ k := by
  classical
  rw [repHatB] at hk
  rcases Finset.mem_union.1 (Finsupp.support_add hk) with hk | hk
  · rcases Finset.mem_union.1 (Finsupp.support_add hk) with hk | hk
    · obtain ⟨j, _, hkj⟩ := key_of_sum_single _ _ _ k hk; omega
    · obtain ⟨i, _, hki⟩ := key_of_sum_single _ _ _ k hk; omega
  · obtain ⟨i, _, hki⟩ := key_of_sum_single _ _ _ k hk; omega

/-- **The row's theorem, with nothing left assumed**, at the hat member's own cell.  `1 ≤ m` is
all `evalRep_slice_zero` needs at `u = 0, 1` (`u + 1 ≤ 5m`), so this is strictly weaker than the
`2 ≤ n` the (★) antidifference will require — the extra strength there comes from `D`'s
cancellation, not from this machinery. -/
theorem hbdy_hat_repHat (m : ℕ) (hm : 1 ≤ m) : Phihat m (repDelta (repHat m)) = 0 :=
  hbdy_hat m (repHat m)
    (fun k hk => by have := repHatB_support m k hk; omega)
    (fun k hk => by have := repHatA_support m k hk; omega)
    (evalRep_slice_zero m 0 (by omega)) (evalRep_slice_zero m 1 (by omega))

end Zeta2HatShift

#print axioms Zeta2HatShift.sum_shift
#print axioms Zeta2HatShift.evalRep_shiftRep
#print axioms Zeta2HatShift.Lhat_even
#print axioms Zeta2HatShift.Lhat_succ
#print axioms Zeta2HatShift.beltPt_node
#print axioms Zeta2HatShift.evalRep_beltPt_gen
#print axioms Zeta2HatShift.Phihat_rat_argshift
#print axioms Zeta2HatShift.Phihat_zeta2_argshift
#print axioms Zeta2HatShift.Phihat_ln2_argshift
#print axioms Zeta2HatShift.evalRep_repDelta
#print axioms Zeta2HatShift.Phihat_repDelta
#print axioms Zeta2HatShift.hbdy_hat_eq
#print axioms Zeta2HatShift.hbdy_hat
#print axioms Zeta2HatShift.key_of_sum_single
#print axioms Zeta2HatShift.repHatA_support
#print axioms Zeta2HatShift.repHatB_support
#print axioms Zeta2HatShift.hbdy_hat_repHat
