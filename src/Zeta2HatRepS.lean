/-
# Row PAIR-5 — `repS`, and the row's three obligations discharged at it

`docs/future/zeta2-lean-chain.md` row PAIR-5, §PAIR-5 design notes attempt 5.

**The row's own statement, and what this file proves.**  PAIR-5 is
`theorem hbdŷ (n) (h : 2 ≤ n) : Φ̂ n (repDelta (repS n)) = 0`, and its cell names three obligations:
**exhibit `repS n`**, prove **`evalRep (repS n) t = Ŝ t − C₀` off a finite set**, and **apply the
boundary law**.  All three are here:

    repS n bh xh                : Rep̂                            -- the object
    evalRep_repS_eq_shat        : evalRep (repS n bh xh) t = Ŝ t − C₀   (off the poles and the block)
    hbdy_hat_n (n) (hn : 2 ≤ n) (bh xh) (hb) (hx)
        : Phihat n (repDelta (repS n bh xh)) = 0

for every `n ≥ 2` and for every `bh xh : ℚ[X]` with `bh.natDegree ≤ 5` and `xh.natDegree ≤ 120`.

**HEADLINE: the row is NOT closed by this file, and the reason is a naming one.**  The theorem
quantifies over a family that provably CONTAINS the row's object but does not NAME it.  A
`#print axioms` receipt on a ∀-statement is not a receipt on the instance the chain consumes —
LEAN.md §2's own rule, "identify the dependency before you check it", which the D5 fork was
answered on the wrong side of.  What closes the row is `hbdy_hat_n` INSTANTIATED at `b̂(X−1)` and
`x̂ n` once PAIR-1 emits them as Lean data; that is one line plus `Zeta2HatShatForm`'s two degree
helpers, both proved, and it is an emission rather than a proof.  **The degree bounds are TIGHT and
not slack**: the landed coords header reads `dx = 120` and `FACSYM b 5`, so the real `x̂` has degree
exactly 120 and the real `b̂` exactly 5.  That is why 5H is instantiation and not re-proof.

**`2 ≤ n` enters in exactly one place** — `Zeta2HatRawPoles.numS_eval_belt0`, where the numerator's
`(2t + 8n+1)` has to sit ABOVE the run bottom `3n+11` that `D`'s cancelled lead-2 block left
behind, i.e. `5n ≥ 10`.  That is attempt 2's measured threshold reached by a different route, and
the fourth independent derivation of the same number.  Arm `S1` weakens it to `1 ≤ n` and reds.

**A RED arm shows the PROOF breaks, not that the STATEMENT is false, and the two are different
claims.**  What says this theorem is FALSE below `2 ≤ n` is the exact-ℚ probe, which evaluates
`Phihat 1 (repDelta (repS 1))` on the landed coordinates and gets a nonzero rational coordinate
— `external_tests/zeta2_star_b1/hat_raw_route_probe.py` §F on THIS construction and
`hat_repS_probe.py` §E on the REDUCED one, two unrelated bases for the same
`Phihat n (repDelta (repS n)) = 0` **iff** `2 ≤ n`.  Both halves are
present and neither alone would be enough; this corpus has been wrong about a binder before by
having only the first.

**What this file does NOT do.**  It proves nothing about `repS`'s SUPPORT beyond `⊆ idxS1 ∪ idxS2`
— which is all the boundary law needs, since its hypothesis is a floor (`4n+1 ≤ k`) and `7n+1`
clears it with room.  In particular it does NOT prove that the support is exactly `Zeta2HatCancel`'s
reduced `T₁ ∪ T₂`.  That IS true, and it is measured — the raw route builds the same `Finsupp`, it
just proves less about it — and whether PAIR-6 needs it as a theorem is PAIR-6's question, not this
row's.  It also proves nothing about `C₀`'s value: `C₀` is `numS`'s top coefficient because `denS`
is monic, it is never divided by, and `repDelta` cancels it.  Any PAIR-6 use of `repS`
UNDIFFERENCED would have to face it.

**The law this file applies is `hbdy_hat_eq`, not `hbdy_hat`, and that is load-bearing.**  `Ŝ` is
NOT PROPER (`deg num = deg den = 22n+125`, measured by attempt 3), so `Ŝ(∞) = C₀ ≠ 0` while
`evalRep` of any `Rep̂` tends to `0`: no `Rep̂` represents `Ŝ`, `repS n` represents `Ŝ − C₀`, and
BOTH strip samples are `−C₀ ≠ 0`.  `hbdy_hat`'s `hz0`/`hz1` are therefore both FALSE at this
object.  `hbdy_hat_eq` asks only that the two samples be EQUAL, which they are — and they are
equal for two DIFFERENT reasons, `sample_belt1` because the `(t+l)` run carries `l = 4n` and
`sample_belt0` because the `(2t+l)` run carries `l = 8n+1`.

**Elaborate with the corpus oleans on the path** — it imports `Zeta2HatRepOf`, `Zeta2HatRawPoles`,
`Zeta2HatShatForm` and `Zeta2HatShift`:

    sh external_tests/zeta2_arith/run_probe.sh Zeta2HatRepS.lean

Without `LEAN_PATH` pointing at the probes directory the imports fail, the run TRUNCATES, and NO
`#print axioms` line is printed at all — which is not a green.

**Receipts** `out_axioms_hatreps.txt`; falsifier arms `S1`–`S3` in `falsify_hatreps.sh` →
`out_hatreps_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic
import Zeta2HatRepOf
import Zeta2HatRawPoles
import Zeta2HatShatForm
import Zeta2HatShift

namespace Zeta2HatRepS

open Polynomial Finset Zeta2HatRep Zeta2HatBelt Zeta2HatShift
open Zeta2HatRawPoles Zeta2HatRepOf Zeta2HatShatForm

/-- `N = numS − C₀·denS`, the numerator of `Ŝ − C₀`.  `C₀` is `numS`'s top coefficient because
`denS` is MONIC — no division, and nothing about `C₀`'s value is ever needed. -/
noncomputable def NS (n : ℕ) (bh xh : ℚ[X]) : ℚ[X] :=
  numS n bh xh - C ((numS n bh xh).coeff (22 * n + 116)) * denS n

/-- **`repS n`** — the row's object: the `Rep̂` whose coefficients are `partialFractions_res`'s
solved residues at the UNREDUCED pole sets. -/
noncomputable def repS (n : ℕ) (bh xh : ℚ[X]) : Rephat :=
  repOf (idxS1 n) (idxS2 n) (NS n bh xh)

theorem denS_eval (n : ℕ) (t : ℚ) :
    (denS n).eval t
      = (∏ k ∈ idxS1 n, (t + ((k : ℕ) : ℚ))) * (∏ k ∈ idxS2 n, (t + ((k : ℕ) : ℚ))) ^ 2 := by
  rw [denS_eq]
  simp only [eval_mul, eval_prod, eval_add, eval_X, eval_C]
  ring

theorem NS_natDegree (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X])
    (hb : bh.natDegree ≤ 5) (hx : xh.natDegree ≤ 120) :
    (NS n bh xh).natDegree < (idxS1 n).card + 2 * (idxS2 n).card := by
  have h := natDegree_sub_lead_lt (p := numS n bh xh) (q := denS n) (d := 22 * n + 116)
    (by omega) (numS_natDegree_le n hn bh xh hb hx) (denS_monic n) (denS_natDegree n)
  rw [card_sum]
  exact h

/-- The representation, at every non-pole `t`. -/
theorem evalRep_repS (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X])
    (hb : bh.natDegree ≤ 5) (hx : xh.natDegree ≤ 120) (t : ℚ)
    (ht : ∀ k ∈ idxS1 n ∪ idxS2 n, t + ((k : ℕ) : ℚ) ≠ 0) :
    evalRep (repS n bh xh) t = (NS n bh xh).eval t / (denS n).eval t := by
  rw [repS, evalRep_repOf (idxS1 n) (idxS2 n) (idxS1_disjoint_idxS2 n) (NS n bh xh)
    (NS_natDegree n hn bh xh hb hx) t ht, denS_eval]

/-! ## The two strip samples — both `−C₀`, for two different reasons -/

theorem denS_eval_ne_belt1 (n : ℕ) : (denS n).eval (beltPt n 1) ≠ 0 := by
  rw [denS_eval]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k hk => ?_)
    (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k hk => ?_))
  · have : beltPt n 1 = -(4 * (n : ℚ)) := by rw [beltPt]; push_cast; ring
    rw [this]
    exact belt1_not_pole n k (Finset.mem_union_left _ hk)
  · have : beltPt n 1 = -(4 * (n : ℚ)) := by rw [beltPt]; push_cast; ring
    rw [this]
    exact belt1_not_pole n k (Finset.mem_union_right _ hk)

theorem denS_eval_ne_belt0 (n : ℕ) : (denS n).eval (beltPt n 0) ≠ 0 := by
  rw [denS_eval]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k hk => ?_)
    (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k hk => ?_))
  · have : beltPt n 0 = -(4 * (n : ℚ)) - 1 / 2 := by rw [beltPt]; push_cast; ring
    rw [this]
    exact belt0_not_pole n k
  · have : beltPt n 0 = -(4 * (n : ℚ)) - 1 / 2 := by rw [beltPt]; push_cast; ring
    rw [this]
    exact belt0_not_pole n k

theorem sample_belt1 (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X])
    (hb : bh.natDegree ≤ 5) (hx : xh.natDegree ≤ 120) :
    evalRep (repS n bh xh) (beltPt n 1) = -((numS n bh xh).coeff (22 * n + 116)) := by
  have hpt : beltPt n 1 = -(4 * (n : ℚ)) := by rw [beltPt]; push_cast; ring
  have hne := denS_eval_ne_belt1 n
  have hnum : (numS n bh xh).eval (beltPt n 1) = 0 := by
    rw [hpt]; exact numS_eval_belt1 n hn bh xh
  rw [evalRep_repS n hn bh xh hb hx _ (fun k hk => by
    rw [hpt]
    rcases Finset.mem_union.1 hk with h | h
    · exact belt1_not_pole n k (Finset.mem_union_left _ h)
    · exact belt1_not_pole n k (Finset.mem_union_right _ h))]
  rw [NS, eval_sub, eval_mul, eval_C, hnum, zero_sub, neg_div, mul_div_assoc,
    div_self hne, mul_one]

theorem sample_belt0 (n : ℕ) (hn : 2 ≤ n) (bh xh : ℚ[X])
    (hb : bh.natDegree ≤ 5) (hx : xh.natDegree ≤ 120) :
    evalRep (repS n bh xh) (beltPt n 0) = -((numS n bh xh).coeff (22 * n + 116)) := by
  have hpt : beltPt n 0 = -(4 * (n : ℚ)) - 1 / 2 := by rw [beltPt]; push_cast; ring
  have hne := denS_eval_ne_belt0 n
  have hnum : (numS n bh xh).eval (beltPt n 0) = 0 := by
    rw [hpt]; exact numS_eval_belt0 n hn bh xh
  rw [evalRep_repS n (by omega) bh xh hb hx _ (fun k hk => by
    rw [hpt]; exact belt0_not_pole n k)]
  rw [NS, eval_sub, eval_mul, eval_C, hnum, zero_sub, neg_div, mul_div_assoc,
    div_self hne, mul_one]

/-! ## The support floor — `7n+1 ≥ 4n+1`, with room -/

theorem support_floor (n k : ℕ) (hk : k ∈ idxS1 n ∪ idxS2 n) : 4 * n + 1 ≤ k := by
  simp only [idxS1, idxS2, Finset.mem_union, Finset.mem_Icc] at hk
  omega

/-! ## THE ROW -/

/-- **PAIR-5, `hbdy-hat`, for every `n ≥ 2` and every bounded-degree `(bh, xh)`.**  The proof is
three lines: `Zeta2HatShift.hbdy_hat_eq` applied with the support floor and the two strip samples,
both of which are `−C₀` — the first because the `(t+l)` run carries `l = 4n`, the second because
the `(2t+l)` run carries `l = 8n+1`.

Nothing in this proof goes through `Zeta2HatCancel`: the route never reduces the pole sets. -/
theorem hbdy_hat_n (n : ℕ) (hn : 2 ≤ n) (bh xh : ℚ[X])
    (hb : bh.natDegree ≤ 5) (hx : xh.natDegree ≤ 120) :
    Phihat n (repDelta (repS n bh xh)) = 0 :=
  hbdy_hat_eq n (repS n bh xh)
    (fun k hk => support_floor n k (repOfB_support _ _ _ hk))
    (fun k hk => support_floor n k (Finset.mem_union_right _ (repOfA_support _ _ _ hk)))
    (by rw [sample_belt0 n hn bh xh hb hx, sample_belt1 n (by omega) bh xh hb hx])

/-! ## The row's SECOND obligation, in the corrected form attempt 3 established

`repS n` represents `Ŝ − C₀`, not `Ŝ` — and this is the form PAIR-6 consumes through
`Zeta2HatInj.Phihat_of_evalRep`.  It was carried as a sentence for one pass, and a sentence is a
hypothesis until it elaborates (LEAN.md §3). -/

theorem evalRep_repS_eq_shat (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X])
    (hb : bh.natDegree ≤ 5) (hx : xh.natDegree ≤ 120) (t : ℚ)
    (ht : ∀ k ∈ idxS1 n ∪ idxS2 n, t + ((k : ℕ) : ℚ) ≠ 0)
    (hblk : (dBlock n).eval t ≠ 0) :
    evalRep (repS n bh xh) t
      = bh.eval t * xh.eval t * Zeta2HatRep.hatMember n t / (dRuns n * dBlock n).eval t
        - (numS n bh xh).coeff (22 * n + 116) := by
  have hden : (denS n).eval t ≠ 0 := by
    rw [denS_eval]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k hk => ?_)
      (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k hk => ?_))
    · exact ht k (Finset.mem_union_left _ hk)
    · exact ht k (Finset.mem_union_right _ hk)
  rw [evalRep_repS n hn bh xh hb hx t ht, shat_eq n hn bh xh t hblk hden, NS, eval_sub,
    eval_mul, eval_C]
  field_simp

end Zeta2HatRepS

#print axioms Zeta2HatRepS.denS_eval
#print axioms Zeta2HatRepS.NS_natDegree
#print axioms Zeta2HatRepS.evalRep_repS
#print axioms Zeta2HatRepS.denS_eval_ne_belt1
#print axioms Zeta2HatRepS.denS_eval_ne_belt0
#print axioms Zeta2HatRepS.sample_belt1
#print axioms Zeta2HatRepS.sample_belt0
#print axioms Zeta2HatRepS.support_floor
#print axioms Zeta2HatRepS.hbdy_hat_n
#print axioms Zeta2HatRepS.evalRep_repS_eq_shat
