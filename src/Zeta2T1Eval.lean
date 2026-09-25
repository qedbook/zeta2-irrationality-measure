/-
# Row PHI-EVAL — `Φ` evaluates the member's representation to the coordinates

`docs/future/zeta2-lean-chain.md` row PHI-EVAL.

**What the row owes.**  `Zeta2Defs.Member.qn`/`.pn` are DEFINED as the §1.1/§5.2 closed forms —
`qₙ = sgn·Π·Σ_k c_k` and `pₙ = −sgn·Π·(Σ_j P_j I_j(C) − Σ_k c_k H⁽²⁾_{k+⌊C⌋})`.  `Zeta2T1Shift.Phi`
is defined on `Rep = ℚ[X] × (ℕ →₀ ℚ)`, abstractly, by the two coordinates the tale-1 kernel
produces.  **The row is the claim that those two definitions are the same numbers**, once the
sign/Π normalisation is applied — it is an IDENTIFICATION row and the identification content sits
in the STATEMENT, which is why the statement below quantifies over an ARBITRARY representing `Rep`
rather than over the constructed one.

**The row's theorem is `Phi_rho`**, and it says: if `r : Rep` evaluates to `R_n/Π = numPoly/denPoly`
off the pole window — which is ALL that STAR-ID delivers about `ρⱼ = u·Pa j`, since the (★) data is
a function, not a syntactic `Rep` — then

    ( sgn·Π·(Φ (β₃n) r).1 , −sgn·Π·(Φ (β₃n) r).2 ) = ( qₙ , pₙ ).

Uniqueness of the partial-fraction data (`Zeta2T1Inj.evalRep_inj`, row PHI-REP) is what turns the
hypothesis about the FUNCTION into a statement about the `Rep`; the construction `repR` below is
then only the witness that some representing `Rep` exists, not the object the consumer must supply.

**The `in:` list, and what each input actually contributed.**

  * `Zeta2Resid.member_eq_Ppol_add_residues` (RESID) — the whole analytic content:
    `R_n/Π = Ppol + Σ_{k ∈ window} c_k/(t+k)` off the poles.  Used once, in `evalRep_repR`.
  * `Zeta2T1Inj.evalRep_inj` (PHI-REP) — used once, in `Phi_rho`, and it is what makes the row's
    statement about the function rather than about a spelling.
  * `Zeta2Defs.qn/pn/pnHarm/pnPoly/momI/cell` — the target vocabulary.
  * `Zeta2Moments.momI_eq_bernoulli` — **an input the row's cell did not name, and it is
    load-bearing.**  `Zeta2Moments.momI` is the §5.2 RECURSION and `Zeta2Defs.momI` is the
    BERNOULLI EVALUATION; `Zeta2T1Shift.Phi` is built on the first and `Member.pnPoly` on the
    second, so they are NOT the same constant and no `rfl` bridges them.  `momI_agree` below is
    that bridge, and it is the reason `Zeta2Moments` is an import of this file.  (`harm` is
    duplicated the same way — `Zeta2Defs.harm` and `Zeta2Moments.harm` — but there the two bodies
    are literally the same expression, so `harm_agree` IS `rfl`.  Two duplications, two different
    answers: the difference had to be measured, not assumed.)
  * `Zeta2MomStep.momI_step` — **NOT used.**  It is the moment RECURSION as a rewrite rule, which
    is what PAIR-0p's per-instance evaluation of the 16n moments needed.  This row never evaluates
    a moment: `Lpoly_Ppol` moves the whole moment sum across symbolically.  Listed here because a
    named input that turns out to be unnecessary is a measurement about the row's size, and the
    cell should stop charging for it.

**What this file does NOT do, and the row's honest scope.**  It does not identify `ρⱼ` with
`R_{n+j}/Π` — that is STAR-ID, and `Phi_rho`'s hypothesis `hr` is exactly the shape STAR-ID must
produce.  It says nothing about the recurrence; turning `α·Φ ρⱼ = 0` into `hrecq`/`hrecp` is
L1-ASM's job, and `Phi_rho` is stated in the coordinate pair L1-ASM consumes.

**AMENDED 2026-09-17, by STAR-ID's closing unit, and the row's statement is UNCHANGED.**
`Phi_rho_off` is `Phi_rho` with the hypothesis weakened to hold only off a caller-supplied extra
`Finset ℚ`, and `Phi_rho` is now its `E := ∅` corollary — one proof, not two.  The generalisation
is forced by what STAR-ID can actually deliver: `Zeta2StarId.rho_eq_member` identifies the (★)
datum with `numPoly (n+j) / denPoly (n+j)` only where `denPoly n` and the rebase denominator
`D_n = afProd pa0Facs` are ALSO nonzero, and for `j > 0` neither of those zero sets is contained
in `mem.window (n+j)` — so the unmodified `Phi_rho` could not be applied at all.  Consumer:
`Zeta2StarIdPhi.star_phi_rho`.

**The index-agreement hazard, and what is proved about it here.**  `Phi m` reads the cell only
through `Lpoly (−m−1)` and `harm 2 (k−m−1)`; `Member.cell n = −β₃n−1` and
`Member.harmIndex n k = k−β₃n−1`.  So instantiating `m := β₃n` makes the two agree BY DEFINITION —
`cell_eq` is a cast lemma and `Phi_snd`'s harmonic half closes by `rfl`.  That is stronger than
PAIR-0p's measurement at `n = 1, 2`, which was a check at two points; here the agreement is the
statement's own shape at every `n`.  §7's `Phi_index_matters` proves the index is not decorative:
the same `Rep` has a DIFFERENT `Φ` at `m` and at `m + 1`.

**How to elaborate it** (LEAN.md §0 — Lean never runs on the laptop):

    sh external_tests/zeta2_arith/run_probe.sh Zeta2T1Eval.lean

Falsifier: `sh external_tests/zeta2_arith/falsify_t1eval.sh`.  Archived output:
`out_axioms_t1eval.txt`, `out_t1eval_falsify.txt`.
-/
import Zeta2Resid
import Zeta2T1Inj

namespace Zeta2T1Eval

open Polynomial Finset Zeta2Defs Zeta2T1Shift

/-! ## §1 — the pole family as a `Finsupp`, and its sums -/

/-- The member's residue family `k ↦ c_k` on the pole window, as a `Finsupp`.  Written as a sum
of `single`s rather than with `Finsupp.indicator` because every use below is a SUM over it, and
`Finsupp.sum_finset_sum_index` turns that into the `Finset` sum `qn`/`pnHarm` are stated with in
one rewrite. -/
noncomputable def ckRep (mem : Member) (n : ℕ) : ℕ →₀ ℚ :=
  ∑ k ∈ mem.window n, Finsupp.single k (mem.ck n k)

/-- **The one bookkeeping lemma.**  Any additive-in-the-value `g` sums over `ckRep` as the
`Finset` sum over the window.  All three of `Φ`'s and `evalRep`'s sums are instances. -/
theorem ckRep_sum (mem : Member) (n : ℕ) (g : ℕ → ℚ → ℚ)
    (h0 : ∀ k, g k 0 = 0) (hadd : ∀ (k : ℕ) (a b : ℚ), g k (a + b) = g k a + g k b) :
    (ckRep mem n).sum g = ∑ k ∈ mem.window n, g k (mem.ck n k) := by
  rw [ckRep, ← Finsupp.sum_finsetSum_index h0 hadd]
  exact Finset.sum_congr rfl fun k _ => Finsupp.sum_single_index (h0 k)

/-- The `Rep` of `R_n/Π`: the §5.2 polynomial part and the residues.  RESID says this is the
partial-fraction data, so by `evalRep_inj` it is THE representation and not merely one. -/
noncomputable def repR (mem : Member) (n : ℕ) : Rep := (mem.Ppol n, ckRep mem n)

/-! ## §2 — the two duplicated constants, bridged

`Zeta2Defs` and `Zeta2Moments` each carry a `momI` and a `harm`.  One pair is `rfl` and the other
is a landed theorem; the file would elaborate with the wrong belief about either, since a failed
`rfl` is an error and a succeeding one is silent. -/

/-- `Zeta2Moments.momI` is the §5.2 four-line recursion; `Zeta2Defs.momI` is `B_j(M+1)`.  A2's own
conclusion (`momI_eq_bernoulli`, receipted in `Zeta2Moments.lean`) is the bridge. -/
theorem momI_agree (M : ℤ) (j : ℕ) : Zeta2Moments.momI M j = Zeta2Defs.momI M j := by
  rw [Zeta2Moments.momI_eq_bernoulli]
  rfl

/-- The two `harm`s ARE the same expression, so this one is `rfl` — and it is written down rather
than used silently, because the `momI` pair above shows that "same name, same file family" does
not imply it. -/
theorem harm_agree (s k : ℕ) : Zeta2Moments.harm s k = Zeta2Defs.harm s k := rfl

/-- `Φ`'s cell `−m−1` at `m := β₃n` IS `Member.cell n`.  A cast, and the whole of the
index-agreement obligation on the polynomial half. -/
theorem cell_eq (mem : Member) (n : ℕ) : -((mem.b3 * n : ℕ) : ℤ) - 1 = mem.cell n := by
  rw [Member.cell]
  push_cast
  ring

/-! ## §3 — `Φ`'s two coordinates on `repR` -/

/-- `Φ`'s ζ(2) coordinate is the bare residue sum: `qₙ` without its `sgn·Π`. -/
theorem Phi_fst (mem : Member) (n : ℕ) :
    (Phi (mem.b3 * n) (repR mem n)).1 = ∑ k ∈ mem.window n, mem.ck n k := by
  have h : (Phi (mem.b3 * n) (repR mem n)).1 = (ckRep mem n).sum (fun _ c => c) := rfl
  rw [h]
  exact ckRep_sum mem n _ (fun _ => rfl) (fun _ _ _ => rfl)

/-- The moment functional on the polynomial part IS `pnPoly`.  `Polynomial.sum_over_range` moves
`Lpoly`'s support sum onto `range (natDegree + 1)`, which is the range `pnPoly` is stated with;
`momI_agree` then bridges the two moment constants termwise. -/
theorem Lpoly_Ppol (mem : Member) (n : ℕ) :
    Zeta2Moments.Lpoly (mem.cell n) (mem.Ppol n) = mem.pnPoly n := by
  rw [Zeta2Moments.Lpoly,
    Polynomial.sum_over_range (mem.Ppol n) (fun j => zero_mul (Zeta2Moments.momI (mem.cell n) j)),
    Member.pnPoly]
  exact Finset.sum_congr rfl fun j _ => by rw [momI_agree]

/-- `Φ`'s rational coordinate is `pnPoly − pnHarm`: `pₙ` without its `−sgn·Π`. -/
theorem Phi_snd (mem : Member) (n : ℕ) :
    (Phi (mem.b3 * n) (repR mem n)).2 = mem.pnPoly n - mem.pnHarm n := by
  have h : (Phi (mem.b3 * n) (repR mem n)).2
      = Zeta2Moments.Lpoly (-((mem.b3 * n : ℕ) : ℤ) - 1) (mem.Ppol n)
        - (ckRep mem n).sum (fun k c => c * Zeta2Moments.harm 2 (k - mem.b3 * n - 1)) := rfl
  rw [h, cell_eq, Lpoly_Ppol,
    ckRep_sum mem n _ (fun k => zero_mul (Zeta2Moments.harm 2 (k - mem.b3 * n - 1)))
      (fun k a b => add_mul a b (Zeta2Moments.harm 2 (k - mem.b3 * n - 1))),
    Member.pnHarm]
  refine congrArg (fun x => mem.pnPoly n - x) (Finset.sum_congr rfl fun k _ => ?_)
  rw [harm_agree, Member.harmIndex]

/-! ## §4 — the representation, from RESID -/

/-- `repR` represents `R_n/Π` off the pole window.  This is RESID's evaluated corollary with the
`Finsupp` sum unfolded, and nothing else. -/
theorem evalRep_repR (mem : Member) (hm : mem.WF) (n : ℕ) (t : ℚ)
    (ht : ∀ k ∈ mem.window n, t + (k : ℚ) ≠ 0) :
    evalRep (repR mem n) t = (mem.numPoly n).eval t / (mem.denPoly n).eval t := by
  have h : evalRep (repR mem n) t
      = (mem.Ppol n).eval t + (ckRep mem n).sum (fun k c => c / (t + (k : ℚ))) := rfl
  rw [h, ckRep_sum mem n _ (fun k => zero_div (t + (k : ℚ)))
      (fun k a b => add_div a b (t + (k : ℚ))),
    Zeta2Resid.member_eq_Ppol_add_residues mem hm n t ht]

/-! ## §5 — PHI-EVAL, on the constructed representation and then on ANY -/

/-- **PHI-EVAL at the constructed `Rep`.**  The sign/Π normalisation is applied exactly as
`Zeta2Defs` builds it into `qn`/`pn`: `+sgn·Π` on the ζ(2) coordinate, `−sgn·Π` on the rational
one. -/
theorem Phi_repR_coords (mem : Member) (n : ℕ) :
    (mem.sgn n * mem.Pin n * (Phi (mem.b3 * n) (repR mem n)).1,
      -(mem.sgn n * mem.Pin n) * (Phi (mem.b3 * n) (repR mem n)).2)
      = (mem.qn n, mem.pn n) := by
  have hq : mem.sgn n * mem.Pin n * (∑ k ∈ mem.window n, mem.ck n k) = mem.qn n := by
    rw [Member.qn]
  have hp : -(mem.sgn n * mem.Pin n) * (mem.pnPoly n - mem.pnHarm n) = mem.pn n := by
    rw [Member.pn]
    ring
  rw [Phi_fst, Phi_snd, hq, hp]

/-- **ROW PHI-EVAL, off an ARBITRARY extra finite set.**  Same statement as `Phi_rho` below,
with the hypothesis weakened to hold only off a caller-supplied `E`.  `evalRep_inj` already
takes an arbitrary finite exceptional set, so this costs one `Finset.union` and nothing else —
and it is what row STAR-ID needs, because the (★) rebase `ρ j = u · Pa j` is the member's
function only where `denPoly n` and the rebase denominator `D_n` are ALSO nonzero, and neither
of those two zero sets is inside `mem.window n`.  Added 2026-09-17 by STAR-ID's closing unit;
`Phi_rho` is now its `E := ∅` corollary rather than a second proof. -/
theorem Phi_rho_off (mem : Member) (hm : mem.WF) (n : ℕ) (r : Rep) (E : Finset ℚ)
    (hr : ∀ t : ℚ, t ∉ E → (∀ k ∈ mem.window n, t + (k : ℚ) ≠ 0) →
      evalRep r t = (mem.numPoly n).eval t / (mem.denPoly n).eval t) :
    (mem.sgn n * mem.Pin n * (Phi (mem.b3 * n) r).1,
      -(mem.sgn n * mem.Pin n) * (Phi (mem.b3 * n) r).2)
      = (mem.qn n, mem.pn n) := by
  classical
  have hE : r = repR mem n := by
    refine Zeta2T1Inj.evalRep_inj r (repR mem n)
      (E ∪ (mem.window n).image (fun k : ℕ => -((k : ℕ) : ℚ))) ?_
    intro t htE
    have htE' : t ∉ E := fun h => htE (Finset.mem_union_left _ h)
    have ht : ∀ k ∈ mem.window n, t + (k : ℚ) ≠ 0 := by
      intro k hk hc
      exact htE (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk, by linarith⟩))
    rw [hr t htE' ht, evalRep_repR mem hm n t ht]
  rw [hE]
  exact Phi_repR_coords mem n

/-- **ROW PHI-EVAL.**  `Φ` evaluates ANY representation of `R_n/Π` to the member's coordinates.
The hypothesis is the shape a consumer PRODUCES (LEAN.md §3): STAR-ID identifies the (★) datum
`ρⱼ` with the FUNCTION `R_{n+j}/Π`, off the poles, and that is all this asks for. -/
theorem Phi_rho (mem : Member) (hm : mem.WF) (n : ℕ) (r : Rep)
    (hr : ∀ t : ℚ, (∀ k ∈ mem.window n, t + (k : ℚ) ≠ 0) →
      evalRep r t = (mem.numPoly n).eval t / (mem.denPoly n).eval t) :
    (mem.sgn n * mem.Pin n * (Phi (mem.b3 * n) r).1,
      -(mem.sgn n * mem.Pin n) * (Phi (mem.b3 * n) r).2)
      = (mem.qn n, mem.pn n) :=
  Phi_rho_off mem hm n r ∅ (fun t _ ht => hr t ht)

/-- The candidate's instance — the member the μ ≤ 5.0495243 bound is about.  A specialisation,
not a second proof. -/
theorem Phi_rho_candidate (n : ℕ) (r : Rep)
    (hr : ∀ t : ℚ, (∀ k ∈ candidateM.window n, t + (k : ℚ) ≠ 0) →
      evalRep r t = (candidateM.numPoly n).eval t / (candidateM.denPoly n).eval t) :
    (candidateM.sgn n * candidateM.Pin n * (Phi (candidateM.b3 * n) r).1,
      -(candidateM.sgn n * candidateM.Pin n) * (Phi (candidateM.b3 * n) r).2)
      = (candidateM.qn n, candidateM.pn n) :=
  Phi_rho candidateM candidateM_wf n r hr

/-! ## §6 — rung 0: the GREEN/RED pair on ONE object

Same member, same `n`, same `Φ`, same `repR`.  The ONLY difference is whether the sign/Π
normalisation is applied.  `qn 0 = −1` (`Zeta2Defs.Member.qn_zero`) while the bare `Φ` coordinate
is the residue sum `c₁ = 1` (`Member.ck_zero`), so the row's conclusion is FALSE without the
normalisation rather than merely unproved. -/

/-- The candidate's window at `n = 0` is the single pole `k = 1`. -/
theorem window_zero_candidate : candidateM.window 0 = {1} := Member.window_zero candidateM

/-- **GREEN.**  The row's theorem at the candidate, `n = 0`, on the constructed representation —
so the green is the ROW's statement and not a lemma of it. -/
theorem phi_eval_green :
    (candidateM.sgn 0 * candidateM.Pin 0 * (Phi (candidateM.b3 * 0) (repR candidateM 0)).1,
      -(candidateM.sgn 0 * candidateM.Pin 0) * (Phi (candidateM.b3 * 0) (repR candidateM 0)).2)
      = (candidateM.qn 0, candidateM.pn 0) :=
  Phi_repR_coords candidateM 0

/-- **RED — the SAME `Φ` on the SAME object with the normalisation removed.**  `Φ`'s ζ(2)
coordinate is `+1` and `qn 0` is `−1`.  Machine-checked, so "up to the sign/Π normalisation" is
carrying weight rather than hedging. -/
theorem phi_eval_red :
    (Phi (candidateM.b3 * 0) (repR candidateM 0)).1 ≠ candidateM.qn 0 := by
  rw [Phi_fst, window_zero_candidate, Finset.sum_singleton, Member.ck_zero,
    Member.qn_zero candidateM]
  norm_num

/-- **Expected-GREEN control 1.**  The construction computes the RIGHT FUNCTION at a concrete
point: `R_0/Π` is `1/(t+1)`, so at `t = 1` it is `1/2`.  An arm table that reds everywhere it
looks is not evidence of discrimination. -/
theorem evalRep_repR_green : evalRep (repR candidateM 0) 1 = 1 / 2 := by
  rw [evalRep_repR candidateM candidateM_wf 0 1 (fun k hk => by
    rw [window_zero_candidate] at hk
    simp only [Finset.mem_singleton] at hk
    subst hk
    norm_num)]
  norm_num [Member.numPoly, Member.denPoly, block, candidateM]

/-- **Expected-GREEN control 2.**  The green object is not the zero `Rep`, so `phi_eval_green` is
not a green by vacuity. -/
theorem repR_green_nontrivial : repR candidateM 0 ≠ 0 := by
  intro h
  have h1 := evalRep_repR_green
  rw [h] at h1
  rw [Zeta2T1Inj.evalRep_zero] at h1
  norm_num at h1

/-! ## §7 — the cell index is not decorative

`Wone_shift_off_by_one_false`'s trap, stated on `Φ` itself rather than on the member: the same
`Rep` at two adjacent cells has two different `Φ`s.  ℕ subtraction is why — `harm 2 (k−m−1)`
truncates one step earlier at `m + 1`, which is exactly the off-by-one the row's `m := β₃n`
instantiation has to get right. -/

/-- One pole at `k = 2`, residue `1`, no polynomial part. -/
noncomputable def probeRep : Rep := (0, Finsupp.single 2 1)

theorem probe_fst : (Finsupp.single 2 (1 : ℚ)).sum (fun _ c => c) = 1 :=
  Finsupp.sum_single_index rfl

theorem Phi_probe_zero : Phi 0 probeRep = (1, -1) := by
  have h2 : (Finsupp.single 2 (1 : ℚ)).sum (fun k c => c * Zeta2Moments.harm 2 (k - 0 - 1))
      = 1 * Zeta2Moments.harm 2 (2 - 0 - 1) := Finsupp.sum_single_index (by simp)
  have h : Phi 0 probeRep
      = ((Finsupp.single 2 (1 : ℚ)).sum (fun _ c => c),
        Zeta2Moments.Lpoly (-(0 : ℤ) - 1) 0
          - (Finsupp.single 2 (1 : ℚ)).sum (fun k c => c * Zeta2Moments.harm 2 (k - 0 - 1))) := rfl
  rw [h, probe_fst, h2, Zeta2Moments.Lpoly_zero]
  norm_num [Zeta2Moments.harm]

theorem Phi_probe_one : Phi 1 probeRep = (1, 0) := by
  have h2 : (Finsupp.single 2 (1 : ℚ)).sum (fun k c => c * Zeta2Moments.harm 2 (k - 1 - 1))
      = 1 * Zeta2Moments.harm 2 (2 - 1 - 1) := Finsupp.sum_single_index (by simp)
  have h : Phi 1 probeRep
      = ((Finsupp.single 2 (1 : ℚ)).sum (fun _ c => c),
        Zeta2Moments.Lpoly (-(1 : ℤ) - 1) 0
          - (Finsupp.single 2 (1 : ℚ)).sum (fun k c => c * Zeta2Moments.harm 2 (k - 1 - 1))) := rfl
  rw [h, probe_fst, h2, Zeta2Moments.Lpoly_zero]
  norm_num [Zeta2Moments.harm]

/-- **The index matters.**  So `Phi (mem.b3 * n)` in the row's statement is a load-bearing choice,
and a statement made at `β₃n + 1` would be a different — and false — claim. -/
theorem Phi_index_matters : Phi 0 probeRep ≠ Phi 1 probeRep := by
  rw [Phi_probe_zero, Phi_probe_one]
  norm_num

/-! ## §8 — receipts (`LEAN.md` §1 — exit 0 is not an attestation) -/

#print axioms window_zero_candidate
#print axioms probe_fst
#print axioms Phi_probe_zero
#print axioms Phi_probe_one
#print axioms ckRep_sum
#print axioms momI_agree
#print axioms harm_agree
#print axioms cell_eq
#print axioms Phi_fst
#print axioms Lpoly_Ppol
#print axioms Phi_snd
#print axioms evalRep_repR
#print axioms Phi_repR_coords
#print axioms Phi_rho_off
#print axioms Phi_rho
#print axioms Phi_rho_candidate
#print axioms phi_eval_green
#print axioms phi_eval_red
#print axioms evalRep_repR_green
#print axioms repR_green_nontrivial
#print axioms Phi_index_matters

end Zeta2T1Eval
