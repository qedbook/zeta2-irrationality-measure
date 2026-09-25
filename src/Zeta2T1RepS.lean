/-
# Row PHI-BDY — the CONSTRUCTION: `repS n : Rep`, that it represents `S`, and the row's law on it

`docs/future/zeta2-lean-chain.md` row PHI-BDY, §PHI-BDY design notes.

**What the row owed after `Zeta2T1Shift`, and what this file pays.**  `Zeta2T1Shift.hbdy` proves the
row's LAW for an ARBITRARY `Rep` supported above `m`, given one hypothesis `hz`.  §6 of the row's
design notes records what was left: *"Nothing in §1–§3 exhibits `repS n : Rep` or proves
`evalRep (repS n) t = S t` off the poles."*  This file exhibits it, proves it represents, and
discharges `hz` — so `Φ (β₃n) (repDelta (repS n)) = 0` is a theorem about the row's own object.

**The three obstacles the row's cell named, each verified against the elaboration.**

  1. *"one `Polynomial.modByMonic` split for the improper part"* — **REAL, and it is three lines.**
     `S` is improper by `16n+48` (cand) / `9n+27` (rec), so `evalRep_repOf`'s properness premise is
     met by splitting `numS = (numS %ₘ denS) + denS * (numS /ₘ denS)` and carrying the quotient in
     `Rep`'s polynomial part — the part `Rep̂` does not have, and the reason the hat's
     `numS_natDegree_le` + `natDegree_sub_lead_lt` device is deleted rather than ported.
  2. *"ONE genuinely new algebraic lemma, the derivative of a simple-pole representation in closed
     form … [E] 80–150 lines"* — **REAL, and it is `res_deriv_id` + `phi_coord_eq`, ~45 lines.**
     Under the band, for a reason worth recording: the per-key step is an identity `ring` closes.
     With `den = (X+k)·E_k`, `den′·E_k − E_k′·den = E_k²` ON THE NOSE, so the closed form is one
     `Finset.sum_congr` over that.  No `HasDerivAt`, no analysis, exactly as the cell predicted.
  3. *"plus `(X + β₃n)² ∣ numS` [E] 40–80 lines"* — **REAL but HALF of it was already landed.**
     `Zeta2PF.eval_pair_zero_of_sq_dvd` — a square divisor kills both the value and the derivative —
     is the CONSUMING half and is a landed theorem of PAIR-4R's own file, so this row adds only the
     producing half (`sq_dvd_numS`: the two numerator blocks that both contain the strip offset).
     The transfer census that priced this row did not have that lemma in it.

**AND ONE OBSTACLE THE CELL DID NOT NAME, WHICH IS THE ONLY PLACE THIS ROW IS HARDER THAN PAIR-5.**
PAIR-5's structural lesson — *"take the WRITTEN denominator, regroup, and stop; a pole the numerator
kills gets coefficient 0, unproved and unmentioned"* — transfers to the RESIDUES exactly as the
transfer census says.  It does **not** transfer to `Phi_repDelta`'s SUPPORT hypothesis, and the two
were conflated.  At the hat every written pole clears the floor (`7n+1 ≥ 4n+1`), so
`Zeta2HatRepS.support_floor` is an `omega`.  Here that is FALSE: `D`'s β₂-slope run sits at
`[β₂n+1, β₂n+L]`, ENTIRELY below the floor `β₃n+1` once `n` passes the threshold, so the written
pole set contains keys the support hypothesis forbids.

The fix is not a cancellation and not a reduced pole set.  A `Finsupp`'s support is its NONZERO
set, so a below-floor pole leaves the support as soon as its residue is `0` — and that is one line,
because `numS = R + denS·Q` with `denS(−k) = 0` forces `R(−k) = numS(−k)`, so a pole the numerator
kills has `resB = 0` by `Zeta2PF.resB_simple` and nothing else (`repSOf_coeff_eq_zero`).  **So
PAIR-5's lesson holds after all, one level deeper than it was stated**: the uncancelled route
survives, the reduction is still never performed, and what the row pays is one containment fact
(`hlow`) saying the numerator's first block covers every below-floor written pole.

**What is GENERIC here and what is not.**  Everything through §5 is generic in `(S, NUM)`: no
member, no star solve, no census.  §6 instantiates at a `Zeta2Defs.Member` with the star numerator
`bT`, `xT` OPAQUE — only `natDegree` bounds are ever asked of them, as at the hat — and `D`'s index
set `dIdx` abstract, carrying only the two containment facts `t1_bdy_probe.py` measures.  The
literal coordinate lists never enter the proof, which is the same shape as `hbdy_hat_n`'s
`∀ (bh, xh) of bounded degree`.

**`m` is `β₃n`**, so the cell is `M = −m−1` and the strip integer is `M + 1 = −m`, both spelled as
`Zeta2Defs.Member.cell` spells them.

**Rung 0 (`LEAN.md` §5) — §7 is a GREEN/RED PAIR ON ONE OBJECT.**  Same pole set `S = {1}`, same
`m = 0`, same `Φ`, same `repSOf`: `hbdy_green` proves `Φ 0 (repDelta (repSOf {1} X²)) = 0`, and
`hbdy_red` proves `Φ 0 (repDelta (repSOf {1} X)) ≠ 0` — the SAME identity at the SAME point with
the double zero at the strip integer removed and NOTHING else changed.  Both are theorems, so the
conclusion is FALSE there rather than merely out of reach, which is what makes the first a
discriminating green.  Two expected-GREEN controls sit beside them (`evalRep_green` — the
construction computes the right FUNCTION at a concrete point; `repSOf_green_nontrivial` — the
object is not the zero `Rep`, so the green is not green-by-vacuity).

**How to elaborate it** (LEAN.md §0 — Lean never runs on the laptop):

    sh external_tests/zeta2_arith/run_probe.sh Zeta2T1RepS.lean

Without `LEAN_PATH` pointing at the probes directory the imports fail, the run TRUNCATES, and NO
`#print axioms` line is printed at all — which is not a green, and is what the receipt predicate's
third arm refuses.

**Receipts** `out_axioms_t1reps.txt`; falsifier `sh external_tests/zeta2_arith/falsify_t1reps.sh`
→ `out_t1reps_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic
import Zeta2HatRepOf
import Zeta2HatRawPoles
import Zeta2T1Shift

namespace Zeta2T1RepS

open Polynomial Finset Zeta2Defs
open Zeta2HatRepOf (repOf repOfA repOfB nodes)

/-! ## §1 — the monic run product, and the `block ↔ Icc` bridge -/

/-- `∏_{k ∈ S} (X + k)` — the denominator of a simple-pole family, in INDEX vocabulary.  This is
`Zeta2HatRawPoles`'s run product under a name, and its two facts are THAT file's, not a second
copy: PAIR-5 attempt 5's own retrospective records the sibling-files-carry-sibling-proofs defect
(`poleS1` vs `nodes ∅`, three declarations collapsed to nothing by ordering them), and the two
lemmas below are the same shape one row later. -/
noncomputable def runProd (S : Finset ℕ) : ℚ[X] := ∏ k ∈ S, (X + C ((k : ℕ) : ℚ))

theorem runProd_monic (S : Finset ℕ) : (runProd S).Monic := Zeta2HatRawPoles.monic_run S

theorem runProd_natDegree (S : Finset ℕ) : (runProd S).natDegree = S.card :=
  Zeta2HatRawPoles.natDegree_run S

theorem runProd_eval (S : Finset ℕ) (t : ℚ) :
    (runProd S).eval t = ∏ k ∈ S, (t + ((k : ℕ) : ℚ)) := by
  rw [runProd, eval_prod]
  simp

theorem runProd_eval_ne (S : Finset ℕ) (t : ℚ) (ht : ∀ k ∈ S, t + ((k : ℕ) : ℚ) ≠ 0) :
    (runProd S).eval t ≠ 0 := by
  rw [runProd_eval]
  exact Finset.prod_ne_zero_iff.2 ht

/-- `nodes ∅ = ∅`.  Named rather than inlined because `Zeta2PF.resB_simple`'s side condition is
`−k ∉ nodes ∅` at every call site below, and `simp` does not see through `nodes`. -/
theorem nodes_empty : nodes (∅ : Finset ℕ) = (∅ : Finset ℚ) := by
  rw [nodes]; exact Finset.image_empty _

theorem not_mem_nodes_empty (x : ℚ) : x ∉ nodes (∅ : Finset ℕ) := by
  rw [nodes_empty]; simp

/-- The member's denominator block, as a `Finset` product over its own pole window.  `block` is a
`range` product and `window` an `Icc`; this is the one reindexing between them. -/
theorem block_eq_runProd (c len : ℕ) (hlen : 1 ≤ len) :
    block c len = runProd (Finset.Icc c (c + len - 1)) := by
  have himg : Finset.Icc c (c + len - 1) = (Finset.range len).image (fun i => c + i) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨k - c, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega
  rw [runProd, himg, Finset.prod_image (fun x _ y _ h => by omega), block]

/-- A run contains the factor at any offset inside it. -/
theorem block_dvd (c len k : ℕ) (h1 : c ≤ k) (h2 : k < c + len) :
    (X + C ((k : ℕ) : ℚ)) ∣ block c len := by
  rw [block]
  have hmem : k - c ∈ Finset.range len := Finset.mem_range.2 (by omega)
  have hd := Finset.dvd_prod_of_mem (fun i : ℕ => X + C (((c + i : ℕ) : ℚ))) hmem
  rwa [show c + (k - c) = k by omega] at hd

/-! ## §2 — `repSOf`: the `Rep` of `NUM / ∏_{S}(X+k)`

The polynomial part is the quotient and the pole family is `partialFractions_res`'s SOLVED
residues at `S₂ = ∅`, taken from `Zeta2HatRepOf` unchanged.  Nothing about `NUM`'s shape is asked
for here — that is what makes this the same object at the hat and at tale-1. -/

/-- **`repSOf S NUM`** — the row's object, generic.  `Rep`'s polynomial part carries the improper
part that `Rep̂` had nowhere to put. -/
noncomputable def repSOf (S : Finset ℕ) (NUM : ℚ[X]) : Zeta2T1Shift.Rep :=
  (NUM /ₘ runProd S, repOfB S ∅ (NUM %ₘ runProd S))

/-- At `S₂ = ∅` the hat's order-2 family is the zero `Finsupp`, so `Rep̂`'s evaluation collapses
onto tale-1's pole sum and `evalRep_repOf` applies with no order-2 residue anywhere. -/
theorem repOfA_empty (S : Finset ℕ) (N : ℚ[X]) : repOfA S ∅ N = 0 := by
  ext k
  by_contra hne
  have hk : k ∈ (repOfA S ∅ N).support := Finsupp.mem_support_iff.2 (by simpa using hne)
  simpa using Zeta2HatRepOf.repOfA_support S ∅ N hk

/-- The remainder's degree, which is `evalRep_repOf`'s only premise about `NUM`. -/
theorem mod_natDegree_lt (S : Finset ℕ) (hS : S.Nonempty) (NUM : ℚ[X]) :
    (NUM %ₘ runProd S).natDegree < S.card + 2 * (∅ : Finset ℕ).card := by
  simp only [Finset.card_empty, mul_zero, add_zero]
  rcases eq_or_ne (NUM %ₘ runProd S) 0 with h | h
  · rw [h, natDegree_zero]
    exact Finset.card_pos.2 hS
  · have hlt := degree_modByMonic_lt NUM (runProd_monic S)
    have hnd := natDegree_lt_natDegree h hlt
    rwa [runProd_natDegree] at hnd

/-- The pole family alone, summed — the bridge from `Rep̂`'s evaluation to tale-1's. -/
theorem poles_sum (S : Finset ℕ) (N : ℚ[X]) (hdeg : N.natDegree < S.card + 2 * (∅ : Finset ℕ).card)
    (t : ℚ) (ht : ∀ k ∈ S, t + ((k : ℕ) : ℚ) ≠ 0) :
    (repOfB S ∅ N).sum (fun k c => c / (t + ((k : ℕ) : ℚ))) = N.eval t / (runProd S).eval t := by
  have hunion : ∀ k ∈ S ∪ (∅ : Finset ℕ), t + ((k : ℕ) : ℚ) ≠ 0 := by
    intro k hk; exact ht k (by simpa using hk)
  have h := Zeta2HatRepOf.evalRep_repOf S ∅ (by simp) N hdeg t hunion
  rw [Zeta2HatRep.evalRep, repOf, repOfA_empty] at h
  simpa [runProd_eval] using h

/-- **The row's SECOND obligation, generically: `repSOf` represents `NUM / ∏(X+k)` off the poles.**
The `modByMonic` split is the whole of it — the quotient goes in the polynomial part, the
remainder is proper, and `evalRep_repOf` carries the rest. -/
theorem evalRep_repSOf (S : Finset ℕ) (hS : S.Nonempty) (NUM : ℚ[X]) (t : ℚ)
    (ht : ∀ k ∈ S, t + ((k : ℕ) : ℚ) ≠ 0) :
    Zeta2T1Shift.evalRep (repSOf S NUM) t = NUM.eval t / (runProd S).eval t := by
  have hne : (runProd S).eval t ≠ 0 := runProd_eval_ne S t ht
  have hsplit : NUM %ₘ runProd S + runProd S * (NUM /ₘ runProd S) = NUM :=
    modByMonic_add_div NUM (runProd S)
  have hev := congrArg (fun p : ℚ[X] => p.eval t) hsplit
  simp only [eval_add, eval_mul] at hev
  show (NUM /ₘ runProd S).eval t + (repOfB S ∅ (NUM %ₘ runProd S)).sum
      (fun k c => c / (t + ((k : ℕ) : ℚ))) = _
  rw [poles_sum S _ (mod_natDegree_lt S hS NUM) t ht]
  field_simp
  linarith [hev]

/-! ## §3 — the SUPPORT, and why the uncancelled denominator survives

This is the step with no hat twin.  `Zeta2HatRepS.support_floor` is an `omega` because every
written pole of `Ŝ` clears the floor; tale-1's `D` puts a whole run BELOW it.  What rescues the
route is that a `Finsupp`'s support is its NONZERO set. -/

/-- A pole the numerator kills has residue `0`, so it is not in the support.  `denS(−k) = 0` is
what makes the remainder agree with `NUM` there, which is why no cancellation is performed and
none is needed — PAIR-5's lesson, one level below where PAIR-5 stated it. -/
theorem repSOf_coeff_eq_zero (S : Finset ℕ) (NUM : ℚ[X]) {k : ℕ} (hk : k ∈ S)
    (h0 : NUM.eval (-((k : ℕ) : ℚ)) = 0) : (repSOf S NUM).2 k = 0 := by
  have hden : (runProd S).eval (-((k : ℕ) : ℚ)) = 0 := by
    rw [runProd_eval]
    exact Finset.prod_eq_zero hk (neg_add_cancel _)
  have hsplit : NUM %ₘ runProd S + runProd S * (NUM /ₘ runProd S) = NUM :=
    modByMonic_add_div NUM (runProd S)
  have hR : (NUM %ₘ runProd S).eval (-((k : ℕ) : ℚ)) = 0 := by
    have hev := congrArg (fun p : ℚ[X] => p.eval (-((k : ℕ) : ℚ))) hsplit
    simp only [eval_add, eval_mul, hden, zero_mul, add_zero] at hev
    rw [hev, h0]
  show repOfB S ∅ (NUM %ₘ runProd S) k = 0
  rw [Zeta2HatRepOf.repOfB_apply S ∅ _ (Finset.mem_union_left _ hk),
    Zeta2PF.resB_simple _ _ _ (not_mem_nodes_empty _), hR, zero_div]

/-- **The support hypothesis `Phi_repDelta` needs, from run containment alone.**  A key is in the
support only if it is a written pole AND the numerator does not kill it; `hlow` says every written
pole below the floor IS killed. -/
theorem repSOf_support (S : Finset ℕ) (NUM : ℚ[X]) (m : ℕ)
    (hlow : ∀ k ∈ S, k < m + 1 → NUM.eval (-((k : ℕ) : ℚ)) = 0) :
    ∀ k ∈ (repSOf S NUM).2.support, m + 1 ≤ k := by
  intro k hk
  by_contra hlt
  have hkS : k ∈ S := by
    have hsub := Zeta2HatRepOf.repOfB_support S ∅ (NUM %ₘ runProd S) hk
    simpa using hsub
  exact Finsupp.mem_support_iff.1 hk
    (repSOf_coeff_eq_zero S NUM hkS (hlow k hkS (by omega)))

/-! ## §4 — the closed form for the derivative of a simple-pole representation

The row's ONE genuinely new algebraic step (`Zeta2HatRepS.sample_belt0/1` have no twin here: the
hat discharges its hypothesis by two VALUE samples, tale-1's is a DERIVATIVE).  It is done by
`Polynomial.derivative` alone — no `HasDerivAt`, no analysis — because the per-key step is an
identity `ring` closes. -/

/-- The cofactor at a key: `den / (X + k)`. -/
noncomputable def cofac (S : Finset ℕ) (k : ℕ) : ℚ[X] := ∏ j ∈ S.erase k, (X + C ((j : ℕ) : ℚ))

theorem runProd_eq_cofac (S : Finset ℕ) {k : ℕ} (hk : k ∈ S) :
    runProd S = (X + C ((k : ℕ) : ℚ)) * cofac S k :=
  (Finset.mul_prod_erase S _ hk).symm

/-- `partialFractions_res`'s cofactor at `S₂ = ∅` IS `cofac`.  Stated so that no call site below
has to carry `nodes ∅` and `∅` in the same goal — the two are equal, and rewriting one direction
un-matches the other (`Zeta2HatRepOf.pf1_eq` is stated in `nodes` vocabulary). -/
theorem pf1_eq_cofac (S : Finset ℕ) (k : ℕ) :
    Zeta2PF.pf1 (nodes S) (∅ : Finset ℚ) (-((k : ℕ) : ℚ)) = cofac S k := by
  rw [← nodes_empty, Zeta2HatRepOf.pf1_eq S ∅ k, cofac]
  simp

/-- **THE CLOSED FORM, for an arbitrary coefficient family.**  `den′·N − N′·den = Σ_k c_k·E_k²` as
POLYNOMIALS whenever `N` is the residue-weighted sum of cofactors.  The per-key step is
`den′·E − E′·den = E²` with `den = (X+k)·E`, which `ring` closes on the nose — the whole reason
this came in under the cell's `[E] 80–150 lines`. -/
theorem deriv_pf_sum (S : Finset ℕ) (c : ℕ → ℚ) :
    derivative (runProd S) * (∑ k ∈ S, C (c k) * cofac S k)
        - derivative (∑ k ∈ S, C (c k) * cofac S k) * runProd S
      = ∑ k ∈ S, C (c k) * (cofac S k) ^ 2 := by
  rw [derivative_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [derivative_C_mul]
  conv_lhs => rw [runProd_eq_cofac S hk]
  rw [derivative_mul, derivative_add, derivative_X, derivative_C]
  ring

/-- Polynomial-valued reindexing of a sum over `nodes S`.  `Zeta2HatRepOf.sum_nodes` is the
ℚ-valued twin; the injectivity is its, not re-derived. -/
theorem sum_nodes_poly (S : Finset ℕ) (f : ℚ → ℚ[X]) :
    ∑ x ∈ nodes S, f x = ∑ κ ∈ S, f (-((κ : ℕ) : ℚ)) := by
  classical
  rw [nodes]
  exact Finset.sum_image (fun x _ y _ h => Zeta2HatPoles.neg_cast_inj h)

/-- `partialFractions_res` at `S₂ = ∅`, in INDEX vocabulary: the numerator IS the residue-weighted
sum of cofactors.  The residues are `repSOf`'s own, so nothing is solved twice. -/
theorem res_decomp (S : Finset ℕ) (N : ℚ[X])
    (hdeg : N.natDegree < S.card + 2 * (∅ : Finset ℕ).card) :
    N = ∑ k ∈ S, C (repOfB S ∅ N k) * cofac S k := by
  classical
  have hnd : Disjoint (nodes S) (nodes (∅ : Finset ℕ)) := Zeta2HatRepOf.nodes_disjoint (by simp)
  have hdeg' : N.natDegree < (nodes S).card + 2 * (nodes (∅ : Finset ℕ)).card := by
    rwa [Zeta2HatRepOf.card_nodes, Zeta2HatRepOf.card_nodes]
  have key := Zeta2PF.partialFractions_res (nodes S) (nodes ∅) hnd N hdeg'
  rw [nodes_empty, Finset.sum_empty, add_zero] at key
  refine key.trans ?_
  rw [sum_nodes_poly]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Zeta2HatRepOf.repOfB_apply S ∅ N (Finset.mem_union_left _ hk), nodes_empty, pf1_eq_cofac]

/-- The cofactor's value: `E_k(a)·(a+k) = den(a)`. -/
theorem cofac_eval (S : Finset ℕ) {k : ℕ} (hk : k ∈ S) (a : ℚ) :
    (cofac S k).eval a * (a + ((k : ℕ) : ℚ)) = (runProd S).eval a := by
  conv_rhs => rw [runProd_eq_cofac S hk]
  rw [eval_mul, eval_add, eval_X, eval_C]
  ring

/-- The strip-residue sum in closed form, evaluated: `Σ_k c_k/(a+k)² = (den′(a)N(a) −
N′(a)den(a))/den(a)²`.  This is the cell's formula verbatim, with `x_k = −k`. -/
theorem res_deriv_eval (S : Finset ℕ) (N : ℚ[X])
    (hdeg : N.natDegree < S.card + 2 * (∅ : Finset ℕ).card) (a : ℚ)
    (ha : ∀ k ∈ S, a + ((k : ℕ) : ℚ) ≠ 0) :
    (derivative (runProd S)).eval a * N.eval a - (derivative N).eval a * (runProd S).eval a
      = (runProd S).eval a ^ 2 * ∑ k ∈ S, repOfB S ∅ N k / (a + ((k : ℕ) : ℚ)) ^ 2 := by
  classical
  -- the closed form as POLYNOMIALS first: rewriting the residue sum back to `N` has to happen
  -- before `eval` is pushed in, or the sum is no longer the one `res_decomp` names.
  have hpoly := deriv_pf_sum S (repOfB S ∅ N)
  rw [← res_decomp S N hdeg] at hpoly
  have hid := congrArg (fun p : ℚ[X] => p.eval a) hpoly
  simp only [eval_sub, eval_mul, eval_finsetSum, eval_pow, eval_C] at hid
  rw [hid, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hne := ha k hk
  have hE : (cofac S k).eval a = (runProd S).eval a / (a + ((k : ℕ) : ℚ)) := by
    rw [eq_div_iff hne]; exact cofac_eval S hk a
  rw [hE, div_pow]
  field_simp

/-! ## §5 — the Φ coordinate IS the derivative of `NUM/den`, and the row's law on the object -/

/-- **`Φ`'s rational coordinate on `repDelta (repSOf S NUM)` is exactly `(NUM/den)′` at the strip
integer**, in closed form and with the polynomial part included.  Everything the row needs is a
corollary: the GREEN arm is `(X+m)² ∣ NUM` making the numerator vanish, the RED arm is a concrete
`NUM` for which it does not. -/
theorem phi_coord_eq (S : Finset ℕ) (hS : S.Nonempty) (NUM : ℚ[X]) (m : ℕ) (hm : m ∉ S) :
    (derivative (repSOf S NUM).1).eval (-((m : ℕ) : ℚ))
        - (repSOf S NUM).2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2)
      = ((derivative NUM).eval (-((m : ℕ) : ℚ)) * (runProd S).eval (-((m : ℕ) : ℚ))
          - NUM.eval (-((m : ℕ) : ℚ)) * (derivative (runProd S)).eval (-((m : ℕ) : ℚ)))
        / (runProd S).eval (-((m : ℕ) : ℚ)) ^ 2 := by
  classical
  have hak : ∀ k ∈ S, (-((m : ℕ) : ℚ)) + ((k : ℕ) : ℚ) ≠ 0 := by
    intro k hk hz
    have hkm : (k : ℚ) = (m : ℚ) := by linarith
    exact hm (by rwa [Nat.cast_inj.1 hkm] at hk)
  have hden : (runProd S).eval (-((m : ℕ) : ℚ)) ≠ 0 := runProd_eval_ne S _ hak
  have hsplit : NUM %ₘ runProd S + runProd S * (NUM /ₘ runProd S) = NUM :=
    modByMonic_add_div NUM (runProd S)
  -- the value and the derivative of the split, at the strip integer
  have hNUM0 : NUM.eval (-((m : ℕ) : ℚ))
      = (NUM %ₘ runProd S).eval (-((m : ℕ) : ℚ))
        + (runProd S).eval (-((m : ℕ) : ℚ)) * (NUM /ₘ runProd S).eval (-((m : ℕ) : ℚ)) := by
    have hev := congrArg (fun p : ℚ[X] => p.eval (-((m : ℕ) : ℚ))) hsplit
    simp only [eval_add, eval_mul] at hev
    linarith [hev]
  have hNUM1 : (derivative NUM).eval (-((m : ℕ) : ℚ))
      = (derivative (NUM %ₘ runProd S)).eval (-((m : ℕ) : ℚ))
        + (derivative (runProd S)).eval (-((m : ℕ) : ℚ))
            * (NUM /ₘ runProd S).eval (-((m : ℕ) : ℚ))
        + (runProd S).eval (-((m : ℕ) : ℚ))
            * (derivative (NUM /ₘ runProd S)).eval (-((m : ℕ) : ℚ)) := by
    have hd : derivative (NUM %ₘ runProd S)
        + (derivative (runProd S) * (NUM /ₘ runProd S)
            + runProd S * derivative (NUM /ₘ runProd S)) = derivative NUM := by
      rw [← derivative_mul, ← derivative_add, hsplit]
    have hev := congrArg (fun p : ℚ[X] => p.eval (-((m : ℕ) : ℚ))) hd
    simp only [eval_add, eval_mul] at hev
    linarith [hev]
  -- the closed form on the REMAINDER, which is the proper part
  have hid := res_deriv_eval S (NUM %ₘ runProd S) (mod_natDegree_lt S hS NUM) _ hak
  -- the Finsupp sum is the Finset sum over `S`
  have hsupp : (repSOf S NUM).2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2)
      = ∑ k ∈ S, repOfB S ∅ (NUM %ₘ runProd S) k / ((-((m : ℕ) : ℚ)) + ((k : ℕ) : ℚ)) ^ 2 := by
    show (repOfB S ∅ (NUM %ₘ runProd S)).sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2) = _
    rw [Finsupp.sum_of_support_subset _ (by
      intro k hk
      simpa using Zeta2HatRepOf.repOfB_support S ∅ (NUM %ₘ runProd S) hk) _ (fun i _ => by simp)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    ring
  rw [hsupp, eq_div_iff (pow_ne_zero 2 hden)]
  show ((derivative (NUM /ₘ runProd S)).eval (-((m : ℕ) : ℚ)) - _) * _ = _
  linear_combination (derivative (runProd S)).eval (-((m : ℕ) : ℚ)) * hNUM0
    - (runProd S).eval (-((m : ℕ) : ℚ)) * hNUM1 + hid

/-- **The `hz` hypothesis of `Zeta2T1Shift.hbdy`, discharged from a DOUBLE ZERO.**  `(X + m)² ∣ NUM`
kills `NUM` and `NUM′` at `−m` (`Zeta2PF.eval_pair_zero_of_sq_dvd`, landed), so `phi_coord_eq`'s
numerator is `0`. -/
theorem hz_repSOf (S : Finset ℕ) (hS : S.Nonempty) (NUM : ℚ[X]) (m : ℕ) (hm : m ∉ S)
    (hsq : (X + C ((m : ℕ) : ℚ)) ^ 2 ∣ NUM) :
    (derivative (repSOf S NUM).1).eval (-((m : ℕ) : ℚ))
      = (repSOf S NUM).2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2) := by
  have hsq' : (X - C (-((m : ℕ) : ℚ))) ^ 2 ∣ NUM := by
    rw [map_neg, sub_neg_eq_add]; exact hsq
  obtain ⟨hnum0, hnum1⟩ := Zeta2PF.eval_pair_zero_of_sq_dvd hsq'
  have h := phi_coord_eq S hS NUM m hm
  rw [hnum0, hnum1, zero_mul, zero_mul, sub_zero, zero_div] at h
  linarith [h]

/-- **ROW PHI-BDY's law, on the row's own object.**  `Zeta2T1Shift.hbdy` with both of its
hypotheses discharged from run containment plus one divisibility. -/
theorem hbdy_repSOf (S : Finset ℕ) (hS : S.Nonempty) (NUM : ℚ[X]) (m : ℕ) (hm : m ∉ S)
    (hlow : ∀ k ∈ S, k < m + 1 → NUM.eval (-((k : ℕ) : ℚ)) = 0)
    (hsq : (X + C ((m : ℕ) : ℚ)) ^ 2 ∣ NUM) :
    Zeta2T1Shift.Phi m (Zeta2T1Shift.repDelta (repSOf S NUM)) = 0 :=
  Zeta2T1Shift.hbdy m (repSOf S NUM) (repSOf_support S NUM m hlow) (hz_repSOf S hS NUM m hm hsq)

/-! ## §6 — the instantiation at a `Zeta2Defs.Member`

`bT` (the star solve's `b(·−1)`) and `xT` (its degree-`dx` coefficient list) are OPAQUE — exactly
as `bh`/`xh` are at the hat, and for the same reason: the degree-141 certificate that priced the
earlier route out is not in the route.  `dIdx` is `D`'s index set, abstract, carrying only the two
containment facts the probe measures. -/

/-- `S = b(·−1)·numPoly·x / (denPoly · ∏_D)` — the (★) antidifference's numerator. -/
noncomputable def numS (mem : Member) (n : ℕ) (bT xT : ℚ[X]) : ℚ[X] :=
  bT * mem.numPoly n * xT

/-- The WRITTEN pole index set: the member's own window, then `D`'s indices.  NOT reduced. -/
def idxS (mem : Member) (n : ℕ) (dIdx : Finset ℕ) : Finset ℕ := mem.window n ∪ dIdx

theorem idxS_nonempty (mem : Member) (hm : mem.WF) (n : ℕ) (dIdx : Finset ℕ) :
    (idxS mem n dIdx).Nonempty := by
  refine ⟨mem.a4 * n + 1, Finset.mem_union_left _ ?_⟩
  have hle := Nat.mul_le_mul_right n hm.a4_lt.le
  simp only [Member.window, Finset.mem_Icc]
  omega

/-- `denPoly` as a run product over the window. -/
theorem denPoly_eq_runProd (mem : Member) (hm : mem.WF) (n : ℕ) :
    mem.denPoly n = runProd (mem.window n) := by
  have hle := Nat.mul_le_mul_right n hm.a4_lt.le
  have hsub : (mem.b4 - mem.a4) * n = mem.b4 * n - mem.a4 * n := Nat.sub_mul _ _ _
  rw [Member.denPoly, block_eq_runProd _ _ (by omega), Member.window]
  congr 1
  refine Finset.ext fun k => ?_
  simp only [Finset.mem_Icc]
  omega

/-- The written denominator IS `denPoly · ∏_D`, given the poles are simple (the probe's §D:
ALL SIMPLE at every `n ≥ 1` of a seven-point ladder, both members). -/
theorem runProd_idxS (mem : Member) (hm : mem.WF) (n : ℕ) (dIdx : Finset ℕ)
    (hdisj : Disjoint (mem.window n) dIdx) (t : ℚ) :
    (runProd (idxS mem n dIdx)).eval t
      = (mem.denPoly n).eval t * ∏ k ∈ dIdx, (t + ((k : ℕ) : ℚ)) := by
  rw [idxS, runProd_eval, Finset.prod_union hdisj, denPoly_eq_runProd mem hm n, runProd_eval]

/-- **`(X + β₃n)² ∣ numS` — the row's third named obstacle, from TWO numerator blocks.**  The
strip offset `β₃n` lies in `numPoly`'s first block `[1, α₁n]` and in its second `[β₂n+1, α₂n]`,
and the two are different factors of the same product, so the square divides. -/
theorem sq_dvd_numS (mem : Member) (n : ℕ) (bT xT : ℚ[X])
    (h1 : 1 ≤ mem.b3 * n) (h2 : mem.b3 * n ≤ mem.a1 * n)
    (h3 : mem.b2 * n + 1 ≤ mem.b3 * n)
    (h4 : mem.b3 * n < mem.b2 * n + 1 + (mem.a2 - mem.b2) * n) :
    (X + C (((mem.b3 * n : ℕ) : ℚ))) ^ 2 ∣ numS mem n bT xT := by
  have d1 : (X + C (((mem.b3 * n : ℕ) : ℚ))) ∣ block 1 (mem.a1 * n) :=
    block_dvd 1 (mem.a1 * n) (mem.b3 * n) h1 (by omega)
  have d2 : (X + C (((mem.b3 * n : ℕ) : ℚ)))
      ∣ block (mem.b2 * n + 1) ((mem.a2 - mem.b2) * n) :=
    block_dvd _ _ (mem.b3 * n) h3 h4
  have dsq : (X + C (((mem.b3 * n : ℕ) : ℚ))) ^ 2
      ∣ block 1 (mem.a1 * n) * block (mem.b2 * n + 1) ((mem.a2 - mem.b2) * n) := by
    rw [sq]; exact mul_dvd_mul d1 d2
  rw [numS, Member.numPoly]
  exact dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dsq _) bT) xT

/-- Every below-floor written pole is killed by `numPoly`'s FIRST block.  The window's own poles
clear the floor by `Member.WF.b3_le` (`β₃ ≤ α₄`), which is the row's `in:` entry for it. -/
theorem numS_low_zero (mem : Member) (hm : mem.WF) (n : ℕ) (bT xT : ℚ[X]) (dIdx : Finset ℕ)
    (hlow : ∀ k ∈ dIdx, k < mem.b3 * n + 1 → 1 ≤ k ∧ k ≤ mem.a1 * n) :
    ∀ k ∈ idxS mem n dIdx, k < mem.b3 * n + 1 →
      (numS mem n bT xT).eval (-((k : ℕ) : ℚ)) = 0 := by
  intro k hk hlt
  have hkD : k ∈ dIdx := by
    rcases Finset.mem_union.1 hk with h | h
    · exfalso
      have hb3 := Nat.mul_le_mul_right n hm.b3_le
      simp only [Member.window, Finset.mem_Icc] at h
      omega
    · exact h
  obtain ⟨hk1, hk2⟩ := hlow k hkD hlt
  have hb : (X + C ((k : ℕ) : ℚ)) ∣ block 1 (mem.a1 * n) :=
    block_dvd 1 (mem.a1 * n) k hk1 (by omega)
  have hdvd : (X + C ((k : ℕ) : ℚ)) ∣ numS mem n bT xT := by
    rw [numS, Member.numPoly]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hb _) _) bT) xT
  obtain ⟨G, hG⟩ := hdvd
  rw [hG, eval_mul, eval_add, eval_X, eval_C]
  ring

/-- **ROW PHI-BDY, at the member.**  `Φ (β₃n) (repDelta (repS n)) = 0` for the star
antidifference's own representation, for ANY bounded star solve. -/
theorem hbdy_t1 (mem : Member) (hm : mem.WF) (n : ℕ) (bT xT : ℚ[X]) (dIdx : Finset ℕ)
    (hstrip : mem.b3 * n ∉ idxS mem n dIdx)
    (hlow : ∀ k ∈ dIdx, k < mem.b3 * n + 1 → 1 ≤ k ∧ k ≤ mem.a1 * n)
    (h1 : 1 ≤ mem.b3 * n) (h2 : mem.b3 * n ≤ mem.a1 * n)
    (h3 : mem.b2 * n + 1 ≤ mem.b3 * n)
    (h4 : mem.b3 * n < mem.b2 * n + 1 + (mem.a2 - mem.b2) * n) :
    Zeta2T1Shift.Phi (mem.b3 * n)
        (Zeta2T1Shift.repDelta (repSOf (idxS mem n dIdx) (numS mem n bT xT))) = 0 :=
  hbdy_repSOf (idxS mem n dIdx) (idxS_nonempty mem hm n dIdx) (numS mem n bT xT) (mem.b3 * n)
    hstrip (numS_low_zero mem hm n bT xT dIdx hlow) (sq_dvd_numS mem n bT xT h1 h2 h3 h4)

/-- **The row's SECOND obligation at the member: `evalRep (repS n) t = S t` off the poles.** -/
theorem evalRep_repS_eq_S (mem : Member) (hm : mem.WF) (n : ℕ) (bT xT : ℚ[X]) (dIdx : Finset ℕ)
    (hdisj : Disjoint (mem.window n) dIdx) (t : ℚ)
    (ht : ∀ k ∈ idxS mem n dIdx, t + ((k : ℕ) : ℚ) ≠ 0) :
    Zeta2T1Shift.evalRep (repSOf (idxS mem n dIdx) (numS mem n bT xT)) t
      = bT.eval t * (mem.numPoly n).eval t * xT.eval t
          / ((mem.denPoly n).eval t * ∏ k ∈ dIdx, (t + ((k : ℕ) : ℚ))) := by
  rw [evalRep_repSOf _ (idxS_nonempty mem hm n dIdx) _ t ht,
    runProd_idxS mem hm n dIdx hdisj t, numS, eval_mul, eval_mul]

/-! ## §7 — the two landed tale-1 members, with `D`'s runs written down

The literals below are the ONLY member-specific data in this file, and a literal transcribed from
a 21 MB coordinate file by eye is a claim rather than evidence.  The instrument that turns it into
evidence is `../zeta2_star_b1/t1_druns_check.py`: **113 checks, 0 failed, four falsifier arms all
as wanted** on BOTH landed coordinate files.  Its §A compares `D`'s factor MULTISET off the file
against exactly these three runs at ten `n` (0,1,2,3,4,5,6,9,17,40) — multiset and not set, since
a repeated index would be an order-2 pole and everything above is stated at `S₂ = ∅`.

**Both thresholds below are MEASURED SHARP, not margins** (that checker's §G, stated as an
EQUALITY so an arm moving the threshold in either direction reds):

  * `3 ≤ n` — from here the written pole set is SIMPLE and the window is clear of `D`.  Below it
    the three `D` runs overlap EACH OTHER (multiplicity 2 at `n = 1,2`, 3 at `n = 0`), so `S₂ = ∅`
    is not merely unproved there, it is false.
  * `4 ≤ n` — from here the strip integer `β₃n` is not a written pole, which is `hstrip`.  Below
    it `D`'s β₂-slope run `[β₂n+1, β₂n+L]` CONTAINS `β₃n`, since `(β₃−β₂)n ≤ L`.

Both clear the row's own `N₀ = 6`, so nothing downstream moves.  **This `4` and
`t1_bdy_probe.py`'s SHARP `3` are different measurements of different objects and both are
right**: that probe measures the order of the REDUCED `S`, and at `n = 3` the record's own
`b`-factor `(t + n + 3)` happens to vanish at the strip integer as well, so the reduced order is
2 there by an accident of the solve rather than by run structure.  This file consumes the WRITTEN
pole set, which is what `partialFractions_res` is handed, so it states `4`. -/

/-- `D`'s pole indices at the RECORD member `(7,6,5,8;14)`, off `coords/starcoords_rec-t1.txt`
(`FACSYM D 51`, all lead-1, all multiplicity 1). -/
def dIdxRec (n : ℕ) : Finset ℕ :=
  Finset.Icc (n + 1) (n + 3) ∪ Finset.Icc (2 * n + 1) (2 * n + 6)
    ∪ Finset.Icc (14 * n + 2) (14 * n + 43)

/-- `D`'s pole indices at the CANDIDATE `(13,11,9,15;26)` — the member the μ bound is about —
off `coords/starcoords_cand-t1.txt` (`FACSYM D 96`, all lead-1, all multiplicity 1). -/
def dIdxCand (n : ℕ) : Finset ℕ :=
  Finset.Icc (2 * n + 1) (2 * n + 6) ∪ Finset.Icc (4 * n + 1) (4 * n + 12)
    ∪ Finset.Icc (26 * n + 2) (26 * n + 79)

/-- **ROW PHI-BDY AT THE CANDIDATE, with no structural hypothesis left.**  `Φ (β₃n) (repDelta
(repS n)) = 0` for every `n ≥ 4` and every star solve `(bT, xT)`. -/
theorem hbdy_cand (n : ℕ) (hn : 4 ≤ n) (bT xT : ℚ[X]) :
    Zeta2T1Shift.Phi (candidateM.b3 * n)
        (Zeta2T1Shift.repDelta
          (repSOf (idxS candidateM n (dIdxCand n)) (numS candidateM n bT xT))) = 0 := by
  have e1 : candidateM.a1 = 13 := rfl
  have e2 : candidateM.a2 = 11 := rfl
  have e4 : candidateM.a4 = 15 := rfl
  have e5 : candidateM.b2 = 2 := rfl
  have e6 : candidateM.b3 = 4 := rfl
  have e7 : candidateM.b4 = 26 := rfl
  refine hbdy_t1 candidateM candidateM_wf n bT xT (dIdxCand n) ?_ ?_ ?_ ?_ ?_ ?_
  · intro hmem
    simp only [idxS, dIdxCand, Member.window, e1, e2, e4, e5, e6, e7, Finset.mem_union,
      Finset.mem_Icc] at hmem
    omega
  · intro k hk hlt
    simp only [dIdxCand, Finset.mem_union, Finset.mem_Icc] at hk
    simp only [e1, e6] at hlt ⊢
    omega
  · simp only [e6]; omega
  · simp only [e1, e6]; omega
  · simp only [e5, e6]; omega
  · simp only [e2, e5, e6]; omega

/-- **ROW PHI-BDY AT THE RECORD member**, the same statement at `Zeta2StarRecT1N0`'s member. -/
theorem hbdy_rec (n : ℕ) (hn : 4 ≤ n) (bT xT : ℚ[X]) :
    Zeta2T1Shift.Phi (recordM.b3 * n)
        (Zeta2T1Shift.repDelta
          (repSOf (idxS recordM n (dIdxRec n)) (numS recordM n bT xT))) = 0 := by
  have e1 : recordM.a1 = 7 := rfl
  have e2 : recordM.a2 = 6 := rfl
  have e4 : recordM.a4 = 8 := rfl
  have e5 : recordM.b2 = 1 := rfl
  have e6 : recordM.b3 = 2 := rfl
  have e7 : recordM.b4 = 14 := rfl
  refine hbdy_t1 recordM recordM_wf n bT xT (dIdxRec n) ?_ ?_ ?_ ?_ ?_ ?_
  · intro hmem
    simp only [idxS, dIdxRec, Member.window, e1, e2, e4, e5, e6, e7, Finset.mem_union,
      Finset.mem_Icc] at hmem
    omega
  · intro k hk hlt
    simp only [dIdxRec, Finset.mem_union, Finset.mem_Icc] at hk
    simp only [e1, e6] at hlt ⊢
    omega
  · simp only [e6]; omega
  · simp only [e1, e6]; omega
  · simp only [e5, e6]; omega
  · simp only [e2, e5, e6]; omega

/-- The window is clear of `D` from `n = 3`, which is `evalRep_repS_eq_S`'s `hdisj`. -/
theorem disjoint_window_dIdxCand (n : ℕ) (hn : 3 ≤ n) :
    Disjoint (candidateM.window n) (dIdxCand n) := by
  have e4 : candidateM.a4 = 15 := rfl
  have e7 : candidateM.b4 = 26 := rfl
  rw [Finset.disjoint_left]
  intro k hk hk2
  simp only [Member.window, e4, e7, Finset.mem_Icc] at hk
  simp only [dIdxCand, Finset.mem_union, Finset.mem_Icc] at hk2
  omega

/-- `D`'s three runs are pairwise disjoint from `n = 3`, so the `Finset` union really is the
WRITTEN denominator rather than a union that silently dropped a repeated factor.  Load-bearing
for reading the theorem below as "`= S t`": at `n ≤ 2` the runs DO overlap. -/
theorem prod_dIdxCand (n : ℕ) (hn : 3 ≤ n) (t : ℚ) :
    ∏ k ∈ dIdxCand n, (t + ((k : ℕ) : ℚ))
      = (∏ k ∈ Finset.Icc (2 * n + 1) (2 * n + 6), (t + ((k : ℕ) : ℚ)))
        * (∏ k ∈ Finset.Icc (4 * n + 1) (4 * n + 12), (t + ((k : ℕ) : ℚ)))
        * ∏ k ∈ Finset.Icc (26 * n + 2) (26 * n + 79), (t + ((k : ℕ) : ℚ)) := by
  have hAB : Disjoint (Finset.Icc (2 * n + 1) (2 * n + 6))
      (Finset.Icc (4 * n + 1) (4 * n + 12)) := by
    rw [Finset.disjoint_left]
    intro k hk hk2
    simp only [Finset.mem_Icc] at hk hk2
    omega
  have hABC : Disjoint (Finset.Icc (2 * n + 1) (2 * n + 6) ∪ Finset.Icc (4 * n + 1) (4 * n + 12))
      (Finset.Icc (26 * n + 2) (26 * n + 79)) := by
    rw [Finset.disjoint_left]
    intro k hk hk2
    simp only [Finset.mem_union, Finset.mem_Icc] at hk
    simp only [Finset.mem_Icc] at hk2
    omega
  rw [dIdxCand, Finset.prod_union hABC, Finset.prod_union hAB]

/-- **The row's SECOND obligation at the candidate: `evalRep (repS n) t = S t` off the poles**,
with `S`'s written denominator spelled out as the member's own block times `D`'s three runs. -/
theorem evalRep_repS_eq_S_cand (n : ℕ) (hn : 3 ≤ n) (bT xT : ℚ[X]) (t : ℚ)
    (ht : ∀ k ∈ idxS candidateM n (dIdxCand n), t + ((k : ℕ) : ℚ) ≠ 0) :
    Zeta2T1Shift.evalRep (repSOf (idxS candidateM n (dIdxCand n)) (numS candidateM n bT xT)) t
      = bT.eval t * (candidateM.numPoly n).eval t * xT.eval t
          / ((candidateM.denPoly n).eval t
              * ((∏ k ∈ Finset.Icc (2 * n + 1) (2 * n + 6), (t + ((k : ℕ) : ℚ)))
                * (∏ k ∈ Finset.Icc (4 * n + 1) (4 * n + 12), (t + ((k : ℕ) : ℚ)))
                * ∏ k ∈ Finset.Icc (26 * n + 2) (26 * n + 79), (t + ((k : ℕ) : ℚ)))) := by
  rw [evalRep_repS_eq_S candidateM candidateM_wf n bT xT (dIdxCand n)
    (disjoint_window_dIdxCand n hn) t ht, prod_dIdxCand n hn t]

/-! ## §8 — rung 0: the GREEN/RED PAIR ON ONE OBJECT

Same pole set `S = {1}`, same `m = 0`, same `Φ`, same `repSOf`.  The ONLY difference between the
two theorems below is whether `NUM` has a DOUBLE zero at the strip integer `t = 0`: `X²` does, `X`
does not.  The second is proved `≠ 0`, so the row's conclusion is FALSE without the double zero
rather than merely unproved.  Both instances are IMPROPER (`deg NUM ≥ deg den`), so the arms also
exercise the `modByMonic` split rather than dodging it. -/

theorem one_nonempty : ({1} : Finset ℕ).Nonempty := ⟨1, by simp⟩

theorem zero_not_mem_one : (0 : ℕ) ∉ ({1} : Finset ℕ) := by decide

theorem runProd_one : runProd ({1} : Finset ℕ) = X + C (1 : ℚ) := by
  rw [runProd]; simp

/-- **GREEN.**  `X²` has the double zero at `t = 0`, and the row's law holds. -/
theorem hbdy_green :
    Zeta2T1Shift.Phi 0 (Zeta2T1Shift.repDelta (repSOf {1} (X ^ 2))) = 0 := by
  refine hbdy_repSOf {1} one_nonempty (X ^ 2) 0 zero_not_mem_one (fun k hk hlt => ?_) ?_
  · simp only [Finset.mem_singleton] at hk
    omega
  · simp

/-- **RED — the SAME identity at the SAME point with the double zero removed.**  `X` has only a
SIMPLE zero at `t = 0`; `Φ`'s rational coordinate is then `1`, not `0`.  Machine-checked, so the
statement is false there and not merely out of reach. -/
theorem hbdy_red :
    Zeta2T1Shift.Phi 0 (Zeta2T1Shift.repDelta (repSOf {1} X)) ≠ 0 := by
  have hsupp : ∀ k ∈ (repSOf {1} (X : ℚ[X])).2.support, 0 + 1 ≤ k := by
    intro k hk
    have hsub := Zeta2HatRepOf.repOfB_support {1} ∅ ((X : ℚ[X]) %ₘ runProd {1}) hk
    simp only [Finset.union_empty, Finset.mem_singleton] at hsub
    omega
  have hcoord := phi_coord_eq {1} one_nonempty (X : ℚ[X]) 0 zero_not_mem_one
  -- the closed form's RIGHT-hand side at this instance is `1`, computed without touching the
  -- left-hand side, so `hcoord` stays syntactically the term `Phi_repDelta` produces
  have hrhs : (((derivative (X : ℚ[X])).eval (-((0 : ℕ) : ℚ))
        * (runProd ({1} : Finset ℕ)).eval (-((0 : ℕ) : ℚ))
      - (X : ℚ[X]).eval (-((0 : ℕ) : ℚ))
        * (derivative (runProd ({1} : Finset ℕ))).eval (-((0 : ℕ) : ℚ)))
    / (runProd ({1} : Finset ℕ)).eval (-((0 : ℕ) : ℚ)) ^ 2) = 1 := by
    rw [runProd_one, derivative_X_add_C]
    norm_num
  rw [hrhs] at hcoord
  rw [Zeta2T1Shift.Phi_repDelta 0 _ hsupp]
  intro h
  have h2 := congrArg Prod.snd h
  rw [hcoord] at h2
  simp at h2

/-- **Expected-GREEN control 1.**  The construction computes the RIGHT FUNCTION, at a concrete
point: `evalRep (repSOf {1} X²) 2 = 4/3 = 2²/(2+1)`.  An arm table that reds everywhere it looks is
not evidence of discrimination. -/
theorem evalRep_green : Zeta2T1Shift.evalRep (repSOf {1} (X ^ 2)) 2 = 4 / 3 := by
  rw [evalRep_repSOf {1} one_nonempty (X ^ 2) 2 (fun k hk => by
    simp only [Finset.mem_singleton] at hk
    subst hk
    norm_num)]
  rw [runProd_one]
  norm_num

/-- **Expected-GREEN control 2.**  The green object is not the zero `Rep`, so `hbdy_green` is not
a green by vacuity. -/
theorem repSOf_green_nontrivial : repSOf {1} (X ^ 2) ≠ 0 := by
  intro h
  have h1 := evalRep_green
  rw [h] at h1
  simp only [Zeta2T1Shift.evalRep] at h1
  norm_num at h1

/-! ## §9 — receipts (`LEAN.md` §1 — exit 0 is not an attestation) -/

end Zeta2T1RepS

#print axioms Zeta2T1RepS.runProd_natDegree
#print axioms Zeta2T1RepS.block_eq_runProd
#print axioms Zeta2T1RepS.block_dvd
#print axioms Zeta2T1RepS.repOfA_empty
#print axioms Zeta2T1RepS.mod_natDegree_lt
#print axioms Zeta2T1RepS.poles_sum
#print axioms Zeta2T1RepS.evalRep_repSOf
#print axioms Zeta2T1RepS.repSOf_coeff_eq_zero
#print axioms Zeta2T1RepS.repSOf_support
#print axioms Zeta2T1RepS.deriv_pf_sum
#print axioms Zeta2T1RepS.pf1_eq_cofac
#print axioms Zeta2T1RepS.res_decomp
#print axioms Zeta2T1RepS.cofac_eval
#print axioms Zeta2T1RepS.res_deriv_eval
#print axioms Zeta2T1RepS.phi_coord_eq
#print axioms Zeta2T1RepS.hz_repSOf
#print axioms Zeta2T1RepS.hbdy_repSOf
#print axioms Zeta2T1RepS.denPoly_eq_runProd
#print axioms Zeta2T1RepS.runProd_idxS
#print axioms Zeta2T1RepS.sq_dvd_numS
#print axioms Zeta2T1RepS.numS_low_zero
#print axioms Zeta2T1RepS.hbdy_t1
#print axioms Zeta2T1RepS.evalRep_repS_eq_S
#print axioms Zeta2T1RepS.hbdy_cand
#print axioms Zeta2T1RepS.hbdy_rec
#print axioms Zeta2T1RepS.disjoint_window_dIdxCand
#print axioms Zeta2T1RepS.prod_dIdxCand
#print axioms Zeta2T1RepS.evalRep_repS_eq_S_cand
#print axioms Zeta2T1RepS.hbdy_green
#print axioms Zeta2T1RepS.hbdy_red
#print axioms Zeta2T1RepS.evalRep_green
#print axioms Zeta2T1RepS.repSOf_green_nontrivial
