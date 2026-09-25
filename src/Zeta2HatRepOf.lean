/-
# Row PAIR-5 — `repOf`: a cleared partial-fraction identity ⇒ a `Rep̂` that REPRESENTS the quotient

`docs/future/zeta2-lean-chain.md` row PAIR-5, §PAIR-5 design notes attempt 5.

**What the row owed that this file pays.**  PAIR-5's first obligation is *exhibit* `repS n : Rep̂`
and its second is *`evalRep (repS n) t = Ŝ t − C₀` off a finite set*.  The corpus had that step
only at the hat member: `Zeta2HatPoles.hat_rep_of_residues` goes from the cleared polynomial
identity to `evalRep (repHat n) t = hatPi n * hatMember n t`, but it does it with the residues
**supplied** and the member's own index sets **baked in**.  `Ŝ` has no closed form for any residue
(its numerator carries the degree-120 certificate `x̂` as an unfactored coefficient list), so no
instantiation of that lemma reaches it.

**What this file does.**  With `Zeta2PF.partialFractions_res` — the same generic lemma with the
residues SOLVED FOR, landed by attempt 3 — the computation can be done ONCE, generically in two
`Finset ℕ` index sets, and a consumer then supplies only its own `S₁`, `S₂` and numerator:

    repOf S₁ S₂ N : Rep̂                                   -- coefficients ARE the solved residues
    evalRep_repOf : evalRep (repOf S₁ S₂ N) t
                      = N.eval t / (∏_{S₁}(t+k) · (∏_{S₂}(t+k))²)

and its ONLY hypotheses are `Disjoint S₁ S₂`, the degree bound `N.natDegree < |S₁| + 2|S₂|`, and
non-vanishing at `t`.  All three are statements about the INDEX SETS and the DEGREE; none is about
`N`'s shape.  That is precisely what makes it usable at `Ŝ`.

**What this file does NOT do.**  It says nothing about `Ŝ`, about PAIR-5's pole sets, or about any
polynomial of this corpus: `S₁`, `S₂` and `N` are free.  It is the generic half only; the row's own
sets arrive in `Zeta2HatRawPoles` and the row's object in `Zeta2HatRepS`.  It also proves nothing
about `repOf`'s support beyond `⊆ S₁ ∪ S₂` — in particular nothing about which of those keys carry
a NONZERO residue, which for `Ŝ` is a strictly smaller set (`Zeta2HatCancel`'s reduced `T₁ ∪ T₂`,
measured, unproved on this route and not needed by it).

**Where the node vocabulary lives, and why it lives here.**  `nodes`/`card_nodes`/`nodes_disjoint`/
`sum_nodes` translate an index `Finset ℕ` into the `Finset ℚ` of poles `t = −k` that
`Zeta2PF.partialFractions_res` consumes.  They are generic in exactly the way `Zeta2PartialFractions`
is, and the design's reuse census recommends they end up there.  They are HERE instead because the
move is not free: `nodes` rests on `Zeta2HatPoles.neg_cast_inj` and the cofactor lemmas `pf1_eq`/
`pf2_eq` rest on `image_erase_comm`/`poly_prod_image`/`poly_prod_image_sq`, all four LANDED in
`Zeta2HatPoles`, which references them seventeen times — so relocating them re-elaborates and
re-receipts the whole hat chain.  That is its own landing, and A→B ≡ B→A: nothing here has to
change when it happens.  What this file does NOT do is make a second copy of any of them.

**Elaborate with the corpus oleans on the path** — it imports `Zeta2HatPoles`:

    sh external_tests/zeta2_arith/run_probe.sh Zeta2HatRepOf.lean

Without `LEAN_PATH` pointing at the probes directory the import fails, the run TRUNCATES, and NO
`#print axioms` line is printed at all — which is not a green.  The receipt predicate's third arm
(`tools/lean_falsifier_restore.py audit-probe`, "asked for and Lean printed no footprint") is what
refuses that; a `grep -c sorryAx` would return 0 and read clean.

**Receipts** `out_axioms_hatrepof.txt`; falsifier arm `B1` in `falsify_hatreps.sh` →
`out_hatreps_falsify.txt` (the degree margin relaxed from `<` to `≤`, which must RED).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic
import Zeta2HatPoles

namespace Zeta2HatRepOf

open Polynomial Finset Zeta2HatRep

/-! ## The nodes, and the cofactors in INDEX vocabulary

`Zeta2HatPoles.pf1_eq`/`pf2_eq` are the same two facts with the member's own sets baked in; these
are their generic twins, and they reuse that file's four node helpers rather than re-proving them. -/

/-- The poles `t = −k` of an index set, as the `Finset ℚ` `Zeta2PF.partialFractions_res` consumes. -/
noncomputable def nodes (S : Finset ℕ) : Finset ℚ := S.image (fun k : ℕ => -((k : ℕ) : ℚ))

theorem card_nodes (S : Finset ℕ) : (nodes S).card = S.card := by
  rw [nodes, Finset.card_image_of_injective _ Zeta2HatPoles.neg_cast_inj]

theorem nodes_disjoint {S1 S2 : Finset ℕ} (h : Disjoint S1 S2) :
    Disjoint (nodes S1) (nodes S2) := by
  classical
  rw [nodes, nodes, Finset.disjoint_left]
  rintro a ha hb
  simp only [Finset.mem_image] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, hxy⟩ := hb
  have : y = x := Zeta2HatPoles.neg_cast_inj hxy
  subst this
  exact (Finset.disjoint_left.1 h) hx hy

theorem sum_nodes (S : Finset ℕ) (g : ℚ → ℚ) :
    ∑ x ∈ nodes S, g x = ∑ κ ∈ S, g (-((κ : ℕ) : ℚ)) := by
  classical
  rw [nodes]
  exact Finset.sum_image (fun x _ y _ h => Zeta2HatPoles.neg_cast_inj h)

theorem pf1_eq (S1 S2 : Finset ℕ) (κ : ℕ) :
    Zeta2PF.pf1 (nodes S1) (nodes S2) (-((κ : ℕ) : ℚ))
      = (∏ j ∈ S1.erase κ, (X + C ((j : ℕ) : ℚ)))
        * (∏ j ∈ S2, (X + C ((j : ℕ) : ℚ))) ^ 2 := by
  classical
  rw [Zeta2PF.pf1, nodes, nodes, Zeta2HatPoles.image_erase_comm,
    Zeta2HatPoles.poly_prod_image, Zeta2HatPoles.poly_prod_image_sq]

theorem pf2_eq (S1 S2 : Finset ℕ) (κ : ℕ) :
    Zeta2PF.pf2 (nodes S1) (nodes S2) (-((κ : ℕ) : ℚ))
      = (∏ j ∈ S1, (X + C ((j : ℕ) : ℚ)))
        * (∏ j ∈ S2.erase κ, (X + C ((j : ℕ) : ℚ))) ^ 2 := by
  classical
  rw [Zeta2PF.pf2, nodes, nodes, Zeta2HatPoles.image_erase_comm,
    Zeta2HatPoles.poly_prod_image, Zeta2HatPoles.poly_prod_image_sq]

/-! ## `repOf` — the `Rep̂` whose coefficients ARE `partialFractions_res`'s solved residues -/

open scoped Classical in
noncomputable def repOfB (S1 S2 : Finset ℕ) (N : ℚ[X]) : ℕ →₀ ℚ :=
  Finsupp.onFinset (S1 ∪ S2)
    (fun k => if k ∈ S1 ∪ S2 then Zeta2PF.resB (nodes S1) (nodes S2) N (-((k : ℕ) : ℚ)) else 0)
    (by intro a ha; by_contra hn; rw [ite_eq_right hn] at ha; exact ha rfl)

open scoped Classical in
noncomputable def repOfA (S1 S2 : Finset ℕ) (N : ℚ[X]) : ℕ →₀ ℚ :=
  Finsupp.onFinset S2
    (fun k => if k ∈ S2 then Zeta2PF.resA (nodes S1) (nodes S2) N (-((k : ℕ) : ℚ)) else 0)
    (by intro a ha; by_contra hn; rw [ite_eq_right hn] at ha; exact ha rfl)

/-- **The generic `repS`.**  A consumer supplies its own two index sets and its own numerator;
nothing about the numerator's shape is asked for anywhere below. -/
noncomputable def repOf (S1 S2 : Finset ℕ) (N : ℚ[X]) : Rephat :=
  (repOfB S1 S2 N, repOfA S1 S2 N)

theorem repOfB_support (S1 S2 : Finset ℕ) (N : ℚ[X]) :
    (repOfB S1 S2 N).support ⊆ S1 ∪ S2 := Finsupp.support_onFinset_subset

theorem repOfA_support (S1 S2 : Finset ℕ) (N : ℚ[X]) :
    (repOfA S1 S2 N).support ⊆ S2 := Finsupp.support_onFinset_subset

theorem repOfB_apply (S1 S2 : Finset ℕ) (N : ℚ[X]) {κ : ℕ} (hκ : κ ∈ S1 ∪ S2) :
    repOfB S1 S2 N κ = Zeta2PF.resB (nodes S1) (nodes S2) N (-((κ : ℕ) : ℚ)) := by
  classical
  rw [repOfB, Finsupp.onFinset_apply, ite_eq_left hκ]

theorem repOfA_apply (S1 S2 : Finset ℕ) (N : ℚ[X]) {κ : ℕ} (hκ : κ ∈ S2) :
    repOfA S1 S2 N κ = Zeta2PF.resA (nodes S1) (nodes S2) N (-((κ : ℕ) : ℚ)) := by
  classical
  rw [repOfA, Finsupp.onFinset_apply, ite_eq_left hκ]

theorem evalRep_repOf_eq (S1 S2 : Finset ℕ) (N : ℚ[X]) (t : ℚ) :
    evalRep (repOf S1 S2 N) t
      = (∑ κ ∈ S1 ∪ S2, repOfB S1 S2 N κ / (t + ((κ : ℕ) : ℚ)))
        + ∑ κ ∈ S2, repOfA S1 S2 N κ / (t + ((κ : ℕ) : ℚ)) ^ 2 := by
  classical
  show (repOfB S1 S2 N).sum (fun k b => b / (t + ((k : ℕ) : ℚ)))
      + (repOfA S1 S2 N).sum (fun k a => a / (t + ((k : ℕ) : ℚ)) ^ 2) = _
  rw [Finsupp.sum_of_support_subset _ (repOfB_support S1 S2 N) _ (fun i _ => by simp),
    Finsupp.sum_of_support_subset _ (repOfA_support S1 S2 N) _ (fun i _ => by simp)]

/-! ## The theorem: `repOf` represents `N / W`, off the poles -/

open scoped Classical in
/-- **The generic representation lemma.**  `repOf S₁ S₂ N` evaluates to `N / W` at every `t` that
is not a pole, where `W = ∏_{S₁}(t+k) · (∏_{S₂}(t+k))²`.  Its ONLY hypotheses are disjointness,
the degree bound, and non-vanishing at `t` — all statements about the INDEX SETS and the DEGREE,
none about `N`'s shape.  That is what makes it usable at `Ŝ`, whose residues have no closed form.

The proof is `Zeta2HatPoles.hat_rep_of_residues`'s, with the residues SOLVED FOR instead of
supplied — which is why the two files do not share a lemma but do share a shape. -/
theorem evalRep_repOf (S1 S2 : Finset ℕ) (hdisj : Disjoint S1 S2) (N : ℚ[X])
    (hdeg : N.natDegree < S1.card + 2 * S2.card)
    (t : ℚ) (ht : ∀ k ∈ S1 ∪ S2, t + ((k : ℕ) : ℚ) ≠ 0) :
    evalRep (repOf S1 S2 N) t
      = N.eval t / ((∏ k ∈ S1, (t + ((k : ℕ) : ℚ))) * (∏ k ∈ S2, (t + ((k : ℕ) : ℚ))) ^ 2) := by
  classical
  have hnd : Disjoint (nodes S1) (nodes S2) := nodes_disjoint hdisj
  have hdeg' : N.natDegree < (nodes S1).card + 2 * (nodes S2).card := by
    rwa [card_nodes, card_nodes]
  have key := Zeta2PF.partialFractions_res (nodes S1) (nodes S2) hnd N hdeg'
  have hne1 : ∀ κ ∈ S1, t + ((κ : ℕ) : ℚ) ≠ 0 := fun κ hκ => ht κ (Finset.mem_union_left _ hκ)
  have hne2 : ∀ κ ∈ S2, t + ((κ : ℕ) : ℚ) ≠ 0 := fun κ hκ => ht κ (Finset.mem_union_right _ hκ)
  set P1 : ℚ := ∏ κ ∈ S1, (t + ((κ : ℕ) : ℚ)) with hP1
  set P2 : ℚ := ∏ κ ∈ S2, (t + ((κ : ℕ) : ℚ)) with hP2
  have hP1ne : P1 ≠ 0 := Finset.prod_ne_zero_iff.2 hne1
  have hP2ne : P2 ≠ 0 := Finset.prod_ne_zero_iff.2 hne2
  have hWne : P1 * P2 ^ 2 ≠ 0 := mul_ne_zero hP1ne (pow_ne_zero _ hP2ne)
  -- the cofactor values at a general `t`
  have hE1 : ∀ κ ∈ S1, (Zeta2PF.pf1 (nodes S1) (nodes S2) (-((κ : ℕ) : ℚ))).eval t
      = (∏ j ∈ S1.erase κ, (t + ((j : ℕ) : ℚ))) * P2 ^ 2 := by
    intro κ _
    rw [pf1_eq, eval_mul, eval_pow, eval_prod, eval_prod, hP2]
    simp
  have hE2 : ∀ κ ∈ S2, (Zeta2PF.pf2 (nodes S1) (nodes S2) (-((κ : ℕ) : ℚ))).eval t
      = P1 * (∏ j ∈ S2.erase κ, (t + ((j : ℕ) : ℚ))) ^ 2 := by
    intro κ _
    rw [pf2_eq, eval_mul, eval_pow, eval_prod, eval_prod, hP1]
    simp
  have hD1 : ∀ κ ∈ S1, P1 * P2 ^ 2
      = (t + ((κ : ℕ) : ℚ)) * ((∏ j ∈ S1.erase κ, (t + ((j : ℕ) : ℚ))) * P2 ^ 2) := by
    intro κ hκ
    rw [hP1, ← Finset.mul_prod_erase _ _ hκ]
    ring
  have hD2 : ∀ κ ∈ S2, P1 * P2 ^ 2
      = (t + ((κ : ℕ) : ℚ)) ^ 2 * (P1 * (∏ j ∈ S2.erase κ, (t + ((j : ℕ) : ℚ))) ^ 2) := by
    intro κ hκ
    rw [hP2, ← Finset.mul_prod_erase _ _ hκ]
    ring
  have hev := congrArg (fun p : ℚ[X] => p.eval t) key
  simp only [eval_add, eval_mul, eval_C, eval_finsetSum, eval_sub, eval_X] at hev
  rw [sum_nodes, sum_nodes] at hev
  have hmain : evalRep (repOf S1 S2 N) t * (P1 * P2 ^ 2) = N.eval t := by
    rw [evalRep_repOf_eq, Finset.sum_union hdisj, add_mul, add_mul, Finset.sum_mul,
      Finset.sum_mul, Finset.sum_mul, add_assoc, hev]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun κ hκ => ?_
      have hκne : t + ((κ : ℕ) : ℚ) ≠ 0 := hne1 κ hκ
      rw [hD1 κ hκ, hE1 κ hκ, repOfB_apply S1 S2 N (Finset.mem_union_left _ hκ)]
      field_simp
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun κ hκ => ?_
      have hκne : t + ((κ : ℕ) : ℚ) ≠ 0 := hne2 κ hκ
      rw [hD2 κ hκ, hE2 κ hκ, repOfB_apply S1 S2 N (Finset.mem_union_right _ hκ),
        repOfA_apply S1 S2 N hκ]
      field_simp
      ring
  rw [eq_div_iff hWne]
  exact hmain

end Zeta2HatRepOf

#print axioms Zeta2HatRepOf.card_nodes
#print axioms Zeta2HatRepOf.nodes_disjoint
#print axioms Zeta2HatRepOf.pf1_eq
#print axioms Zeta2HatRepOf.pf2_eq
#print axioms Zeta2HatRepOf.repOfB_apply
#print axioms Zeta2HatRepOf.repOfA_apply
#print axioms Zeta2HatRepOf.evalRep_repOf_eq
#print axioms Zeta2HatRepOf.evalRep_repOf
