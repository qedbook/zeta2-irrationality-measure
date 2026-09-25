/-
# Row PAIR-5 — `Ŝ`'s WRITTEN denominator, regrouped: the four raw runs, the degrees, the strip zeros

`docs/future/zeta2-lean-chain.md` row PAIR-5, §PAIR-5 design notes attempt 5.

**What the row owed that this file pays, and the reason it is smaller than the row thought.**
Attempts 3 and 4 read PAIR-5 as needing `Ŝ`'s poles **in lowest terms** — `T₁ ∪ T₂`,
`deg W = 19n+114`, which is what the exact-ℚ probe computes and what `Zeta2HatCancel` states — and
the residual was written down as obligation **(b), the TRANSFER**: that `Ŝ`'s `Finset.prod`s of
affine factors really have the valuations `Zeta2HatCancel.ord` computes.  **Nothing asks for lowest
terms.**  `Zeta2PF.partialFractions_res` takes the pole sets as GIVEN and SOLVES for the residues,
so a pole the numerator kills simply gets residue `0`, unproved and unmentioned — exactly as
PAIR-4R's own `Zeta2HatPoles.hatDen` is written and not reduced (`hat_res_cancelled` on `[7n+1, 9n]`
is the same phenomenon one row earlier).  So the route is: **take `Ŝ`'s written denominator,
regroup it, and stop.**  Obligation (b) is deleted from the row rather than discharged.

**The regrouping.**  `Ŝ`'s written denominator is the member's two runs times `D`'s two integer runs

    A = [7n+1, 18n+1]   B = [9n+1, 20n+1]   C = [18n+2, 18n+55]   D = [20n+2, 20n+61]

whose overlap STRUCTURE is `n`-dependent (`B ∩ C` and `C ∩ D` change shape around `n = 26`) while
their multiplicity function is NOT — which is the fact the whole route turns on:

    S₂ (double)  [9n+1, 18n+55]                     9n+55
    S₁ (simple)  [7n+1, 9n] ∪ [18n+56, 20n+61]      4n+6
    max multiplicity 2 at every n — no triple pole, so `partialFractions_res` applies
    |S₁| + 2|S₂| = 22n+116 = deg denS, counted the other way round

`den_multiset` is that identity as a multiset count, closed by `split_ifs <;> omega` — the same
shape as `Zeta2HatCancel.ord_eq` but over the four DENOMINATOR runs only, so nothing it says has to
be transferred to a polynomial afterwards.  Cross-checked offline over 154,880 `(n, k)` pairs,
`n = 0..120`, by `external_tests/zeta2_star_b1/hat_raw_route_probe.py` §A, which also measures the
containment arm (every raw pole lies in `[7n+1, 20n+61]`).  That probe is what decides whether the
theorems below are the INTENDED ones: a falsifier arm shows the PROOF breaks, and only an
evaluation shows the STATEMENT is false.

**ONE cancellation is not optional and it is the only one.**  `D`'s lead-2 block `(2t + 3n + b)`,
`b ∈ [2,10]` — `D`'s only `lead = 2` entries in the landed FACSYM — has HALF-INTEGER roots, and
`Rep̂`'s keys are ℕ.  It is cancelled against the member's own `(2t+l)` run, leaving `numS`'s run
starting at `3n+11`.  That single `Finset.Icc` split is `Zeta2HatShatForm.hatNum_split`.

**And that split is where the row's `2 ≤ n` comes from.**  After it, `Ŝ(−4n−1/2) = 0` needs its
factor `(2t + 8n+1)` to be inside `[3n+11, 20n+1]`: `3n+11 ≤ 8n+1 ⟺ 5n ≥ 10 ⟺ 2 ≤ n`.  That is
attempt 2's measured threshold (`D`'s block contains `8n+1` iff `5n ≤ 9`) reached from the other
side — a fourth independent derivation of one number.  `numS_eval_belt0` is where it binds, and arm
`R1` of the falsifier weakens it to `1 ≤ n` and reds.

**What this file does NOT do.**  It does not mention `Ŝ`: `numS`/`denS` are polynomials in their own
right and `bh`, `xh` are OPAQUE, carrying only `natDegree ≤ 5` and `≤ 120`.  That `numS/denS` IS
`Ŝ` is `Zeta2HatShatForm.shat_eq`, and the `Rep̂` built from these sets is `Zeta2HatRepS`.  It also
does not claim these pole sets are REDUCED — they are deliberately not, and `partialFractions_res`
does not care.  `partialFractions_at_S` below EXECUTES the composition (LEAN.md §3) rather than
asserting it: if the pole sets were the wrong shape for the generic lemma, that line would not
typecheck.

**The degree-120 certificate never enters a proof.**  The design's one measured blocker on the
earlier route was `x̂`, an unfactored degree-120 coefficient list.  Everything below asks of it only
`natDegree ≤ 120` — `Zeta2HatShatForm.natDegree_coeffs_le` discharges that for ANY 121-coefficient
family — so the object that priced the route out is not in the route.

**Elaborate with the corpus oleans on the path** — it imports `Zeta2HatRepOf` (hence
`Zeta2HatPoles`):

    sh external_tests/zeta2_arith/run_probe.sh Zeta2HatRawPoles.lean

Without `LEAN_PATH` pointing at the probes directory the import fails, the run TRUNCATES, and NO
`#print axioms` line is printed at all — which is not a green; the receipt predicate's third arm is
what refuses that, where a `grep -c sorryAx` would return 0 and read clean.

**Receipts** `out_axioms_hatrawpoles.txt`; falsifier arms `R1`–`R7` in `falsify_hatreps.sh` →
`out_hatreps_falsify.txt`, seven RED with a GREEN control at each end of the block (the trailing
one checks the restore by ELABORATION rather than by `cmp`) and a byte-identical restore.  Two of
them are about BINDERS rather than about numbers, because attempt 4 measured that a hypothesis
doing nothing silently narrows what a suite can reach: `R6` empties `numS_natDegree_le`'s `1 ≤ n`
to a tautology and `R7` REMOVES `numS_eval_belt1`'s outright.  Both RED, so both binders are
load-bearing and neither is decoration.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic
import Zeta2HatRepOf

namespace Zeta2HatRawPoles

open Polynomial Finset

/-! ## 1. The pole index sets, straight off the WRITTEN denominator -/

/-- The SIMPLE raw poles. -/
def idxS1 (n : ℕ) : Finset ℕ := Icc (7 * n + 1) (9 * n) ∪ Icc (18 * n + 56) (20 * n + 61)

/-- The DOUBLE raw poles. -/
def idxS2 (n : ℕ) : Finset ℕ := Icc (9 * n + 1) (18 * n + 55)

theorem count_val (s : Finset ℕ) (k : ℕ) :
    Multiset.count k s.val = if k ∈ s then 1 else 0 := by
  classical
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem s.nodup h
  · exact Multiset.count_eq_zero.mpr h

/-- **The regrouping, at the DENOMINATOR only.**  The four written runs, as a multiset of indices,
are `S₁ + S₂ + S₂`.  Every endpoint is integer-linear in `n`, so this is the `split_ifs <;> omega`
shape `Zeta2HatCancel.ord_eq` is — but with no numerator run in it, so nothing here has to be
transferred to `rootMultiplicity` later.  That difference is the whole of why this route is cheap
and the reduced one was not. -/
theorem den_multiset (n : ℕ) :
    (Icc (7 * n + 1) (18 * n + 1)).val + (Icc (9 * n + 1) (20 * n + 1)).val
        + ((Icc (18 * n + 2) (18 * n + 55)).val + (Icc (20 * n + 2) (20 * n + 61)).val)
      = (idxS1 n).val + ((idxS2 n).val + (idxS2 n).val) := by
  classical
  refine Multiset.ext.2 fun k => ?_
  simp only [Multiset.count_add, count_val, idxS1, idxS2, Finset.mem_union, Finset.mem_Icc]
  split_ifs <;> omega

/-- `Ŝ`'s WRITTEN denominator: `hatMember`'s two runs, then `D`'s two integer runs.
`D`'s lead-2 block `(2t+3n+b)`, `b ∈ [2,10]`, is NOT here — it is cancelled against the member's
own `(2t+l)` run, which is the one cancellation this route needs and the only one it cannot avoid
(`Rep̂`'s keys are ℕ, and that block's roots are half-integers). -/
noncomputable def denS (n : ℕ) : ℚ[X] :=
  (∏ l ∈ Icc (7 * n + 1) (18 * n + 1), (X + C (l : ℚ)))
      * (∏ l ∈ Icc (9 * n + 1) (20 * n + 1), (X + C (l : ℚ)))
    * ((∏ l ∈ Icc (18 * n + 2) (18 * n + 55), (X + C (l : ℚ)))
      * ∏ l ∈ Icc (20 * n + 2) (20 * n + 61), (X + C (l : ℚ)))

theorem denS_eq (n : ℕ) :
    denS n = (∏ l ∈ idxS1 n, (X + C (l : ℚ)))
      * ((∏ l ∈ idxS2 n, (X + C (l : ℚ))) * ∏ l ∈ idxS2 n, (X + C (l : ℚ))) := by
  classical
  have h := congrArg (fun m : Multiset ℕ => (m.map (fun l : ℕ => (X + C (l : ℚ)))).prod)
    (den_multiset n)
  rw [denS]
  simpa only [Multiset.map_add, Multiset.prod_add, ← Finset.prod_eq_multiset_prod] using h

/-! ## 2. Degrees and cardinalities — the same number from two directions -/

theorem monic_run (s : Finset ℕ) : (∏ l ∈ s, (X + C (l : ℚ))).Monic :=
  monic_prod_of_monic _ _ fun _l _ => monic_X_add_C _

theorem natDegree_run (s : Finset ℕ) : (∏ l ∈ s, (X + C (l : ℚ))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ fun l _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]

theorem denS_monic (n : ℕ) : (denS n).Monic := by
  rw [denS_eq]
  exact (monic_run _).mul ((monic_run _).mul (monic_run _))

theorem idxS1_runs_disjoint (n : ℕ) :
    Disjoint (Icc (7 * n + 1) (9 * n)) (Icc (18 * n + 56) (20 * n + 61)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_Icc] at ha hb
  omega

theorem card_idxS1 (n : ℕ) : (idxS1 n).card = 4 * n + 6 := by
  rw [idxS1, Finset.card_union_of_disjoint (idxS1_runs_disjoint n), Nat.card_Icc, Nat.card_Icc]
  omega

theorem card_idxS2 (n : ℕ) : (idxS2 n).card = 9 * n + 55 := by
  rw [idxS2, Nat.card_Icc]
  omega

theorem idxS1_disjoint_idxS2 (n : ℕ) : Disjoint (idxS1 n) (idxS2 n) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [idxS1, idxS2, Finset.mem_union, Finset.mem_Icc] at ha hb
  omega

/-- **`deg denS = 22n+116` — and `|S₁| + 2|S₂|` is the same number** (`card_sum` below).  Two
independent routes to one integer: the degree counts the four written runs, the cardinality counts
the regrouped two.  They agree, which is the arithmetic check on the regrouping that no falsifier
arm has to supply. -/
theorem denS_natDegree (n : ℕ) : (denS n).natDegree = 22 * n + 116 := by
  rw [denS_eq, (monic_run _).natDegree_mul ((monic_run _).mul (monic_run _)),
    (monic_run _).natDegree_mul (monic_run _)]
  simp only [natDegree_run, card_idxS1, card_idxS2]
  omega

theorem card_sum (n : ℕ) : (idxS1 n).card + 2 * (idxS2 n).card = 22 * n + 116 := by
  rw [card_idxS1, card_idxS2]; omega

/-! ## 3. The nodes `t = −k`, in `partialFractions_res`'s vocabulary

`Zeta2HatRepOf.nodes` is the generic translation and these are its two instances; there is no
second `Finset.image` and no second injectivity proof here. -/

noncomputable def poleS1 (n : ℕ) : Finset ℚ := Zeta2HatRepOf.nodes (idxS1 n)

noncomputable def poleS2 (n : ℕ) : Finset ℚ := Zeta2HatRepOf.nodes (idxS2 n)

theorem card_poleS1 (n : ℕ) : (poleS1 n).card = 4 * n + 6 := by
  rw [poleS1, Zeta2HatRepOf.card_nodes, card_idxS1]

theorem card_poleS2 (n : ℕ) : (poleS2 n).card = 9 * n + 55 := by
  rw [poleS2, Zeta2HatRepOf.card_nodes, card_idxS2]

theorem poles_disjoint (n : ℕ) : Disjoint (poleS1 n) (poleS2 n) :=
  Zeta2HatRepOf.nodes_disjoint (idxS1_disjoint_idxS2 n)

/-! ## 4. The numerator, with `b̂` and `x̂` OPAQUE

The design never asks anything of `x̂` beyond its degree bound, so the degree-120 unfactored
certificate — attempt 3's "genuinely unpriced" object — never enters a proof at all. -/

noncomputable def numS (n : ℕ) (bh xh : ℚ[X]) : ℚ[X] :=
  bh * xh * (∏ l ∈ Icc (3 * n + 11) (20 * n + 1), (C (2 : ℚ) * X + C (l : ℚ)))
    * ∏ l ∈ Icc 1 (5 * n), (X + C (l : ℚ))

theorem natDegree_run2_le (s : Finset ℕ) :
    (∏ l ∈ s, (C (2 : ℚ) * X + C (l : ℚ))).natDegree ≤ s.card := by
  refine le_trans (natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : ℕ => 1) (fun l _ => ?_)) (by simp)
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans (natDegree_C_mul_le _ _) (le_of_eq natDegree_X)
  · simp

/-- `1 ≤ n` is load-bearing and arm `R6` is how that was checked rather than assumed: at `n = 0`
both affine runs are EMPTY, so the bound would read `125 ≤ 116`. -/
theorem numS_natDegree_le (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X])
    (hb : bh.natDegree ≤ 5) (hx : xh.natDegree ≤ 120) :
    (numS n bh xh).natDegree ≤ 22 * n + 116 := by
  have h1 : (bh * xh).natDegree ≤ 125 := le_trans natDegree_mul_le (by omega)
  have h2 := natDegree_run2_le (Icc (3 * n + 11) (20 * n + 1))
  have h3 := natDegree_run (Icc 1 (5 * n))
  rw [Nat.card_Icc] at h2
  rw [Nat.card_Icc] at h3
  have h4 : (bh * xh * ∏ l ∈ Icc (3 * n + 11) (20 * n + 1),
      (C (2 : ℚ) * X + C (l : ℚ))).natDegree ≤ 125 + (20 * n + 1 + 1 - (3 * n + 11)) :=
    le_trans natDegree_mul_le (by omega)
  refine le_trans (natDegree_mul_le) ?_
  rw [h3]
  omega

/-! ## 5. The degree drop — the `C₀` subtraction, with nothing about `C₀`'s value

`Ŝ` is NOT PROPER (`deg num = deg den`, measured by attempt 3), so no `Rep̂` represents it and the
object that gets a representation is `Ŝ − C₀`.  `C₀` is `numS`'s top coefficient because `denS` is
MONIC — no division anywhere, and the VALUE of `C₀` is never used. -/

theorem natDegree_sub_lead_lt {p q : ℚ[X]} {d : ℕ} (hd : 0 < d) (hp : p.natDegree ≤ d)
    (hq : q.Monic) (hqd : q.natDegree = d) :
    (p - C (p.coeff d) * q).natDegree < d := by
  set r := p - C (p.coeff d) * q with hr
  have hle : r.natDegree ≤ d := by
    refine le_trans (natDegree_sub_le _ _) (max_le hp ?_)
    exact le_trans (natDegree_C_mul_le _ _) (le_of_eq hqd)
  have hcq : q.coeff d = 1 := by
    have := hq.coeff_natDegree
    rwa [hqd] at this
  have hc : r.coeff d = 0 := by
    rw [hr, coeff_sub, coeff_C_mul, hcq, mul_one, sub_self]
  rcases eq_or_lt_of_le hle with heq | hlt
  · exfalso
    have : r.leadingCoeff = 0 := by rw [leadingCoeff, heq, hc]
    rw [leadingCoeff_eq_zero] at this
    rw [this] at heq
    simp at heq
    omega
  · exact hlt

/-- **The `partialFractions_res` hypothesis package, complete.** -/
theorem hdeg (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X])
    (hb : bh.natDegree ≤ 5) (hx : xh.natDegree ≤ 120) :
    (numS n bh xh - C ((numS n bh xh).coeff (22 * n + 116)) * denS n).natDegree
      < (poleS1 n).card + 2 * (poleS2 n).card := by
  rw [card_poleS1, card_poleS2]
  have := natDegree_sub_lead_lt (p := numS n bh xh) (q := denS n) (d := 22 * n + 116)
    (by omega) (numS_natDegree_le n hn bh xh hb hx) (denS_monic n) (denS_natDegree n)
  omega

/-- **The composition, EXECUTED** (LEAN.md §3): if the pole sets were the wrong shape, this would
not typecheck. -/
theorem partialFractions_at_S (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X])
    (hb : bh.natDegree ≤ 5) (hx : xh.natDegree ≤ 120) :
    (numS n bh xh - C ((numS n bh xh).coeff (22 * n + 116)) * denS n)
      = (∑ k ∈ poleS1 n, C (Zeta2PF.resB (poleS1 n) (poleS2 n)
              (numS n bh xh - C ((numS n bh xh).coeff (22 * n + 116)) * denS n) k)
            * Zeta2PF.pf1 (poleS1 n) (poleS2 n) k)
        + ∑ k ∈ poleS2 n,
            (C (Zeta2PF.resB (poleS1 n) (poleS2 n)
                  (numS n bh xh - C ((numS n bh xh).coeff (22 * n + 116)) * denS n) k)
                * ((X - C k) * Zeta2PF.pf2 (poleS1 n) (poleS2 n) k)
              + C (Zeta2PF.resA (poleS1 n) (poleS2 n)
                  (numS n bh xh - C ((numS n bh xh).coeff (22 * n + 116)) * denS n) k)
                * Zeta2PF.pf2 (poleS1 n) (poleS2 n) k) :=
  Zeta2PF.partialFractions_res (poleS1 n) (poleS2 n) (poles_disjoint n) _ (hdeg n hn bh xh hb hx)

/-! ## 6. The two strip zeros, and the two non-pole facts -/

/-- `Ŝ(−4n) = 0`: the member's own `(t+l)` run carries `l = 4n`.  `1 ≤ n` is where it binds, and
arm `R7` REMOVES this binder and reds — at `n = 0` the run `[1, 0]` is empty. -/
theorem numS_eval_belt1 (n : ℕ) (hn : 1 ≤ n) (bh xh : ℚ[X]) :
    (numS n bh xh).eval (-(4 * (n : ℚ))) = 0 := by
  rw [numS, eval_mul]
  refine mul_eq_zero_of_right _ ?_
  rw [eval_prod]
  refine Finset.prod_eq_zero (i := 4 * n) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) ?_
  simp only [eval_add, eval_X, eval_C]
  push_cast
  ring

/-- **`Ŝ(−4n−1/2) = 0`, and this is exactly where the row's `2 ≤ n` comes from.**  The zero is the
member's `(2t + 8n+1)`, and it survives only above the run bottom `3n+11` that `D`'s cancelled
lead-2 block left behind: `3n+11 ≤ 8n+1 ⟺ 2 ≤ n`.  The same inequality attempt 2 measured from the
other side as `5n ≤ 9`. -/
theorem numS_eval_belt0 (n : ℕ) (hn : 2 ≤ n) (bh xh : ℚ[X]) :
    (numS n bh xh).eval (-(4 * (n : ℚ)) - 1 / 2) = 0 := by
  rw [numS, eval_mul]
  refine mul_eq_zero_of_left ?_ _
  rw [eval_mul]
  refine mul_eq_zero_of_right _ ?_
  rw [eval_prod]
  refine Finset.prod_eq_zero (i := 8 * n + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) ?_
  simp only [eval_add, eval_mul, eval_X, eval_C]
  push_cast
  ring

/-- `−4n` is not a pole: every raw pole index is `≥ 7n+1 > 4n`. -/
theorem belt1_not_pole (n k : ℕ) (hk : k ∈ idxS1 n ∪ idxS2 n) :
    -(4 * (n : ℚ)) + (k : ℚ) ≠ 0 := by
  simp only [idxS1, idxS2, Finset.mem_union, Finset.mem_Icc] at hk
  have hlt : 4 * n < k := by omega
  intro h
  have : (k : ℚ) = 4 * (n : ℚ) := by linarith
  have : (k : ℕ) = 4 * n := by exact_mod_cast this
  omega

/-- `−4n−1/2` is not a pole for a reason independent of `n`: `Rep̂`'s poles are at INTEGERS, and
`2k = 8n+1` has no solution. -/
theorem belt0_not_pole (n k : ℕ) : -(4 * (n : ℚ)) - 1 / 2 + (k : ℚ) ≠ 0 := by
  intro h
  have h2 : (2 * k : ℚ) = (8 * n + 1 : ℚ) := by linarith
  have h3 : (2 * k : ℕ) = 8 * n + 1 := by exact_mod_cast h2
  omega

end Zeta2HatRawPoles

#print axioms Zeta2HatRawPoles.den_multiset
#print axioms Zeta2HatRawPoles.denS_eq
#print axioms Zeta2HatRawPoles.denS_monic
#print axioms Zeta2HatRawPoles.denS_natDegree
#print axioms Zeta2HatRawPoles.card_idxS1
#print axioms Zeta2HatRawPoles.card_idxS2
#print axioms Zeta2HatRawPoles.card_sum
#print axioms Zeta2HatRawPoles.poles_disjoint
#print axioms Zeta2HatRawPoles.numS_natDegree_le
#print axioms Zeta2HatRawPoles.natDegree_sub_lead_lt
#print axioms Zeta2HatRawPoles.hdeg
#print axioms Zeta2HatRawPoles.partialFractions_at_S
#print axioms Zeta2HatRawPoles.numS_eval_belt1
#print axioms Zeta2HatRawPoles.numS_eval_belt0
#print axioms Zeta2HatRawPoles.belt1_not_pole
#print axioms Zeta2HatRawPoles.belt0_not_pole
