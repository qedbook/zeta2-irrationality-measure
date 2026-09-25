/-
# Row RESID — `ck` ARE the residues of `numPoly / denPoly`

`docs/future/zeta2-lean-chain.md` row RESID, §RESID design notes.

`Zeta2Defs` defines `ck` by the §1.1 factorial closed form and `Ppol` by polynomial division,
and — the scope audit's §2.9 — **not one of its theorems relates the two**.  `ck`'s docstring
says "the residue of `R_n` at the simple pole `t = −k`" and nothing proves it.  Three rows wait
on that sentence becoming a theorem (PHI-EVAL, PNCLR/PT-P, L7ID), so this file proves it:

    numPoly n %ₘ denPoly n = Σ_{k ∈ window n} C (ck n k) · ∏_{j ∈ window n \ {k}} (X + C j)

The generic half is already landed — `Zeta2PF.partialFractions_simple` and its reindexed form
`Zeta2PF.partialFractions_nodes` (`Zeta2PartialFractions.lean`), the partial-fraction lemma
Mathlib does not have.  What is left, and what this file is, is the member-specific part:

  (i)   the `%ₘ` bridge — at a pole the remainder agrees with the numerator, from
        `Zeta2Defs.Member.Ppol_spec` and `denPoly_monic`;
  (ii)  the reindex — `window n` is a `Finset ℕ` and the poles sit at `t = −k`, against the
        generic lemma's `Finset ℚ` of nodes and its `X − C k` factors (the SIGN convention);
  (iii) the residue evaluation — `numPoly.eval (−k) = ck n k · ∏_{j≠k} (j − k)`, the §1.1
        closed form, out of the `Zeta2PE` product atoms.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2PartialFractions
import Zeta2ProdEval

namespace Zeta2Resid

open Zeta2Defs Polynomial Finset Nat

set_option profiler true
set_option profiler.threshold 100

/-! ## `block` as a product over its NODES

`Zeta2Defs.block` is indexed by `Finset.range len` with the node read off as `c + i`.  Every
statement below is about the NODES themselves — which pole, which factor — so the first act is
to re-index it onto the `Icc` of its nodes.  `1 ≤ c` is what makes the empty case agree: at
`len = 0` the interval is `Icc c (c−1)`, and at `c = 0` ℕ-subtraction would make that `Icc 0 0`,
a singleton, so the lemma would be FALSE (LEAN.md §5 — the edge case is checked, not assumed). -/

theorem block_eq_prod_Icc (c len : ℕ) (hc : 1 ≤ c) :
    block c len = ∏ j ∈ Finset.Icc c (c + len - 1), (X + C ((j : ℕ) : ℚ)) := by
  induction len with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega : ¬ c ≤ c + 0 - 1)]
    simp [block]
  | succ len ih =>
    have hsplit : block c (len + 1) = block c len * (X + C ((c + len : ℕ) : ℚ)) := by
      rw [block, block, Finset.prod_range_succ]
    have hidx : c + (len + 1) - 1 = (c + len - 1) + 1 := by omega
    have htop : (c + len - 1) + 1 = c + len := by omega
    rw [hsplit, ih, hidx, Finset.prod_Icc_succ_top (by omega : c ≤ (c + len - 1) + 1), htop]

/-- The denominator is exactly the product over the pole window — the statement `window` was
written to make true, and the one every pole argument below starts from. -/
theorem denPoly_eq_prod_window (m : Member) (hm : m.WF) (n : ℕ) :
    m.denPoly n = ∏ j ∈ m.window n, (X + C ((j : ℕ) : ℚ)) := by
  have hle : m.a4 * n ≤ m.b4 * n := Nat.mul_le_mul_right _ hm.a4_lt.le
  have hsub : (m.b4 - m.a4) * n = m.b4 * n - m.a4 * n := Nat.sub_mul _ _ _
  have hidx : m.a4 * n + 1 + ((m.b4 - m.a4) * n + 1) - 1 = m.b4 * n + 1 := by omega
  rw [Member.denPoly, block_eq_prod_Icc _ _ (by omega), hidx, Member.window]

/-! ## (i) The `%ₘ` bridge -/

/-- **At a pole the remainder agrees with the numerator.**  `num = (num %ₘ den) + den · Ppol`
(`Ppol_spec`, which says something only because `denPoly` is MONIC) and `den` vanishes at
`t = −k` for every `k` in the window. -/
theorem modByMonic_eval_neg (m : Member) (hm : m.WF) (n k : ℕ) (hk : k ∈ m.window n) :
    (m.numPoly n %ₘ m.denPoly n).eval (-(k : ℚ)) = (m.numPoly n).eval (-(k : ℚ)) := by
  have hden : (m.denPoly n).eval (-(k : ℚ)) = 0 := by
    rw [denPoly_eq_prod_window m hm n, eval_prod]
    exact Finset.prod_eq_zero hk (by simp)
  have h := congrArg (fun p : ℚ[X] => p.eval (-(k : ℚ))) (m.Ppol_spec n)
  simp only [eval_add, eval_mul, hden, zero_mul, add_zero] at h
  exact h

/-- The degree side of the generic lemma's hypothesis: the remainder has smaller degree than
the number of poles.  The `%ₘ`-remainder can be `0`, whose `natDegree` is `0` rather than `⊥`,
so the zero case is discharged separately rather than by `natDegree_lt_natDegree`. -/
theorem natDegree_modByMonic_lt_card (m : Member) (hm : m.WF) (n : ℕ) :
    (m.numPoly n %ₘ m.denPoly n).natDegree < (m.window n).card := by
  rw [m.window_card hm n]
  rcases eq_or_ne (m.numPoly n %ₘ m.denPoly n) 0 with h | h
  · rw [h]
    simp
  · have hlt : (m.numPoly n %ₘ m.denPoly n).degree < (m.denPoly n).degree :=
      degree_modByMonic_lt _ (m.denPoly_monic n)
    have hnd := natDegree_lt_natDegree h hlt
    rwa [m.denPoly_natDegree n] at hnd

/-! ## (ii) The reindex — RESID modulo the residue evaluation

This is the composition executed (LEAN.md §3): the generic lemma is instantiated at the member's
own objects, with the node map `j ↦ −j` and its closed-form left inverse.  What is left over is
exactly one statement about factorials, which (iii) supplies. -/

/-- **RESID, modulo the residue evaluation.**  Everything structural is discharged here; the
hypothesis is the §1.1 closed form evaluated at a pole and nothing else. -/
theorem partial_fractions_of_residues (m : Member) (hm : m.WF) (n : ℕ)
    (hres : ∀ k ∈ m.window n, (m.numPoly n).eval (-(k : ℚ))
      = m.ck n k * ∏ j ∈ (m.window n).erase k, ((j : ℚ) - (k : ℚ))) :
    m.numPoly n %ₘ m.denPoly n
      = ∑ k ∈ m.window n, C (m.ck n k) * ∏ j ∈ (m.window n).erase k, (X + C ((j : ℕ) : ℚ)) := by
  have hw : ∀ k ∈ m.window n, (-(-((k : ℕ) : ℚ))).num.toNat = k := by
    intro k _
    simp
  have hev : ∀ k ∈ m.window n,
      (m.numPoly n %ₘ m.denPoly n).eval (-((k : ℕ) : ℚ))
        = m.ck n k * ∏ j ∈ (m.window n).erase k, (-((k : ℕ) : ℚ) - -((j : ℕ) : ℚ)) := by
    intro k hk
    rw [modByMonic_eval_neg m hm n k hk, hres k hk]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by ring
  have key := Zeta2PF.partialFractions_nodes (m.window n) (fun j : ℕ => -((j : ℕ) : ℚ))
    (fun x : ℚ => (-x).num.toNat) hw (m.numPoly n %ₘ m.denPoly n) (fun k => m.ck n k)
    (natDegree_modByMonic_lt_card m hm n) hev
  rw [key]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [map_neg, sub_neg_eq_add]

/-! ## (iii) The residue evaluation — the §1.1 closed form AT a pole

Three products, all of them instances of the `Zeta2PE` atoms: the numerator's three Pochhammer
blocks, and the window product `∏_{j≠k}(j−k)` that the residue is divided by.  Everything is
stated MULTIPLICATIVELY (`… * (…)! = …`) so no nonvanishing side condition travels; the single
division is cancelled once, at the end. -/

/-- `block c len` at the pole `t = −k`, cleared.  `c + len ≤ k` says the pole lies strictly to
the right of the block, which is what makes every factor negative and the reflection exact. -/
theorem block_eval_neg (c len k : ℕ) (hc : 1 ≤ c) (hk : c + len ≤ k) :
    (block c len).eval (-(k : ℚ)) * (((k - c - len)! : ℕ) : ℚ)
      = (-1) ^ len * (((k - c)! : ℕ) : ℚ) := by
  rw [block_eq_prod_Icc c len hc, eval_prod]
  rw [Finset.prod_congr rfl (fun j _ => by simp only [eval_add, eval_X, eval_C]; ring :
    ∀ j ∈ Finset.Icc c (c + len - 1),
      eval (-(k : ℚ)) (X + C ((j : ℕ) : ℚ)) = ((j : ℚ) - (k : ℚ)))]
  rcases Nat.eq_zero_or_pos len with rfl | hlen
  · rw [Finset.Icc_eq_empty (by omega)]
    simp
  · rw [Zeta2PE.prod_Icc_sub_rev k c (c + len - 1)]
    have hexp : (c + len - 1) + 1 - c = len := by omega
    have hatom := Zeta2PE.prod_Icc_sub_cast k c (c + len - 1) (by omega) (by omega)
    have hidx : k - (c + len - 1) - 1 = k - c - len := by omega
    rw [hidx] at hatom
    rw [hexp, mul_assoc, hatom]

/-- The numerator at a pole, cleared by the three denominator factorials of `ckAbs` that it
does NOT share with the window product. -/
theorem numPoly_eval_neg_cleared (m : Member) (hm : m.WF) (n k : ℕ) (hk : k ∈ m.window n) :
    (m.numPoly n).eval (-(k : ℚ))
        * (((k - m.a1 * n - 1)! * (k - m.a2 * n - 1)! * (k - m.a3 * n - 1)! : ℕ) : ℚ)
      = (-1) ^ (m.a1 * n + (m.a2 - m.b2) * n + (m.a3 - m.b3) * n)
        * (((k - 1)! * (k - m.b2 * n - 1)! * (k - m.b3 * n - 1)! : ℕ) : ℚ) := by
  rw [Member.window, Finset.mem_Icc] at hk
  have h1 : m.a1 * n ≤ m.a4 * n := Nat.mul_le_mul_right _ hm.a1_le
  have h2 : m.a2 * n ≤ m.a4 * n := Nat.mul_le_mul_right _ hm.a2_le
  have h3 : m.a3 * n ≤ m.a4 * n := Nat.mul_le_mul_right _ hm.a3_le
  have h4 : m.b2 * n ≤ m.a2 * n := Nat.mul_le_mul_right _ hm.b2_lt.le
  have h5 : m.b3 * n ≤ m.a3 * n := Nat.mul_le_mul_right _ hm.b3_lt.le
  have s2 : (m.a2 - m.b2) * n = m.a2 * n - m.b2 * n := Nat.sub_mul _ _ _
  have s3 : (m.a3 - m.b3) * n = m.a3 * n - m.b3 * n := Nat.sub_mul _ _ _
  have B1 : (block 1 (m.a1 * n)).eval (-(k : ℚ)) * (((k - m.a1 * n - 1)! : ℕ) : ℚ)
      = (-1) ^ (m.a1 * n) * (((k - 1)! : ℕ) : ℚ) := by
    have h := block_eval_neg 1 (m.a1 * n) k (le_refl 1) (by omega)
    have e : k - 1 - m.a1 * n = k - m.a1 * n - 1 := by omega
    rwa [e] at h
  have B2 : (block (m.b2 * n + 1) ((m.a2 - m.b2) * n)).eval (-(k : ℚ))
        * (((k - m.a2 * n - 1)! : ℕ) : ℚ)
      = (-1) ^ ((m.a2 - m.b2) * n) * (((k - m.b2 * n - 1)! : ℕ) : ℚ) := by
    have h := block_eval_neg (m.b2 * n + 1) ((m.a2 - m.b2) * n) k (by omega) (by omega)
    have e : k - (m.b2 * n + 1) - (m.a2 - m.b2) * n = k - m.a2 * n - 1 := by omega
    have e' : k - (m.b2 * n + 1) = k - m.b2 * n - 1 := by omega
    rwa [e, e'] at h
  have B3 : (block (m.b3 * n + 1) ((m.a3 - m.b3) * n)).eval (-(k : ℚ))
        * (((k - m.a3 * n - 1)! : ℕ) : ℚ)
      = (-1) ^ ((m.a3 - m.b3) * n) * (((k - m.b3 * n - 1)! : ℕ) : ℚ) := by
    have h := block_eval_neg (m.b3 * n + 1) ((m.a3 - m.b3) * n) k (by omega) (by omega)
    have e : k - (m.b3 * n + 1) - (m.a3 - m.b3) * n = k - m.a3 * n - 1 := by omega
    have e' : k - (m.b3 * n + 1) = k - m.b3 * n - 1 := by omega
    rwa [e, e'] at h
  have hnum : (m.numPoly n).eval (-(k : ℚ))
      = (block 1 (m.a1 * n)).eval (-(k : ℚ))
        * (block (m.b2 * n + 1) ((m.a2 - m.b2) * n)).eval (-(k : ℚ))
        * (block (m.b3 * n + 1) ((m.a3 - m.b3) * n)).eval (-(k : ℚ)) := by
    rw [Member.numPoly, eval_mul, eval_mul]
  rw [hnum]
  push_cast
  calc (block 1 (m.a1 * n)).eval (-(k : ℚ))
        * (block (m.b2 * n + 1) ((m.a2 - m.b2) * n)).eval (-(k : ℚ))
        * (block (m.b3 * n + 1) ((m.a3 - m.b3) * n)).eval (-(k : ℚ))
        * ((((k - m.a1 * n - 1)! : ℕ) : ℚ) * (((k - m.a2 * n - 1)! : ℕ) : ℚ)
          * (((k - m.a3 * n - 1)! : ℕ) : ℚ))
      = ((block 1 (m.a1 * n)).eval (-(k : ℚ)) * (((k - m.a1 * n - 1)! : ℕ) : ℚ))
        * ((block (m.b2 * n + 1) ((m.a2 - m.b2) * n)).eval (-(k : ℚ))
            * (((k - m.a2 * n - 1)! : ℕ) : ℚ))
        * ((block (m.b3 * n + 1) ((m.a3 - m.b3) * n)).eval (-(k : ℚ))
            * (((k - m.a3 * n - 1)! : ℕ) : ℚ)) := by ring
    _ = ((-1 : ℚ)) ^ (m.a1 * n + (m.a2 - m.b2) * n + (m.a3 - m.b3) * n)
        * ((((k - 1)! : ℕ) : ℚ) * (((k - m.b2 * n - 1)! : ℕ) : ℚ)
          * (((k - m.b3 * n - 1)! : ℕ) : ℚ)) := by
        rw [B1, B2, B3, pow_add, pow_add]
        ring

/-! ### The window product `∏_{j≠k}(j−k)`

The split of a run of consecutive integers AT one of its own members is generic, and PAIR-4R's
pole table is four such runs, so the three atoms it needs live in `Zeta2ProdEval.lean` beside
the family they belong to (`Zeta2PE.prod_Icc_shift` / `prod_Icc_lt_sub` / `prod_Icc_gt_sub`)
rather than here. What is member-specific is only which run, and that is below. -/

/-- **The window product.**  `∏_{j ∈ window \ {k}} (j − k)` is `(−1)^(k−α₄n−1)` times the two
factorials `ckAbs` carries in its denominator and nothing else carries.

No `WF` hypothesis: the window's own bounds are all this needs, and Lean's unused-variable
linter said so on the first draft.  Carrying it would tell a caller this proved something
narrower than it did (the same call the `Zeta2PE` atoms make). -/
theorem prod_window_erase (m : Member) (n k : ℕ) (hk : k ∈ m.window n) :
    ∏ j ∈ (m.window n).erase k, ((j : ℚ) - (k : ℚ))
      = (-1) ^ (k - m.a4 * n - 1)
        * (((k - m.a4 * n - 1)! * (m.b4 * n + 1 - k)! : ℕ) : ℚ) := by
  have hkm := hk
  rw [Member.window, Finset.mem_Icc] at hkm
  have hsplit : (m.window n).erase k
      = Finset.Icc (m.a4 * n + 1) (k - 1) ∪ Finset.Icc (k + 1) (m.b4 * n + 1) := by
    ext x
    rw [Member.window]
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc (m.a4 * n + 1) (k - 1))
      (Finset.Icc (k + 1) (m.b4 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  rw [hsplit, Finset.prod_union hdisj,
    Zeta2PE.prod_Icc_lt_sub (m.a4 * n + 1) k (by omega) (by omega),
    Zeta2PE.prod_Icc_gt_sub k (m.b4 * n + 1) (by omega)]
  have e : k - (m.a4 * n + 1) = k - m.a4 * n - 1 := by omega
  rw [e]
  push_cast
  ring

/-- **The residue evaluation.**  `numPoly.eval (−k) = ck n k · ∏_{j≠k}(j−k)` — the sentence
`ck`'s docstring asserts, as a theorem.  The sign is where this could have been silently wrong:
the closed form's `(−1)^{Dn+k−1}` and the window product's `(−1)^{k−α₄n−1}` differ from the
numerator's `(−1)^{(α₁+(α₂−β₂)+(α₃−β₃))n}` by `2(k−α₄n−1)`, i.e. by nothing. -/
theorem numPoly_eval_neg (m : Member) (hm : m.WF) (n k : ℕ) (hk : k ∈ m.window n) :
    (m.numPoly n).eval (-(k : ℚ))
      = m.ck n k * ∏ j ∈ (m.window n).erase k, ((j : ℚ) - (k : ℚ)) := by
  have hkm := hk
  rw [Member.window, Finset.mem_Icc] at hkm
  have hDpar : m.Dpar + m.a4 = m.a1 + (m.a2 - m.b2) + (m.a3 - m.b3) := by
    rw [Member.Dpar]
    have := hm.a4_le_deg
    omega
  have hD : m.Dpar * n + m.a4 * n
      = m.a1 * n + (m.a2 - m.b2) * n + (m.a3 - m.b3) * n := by
    rw [← Nat.add_mul, hDpar, Nat.add_mul, Nat.add_mul]
  have hsign : ((-1 : ℚ)) ^ (m.Dpar * n + k - 1) * ((-1 : ℚ)) ^ (k - m.a4 * n - 1)
      = ((-1 : ℚ)) ^ (m.a1 * n + (m.a2 - m.b2) * n + (m.a3 - m.b3) * n) := by
    rw [← pow_add]
    have he : (m.Dpar * n + k - 1) + (k - m.a4 * n - 1)
        = (m.a1 * n + (m.a2 - m.b2) * n + (m.a3 - m.b3) * n) + 2 * (k - m.a4 * n - 1) := by
      omega
    rw [he, pow_add, pow_mul]
    norm_num
  have f1 : (((k - m.a1 * n - 1)! : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f2 : (((k - m.a2 * n - 1)! : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f3 : (((k - m.a3 * n - 1)! : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f4 : (((k - m.a4 * n - 1)! : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f5 : (((m.b4 * n + 1 - k)! : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hPne : (((k - m.a1 * n - 1)! * (k - m.a2 * n - 1)! * (k - m.a3 * n - 1)! : ℕ) : ℚ) ≠ 0 := by
    push_cast
    exact mul_ne_zero (mul_ne_zero f1 f2) f3
  refine mul_right_cancel₀ hPne ?_
  rw [numPoly_eval_neg_cleared m hm n k hk, prod_window_erase m n k hk,
    Member.ck, Member.ckAbs, ← hsign]
  push_cast
  -- `field_simp` closes this outright; a trailing `ring` would error with "No goals"
  -- (LEAN.md §8 — read the error, do not cargo-cult the pair).
  field_simp

/-! ## RESID — the row's theorem -/

/-- **RESID.**  `ck` ARE the residues: the remainder of `numPoly` by the monic `denPoly` is the
sum of the principal parts over the pole window, with `ck n k` the coefficient at `t = −k`.
Stated for EVERY well-formed member and every `n`; the candidate and the record follow. -/
theorem Ppol_partial_fractions (m : Member) (hm : m.WF) (n : ℕ) :
    m.numPoly n %ₘ m.denPoly n
      = ∑ k ∈ m.window n, C (m.ck n k) * ∏ j ∈ (m.window n).erase k, (X + C ((j : ℕ) : ℚ)) :=
  partial_fractions_of_residues m hm n fun k hk => numPoly_eval_neg m hm n k hk

/-- The candidate's instance — the member the μ ≤ 5.0495243 bound is about. -/
theorem candidate_partial_fractions (n : ℕ) :
    candidateM.numPoly n %ₘ candidateM.denPoly n
      = ∑ k ∈ candidateM.window n,
          C (candidateM.ck n k) * ∏ j ∈ (candidateM.window n).erase k, (X + C ((j : ℕ) : ℚ)) :=
  Ppol_partial_fractions candidateM candidateM_wf n

/-- The RECORD at `n = 1` — the row's named smallest instance, seven simple poles.  It is a
specialisation and not a separate proof, which is the point: the reindex composed at SYMBOLIC
`n`, which is strictly stronger than composing at one instance. -/
theorem record_window_one_card : (recordM.window 1).card = 7 := by decide

theorem record_partial_fractions_one :
    recordM.numPoly 1 %ₘ recordM.denPoly 1
      = ∑ k ∈ recordM.window 1,
          C (recordM.ck 1 k) * ∏ j ∈ (recordM.window 1).erase k, (X + C ((j : ℕ) : ℚ)) :=
  Ppol_partial_fractions recordM recordM_wf 1

/-- The candidate at `n = 0`, where the window is the single pole `k = 1` and `c₁ = 1`
(`Zeta2Defs.Member.ck_zero`): the whole remainder is the constant `1`. -/
theorem candidate_partial_fractions_zero :
    candidateM.numPoly 0 %ₘ candidateM.denPoly 0 = 1 := by
  have h := candidate_partial_fractions 0
  rw [Member.window_zero] at h
  simpa [Member.ck_zero] using h

/-! ## The evaluated form — what the ANALYTIC consumers meet

PHI-EVAL and L7ID do not meet a `Polynomial ℚ` identity; they meet `R_n(t)/Π` as a function.
The polynomial form above is the primary statement because it carries NO side condition and
composes directly with `Ppol_spec`; this corollary is its evaluated shape, stated with the
hypothesis the callers produce — `t` off the poles, quantified over the window, the same shape
row PAIR-4R fixed for the hat (LEAN.md §3). -/

theorem member_eq_Ppol_add_residues (m : Member) (hm : m.WF) (n : ℕ) (t : ℚ)
    (ht : ∀ k ∈ m.window n, t + (k : ℚ) ≠ 0) :
    (m.numPoly n).eval t / (m.denPoly n).eval t
      = (m.Ppol n).eval t + ∑ k ∈ m.window n, m.ck n k / (t + (k : ℚ)) := by
  have hden : (m.denPoly n).eval t = ∏ k ∈ m.window n, (t + (k : ℚ)) := by
    rw [denPoly_eq_prod_window m hm n, eval_prod]
    exact Finset.prod_congr rfl fun j _ => by simp
  have hdne : (m.denPoly n).eval t ≠ 0 := by
    rw [hden]
    exact Finset.prod_ne_zero_iff.2 ht
  have hrem : (m.numPoly n %ₘ m.denPoly n).eval t / (m.denPoly n).eval t
      = ∑ k ∈ m.window n, m.ck n k / (t + (k : ℚ)) := by
    rw [Ppol_partial_fractions m hm n, eval_finsetSum, hden, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hEne : (∏ j ∈ (m.window n).erase k, (t + (j : ℚ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => ht j (Finset.mem_of_mem_erase hj)
    have hkne : t + (k : ℚ) ≠ 0 := ht k hk
    rw [eval_mul, eval_C, eval_prod,
      Finset.prod_congr rfl (fun j _ => by simp :
        ∀ j ∈ (m.window n).erase k, eval t (X + C ((j : ℕ) : ℚ)) = t + (j : ℚ)),
      ← Finset.mul_prod_erase _ _ hk]
    field_simp
  have hspec := congrArg (fun p : ℚ[X] => p.eval t) (m.Ppol_spec n)
  simp only [eval_add, eval_mul] at hspec
  rw [← hspec, add_div, mul_comm ((m.denPoly n).eval t), mul_div_assoc, div_self hdne, mul_one,
    hrem, add_comm]

end Zeta2Resid

#print axioms Zeta2Resid.block_eq_prod_Icc
#print axioms Zeta2Resid.denPoly_eq_prod_window
#print axioms Zeta2Resid.modByMonic_eval_neg
#print axioms Zeta2Resid.natDegree_modByMonic_lt_card
#print axioms Zeta2Resid.partial_fractions_of_residues
#print axioms Zeta2Resid.block_eval_neg
#print axioms Zeta2Resid.numPoly_eval_neg_cleared
#print axioms Zeta2Resid.prod_window_erase
#print axioms Zeta2Resid.numPoly_eval_neg
#print axioms Zeta2Resid.Ppol_partial_fractions
#print axioms Zeta2Resid.candidate_partial_fractions
#print axioms Zeta2Resid.record_partial_fractions_one
#print axioms Zeta2Resid.candidate_partial_fractions_zero
#print axioms Zeta2Resid.member_eq_Ppol_add_residues
