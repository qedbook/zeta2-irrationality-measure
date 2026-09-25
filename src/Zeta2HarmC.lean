/-
# Row PAIR-VAL — the harmonic half shared, so `pnHarm n` and `hatP n` are ONE kernel pass

`Zeta2Defs.harm s k = Σ_{i<k} 1/(i+1)^s` is recomputed FROM SCRATCH at every call site, and
both kernel-bearing evaluations of row PAIR-VAL call it `O(n)` times at indices of size `O(n)`:

* `Member.pnHarm n = Σ_{k ∈ window n} ck n k · harm 2 (harmIndex n k)` — `11n+1` terms whose
  indices run over `[11n, 22n]`, so ≈ `181 n²` rational additions where `22n` would do;
* `Zeta2Hat.hatP n` — `hatLam n j` alone calls `harm 1` EIGHT times at indices up to `33n`,
  for each of the `8n+1` double poles, and `altH s L` (the same prefix-sum shape with an
  alternating sign) is called at indices up to `32n` in all three sums: ≈ `1350 n²` additions
  where `97n` would do (`33n` for `harm 1`, plus `32n+2` for each of `altH 1` and `altH 2`).

This is the same sharing defect `Zeta2MomC.sum_momI` removed on the moment side — one list
hoisted out of the sum and indexed — and the second pass of row PAIR-VAL measured it as the
lever it did not take: `pnHarm_eq` and `hatP_engine` are together the larger half of every
cell's kernel work, and the base's top cell `n = 11` did not fit inside the owner's 30-minute
rule without it.

`sumList f j = [Σ_{i<0} f i, …, Σ_{i<j} f i]` is ONE object for both (`harm` and `altH` differ
only in `f`), built by the same explicit `Nat.rec` `Zeta2MomC.momList` uses and for the same
reason (`LEAN.md` §8): a structural definition the elaborator compiles through
`WellFounded.fix` does not reduce in the kernel at all, and the failure mode is a
`decide +kernel` that never returns rather than an error.  Unlike `momList`'s step, which folds
over the whole prefix, this one reads exactly the last entry — so the list costs `O(j)`
rational additions, and the `++`/`getD` traversal that remains is `O(j²)` LIST steps, which is
the trade this file is about.

The two consumer forms are `pnHarm_shared` and `hatP_shared`; each is a single `rw` at the head
of the generated cell's proof, and neither changes any statement the corpus already had.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Hat

namespace Zeta2HarmC

open Zeta2Defs Zeta2Hat Finset

/-! ## The prefix-sum evaluator

The two `List.getD` facts the prefix argument needs are `List.getD_append` and
`List.getD_append_right`, both in `Mathlib/Data/List/GetD.lean` with exactly the shape used
here (`Zeta2MomC` made the same census; `LEAN.md` §2). -/

/-- `sumList f j = [Σ_{i<0} f i, Σ_{i<1} f i, …, Σ_{i<j} f i]`, length `j+1`
(`sumList_length`, `sumList_getD`).  Explicit `Nat.rec`, not the equation compiler. -/
def sumList (f : ℕ → ℚ) (j : ℕ) : List ℚ :=
  Nat.rec (motive := fun _ => List ℚ) [0] (fun i prev => prev ++ [prev.getD i 0 + f i]) j

theorem sumList_zero (f : ℕ → ℚ) : sumList f 0 = [0] := rfl

theorem sumList_succ (f : ℕ → ℚ) (j : ℕ) :
    sumList f (j + 1) = sumList f j ++ [(sumList f j).getD j 0 + f j] := rfl

theorem sumList_length (f : ℕ → ℚ) : ∀ j, (sumList f j).length = j + 1
  | 0 => rfl
  | j + 1 => by
      rw [sumList_succ, List.length_append, sumList_length f j]
      rfl

/-- **The evaluator's contract**: entry `k` of `sumList f j` is the partial sum `Σ_{i<k} f i`,
for every `k ≤ j`.  The list is a PREFIX of every longer one, which is what makes one list
serve every index a consumer asks for. -/
theorem sumList_getD (f : ℕ → ℚ) :
    ∀ (j k : ℕ), k ≤ j → (sumList f j).getD k 0 = ∑ i ∈ range k, f i := by
  intro j
  induction j with
  | zero =>
      intro k h
      have hk : k = 0 := Nat.le_zero.1 h
      subst hk
      simp [sumList]
  | succ j ih =>
      intro k h
      have hlen := sumList_length f j
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | h'
      · rw [sumList_succ, List.getD_append _ _ _ _ (by rw [hlen]; omega)]
        exact ih k (Nat.lt_succ_iff.1 h')
      · subst h'
        rw [sumList_succ, List.getD_append_right _ _ _ _ hlen.le, hlen, Nat.sub_self,
          ih j le_rfl, Finset.sum_range_succ]
        simp

/-! ## The two instances the chain uses -/

/-- `harmList s N = [harm s 0, …, harm s N]` (`harm_eq_getD`). -/
def harmList (s N : ℕ) : List ℚ := sumList (fun i => 1 / ((i : ℚ) + 1) ^ s) N

/-- `altList s N = [altH s 0, …, altH s N]` (`altH_eq_getD`). -/
def altList (s N : ℕ) : List ℚ := sumList (fun d => (-1) ^ (d + 1) / ((d : ℚ) + 1) ^ s) N

/-- **The bridge for `harm`.**  One list serves every index up to `N`. -/
theorem harm_eq_getD (s N k : ℕ) (h : k ≤ N) : harm s k = (harmList s N).getD k 0 :=
  (sumList_getD _ N k h).symm

/-- **The bridge for `altH`.**  Same list, alternating summand. -/
theorem altH_eq_getD (s N L : ℕ) (h : L ≤ N) : altH s L = (altList s N).getD L 0 :=
  (sumList_getD _ N L h).symm

/-! ## Consumer 1 — `Member.pnHarm` -/

/-- The harmonic index stays inside `[0, (β₄−β₃)n]` on the pole window, which is the ONE bound
the shared list has to cover.  The `β₃ ≤ β₄` hypothesis is what makes both ℕ subtractions
genuine (`Member.WF`'s `b3_le`/`a4_lt` give it at both members). -/
theorem harmIndex_le (m : Member) (hb : m.b3 ≤ m.b4) (n k : ℕ) (hk : k ∈ m.window n) :
    m.harmIndex n k ≤ (m.b4 - m.b3) * n := by
  rw [Member.window, Finset.mem_Icc] at hk
  have hAB : m.b3 * n ≤ m.b4 * n := Nat.mul_le_mul hb (le_refl n)
  rw [Member.harmIndex, Nat.sub_mul]
  omega

/-- **The form `pnHarm`'s kernel evaluation rewrites with** — one `harmList 2 ((β₄−β₃)n)` under
the sum and indexed, instead of a `harm 2` recomputed at each of the `11n+1` window terms. -/
theorem pnHarm_shared (m : Member) (hb : m.b3 ≤ m.b4) (n : ℕ) :
    m.pnHarm n
      = ∑ k ∈ m.window n,
          m.ck n k * (harmList 2 ((m.b4 - m.b3) * n)).getD (m.harmIndex n k) 0 := by
  rw [Member.pnHarm]
  exact Finset.sum_congr rfl fun k hk => by
    rw [harm_eq_getD 2 _ _ (harmIndex_le m hb n k hk)]

/-! ## Consumer 2 — `Zeta2Hat.hatP`

`hatP` reads `harm 1` at indices `≤ 33n` (through `hatLam`) and `altH 1`/`altH 2` at indices
`≤ 32n` (the "hi" simple poles reach exactly `28n+2+2(2n−1) = 32n`), so three lists cover it. -/

/-- `H_m` read from the one `harm 1` prefix list of the cell. -/
def hH (n m : ℕ) : ℚ := (harmList 1 (33 * n)).getD m 0

/-- `A(L, s)` read from the one `altH s` prefix list of the cell. -/
def aA (s n L : ℕ) : ℚ := (altList s (32 * n + 2)).getD L 0

/-- `Λ_k` with its eight harmonic numbers read from one list — `Zeta2Hat.hatLam` verbatim,
`harm 1` replaced by `hH n`. -/
def hatLamS (n j : ℕ) : ℚ :=
  -2 * (hH n (17 * n + 2 * j) - hH n (2 * j)) - (hH n (10 * n + j) - hH n (5 * n + j))
    + (hH n (3 * n + j) - hH n (8 * n - j)) + (hH n (n + j) - hH n (10 * n - j))

/-- **The form `hatP`'s kernel pin rewrites with.**  Three lists, built once each. -/
theorem hatP_shared (n : ℕ) :
    hatP n
      = (∑ j ∈ range (8 * n + 1),
          (hatA n j : ℚ) * (hatLamS n j * aA 1 n (12 * n + 2 * j) + 2 * aA 2 n (12 * n + 2 * j)))
        + (∑ i ∈ range n, hatBlo n i * aA 1 n (10 * n + 2 * i))
        + (∑ i ∈ range (2 * n), hatBhi n i * aA 1 n (28 * n + 2 + 2 * i)) := by
  have h1 : ∀ j ∈ range (8 * n + 1),
      (hatA n j : ℚ) * (hatLam n j * altH 1 (12 * n + 2 * j) + 2 * altH 2 (12 * n + 2 * j))
        = (hatA n j : ℚ)
            * (hatLamS n j * aA 1 n (12 * n + 2 * j) + 2 * aA 2 n (12 * n + 2 * j)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hatLam, hatLamS, hH, hH, hH, hH, hH, hH, hH, hH, aA, aA,
      harm_eq_getD 1 (33 * n) (17 * n + 2 * j) (by omega),
      harm_eq_getD 1 (33 * n) (2 * j) (by omega),
      harm_eq_getD 1 (33 * n) (10 * n + j) (by omega),
      harm_eq_getD 1 (33 * n) (5 * n + j) (by omega),
      harm_eq_getD 1 (33 * n) (3 * n + j) (by omega),
      harm_eq_getD 1 (33 * n) (8 * n - j) (by omega),
      harm_eq_getD 1 (33 * n) (n + j) (by omega),
      harm_eq_getD 1 (33 * n) (10 * n - j) (by omega),
      altH_eq_getD 1 (32 * n + 2) (12 * n + 2 * j) (by omega),
      altH_eq_getD 2 (32 * n + 2) (12 * n + 2 * j) (by omega)]
  have h2 : ∀ i ∈ range n,
      hatBlo n i * altH 1 (10 * n + 2 * i) = hatBlo n i * aA 1 n (10 * n + 2 * i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [aA, altH_eq_getD 1 (32 * n + 2) (10 * n + 2 * i) (by omega)]
  have h3 : ∀ i ∈ range (2 * n),
      hatBhi n i * altH 1 (28 * n + 2 + 2 * i) = hatBhi n i * aA 1 n (28 * n + 2 + 2 * i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [aA, altH_eq_getD 1 (32 * n + 2) (28 * n + 2 + 2 * i) (by omega)]
  rw [hatP, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_congr rfl h3]

/-! ## Rung 0 — the shared route reproduces landed numbers, and can go red

`harm_control`/`altH_control` pin the two summands at a hand-checkable size; the two cell
controls are `Zeta2PairP1`'s OWN landed literals, reached through the new route, so a
`harmList` that was off by one, empty, or unreducible cannot pass this file.  (The literals
themselves are the generators' business: `gen_pn_lean.py` equates `pnHarm` with the tale-1
engine and `gen_hat_lean.py` equates `hatP` with three independent routes, each with
falsifier arms — `LEAN.md` §6.) -/

theorem harm_control : harm 2 5 = (5269 / 3600 : ℚ) := by decide +kernel

theorem harmList_control : (harmList 2 5).getD 5 0 = (5269 / 3600 : ℚ) := by decide +kernel

theorem altH_control : altH 1 4 = (-7 / 12 : ℚ) := by decide +kernel

theorem altList_control : (altList 1 4).getD 4 0 = (-7 / 12 : ℚ) := by decide +kernel

/-- `Zeta2PairP1.pnHarm_eq`'s literal, through the shared route. -/
theorem pnHarm_one_shared :
    candidateM.pnHarm 1 = (1410503664700665182226378240 / 13 : ℚ) := by
  rw [pnHarm_shared candidateM (by decide) 1]
  decide +kernel

/-- `Zeta2PairP1.hatP_engine`'s literal, through the shared route — and the exact tactic
script `gen_hat_lean.hatP_pin_lines` now renders at every cell. -/
theorem hatP_one_shared : hatP 1 = (-41381969327296379567 / 2535 : ℚ) := by
  rw [hatP_shared]
  simp only [hatA, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

end Zeta2HarmC

#print axioms Zeta2HarmC.sumList_length
#print axioms Zeta2HarmC.sumList_getD
#print axioms Zeta2HarmC.harm_eq_getD
#print axioms Zeta2HarmC.altH_eq_getD
#print axioms Zeta2HarmC.harmIndex_le
#print axioms Zeta2HarmC.pnHarm_shared
#print axioms Zeta2HarmC.hatP_shared
#print axioms Zeta2HarmC.harm_control
#print axioms Zeta2HarmC.harmList_control
#print axioms Zeta2HarmC.altH_control
#print axioms Zeta2HarmC.altList_control
#print axioms Zeta2HarmC.pnHarm_one_shared
#print axioms Zeta2HarmC.hatP_one_shared
