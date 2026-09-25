/-
# ROW L4-BR — CLOSED: `hα₃`, `hα₀`, `hrow`, `hM₀` (and `hN₁`) in the target's binder types

`docs/future/zeta2-lean-chain.md` row L4-BR.  Added 2026-09-18, under route B (owner-decided
2026-09-17, `docs/reference/answered_forks/`).

**HEADLINE: `Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.**  This file
closes row L4-BR (and THRESH, whose whole content is the two `le_refl`s below) and nothing
else: `Zeta2L12.candidate_target_of_certified_constants` still waits on the arithmetic half
`hΔne hQ hP` (PT-QB, PT-P), on `hdecay` (RDECAY, through L7ID) and on `hgrowth` (QGROW).

**What is proved.**  Under route B the recurrence `Zeta2L1Asm.hrecq`/`hrecp` is stated at
`αⱼ := Zeta2L1Asm.αR j`, i.e. `αⱼ n = (−1)^j · cⱼ(n)` cast to ℝ, with `cⱼ(n)` the sharded
(ii) modules' own `hornerZ c<j> n`.  There is NO quotient, so each guard is ONE nonvanishing —
and both are already landed as `Zeta2L4.c0_ne_zero` / `c3_ne_zero` (`∀ n : ℕ`, 17 receipts),
stated about `Zeta2L4.hornerZ` on `Zeta2L4.c0`/`c3`.  What separates them from the binders is
exactly what §1–§3 supply:

  * §1  the `List ℤ → ℝ[X]` bridge `ofList` with `eval_ofList`, `coeff_ofList` and
        `natDegree_ofList_le` — the row's (i), also what QGROW's `Pⱼ : ℝ[X]` reads;
  * §2  the TIES: `Zeta2StarIdIIJ{0,3}.hornerZ = Zeta2L4.hornerZ` (one list induction each)
        and `Zeta2StarIdIIJ3.c3 = Zeta2L4.c3`, `Zeta2StarIdIIJ0.c0 = Zeta2L4.c0` (one
        `decide +kernel` each — the J-modules restate the lists rather than import them);
  * §3  `P3 := ofList Zeta2L4.c3`, `P0 := ofList Zeta2L4.c0` with `αR 3 n = −P3.eval n`,
        `αR 0 n = P0.eval n`, their nonvanishing at EVERY `n : ℕ` and the shape facts
        `natDegree ≤ 510`, `coeff 510 = c<j>lead`;
  * §4  the binders — `hα₃`, `hα₀` (at `n₁ = m₀ = N0`, from the all-`n` forms), `hrow` (at
        `m₀ := N0 = 4`, `Zeta2L1Asm.qn_four_ne_zero`), `hM₀`, `hN₁` — and
        `target_of_arith_and_rates`: `candidate_target_of_certified_constants` APPLIED with
        them and with L1-ASM's `hrecq`/`hrecp`, so that the composition is executed
        (LEAN.md §3) and the target's 18 binders are down to the 11 that other rows owe
        (10 once HC2's landed `hc2` is counted).

**`m₀ := N₀ = 4`, and what that retires.**  The cell's `N₀ = 9` (and its 2026-09-13
correction to 6) are both above the landed threshold: `Zeta2L1Asm.N0 = 4`, PHI-BDY's floor.
`hrow` is therefore at `qn 4`, re-checked in the kernel by L1-ASM rather than transferred
(`qn_four_ne_zero`; `qn_six_ne_zero` is the cell's former number, also landed).  The audit's
§2.2 (`candidateM.qn 1127 ≠ 0`, UNSIZED) was never forced and is retired harder still: the
witness is `k = 4`.  `hrow_at_six` and `hrow_at_nine` record that the cell's `6` and its
original `9` work too (each one `decide +kernel`; the `qnInt 9` wall the cell left unmeasured
is seconds) — as controls and as the falsifier's wrong-`m₀` arms, never as inputs.

**Re-derived vs trusted.**  `Zeta2L4.lean` is IMPORTED here, so its `c0_ne_zero`/`c3_ne_zero`
are RE-ELABORATED when its olean is built (measured 1m19s–2m0s standalone), not taken from the
archived receipts.  `Zeta2L1Asm`'s theorems are read from its landed olean in `probes/l1asm`.

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2L4Br.lean

Receipts: `out_axioms_l4br.txt`.  Falsifier: `falsify_l4br.sh --lean`.  Read `lean`'s rc
SEPARATELY from the audit: the predicate scores a parse-broken file GREEN (found_bugs
2026-09-14).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2L4
import Zeta2L1Asm
import Zeta2L12

-- FILE-LEVEL on purpose: placed between a docstring and its theorem a `set_option` is a parse
-- error Lean silently RECOVERS from (zeta2-lean-chain.md, PAIR-7's and PAIR-6's landings).
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Zeta2L4Br

open Polynomial Zeta2Defs

/-! ## §1 — the bridge (i): `List ℤ → ℝ[X]`, ascending coefficients

`Zeta2L4` speaks about `List ℤ` through `hornerZ`; the chain's growth leg (`Zeta2XL1B`) speaks
about `ℝ[X]` through `eval`, `natDegree` and `coeff`.  `ofList` is the Horner form itself as a
polynomial, so `eval_ofList` is the same induction `hornerZ` is defined by. -/

/-- The polynomial `Σ cᵢ Xⁱ` of an ascending integer coefficient list, in Horner form. -/
noncomputable def ofList : List ℤ → ℝ[X]
  | [] => 0
  | c :: cs => C (c : ℝ) + X * ofList cs

/-- **`eval_ofList` at an integer point**: `(ofList c).eval x = hornerZ c x`, cast. -/
theorem eval_ofList_int : ∀ (c : List ℤ) (x : ℤ),
    (ofList c).eval (x : ℝ) = ((Zeta2L4.hornerZ c x : ℤ) : ℝ)
  | [], x => by simp [ofList, Zeta2L4.hornerZ]
  | a :: cs, x => by
    simp only [ofList, Zeta2L4.hornerZ, eval_add, eval_C, eval_mul, eval_X,
      eval_ofList_int cs x, Int.cast_add, Int.cast_mul]

/-- **The row's (i), in the cell's exact spelling**: at a natural `n`. -/
theorem eval_ofList (c : List ℤ) (n : ℕ) :
    (ofList c).eval (n : ℝ) = ((Zeta2L4.hornerZ c (n : ℤ) : ℤ) : ℝ) := by
  have h := eval_ofList_int c (n : ℤ)
  rwa [Int.cast_natCast] at h

/-- The coefficients of `ofList c` are the list's entries (zero past its end). -/
theorem coeff_ofList : ∀ (c : List ℤ) (k : ℕ), (ofList c).coeff k = ((c.getD k 0 : ℤ) : ℝ)
  | [], k => by simp [ofList]
  | a :: cs, 0 => by simp [ofList, coeff_add]
  | a :: cs, k + 1 => by
    rw [ofList, coeff_add, coeff_C_succ, coeff_X_mul, coeff_ofList cs k, List.getD_cons_succ,
      zero_add]

/-- `ofList c` has degree at most `c.length − 1` (an inequality: trailing zeros are allowed). -/
theorem natDegree_ofList_le (c : List ℤ) : (ofList c).natDegree ≤ c.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  simp

/-! ## §2 — the ties: the J-modules' restated `hornerZ` and lists ARE `Zeta2L4`'s

`Zeta2StarIdIIJ0`/`J3` import no `Zeta2L4`; each restates `hornerZ` and its list.  Their
headers say "byte-identical"; here the kernel says it. -/

theorem hornerZ_j3 : ∀ (L : List ℤ) (x : ℤ), Zeta2StarIdIIJ3.hornerZ L x = Zeta2L4.hornerZ L x
  | [], _ => rfl
  | c :: cs, x => by rw [Zeta2StarIdIIJ3.hornerZ, Zeta2L4.hornerZ, hornerZ_j3 cs x]

theorem hornerZ_j0 : ∀ (L : List ℤ) (x : ℤ), Zeta2StarIdIIJ0.hornerZ L x = Zeta2L4.hornerZ L x
  | [], _ => rfl
  | c :: cs, x => by rw [Zeta2StarIdIIJ0.hornerZ, Zeta2L4.hornerZ, hornerZ_j0 cs x]

/-- The 511-entry degree-510 list `c3` is the same list in both files. -/
theorem c3_tie : Zeta2StarIdIIJ3.c3 = Zeta2L4.c3 := by decide +kernel

/-- …and `c0`. -/
theorem c0_tie : Zeta2StarIdIIJ0.c0 = Zeta2L4.c0 := by decide +kernel

/-! ## §3 — `P₃`, `P₀` as real polynomials: the guards' objects, nonvanishing at every `n` -/

/-- `cleared₃` as a real polynomial. -/
noncomputable def P3 : ℝ[X] := ofList Zeta2L4.c3

/-- `cleared₀` as a real polynomial. -/
noncomputable def P0 : ℝ[X] := ofList Zeta2L4.c0

/-- **`α₃ n = −P₃(n)`**: L1-ASM's `'alt'` coefficient at `j = 3` is `(−1)³ · c₃(n)`. -/
theorem αR3_eq (n : ℕ) : Zeta2L1Asm.αR 3 n = -(P3.eval (n : ℝ)) := by
  show ((((-1 : ℚ) ^ 3
      * ((Zeta2StarIdIIJ3.hornerZ Zeta2StarIdIIJ3.c3 (n : ℤ) : ℤ) : ℚ)) : ℚ) : ℝ)
    = -(P3.eval (n : ℝ))
  rw [P3, eval_ofList, hornerZ_j3, c3_tie]
  push_cast
  ring

/-- **`α₀ n = P₀(n)`**: at `j = 0` the sign is `(−1)⁰ = 1`. -/
theorem αR0_eq (n : ℕ) : Zeta2L1Asm.αR 0 n = P0.eval (n : ℝ) := by
  show ((((-1 : ℚ) ^ 0
      * ((Zeta2StarIdIIJ0.hornerZ Zeta2StarIdIIJ0.c0 (n : ℤ) : ℤ) : ℚ)) : ℚ) : ℝ)
    = P0.eval (n : ℝ)
  rw [P0, eval_ofList, hornerZ_j0, c0_tie]
  push_cast
  ring

/-- **`P₃(n) ≠ 0` for EVERY natural `n`** — `Zeta2L4.c3_ne_zero` through the bridge.  This is
the explicit non-root theorem `Zeta2XL1B.candidate_rn_growth_of_recurrence_of_no_root` was
written for. -/
theorem P3_eval_ne_zero (n : ℕ) : P3.eval (n : ℝ) ≠ 0 := by
  rw [P3, eval_ofList]
  exact_mod_cast Zeta2L4.c3_ne_zero n

/-- **`P₀(n) ≠ 0` for EVERY natural `n`** — `Zeta2L4.c0_ne_zero` through the bridge. -/
theorem P0_eval_ne_zero (n : ℕ) : P0.eval (n : ℝ) ≠ 0 := by
  rw [P0, eval_ofList]
  exact_mod_cast Zeta2L4.c0_ne_zero n

/-- The shape facts `Zeta2XL1B` asks of `P₃`: degree at most `dcl = 510`… -/
theorem P3_natDegree_le : P3.natDegree ≤ 510 := by
  have h := natDegree_ofList_le Zeta2L4.c3
  rwa [Zeta2L4.c3_length] at h

/-- …and the leading coefficient is `c3lead` (`Zeta2XL1Data.lead3` is its twin literal). -/
theorem P3_coeff_510 : P3.coeff 510 = ((Zeta2L4.c3lead : ℤ) : ℝ) := by
  rw [P3, coeff_ofList]
  have h := Zeta2L4.a3_lead
  rw [Zeta2L4.a3] at h
  exact_mod_cast h

theorem P0_natDegree_le : P0.natDegree ≤ 510 := by
  have h := natDegree_ofList_le Zeta2L4.c0
  rwa [Zeta2L4.c0_length] at h

theorem P0_coeff_510 : P0.coeff 510 = ((Zeta2L4.c0lead : ℤ) : ℝ) := by
  rw [P0, coeff_ofList]
  have h := Zeta2L4.a0_lead
  rw [Zeta2L4.a0] at h
  exact_mod_cast h

/-! ## §4 — the binders, and the composition EXECUTED

`Zeta2L12.candidate_target_of_certified_constants` binds
`hN₁ : N₀ ≤ n₁`, `hM₀ : N₀ ≤ m₀`, `hα₃ : ∀ n, n₁ ≤ n → α₃ n ≠ 0`, `hα₀ : ∀ n, m₀ ≤ n → α₀ n ≠ 0`
and `hrow : ∃ k, m₀ ≤ k ∧ candidateM.qn k ≠ 0`, at the `N₀` and `αⱼ` of `hrecq`/`hrecp`.
Those are `Zeta2L1Asm.N0 = 4` and `Zeta2L1Asm.αR j`; `n₁ := m₀ := N0`. -/

/-- `α₃ n ≠ 0` at every `n` — stronger than the binder, which asks it from `n₁`. -/
theorem αR3_ne_zero (n : ℕ) : Zeta2L1Asm.αR 3 n ≠ 0 := by
  rw [αR3_eq]
  exact neg_ne_zero.mpr (P3_eval_ne_zero n)

/-- `α₀ n ≠ 0` at every `n`. -/
theorem αR0_ne_zero (n : ℕ) : Zeta2L1Asm.αR 0 n ≠ 0 := by
  rw [αR0_eq]
  exact P0_eval_ne_zero n

/-- **`hα₃`**, in the binder's type at `n₁ := N0`. -/
theorem hα₃ : ∀ n, Zeta2L1Asm.N0 ≤ n → Zeta2L1Asm.αR 3 n ≠ 0 :=
  fun n _ => αR3_ne_zero n

/-- **`hα₀`**, in the binder's type at `m₀ := N0`. -/
theorem hα₀ : ∀ n, Zeta2L1Asm.N0 ≤ n → Zeta2L1Asm.αR 0 n ≠ 0 :=
  fun n _ => αR0_ne_zero n

/-- **`hrow`** at `m₀ := N0 = 4`: the witness is `k = 4` itself, `qn 4 ≠ 0` in the kernel. -/
theorem hrow : ∃ k, Zeta2L1Asm.N0 ≤ k ∧ candidateM.qn k ≠ 0 :=
  ⟨Zeta2L1Asm.N0, le_refl _, Zeta2L1Asm.qn_four_ne_zero⟩

/-- **`hM₀`** — row THRESH's second `le_refl`, at `m₀ := N0`. -/
theorem hM₀ : Zeta2L1Asm.N0 ≤ Zeta2L1Asm.N0 := le_refl _

/-- **`hN₁`** — row THRESH's first `le_refl`, at `n₁ := N0`. -/
theorem hN₁ : Zeta2L1Asm.N0 ≤ Zeta2L1Asm.N0 := le_refl _

/-- The cell's former `m₀ = 6`, as a control: `hrow` holds there too (`qn_six_ne_zero`), and
`hM₀` becomes `4 ≤ 6` rather than `le_refl`.  Not consumed below. -/
theorem hrow_at_six : ∃ k, 6 ≤ k ∧ candidateM.qn k ≠ 0 :=
  ⟨6, le_refl _, Zeta2L1Asm.qn_six_ne_zero⟩

theorem hM₀_at_six : Zeta2L1Asm.N0 ≤ 6 := by decide

/-- The cell's ORIGINAL `m₀ = 9`, measured rather than assumed: `qn 9 ≠ 0` is one
`decide +kernel` on `qnInt 9` (100 `choose` terms), 4.29 s for the whole file including the
import at load 3.3 — the "kernel wall of `qnInt 9`" the cell left unmeasured is negligible.
Not consumed below; `falsify_l4br.sh` A1 hands `hrow_at_nine` to the composition in `hrow`'s
place and the assembly reds on the `m₀` mismatch. -/
theorem qn_nine_ne_zero : candidateM.qn 9 ≠ 0 := by
  rw [← Zeta2Arith.qnInt_cast]
  refine Int.cast_ne_zero.mpr ?_
  simp only [Zeta2Arith.qnInt, Zeta2Arith.cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

theorem hrow_at_nine : ∃ k, 9 ≤ k ∧ candidateM.qn k ≠ 0 :=
  ⟨9, le_refl _, qn_nine_ne_zero⟩

/--
**THE COMPOSITION, EXECUTED.**  `Zeta2L12.candidate_target_of_certified_constants` applied
with L1-ASM's recurrence half (`hrecq`, `hrecp` at `αⱼ := αR j`, `N₀ := N0`) and this row's
five binders.  Of the target's 18 hypotheses, 7 are discharged here by name — `hrecq hrecp
hN₁ hM₀ hα₃ hα₀ hrow` — and the `αⱼ`, `N₀`, `n₁`, `m₀` are no longer free.  The 11 that remain
are the certified-rate literals (`hc0 hc1 hc2 hδ`: HC1, HC2 — HC2 is landed as
`Zeta2Hc2.candidate_target_of_hc2`, not composed here to keep `Zeta2DPhi` off this file's
import path), the arithmetic half (`hΔne hQ hP`: PT-QB, PT-P), and the two rate legs
(`hCr hdecay`: RDECAY; `hCq hgrowth`: QGROW).  This theorem is what makes the binder claims
above checkable: a wrong `N₀`, `n₁` or `m₀` in any of them is a type error HERE.
-/
theorem target_of_arith_and_rates
    (Q P : ℕ → ℤ) (Δ : ℕ → ℝ) {Nr Nq : ℕ} {Cr Cq c0 c1 c2 δ : ℝ}
    (hc0 : (29.10787127 : ℝ) ≤ c0) (hc1 : c1 ≤ (42.03361581 : ℝ))
    (hc2 : c2 ≤ (15.01912095 : ℝ)) (hδ : δ ≤ 1 / 10 ^ 16)
    (hΔne : ∀ n, Δ n ≠ 0)
    (hQ : ∀ n, (Q n : ℝ) = Δ n * ((candidateM.qn n : ℚ) : ℝ))
    (hP : ∀ n, (P n : ℝ) = Δ n * ((candidateM.pn n : ℚ) : ℝ))
    (hCr : 0 < Cr)
    (hdecay : ∀ n, Nr ≤ n → |Δ n * candidateM.rn n| ≤ Cr * Real.exp (-(c0 - c2 - δ)) ^ n)
    (hCq : 0 < Cq)
    (hgrowth : ∀ n, Nq ≤ n → |(Q n : ℝ)| ≤ Cq * Real.exp (c1 + c2) ^ n) :
    ¬ LiouvilleWith (5.0495243 : ℝ) zeta2 :=
  Zeta2L12.candidate_target_of_certified_constants Q P Δ
    (Zeta2L1Asm.αR 0) (Zeta2L1Asm.αR 1) (Zeta2L1Asm.αR 2) (Zeta2L1Asm.αR 3)
    hc0 hc1 hc2 hδ Zeta2L1Asm.hrecq Zeta2L1Asm.hrecp hΔne hQ hP hN₁ hM₀ hα₃ hα₀ hrow
    hCr hdecay hCq hgrowth

/-! ## §5 — rung 0 (LEAN.md §5): the bridge is not vacuous and the guards bite -/

/-- The bridge sends the empty list to `0` and a singleton to a constant: `ofList` is the
Horner form and nothing else. -/
theorem ofList_nil : ofList [] = 0 := rfl

theorem ofList_singleton (a : ℤ) : ofList [a] = C (a : ℝ) := by
  simp [ofList]

/-- `P₃` is not the zero polynomial (a consequence of `P3_coeff_510` and `c3lead ≠ 0`; also of
`P3_eval_ne_zero 0`) — so `hα₃` is a statement about a genuine polynomial. -/
theorem P3_ne_zero : P3 ≠ 0 := by
  intro h
  exact P3_eval_ne_zero 0 (by rw [h, eval_zero])

theorem P0_ne_zero : P0 ≠ 0 := by
  intro h
  exact P0_eval_ne_zero 0 (by rw [h, eval_zero])

end Zeta2L4Br

/-! ## Receipts (LEAN.md §1 — exit 0 is not an attestation, and neither is a receipt alone) -/

#print axioms Zeta2L4Br.eval_ofList_int
#print axioms Zeta2L4Br.eval_ofList
#print axioms Zeta2L4Br.coeff_ofList
#print axioms Zeta2L4Br.natDegree_ofList_le
#print axioms Zeta2L4Br.hornerZ_j3
#print axioms Zeta2L4Br.hornerZ_j0
#print axioms Zeta2L4Br.c3_tie
#print axioms Zeta2L4Br.c0_tie
#print axioms Zeta2L4Br.αR3_eq
#print axioms Zeta2L4Br.αR0_eq
#print axioms Zeta2L4Br.P3_eval_ne_zero
#print axioms Zeta2L4Br.P0_eval_ne_zero
#print axioms Zeta2L4Br.P3_natDegree_le
#print axioms Zeta2L4Br.P3_coeff_510
#print axioms Zeta2L4Br.P0_natDegree_le
#print axioms Zeta2L4Br.P0_coeff_510
#print axioms Zeta2L4Br.αR3_ne_zero
#print axioms Zeta2L4Br.αR0_ne_zero
#print axioms Zeta2L4Br.hα₃
#print axioms Zeta2L4Br.hα₀
#print axioms Zeta2L4Br.hrow
#print axioms Zeta2L4Br.hM₀
#print axioms Zeta2L4Br.hN₁
#print axioms Zeta2L4Br.hrow_at_six
#print axioms Zeta2L4Br.hM₀_at_six
#print axioms Zeta2L4Br.qn_nine_ne_zero
#print axioms Zeta2L4Br.hrow_at_nine
#print axioms Zeta2L4Br.target_of_arith_and_rates
#print axioms Zeta2L4Br.ofList_nil
#print axioms Zeta2L4Br.ofList_singleton
#print axioms Zeta2L4Br.P3_ne_zero
#print axioms Zeta2L4Br.P0_ne_zero
