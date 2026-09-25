/-
# Row PAIR-6, the IDENTIFICATION half — `hρ_hat` and `hu_hat`, uniform in `j`

`docs/future/zeta2-lean-chain.md` row PAIR-6 (§PAIR-6 design notes, 2026-09-14).

**What this file pays.**  Refutation **R6** — *"`hatMember` is a transcription of the PAIR-0
Γ-spec and nothing ties it to the (★) family's `ρ j`, so a green PAIR-4R and a green PAIR-2 do
not compose"* — was REFUTED numerically on 2026-09-12 (`hat_star_id_probe.out`, 89/89).  What
that left the row was the same two facts **in Lean**, and they are the whole of `star_telescopes`'
`ρ` interface:

    hρ   hatMember (n+j) t · D_n(t) = hatMember n t · Pa_j(t)      (`rho_cross`, ∀ j ≤ 3, ∀ n, ∀ t)
    hu   u(t+1) · b(t)             = u(t) · a(t),  u = hatMember n / D_n   (`hu_cross`, ∀ n, ∀ t)

Both are stated CROSS-MULTIPLIED, so no division and no side condition appears here; dividing
through is `Zeta2Pair6`'s job, where the exceptional set is already in hand.

**Why it is short.**  The row's `[E] ~250–500 lines` was written against "123 individual factor
matches".  It is not: every object here is a product of AFFINE RUNS with bounds affine in `n`
(`prI` below), the engine emits `Pa_j` in exactly that run order, and both identities are then a
handful of `Finset.Icc` merges whose side conditions are `omega`.  The four 123-entry literal
lists are tied to their runs by one `decide +kernel` each (§3), so nothing here trusts a
transcription of the engine's data.

**What it does NOT do.**  It proves no new mathematics (net new arithmetic is zero), it says
nothing about `Σⱼ α̃ⱼ·hatQ(n+j) = 0` — that is `Zeta2Pair6` — and it does not close the chain.

**The run table is generated evidence, not a reading.**  `pair6_check.py` §3/§4 re-derives both
identities from `coords/starcoords_cand-t2.txt` in exact ℚ at generic rational `t`, with the
Π̂-exponent and `(−1)^j` convention seams as falsifier arms; `pair6_check.out` is its receipt.

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2Pair6Runs.lean

It imports the GENERATED `StarForallCandt2Base`, so that case carries the same manifest
prerequisite as `Zeta2HatStarBridge.lean` and REFUSES rather than skips.  Receipts:
`out_axioms_pair6runs.txt`.  Falsifier: `falsify_pair6.sh`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic
import Zeta2HatShatForm
import StarForallCandt2Base

namespace Zeta2Pair6Runs

open Polynomial Finset StarForallCandt2

/-! ## 1. `prI` — one affine run, the shape every object in this row is built from -/

/-- `∏_{l ∈ [a,b]} (u + l)`.  `u` is `t` or `2t`; the run bounds are affine in `n`. -/
noncomputable def prI (u : ℚ) (a b : ℕ) : ℚ := ∏ l ∈ Icc a b, (u + (l : ℚ))

theorem prI_split (u : ℚ) (a b c : ℕ) (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    prI u a c = prI u a b * prI u (b + 1) c := by
  classical
  have hsplit : Icc a c = Icc a b ∪ Icc (b + 1) c := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Icc a b) (Icc (b + 1) c) := by
    rw [Finset.disjoint_left]; intro x hx hy
    simp only [Finset.mem_Icc] at hx hy; omega
  simp only [prI, hsplit, Finset.prod_union hdisj]

theorem prI_shift (u : ℚ) (a b k : ℕ) :
    prI (u + (k : ℚ)) a b = prI u (a + k) (b + k) := by
  simp only [prI]
  rw [← Finset.map_add_right_Icc a b k, Finset.prod_map]
  refine Finset.prod_congr rfl ?_
  intro l _
  simp only [addRightEmbedding_apply, Nat.cast_add]
  ring

theorem prI_one (u : ℚ) (a : ℕ) : prI u a a = u + (a : ℚ) := by
  simp [prI]

theorem prI_empty (u : ℚ) (a b : ℕ) (h : b < a) : prI u a b = 1 := by
  have he : Icc a b = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  simp only [prI, he, Finset.prod_empty]

/-- Merge two adjacent runs.  `b'` is passed separately so that the three side conditions are
all `omega` and no `b + 1` has to be normalised at the call site. -/
theorem prI_cat (u : ℚ) (a b b' c : ℕ) (hb : b' = b + 1) (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    prI u a b * prI u b' c = prI u a c := by
  subst hb; exact (prI_split u a b c h1 h2).symm

/-- Append one factor at the top of a run. -/
theorem prI_top (u : ℚ) (a b c : ℕ) (hc : c = b + 1) (h1 : a ≤ b + 1) :
    prI u a b * (u + (c : ℚ)) = prI u a c := by
  subst hc
  rw [← prI_one u (b + 1)]
  exact prI_cat u a b (b + 1) (b + 1) rfl h1 (by omega)

/-- Prepend one factor at the bottom of a run. -/
theorem prI_bot (u : ℚ) (a a' b : ℕ) (ha : a' = a + 1) (h : a ≤ b) :
    (u + (a : ℚ)) * prI u a' b = prI u a b := by
  subst ha
  rw [← prI_one u a]
  exact prI_cat u a a (a + 1) b rfl (by omega) h

/-- A run as a `range` product, which is the shape the `afProd` induction produces. -/
theorem prI_range (u : ℚ) (a m : ℕ) :
    prI u a (a + m) = ∏ i ∈ Finset.range (m + 1), (u + ((a : ℚ) + (i : ℚ))) := by
  induction m with
  | zero => simp [prI]
  | succ m ih =>
    have hstep : prI u a (a + m + 1) = prI u a (a + m) * (u + ((a + m + 1 : ℕ) : ℚ)) := by
      simp only [prI]
      exact Finset.prod_Icc_succ_top (by omega) _
    rw [show a + (m + 1) = a + m + 1 from rfl, hstep, ih]
    conv_rhs => rw [Finset.prod_range_succ]
    push_cast
    ring

/-! ## 2. The literal-list bridge -/

/-- `afProd` over a concatenation — what turns the base's flat 123-entry `pa<j>Facs` into the
runs the engine emitted it from. -/
theorem afProd_append : ∀ (l₁ l₂ : List (ℚ × ℚ × ℚ)) (t : ℚ),
    afProd (l₁ ++ l₂) t = afProd l₁ t * afProd l₂ t := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ t; simp [afProd]
  | cons f fs ih => intro l₂ t; simp only [List.cons_append, afProd, ih l₂ t]; ring

/-- One run of `m` factors `lead·t + c·n + d`, `d` stepping by one — the emitted shape. -/
def runFacs (lead c d : ℚ) : ℕ → List (ℚ × ℚ × ℚ)
  | 0 => []
  | m + 1 => (lead, c, d) :: runFacs lead c (d + 1) m

theorem afProd_run : ∀ (m : ℕ) (lead c d t v : ℚ),
    (afProd (runFacs lead c d m) t).eval v
      = ∏ i ∈ Finset.range m, (lead * t + (d + (i : ℚ)) + c * v) := by
  intro m
  induction m with
  | zero => intro lead c d t v; simp [runFacs, afProd]
  | succ m ih =>
    intro lead c d t v
    rw [runFacs, afProd, eval_mul, af_eval, ih lead c (d + 1) t v]
    conv_rhs => rw [Finset.prod_range_succ']
    rw [Finset.prod_congr rfl (fun i _ => by push_cast; ring :
      ∀ i ∈ Finset.range m, lead * t + (d + 1 + (i : ℚ)) + c * v
        = lead * t + (d + ((i : ℚ) + 1)) + c * v)]
    push_cast
    ring

/-- A run, at `v = n`, IS a `prI`.  The length is written `m + 1` and `c`/`d` carry explicit
casts so that the four decompositions below rewrite with this lemma syntactically. -/
theorem run_prI (lead : ℚ) (c d m n : ℕ) (t : ℚ) :
    (afProd (runFacs lead (c : ℚ) (d : ℚ) (m + 1)) t).eval (n : ℚ)
      = prI (lead * t) (c * n + d) (c * n + d + m) := by
  rw [afProd_run, prI_range]
  refine Finset.prod_congr rfl ?_
  intro i _
  push_cast
  ring

/-! ## 3. The four `Pa` blocks, as run concatenations of the ENGINE's own emission -/

theorem pa0_runs : pa0Facs
    = runFacs 1 ((18 : ℕ) : ℚ) ((2 : ℕ) : ℚ) (53 + 1)
      ++ runFacs 1 ((20 : ℕ) : ℚ) ((2 : ℕ) : ℚ) (59 + 1)
      ++ runFacs 2 ((3 : ℕ) : ℚ) ((2 : ℕ) : ℚ) (8 + 1) := by
  decide +kernel

theorem pa1_runs : pa1Facs
    = runFacs 1 ((5 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (4 + 1)
      ++ runFacs 1 ((7 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (6 + 1)
      ++ runFacs 1 ((9 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (8 + 1)
      ++ runFacs 1 ((18 : ℕ) : ℚ) ((20 : ℕ) : ℚ) (35 + 1)
      ++ runFacs 1 ((20 : ℕ) : ℚ) ((22 : ℕ) : ℚ) (39 + 1)
      ++ runFacs 2 ((3 : ℕ) : ℚ) ((5 : ℕ) : ℚ) (5 + 1)
      ++ runFacs 2 ((20 : ℕ) : ℚ) ((2 : ℕ) : ℚ) (19 + 1) := by
  decide +kernel

theorem pa2_runs : pa2Facs
    = runFacs 1 ((5 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (9 + 1)
      ++ runFacs 1 ((7 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (13 + 1)
      ++ runFacs 1 ((9 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (17 + 1)
      ++ runFacs 1 ((18 : ℕ) : ℚ) ((38 : ℕ) : ℚ) (17 + 1)
      ++ runFacs 1 ((20 : ℕ) : ℚ) ((42 : ℕ) : ℚ) (19 + 1)
      ++ runFacs 2 ((3 : ℕ) : ℚ) ((8 : ℕ) : ℚ) (2 + 1)
      ++ runFacs 2 ((20 : ℕ) : ℚ) ((2 : ℕ) : ℚ) (39 + 1) := by
  decide +kernel

theorem pa3_runs : pa3Facs
    = runFacs 1 ((5 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (14 + 1)
      ++ runFacs 1 ((7 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (20 + 1)
      ++ runFacs 1 ((9 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (26 + 1)
      ++ runFacs 2 ((20 : ℕ) : ℚ) ((2 : ℕ) : ℚ) (59 + 1) := by
  decide +kernel

/-! ## 4. The row's five objects, in `prI` form -/

/-- The hat member's numerator. -/
noncomputable def hmNum (m : ℕ) (t : ℚ) : ℚ := prI (2 * t) (3 * m + 2) (20 * m + 1) * prI t 1 (5 * m)

/-- The hat member's written denominator. -/
noncomputable def hmDen (m : ℕ) (t : ℚ) : ℚ :=
  prI t (7 * m + 1) (18 * m + 1) * prI t (9 * m + 1) (20 * m + 1)

theorem hatMember_eq (m : ℕ) (t : ℚ) : Zeta2HatRep.hatMember m t = hmNum m t / hmDen m t := rfl

/-- `D_n` — the (★) rebase denominator, `dRuns · dBlock` (PAIR-5's transcription of the FACSYM). -/
noncomputable def dPr (n : ℕ) (t : ℚ) : ℚ :=
  prI t (18 * n + 2) (18 * n + 55) * prI t (20 * n + 2) (20 * n + 61)
    * prI (2 * t) (3 * n + 2) (3 * n + 10)

theorem dPr_eq (n : ℕ) (t : ℚ) :
    (Zeta2HatShatForm.dRuns n * Zeta2HatShatForm.dBlock n).eval t = dPr n t := by
  simp only [Zeta2HatShatForm.dRuns, Zeta2HatShatForm.dBlock, dPr, prI, eval_mul, eval_prod,
    eval_add, eval_X, eval_C]

/-- `Pa_j` in run form, UNIFORM in `j` — this is the shape the engine emitted and the shape the
member ratio produces.  At `j = 0` the last four runs are empty and the first three are `D`. -/
noncomputable def paPr (j n : ℕ) (t : ℚ) : ℚ :=
  prI t (18 * n + 18 * j + 2) (18 * n + 55) * prI t (20 * n + 20 * j + 2) (20 * n + 61)
    * prI (2 * t) (3 * n + 3 * j + 2) (3 * n + 10)
    * prI (2 * t) (20 * n + 2) (20 * n + 20 * j + 1)
    * prI t (5 * n + 1) (5 * n + 5 * j) * prI t (7 * n + 1) (7 * n + 7 * j)
    * prI t (9 * n + 1) (9 * n + 9 * j)

/-- `a` of the Gosper normal form. -/
noncomputable def aPr (n : ℕ) (t : ℚ) : ℚ :=
  (t + ((5 * n + 1 : ℕ) : ℚ)) * (t + ((7 * n + 1 : ℕ) : ℚ)) * (t + ((9 * n + 1 : ℕ) : ℚ))
    * (2 * t + ((20 * n + 2 : ℕ) : ℚ)) * (2 * t + ((20 * n + 3 : ℕ) : ℚ))

/-- `b` of the Gosper normal form (the (★) relation reads it at `s − 1`). -/
noncomputable def bPr (n : ℕ) (t : ℚ) : ℚ :=
  (t + ((1 : ℕ) : ℚ)) * (t + ((18 * n + 56 : ℕ) : ℚ)) * (t + ((20 * n + 62 : ℕ) : ℚ))
    * (2 * t + ((3 * n + 11 : ℕ) : ℚ)) * (2 * t + ((3 * n + 12 : ℕ) : ℚ))

theorem aPr_eq (n : ℕ) (t : ℚ) : (afProd aFacs t).eval (n : ℚ) = aPr n t := by
  rw [afProd_eval]
  simp only [aFacs, List.foldr_cons, List.foldr_nil, aPr]
  push_cast
  ring

theorem bPr_eq (n : ℕ) (t : ℚ) : (afProd bFacs t).eval (n : ℚ) = bPr n t := by
  rw [afProd_eval]
  simp only [bFacs, List.foldr_cons, List.foldr_nil, bPr]
  push_cast
  ring

/-! ## 5. `Pa_j` at `v = n` IS `paPr j n` -/

theorem pa0_prI (n : ℕ) (t : ℚ) : (afProd pa0Facs t).eval (n : ℚ) = paPr 0 n t := by
  rw [pa0_runs]
  simp only [afProd_append, eval_mul, run_prI, one_mul, paPr]
  rw [show 18 * n + 2 + 53 = 18 * n + 55 from by omega,
    show 20 * n + 2 + 59 = 20 * n + 61 from by omega,
    show 3 * n + 2 + 8 = 3 * n + 10 from by omega,
    show 18 * n + 18 * 0 + 2 = 18 * n + 2 from by omega,
    show 20 * n + 20 * 0 + 2 = 20 * n + 2 from by omega,
    show 3 * n + 3 * 0 + 2 = 3 * n + 2 from by omega,
    show 20 * n + 20 * 0 + 1 = 20 * n + 1 from by omega,
    show 5 * n + 5 * 0 = 5 * n from by omega,
    show 7 * n + 7 * 0 = 7 * n from by omega,
    show 9 * n + 9 * 0 = 9 * n from by omega,
    prI_empty (2 * t) (20 * n + 2) (20 * n + 1) (by omega),
    prI_empty t (5 * n + 1) (5 * n) (by omega),
    prI_empty t (7 * n + 1) (7 * n) (by omega),
    prI_empty t (9 * n + 1) (9 * n) (by omega)]
  ring

theorem pa1_prI (n : ℕ) (t : ℚ) : (afProd pa1Facs t).eval (n : ℚ) = paPr 1 n t := by
  rw [pa1_runs]
  simp only [afProd_append, eval_mul, run_prI, one_mul, paPr]
  rw [show 5 * n + 1 + 4 = 5 * n + 5 * 1 from by omega,
    show 7 * n + 1 + 6 = 7 * n + 7 * 1 from by omega,
    show 9 * n + 1 + 8 = 9 * n + 9 * 1 from by omega,
    show 18 * n + 20 = 18 * n + 18 * 1 + 2 from by omega,
    show 18 * n + 18 * 1 + 2 + 35 = 18 * n + 55 from by omega,
    show 20 * n + 22 = 20 * n + 20 * 1 + 2 from by omega,
    show 20 * n + 20 * 1 + 2 + 39 = 20 * n + 61 from by omega,
    show 3 * n + 5 = 3 * n + 3 * 1 + 2 from by omega,
    show 3 * n + 3 * 1 + 2 + 5 = 3 * n + 10 from by omega,
    show 20 * n + 2 + 19 = 20 * n + 20 * 1 + 1 from by omega]
  ring

theorem pa2_prI (n : ℕ) (t : ℚ) : (afProd pa2Facs t).eval (n : ℚ) = paPr 2 n t := by
  rw [pa2_runs]
  simp only [afProd_append, eval_mul, run_prI, one_mul, paPr]
  rw [show 5 * n + 1 + 9 = 5 * n + 5 * 2 from by omega,
    show 7 * n + 1 + 13 = 7 * n + 7 * 2 from by omega,
    show 9 * n + 1 + 17 = 9 * n + 9 * 2 from by omega,
    show 18 * n + 38 = 18 * n + 18 * 2 + 2 from by omega,
    show 18 * n + 18 * 2 + 2 + 17 = 18 * n + 55 from by omega,
    show 20 * n + 42 = 20 * n + 20 * 2 + 2 from by omega,
    show 20 * n + 20 * 2 + 2 + 19 = 20 * n + 61 from by omega,
    show 3 * n + 8 = 3 * n + 3 * 2 + 2 from by omega,
    show 3 * n + 3 * 2 + 2 + 2 = 3 * n + 10 from by omega,
    show 20 * n + 2 + 39 = 20 * n + 20 * 2 + 1 from by omega]
  ring

theorem pa3_prI (n : ℕ) (t : ℚ) : (afProd pa3Facs t).eval (n : ℚ) = paPr 3 n t := by
  rw [pa3_runs]
  simp only [afProd_append, eval_mul, run_prI, one_mul, paPr]
  rw [show 5 * n + 1 + 14 = 5 * n + 5 * 3 from by omega,
    show 7 * n + 1 + 20 = 7 * n + 7 * 3 from by omega,
    show 9 * n + 1 + 26 = 9 * n + 9 * 3 from by omega,
    show 20 * n + 2 + 59 = 20 * n + 20 * 3 + 1 from by omega,
    prI_empty t (18 * n + 18 * 3 + 2) (18 * n + 55) (by omega),
    prI_empty t (20 * n + 20 * 3 + 2) (20 * n + 61) (by omega),
    prI_empty (2 * t) (3 * n + 3 * 3 + 2) (3 * n + 10) (by omega)]
  ring

/-! ## 6. `hρ_hat` — the REBASE, cross-multiplied so that no division appears -/

theorem rho_cross (n j : ℕ) (hj : j ≤ 3) (t : ℚ) :
    hmNum (n + j) t * hmDen n t * dPr n t = hmNum n t * hmDen (n + j) t * paPr j n t := by
  have g1 : prI t 1 (5 * n) * prI t (5 * n + 1) (5 * n + 5 * j) = prI t 1 (5 * n + 5 * j) :=
    prI_cat t 1 (5 * n) (5 * n + 1) (5 * n + 5 * j) (by omega) (by omega) (by omega)
  have g2 : prI t (7 * n + 1) (18 * n + 1) * prI t (18 * n + 2) (18 * n + 55)
      = prI t (7 * n + 1) (18 * n + 55) :=
    prI_cat t (7 * n + 1) (18 * n + 1) (18 * n + 2) (18 * n + 55) (by omega) (by omega) (by omega)
  have g3 : prI t (9 * n + 1) (20 * n + 1) * prI t (20 * n + 2) (20 * n + 61)
      = prI t (9 * n + 1) (20 * n + 61) :=
    prI_cat t (9 * n + 1) (20 * n + 1) (20 * n + 2) (20 * n + 61) (by omega) (by omega) (by omega)
  have g4 : prI t (7 * n + 1) (7 * n + 7 * j) * prI t (7 * n + 7 * j + 1) (18 * n + 18 * j + 1)
      = prI t (7 * n + 1) (18 * n + 18 * j + 1) :=
    prI_cat t (7 * n + 1) (7 * n + 7 * j) (7 * n + 7 * j + 1) (18 * n + 18 * j + 1)
      (by omega) (by omega) (by omega)
  have g5 : prI t (7 * n + 1) (18 * n + 18 * j + 1) * prI t (18 * n + 18 * j + 2) (18 * n + 55)
      = prI t (7 * n + 1) (18 * n + 55) :=
    prI_cat t (7 * n + 1) (18 * n + 18 * j + 1) (18 * n + 18 * j + 2) (18 * n + 55)
      (by omega) (by omega) (by omega)
  have g6 : prI t (9 * n + 1) (9 * n + 9 * j) * prI t (9 * n + 9 * j + 1) (20 * n + 20 * j + 1)
      = prI t (9 * n + 1) (20 * n + 20 * j + 1) :=
    prI_cat t (9 * n + 1) (9 * n + 9 * j) (9 * n + 9 * j + 1) (20 * n + 20 * j + 1)
      (by omega) (by omega) (by omega)
  have g7 : prI t (9 * n + 1) (20 * n + 20 * j + 1) * prI t (20 * n + 20 * j + 2) (20 * n + 61)
      = prI t (9 * n + 1) (20 * n + 61) :=
    prI_cat t (9 * n + 1) (20 * n + 20 * j + 1) (20 * n + 20 * j + 2) (20 * n + 61)
      (by omega) (by omega) (by omega)
  have h1 : prI (2 * t) (3 * n + 2) (3 * n + 10)
      = prI (2 * t) (3 * n + 2) (3 * n + 3 * j + 1) * prI (2 * t) (3 * n + 3 * j + 2) (3 * n + 10) := by
    have := prI_split (2 * t) (3 * n + 2) (3 * n + 3 * j + 1) (3 * n + 10) (by omega) (by omega)
    rwa [show 3 * n + 3 * j + 1 + 1 = 3 * n + 3 * j + 2 from by omega] at this
  have h2 : prI (2 * t) (3 * n + 2) (3 * n + 3 * j + 1)
        * prI (2 * t) (3 * n + 3 * j + 2) (20 * n + 20 * j + 1)
      = prI (2 * t) (3 * n + 2) (20 * n + 20 * j + 1) :=
    prI_cat (2 * t) (3 * n + 2) (3 * n + 3 * j + 1) (3 * n + 3 * j + 2) (20 * n + 20 * j + 1)
      (by omega) (by omega) (by omega)
  have h3 : prI (2 * t) (3 * n + 2) (20 * n + 1) * prI (2 * t) (20 * n + 2) (20 * n + 20 * j + 1)
      = prI (2 * t) (3 * n + 2) (20 * n + 20 * j + 1) :=
    prI_cat (2 * t) (3 * n + 2) (20 * n + 1) (20 * n + 2) (20 * n + 20 * j + 1)
      (by omega) (by omega) (by omega)
  have HL : hmNum (n + j) t * hmDen n t * dPr n t
      = prI (2 * t) (3 * n + 2) (20 * n + 20 * j + 1)
          * prI (2 * t) (3 * n + 3 * j + 2) (3 * n + 10)
          * prI t 1 (5 * n + 5 * j) * prI t (7 * n + 1) (18 * n + 55)
          * prI t (9 * n + 1) (20 * n + 61) := by
    simp only [hmNum, hmDen, dPr,
      show 3 * (n + j) + 2 = 3 * n + 3 * j + 2 from by ring,
      show 20 * (n + j) + 1 = 20 * n + 20 * j + 1 from by ring,
      show 5 * (n + j) = 5 * n + 5 * j from by ring]
    rw [← g2, ← g3, ← h2, h1]
    ring
  have HR : hmNum n t * hmDen (n + j) t * paPr j n t
      = prI (2 * t) (3 * n + 2) (20 * n + 20 * j + 1)
          * prI (2 * t) (3 * n + 3 * j + 2) (3 * n + 10)
          * prI t 1 (5 * n + 5 * j) * prI t (7 * n + 1) (18 * n + 55)
          * prI t (9 * n + 1) (20 * n + 61) := by
    simp only [hmNum, hmDen, paPr,
      show 7 * (n + j) + 1 = 7 * n + 7 * j + 1 from by ring,
      show 18 * (n + j) + 1 = 18 * n + 18 * j + 1 from by ring,
      show 9 * (n + j) + 1 = 9 * n + 9 * j + 1 from by ring,
      show 20 * (n + j) + 1 = 20 * n + 20 * j + 1 from by ring]
    rw [← g1, ← g5, ← g4, ← g7, ← g6, ← h3]
    ring
  rw [HL, HR]

/-! ## 7. `hu_hat` — the Gosper normal form, cross-multiplied -/

theorem hu_cross (n : ℕ) (t : ℚ) :
    hmNum n (t + 1) * hmDen n t * dPr n t * bPr n t
      = hmNum n t * hmDen n (t + 1) * dPr n (t + 1) * aPr n t := by
  have s2 : ∀ a b : ℕ, prI (2 * (t + 1)) a b = prI (2 * t) (a + 2) (b + 2) := by
    intro a b
    rw [show 2 * (t + 1) = 2 * t + ((2 : ℕ) : ℚ) from by push_cast; ring, prI_shift]
  have s1 : ∀ a b : ℕ, prI (t + 1) a b = prI t (a + 1) (b + 1) := by
    intro a b
    rw [show t + 1 = t + ((1 : ℕ) : ℚ) from by push_cast; ring, prI_shift]
  -- the canonical pieces, each built by one merge chain
  have c1 : prI t 1 (5 * n) * (t + ((5 * n + 1 : ℕ) : ℚ)) = prI t 1 (5 * n + 1) :=
    prI_top t 1 (5 * n) (5 * n + 1) (by omega) (by omega)
  have c1' : (t + ((1 : ℕ) : ℚ)) * prI t 2 (5 * n + 1) = prI t 1 (5 * n + 1) :=
    prI_bot t 1 2 (5 * n + 1) (by omega) (by omega)
  have c2 : prI t (7 * n + 1) (18 * n + 1) * prI t (18 * n + 2) (18 * n + 55)
      = prI t (7 * n + 1) (18 * n + 55) :=
    prI_cat t (7 * n + 1) (18 * n + 1) (18 * n + 2) (18 * n + 55) (by omega) (by omega) (by omega)
  have c2' : prI t (7 * n + 1) (18 * n + 55) * (t + ((18 * n + 56 : ℕ) : ℚ))
      = prI t (7 * n + 1) (18 * n + 56) :=
    prI_top t (7 * n + 1) (18 * n + 55) (18 * n + 56) (by omega) (by omega)
  have c2r : prI t (7 * n + 2) (18 * n + 2) * prI t (18 * n + 3) (18 * n + 56)
      = prI t (7 * n + 2) (18 * n + 56) :=
    prI_cat t (7 * n + 2) (18 * n + 2) (18 * n + 3) (18 * n + 56) (by omega) (by omega) (by omega)
  have c2r' : (t + ((7 * n + 1 : ℕ) : ℚ)) * prI t (7 * n + 2) (18 * n + 56)
      = prI t (7 * n + 1) (18 * n + 56) :=
    prI_bot t (7 * n + 1) (7 * n + 2) (18 * n + 56) (by omega) (by omega)
  have c3 : prI t (9 * n + 1) (20 * n + 1) * prI t (20 * n + 2) (20 * n + 61)
      = prI t (9 * n + 1) (20 * n + 61) :=
    prI_cat t (9 * n + 1) (20 * n + 1) (20 * n + 2) (20 * n + 61) (by omega) (by omega) (by omega)
  have c3' : prI t (9 * n + 1) (20 * n + 61) * (t + ((20 * n + 62 : ℕ) : ℚ))
      = prI t (9 * n + 1) (20 * n + 62) :=
    prI_top t (9 * n + 1) (20 * n + 61) (20 * n + 62) (by omega) (by omega)
  have c3r : prI t (9 * n + 2) (20 * n + 2) * prI t (20 * n + 3) (20 * n + 62)
      = prI t (9 * n + 2) (20 * n + 62) :=
    prI_cat t (9 * n + 2) (20 * n + 2) (20 * n + 3) (20 * n + 62) (by omega) (by omega) (by omega)
  have c3r' : (t + ((9 * n + 1 : ℕ) : ℚ)) * prI t (9 * n + 2) (20 * n + 62)
      = prI t (9 * n + 1) (20 * n + 62) :=
    prI_bot t (9 * n + 1) (9 * n + 2) (20 * n + 62) (by omega) (by omega)
  have d1 : prI (2 * t) (3 * n + 2) (3 * n + 10) * (2 * t + ((3 * n + 11 : ℕ) : ℚ))
      = prI (2 * t) (3 * n + 2) (3 * n + 11) :=
    prI_top (2 * t) (3 * n + 2) (3 * n + 10) (3 * n + 11) (by omega) (by omega)
  have d2 : prI (2 * t) (3 * n + 2) (3 * n + 11) * (2 * t + ((3 * n + 12 : ℕ) : ℚ))
      = prI (2 * t) (3 * n + 2) (3 * n + 12) :=
    prI_top (2 * t) (3 * n + 2) (3 * n + 11) (3 * n + 12) (by omega) (by omega)
  have d3 : prI (2 * t) (3 * n + 2) (3 * n + 12)
      = prI (2 * t) (3 * n + 2) (3 * n + 3) * prI (2 * t) (3 * n + 4) (3 * n + 12) := by
    have := prI_split (2 * t) (3 * n + 2) (3 * n + 3) (3 * n + 12) (by omega) (by omega)
    rwa [show 3 * n + 3 + 1 = 3 * n + 4 from by omega] at this
  have d4 : prI (2 * t) (3 * n + 2) (3 * n + 3) * prI (2 * t) (3 * n + 4) (20 * n + 3)
      = prI (2 * t) (3 * n + 2) (20 * n + 3) :=
    prI_cat (2 * t) (3 * n + 2) (3 * n + 3) (3 * n + 4) (20 * n + 3) (by omega) (by omega) (by omega)
  have e1 : prI (2 * t) (3 * n + 2) (20 * n + 1) * (2 * t + ((20 * n + 2 : ℕ) : ℚ))
      = prI (2 * t) (3 * n + 2) (20 * n + 2) :=
    prI_top (2 * t) (3 * n + 2) (20 * n + 1) (20 * n + 2) (by omega) (by omega)
  have e2 : prI (2 * t) (3 * n + 2) (20 * n + 2) * (2 * t + ((20 * n + 3 : ℕ) : ℚ))
      = prI (2 * t) (3 * n + 2) (20 * n + 3) :=
    prI_top (2 * t) (3 * n + 2) (20 * n + 2) (20 * n + 3) (by omega) (by omega)
  -- The `2t` side of `hu` needs its four steps as ONE equation: after `← d4` the two factors
  -- `d3` wants are no longer adjacent, so the chain has to be discharged before it is used.
  have dcomb : prI (2 * t) (3 * n + 2) (20 * n + 3) * prI (2 * t) (3 * n + 4) (3 * n + 12)
      = prI (2 * t) (3 * n + 2) (3 * n + 10) * (2 * t + ((3 * n + 11 : ℕ) : ℚ))
        * (2 * t + ((3 * n + 12 : ℕ) : ℚ)) * prI (2 * t) (3 * n + 4) (20 * n + 3) := by
    rw [d1, d2, d3, ← d4]
    ring
  have HL : hmNum n (t + 1) * hmDen n t * dPr n t * bPr n t
      = prI (2 * t) (3 * n + 2) (20 * n + 3) * prI (2 * t) (3 * n + 4) (3 * n + 12)
        * prI t 1 (5 * n + 1) * prI t (7 * n + 1) (18 * n + 56)
        * prI t (9 * n + 1) (20 * n + 62) := by
    simp only [hmNum, hmDen, dPr, bPr, s1, s2,
      show 3 * n + 2 + 2 = 3 * n + 4 from by omega,
      show 20 * n + 1 + 2 = 20 * n + 3 from by omega,
      show 1 + 1 = 2 from by omega]
    rw [← c1', ← c2', ← c2, ← c3', ← c3, dcomb]
    ring
  have HR : hmNum n t * hmDen n (t + 1) * dPr n (t + 1) * aPr n t
      = prI (2 * t) (3 * n + 2) (20 * n + 3) * prI (2 * t) (3 * n + 4) (3 * n + 12)
        * prI t 1 (5 * n + 1) * prI t (7 * n + 1) (18 * n + 56)
        * prI t (9 * n + 1) (20 * n + 62) := by
    simp only [hmNum, hmDen, dPr, aPr, s1, s2,
      show 7 * n + 1 + 1 = 7 * n + 2 from by omega,
      show 18 * n + 1 + 1 = 18 * n + 2 from by omega,
      show 9 * n + 1 + 1 = 9 * n + 2 from by omega,
      show 20 * n + 1 + 1 = 20 * n + 2 from by omega,
      show 18 * n + 2 + 1 = 18 * n + 3 from by omega,
      show 18 * n + 55 + 1 = 18 * n + 56 from by omega,
      show 20 * n + 2 + 1 = 20 * n + 3 from by omega,
      show 20 * n + 61 + 1 = 20 * n + 62 from by omega,
      show 3 * n + 2 + 2 = 3 * n + 4 from by omega,
      show 3 * n + 10 + 2 = 3 * n + 12 from by omega]
    rw [← c1, ← c2r', ← c2r, ← c3r', ← c3r, ← e2, ← e1]
    ring
  rw [HL, HR]

end Zeta2Pair6Runs

#print axioms Zeta2Pair6Runs.prI_split
#print axioms Zeta2Pair6Runs.prI_shift
#print axioms Zeta2Pair6Runs.prI_cat
#print axioms Zeta2Pair6Runs.prI_top
#print axioms Zeta2Pair6Runs.prI_bot
#print axioms Zeta2Pair6Runs.prI_range
#print axioms Zeta2Pair6Runs.afProd_append
#print axioms Zeta2Pair6Runs.afProd_run
#print axioms Zeta2Pair6Runs.run_prI
#print axioms Zeta2Pair6Runs.pa0_runs
#print axioms Zeta2Pair6Runs.pa1_runs
#print axioms Zeta2Pair6Runs.pa2_runs
#print axioms Zeta2Pair6Runs.pa3_runs
#print axioms Zeta2Pair6Runs.hatMember_eq
#print axioms Zeta2Pair6Runs.dPr_eq
#print axioms Zeta2Pair6Runs.aPr_eq
#print axioms Zeta2Pair6Runs.bPr_eq
#print axioms Zeta2Pair6Runs.pa0_prI
#print axioms Zeta2Pair6Runs.pa1_prI
#print axioms Zeta2Pair6Runs.pa2_prI
#print axioms Zeta2Pair6Runs.pa3_prI
#print axioms Zeta2Pair6Runs.rho_cross
#print axioms Zeta2Pair6Runs.hu_cross
