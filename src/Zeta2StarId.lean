/-
# Row STAR-ID (i) — the cand-t1 (★) family's `ρ j` IS `candidateM`'s `R_{n+j}/Π(n+j)`

`docs/future/zeta2-lean-chain.md` row STAR-ID, part (i).

**What this file pays.**  `StarForallCandt1.star_forall` (row STAR, closed) is a statement about
the ENGINE's factor lists `aFacs`, `bFacs`, `pa0Facs .. pa3Facs`.  Nothing in Lean said those
lists are about `Zeta2Defs.candidateM` — the member every other row of the chain is stated at.
`Zeta2StarB1.star_telescopes` consumes the (★) data through exactly two multiplicative facts, and
they are the whole of the identification:

    hρ   R_{n+j}(t) · R_n-den(t) · D_n(t) = R_n(t) · R_{n+j}-den(t) · Pa_j(t)   (`star_rho`, ∀ j ≤ 3)
    hu   u(t+1) · b(t) = u(t) · a(t),   u = numPoly n / (denPoly n · D_n)       (`star_u`)

with `D_n := Pa_0` — the engine never emits `D` separately, and `Pa0 = D` symbolically
(`starid_check.py` §3).  Both are stated in TARGET vocabulary, against `candidateM.numPoly` /
`.denPoly` and the base's own `afProd … Facs` — never against a transcription.  `rho_eq_member`
then divides through: off a finite set, `u(t)·Pa_j(t) = numPoly(n+j)/denPoly(n+j)` — the FUNCTION
`Zeta2T1Eval.Phi_rho`'s hypothesis `hr` is about.

**Why it is short.**  cand-t1's factors are all MONIC and emitted in run order (`starid_check.py`
and the run table in this row's cell), so both identities are `Finset.Icc` merges with `omega`
side conditions — `Zeta2Pair6Runs`' recipe for the hat, with `hatMember` swapped for
`numPoly/denPoly`.  The four `pa<j>Facs` literals are tied to their runs by one `decide +kernel`
each, so nothing here trusts a reading of the engine's data.

**What this file does NOT do.**  It does not prove (ii) — the operator identity between the
coords' `Ãⱼ` and the chain's cleared `cⱼ` — nor any nonvanishing, nor the composition
`Σ αⱼ Φ(ρ_{n+j}) = 0`, which is L1-ASM's.  `Zeta2Target.zeta2_not_liouvilleWith` is still `sorry`.

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2StarId.lean

It imports the GENERATED `StarForallCandt1Base`, pinned by `modules/MANIFEST-cand-t1-kernel.sha256`
— the manifest STAR's own receipt was taken against — so that case REFUSES rather than skips.
Falsifier: `falsify_starid.sh`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic
import Zeta2Defs
import Zeta2PrI
import StarForallCandt1Base

namespace Zeta2StarId

open Polynomial Finset Zeta2PrI StarForallCandt1 Zeta2Defs

/-! ## 1. The literal-list bridge, over THIS base's `afProd` -/

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

/-- A run, at `v = n`, IS a `prI`. -/
theorem run_prI (lead : ℚ) (c d m n : ℕ) (t : ℚ) :
    (afProd (runFacs lead (c : ℚ) (d : ℚ) (m + 1)) t).eval (n : ℚ)
      = prI (lead * t) (c * n + d) (c * n + d + m) := by
  rw [afProd_run, prI_range]
  refine Finset.prod_congr rfl ?_
  intro i _
  push_cast
  ring

/-! ## 2. The four `Pa` blocks, as run concatenations of the ENGINE's own emission -/

theorem pa0_runs : pa0Facs
    = runFacs 1 ((2 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (5 + 1)
      ++ runFacs 1 ((4 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (11 + 1)
      ++ runFacs 1 ((26 : ℕ) : ℚ) ((2 : ℕ) : ℚ) (77 + 1) := by
  decide +kernel

theorem pa1_runs : pa1Facs
    = runFacs 1 ((2 : ℕ) : ℚ) ((3 : ℕ) : ℚ) (3 + 1)
      ++ runFacs 1 ((4 : ℕ) : ℚ) ((5 : ℕ) : ℚ) (7 + 1)
      ++ runFacs 1 ((9 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (8 + 1)
      ++ runFacs 1 ((11 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (10 + 1)
      ++ runFacs 1 ((13 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (12 + 1)
      ++ runFacs 1 ((15 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (14 + 1)
      ++ runFacs 1 ((26 : ℕ) : ℚ) ((28 : ℕ) : ℚ) (51 + 1) := by
  decide +kernel

theorem pa2_runs : pa2Facs
    = runFacs 1 ((2 : ℕ) : ℚ) ((5 : ℕ) : ℚ) (1 + 1)
      ++ runFacs 1 ((4 : ℕ) : ℚ) ((9 : ℕ) : ℚ) (3 + 1)
      ++ runFacs 1 ((9 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (17 + 1)
      ++ runFacs 1 ((11 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (21 + 1)
      ++ runFacs 1 ((13 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (25 + 1)
      ++ runFacs 1 ((15 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (29 + 1)
      ++ runFacs 1 ((26 : ℕ) : ℚ) ((54 : ℕ) : ℚ) (25 + 1) := by
  decide +kernel

theorem pa3_runs : pa3Facs
    = runFacs 1 ((9 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (26 + 1)
      ++ runFacs 1 ((11 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (32 + 1)
      ++ runFacs 1 ((13 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (38 + 1)
      ++ runFacs 1 ((15 : ℕ) : ℚ) ((1 : ℕ) : ℚ) (44 + 1) := by
  decide +kernel

/-! ## 3. The row's objects, in `prI` form -/

/-- `candidateM.numPoly m` at `t`: `(t+1)_{13m} · (t+2m+1)_{9m} · (t+4m+1)_{5m}`. -/
noncomputable def mNum (m : ℕ) (t : ℚ) : ℚ :=
  prI t 1 (13 * m) * prI t (2 * m + 1) (11 * m) * prI t (4 * m + 1) (9 * m)

/-- `candidateM.denPoly m` at `t`: `(t+15m+1)_{11m+1}`. -/
noncomputable def mDen (m : ℕ) (t : ℚ) : ℚ := prI t (15 * m + 1) (26 * m + 1)

/-- `D_n` — the (★) rebase denominator, which the engine emits as `Pa_0`. -/
noncomputable def dPr (n : ℕ) (t : ℚ) : ℚ :=
  prI t (2 * n + 1) (2 * n + 6) * prI t (4 * n + 1) (4 * n + 12) * prI t (26 * n + 2) (26 * n + 79)

/-- `Pa_j` in run form, UNIFORM in `j`.  At `j = 0` the last four runs are empty; at `j = 3` the
first three are. -/
noncomputable def paPr (j n : ℕ) (t : ℚ) : ℚ :=
  prI t (2 * n + 2 * j + 1) (2 * n + 6) * prI t (4 * n + 4 * j + 1) (4 * n + 12)
    * prI t (26 * n + 26 * j + 2) (26 * n + 79)
    * prI t (9 * n + 1) (9 * n + 9 * j) * prI t (11 * n + 1) (11 * n + 11 * j)
    * prI t (13 * n + 1) (13 * n + 13 * j) * prI t (15 * n + 1) (15 * n + 15 * j)

/-- `a` of the Gosper normal form. -/
noncomputable def aPr (n : ℕ) (t : ℚ) : ℚ :=
  (t + ((9 * n + 1 : ℕ) : ℚ)) * (t + ((11 * n + 1 : ℕ) : ℚ)) * (t + ((13 * n + 1 : ℕ) : ℚ))
    * (t + ((15 * n + 1 : ℕ) : ℚ))

/-- `b` of the Gosper normal form. -/
noncomputable def bPr (n : ℕ) (t : ℚ) : ℚ :=
  (t + ((1 : ℕ) : ℚ)) * (t + ((2 * n + 7 : ℕ) : ℚ)) * (t + ((4 * n + 13 : ℕ) : ℚ))
    * (t + ((26 * n + 80 : ℕ) : ℚ))

/-! ## 4. The ties: every `prI` object IS the target-vocabulary or engine object -/

/-- One `Zeta2Defs.block` is one run, when its start is at least `1`. -/
theorem block_eval (c len : ℕ) (hc : 1 ≤ c) (t : ℚ) :
    (block c len).eval t = prI t c (c + len - 1) := by
  induction len with
  | zero =>
    simp only [block, Finset.range_zero, Finset.prod_empty, eval_one]
    rw [prI_empty t c (c + 0 - 1) (by omega)]
  | succ len ih =>
    have h : block c (len + 1) = block c len * (X + C ((c + len : ℕ) : ℚ)) := by
      simp only [block, Finset.prod_range_succ]
    rw [h, eval_mul, ih, eval_add, eval_X, eval_C, show c + (len + 1) - 1 = c + len from by omega]
    exact prI_top t c (c + len - 1) (c + len) (by omega) (by omega)

theorem numPoly_eval (m : ℕ) (t : ℚ) : (candidateM.numPoly m).eval t = mNum m t := by
  have e1 : (block 1 (13 * m)).eval t = prI t 1 (13 * m) := by
    rw [block_eval _ _ le_rfl]; congr 1; omega
  have e2 : (block (2 * m + 1) (9 * m)).eval t = prI t (2 * m + 1) (11 * m) := by
    rw [block_eval _ _ (by omega)]; congr 1; omega
  have e3 : (block (4 * m + 1) (5 * m)).eval t = prI t (4 * m + 1) (9 * m) := by
    rw [block_eval _ _ (by omega)]; congr 1; omega
  show (block 1 (13 * m) * block (2 * m + 1) (9 * m) * block (4 * m + 1) (5 * m)).eval t = _
  rw [eval_mul, eval_mul, e1, e2, e3]
  rfl

theorem denPoly_eval (m : ℕ) (t : ℚ) : (candidateM.denPoly m).eval t = mDen m t := by
  show (block (15 * m + 1) (11 * m + 1)).eval t = prI t (15 * m + 1) (26 * m + 1)
  rw [block_eval _ _ (by omega)]; congr 1; omega

theorem pa0_prI (n : ℕ) (t : ℚ) : (afProd pa0Facs t).eval (n : ℚ) = paPr 0 n t := by
  rw [pa0_runs]
  simp only [afProd_append, eval_mul, run_prI, one_mul, paPr]
  rw [prI_empty t (9 * n + 1) (9 * n + 9 * 0) (by omega),
    prI_empty t (11 * n + 1) (11 * n + 11 * 0) (by omega),
    prI_empty t (13 * n + 1) (13 * n + 13 * 0) (by omega),
    prI_empty t (15 * n + 1) (15 * n + 15 * 0) (by omega),
    show 2 * n + 1 + 5 = 2 * n + 6 from by omega, show 4 * n + 1 + 11 = 4 * n + 12 from by omega,
    show 26 * n + 2 + 77 = 26 * n + 79 from by omega,
    show 2 * n + 2 * 0 + 1 = 2 * n + 1 from by omega, show 4 * n + 4 * 0 + 1 = 4 * n + 1 from by omega,
    show 26 * n + 26 * 0 + 2 = 26 * n + 2 from by omega]
  ring

theorem pa1_prI (n : ℕ) (t : ℚ) : (afProd pa1Facs t).eval (n : ℚ) = paPr 1 n t := by
  rw [pa1_runs]
  simp only [afProd_append, eval_mul, run_prI, one_mul, paPr]
  rw [show 2 * n + 3 = 2 * n + 2 * 1 + 1 from by omega, show 2 * n + 2 * 1 + 1 + 3 = 2 * n + 6 from by omega,
    show 4 * n + 5 = 4 * n + 4 * 1 + 1 from by omega, show 4 * n + 4 * 1 + 1 + 7 = 4 * n + 12 from by omega,
    show 26 * n + 28 = 26 * n + 26 * 1 + 2 from by omega,
    show 26 * n + 26 * 1 + 2 + 51 = 26 * n + 79 from by omega,
    show 9 * n + 1 + 8 = 9 * n + 9 * 1 from by omega, show 11 * n + 1 + 10 = 11 * n + 11 * 1 from by omega,
    show 13 * n + 1 + 12 = 13 * n + 13 * 1 from by omega,
    show 15 * n + 1 + 14 = 15 * n + 15 * 1 from by omega]
  ring

theorem pa2_prI (n : ℕ) (t : ℚ) : (afProd pa2Facs t).eval (n : ℚ) = paPr 2 n t := by
  rw [pa2_runs]
  simp only [afProd_append, eval_mul, run_prI, one_mul, paPr]
  rw [show 2 * n + 5 = 2 * n + 2 * 2 + 1 from by omega, show 2 * n + 2 * 2 + 1 + 1 = 2 * n + 6 from by omega,
    show 4 * n + 9 = 4 * n + 4 * 2 + 1 from by omega, show 4 * n + 4 * 2 + 1 + 3 = 4 * n + 12 from by omega,
    show 26 * n + 54 = 26 * n + 26 * 2 + 2 from by omega,
    show 26 * n + 26 * 2 + 2 + 25 = 26 * n + 79 from by omega,
    show 9 * n + 1 + 17 = 9 * n + 9 * 2 from by omega, show 11 * n + 1 + 21 = 11 * n + 11 * 2 from by omega,
    show 13 * n + 1 + 25 = 13 * n + 13 * 2 from by omega,
    show 15 * n + 1 + 29 = 15 * n + 15 * 2 from by omega]
  ring

theorem pa3_prI (n : ℕ) (t : ℚ) : (afProd pa3Facs t).eval (n : ℚ) = paPr 3 n t := by
  rw [pa3_runs]
  simp only [afProd_append, eval_mul, run_prI, one_mul, paPr]
  rw [prI_empty t (2 * n + 2 * 3 + 1) (2 * n + 6) (by omega),
    prI_empty t (4 * n + 4 * 3 + 1) (4 * n + 12) (by omega),
    prI_empty t (26 * n + 26 * 3 + 2) (26 * n + 79) (by omega),
    show 9 * n + 1 + 26 = 9 * n + 9 * 3 from by omega, show 11 * n + 1 + 32 = 11 * n + 11 * 3 from by omega,
    show 13 * n + 1 + 38 = 13 * n + 13 * 3 from by omega,
    show 15 * n + 1 + 44 = 15 * n + 15 * 3 from by omega]
  ring

theorem paPr_zero (n : ℕ) (t : ℚ) : paPr 0 n t = dPr n t := by
  simp only [paPr, dPr]
  rw [prI_empty t (9 * n + 1) (9 * n + 9 * 0) (by omega),
    prI_empty t (11 * n + 1) (11 * n + 11 * 0) (by omega),
    prI_empty t (13 * n + 1) (13 * n + 13 * 0) (by omega),
    prI_empty t (15 * n + 1) (15 * n + 15 * 0) (by omega),
    show 2 * n + 2 * 0 + 1 = 2 * n + 1 from by omega, show 4 * n + 4 * 0 + 1 = 4 * n + 1 from by omega,
    show 26 * n + 26 * 0 + 2 = 26 * n + 2 from by omega]
  ring

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

/-- The engine's `Pa_j` list, indexed. -/
noncomputable def paF : ℕ → List (ℚ × ℚ × ℚ)
  | 0 => pa0Facs
  | 1 => pa1Facs
  | 2 => pa2Facs
  | _ => pa3Facs

theorem paF_prI (j n : ℕ) (hj : j ≤ 3) (t : ℚ) : (afProd (paF j) t).eval (n : ℚ) = paPr j n t := by
  interval_cases j
  · exact pa0_prI n t
  · exact pa1_prI n t
  · exact pa2_prI n t
  · exact pa3_prI n t

/-! ## 5. `hρ` — the REBASE, cross-multiplied so that no division appears -/

theorem rho_cross (n j : ℕ) (hj : j ≤ 3) (t : ℚ) :
    mNum (n + j) t * mDen n t * dPr n t = mNum n t * mDen (n + j) t * paPr j n t := by
  have d2 : prI t (2 * n + 1) (2 * n + 6)
      = prI t (2 * n + 1) (2 * n + 2 * j) * prI t (2 * n + 2 * j + 1) (2 * n + 6) :=
    (prI_cat t _ _ _ _ rfl (by omega) (by omega)).symm
  have d4 : prI t (4 * n + 1) (4 * n + 12)
      = prI t (4 * n + 1) (4 * n + 4 * j) * prI t (4 * n + 4 * j + 1) (4 * n + 12) :=
    (prI_cat t _ _ _ _ rfl (by omega) (by omega)).symm
  have m2L : prI t (2 * n + 1) (2 * n + 2 * j) * prI t (2 * n + 2 * j + 1) (11 * n + 11 * j)
      = prI t (2 * n + 1) (11 * n + 11 * j) := prI_cat t _ _ _ _ rfl (by omega) (by omega)
  have m4L : prI t (4 * n + 1) (4 * n + 4 * j) * prI t (4 * n + 4 * j + 1) (9 * n + 9 * j)
      = prI t (4 * n + 1) (9 * n + 9 * j) := prI_cat t _ _ _ _ rfl (by omega) (by omega)
  have mdL : prI t (15 * n + 1) (26 * n + 1) * prI t (26 * n + 2) (26 * n + 79)
      = prI t (15 * n + 1) (26 * n + 79) := prI_cat t _ _ _ _ (by omega) (by omega) (by omega)
  have m13R : prI t 1 (13 * n) * prI t (13 * n + 1) (13 * n + 13 * j)
      = prI t 1 (13 * n + 13 * j) := prI_cat t _ _ _ _ rfl (by omega) (by omega)
  have m2R : prI t (2 * n + 1) (11 * n) * prI t (11 * n + 1) (11 * n + 11 * j)
      = prI t (2 * n + 1) (11 * n + 11 * j) := prI_cat t _ _ _ _ rfl (by omega) (by omega)
  have m4R : prI t (4 * n + 1) (9 * n) * prI t (9 * n + 1) (9 * n + 9 * j)
      = prI t (4 * n + 1) (9 * n + 9 * j) := prI_cat t _ _ _ _ rfl (by omega) (by omega)
  have md1R : prI t (15 * n + 1) (15 * n + 15 * j) * prI t (15 * n + 15 * j + 1) (26 * n + 26 * j + 1)
      = prI t (15 * n + 1) (26 * n + 26 * j + 1) := prI_cat t _ _ _ _ rfl (by omega) (by omega)
  have md2R : prI t (15 * n + 1) (26 * n + 26 * j + 1) * prI t (26 * n + 26 * j + 2) (26 * n + 79)
      = prI t (15 * n + 1) (26 * n + 79) := prI_cat t _ _ _ _ (by omega) (by omega) (by omega)
  have eL : mNum (n + j) t * mDen n t * dPr n t
      = prI t 1 (13 * n + 13 * j)
        * (prI t (2 * n + 1) (2 * n + 2 * j) * prI t (2 * n + 2 * j + 1) (11 * n + 11 * j))
        * (prI t (4 * n + 1) (4 * n + 4 * j) * prI t (4 * n + 4 * j + 1) (9 * n + 9 * j))
        * (prI t (15 * n + 1) (26 * n + 1) * prI t (26 * n + 2) (26 * n + 79))
        * prI t (2 * n + 2 * j + 1) (2 * n + 6) * prI t (4 * n + 4 * j + 1) (4 * n + 12) := by
    simp only [mNum, mDen, dPr, show 13 * (n + j) = 13 * n + 13 * j from by ring,
      show 2 * (n + j) = 2 * n + 2 * j from by ring, show 11 * (n + j) = 11 * n + 11 * j from by ring,
      show 4 * (n + j) = 4 * n + 4 * j from by ring, show 9 * (n + j) = 9 * n + 9 * j from by ring]
    rw [d2, d4]
    ring
  have eR : mNum n t * mDen (n + j) t * paPr j n t
      = (prI t 1 (13 * n) * prI t (13 * n + 1) (13 * n + 13 * j))
        * (prI t (2 * n + 1) (11 * n) * prI t (11 * n + 1) (11 * n + 11 * j))
        * (prI t (4 * n + 1) (9 * n) * prI t (9 * n + 1) (9 * n + 9 * j))
        * ((prI t (15 * n + 1) (15 * n + 15 * j) * prI t (15 * n + 15 * j + 1) (26 * n + 26 * j + 1))
          * prI t (26 * n + 26 * j + 2) (26 * n + 79))
        * prI t (2 * n + 2 * j + 1) (2 * n + 6) * prI t (4 * n + 4 * j + 1) (4 * n + 12) := by
    simp only [mNum, mDen, paPr, show 15 * (n + j) = 15 * n + 15 * j from by ring,
      show 26 * (n + j) = 26 * n + 26 * j from by ring]
    ring
  rw [eL, eR, m2L, m4L, mdL, m13R, m2R, m4R, md1R, md2R]

/-! ## 6. `hu` — the Gosper normal form, cross-multiplied -/

theorem hu_cross (n : ℕ) (t : ℚ) :
    mNum n (t + 1) * mDen n t * dPr n t * bPr n t
      = mNum n t * mDen n (t + 1) * dPr n (t + 1) * aPr n t := by
  have s1 : ∀ a b : ℕ, prI (t + 1) a b = prI t (a + 1) (b + 1) := by
    intro a b
    rw [show t + 1 = t + ((1 : ℕ) : ℚ) from by push_cast; ring, prI_shift]
  have tb2 : prI t (2 * n + 1) (2 * n + 6) * (t + ((2 * n + 7 : ℕ) : ℚ))
      = (t + ((2 * n + 1 : ℕ) : ℚ)) * prI t (2 * n + 2) (2 * n + 7) := by
    rw [prI_top t _ _ _ (by omega) (by omega), prI_bot t _ _ _ (by omega) (by omega)]
  have tb4 : prI t (4 * n + 1) (4 * n + 12) * (t + ((4 * n + 13 : ℕ) : ℚ))
      = (t + ((4 * n + 1 : ℕ) : ℚ)) * prI t (4 * n + 2) (4 * n + 13) := by
    rw [prI_top t _ _ _ (by omega) (by omega), prI_bot t _ _ _ (by omega) (by omega)]
  have dm1 : prI t (15 * n + 1) (26 * n + 1) * prI t (26 * n + 2) (26 * n + 79)
      = prI t (15 * n + 1) (26 * n + 79) := prI_cat t _ _ _ _ (by omega) (by omega) (by omega)
  have dm2 : prI t (15 * n + 1) (26 * n + 79) * (t + ((26 * n + 80 : ℕ) : ℚ))
      = prI t (15 * n + 1) (26 * n + 80) := prI_top t _ _ _ (by omega) (by omega)
  have tb13 : prI t 1 (13 * n) * (t + ((13 * n + 1 : ℕ) : ℚ))
      = (t + ((1 : ℕ) : ℚ)) * prI t 2 (13 * n + 1) := by
    rw [prI_top t _ _ _ (by omega) (by omega), prI_bot t _ _ _ (by omega) (by omega)]
  have tb2' : prI t (2 * n + 1) (11 * n) * (t + ((11 * n + 1 : ℕ) : ℚ))
      = (t + ((2 * n + 1 : ℕ) : ℚ)) * prI t (2 * n + 2) (11 * n + 1) := by
    rw [prI_top t _ _ _ (by omega) (by omega), prI_bot t _ _ _ (by omega) (by omega)]
  have tb4' : prI t (4 * n + 1) (9 * n) * (t + ((9 * n + 1 : ℕ) : ℚ))
      = (t + ((4 * n + 1 : ℕ) : ℚ)) * prI t (4 * n + 2) (9 * n + 1) := by
    rw [prI_top t _ _ _ (by omega) (by omega), prI_bot t _ _ _ (by omega) (by omega)]
  have r1 : prI t (15 * n + 2) (26 * n + 2) * prI t (26 * n + 3) (26 * n + 80)
      = prI t (15 * n + 2) (26 * n + 80) := prI_cat t _ _ _ _ (by omega) (by omega) (by omega)
  have r2 : (t + ((15 * n + 1 : ℕ) : ℚ)) * prI t (15 * n + 2) (26 * n + 80)
      = prI t (15 * n + 1) (26 * n + 80) := prI_bot t _ _ _ (by omega) (by omega)
  have eL : mNum n (t + 1) * mDen n t * dPr n t * bPr n t
      = prI t 2 (13 * n + 1) * (t + ((1 : ℕ) : ℚ)) * prI t (2 * n + 2) (11 * n + 1)
        * (prI t (2 * n + 1) (2 * n + 6) * (t + ((2 * n + 7 : ℕ) : ℚ)))
        * prI t (4 * n + 2) (9 * n + 1)
        * (prI t (4 * n + 1) (4 * n + 12) * (t + ((4 * n + 13 : ℕ) : ℚ)))
        * ((prI t (15 * n + 1) (26 * n + 1) * prI t (26 * n + 2) (26 * n + 79))
          * (t + ((26 * n + 80 : ℕ) : ℚ))) := by
    simp only [mNum, mDen, dPr, bPr, s1, show 2 * n + 1 + 1 = 2 * n + 2 from by omega,
      show 4 * n + 1 + 1 = 4 * n + 2 from by omega]
    ring
  have eR : mNum n t * mDen n (t + 1) * dPr n (t + 1) * aPr n t
      = (prI t 1 (13 * n) * (t + ((13 * n + 1 : ℕ) : ℚ)))
        * (prI t (2 * n + 1) (11 * n) * (t + ((11 * n + 1 : ℕ) : ℚ)))
        * prI t (2 * n + 2) (2 * n + 7)
        * (prI t (4 * n + 1) (9 * n) * (t + ((9 * n + 1 : ℕ) : ℚ)))
        * prI t (4 * n + 2) (4 * n + 13)
        * ((t + ((15 * n + 1 : ℕ) : ℚ)) * (prI t (15 * n + 2) (26 * n + 2) * prI t (26 * n + 3) (26 * n + 80))) := by
    simp only [mNum, mDen, dPr, aPr, s1, show 15 * n + 1 + 1 = 15 * n + 2 from by omega,
      show 26 * n + 1 + 1 = 26 * n + 2 from by omega, show 2 * n + 1 + 1 = 2 * n + 2 from by omega,
      show 2 * n + 6 + 1 = 2 * n + 7 from by omega, show 4 * n + 1 + 1 = 4 * n + 2 from by omega,
      show 4 * n + 12 + 1 = 4 * n + 13 from by omega, show 26 * n + 2 + 1 = 26 * n + 3 from by omega,
      show 26 * n + 79 + 1 = 26 * n + 80 from by omega]
    ring
  rw [eL, eR, tb2, tb4, dm1, dm2, tb13, tb2', tb4', r1, r2]
  ring

/-! ## 7. The row's theorems, in TARGET vocabulary -/

/-- **hρ at the chain's member.**  `D_n` is the engine's own `pa0Facs`. -/
theorem star_rho (n j : ℕ) (hj : j ≤ 3) (t : ℚ) :
    (candidateM.numPoly (n + j)).eval t * (candidateM.denPoly n).eval t
        * (afProd pa0Facs t).eval (n : ℚ)
      = (candidateM.numPoly n).eval t * (candidateM.denPoly (n + j)).eval t
        * (afProd (paF j) t).eval (n : ℚ) := by
  rw [numPoly_eval, numPoly_eval, denPoly_eval, denPoly_eval, pa0_prI, paPr_zero, paF_prI j n hj]
  exact rho_cross n j hj t

/-- **hu at the chain's member**, with `c ≡ 1` (cand-t1's `cFacs` is empty). -/
theorem star_u (n : ℕ) (t : ℚ) :
    (candidateM.numPoly n).eval (t + 1) * (candidateM.denPoly n).eval t
        * (afProd pa0Facs t).eval (n : ℚ) * (afProd bFacs t).eval (n : ℚ)
      = (candidateM.numPoly n).eval t * (candidateM.denPoly n).eval (t + 1)
        * (afProd pa0Facs (t + 1)).eval (n : ℚ) * (afProd aFacs t).eval (n : ℚ) := by
  rw [numPoly_eval, numPoly_eval, denPoly_eval, denPoly_eval, pa0_prI, pa0_prI, paPr_zero,
    paPr_zero, aPr_eq, bPr_eq]
  exact hu_cross n t

theorem cFacs_nil : cFacs = [] := rfl

/-- **The FUNCTION `hr` is about.**  With `u = numPoly n / (denPoly n · D_n)`, the (★) datum
`ρ j = u · Pa j` equals `numPoly (n+j) / denPoly (n+j)` wherever the three denominators are
nonzero — all but finitely many `t`, each of them a polynomial with nonzero leading term. -/
theorem rho_eq_member (n j : ℕ) (hj : j ≤ 3) (t : ℚ)
    (h0 : (candidateM.denPoly n).eval t ≠ 0) (hD : (afProd pa0Facs t).eval (n : ℚ) ≠ 0)
    (hj' : (candidateM.denPoly (n + j)).eval t ≠ 0) :
    (candidateM.numPoly n).eval t / ((candidateM.denPoly n).eval t * (afProd pa0Facs t).eval (n : ℚ))
        * (afProd (paF j) t).eval (n : ℚ)
      = (candidateM.numPoly (n + j)).eval t / (candidateM.denPoly (n + j)).eval t := by
  rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero h0 hD) hj']
  have := star_rho n j hj t
  linear_combination -this

#print axioms afProd_append
#print axioms afProd_run
#print axioms run_prI
#print axioms pa0_runs
#print axioms pa1_runs
#print axioms pa2_runs
#print axioms pa3_runs
#print axioms block_eval
#print axioms numPoly_eval
#print axioms denPoly_eval
#print axioms pa0_prI
#print axioms pa1_prI
#print axioms pa2_prI
#print axioms pa3_prI
#print axioms paPr_zero
#print axioms aPr_eq
#print axioms bPr_eq
#print axioms paF_prI
#print axioms rho_cross
#print axioms hu_cross
#print axioms star_rho
#print axioms star_u
#print axioms cFacs_nil
#print axioms rho_eq_member

end Zeta2StarId
