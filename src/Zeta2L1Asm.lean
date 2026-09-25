/-
# ROW L1-ASM, the RECURRENCE HALF — `hrecq`/`hrecp` at the REAL `qₙ`, `pₙ`, composed and executed

`docs/future/zeta2-lean-chain.md` row L1-ASM.  Added 2026-09-18.

**HEADLINE: `Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.**  This file lands
the recurrence half of row L1-ASM and NOT the row: the arithmetic half of the same binder list —
`hΔne hQ hP` at `ΔT`, from PT-DEF / PT-QB / PT-P — is still owed, PT-QB and PT-P are open, and
nothing here touches them.  L1-ASM stays `in progress`.

**WHAT IS PROVED, in three shapes of ONE fact.**  For every `n ≥ N₀ = 4`:

  * `hrecq_rat` / `hrecp_rat` — **PAIR-8's hypothesis, byte for byte**
    (`Zeta2Pair8.pairing_q_of_chain_rec`'s `hrecq`, `pairing_p_of_chain_rec`'s `hrecp`):
        `∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * candidateM.qn (n + j) = 0`
    and the same at `candidateM.pn`.  Over ℚ, before any cast.
  * `hrecq_alt` / `hrecp_alt` — the CLEARED `'alt'` convention STAR-ID (iii) proved is the one
    that holds: `∑ⱼ (−1)^j cⱼ(n) q_{n+j} = 0`, written out, at `alt j n = (−1)^j · cⱼ(n)` with
    `cⱼ` the sharded (ii) modules' own `Cq c<j>` literals (`cq`).  This is the shape QGROW's
    `hL` and L4-BR's `List ℤ → ℝ[X]` bridge read.
  * `hrecq` / `hrecp` — the ℝ casts, in the EXACT binder types of
    `Zeta2L12.candidate_target_of_certified_constants` at `αⱼ := αR j`.

**THE COMPOSITION, EXECUTED — not asserted (LEAN.md §3).**  Both previous compositions in this
program failed at exactly this step, and the cell priced the glue at 150–250 lines.  The line:

  1. `Zeta2StarIdPhi.star_telescopes_member` (STAR-ID) gives the four-term telescoping of the
     MEMBER functions `R_{n+j}/Π(n+j)` against the coords' operator `Ãⱼ`, off `bad n`.
  2. `Zeta2T1RepS.repSOf` makes each of those a `Rep` (`repM`, §2) and the antidifference a
     `Rep` (`Sr`, §3) whose evaluation IS `SE` (`evalRep_Sr`); `htel` restates the telescoping
     on the `Rep`s.
  3. `Zeta2T1Inj.rec_of_telescoping_of_linear` (PHI-REP) with `Zeta2T1RepS.hbdy_cand` (PHI-BDY)
     turns it into `∑ⱼ Ãⱼ • Φ_{4n}(ρ_{n+j}) = 0` (`phi_rel`, §4) — at the ONE cell `m = 4n`.
  4. **The D7 normalisation, which no landed theorem performed** (§1–§2): PHI-EVAL reads
     `(q_{n+j}, p_{n+j})` off `Φ_{4(n+j)}(ρ_{n+j})`, a DIFFERENT cell for each `j`, so the
     relation at `4n` has to be moved up `4j` cells member by member.  `Phi_cell_succ` is one
     strip: `Φ_m(r) = Φ_{m+1}(r)` when the crossed integer `−(m+1)` is a vanishing-derivative
     point of `r` (its hypotheses are `Zeta2T1Shift.hbdy`'s at `m + 1`), `Phi_cell_add` iterates
     it, and `hz_repM` supplies the double zero from the member's own two numerator blocks.
     `phi_shift` is the move at member `n + j` (`phi_rel_shifted`).
  5. `Zeta2StarIdPhi.star_phi_rho` (STAR-ID → PHI-EVAL) reads the coordinates off (`coords`);
     `Prod.mk.inj` splits them.  `Zeta2StarIdSign.alt_weight_j0..j3` convert `Ãⱼ·(W·Π(n))`
     into `−(−1)^j cⱼ · sgn·Π(n+j)` with NO division (§5), and the operator tie
     `al<j>_tie : StarForallCandt1.al<j> = Zeta2Pair7J<j>.alChain` (four `decide +kernel`,
     the chain-side twin of `Zeta2Pair8Tie.al<j>_tie`) puts `gammaN` on `Ãⱼ` (§6).

**`N₀ = 4`, NOT 6 — and where the 6 was.**  The cell's `N₀ = 6` is the D7 census's engine
thresholds (`Zeta2ContourD7.cand_t1_m{8..11}_*`: `n ≥ 9`) read at the member index `n + 3`.
This file consumes NONE of those 402 affine facts: the strip crossing is a theorem about `Rep`
(`Phi_cell_succ`) whose per-strip side condition is `(X + m)² ∣ numPoly (n+j)`, discharged from
block containment by `omega` — and block containment needs only `n ≥ j` (`hz_repM`'s lower
bound `2(n+j)+1 ≤ 4n+i+1`).  The binding threshold is then PHI-BDY's `hbdy_cand`, `4 ≤ n`,
which is SHARP for the written pole set (its `D` run `[2n+1, 2n+6]` contains the strip integer
`4n` at `n ≤ 3`).  So the row's `N₀` is PHI-BDY's 4, and `hrecq_rat` at any larger `N₀` is a
weakening, not a re-proof.  The cell's SHAPE REQUIREMENT still binds, in this form: the double
zero is asked of `repM (n + j)` at the crossed integers `4n+1 … 4(n+j)`, and asking it of
`repM n` instead is a TYPE error here (falsifier A1), not a silently re-inherited threshold.

**`hrow` at the new `N₀`, re-checked in the kernel rather than transferred**: `qn_four_ne_zero`
and `qn_six_ne_zero` (§7), both through `Zeta2Arith.qnInt_cast` and one `decide +kernel` each.

**Second implementation** (exact ℚ, laptop, seconds): `l1asm_check.py` recomputes `qₙ`, `pₙ`
from `Zeta2Defs`'s closed forms and `gammaN`/`cⱼ` from the committed literals, scores BOTH
exported shapes on every window `n ∈ [0, 12]`, the chain-side tie coefficient by coefficient,
and the double-zero condition's `n ≥ j` bound; `--falsify` arms.  Lean falsifier:
`falsify_l1asm.sh --lean`.

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2L1Asm.lean

Receipts: `out_axioms_l1asm.txt`.  Read `lean`'s rc SEPARATELY from the audit: the predicate
scores a parse-broken file GREEN (found_bugs 2026-09-14).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2T1RepS
import Zeta2StarIdPhi
import Zeta2StarIdSign
import Zeta2Pair8Tie

-- FILE-LEVEL on purpose: placed between a docstring and its theorem a `set_option` is a parse
-- error Lean silently RECOVERS from (zeta2-lean-chain.md, PAIR-7's and PAIR-6's landings).
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Zeta2L1Asm

open Polynomial Finset Zeta2Defs Zeta2T1Shift Zeta2T1RepS Zeta2StarIdPhi
open Zeta2Moments (Lpoly Lpoly_add Lpoly_monomial Lpoly_shift momI_eq_bernoulli)

/-- The row's threshold.  PHI-BDY's, see the header. -/
def N0 : ℕ := 4

/-! ## §1 — the cell-shift law: moving the contour by one cell crosses one double pole

`Φ m r` reads the cell only through `Lpoly (−m−1)` and `harm 2 (k − m − 1)`.  Shifting the
ARGUMENT by one (`shiftRep`) and the CELL by one cancel exactly (`Phi_shiftRep_pred`, no
hypothesis), so `Φ_m(r) − Φ_{m+1}(r) = Φ_{m+1}(r(·+1)) − Φ_{m+1}(r) = Φ_{m+1}(Δr)`, which is the
strip residue `Zeta2T1Shift.Phi_repDelta` computes.  It vanishes exactly when the crossed integer
is a vanishing-derivative point — `Zeta2T1Shift.hbdy`'s hypothesis at `m + 1`. -/

/-- `I_j(M+1) − I_j(M) = j·(M+1)^(j−1)`: from `momI_eq_bernoulli` and Mathlib's
`bernoulli_eval_one_add`. -/
theorem momI_succ (M : ℤ) (j : ℕ) :
    Zeta2Moments.momI (M + 1) j
      = Zeta2Moments.momI M j + (j : ℚ) * ((M : ℚ) + 1) ^ (j - 1) := by
  rw [momI_eq_bernoulli, momI_eq_bernoulli]
  have hc : (((M + 1 : ℤ) : ℚ) + 1) = 1 + ((M : ℚ) + 1) := by push_cast; ring
  rw [hc, Polynomial.bernoulli_eval_one_add]

/-- `ℒ_{M+1}(p) − ℒ_M(p) = p′(M+1)` — the cell shift on the polynomial part. -/
theorem Lpoly_succ (M : ℤ) (p : ℚ[X]) :
    Lpoly (M + 1) p = Lpoly M p + (derivative p).eval ((M : ℚ) + 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Lpoly_add, Lpoly_add, derivative_add, eval_add, hp, hq]
      ring
  | monomial j a =>
      rw [Lpoly_monomial, Lpoly_monomial, momI_succ, derivative_monomial, eval_monomial]
      ring

/-- The argument shift IS the cell shift on the polynomial part: `ℒ_M(p(·+1)) = ℒ_{M+1}(p)`. -/
theorem Lpoly_comp_succ (M : ℤ) (p : ℚ[X]) :
    Lpoly M (p.comp (X + 1)) = Lpoly (M + 1) p := by
  have h := Lpoly_shift M p
  rw [Lpoly_succ]
  linarith

/-- **Argument shift and cell shift cancel, with NO hypothesis**: `Φ_{m+1}(r(·+1)) = Φ_m(r)`.
The ζ(2) coordinate is `m`-free; the rational one moves its `Lpoly` cell by `Lpoly_comp_succ`
and its harmonic index by `k + 1 − (m+1) − 1 = k − m − 1`. -/
theorem Phi_shiftRep_pred (m : ℕ) (r : Rep) : Phi (m + 1) (shiftRep r) = Phi m r := by
  have h1 : (Phi (m + 1) (shiftRep r)).1 = (Phi m r).1 := by
    rw [Phi_zeta2_argshift]
    rfl
  have h2 : (Phi (m + 1) (shiftRep r)).2 = (Phi m r).2 := by
    show Lpoly (-((m + 1 : ℕ) : ℤ) - 1) (r.1.comp (X + 1))
        - (r.2.mapDomain (fun k => k + 1)).sum
            (fun k c => c * Zeta2Moments.harm 2 (k - (m + 1) - 1))
      = Lpoly (-(m : ℤ) - 1) r.1 - r.2.sum (fun k c => c * Zeta2Moments.harm 2 (k - m - 1))
    have hL : Lpoly (-((m + 1 : ℕ) : ℤ) - 1) (r.1.comp (X + 1))
        = Lpoly (-(m : ℤ) - 1) r.1 := by
      rw [Lpoly_comp_succ]
      congr 1
      push_cast
      ring
    have hM : (r.2.mapDomain (fun k => k + 1)).sum
          (fun k c => c * Zeta2Moments.harm 2 (k - (m + 1) - 1))
        = r.2.sum (fun k c => c * Zeta2Moments.harm 2 (k + 1 - (m + 1) - 1)) := by
      rw [Finsupp.sum_mapDomain_index_inj succ_inj]
    have hH : r.2.sum (fun k c => c * Zeta2Moments.harm 2 (k + 1 - (m + 1) - 1))
        = r.2.sum (fun k c => c * Zeta2Moments.harm 2 (k - m - 1)) := by
      refine Finsupp.sum_congr fun k _ => ?_
      have he : k + 1 - (m + 1) - 1 = k - m - 1 := by omega
      rw [he]
    rw [hL, hM, hH]
  exact Prod.ext h1 h2

/-- **The cell-shift law, one strip.**  For a `Rep` supported above `m + 1` whose evaluation has
vanishing derivative at the crossed integer `−(m+1)`, `Φ_m(r) = Φ_{m+1}(r)`.  This is row B4's
D7 contour move, one strip, in `Rep` vocabulary. -/
theorem Phi_cell_succ (m : ℕ) (r : Rep) (hsupp : ∀ k ∈ r.2.support, m + 2 ≤ k)
    (hz : (derivative r.1).eval (-((m + 1 : ℕ) : ℚ))
            = r.2.sum (fun k c => c / ((k : ℚ) - ((m + 1 : ℕ) : ℚ)) ^ 2)) :
    Phi m r = Phi (m + 1) r := by
  have h := Zeta2T1Shift.hbdy (m + 1) r (fun k hk => by have := hsupp k hk; omega) hz
  rw [repDelta, Phi_sub, sub_eq_zero, Phi_shiftRep_pred] at h
  exact h

/-- The law iterated `d` strips: `Φ_m(r) = Φ_{m+d}(r)` once every crossed integer
`−(m+1), …, −(m+d)` is a vanishing-derivative point and the support clears `m + d`. -/
theorem Phi_cell_add (m : ℕ) (r : Rep) : ∀ d : ℕ,
    (∀ k ∈ r.2.support, m + d + 1 ≤ k) →
    (∀ i, i < d → (derivative r.1).eval (-((m + i + 1 : ℕ) : ℚ))
        = r.2.sum (fun k c => c / ((k : ℚ) - ((m + i + 1 : ℕ) : ℚ)) ^ 2)) →
    Phi m r = Phi (m + d) r := by
  intro d
  induction d with
  | zero => intro _ _; rfl
  | succ d ih =>
      intro hsupp hz
      rw [ih (fun k hk => by have := hsupp k hk; omega) (fun i hi => hz i (by omega))]
      exact Phi_cell_succ (m + d) r (fun k hk => by have := hsupp k hk; omega)
        (hz d (Nat.lt_succ_self d))

/-! ## §2 — the member's `Rep`, and the D7 move from cell `4n` up to cell `4(n+j)` -/

/-- `R_N/Π(N)` as `repSOf` over its own pole window — the object the cell shift is applied to. -/
noncomputable def repM (N : ℕ) : Rep :=
  repSOf (candidateM.window N) (candidateM.numPoly N)

theorem window_nonempty (N : ℕ) : (candidateM.window N).Nonempty := by
  refine ⟨candidateM.a4 * N + 1, ?_⟩
  have hle := Nat.mul_le_mul_right N candidateM_wf.a4_lt.le
  simp only [Member.window, Finset.mem_Icc]
  omega

/-- `repM N` represents `numPoly N / denPoly N` off the window. -/
theorem evalRep_repM (N : ℕ) (t : ℚ) (ht : ∀ k ∈ candidateM.window N, t + ((k : ℕ) : ℚ) ≠ 0) :
    evalRep (repM N) t = (candidateM.numPoly N).eval t / (candidateM.denPoly N).eval t := by
  rw [repM, evalRep_repSOf _ (window_nonempty N) _ t ht,
    denPoly_eq_runProd candidateM candidateM_wf N]

/-- Its support is inside the window, so it clears any floor below `15N + 1`. -/
theorem repM_support (N m : ℕ) (h : m + 1 ≤ 15 * N + 1) :
    ∀ k ∈ (repM N).2.support, m + 1 ≤ k := by
  refine repSOf_support _ _ m ?_
  intro k hk hlt
  exfalso
  have e4 : candidateM.a4 = 15 := rfl
  simp only [Member.window, Finset.mem_Icc, e4] at hk
  omega

/-- `(X + m)² ∣ numPoly N` when `−m` lies in BOTH the first block `[1, α₁N]` and the second
`[β₂N+1, α₂N]` — two different factors of one product (the shape of `sq_dvd_numS`). -/
theorem sq_dvd_numPoly (mem : Member) (N m : ℕ) (h1 : 1 ≤ m) (h2 : m < 1 + mem.a1 * N)
    (h3 : mem.b2 * N + 1 ≤ m) (h4 : m < mem.b2 * N + 1 + (mem.a2 - mem.b2) * N) :
    (X + C ((m : ℕ) : ℚ)) ^ 2 ∣ mem.numPoly N := by
  have d1 := block_dvd 1 (mem.a1 * N) m h1 h2
  have d2 := block_dvd (mem.b2 * N + 1) ((mem.a2 - mem.b2) * N) m h3 h4
  rw [Member.numPoly]
  exact dvd_mul_of_dvd_left (by rw [sq]; exact mul_dvd_mul d1 d2) _

/-- **The crossed integers are double zeros of the member**: `hz` at every `m ∈ [2N+1, 11N]`,
which contains every strip `4n+1 … 4(n+j)` of the D7 move as soon as `n ≥ j`. -/
theorem hz_repM (N m : ℕ) (h3 : 2 * N + 1 ≤ m) (h4 : m ≤ 11 * N) :
    (derivative (repM N).1).eval (-((m : ℕ) : ℚ))
      = (repM N).2.sum (fun k c => c / ((k : ℚ) - (m : ℚ)) ^ 2) := by
  have e1 : candidateM.a1 = 13 := rfl
  have e2 : candidateM.a2 = 11 := rfl
  have e4 : candidateM.a4 = 15 := rfl
  have e5 : candidateM.b2 = 2 := rfl
  have e7 : candidateM.b4 = 26 := rfl
  refine hz_repSOf _ (window_nonempty N) _ m ?_ ?_
  · simp only [Member.window, Finset.mem_Icc, e4, e7]
    omega
  · refine sq_dvd_numPoly candidateM N m (by omega) ?_ ?_ ?_
    · rw [e1]; omega
    · rw [e5]; omega
    · rw [e5, e2]; omega

/-- **The D7 move at member `n + j`, executed**: `Φ_{4n}(ρ_{n+j}) = Φ_{4(n+j)}(ρ_{n+j})` for
`n ≥ j`.  The `4j` strips are crossed one at a time by `Phi_cell_add`; each crossing's double
zero is `hz_repM` at `m = 4n + i + 1`, whose lower bound `2(n+j)+1 ≤ 4n+i+1` is where `n ≥ j`
enters — at the MEMBER index `n + j`, which is the cell's shape requirement in this route. -/
theorem phi_shift (n j : ℕ) (hn : j ≤ n) :
    Phi (4 * n) (repM (n + j)) = Phi (4 * (n + j)) (repM (n + j)) := by
  have h := Phi_cell_add (4 * n) (repM (n + j)) (4 * j)
    (repM_support (n + j) (4 * n + 4 * j) (by omega))
    (fun i hi => hz_repM (n + j) (4 * n + i + 1) (by omega) (by omega))
  rw [h, mul_add]

/-! ## §3 — the antidifference's `Rep`, and the telescoping restated on `Rep`s

`Zeta2T1RepS.hbdy_cand` and `.evalRep_repS_eq_S_cand` are stated at
`repSOf (idxS candidateM n (dIdxCand n)) (numS candidateM n bT xT)` for OPAQUE `bT xT : ℚ[X]`.
The star solve's `b(·−1)` and `x(n, ·)` are supplied as polynomials in `t` here: `bT` is the
four-factor `bPr` shifted by one, `xT` is `polB2 xCoeffs` with the member index `n` substituted
into every coefficient list (`polB2` is Horner in the contour variable, so at fixed `n` it IS
`polB` of the evaluated coefficients). -/

/-- `b(t − 1)` of the Gosper normal form, as a polynomial in `t`. -/
noncomputable def bT (n : ℕ) : ℚ[X] :=
  X * (X + C ((2 * n + 6 : ℕ) : ℚ)) * (X + C ((4 * n + 12 : ℕ) : ℚ))
    * (X + C ((26 * n + 79 : ℕ) : ℚ))

theorem bT_eval (n : ℕ) (s : ℚ) : (bT n).eval s = bE n (s - 1) := by
  rw [bE, Zeta2StarId.bPr_eq, Zeta2StarId.bPr, bT]
  simp only [eval_mul, eval_add, eval_X, eval_C]
  push_cast
  ring

/-- The certificate `x(n, ·)` at fixed `n`, as a polynomial in the contour variable. -/
noncomputable def xT (n : ℕ) : ℚ[X] :=
  StarForallCandt1.polB (StarForallCandt1.xCoeffs.map
    (fun l => (StarForallCandt1.polB l).eval (n : ℚ)))

theorem xT_eval (n : ℕ) (s : ℚ) : (xT n).eval s = xE n s := by
  rw [xE, StarForallCandt1.polB2_eval, xT, StarForallCandt1.polB_eval, List.foldr_map]

/-- The antidifference's `Rep` — PHI-BDY's own object at the star solve's `bT`, `xT`. -/
noncomputable def Sr (n : ℕ) : Rep :=
  repSOf (idxS candidateM n (dIdxCand n)) (numS candidateM n (bT n) (xT n))

/-- Every written pole of `Sr n` is in STAR-ID's exceptional set. -/
theorem idxS_sub_badK (n : ℕ) : ∀ k ∈ idxS candidateM n (dIdxCand n), k ∈ badK n := by
  intro k hk
  rcases Finset.mem_union.1 hk with h | h
  · exact win_sub n 0 (by omega) h
  · simp only [dIdxCand, Finset.mem_union] at h
    rcases h with (h | h) | h
    · exact d2_sub n h
    · exact d4_sub n h
    · exact d26_sub n h

/-- **`Sr n` represents the antidifference `SE n` off `bad n`** (`n ≥ 3`, PHI-BDY's own floor
for the written pole set to be simple). -/
theorem evalRep_Sr (n : ℕ) (hn : 3 ≤ n) (t : ℚ) (ht : t ∉ bad n) :
    evalRep (Sr n) t = SE n t := by
  have ht' : ∀ k ∈ idxS candidateM n (dIdxCand n), t + ((k : ℕ) : ℚ) ≠ 0 :=
    fun k hk => ne_of_not_bad ht k (idxS_sub_badK n k hk)
  rw [Sr, evalRep_repS_eq_S_cand n hn (bT n) (xT n) t ht', bT_eval, xT_eval, SE, uStar,
    Zeta2StarId.pa0_prI, Zeta2StarId.paPr_zero, Zeta2StarId.dPr]
  simp only [Zeta2PrI.prI]
  ring

/-- The exceptional set of the telescoping on `Rep`s: `t` and `t + 1` both off `bad n`. -/
noncomputable def E (n : ℕ) : Finset ℚ := bad n ∪ (bad n).image (fun s : ℚ => s - 1)

theorem not_bad_of_not_E {n : ℕ} {t : ℚ} (ht : t ∉ E n) : t ∉ bad n :=
  fun h => ht (Finset.mem_union_left _ h)

theorem succ_not_bad_of_not_E {n : ℕ} {t : ℚ} (ht : t ∉ E n) : t + 1 ∉ bad n :=
  fun h => ht (Finset.mem_union_right _ (Finset.mem_image.2 ⟨t + 1, h, by ring⟩))

/-- **STAR-ID's telescoping, restated on the `Rep`s** — the `htel` hypothesis of
`Zeta2T1Inj.rec_of_telescoping_of_linear`, discharged from `star_telescopes_member`. -/
theorem htel (n : ℕ) (hn : 3 ≤ n) (t : ℚ) (ht : t ∉ E n) :
    Atil n 0 * evalRep (repM (n + 0)) t + Atil n 1 * evalRep (repM (n + 1)) t
      + Atil n 2 * evalRep (repM (n + 2)) t + Atil n 3 * evalRep (repM (n + 3)) t
      = evalRep (Sr n) (t + 1) - evalRep (Sr n) t := by
  have ht0 := not_bad_of_not_E ht
  have ht1 := succ_not_bad_of_not_E ht
  have h := star_telescopes_member n t ht0 ht1
  rw [Fin.sum_univ_four] at h
  have e : ∀ j, j ≤ 3 → evalRep (repM (n + j)) t = rhoMem n j t := fun j hj => by
    rw [evalRep_repM (n + j) t (fun k hk => ne_of_not_bad ht0 k (win_sub n j hj hk)), rhoMem]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
    evalRep_Sr n hn (t + 1) ht1, evalRep_Sr n hn t ht0]
  exact h

/-! ## §4 — the Φ-relation, executed, then moved to the read-off cells -/

/-- **`∑ⱼ Ãⱼ • Φ_{4n}(ρ_{n+j}) = 0`** — PHI-REP's `rec_of_telescoping_of_linear` at `m = 4n`
with PHI-BDY's `hbdy_cand`; `4 ≤ n` is `hbdy_cand`'s own floor and the row's `N₀`. -/
theorem phi_rel (n : ℕ) (hn : 4 ≤ n) :
    Atil n 0 • Phi (4 * n) (repM (n + 0)) + Atil n 1 • Phi (4 * n) (repM (n + 1))
      + Atil n 2 • Phi (4 * n) (repM (n + 2)) + Atil n 3 • Phi (4 * n) (repM (n + 3)) = 0 :=
  Zeta2T1Inj.rec_of_telescoping_of_linear (4 * n) (repM (n + 0)) (repM (n + 1)) (repM (n + 2))
    (repM (n + 3)) (Sr n) (Atil n 0) (Atil n 1) (Atil n 2) (Atil n 3) (E n)
    (fun t ht => htel n (by omega) t ht) (hbdy_cand n hn (bT n) (xT n))

/-- The same relation with each member read at ITS OWN cell `4(n+j)` — the D7 move applied
member by member, at the member index. -/
theorem phi_rel_shifted (n : ℕ) (hn : 4 ≤ n) :
    Atil n 0 • Phi (4 * (n + 0)) (repM (n + 0)) + Atil n 1 • Phi (4 * (n + 1)) (repM (n + 1))
      + Atil n 2 • Phi (4 * (n + 2)) (repM (n + 2))
      + Atil n 3 • Phi (4 * (n + 3)) (repM (n + 3)) = 0 := by
  have h := phi_rel n hn
  rw [phi_shift n 0 (by omega), phi_shift n 1 (by omega), phi_shift n 2 (by omega),
    phi_shift n 3 (by omega)] at h
  exact h

/-- **PHI-EVAL's read-off through STAR-ID's `hr` spelling**, at `repM (n + j)`. -/
theorem coords (n j : ℕ) (hj : j ≤ 3) :
    (candidateM.sgn (n + j) * candidateM.Pin (n + j) * (Phi (4 * (n + j)) (repM (n + j))).1,
      -(candidateM.sgn (n + j) * candidateM.Pin (n + j)) * (Phi (4 * (n + j)) (repM (n + j))).2)
      = (candidateM.qn (n + j), candidateM.pn (n + j)) :=
  star_phi_rho n j hj (repM (n + j)) (fun t ht => by
    rw [evalRep_repM (n + j) t (fun k hk => ne_of_not_bad ht k (win_sub n j hj hk)),
      rhoStar_eq_rhoMem n j hj t ht, rhoMem])

theorem coord_q (n j : ℕ) (hj : j ≤ 3) :
    candidateM.sgn (n + j) * candidateM.Pin (n + j) * (Phi (4 * (n + j)) (repM (n + j))).1
      = candidateM.qn (n + j) :=
  (Prod.mk.inj (coords n j hj)).1

theorem coord_p (n j : ℕ) (hj : j ≤ 3) :
    -(candidateM.sgn (n + j) * candidateM.Pin (n + j)) * (Phi (4 * (n + j)) (repM (n + j))).2
      = candidateM.pn (n + j) :=
  (Prod.mk.inj (coords n j hj)).2

/-- The ζ(2) coordinate of the relation. -/
theorem rec_q_raw (n : ℕ) (hn : 4 ≤ n) :
    Atil n 0 * (Phi (4 * (n + 0)) (repM (n + 0))).1
      + Atil n 1 * (Phi (4 * (n + 1)) (repM (n + 1))).1
      + Atil n 2 * (Phi (4 * (n + 2)) (repM (n + 2))).1
      + Atil n 3 * (Phi (4 * (n + 3)) (repM (n + 3))).1 = 0 := by
  have h := congrArg Prod.fst (phi_rel_shifted n hn)
  simpa only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero] using h

/-- The rational coordinate of the relation. -/
theorem rec_p_raw (n : ℕ) (hn : 4 ≤ n) :
    Atil n 0 * (Phi (4 * (n + 0)) (repM (n + 0))).2
      + Atil n 1 * (Phi (4 * (n + 1)) (repM (n + 1))).2
      + Atil n 2 * (Phi (4 * (n + 2)) (repM (n + 2))).2
      + Atil n 3 * (Phi (4 * (n + 3)) (repM (n + 3))).2 = 0 := by
  have h := congrArg Prod.snd (phi_rel_shifted n hn)
  simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero] using h

/-! ## §5 — the CLEARED `'alt'` convention: `∑ⱼ (−1)^j cⱼ(n) q_{n+j} = 0`, no division

`Zeta2StarIdSign.alt_weight_j<j>` is `Ãⱼ·(W·Π(n)) = −((−1)^j·cⱼ·(sgn(n+j)·Π(n+j)))`, each in
its own sharded module's `Wq`.  One `W` (`Zeta2StarIdIIJ1.Wq`) is put on all four through
`w13_tie_01`/`w13_tie_31`/`Wq_tie` and the `hornerZ` ties, and the relation of §4 is multiplied
by `W·Π(n)`: the weight identity then trades `Ãⱼ` for `−(−1)^j cⱼ sgn Π(n+j)` term by term, and
`coord_q` collapses `sgn Π(n+j) Φ.1` to `q_{n+j}`.  No `W ≠ 0`, no `Π ≠ 0`, no division. -/

/-- `cⱼ(n)`, indexed: the sharded (ii) modules' own `Cq c<j>` literals. -/
def cq (j n : ℕ) : ℚ :=
  match j with
  | 0 => Zeta2StarIdIIJ0.Cq Zeta2StarIdIIJ0.c0 n
  | 1 => Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.c1 n
  | 2 => Zeta2StarIdIIJ2.Cq Zeta2StarIdIIJ2.c2 n
  | _ => Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.c3 n

/-- The `'alt'` coefficient `αⱼ(n) = (−1)^j · cⱼ(n)` — STAR-ID (iii)'s convention. -/
def alt (j n : ℕ) : ℚ := (-1) ^ j * cq j n

/-- The one `W`. -/
def W (n : ℕ) : ℚ := Zeta2StarIdIIJ1.Wq n

theorem Wq0_tie (n : ℕ) : Zeta2StarIdIIJ0.Wq n = W n := by
  show ((Zeta2StarIdIIJ0.hornerZ Zeta2StarIdIIJ0.w13 (n : ℤ) : ℤ) : ℚ) / 13
    = ((Zeta2StarIdIIJ1.hornerZ Zeta2StarIdIIJ1.w13 (n : ℤ) : ℤ) : ℚ) / 13
  rw [Zeta2StarIdSign.w13_tie_01, ← Zeta2StarIdSign.hz_pi_j0, Zeta2StarIdSign.hz_pi_j1]

theorem Wq2_tie (n : ℕ) : Zeta2StarIdIIJ2.Wq n = W n :=
  (Zeta2StarIdSign.Wq_tie n).symm

theorem Wq3_tie (n : ℕ) : Zeta2StarIdIIJ3.Wq n = W n := by
  show ((Zeta2StarIdIIJ3.hornerZ Zeta2StarIdIIJ3.w13 (n : ℤ) : ℤ) : ℚ) / 13
    = ((Zeta2StarIdIIJ1.hornerZ Zeta2StarIdIIJ1.w13 (n : ℤ) : ℤ) : ℚ) / 13
  rw [Zeta2StarIdSign.w13_tie_31, ← Zeta2StarIdSign.hz_pi_j3, Zeta2StarIdSign.hz_pi_j1]

/-- The four weight identities at ONE `W` and at this file's `Atil`/`cq` spellings.  Each
`Zeta2StarIdIIJ<j>.Atil<j> n` IS `Zeta2StarIdPhi.Atil n j` by definition. -/
theorem hw0 (n : ℕ) : Atil n 0 * (W n * candidateM.Pin n)
    = -((-1 : ℚ) ^ 0 * cq 0 n * (candidateM.sgn (n + 0) * candidateM.Pin (n + 0))) := by
  have h := Zeta2StarIdSign.alt_weight_j0 n
  rw [Wq0_tie] at h
  exact h

theorem hw1 (n : ℕ) : Atil n 1 * (W n * candidateM.Pin n)
    = -((-1 : ℚ) ^ 1 * cq 1 n * (candidateM.sgn (n + 1) * candidateM.Pin (n + 1))) :=
  Zeta2StarIdSign.alt_weight_j1 n

theorem hw2 (n : ℕ) : Atil n 2 * (W n * candidateM.Pin n)
    = -((-1 : ℚ) ^ 2 * cq 2 n * (candidateM.sgn (n + 2) * candidateM.Pin (n + 2))) := by
  have h := Zeta2StarIdSign.alt_weight_j2 n
  rw [Wq2_tie] at h
  exact h

theorem hw3 (n : ℕ) : Atil n 3 * (W n * candidateM.Pin n)
    = -((-1 : ℚ) ^ 3 * cq 3 n * (candidateM.sgn (n + 3) * candidateM.Pin (n + 3))) := by
  have h := Zeta2StarIdSign.alt_weight_j3 n
  rw [Wq3_tie] at h
  exact h

/-- **`hrecq_alt`** — `∑ⱼ (−1)^j cⱼ(n) q_{n+j} = 0` over ℚ, for every `n ≥ N₀`, written out. -/
theorem hrecq_alt : ∀ n, N0 ≤ n →
    alt 0 n * candidateM.qn n + alt 1 n * candidateM.qn (n + 1)
      + alt 2 n * candidateM.qn (n + 2) + alt 3 n * candidateM.qn (n + 3) = 0 := by
  intro n hn
  have hraw := rec_q_raw n (by simpa [N0] using hn)
  have q0 := coord_q n 0 (by omega)
  have q1 := coord_q n 1 (by omega)
  have q2 := coord_q n 2 (by omega)
  have q3 := coord_q n 3 (by omega)
  have w0 := hw0 n
  have w1 := hw1 n
  have w2 := hw2 n
  have w3 := hw3 n
  simp only [Nat.add_zero] at hraw q0 w0
  simp only [alt]
  linear_combination (-(W n * candidateM.Pin n)) * hraw
    + (Phi (4 * n) (repM n)).1 * w0 + (Phi (4 * (n + 1)) (repM (n + 1))).1 * w1
    + (Phi (4 * (n + 2)) (repM (n + 2))).1 * w2 + (Phi (4 * (n + 3)) (repM (n + 3))).1 * w3
    - ((-1 : ℚ) ^ 0 * cq 0 n) * q0 - ((-1 : ℚ) ^ 1 * cq 1 n) * q1
    - ((-1 : ℚ) ^ 2 * cq 2 n) * q2 - ((-1 : ℚ) ^ 3 * cq 3 n) * q3

/-- **`hrecp_alt`** — the same at `pₙ`. -/
theorem hrecp_alt : ∀ n, N0 ≤ n →
    alt 0 n * candidateM.pn n + alt 1 n * candidateM.pn (n + 1)
      + alt 2 n * candidateM.pn (n + 2) + alt 3 n * candidateM.pn (n + 3) = 0 := by
  intro n hn
  have hraw := rec_p_raw n (by simpa [N0] using hn)
  have p0 := coord_p n 0 (by omega)
  have p1 := coord_p n 1 (by omega)
  have p2 := coord_p n 2 (by omega)
  have p3 := coord_p n 3 (by omega)
  have w0 := hw0 n
  have w1 := hw1 n
  have w2 := hw2 n
  have w3 := hw3 n
  simp only [Nat.add_zero] at hraw p0 w0
  simp only [alt]
  linear_combination (W n * candidateM.Pin n) * hraw
    - (Phi (4 * n) (repM n)).2 * w0 - (Phi (4 * (n + 1)) (repM (n + 1))).2 * w1
    - (Phi (4 * (n + 2)) (repM (n + 2))).2 * w2 - (Phi (4 * (n + 3)) (repM (n + 3))).2 * w3
    - ((-1 : ℚ) ^ 0 * cq 0 n) * p0 - ((-1 : ℚ) ^ 1 * cq 1 n) * p1
    - ((-1 : ℚ) ^ 2 * cq 2 n) * p2 - ((-1 : ℚ) ^ 3 * cq 3 n) * p3

/-! ## §6 — PAIR-8's shape: `gammaN`, the (★) operator with its `Π`-rebase

`Zeta2Pair8Tie.gammaN n j = qeval n (Zeta2Pair7J<j>.alChain) · Π(n)/Π(n+j)`, PAIR-7's encoding
of the CHAIN solve's operator.  STAR-ID's `Ãⱼ` is `(polB StarForallCandt1.al<j>).eval n`, the
base module's literal.  Two encodings of the same rationals, tied by nothing until here — the
chain-side twin of `Zeta2Pair8Tie.al<j>_tie` (`l1asm_check.py` §T re-derives the four lists
from the committed coords, 0 of 4 disagree). -/

theorem al0_tie : StarForallCandt1.al0 = Zeta2Pair7J0.alChain := by decide +kernel
theorem al1_tie : StarForallCandt1.al1 = Zeta2Pair7J1.alChain := by decide +kernel
theorem al2_tie : StarForallCandt1.al2 = Zeta2Pair7J2.alChain := by decide +kernel
theorem al3_tie : StarForallCandt1.al3 = Zeta2Pair7J3.alChain := by decide +kernel

theorem gammaN_eq0 (n : ℕ) :
    Zeta2Pair8Tie.gammaN n 0 = Atil n 0 * (candidateM.Pin n / candidateM.Pin (n + 0)) := by
  show StarKernel.qeval (n : ℚ) Zeta2Pair7J0.alChain * (candidateM.Pin n / candidateM.Pin (n + 0))
    = (StarForallCandt1.polB StarForallCandt1.al0).eval (n : ℚ)
        * (candidateM.Pin n / candidateM.Pin (n + 0))
  rw [← al0_tie, StarForallCandt1.polB_eval]
  rfl

theorem gammaN_eq1 (n : ℕ) :
    Zeta2Pair8Tie.gammaN n 1 = Atil n 1 * (candidateM.Pin n / candidateM.Pin (n + 1)) := by
  show StarKernel.qeval (n : ℚ) Zeta2Pair7J1.alChain * (candidateM.Pin n / candidateM.Pin (n + 1))
    = (StarForallCandt1.polB StarForallCandt1.al1).eval (n : ℚ)
        * (candidateM.Pin n / candidateM.Pin (n + 1))
  rw [← al1_tie, StarForallCandt1.polB_eval]
  rfl

theorem gammaN_eq2 (n : ℕ) :
    Zeta2Pair8Tie.gammaN n 2 = Atil n 2 * (candidateM.Pin n / candidateM.Pin (n + 2)) := by
  show StarKernel.qeval (n : ℚ) Zeta2Pair7J2.alChain * (candidateM.Pin n / candidateM.Pin (n + 2))
    = (StarForallCandt1.polB StarForallCandt1.al2).eval (n : ℚ)
        * (candidateM.Pin n / candidateM.Pin (n + 2))
  rw [← al2_tie, StarForallCandt1.polB_eval]
  rfl

theorem gammaN_eq3 (n : ℕ) :
    Zeta2Pair8Tie.gammaN n 3 = Atil n 3 * (candidateM.Pin n / candidateM.Pin (n + 3)) := by
  show StarKernel.qeval (n : ℚ) Zeta2Pair7J3.alChain * (candidateM.Pin n / candidateM.Pin (n + 3))
    = (StarForallCandt1.polB StarForallCandt1.al3).eval (n : ℚ)
        * (candidateM.Pin n / candidateM.Pin (n + 3))
  rw [← al3_tie, StarForallCandt1.polB_eval]
  rfl

/-- `gammaN n j = Ãⱼ(n)·Π(n)/Π(n+j)` for every `j ≤ 3`. -/
theorem gammaN_eq (n j : ℕ) (hj : j ≤ 3) :
    Zeta2Pair8Tie.gammaN n j = Atil n j * (candidateM.Pin n / candidateM.Pin (n + j)) := by
  interval_cases j
  · exact gammaN_eq0 n
  · exact gammaN_eq1 n
  · exact gammaN_eq2 n
  · exact gammaN_eq3 n

/-- One term of PAIR-8's sum, in terms of the Φ-relation's term.  `Π(n+j) ≠ 0`
(`Member.Pin_pos`) cancels the rebase; `sgn = −1` is `sgn_candidate`. -/
theorem gammaN_mul_qn (n j : ℕ) (hj : j ≤ 3) :
    Zeta2Pair8Tie.gammaN n j * candidateM.qn (n + j)
      = -(candidateM.Pin n * (Atil n j * (Phi (4 * (n + j)) (repM (n + j))).1)) := by
  rw [gammaN_eq n j hj, ← coord_q n j hj, Zeta2StarIdSign.sgn_candidate, div_eq_mul_inv]
  have hc : candidateM.Pin (n + j) * (candidateM.Pin (n + j))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt (candidateM.Pin_pos _))
  linear_combination (-(Atil n j * candidateM.Pin n * (Phi (4 * (n + j)) (repM (n + j))).1)) * hc

theorem gammaN_mul_pn (n j : ℕ) (hj : j ≤ 3) :
    Zeta2Pair8Tie.gammaN n j * candidateM.pn (n + j)
      = candidateM.Pin n * (Atil n j * (Phi (4 * (n + j)) (repM (n + j))).2) := by
  rw [gammaN_eq n j hj, ← coord_p n j hj, Zeta2StarIdSign.sgn_candidate, div_eq_mul_inv]
  have hc : candidateM.Pin (n + j) * (candidateM.Pin (n + j))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt (candidateM.Pin_pos _))
  linear_combination (Atil n j * candidateM.Pin n * (Phi (4 * (n + j)) (repM (n + j))).2) * hc

/-- **`hrecq_rat` — ROW PAIR-8's `hrecq`, byte for byte**
(`Zeta2Pair8.pairing_q_of_chain_rec (N0 := N0)`'s hypothesis), for every `n ≥ N₀ = 4`. -/
theorem hrecq_rat : ∀ n, N0 ≤ n →
    ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * candidateM.qn (n + j) = 0 := by
  intro n hn
  have hraw := rec_q_raw n (by simpa [N0] using hn)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [gammaN_mul_qn n 0 (by omega), gammaN_mul_qn n 1 (by omega), gammaN_mul_qn n 2 (by omega),
    gammaN_mul_qn n 3 (by omega)]
  linear_combination (-(candidateM.Pin n)) * hraw

/-- **`hrecp_rat` — ROW PAIR-8's `hrecp`, byte for byte**
(`Zeta2Pair8.pairing_p_of_chain_rec (N0 := N0)`'s hypothesis). -/
theorem hrecp_rat : ∀ n, N0 ≤ n →
    ∑ j ∈ Finset.range 4, Zeta2Pair8Tie.gammaN n j * candidateM.pn (n + j) = 0 := by
  intro n hn
  have hraw := rec_p_raw n (by simpa [N0] using hn)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [gammaN_mul_pn n 0 (by omega), gammaN_mul_pn n 1 (by omega), gammaN_mul_pn n 2 (by omega),
    gammaN_mul_pn n 3 (by omega)]
  linear_combination (candidateM.Pin n) * hraw

/-! ## §7 — the ℝ casts in the chain's binder types, and `hrow` at the new `N₀`

`Zeta2L12.candidate_target_of_certified_constants` binds
`hrecq : ∀ n, N₀ ≤ n → α₀ n * ((candidateM.qn n : ℚ) : ℝ) + … + α₃ n * ((candidateM.qn (n + 3) : ℚ) : ℝ) = 0`
for free `αⱼ : ℕ → ℝ`.  `αR j` is the `'alt'` coefficient cast; the two theorems below are those
binders at `αⱼ := αR j`, `N₀ := N0`, SYNTACTICALLY — the instantiation into that theorem itself
waits on the arithmetic half (`hΔne hQ hP`) and is not claimed here. -/

/-- `αⱼ` over ℝ: the `'alt'` coefficient, cast. -/
noncomputable def αR (j : ℕ) : ℕ → ℝ := fun n => ((alt j n : ℚ) : ℝ)

theorem hrecq : ∀ n, N0 ≤ n →
    αR 0 n * ((candidateM.qn n : ℚ) : ℝ) + αR 1 n * ((candidateM.qn (n + 1) : ℚ) : ℝ)
      + αR 2 n * ((candidateM.qn (n + 2) : ℚ) : ℝ)
      + αR 3 n * ((candidateM.qn (n + 3) : ℚ) : ℝ) = 0 := by
  intro n hn
  simp only [αR]
  exact_mod_cast hrecq_alt n hn

theorem hrecp : ∀ n, N0 ≤ n →
    αR 0 n * ((candidateM.pn n : ℚ) : ℝ) + αR 1 n * ((candidateM.pn (n + 1) : ℚ) : ℝ)
      + αR 2 n * ((candidateM.pn (n + 2) : ℚ) : ℝ)
      + αR 3 n * ((candidateM.pn (n + 3) : ℚ) : ℝ) = 0 := by
  intro n hn
  simp only [αR]
  exact_mod_cast hrecp_alt n hn

/-- `hrow` at `N₀ = 4`: `candidateM.qn 4 ≠ 0`, in the kernel through `qnInt`. -/
theorem qn_four_ne_zero : candidateM.qn 4 ≠ 0 := by
  rw [← Zeta2Arith.qnInt_cast]
  refine Int.cast_ne_zero.mpr ?_
  simp only [Zeta2Arith.qnInt, Zeta2Arith.cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- …and at the cell's former `N₀ = 6`, re-checked rather than transferred. -/
theorem qn_six_ne_zero : candidateM.qn 6 ≠ 0 := by
  rw [← Zeta2Arith.qnInt_cast]
  refine Int.cast_ne_zero.mpr ?_
  simp only [Zeta2Arith.qnInt, Zeta2Arith.cTerm, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-! ## §8 — rung 0 (LEAN.md §5): the hypotheses are load-bearing and the objects are not empty -/

/-- The cell-shift law is CONDITIONAL: at `Zeta2T1Eval.probeRep` (one pole at `k = 2`, so
`hz` fails at the crossed integer `−1`) `Φ_0 ≠ Φ_1`.  `Phi_cell_succ` without its `hz` would
be false. -/
theorem cell_shift_needs_hz : Phi 0 Zeta2T1Eval.probeRep ≠ Phi 1 Zeta2T1Eval.probeRep :=
  Zeta2T1Eval.Phi_index_matters

/-- The exceptional set `E n` is nonempty (so `htel` excludes something) … -/
theorem E_nonempty (n : ℕ) : (E n).Nonempty :=
  (bad_nonempty n).mono (Finset.subset_union_left)

/-- … and finite, with `0 ∉ E n`: the telescoping holds at `t = 0` in particular. -/
theorem zero_not_E (n : ℕ) : (0 : ℚ) ∉ E n := by
  intro h
  rcases Finset.mem_union.1 h with h | h
  · exact zero_not_bad n h
  · obtain ⟨s, hs, hse⟩ := Finset.mem_image.1 h
    have h1 : s = 1 := by linarith
    subst h1
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 hs
    have : ((k : ℚ)) = -1 := by linarith [hke]
    have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    linarith

/-- The `'alt'` coefficients are NOT all zero at the threshold: `c₃(N₀) ≠ 0`, read in the
kernel, so `hrecq_alt` is a relation with a nonzero leading coefficient rather than `0 = 0`. -/
theorem alt3_N0_ne_zero : alt 3 N0 ≠ 0 := by
  show (-1 : ℚ) ^ 3 * ((Zeta2StarIdIIJ3.hornerZ Zeta2StarIdIIJ3.c3 ((4 : ℕ) : ℤ) : ℤ) : ℚ) ≠ 0
  refine mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr ?_)
  decide +kernel

end Zeta2L1Asm

/-! ## Receipts (LEAN.md §1 — exit 0 is not an attestation, and neither is a receipt alone) -/

#print axioms Zeta2L1Asm.momI_succ
#print axioms Zeta2L1Asm.Lpoly_succ
#print axioms Zeta2L1Asm.Lpoly_comp_succ
#print axioms Zeta2L1Asm.Phi_shiftRep_pred
#print axioms Zeta2L1Asm.Phi_cell_succ
#print axioms Zeta2L1Asm.Phi_cell_add
#print axioms Zeta2L1Asm.window_nonempty
#print axioms Zeta2L1Asm.evalRep_repM
#print axioms Zeta2L1Asm.repM_support
#print axioms Zeta2L1Asm.sq_dvd_numPoly
#print axioms Zeta2L1Asm.hz_repM
#print axioms Zeta2L1Asm.phi_shift
#print axioms Zeta2L1Asm.bT_eval
#print axioms Zeta2L1Asm.xT_eval
#print axioms Zeta2L1Asm.idxS_sub_badK
#print axioms Zeta2L1Asm.evalRep_Sr
#print axioms Zeta2L1Asm.htel
#print axioms Zeta2L1Asm.phi_rel
#print axioms Zeta2L1Asm.phi_rel_shifted
#print axioms Zeta2L1Asm.coords
#print axioms Zeta2L1Asm.coord_q
#print axioms Zeta2L1Asm.coord_p
#print axioms Zeta2L1Asm.rec_q_raw
#print axioms Zeta2L1Asm.rec_p_raw
#print axioms Zeta2L1Asm.Wq0_tie
#print axioms Zeta2L1Asm.Wq2_tie
#print axioms Zeta2L1Asm.Wq3_tie
#print axioms Zeta2L1Asm.hw0
#print axioms Zeta2L1Asm.hw1
#print axioms Zeta2L1Asm.hw2
#print axioms Zeta2L1Asm.hw3
#print axioms Zeta2L1Asm.hrecq_alt
#print axioms Zeta2L1Asm.hrecp_alt
#print axioms Zeta2L1Asm.al0_tie
#print axioms Zeta2L1Asm.al1_tie
#print axioms Zeta2L1Asm.al2_tie
#print axioms Zeta2L1Asm.al3_tie
#print axioms Zeta2L1Asm.gammaN_eq
#print axioms Zeta2L1Asm.gammaN_mul_qn
#print axioms Zeta2L1Asm.gammaN_mul_pn
#print axioms Zeta2L1Asm.hrecq_rat
#print axioms Zeta2L1Asm.hrecp_rat
#print axioms Zeta2L1Asm.hrecq
#print axioms Zeta2L1Asm.hrecp
#print axioms Zeta2L1Asm.qn_four_ne_zero
#print axioms Zeta2L1Asm.qn_six_ne_zero
#print axioms Zeta2L1Asm.cell_shift_needs_hz
#print axioms Zeta2L1Asm.E_nonempty
#print axioms Zeta2L1Asm.zero_not_E
#print axioms Zeta2L1Asm.alt3_N0_ne_zero
