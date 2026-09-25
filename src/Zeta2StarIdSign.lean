/-
# Row STAR-ID part (iii) — the `'alt'` sign is a THEOREM, at the indices where it can be one today

`docs/future/zeta2-lean-chain.md` row STAR-ID.  Added 2026-09-17 by the row's closing unit.

**HEADLINE: `Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.**

**WHAT (iii) IS, and why it was a trap.**  The chain's certified quadruple `cⱼ` annihilates
`(−1)ⁿ rₙ`, not `rₙ` — equivalently, the recurrence the sequence obeys is
`∑ⱼ (−1)^j cⱼ(n) q_{n+j} = 0`, the `'alt'` convention, and the `'plain'` one fails.  Until this
file that was ONE off-Lean checker's verdict (`closure.py` stage ROWS), and a sign convention is
exactly the class of claim that typechecks either way: the guards `hα₃`/`hα₀` never see a
per-index sign, so L1-ASM would thread `αⱼ := cⱼ` and prove a theorem about the wrong operator
without a red anywhere.

**WHAT THIS FILE PROVES.**  The sign is not a new datum; it is FORCED by three landed facts —
part (ii) `cⱼ·Nⱼ = (−1)^j·Ãⱼ·Dⱼ·W`, the Π-rebase `Π(n+j)·Dⱼ = Π(n)·Nⱼ`
(`Zeta2StarIdPi.Pin_shift`), and `candidateM.sgn n = −1` — and `alt_of_ii_of_pin` is that
derivation as ONE generic `linear_combination` with `Dⱼ ≠ 0` cancelled.  Its conclusion is the
per-index WEIGHT identity the Φ route needs,

    Ãⱼ(n) · (W(n) · Π(n))  =  −((−1)^j · cⱼ(n) · (sgn(n+j) · Π(n+j))),

which converts `∑ⱼ Ãⱼ(n)·(Φ ρ_{n+j}).1 = 0` term by term into `∑ⱼ (−1)^j cⱼ(n) q_{n+j} = 0`
through `Zeta2StarIdPhi.star_phi_rho` — with NO division, so no nonvanishing of `W` is owed.
`alt_weight_j1` and `alt_weight_j2` instantiate it from `Zeta2StarIdIIJ1.star_ii_j1` /
`Zeta2StarIdIIJ2.star_ii_j2` and `Zeta2StarIdPi.pin_j1` / `.pin_j2`.  **`j = 1` is the index
where the two conventions DIFFER** (at even `j` they coincide), and `plain_fails_j1` is a Lean
REFUTATION of the plain reading there: the same line with `(−1)^j` deleted is FALSE at `n = 0`.

**THE NUMBER (iii) TURNS ON is `candidateM.dsum = 16`**, EVEN: `sgn n = (−1)^(16n+1) = −1` at every
`n`, so the candidate's sign carries no `n`-parity of its own and (ii)'s `(−1)^j` survives into
the recurrence rather than cancelling.  `record_sgn_alternates` is the control on the other
side: at the RECORD member `dsum = 9` and `sgn` genuinely alternates, so this is a fact about
THIS member and not about the family.

**THE TIES, and why they are theorems.**  `Zeta2StarIdPi` and `Zeta2StarIdIIJ1/J2` each carry
their OWN `hornerZ` and their own `n1/d1/n2/d2` literals — and `J1` and `J2` each carry their own
`w13`.  Nothing but a theorem says those are the same objects; `hz_pi_j1`/`hz_pi_j2` (induction)
and `d1_tie`/`n1_tie`/`d2_tie`/`n2_tie`/`w13_tie` (`decide +kernel`) are those theorems.  `w13_tie`
is the one with content: it is the `j`-INDEPENDENCE of `W` across two separately generated
modules, machine-checked rather than promised by a generator's refusal.

**ALL FOUR INDICES, as of 2026-09-18.**  The first version of this file (2026-09-17) carried
`j = 1, 2` only: `(0,3)`'s (ii) lived in the monolithic `Zeta2StarIdII`, whose olean would have
cost the 3 h 46 m its elaboration did.  `(0,3)` was then RE-SHARDED as `(1,2)` had been
(`Zeta2StarIdIIJ0`/`J3`, importable in minutes), and §5a adds `alt_weight_j0`/`_j3` on the same
three-`have` pattern, `plain_fails_j3`, and the `w13` ties across all four generated modules.
With that, row STAR-ID is CLOSED: `Zeta2StarIdPhi` + the four `alt_weight_j` are everything
L1-ASM's recurrence half needs from it.  Nothing here transports to ℝ (row L4-BR); nothing here
applies Φ to the telescoping (row L1-ASM).

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2StarIdSign.lean

Receipts: `out_axioms_staridsign.txt`.  Falsifier: `falsify_staridsign.sh --lean`.  Second
implementation, exact ℚ/ℤ at ALL FOUR indices and against the engine's own `qₙ`:
`starid_sign_check.py` (31 checks, 6 arms).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2StarIdPi
import Zeta2StarIdIIJ0
import Zeta2StarIdIIJ1
import Zeta2StarIdIIJ2
import Zeta2StarIdIIJ3

namespace Zeta2StarIdSign

open Zeta2Defs

/-! ## 1. The candidate's sign is the constant `−1` -/

/-- `candidateM.dsum = 16`: `13 + 11 + 9 + 15 − (2 + 4 + 26)`. -/
theorem candidate_dsum : candidateM.dsum = 16 := by decide

/-- **`sgn n = −1` at every `n`.**  `(−1)^(16n+1) = ((−1)^16)^n · (−1)`. -/
theorem sgn_candidate (n : ℕ) : candidateM.sgn n = -1 := by
  show ((-1 : ℚ)) ^ (candidateM.dsum * n + 1) = -1
  rw [candidate_dsum, pow_succ, pow_mul]
  norm_num

/-- **Control on the other side.**  At the record member `dsum = 9` is odd and the sign really
does alternate, so `sgn_candidate` is a fact about the candidate and not a triviality. -/
theorem record_sgn_alternates : recordM.sgn 0 ≠ recordM.sgn 1 := by
  norm_num [Member.sgn, Member.dsum, recordM]

/-! ## 2. The generic step: (ii) + the Π-rebase + a constant sign ⟹ the per-index weight -/

/-- **The whole of part (iii), index-free.**  From `c·N = (−1)^e·(A·D·W)` and `Pj·D = P·N` with
`D ≠ 0` and `s = −1`: `A·(W·P) = −((−1)^e·c·(s·Pj))`.  Stated with `(−1)^e` as an atom so that
`ring` never has to decide the parity: `hsq` supplies `((−1)^e)² = 1` as a hypothesis. -/
theorem alt_of_ii_of_pin {A c W P Pj N D s : ℚ} {e : ℕ} (hD : D ≠ 0)
    (hii : c * N = (-1 : ℚ) ^ e * (A * D * W))
    (hpin : Pj * D = P * N) (hs : s = -1) :
    A * (W * P) = -((-1 : ℚ) ^ e * c * (s * Pj)) := by
  have hsq : ((-1 : ℚ) ^ e) * ((-1 : ℚ) ^ e) = 1 := by
    rw [← mul_pow]; norm_num
  have h1 : (c * Pj) * D = ((-1 : ℚ) ^ e * (A * W * P)) * D := by
    calc (c * Pj) * D = c * (Pj * D) := by ring
      _ = c * (P * N) := by rw [hpin]
      _ = (c * N) * P := by ring
      _ = ((-1 : ℚ) ^ e * (A * D * W)) * P := by rw [hii]
      _ = ((-1 : ℚ) ^ e * (A * W * P)) * D := by ring
  have h2 : c * Pj = (-1 : ℚ) ^ e * (A * W * P) := mul_right_cancel₀ hD h1
  rw [hs]
  linear_combination (-((-1 : ℚ) ^ e)) * h2 - (A * W * P) * hsq

/-! ## 3. The ties between the three modules' private copies of the same objects -/

theorem hz_pi_j1 (L : List ℤ) (x : ℤ) :
    Zeta2StarIdPi.hornerZ L x = Zeta2StarIdIIJ1.hornerZ L x := by
  induction L with
  | nil => rfl
  | cons c l ih => simp [Zeta2StarIdPi.hornerZ, Zeta2StarIdIIJ1.hornerZ, ih]

theorem hz_pi_j2 (L : List ℤ) (x : ℤ) :
    Zeta2StarIdPi.hornerZ L x = Zeta2StarIdIIJ2.hornerZ L x := by
  induction L with
  | nil => rfl
  | cons c l ih => simp [Zeta2StarIdPi.hornerZ, Zeta2StarIdIIJ2.hornerZ, ih]

theorem d1_tie : Zeta2StarIdPi.d1 = Zeta2StarIdIIJ1.d1 := by decide +kernel
theorem n1_tie : Zeta2StarIdPi.n1 = Zeta2StarIdIIJ1.n1 := by decide +kernel
theorem d2_tie : Zeta2StarIdPi.d2 = Zeta2StarIdIIJ2.d2 := by decide +kernel
theorem n2_tie : Zeta2StarIdPi.n2 = Zeta2StarIdIIJ2.n2 := by decide +kernel

/-- **`W` is the SAME polynomial at `j = 1` and `j = 2`** — the `j`-independence part (ii)
exists to establish, checked in the kernel across two separately generated modules. -/
theorem w13_tie : Zeta2StarIdIIJ1.w13 = Zeta2StarIdIIJ2.w13 := by decide +kernel

/-! ## 4. (iii) at `j = 1` — the index where the conventions differ -/

/-- **`alt_weight` at `j = 1`.** -/
theorem alt_weight_j1 (n : ℕ) :
    Zeta2StarIdIIJ1.Atil1 n * (Zeta2StarIdIIJ1.Wq n * candidateM.Pin n)
      = -((-1 : ℚ) ^ 1 * Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.c1 n
            * (candidateM.sgn (n + 1) * candidateM.Pin (n + 1))) := by
  have hD : Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.d1 n ≠ 0 := by
    have h := Zeta2StarIdPi.d1_ne_zero n
    rw [d1_tie, hz_pi_j1] at h
    exact h
  have hpin : candidateM.Pin (n + 1) * Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.d1 n
      = candidateM.Pin n * Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.n1 n := by
    have h := Zeta2StarIdPi.pin_j1 n
    rw [d1_tie, n1_tie, hz_pi_j1, hz_pi_j1] at h
    exact h
  have hii : Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.c1 n * Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.n1 n
      = (-1 : ℚ) ^ 1 * (Zeta2StarIdIIJ1.Atil1 n * Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.d1 n
          * Zeta2StarIdIIJ1.Wq n) := by
    rw [pow_one, neg_one_mul]
    exact Zeta2StarIdIIJ1.star_ii_j1 n
  -- `linear_combination`, NOT `exact`: on a mismatched statement `exact` unifies until the
  -- heartbeat or recursion limit, and a falsifier arm that RESOURCE-ERRORS has rejected
  -- nothing (LEAN.md §3, and `falsify_staridsign.sh` A5/A7 measured exactly that on the
  -- first run).  `linear_combination` ends in `ring1`, which refuses in milliseconds.
  have h := alt_of_ii_of_pin hD hii hpin (sgn_candidate (n + 1))
  linear_combination h

/-- `c₁(0) ≠ 0` — the constant term of the landed `c1`, read in the kernel. -/
theorem c1_zero_ne : Zeta2StarIdIIJ1.hornerZ Zeta2StarIdIIJ1.c1 0 ≠ 0 := by decide +kernel

/-- **The PLAIN convention is REFUTED at `j = 1`.**  The same line as `alt_weight_j1` with the
`(−1)^j` deleted is FALSE at `n = 0`, because the two readings differ by `2·c₁(0)·Π(1) ≠ 0`.
This is the theorem that makes (iii) a decision Lean has taken rather than one it tolerates. -/
theorem plain_fails_j1 :
    Zeta2StarIdIIJ1.Atil1 0 * (Zeta2StarIdIIJ1.Wq 0 * candidateM.Pin 0)
      ≠ -(Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.c1 0
            * (candidateM.sgn (0 + 1) * candidateM.Pin (0 + 1))) := by
  intro hplain
  have halt := alt_weight_j1 0
  have hP : candidateM.Pin (0 + 1) ≠ 0 := ne_of_gt (candidateM.Pin_pos _)
  have hc : Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.c1 0 ≠ 0 := by
    show ((Zeta2StarIdIIJ1.hornerZ Zeta2StarIdIIJ1.c1 ((0 : ℕ) : ℤ) : ℤ) : ℚ) ≠ 0
    rw [Nat.cast_zero]
    exact Int.cast_ne_zero.mpr c1_zero_ne
  rw [sgn_candidate] at halt hplain
  have h2 : Zeta2StarIdIIJ1.Cq Zeta2StarIdIIJ1.c1 0 * candidateM.Pin (0 + 1) = 0 := by
    linear_combination (-1 / 2 : ℚ) * (hplain - halt)
  exact mul_ne_zero hc hP h2

/-! ## 5. (iii) at `j = 2` — where the conventions coincide, and the theorem says so -/

/-- **`alt_weight` at `j = 2`.** -/
theorem alt_weight_j2 (n : ℕ) :
    Zeta2StarIdIIJ2.Atil2 n * (Zeta2StarIdIIJ2.Wq n * candidateM.Pin n)
      = -((-1 : ℚ) ^ 2 * Zeta2StarIdIIJ2.Cq Zeta2StarIdIIJ2.c2 n
            * (candidateM.sgn (n + 2) * candidateM.Pin (n + 2))) := by
  have hD : Zeta2StarIdIIJ2.Cq Zeta2StarIdIIJ2.d2 n ≠ 0 := by
    have h := Zeta2StarIdPi.d2_ne_zero n
    rw [d2_tie, hz_pi_j2] at h
    exact h
  have hpin : candidateM.Pin (n + 2) * Zeta2StarIdIIJ2.Cq Zeta2StarIdIIJ2.d2 n
      = candidateM.Pin n * Zeta2StarIdIIJ2.Cq Zeta2StarIdIIJ2.n2 n := by
    have h := Zeta2StarIdPi.pin_j2 n
    rw [d2_tie, n2_tie, hz_pi_j2, hz_pi_j2] at h
    exact h
  have hii : Zeta2StarIdIIJ2.Cq Zeta2StarIdIIJ2.c2 n * Zeta2StarIdIIJ2.Cq Zeta2StarIdIIJ2.n2 n
      = (-1 : ℚ) ^ 2 * (Zeta2StarIdIIJ2.Atil2 n * Zeta2StarIdIIJ2.Cq Zeta2StarIdIIJ2.d2 n
          * Zeta2StarIdIIJ2.Wq n) := by
    rw [show ((-1 : ℚ)) ^ 2 = 1 by norm_num, one_mul]
    exact Zeta2StarIdIIJ2.star_ii_j2 n
  have h := alt_of_ii_of_pin hD hii hpin (sgn_candidate (n + 2))
  linear_combination h

/-- At even `j` the plain and alt readings are the SAME statement — recorded so that nobody
takes a green at `j = 0` or `j = 2` as evidence about the convention. -/
theorem plain_eq_alt_j2 (n : ℕ) :
    Zeta2StarIdIIJ2.Atil2 n * (Zeta2StarIdIIJ2.Wq n * candidateM.Pin n)
      = -(Zeta2StarIdIIJ2.Cq Zeta2StarIdIIJ2.c2 n
            * (candidateM.sgn (n + 2) * candidateM.Pin (n + 2))) := by
  have h := alt_weight_j2 n
  rw [show ((-1 : ℚ)) ^ 2 = 1 by norm_num, one_mul] at h
  exact h

/-! ## 5a. (iii) at `j = 0` and `j = 3` — added 2026-09-18, once `(0,3)` was re-sharded as
`(1,2)` was (`Zeta2StarIdIIJ0`/`J3`, each an importable module in minutes rather than a 3 h 46 m
olean).  Same three `have`s each; at `j = 0` the Pochhammers are `1` and the flat `c₀ = Ã₀·W`
(`star_ii_j0_flat`) feeds the generic lemma with `N = D = 1`.  The `w13` ties across ALL FOUR
generated modules are theorems, not the generator's promise. -/

theorem hz_pi_j0 (L : List ℤ) (x : ℤ) :
    Zeta2StarIdPi.hornerZ L x = Zeta2StarIdIIJ0.hornerZ L x := by
  induction L with
  | nil => rfl
  | cons c l ih => simp [Zeta2StarIdPi.hornerZ, Zeta2StarIdIIJ0.hornerZ, ih]

theorem hz_pi_j3 (L : List ℤ) (x : ℤ) :
    Zeta2StarIdPi.hornerZ L x = Zeta2StarIdIIJ3.hornerZ L x := by
  induction L with
  | nil => rfl
  | cons c l ih => simp [Zeta2StarIdPi.hornerZ, Zeta2StarIdIIJ3.hornerZ, ih]

theorem d3_tie : Zeta2StarIdPi.d3 = Zeta2StarIdIIJ3.d3 := by decide +kernel
theorem n3_tie : Zeta2StarIdPi.n3 = Zeta2StarIdIIJ3.n3 := by decide +kernel

/-- `W` is ONE polynomial across all four sharded modules — `j = 0` against `j = 1`. -/
theorem w13_tie_01 : Zeta2StarIdIIJ0.w13 = Zeta2StarIdIIJ1.w13 := by decide +kernel
/-- …and `j = 3` against `j = 1`. -/
theorem w13_tie_31 : Zeta2StarIdIIJ3.w13 = Zeta2StarIdIIJ1.w13 := by decide +kernel

/-- **`alt_weight` at `j = 0`.**  `(−1)^0 = 1`, `sgn n = −1`, so the weight is `+c₀·Π(n)`. -/
theorem alt_weight_j0 (n : ℕ) :
    Zeta2StarIdIIJ0.Atil0 n * (Zeta2StarIdIIJ0.Wq n * candidateM.Pin n)
      = -((-1 : ℚ) ^ 0 * Zeta2StarIdIIJ0.Cq Zeta2StarIdIIJ0.c0 n
            * (candidateM.sgn (n + 0) * candidateM.Pin (n + 0))) := by
  have hD : (1 : ℚ) ≠ 0 := one_ne_zero
  have hpin : candidateM.Pin (n + 0) * (1 : ℚ) = candidateM.Pin n * 1 := by
    rw [Nat.add_zero]
  have hii : Zeta2StarIdIIJ0.Cq Zeta2StarIdIIJ0.c0 n * (1 : ℚ)
      = (-1 : ℚ) ^ 0 * (Zeta2StarIdIIJ0.Atil0 n * 1 * Zeta2StarIdIIJ0.Wq n) := by
    rw [pow_zero, one_mul, mul_one, mul_one]
    exact Zeta2StarIdIIJ0.star_ii_j0_flat n
  have h := alt_of_ii_of_pin hD hii hpin (sgn_candidate (n + 0))
  linear_combination h

/-- At `j = 0` the plain and alt readings coincide (recorded, as at `j = 2`). -/
theorem plain_eq_alt_j0 (n : ℕ) :
    Zeta2StarIdIIJ0.Atil0 n * (Zeta2StarIdIIJ0.Wq n * candidateM.Pin n)
      = -(Zeta2StarIdIIJ0.Cq Zeta2StarIdIIJ0.c0 n
            * (candidateM.sgn (n + 0) * candidateM.Pin (n + 0))) := by
  have h := alt_weight_j0 n
  rw [pow_zero, one_mul] at h
  exact h

/-- **`alt_weight` at `j = 3`** — the second index where the conventions differ. -/
theorem alt_weight_j3 (n : ℕ) :
    Zeta2StarIdIIJ3.Atil3 n * (Zeta2StarIdIIJ3.Wq n * candidateM.Pin n)
      = -((-1 : ℚ) ^ 3 * Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.c3 n
            * (candidateM.sgn (n + 3) * candidateM.Pin (n + 3))) := by
  have hD : Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.d3 n ≠ 0 := by
    have h := Zeta2StarIdPi.d3_ne_zero n
    rw [d3_tie, hz_pi_j3] at h
    exact h
  have hpin : candidateM.Pin (n + 3) * Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.d3 n
      = candidateM.Pin n * Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.n3 n := by
    have h := Zeta2StarIdPi.pin_j3 n
    rw [d3_tie, n3_tie, hz_pi_j3, hz_pi_j3] at h
    exact h
  have hii : Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.c3 n * Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.n3 n
      = (-1 : ℚ) ^ 3 * (Zeta2StarIdIIJ3.Atil3 n * Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.d3 n
          * Zeta2StarIdIIJ3.Wq n) := by
    rw [show ((-1 : ℚ)) ^ 3 = -1 by norm_num, neg_one_mul]
    exact Zeta2StarIdIIJ3.star_ii_j3 n
  have h := alt_of_ii_of_pin hD hii hpin (sgn_candidate (n + 3))
  linear_combination h

/-- `c₃(0) ≠ 0` — the constant term of the landed `c3`, read in the kernel. -/
theorem c3_zero_ne : Zeta2StarIdIIJ3.hornerZ Zeta2StarIdIIJ3.c3 0 ≠ 0 := by decide +kernel

/-- **The PLAIN convention is REFUTED at `j = 3` too.** -/
theorem plain_fails_j3 :
    Zeta2StarIdIIJ3.Atil3 0 * (Zeta2StarIdIIJ3.Wq 0 * candidateM.Pin 0)
      ≠ -(Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.c3 0
            * (candidateM.sgn (0 + 3) * candidateM.Pin (0 + 3))) := by
  intro hplain
  have halt := alt_weight_j3 0
  have hP : candidateM.Pin (0 + 3) ≠ 0 := ne_of_gt (candidateM.Pin_pos _)
  have hc : Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.c3 0 ≠ 0 := by
    show ((Zeta2StarIdIIJ3.hornerZ Zeta2StarIdIIJ3.c3 ((0 : ℕ) : ℤ) : ℤ) : ℚ) ≠ 0
    rw [Nat.cast_zero]
    exact Int.cast_ne_zero.mpr c3_zero_ne
  rw [sgn_candidate] at halt hplain
  have h2 : Zeta2StarIdIIJ3.Cq Zeta2StarIdIIJ3.c3 0 * candidateM.Pin (0 + 3) = 0 := by
    linear_combination (-1 / 2 : ℚ) * (hplain - halt)
  exact mul_ne_zero hc hP h2

/-! ## 6. The same `W` on both sides, as the consumer will see it -/

/-- `Zeta2StarIdIIJ1.Wq` and `Zeta2StarIdIIJ2.Wq` are one function of `n`. -/
theorem Wq_tie (n : ℕ) : Zeta2StarIdIIJ1.Wq n = Zeta2StarIdIIJ2.Wq n := by
  show ((Zeta2StarIdIIJ1.hornerZ Zeta2StarIdIIJ1.w13 (n : ℤ) : ℤ) : ℚ) / 13
    = ((Zeta2StarIdIIJ2.hornerZ Zeta2StarIdIIJ2.w13 (n : ℤ) : ℤ) : ℚ) / 13
  rw [w13_tie, ← hz_pi_j1, hz_pi_j2]

/-! ## 7. Receipts (LEAN.md §1 — exit 0 is not an attestation, and neither is a receipt alone) -/

#print axioms candidate_dsum
#print axioms sgn_candidate
#print axioms record_sgn_alternates
#print axioms alt_of_ii_of_pin
#print axioms hz_pi_j1
#print axioms hz_pi_j2
#print axioms d1_tie
#print axioms n1_tie
#print axioms d2_tie
#print axioms n2_tie
#print axioms w13_tie
#print axioms alt_weight_j1
#print axioms c1_zero_ne
#print axioms plain_fails_j1
#print axioms alt_weight_j2
#print axioms plain_eq_alt_j2
#print axioms hz_pi_j0
#print axioms hz_pi_j3
#print axioms d3_tie
#print axioms n3_tie
#print axioms w13_tie_01
#print axioms w13_tie_31
#print axioms alt_weight_j0
#print axioms plain_eq_alt_j0
#print axioms alt_weight_j3
#print axioms c3_zero_ne
#print axioms plain_fails_j3
#print axioms Wq_tie

end Zeta2StarIdSign
