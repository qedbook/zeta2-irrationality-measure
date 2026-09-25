/-
# ROW PAIR-8, obligation 2 of 3 — the OPERATOR TIE that lets PAIR-6 and PAIR-7 be combined

`docs/future/zeta2-lean-chain.md` row PAIR-8.

**Why this file exists, and why no cell named it until PAIR-6's landing.**  PAIR-6 proves
`Σ_{j<4} β̂ⱼ(n)·hatQ(n+j) = 0` with `β̂ⱼ(n) = Zeta2Pair6.betaHat n j` built from
`StarForallCandt2.alⱼ`, the GENERATED base module's literal `List ℚ`.  PAIR-7 proves
`β̂ⱼ(n)·λden(n) = γⱼ(n)·λnum(n)` with `β̂ⱼ(n) = Zeta2Pair7J<j>.betaHat n` built from that
module's own `zh.map (· / dh)`.  They are the same rationals through two encodings, and
`Zeta2Pair7J<j>` does not import the base — `alⱼ` is not even in scope there — so **nothing in
Lean connects them** and PAIR-8 cannot multiply one row's conclusion by the other's until
something does.  That is §6a's lesson in its original words, one layer further in:

> a `c3_ne_zero` about `hornerZ c3` discharges nothing about a coords-derived `α₃` until
> STAR-ID (ii) identifies them.

Measured equal in exact ℚ (155 coefficients at each of the four indices, 0 of 4 disagree —
`pair8_check.py` §T, rebuilt from the committed coords, with a negative control).  A
measurement is not a theorem; sections 1 and 2 below make it one, at four `decide +kernel`s.

**What is proved here**

  * `al<j>_tie   : StarForallCandt2.al<j> = Zeta2Pair7J<j>.alHat`   (four `decide +kernel`)
  * `betaHat_tie : Zeta2Pair6.betaHat n j = betaHat7 n j` for every `n` and every `j ≤ 3`
  * `pair7N      : Zeta2Pair6.betaHat n j * λden n = gammaN n j * λnum n`, i.e. PAIR-7's row
    restated at PAIR-6's OWN operator and at ONE `λ` rather than four namespaced copies.

**What is NOT proved here.**  Nothing about `λden ≠ 0` (that is `Zeta2Pair8Lam`) and nothing
about `hatQ n = qnInt n` (that is `Zeta2Pair8`, and it is CONDITIONAL — see its header).

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2Pair8Tie.lean

Receipts: `out_axioms_pair8tie.txt`.  Falsifier: `falsify_pair8.sh --lean`.  Second
implementation, in exact ℚ: `pair8_check.py` → `pair8_check.out`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Pair6
import Zeta2Pair7J0
import Zeta2Pair7J1
import Zeta2Pair7J2
import Zeta2Pair7J3

-- FILE-LEVEL on purpose: placed between a docstring and its theorem a `set_option` is a parse
-- error Lean silently RECOVERS from — the file does not parse, the option is dropped, and every
-- receipt still prints clean (zeta2-lean-chain.md, PAIR-7's and PAIR-6's landings).
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Zeta2Pair8Tie

/-! ## 1. The four coefficient lists are the same list

`StarForallCandt2.al<j>` is 155 ℚ literals emitted by `star_forall_to_lean.py`;
`Zeta2Pair7J<j>.alHat` is 155 ℤ literals over one denominator emitted by `gen_pair7_lean.py`.
The same ring the base's own kernel shards decide `al<j>` in (`kha<j>_<n>`) decides this. -/

theorem al0_tie : StarForallCandt2.al0 = Zeta2Pair7J0.alHat := by decide +kernel

theorem al1_tie : StarForallCandt2.al1 = Zeta2Pair7J1.alHat := by decide +kernel

theorem al2_tie : StarForallCandt2.al2 = Zeta2Pair7J2.alHat := by decide +kernel

theorem al3_tie : StarForallCandt2.al3 = Zeta2Pair7J3.alHat := by decide +kernel

/-! ## 2. One indexed operator, and one `λ`

PAIR-7 lives in four namespaces, so its `betaHat`, `gammaCh`, `lamNum` and `lamDen` exist in
four copies.  The `λ` copies are the SAME definition over the same `Zeta2Pair7Lam` data, so the
three restatements below are `rfl`; they are written out rather than left implicit because a
consumer reading `pair7N` must be able to see that only one `λ` is in play. -/

/-- The HAT operator, indexed, in PAIR-7's encoding. -/
noncomputable def betaHat7 (n j : ℕ) : ℚ :=
  match j with
  | 0 => Zeta2Pair7J0.betaHat n
  | 1 => Zeta2Pair7J1.betaHat n
  | 2 => Zeta2Pair7J2.betaHat n
  | _ => Zeta2Pair7J3.betaHat n

/-- The CHAIN operator, indexed — the one L1-ASM's recurrence runs in. -/
noncomputable def gammaN (n j : ℕ) : ℚ :=
  match j with
  | 0 => Zeta2Pair7J0.gammaCh n
  | 1 => Zeta2Pair7J1.gammaCh n
  | 2 => Zeta2Pair7J2.gammaCh n
  | _ => Zeta2Pair7J3.gammaCh n

theorem lamDen_1 (n : ℕ) : Zeta2Pair7J1.lamDen n = Zeta2Pair7J0.lamDen n := rfl
theorem lamDen_2 (n : ℕ) : Zeta2Pair7J2.lamDen n = Zeta2Pair7J0.lamDen n := rfl
theorem lamDen_3 (n : ℕ) : Zeta2Pair7J3.lamDen n = Zeta2Pair7J0.lamDen n := rfl
theorem lamNum_1 (n : ℕ) : Zeta2Pair7J1.lamNum n = Zeta2Pair7J0.lamNum n := rfl
theorem lamNum_2 (n : ℕ) : Zeta2Pair7J2.lamNum n = Zeta2Pair7J0.lamNum n := rfl
theorem lamNum_3 (n : ℕ) : Zeta2Pair7J3.lamNum n = Zeta2Pair7J0.lamNum n := rfl

/-! ## 3. PAIR-6's operator IS PAIR-7's

`Zeta2Pair6.alN n j = (polB al_j).eval (n : ℚ)` and `polB_eval` turns that into the `foldr`
that `StarKernel.qeval` is, which is the left factor of `Zeta2Pair7J<j>.betaHat`.  The `Π̂`
factor is written identically on both sides (`Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + j)`), so
once the coefficient lists are tied the two operators are the same term. -/

theorem alN_tie0 (n : ℕ) :
    Zeta2Pair6.alN n 0 = StarKernel.qeval (n : ℚ) Zeta2Pair7J0.alHat := by
  show (StarForallCandt2.polB StarForallCandt2.al0).eval (n : ℚ)
      = StarKernel.qeval (n : ℚ) Zeta2Pair7J0.alHat
  rw [al0_tie, StarForallCandt2.polB_eval]
  rfl

theorem alN_tie1 (n : ℕ) :
    Zeta2Pair6.alN n 1 = StarKernel.qeval (n : ℚ) Zeta2Pair7J1.alHat := by
  show (StarForallCandt2.polB StarForallCandt2.al1).eval (n : ℚ)
      = StarKernel.qeval (n : ℚ) Zeta2Pair7J1.alHat
  rw [al1_tie, StarForallCandt2.polB_eval]
  rfl

theorem alN_tie2 (n : ℕ) :
    Zeta2Pair6.alN n 2 = StarKernel.qeval (n : ℚ) Zeta2Pair7J2.alHat := by
  show (StarForallCandt2.polB StarForallCandt2.al2).eval (n : ℚ)
      = StarKernel.qeval (n : ℚ) Zeta2Pair7J2.alHat
  rw [al2_tie, StarForallCandt2.polB_eval]
  rfl

theorem alN_tie3 (n : ℕ) :
    Zeta2Pair6.alN n 3 = StarKernel.qeval (n : ℚ) Zeta2Pair7J3.alHat := by
  show (StarForallCandt2.polB StarForallCandt2.al3).eval (n : ℚ)
      = StarKernel.qeval (n : ℚ) Zeta2Pair7J3.alHat
  rw [al3_tie, StarForallCandt2.polB_eval]
  rfl

theorem betaHat_tie0 (n : ℕ) : Zeta2Pair6.betaHat n 0 = betaHat7 n 0 := by
  show Zeta2Pair6.alN n 0 * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + 0))
      = StarKernel.qeval (n : ℚ) Zeta2Pair7J0.alHat
          * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + 0))
  rw [alN_tie0]

theorem betaHat_tie1 (n : ℕ) : Zeta2Pair6.betaHat n 1 = betaHat7 n 1 := by
  show Zeta2Pair6.alN n 1 * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + 1))
      = StarKernel.qeval (n : ℚ) Zeta2Pair7J1.alHat
          * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + 1))
  rw [alN_tie1]

theorem betaHat_tie2 (n : ℕ) : Zeta2Pair6.betaHat n 2 = betaHat7 n 2 := by
  show Zeta2Pair6.alN n 2 * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + 2))
      = StarKernel.qeval (n : ℚ) Zeta2Pair7J2.alHat
          * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + 2))
  rw [alN_tie2]

theorem betaHat_tie3 (n : ℕ) : Zeta2Pair6.betaHat n 3 = betaHat7 n 3 := by
  show Zeta2Pair6.alN n 3 * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + 3))
      = StarKernel.qeval (n : ℚ) Zeta2Pair7J3.alHat
          * (Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + 3))
  rw [alN_tie3]

/-- **The tie, indexed.**  PAIR-6's operator and PAIR-7's are the same function on `j ≤ 3`. -/
theorem betaHat_tie (n j : ℕ) (hj : j ≤ 3) : Zeta2Pair6.betaHat n j = betaHat7 n j := by
  interval_cases j
  · exact betaHat_tie0 n
  · exact betaHat_tie1 n
  · exact betaHat_tie2 n
  · exact betaHat_tie3 n

/--
**ROW PAIR-7, restated at PAIR-6's own operator and at ONE `λ`.**  This is the statement
PAIR-8's crossing consumes: everything on the left is the object PAIR-6's recurrence is about,
and `λden`/`λnum` are `Zeta2Pair7J0`'s single pair rather than four namespaced copies.
-/
theorem pair7N (n j : ℕ) (hj : j ≤ 3) :
    Zeta2Pair6.betaHat n j * Zeta2Pair7J0.lamDen n
      = gammaN n j * Zeta2Pair7J0.lamNum n := by
  interval_cases j
  · rw [betaHat_tie0 n]
    exact Zeta2Pair7J0.pair7_j0 n
  · rw [betaHat_tie1 n, ← lamDen_1 n, ← lamNum_1 n]
    exact Zeta2Pair7J1.pair7_j1 n
  · rw [betaHat_tie2 n, ← lamDen_2 n, ← lamNum_2 n]
    exact Zeta2Pair7J2.pair7_j2 n
  · rw [betaHat_tie3 n, ← lamDen_3 n, ← lamNum_3 n]
    exact Zeta2Pair7J3.pair7_j3 n

end Zeta2Pair8Tie

#print axioms Zeta2Pair8Tie.al0_tie
#print axioms Zeta2Pair8Tie.al1_tie
#print axioms Zeta2Pair8Tie.al2_tie
#print axioms Zeta2Pair8Tie.al3_tie
#print axioms Zeta2Pair8Tie.lamDen_1
#print axioms Zeta2Pair8Tie.lamDen_2
#print axioms Zeta2Pair8Tie.lamDen_3
#print axioms Zeta2Pair8Tie.lamNum_1
#print axioms Zeta2Pair8Tie.lamNum_2
#print axioms Zeta2Pair8Tie.lamNum_3
#print axioms Zeta2Pair8Tie.alN_tie0
#print axioms Zeta2Pair8Tie.alN_tie1
#print axioms Zeta2Pair8Tie.alN_tie2
#print axioms Zeta2Pair8Tie.alN_tie3
#print axioms Zeta2Pair8Tie.betaHat_tie0
#print axioms Zeta2Pair8Tie.betaHat_tie1
#print axioms Zeta2Pair8Tie.betaHat_tie2
#print axioms Zeta2Pair8Tie.betaHat_tie3
#print axioms Zeta2Pair8Tie.betaHat_tie
#print axioms Zeta2Pair8Tie.pair7N
