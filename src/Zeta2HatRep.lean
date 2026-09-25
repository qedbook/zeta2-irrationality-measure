/-
# Row PAIR-4 — `Rep̂`, `Φ̂`, and the hat's representation: the n = 0 instance

`docs/future/zeta2-lean-chain.md` row PAIR-4 (and the definitional half of PAIR-3, folded into
it — see the PAIR-4 design notes: PAIR-4's statement cannot be WRITTEN without `Rep̂`/`Φ̂`,
so the row that is ordered first has to carry them).

The hat member at integer `n` is the rational function

    R̂ₙ/Π̂ = ∏_{l=3n+2}^{20n+1}(2t+l)·∏_{l=1}^{5n}(t+l) / [∏_{l=7n+1}^{18n+1}(t+l)·∏_{l=9n+1}^{20n+1}(t+l)]

of degree `22n` over `22n+2` — no polynomial part, poles of order ≤ 2 at negative integers.
Its partial-fraction data is a pair of finitely-supported coefficient families

    `Rep̂ := (ℕ →₀ ℚ) × (ℕ →₀ ℚ)`   —   `(B, A)`, the order-1 and order-2 coefficients at `t = −k`

and the pairing functional at the contour `Ĉ N = −4N − 3/4` is the ℚ³-valued (rational, ζ(2),
ln 2) map `Φ̂ N`, with `L_k = 2k − 8N − 2` the alternating-sum length the left-closing evaluator
produces (`mb2.W2_pole`; PAIR-0 design notes).

**`rep̂` is NOT an extraction function, and PAIR-4's cell said `rep̂ (R̂ₙ/Π̂) = (B, A)`.**  The
object that exists is the EVALUATION map `evalRep : Rep̂ → ℚ → ℚ`; "the representation of the
member" is the theorem `evalRep (repHat n) t = hatPi n * hatMember n t` (`hat_rep_zero` below at
`n = 0`), and uniqueness is injectivity of `evalRep`, which is PAIR-3's `rep̂_injective`.  Stated
the other way round, injectivity would have nothing to do.  PHI-REP's row already states its
tale-1 twin in the evaluation direction (`rep_injective`), so this is the corpus's own convention.

**Normalisation, pinned here**: `Zeta2Hat`'s `hatA`, `hatBlo`, `hatBhi` are the Π̂-SCALED
residues (`Π̂·A_k`, `Π̂·B_k` — PAIR-0's derivation), so `repHat n` represents `Π̂(n)·(R̂ₙ/Π̂)`,
i.e. `R̂ₙ`, and `Φ̂` lands on `(hatP n, −hatQ n, 0)` with no division.  PAIR-6/PAIR-7 consume it
at THAT normalisation; the Π̂-rebase factors are PAIR-7's.

Measured beside this file, in exact rationals over `n ≤ 4` (`hat_rep_probe.py`,
`hat_rep_probe.out`): the representation (20 of 20 `(n,t)` pairs), the evaluation at the
member's own cell including `Σ_k B_k = 0` — the `ln 2` coordinate, which the PAIR design notes
DO already measure at `n ≤ 6`, but on a different object (`gen_hat_lean.out`'s seven "mb2 hat
value is ln2-free" lines are about the independent EVALUATOR's value, not about this coefficient
sum over the landed families) — and belt invariance, which agrees with `Φ̂` at the
neighbour's cell on exactly the 10 of 14 `(n,j)` pairs satisfying `2.5n + 3/4 > 1.5j` and fails
on the other 4, in the RATIONAL coordinate only.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Data.Finsupp.Basic
import Zeta2Defs
import Zeta2Hat

namespace Zeta2HatRep

open Zeta2Defs Zeta2Hat Nat Finset

/-! ## `Rep̂`, its evaluation, and `Φ̂` — the definitions PAIR-4 needs to be STATED -/

/-- **`Rep̂`** — the hat's partial-fraction data: `(B, A)`, the order-1 and order-2 coefficient
families at the poles `t = −k`.  No polynomial part (deg num = deg den − 2) and no Bernoulli
tail: that is the whole way in which `Φ̂` is simpler than tale-1's `Φ`. -/
abbrev Rephat := (ℕ →₀ ℚ) × (ℕ →₀ ℚ)

/-- The evaluation map `Rep̂ → (ℚ → ℚ)`.  A pair `(B, A)` REPRESENTS a function `f` when this
agrees with `f` off the poles; PAIR-3's `rep̂_injective` is injectivity of THIS map. -/
def evalRep (r : Rephat) (t : ℚ) : ℚ :=
  r.1.sum (fun k b => b / (t + (k : ℚ))) + r.2.sum (fun k a => a / (t + (k : ℚ)) ^ 2)

/-- `L_k = 2k − 8N − 2`, the alternating-sum length at the contour `Ĉ N = −4N − 3/4`.  Nat
subtraction is faithful: every pole of the hat member has `k ≥ 9N+1`, so `2k ≥ 18N+2 ≥ 8N+2`. -/
def Lhat (N k : ℕ) : ℕ := 2 * k - (8 * N + 2)

/-- **`Φ̂ N`** — the pairing functional at the cell `Ĉ N`, ℚ³-valued:
`(rational, ζ(2), ln 2)`.  The kernel `π/sin 2πt` has no constant term in its Laurent expansion
at an even lattice point, so the ζ(2) coordinate is the order-2 coefficient sum alone. -/
def Phihat (N : ℕ) (r : Rephat) : ℚ × ℚ × ℚ :=
  (r.1.sum (fun k b => b * altH 1 (Lhat N k)) + 2 * r.2.sum (fun k a => a * altH 2 (Lhat N k)),
   r.2.sum (fun _ a => a),
   r.1.sum (fun _ b => b))

/-! ## The hat member and its representation -/

/-- `R̂ₙ/Π̂` as an explicit rational function (`z2a.hat_rational`; PAIR-0 design notes). -/
def hatMember (n : ℕ) (t : ℚ) : ℚ :=
  ((∏ l ∈ Icc (3 * n + 2) (20 * n + 1), (2 * t + (l : ℚ)))
      * (∏ l ∈ Icc 1 (5 * n), (t + (l : ℚ))))
    / ((∏ l ∈ Icc (7 * n + 1) (18 * n + 1), (t + (l : ℚ)))
      * (∏ l ∈ Icc (9 * n + 1) (20 * n + 1), (t + (l : ℚ))))

/-- The order-2 family: `hatA n j` at the double pole `k = 10n+1+j`, `j ≤ 8n`. -/
noncomputable def repHatA (n : ℕ) : ℕ →₀ ℚ :=
  ∑ j ∈ range (8 * n + 1), Finsupp.single (10 * n + 1 + j) ((hatA n j : ℚ))

/-- The order-1 family: `hatA·hatLam` at the double poles, `hatBlo` on the lo simple run
`k ∈ [9n+1, 10n]`, `hatBhi` on the hi simple run `k ∈ [18n+2, 20n+1]`. -/
noncomputable def repHatB (n : ℕ) : ℕ →₀ ℚ :=
  (∑ j ∈ range (8 * n + 1), Finsupp.single (10 * n + 1 + j) ((hatA n j : ℚ) * hatLam n j))
    + (∑ i ∈ range n, Finsupp.single (9 * n + 1 + i) (hatBlo n i))
    + (∑ i ∈ range (2 * n), Finsupp.single (18 * n + 2 + i) (hatBhi n i))

/-- **`repHat n : Rep̂`** — the candidate representation of `R̂ₙ`. -/
noncomputable def repHat (n : ℕ) : Rephat := (repHatB n, repHatA n)

/-! ## The reduction lemmas — every coordinate of `Φ̂` is ADDITIVE in the coefficient value

`repHat n` is a `Finset.sum` of `Finsupp.single`s, and every functional `Φ̂` and `evalRep` apply
is of the form `fun k b => b * (something depending on k)`, hence additive in `b`.  So the
`Finsupp.sum` distributes over the `Finset.sum` with NO injectivity-of-keys side condition —
which is what makes the evaluation half of PAIR-4 general-`n` bookkeeping rather than a
per-`n` computation. -/

theorem sum_finsupp_gen {g : ℕ → ℚ → ℚ} (h0 : ∀ k, g k 0 = 0)
    (hadd : ∀ k b₁ b₂, g k (b₁ + b₂) = g k b₁ + g k b₂) (s : Finset ℕ) (F : ℕ → (ℕ →₀ ℚ)) :
    (∑ i ∈ s, F i).sum g = ∑ i ∈ s, (F i).sum g := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.sum_add_index' h0 hadd, ih]

theorem repHatA_sum {g : ℕ → ℚ → ℚ} (h0 : ∀ k, g k 0 = 0)
    (hadd : ∀ k b₁ b₂, g k (b₁ + b₂) = g k b₁ + g k b₂) (n : ℕ) :
    (repHatA n).sum g = ∑ j ∈ range (8 * n + 1), g (10 * n + 1 + j) ((hatA n j : ℚ)) := by
  rw [repHatA, sum_finsupp_gen h0 hadd]
  exact Finset.sum_congr rfl fun _ _ => Finsupp.sum_single_index (h0 _)

theorem repHatB_sum {g : ℕ → ℚ → ℚ} (h0 : ∀ k, g k 0 = 0)
    (hadd : ∀ k b₁ b₂, g k (b₁ + b₂) = g k b₁ + g k b₂) (n : ℕ) :
    (repHatB n).sum g
      = (∑ j ∈ range (8 * n + 1), g (10 * n + 1 + j) ((hatA n j : ℚ) * hatLam n j))
        + (∑ i ∈ range n, g (9 * n + 1 + i) (hatBlo n i))
        + (∑ i ∈ range (2 * n), g (18 * n + 2 + i) (hatBhi n i)) := by
  rw [repHatB, Finsupp.sum_add_index' h0 hadd, Finsupp.sum_add_index' h0 hadd,
    sum_finsupp_gen h0 hadd, sum_finsupp_gen h0 hadd, sum_finsupp_gen h0 hadd]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
    exact Finset.sum_congr rfl fun _ _ => Finsupp.sum_single_index (h0 _)

/-! ## The lengths `L_k` at the member's OWN cell, and the evaluation half at general `n` -/

theorem Lhat_double (n j : ℕ) : Lhat n (10 * n + 1 + j) = 12 * n + 2 * j := by
  unfold Lhat; omega

theorem Lhat_lo (n i : ℕ) : Lhat n (9 * n + 1 + i) = 10 * n + 2 * i := by
  unfold Lhat; omega

theorem Lhat_hi (n i : ℕ) : Lhat n (18 * n + 2 + i) = 28 * n + 2 + 2 * i := by
  unfold Lhat; omega

/-- **The ζ(2) coordinate, at EVERY cell and every `n`**: `Σ_k A_k = −hatQ n`.

The cell `N` is a free variable here — the order-2 coefficient sum does not see `L`, so the
ζ(2) coordinate is CELL-INDEPENDENT.  Measured first in `hat_rep_probe.py` (section C: the
ζ(2) coordinate never breaks outside the belt, only the rational one does), and that is why
PAIR-6's `hatQ_rec` does not inherit PAIR-4's belt hypothesis. -/
theorem Phihat_zeta2_coord (N n : ℕ) : (Phihat N (repHat n)).2.1 = -(hatQ n : ℚ) := by
  show (repHatA n).sum (fun _ a => a) = _
  rw [repHatA_sum (fun _ => rfl) (fun _ _ _ => rfl), hatQ]
  push_cast
  ring

/-- **The rational coordinate, at the member's OWN cell `Ĉ n`, for every `n`**:
`Σ_k B_k·A(L_k,1) + 2·Σ_k A_k·A(L_k,2) = hatP n`.  Pure `Finset` bookkeeping once the three
`L_k` laws are in hand — `hatP` was DEFINED as this sum, and this theorem is what makes that
definition a statement about the representation rather than a transcription. -/
theorem Phihat_rat_coord (n : ℕ) : (Phihat n (repHat n)).1 = hatP n := by
  show (repHatB n).sum (fun k b => b * altH 1 (Lhat n k))
      + 2 * (repHatA n).sum (fun k a => a * altH 2 (Lhat n k)) = _
  rw [repHatB_sum (g := fun k b => b * altH 1 (Lhat n k))
      (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    repHatA_sum (g := fun k a => a * altH 2 (Lhat n k))
      (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), hatP]
  simp only [Lhat_double, Lhat_lo, Lhat_hi]
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ =>
    (by ring : (hatA n j : ℚ) * (hatLam n j * altH 1 (12 * n + 2 * j)
      + 2 * altH 2 (12 * n + 2 * j))
      = (hatA n j : ℚ) * hatLam n j * altH 1 (12 * n + 2 * j)
        + 2 * ((hatA n j : ℚ) * altH 2 (12 * n + 2 * j))))]
  rw [Finset.sum_add_distrib]
  ring

/-! ## The n = 0 instance — the smallest one, where `R̂₀/Π̂ = 1/(t+1)²`

One double pole at `k = 1`, `A₁ = 1`, `B₁ = 0`, `L₁ = 0`, so every alternating sum is empty:
`Φ̂ 0 (repHat 0) = (0, 1, 0) = (hatP 0, −hatQ 0, 0)`. -/

theorem repHatA_zero : repHatA 0 = Finsupp.single 1 (1 : ℚ) := by
  simp [repHatA, hatA]

theorem hatLam_zero : hatLam 0 0 = 0 := by
  simp [hatLam, harm]

theorem repHatB_zero : repHatB 0 = 0 := by
  simp [repHatB, hatLam_zero]

theorem hatPi_zero : hatPi 0 = 1 := by
  simp [hatPi]

theorem hatMember_zero (t : ℚ) : hatMember 0 t = 1 / ((t + 1) * (t + 1)) := by
  norm_num [hatMember]

/-- **The representation half at `n = 0`**: `repHat 0` represents `Π̂(0)·(R̂₀/Π̂) = 1/(t+1)²`. -/
theorem hat_rep_zero (t : ℚ) (ht : t + 1 ≠ 0) :
    evalRep (repHat 0) t = hatPi 0 * hatMember 0 t := by
  rw [hatPi_zero, hatMember_zero, evalRep, repHat, repHatA_zero, repHatB_zero]
  simp only [Finsupp.sum_zero_index, Finsupp.sum_single_index, zero_div, Nat.cast_one]
  field_simp
  ring

/-- **The evaluation half at `n = 0`**: `Φ̂` at the member's own cell reads off the coordinates
`Zeta2Hat` computes as finite sums — with the `ln 2` coordinate `0`. -/
theorem Phihat_zero : Phihat 0 (repHat 0) = (hatP 0, -(hatQ 0 : ℚ), 0) := by
  rw [hatP_zero, hatQ_zero, Phihat, repHat, repHatA_zero, repHatB_zero]
  simp [Lhat, altH]

end Zeta2HatRep

#print axioms Zeta2HatRep.sum_finsupp_gen
#print axioms Zeta2HatRep.repHatA_sum
#print axioms Zeta2HatRep.repHatB_sum
#print axioms Zeta2HatRep.Phihat_zeta2_coord
#print axioms Zeta2HatRep.Phihat_rat_coord
#print axioms Zeta2HatRep.repHatA_zero
#print axioms Zeta2HatRep.repHatB_zero
#print axioms Zeta2HatRep.hatMember_zero
#print axioms Zeta2HatRep.hat_rep_zero
#print axioms Zeta2HatRep.Phihat_zero
