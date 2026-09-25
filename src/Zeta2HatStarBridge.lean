/-
# Row PAIR-5, phase 5H — the boundary vanishing AT THE CHAIN'S OWN `b̂` and `x̂`

`docs/future/zeta2-lean-chain.md` row PAIR-5 (§PAIR-5 design notes, attempt 6).

**What the row owed after attempt 5.**  `Zeta2HatRepS.hbdy_hat_n` proves
`Φ̂ n (repDelta (repS n bh xh)) = 0` for every `n ≥ 2` and every `bh xh : ℚ[X]` with
`bh.natDegree ≤ 5` / `xh.natDegree ≤ 120` — a family that provably CONTAINS the chain's own
pair but does not NAME it, and a `#print axioms` receipt on a ∀-statement is not a receipt on
the instance the chain consumes (`skills/LEAN.md` §2).  This file names the pair.

**THE FINDING THAT RESHAPED THE PHASE — this is a TRANSPOSE, not an instantiation, and two
earlier passes priced it as the latter.**  `StarForallCandt2Base`'s own header states the
convention: *"`F t : ℚ[X]` is the CLEARED (★) residual as a polynomial in `n`, with the contour
variable `t` a parameter"*.  So the base's `afProd bFacs t` and `polB2 xCoeffs s` are
polynomials **in `n`**, with the contour variable a scalar parameter, while `hbdy_hat_n`'s
`bh xh : ℚ[X]` are polynomials **in the contour variable** at a fixed `n : ℕ`
(`numS n bh xh` multiplies them by runs in `X`; `shat_eq` evaluates `bh.eval t * xh.eval t`).
**The two sides hold the same two objects with the variables exchanged**, so `hbdy_hat_n`
cannot be applied to `polB2 xCoeffs s` at all — it is the wrong `ℚ[X]`.  §2 below builds the
two transposes, `xT` and `afProdT`, and ties each to the base's original by a proved `eval`
lemma.  That is the phase's content; the row's own theorem really is one term application, and
the estimate that called it "one line" priced that line and not the object it is applied to.

**AND THE HEADLINE THEOREM ALONE CERTIFIES NOTHING — measured, by this file's own falsifier
arm `A5`, and it is the most important fact in this header.**  `hbdy_hat_star` is a pure
instantiation of `hbdy_hat_n`, which holds for ANY degree-bounded pair; so perturbing §2's
transpose to a FALSE statement (the variables NOT exchanged) leaves `hbdy_hat_star` GREEN.
A 5H shipping only the instantiation would be ceremonial, and would move LEAN.md §2's defect
one level rather than fix it.  What makes this a receipt about the CHAIN's objects is the pair
of TIES, **`xHat_eval` and `bHat_eval`** — the only declarations here that can see the
difference between the chain's `x̂`/`b̂` and an arbitrary degree-bounded pair.  They are row
OUTPUT, not helper lemmas, and neither half of the pair is the deliverable alone.

**AND SAY EXACTLY WHAT THE TIES PIN, because the sentence above oversells if left alone.**  The
ties are stated `∀ (n : ℕ) (s : ℚ)`, so each fixes its polynomial uniquely (over an infinite
field a polynomial is determined by its evaluation function) — they pin `xHat`/`bHat` **relative
to `xCoeffs`/`bFacs`**: that the objects handed to `hbdy_hat_n` really are the base's own data,
transposed, with `b` shifted by `−1`.  **They do NOT pin the base's coefficient VALUES.**  Both
ties are instances of lemmas generic in the data (`xHat_eval := xT_eval _ _ _`), so an
`xCoeffs` with the right SPINE and wrong coefficients leaves all ten receipts green.  That
residual is not carried in Lean at all and is not meant to be: it is carried by the committed
manifest hash, by `run_probe.sh`'s refusal on a base it cannot vouch for (falsifier arms P1/P2),
and by `transpose_probe.py` reading the engine's own `coords/starcoords_cand-t2.txt`.  Two
different guards for two different claims, and neither substitutes for the other.

**`dx = 120` is the CONTOUR degree, not the `n`-degree**, which is what makes the row's
`hx : xh.natDegree ≤ 120` satisfiable at the real `x̂`: `polB2 (l :: ls) s = polB l + C s *
polB2 ls s`, so `xCoeffs`'s OUTER index is the power of the contour variable and the inner list
carries the powers of `n`.  Independently, `Zeta2HatRawPoles.denS_natDegree` gives
`deg denS = 22n+116` and `deg numS = 5 + dx + (17n−9) + 5n`, which agree iff `dx = 120`; the
base's header says `dx = 120, J = 3, 125 coordinates` and gives the certificate's `n`-degree as
the DIFFERENT number 272 in the same sentence.  Both bounds are TIGHT, measured in exact ℚ by
`transpose_probe.py` §B (`X₁₂₀(n) ≠ 0` on the whole ladder, `b̂`'s five leads all nonzero).

**The object named is the CLEARED certificate** `Xₖ = Aₖ·(L/Bₖ)`, because that is the one the
chain's Lean side carries — `star_forall`'s `F` is cleared and the uncleared `x̂` exists in no
Lean file.  The un-clearing scalar `L` is PAIR-6/PAIR-7's, not this row's; `transpose_probe.py`
§E measures `deg_n L = 154` and `L(n) ≠ 0` at every integer `n ∈ [0, 4000]`, recorded there and
in PAIR-6's cell rather than claimed here.

**What this file does NOT do.**  It proves no new mathematics — net new arithmetic is zero.  It
does not touch `Ŝ`'s reduced pole structure (`Zeta2HatCancel`, which this route never needs and
which 5I has now measured PAIR-6 does not need either).  It does not close the chain: the row it
closes is one of 42, and `Zeta2Target.zeta2_not_liouvilleWith` is still `sorry`.  It says nothing
about `Σⱼ α̃ⱼ·hatQ(n+j) = 0` — that is PAIR-6 — nor about whether PAIR-7's `αⱼ` are the cleared
`α̃ⱼ` or the uncleared ones.

**The two `rfl`s are the only place this file touches the engine's data, and they read a SPINE.**
`xCoeffs` is a list of 121 opaque names and `bFacs` five triples; the 10 MB of coefficients is
load-bearing for the OBJECT and for no proof.  Everything above the spine is generic in the data,
which is why `A1`/`A2` (perturbing a spine length) leave the transposes green and why re-greening
after a coords change is two integers and 4 s.

**How to elaborate** — Lean NEVER runs on the laptop (owner rule 2026-09-07):

    sh external_tests/zeta2_star_b1/run_probe.sh Zeta2HatStarBridge.lean

That case REFUSES rather than skips if `StarForallCandt2Base.lean` is absent from the box's
`probes/asm`, or is not byte-identical to the committed
`modules/MANIFEST-cand-t2-kernel.sha256` at `# points all` / `# encoding kernel` /
`# assemble 1`.  The base is ~16 MB, generated and deliberately not committed (§12.7's archive
rule), so a file-exists check is exactly the residual risk this design named: a base that is
present but wrong-flavoured would elaborate a green for different objects.  Receipts:
`out_axioms_starbridge.txt`.  Falsifier: `falsify_hbdy_star.sh` → `out_hbdy_star_falsify.txt`.
Second implementation, in exact ℚ and a different language: `transpose_probe.py`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.Tactic
import Zeta2HatRepS
import StarForallCandt2Base

namespace Zeta2HatStarBridge

-- `Zeta2HatPoles.bhat` is a DIFFERENT object (a residue function `ℚ → ℚ`) and is in scope
-- transitively through `Zeta2HatRepS`.  `bHat` below differs from it in case and in namespace,
-- and `Zeta2HatPoles` is deliberately not opened here.
open Polynomial StarForallCandt2

/-! ## 1. The two SPINE facts -/

theorem bFacs_length : bFacs.length = 5 := rfl

theorem xCoeffs_length : xCoeffs.length = 121 := rfl

/-! ## 2. The transposes, generic in the data -/

/-- The `x` transpose: the base's `polB2 ls s : ℚ[X]` is a polynomial in `n`; this is the same
data read as a polynomial in the contour variable, with `n` the parameter. -/
noncomputable def xT (ls : List (List ℚ)) (n : ℚ) : ℚ[X] :=
  polB (ls.map (fun l => (polB l).eval n))

theorem xT_eval (ls : List (List ℚ)) (n s : ℚ) :
    (xT ls n).eval s = (polB2 ls s).eval n := by
  simp only [xT]
  rw [polB_eval, polB2_eval]
  induction ls with
  | nil => simp
  | cons l ls ih => simp only [List.map_cons, List.foldr_cons, ih]

theorem xT_natDegree_le (ls : List (List ℚ)) (n : ℚ) (d : ℕ) (h : ls.length ≤ d + 1) :
    (xT ls n).natDegree ≤ d :=
  polB_natDegree_le _ d (by simpa using h)

/-- The `b` transpose, same convention as `xT`. -/
noncomputable def afProdT : List (ℚ × ℚ × ℚ) → ℚ → ℚ[X]
  | [], _ => 1
  | f :: fs, n => (C f.1 * X + C (f.2.1 * n + f.2.2)) * afProdT fs n

theorem afProdT_eval : ∀ (fs : List (ℚ × ℚ × ℚ)) (n s : ℚ),
    (afProdT fs n).eval s = (afProd fs s).eval n := by
  intro fs
  induction fs with
  | nil => intro n s; simp [afProdT, afProd_eval]
  | cons f fs ih =>
    intro n s
    have hr := ih n s
    simp only [afProdT, eval_mul, eval_add, eval_C, eval_X, hr, afProd_eval, List.foldr_cons]
    ring

theorem afProdT_natDegree_le : ∀ (fs : List (ℚ × ℚ × ℚ)) (n : ℚ),
    (afProdT fs n).natDegree ≤ fs.length := by
  intro fs
  induction fs with
  | nil => intro n; simp [afProdT]
  | cons f fs ih =>
    intro n
    have h1 : ((C f.1 * X + C (f.2.1 * n + f.2.2) : ℚ[X])).natDegree ≤ 1 := by
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · exact le_trans (natDegree_C_mul_le _ _) (by simp)
      · simp only [natDegree_C]; omega
    have h2 := ih n
    have hm := natDegree_mul_le (p := (C f.1 * X + C (f.2.1 * n + f.2.2) : ℚ[X]))
      (q := afProdT fs n)
    show ((C f.1 * X + C (f.2.1 * n + f.2.2)) * afProdT fs n).natDegree ≤ (f :: fs).length
    simp only [List.length_cons]
    omega

/-! ## 3. THE ROW'S TWO OBJECTS, NAMED -/

/-- `x̂ n` — the CLEARED certificate `x(n, ·)` as a polynomial in the contour variable. -/
noncomputable def xHat (n : ℕ) : ℚ[X] := xT xCoeffs (n : ℚ)

/-- `b̂(·−1) n` — the (★) relation's `b (s − 1)` as a polynomial in the contour variable.  The
`.comp (X − C 1)` is not decoration: `star_telescopes`' `hS` reads `b (s − 1)`, and dropping the
shift is falsifier arm `A6` here and `shift-sign` in `transpose_probe.py`. -/
noncomputable def bHat (n : ℕ) : ℚ[X] := (afProdT bFacs (n : ℚ)).comp (X - C 1)

theorem xHat_natDegree (n : ℕ) : (xHat n).natDegree ≤ 120 :=
  xT_natDegree_le xCoeffs _ 120 (by rw [xCoeffs_length])

theorem bHat_natDegree (n : ℕ) : (bHat n).natDegree ≤ 5 := by
  refine le_trans natDegree_comp_le ?_
  rw [natDegree_X_sub_C, mul_one]
  exact le_trans (afProdT_natDegree_le bFacs _) (by rw [bFacs_length])

/-! ## 4. THE TIES — the half that carries the row

`hbdy_hat_star` below is insensitive to whether the objects it names are the chain's (arm `A5`).
These two theorems are the ONLY declarations that can see the difference, so they are the row's
output beside it and not helper lemmas. -/

theorem xHat_eval (n : ℕ) (s : ℚ) : (xHat n).eval s = (polB2 xCoeffs s).eval (n : ℚ) :=
  xT_eval _ _ _

theorem bHat_eval (n : ℕ) (s : ℚ) :
    (bHat n).eval s = (afProd bFacs (s - 1)).eval (n : ℚ) := by
  rw [bHat, eval_comp]
  simp only [eval_sub, eval_X, eval_C]
  exact afProdT_eval bFacs _ _

/-! ## 5. THE ROW — `hbdy-hat` at the chain's own pair, not at a family containing it -/

theorem hbdy_hat_star (n : ℕ) (hn : 2 ≤ n) :
    Zeta2HatRep.Phihat n
        (Zeta2HatShift.repDelta (Zeta2HatRepS.repS n (bHat n) (xHat n))) = 0 :=
  Zeta2HatRepS.hbdy_hat_n n hn (bHat n) (xHat n) (bHat_natDegree n) (xHat_natDegree n)

/-! ## 6. The row's SECOND obligation at the same pair, in the star side's own vocabulary —
this is the statement PAIR-6 pushes through `Zeta2HatInj.Phihat_of_evalRep`, at `t+1` and at `t`,
where the two `C₀` terms cancel identically under `Zeta2HatShift.evalRep_repDelta` (phase 5I). -/

theorem evalRep_repS_star (n : ℕ) (hn : 1 ≤ n) (t : ℚ)
    (ht : ∀ k ∈ Zeta2HatRawPoles.idxS1 n ∪ Zeta2HatRawPoles.idxS2 n, t + ((k : ℕ) : ℚ) ≠ 0)
    (hblk : (Zeta2HatShatForm.dBlock n).eval t ≠ 0) :
    Zeta2HatRep.evalRep (Zeta2HatRepS.repS n (bHat n) (xHat n)) t
      = (afProd bFacs (t - 1)).eval (n : ℚ) * (polB2 xCoeffs t).eval (n : ℚ)
            * Zeta2HatRep.hatMember n t
          / (Zeta2HatShatForm.dRuns n * Zeta2HatShatForm.dBlock n).eval t
        - (Zeta2HatRawPoles.numS n (bHat n) (xHat n)).coeff (22 * n + 116) := by
  rw [Zeta2HatRepS.evalRep_repS_eq_shat n hn (bHat n) (xHat n)
        (bHat_natDegree n) (xHat_natDegree n) t ht hblk, bHat_eval, xHat_eval]

end Zeta2HatStarBridge

#print axioms Zeta2HatStarBridge.bFacs_length
#print axioms Zeta2HatStarBridge.xCoeffs_length
#print axioms Zeta2HatStarBridge.xT_eval
#print axioms Zeta2HatStarBridge.afProdT_eval
#print axioms Zeta2HatStarBridge.xHat_natDegree
#print axioms Zeta2HatStarBridge.bHat_natDegree
#print axioms Zeta2HatStarBridge.xHat_eval
#print axioms Zeta2HatStarBridge.bHat_eval
#print axioms Zeta2HatStarBridge.hbdy_hat_star
#print axioms Zeta2HatStarBridge.evalRep_repS_star
