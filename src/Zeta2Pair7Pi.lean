/-
# Row PAIR-7, part 1 — the Π-rebase lemmas, and the ∀-`n` PAIR-K2 bridge

`docs/future/zeta2-lean-chain.md` row PAIR-7 identifies the HAT's (★) recurrence operator with
the CHAIN's.  On the sequences those operators carry a prefactor rebase with exponent **−1**
(`Zeta2HatRep`'s own header: `evalRep (repHat n) t = hatPi n * hatMember n t`, so the
coefficient sitting on `repHat (n+j)` carries `1/Π̂(n+j)`):

    β̂ⱼ(n) = α̃ʰⱼ(n)·Π̂(n)/Π̂(n+j)        γⱼ(n) = α̃ᶜⱼ(n)·Π(n)/Π(n+j)

This file supplies the two things the four per-`j` identity modules need and the corpus did not
have, both stated over the LANDED definitions (`Zeta2Hat.hatPi`, `Zeta2Defs.candidateM.Pin`) so
that nothing here is about a re-declared copy of the prefactors:

1. **The Π-rebase**, `hatPi_rebase` / `Pin_rebase` — a factorial quotient `Π(n)/Π(n+j)` is a
   quotient of **affine runs** `∏_{i=1}^{c·j} (c·n + i)`, and an affine run is exactly what
   `StarKernel.zprod` builds.  The route is one elementary induction (`cast_factorial_add`),
   not `Nat.ascFactorial`: the row's design named the `ascFactorial` API as the likely one, and
   the direct induction turned out to need no API surface at all beyond `Nat.factorial_succ`.
2. **`qeval_map_hornerQ`** — `StarKernel.qeval_map_zdivq`'s ∀-`n` twin.  PAIR-K2's landed bridge
   is stated at an INTEGER grid point (`hornerZ`); PAIR-7 is a ∀-`n` polynomial identity, so the
   same step is needed at a symbolic `t : ℚ` against `hornerQ`.  This is the link from
   `(polB alⱼ).eval n` (what PAIR-6 holds, via `polB_eval`) to `hornerQ zⱼ n / dⱼ` (what the
   kernel decides).

`pair7_assemble` is the last mile, kept generic and proved once: the four per-`j` modules each
apply it rather than re-doing the field algebra, so the sign-and-denominator seam that this
chain has already lost a row to (L7ID-0) exists in exactly one place.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732, buildbox.
-/
import Zeta2Hat
import StarKernelBridge

namespace Zeta2Pair7

open Nat StarKernel Zeta2Defs

/-! ## `runFacs` — the affine run `∏_{i=1}^{m} (c·t + i)` as `zprod` factor data -/

/-- The factor list of `∏_{i=1}^{m} (c·t + i)` in `StarKernel.zprod`'s `(lead, off)` form.

The `i : ℕ` annotation is load-bearing: without it Lean unifies the lambda's domain with `ℤ`
and inserts a `List ℕ → List ℤ` coercion, so `runFacs` becomes a map over a COERCED list and
every `List.map_append` rewrite below fails to find its pattern (MEASURED: that is exactly how
this file first came back red). -/
def runFacs (c m : ℕ) : List (ℤ × ℤ) :=
  (List.range m).map (fun i : ℕ => ((c : ℤ), (i : ℤ) + 1))

/-- `hornerQ_zprod`'s right-hand side, named so it can be inducted on. -/
def qfacProd (t : ℚ) (fs : List (ℤ × ℤ)) : ℚ :=
  fs.foldr (fun f acc => ((f.1 : ℚ) * t + (f.2 : ℚ)) * acc) 1

theorem qfacProd_nil (t : ℚ) : qfacProd t [] = 1 := rfl

theorem qfacProd_cons (t : ℚ) (f : ℤ × ℤ) (fs : List (ℤ × ℤ)) :
    qfacProd t (f :: fs) = ((f.1 : ℚ) * t + (f.2 : ℚ)) * qfacProd t fs := rfl

/-- The landed `hornerQ_zprod`, read in `qfacProd`'s vocabulary. -/
theorem hornerQ_zprod_eq (fs : List (ℤ × ℤ)) (t : ℚ) :
    hornerQ (zprod fs) t = qfacProd t fs := hornerQ_zprod fs t

theorem qfacProd_append (t : ℚ) (fs gs : List (ℤ × ℤ)) :
    qfacProd t (fs ++ gs) = qfacProd t fs * qfacProd t gs := by
  induction fs with
  | nil => rw [List.nil_append, qfacProd_nil, one_mul]
  | cons f fs ih => rw [List.cons_append, qfacProd_cons, ih, qfacProd_cons, mul_assoc]

theorem runFacs_succ (c m : ℕ) :
    runFacs c (m + 1) = runFacs c m ++ [((c : ℤ), (m : ℤ) + 1)] := by
  rw [runFacs, runFacs, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The run, as a `Finset.prod` — the shape the factorial induction below produces. -/
theorem qfacProd_runFacs (c m : ℕ) (t : ℚ) :
    qfacProd t (runFacs c m) = ∏ i ∈ Finset.range m, ((c : ℚ) * t + (i : ℚ) + 1) := by
  induction m with
  | zero => rw [runFacs]; simp [qfacProd]
  | succ m ih =>
    rw [runFacs_succ, qfacProd_append, ih, Finset.prod_range_succ, qfacProd_cons, qfacProd_nil,
      mul_one]
    push_cast
    ring

/-- Every factor of a run at a NATURAL point is `≥ 1`, so the run is positive — this is what
lets the rebase be divided through, and it is the only nonvanishing the Π side needs. -/
theorem qfacProd_runFacs_pos (c m n : ℕ) : 0 < qfacProd (n : ℚ) (runFacs c m) := by
  rw [qfacProd_runFacs]
  refine Finset.prod_pos ?_
  intro i _
  positivity

/-! ## The factorial shift -/

/-- `(a + m)! = a! · ∏_{i=1}^{m} (a + i)`, over ℚ.  One induction; no `ascFactorial`. -/
theorem cast_factorial_add (a m : ℕ) :
    ((a + m)! : ℚ) = (a ! : ℚ) * ∏ i ∈ Finset.range m, ((a : ℚ) + (i : ℚ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih, ← Nat.add_assoc, Nat.factorial_succ]
    push_cast
    ring

/-- The shift at slope `c`: `(c(n+j))! = (cn)! · ∏_{i=1}^{cj} (cn + i)`, the right-hand product
written as the run `runFacs c (c*j)` the kernel data is built from. -/
theorem cast_factorial_run (c n j : ℕ) :
    (((c * (n + j))! : ℕ) : ℚ) = (((c * n)! : ℕ) : ℚ) * qfacProd (n : ℚ) (runFacs c (c * j)) := by
  rw [qfacProd_runFacs]
  have h : c * (n + j) = c * n + c * j := by ring
  rw [h, cast_factorial_add]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _
  push_cast
  ring

/-! ## The two prefactors, rebased -/

/-- `Π̂(n) = (11n)!²/((17n)!(5n)!)`, with the casts distributed. -/
theorem hatPi_eq (n : ℕ) :
    Zeta2Hat.hatPi n = (((11 * n)! : ℕ) : ℚ) * (((11 * n)! : ℕ) : ℚ)
      / ((((17 * n)! : ℕ) : ℚ) * (((5 * n)! : ℕ) : ℚ)) := by
  unfold Zeta2Hat.hatPi
  push_cast
  ring

theorem hatPi_pos (n : ℕ) : 0 < Zeta2Hat.hatPi n := by
  rw [hatPi_eq]
  refine div_pos (mul_pos ?_ ?_) (mul_pos ?_ ?_) <;>
    exact_mod_cast Nat.factorial_pos _

/-- **The hat prefactor's rebase.**  `Π̂(n)·(∏_{i≤11j}(11n+i))² = Π̂(n+j)·∏_{i≤17j}(17n+i)·∏_{i≤5j}(5n+i)`,
i.e. `Π̂(n)/Π̂(n+j)` is the affine-run quotient the kernel data encodes.  Note the DIRECTION:
the numerator runs come from `Π̂`'s DENOMINATOR slopes (17, 5) and the denominator run from its
numerator slope (11), which is the exponent `−1` the row's cell had backwards. -/
theorem hatPi_rebase (n j : ℕ) :
    Zeta2Hat.hatPi n
        * (qfacProd (n : ℚ) (runFacs 11 (11 * j)) * qfacProd (n : ℚ) (runFacs 11 (11 * j)))
      = Zeta2Hat.hatPi (n + j)
        * (qfacProd (n : ℚ) (runFacs 17 (17 * j)) * qfacProd (n : ℚ) (runFacs 5 (5 * j))) := by
  have f17 : ((((17 : ℕ) * n)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have f5 : ((((5 : ℕ) * n)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have q17 : qfacProd (n : ℚ) (runFacs 17 (17 * j)) ≠ 0 := (qfacProd_runFacs_pos _ _ _).ne'
  have q5 : qfacProd (n : ℚ) (runFacs 5 (5 * j)) ≠ 0 := (qfacProd_runFacs_pos _ _ _).ne'
  rw [hatPi_eq, hatPi_eq, cast_factorial_run 11 n j, cast_factorial_run 17 n j,
    cast_factorial_run 5 n j]
  field_simp

/-- `Π(n) = (11n)!/((13n)!(9n)!(5n)!)` at the candidate, with the casts distributed. -/
theorem Pin_eq (n : ℕ) :
    candidateM.Pin n = (((11 * n)! : ℕ) : ℚ)
      / ((((13 * n)! : ℕ) : ℚ) * (((9 * n)! : ℕ) : ℚ) * (((5 * n)! : ℕ) : ℚ)) := by
  rw [Zeta2Arith.candidate_Pin]
  push_cast
  ring

/-- **The chain prefactor's rebase**, the twin of `hatPi_rebase` at `Π(n) = (11n)!/((13n)!(9n)!(5n)!)`. -/
theorem Pin_rebase (n j : ℕ) :
    candidateM.Pin n * qfacProd (n : ℚ) (runFacs 11 (11 * j))
      = candidateM.Pin (n + j)
        * (qfacProd (n : ℚ) (runFacs 13 (13 * j)) * qfacProd (n : ℚ) (runFacs 9 (9 * j))
            * qfacProd (n : ℚ) (runFacs 5 (5 * j))) := by
  have f13 : ((((13 : ℕ) * n)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have f9 : ((((9 : ℕ) * n)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have f5 : ((((5 : ℕ) * n)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have q13 : qfacProd (n : ℚ) (runFacs 13 (13 * j)) ≠ 0 := (qfacProd_runFacs_pos _ _ _).ne'
  have q9 : qfacProd (n : ℚ) (runFacs 9 (9 * j)) ≠ 0 := (qfacProd_runFacs_pos _ _ _).ne'
  have q5 : qfacProd (n : ℚ) (runFacs 5 (5 * j)) ≠ 0 := (qfacProd_runFacs_pos _ _ _).ne'
  rw [Pin_eq, Pin_eq, cast_factorial_run 11 n j, cast_factorial_run 13 n j,
    cast_factorial_run 9 n j, cast_factorial_run 5 n j]
  field_simp

/-! ## The rebase, read as a ratio -/

/-- `Π̂(n)/Π̂(n+j) = rn/rd` from the cleared rebase, once `rd` is known nonzero.  Stated against
opaque `rn`, `rd` so the per-`j` module can hand it the values of its own emitted lists. -/
theorem hatPi_ratio_of (n j : ℕ) (rn rd : ℚ) (hrd : rd ≠ 0)
    (hd : rd = qfacProd (n : ℚ) (runFacs 11 (11 * j)) * qfacProd (n : ℚ) (runFacs 11 (11 * j)))
    (hn : rn = qfacProd (n : ℚ) (runFacs 17 (17 * j)) * qfacProd (n : ℚ) (runFacs 5 (5 * j))) :
    Zeta2Hat.hatPi n / Zeta2Hat.hatPi (n + j) = rn / rd := by
  rw [div_eq_div_iff (hatPi_pos (n + j)).ne' hrd, hd, hn]
  rw [hatPi_rebase n j]
  ring

/-- The chain twin of `hatPi_ratio_of`. -/
theorem Pin_ratio_of (n j : ℕ) (sn sd : ℚ) (hsd : sd ≠ 0)
    (hd : sd = qfacProd (n : ℚ) (runFacs 11 (11 * j)))
    (hn : sn = qfacProd (n : ℚ) (runFacs 13 (13 * j)) * qfacProd (n : ℚ) (runFacs 9 (9 * j))
      * qfacProd (n : ℚ) (runFacs 5 (5 * j))) :
    candidateM.Pin n / candidateM.Pin (n + j) = sn / sd := by
  rw [div_eq_div_iff (candidateM.Pin_pos (n + j)).ne' hsd, hd, hn]
  rw [Pin_rebase n j]
  ring

/-! ## The ∀-`n` PAIR-K2 bridge -/

/-- **`qeval_map_zdivq` at a symbolic point.**  The base module carries `alⱼ : List ℚ` as
`zⱼ.map (fun c : ℤ => (c : ℚ) / dⱼ)`; `polB_eval` turns `(polB alⱼ).eval t` into `qeval t alⱼ`,
and this turns that into the integer Horner value over the clearing denominator.  No hypothesis
on `d`: at `d = 0` both sides are `0`, exactly as in the landed integer-point twin. -/
theorem qeval_map_hornerQ (d : ℤ) (t : ℚ) : ∀ p : ZP,
    qeval t (p.map (fun c : ℤ => (c : ℚ) / (d : ℚ))) = hornerQ p t / (d : ℚ) := by
  intro p
  induction p with
  | nil => rw [List.map_nil, qeval_nil, hornerQ_nil]; simp
  | cons c p ih => rw [List.map_cons, qeval_cons, ih, hornerQ_cons]; ring

/-! ## The last mile, proved once -/

/-- **PAIR-7's assembly step.**  From the kernel identity
`K₁·(ah·rn·sd·ld) = K₂·(ac·sn·rd·ln)` and the two clearing facts `dc·dln = K₁·Kg`,
`dh·dld = K₂·Kg` (the generator divides the two scalars by their gcd `Kg` before emitting),
read off the operator statement the row makes:

    (ah/dh)·(rn/rd)·(ld/dld) = (ac/dc)·(sn/sd)·(ln/dln)

i.e. `β̂ⱼ·λden = γⱼ·λnum`.  `Kg ≠ 0` is NOT needed — the gcd only has to be *consistent* between
the two clearing facts, and a spurious `Kg = 0` would make both `dc·dln` and `dh·dld` zero,
which the `dh, dc, dln, dld ≠ 0` hypotheses already forbid. -/
theorem pair7_assemble
    (ah ac rn rd sn sd ln ld dh dc dln dld K1 K2 Kg : ℚ)
    (hdh : dh ≠ 0) (hdc : dc ≠ 0) (hdln : dln ≠ 0) (hdld : dld ≠ 0)
    (hrd : rd ≠ 0) (hsd : sd ≠ 0)
    (hK1 : dc * dln = K1 * Kg) (hK2 : dh * dld = K2 * Kg)
    (hker : K1 * (ah * rn * (sd * ld)) = K2 * (ac * sn * (rd * ln))) :
    ah / dh * (rn / rd) * (ld / dld) = ac / dc * (sn / sd) * (ln / dln) := by
  -- `_root_.` is load-bearing: this file `open Nat`s for the `!` notation, and `simp only`
  -- resolves a bare `div_mul_div_comm` to `Nat.div_mul_div_comm` — a CONDITIONAL rewrite about
  -- ℕ division, which matches nothing here and reports "made no progress" (MEASURED: that is
  -- how this proof first came back red, and the term-level `mul_ne_zero` below is prefixed for
  -- the same reason even though term elaboration would disambiguate it).
  simp only [_root_.div_mul_div_comm]
  rw [_root_.div_eq_div_iff (_root_.mul_ne_zero (_root_.mul_ne_zero hdh hrd) hdld)
    (_root_.mul_ne_zero (_root_.mul_ne_zero hdc hsd) hdln)]
  linear_combination Kg * hker + (ah * rn * ld * sd) * hK1 - (ac * sn * ln * rd) * hK2

end Zeta2Pair7

#print axioms Zeta2Pair7.qfacProd_nil
#print axioms Zeta2Pair7.qfacProd_cons
#print axioms Zeta2Pair7.hornerQ_zprod_eq
#print axioms Zeta2Pair7.qfacProd_append
#print axioms Zeta2Pair7.runFacs_succ
#print axioms Zeta2Pair7.qfacProd_runFacs
#print axioms Zeta2Pair7.hatPi_eq
#print axioms Zeta2Pair7.Pin_eq
#print axioms Zeta2Pair7.qfacProd_runFacs_pos
#print axioms Zeta2Pair7.cast_factorial_add
#print axioms Zeta2Pair7.cast_factorial_run
#print axioms Zeta2Pair7.hatPi_pos
#print axioms Zeta2Pair7.hatPi_rebase
#print axioms Zeta2Pair7.Pin_rebase
#print axioms Zeta2Pair7.hatPi_ratio_of
#print axioms Zeta2Pair7.Pin_ratio_of
#print axioms Zeta2Pair7.qeval_map_hornerQ
#print axioms Zeta2Pair7.pair7_assemble
