import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic

/-!
# StarKernelBridge — from a kernel-checked `List ℤ` identity to `(F t).eval n = 0`

Row PAIR-K of `docs/future/zeta2-lean-chain.md`.  ONE generic theorem, `h0_of_kernel`, applied
once per grid point by every kernel-encoded h0 shard (`star_forall_to_lean.py --h0-encoding
kernel`); nothing in it depends on the data of a point or of a side.

## What it connects

* The h0 module (generated, `StarForall<Side>Base`) states each grid point as
  `theorem h0_n (t : ℚ) : (F t).eval (n : ℚ) = 0`, where `F t : ℚ[X]` is the cleared (★)
  residual as a polynomial in `n`, built from RATIONAL data: factor lists `aFacs bFacs cFacs
  paⱼFacs : List (ℚ × ℚ × ℚ)` (`lead·t + a·n + b`), the certificate's cleared coefficient lists
  `xCoeffs : List (List ℚ)` (`Xₖ(n)` as Horner lists in `n`) and `alⱼ : List ℚ` (`Ãⱼ(n)`).
  Its evaluation lemmas `afProd_eval` / `polB2_eval` / `polB_eval` turn `(F t).eval n` into
  `List.foldr`s over those lists — the shape this file's conclusion is stated in, so a shard
  closes with `simp only [F_def, eval_sub, eval_mul, eval_add, afProd_eval, polB2_eval,
  polB_eval]` followed by ONE `exact h0_of_kernel …`.
* The kernel identity (measured in `zeta2_arith/StarKernel*.lean`, 19–37 s / 2.2 GB per point)
  is over INTEGER data: at a fixed `n`, `L := lcm(den Xₖ(n))`, `M := lcm(den Ãⱼ(n))`,
  `xL := L·X(n)`, `mⱼ := M·Ãⱼ(n)`, the factor lists with `off := a·n + b` (and `off − lead` for
  `b(t − 1)`), and
      `ztrim (zsub (M·[aF·xL(t+1) − bF·xL(t)]) (L·cF·Σⱼ mⱼ·paⱼ)) = []`
  decided by `decide +kernel`.

## The relation, PROVED here (design question (1) of the row)

At a grid point `n`, with `⟦·⟧ₜ := hornerQ · t`,
    `(F t).eval n = ⟦aF⟧ₜ·⟦xL⟧ₜ₊₁/L − ⟦bF⟧ₜ·⟦xL⟧ₜ/L − ⟦cF⟧ₜ·Σⱼ (mⱼ/M)·⟦paⱼ⟧ₜ`
and the kernel identity says `M·(⟦aF⟧ₜ⟦xL⟧ₜ₊₁ − ⟦bF⟧ₜ⟦xL⟧ₜ) = L·⟦cF⟧ₜ·Σⱼ mⱼ⟦paⱼ⟧ₜ`, so
`L·M·(F t).eval n = 0` and `L, M ≠ 0` finishes it.  The data hypotheses that make the first
line true are ℚ-list equalities a shard proves by kernel computation (`decide +kernel`) or
`norm_num` — they are the ONLY per-point cost besides the identity itself.

## The kernel operations

The block between `-- BEGIN kernel ops` and `-- END kernel ops` is byte-identical to the
`PRELUDE` of `external_tests/zeta2_arith/gen_star_kernel_probe.py`, which measured them;
`gen_star_kernel_probe.py --check` diffs the two so they cannot drift (LEAN.md §10).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732, buildbox.
-/

namespace StarKernel

-- BEGIN kernel ops
/-- Dense integer polynomial, low degree first. -/
abbrev ZP := List Int

def zadd : ZP → ZP → ZP
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: zadd p q

def zscale (c : Int) (p : ZP) : ZP := p.map (fun v => c * v)

/-- `zmul p q`: schoolbook, recursing on `p`. -/
def zmul : ZP → ZP → ZP
  | [], _ => []
  | a :: p, q => zadd (zscale a q) (0 :: zmul p q)

/-- `∏ (lead·t + off)` over a list of `(lead, off)`. -/
def zprod : List (Int × Int) → ZP
  | [] => [1]
  | (l, o) :: fs => zmul [o, l] (zprod fs)

/-- `p(t + 1)`, by Horner from the top coefficient: `c + (t + 1)·q` with `(t + 1)·q` written as
`q + t·q = zadd q (0 :: q)` — NEVER as `zmul [1, 1] q`.  Same function, and the kernel's cost
is 150× apart: on the 121-entry, ~1000-digit list of the hat grid's n = 277 the `zmul` form
took 215 s (and its structurally recursive twin over 400 s) where this takes 1.4 s
(MEASURED-buildbox 2026-09-11, `K277Shift*` probes); with it the whole point identity is
flat in n again (19.6 s at n = 277 against 20.7 s at n = 0).  A `let` on the recursive call
changes nothing either way. -/
def zshift1 : ZP → ZP
  | [] => []
  | c :: p => zadd [c] (zadd (zshift1 p) (0 :: zshift1 p))

def zsub (p q : ZP) : ZP := zadd p (zscale (-1) q)

/-- Drop trailing zeros, so two representations of one polynomial compare equal. -/
def ztrim (p : ZP) : ZP := (p.reverse.dropWhile (fun c => decide (c = 0))).reverse
-- END kernel ops

/-! ## Evaluation at a rational point -/

/-- Horner evaluation of an integer coefficient list at `t : ℚ`. -/
def hornerQ (p : ZP) (t : ℚ) : ℚ := p.foldr (fun c acc => (c : ℚ) + t * acc) 0

@[simp] theorem hornerQ_nil (t : ℚ) : hornerQ [] t = 0 := rfl

@[simp] theorem hornerQ_cons (c : ℤ) (p : ZP) (t : ℚ) :
    hornerQ (c :: p) t = (c : ℚ) + t * hornerQ p t := rfl

theorem hornerQ_zadd (p q : ZP) (t : ℚ) : hornerQ (zadd p q) t = hornerQ p t + hornerQ q t := by
  induction p generalizing q with
  | nil => simp [zadd]
  | cons a p ih =>
    cases q with
    | nil => simp [zadd]
    | cons b q =>
      simp only [zadd, hornerQ_cons, ih, Int.cast_add]
      ring

theorem hornerQ_map_mul (c : ℤ) (p : ZP) (t : ℚ) :
    hornerQ (p.map (fun v => c * v)) t = (c : ℚ) * hornerQ p t := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.map_cons, hornerQ_cons, ih, Int.cast_mul]
    ring

theorem hornerQ_zscale (c : ℤ) (p : ZP) (t : ℚ) :
    hornerQ (zscale c p) t = (c : ℚ) * hornerQ p t := hornerQ_map_mul c p t

theorem hornerQ_zmul (p q : ZP) (t : ℚ) : hornerQ (zmul p q) t = hornerQ p t * hornerQ q t := by
  induction p with
  | nil => simp [zmul]
  | cons a p ih =>
    simp only [zmul, hornerQ_zadd, hornerQ_zscale, hornerQ_cons, ih, Int.cast_zero]
    ring

theorem hornerQ_zprod (fs : List (ℤ × ℤ)) (t : ℚ) :
    hornerQ (zprod fs) t = fs.foldr (fun f acc => ((f.1 : ℚ) * t + (f.2 : ℚ)) * acc) 1 := by
  induction fs with
  | nil => simp [zprod]
  | cons f fs ih =>
    obtain ⟨l, o⟩ := f
    simp only [zprod, hornerQ_zmul, ih, List.foldr_cons, hornerQ_cons, hornerQ_nil]
    ring

theorem hornerQ_zshift1 (p : ZP) (t : ℚ) : hornerQ (zshift1 p) t = hornerQ p (t + 1) := by
  induction p with
  | nil => simp [zshift1]
  | cons c p ih =>
    simp only [zshift1, hornerQ_zadd, hornerQ_cons, hornerQ_nil, ih, Int.cast_zero]
    ring

theorem hornerQ_eq_zero_of_all_zero (p : ZP) (hall : ∀ c ∈ p, c = 0) (t : ℚ) :
    hornerQ p t = 0 := by
  induction p with
  | nil => simp
  | cons c p ih =>
    have hc : c = 0 := hall c (List.mem_cons_self)
    have hp : ∀ d ∈ p, d = 0 := fun d hd => hall d (List.mem_cons_of_mem c hd)
    simp [hc, ih hp]

theorem all_zero_of_ztrim_nil (p : ZP) (h : ztrim p = []) : ∀ c ∈ p, c = 0 := by
  unfold ztrim at h
  rw [List.reverse_eq_nil_iff, List.dropWhile_eq_nil_iff] at h
  intro c hc
  simpa using h c (List.mem_reverse.mpr hc)

theorem hornerQ_eq_zero_of_ztrim_nil (p : ZP) (h : ztrim p = []) (t : ℚ) : hornerQ p t = 0 :=
  hornerQ_eq_zero_of_all_zero p (all_zero_of_ztrim_nil p h) t

theorem hornerQ_zsub (p q : ZP) (t : ℚ) : hornerQ (zsub p q) t = hornerQ p t - hornerQ q t := by
  rw [zsub, hornerQ_zadd, hornerQ_zscale]
  push_cast
  ring

/-- The kernel verdict, read at a rational point: `ztrim (zsub p q) = []` gives
`⟦p⟧ₜ = ⟦q⟧ₜ` for every `t`. -/
theorem hornerQ_eq_of_ztrim_zsub (p q : ZP) (t : ℚ) (h : ztrim (zsub p q) = []) :
    hornerQ p t = hornerQ q t := by
  have h0 := hornerQ_eq_zero_of_ztrim_nil _ h t
  rw [hornerQ_zsub] at h0
  linarith

/-- The scaling step, on atoms: `L·M·(F t).eval n` is the kernel identity's difference. -/
theorem bridge_alg (a b c x0 x1 q0 q1 q2 q3 m0 m1 m2 m3 L M : ℚ) (hL : L ≠ 0) (hM : M ≠ 0)
    (hk : M * (a * x1 - b * x0) = L * (c * ((m0 * q0 + m1 * q1) + (m2 * q2 + m3 * q3)))) :
    a * (x1 / L) - b * (x0 / L)
      - c * (m0 / M * q0 + m1 / M * q1 + m2 / M * q2 + m3 / M * q3) = 0 := by
  have hLM : L * M ≠ 0 := mul_ne_zero hL hM
  have hLi : L * L⁻¹ = 1 := mul_inv_cancel₀ hL
  have hMi : M * M⁻¹ = 1 := mul_inv_cancel₀ hM
  have key : (a * (x1 / L) - b * (x0 / L)
      - c * (m0 / M * q0 + m1 / M * q1 + m2 / M * q2 + m3 / M * q3)) * (L * M) = 0 := by
    have e : (a * (x1 / L) - b * (x0 / L)
        - c * (m0 / M * q0 + m1 / M * q1 + m2 / M * q2 + m3 / M * q3)) * (L * M)
        = (a * x1 - b * x0) * M * (L * L⁻¹)
          - c * ((m0 * q0 + m1 * q1) + (m2 * q2 + m3 * q3)) * L * (M * M⁻¹) := by
      ring
    rw [e, hLi, hMi]
    linear_combination hk
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hLM

/-! ## The data predicates a shard proves by computation

Named so that a generated shard states them without a lambda (a bare `fun c => (c : ℚ) / L`
over `xL : List ℤ` elaborates the ascription as the binder's TYPE and coerces the whole list
monadically — measured 2026-09-11, the statement then never finished elaborating), and so that
`decide +kernel` has one definition to unfold. -/

/-- A ℚ factor `(lead, a, b)` at the grid point `n`: `lead·t + (a·n + b)`. -/
def qfac (n : ℚ) (f : ℚ × ℚ × ℚ) : ℚ × ℚ := (f.1, f.2.2 + f.2.1 * n)

/-- The same for `b(t − 1)`: `lead·(t − 1) + a·n + b = lead·t + (a·n + b − lead)`. -/
def qfacs (n : ℚ) (f : ℚ × ℚ × ℚ) : ℚ × ℚ := (f.1, f.2.2 + f.2.1 * n - f.1)

/-- An integer factor `(lead, off)`, cast. -/
def zfac (f : ℤ × ℤ) : ℚ × ℚ := ((f.1 : ℚ), (f.2 : ℚ))

/-- `polB_eval`'s right-hand side: Horner of a ℚ list at `n`. -/
def qeval (n : ℚ) (l : List ℚ) : ℚ := l.foldr (fun c acc => c + n * acc) 0

/-- An integer coefficient over the clearing denominator. -/
def zdiv (L : ℤ) (c : ℤ) : ℚ := (c : ℚ) / L

/-! ## PAIR-K2: the coefficient lists carried as `List ℤ` + one denominator

The base module emits each certificate coefficient list as `xzₖ : List ℤ` with `xdₖ : ℤ` and
`xcₖ : List ℚ := xzₖ.map (fun c : ℤ => (c : ℚ) / (xdₖ : ℚ))`, so that a shard's data fact
`xCoeffs.map (qeval n) = xL.map (zdiv L)` is decided by the kernel over **ℤ** rather than over
ℚ.  MEASURED-buildbox 2026-09-11 (row PAIR-K): a kernel `Rat` op is ~10× a kernel `Int` op and
the ℚ form of that one fact was 110 s of a 125 s point.  Nothing else moves: `xCoeffs`, `F`,
`F_def`, `hdeg`'s statement, `grid`, `hs` and `h0_of_kernel` are untouched — this is the
representation of the *entries*, read back here. -/

/-- Horner evaluation of an integer coefficient list at an INTEGER point.  The ℤ twin of
`hornerQ`; the shard's per-list kernel fact is stated with it. -/
def hornerZ (p : ZP) (n : ℤ) : ℤ := p.foldr (fun c acc => c + n * acc) 0

theorem qeval_nil (n : ℚ) : qeval n [] = 0 := rfl

theorem qeval_cons (n c : ℚ) (l : List ℚ) : qeval n (c :: l) = c + n * qeval n l := rfl

theorem hornerZ_nil (n : ℤ) : hornerZ [] n = 0 := rfl

theorem hornerZ_cons (c : ℤ) (p : ZP) (n : ℤ) :
    hornerZ (c :: p) n = c + n * hornerZ p n := rfl

/-- The base module's `xcₖ`, evaluated at an integer grid point, IS the integer Horner value
over the list's own denominator.  No hypothesis on `d`: at `d = 0` both sides are `0`. -/
theorem qeval_map_zdivq (d nz : ℤ) : ∀ p : ZP,
    qeval (nz : ℚ) (p.map (fun c : ℤ => (c : ℚ) / (d : ℚ)))
      = ((hornerZ p nz : ℤ) : ℚ) / (d : ℚ) := by
  intro p
  induction p with
  | nil => rw [List.map_nil, qeval_nil, hornerZ_nil]; simp
  | cons c p ih =>
    rw [List.map_cons, qeval_cons, ih, hornerZ_cons]
    push_cast
    ring

/-- **PAIR-K2's per-list step**: an INTEGER kernel identity `hornerZ p n · L = xl · d` gives the
ℚ data fact `h0_of_kernel` consumes for that list.  `nq` is passed separately from `nz` because
the shard's goal carries the grid point as a ℚ numeral and `((n : ℤ) : ℚ)` is not that numeral
syntactically; `hn` is one `norm_num` per shard. -/
theorem qeval_map_of_kernel (p : ZP) (d L xl nz : ℤ) (nq : ℚ)
    (hn : ((nz : ℤ) : ℚ) = nq) (hd : (d : ℚ) ≠ 0) (hL : (L : ℚ) ≠ 0)
    (h : hornerZ p nz * L = xl * d) :
    qeval nq (p.map (fun c : ℤ => (c : ℚ) / (d : ℚ))) = zdiv L xl := by
  subst hn
  rw [qeval_map_zdivq, zdiv, div_eq_div_iff hd hL]
  exact_mod_cast h

/-! ## The base module's evaluation shapes, matched to the integer data

`af_foldr_eq` is `afProd_eval`'s right-hand side at `v := n`; `af_foldr_shift_eq` the same at
`t − 1` (the `b` factor); `pol2_foldr_eq` is `polB2_eval`'s after `polB_eval` has fired inside
it.  Each takes the ℚ-list-equals-cast-ℤ-list fact a shard proves by computation. -/

theorem af_foldr_eq (A : List (ℚ × ℚ × ℚ)) (aF : List (ℤ × ℤ)) (n t : ℚ)
    (h : A.map (qfac n) = aF.map zfac) :
    A.foldr (fun f acc => (f.1 * t + f.2.2 + f.2.1 * n) * acc) 1 = hornerQ (zprod aF) t := by
  rw [hornerQ_zprod]
  induction A generalizing aF with
  | nil =>
    cases aF with
    | nil => rfl
    | cons _ _ => simp at h
  | cons f A ih =>
    cases aF with
    | nil => simp at h
    | cons g aF =>
      rw [List.map_cons, List.map_cons] at h
      obtain ⟨h1, h3⟩ := List.cons.inj h
      simp only [qfac, zfac, Prod.mk.injEq] at h1
      obtain ⟨h1, h2⟩ := h1
      simp only [List.foldr_cons, ih aF h3]
      rw [← h1, ← h2]
      ring

theorem af_foldr_shift_eq (B : List (ℚ × ℚ × ℚ)) (bF : List (ℤ × ℤ)) (n t : ℚ)
    (h : B.map (qfacs n) = bF.map zfac) :
    B.foldr (fun f acc => (f.1 * (t - 1) + f.2.2 + f.2.1 * n) * acc) 1 = hornerQ (zprod bF) t := by
  rw [hornerQ_zprod]
  induction B generalizing bF with
  | nil =>
    cases bF with
    | nil => rfl
    | cons _ _ => simp at h
  | cons f B ih =>
    cases bF with
    | nil => simp at h
    | cons g bF =>
      rw [List.map_cons, List.map_cons] at h
      obtain ⟨h1, h3⟩ := List.cons.inj h
      simp only [qfacs, zfac, Prod.mk.injEq] at h1
      obtain ⟨h1, h2⟩ := h1
      simp only [List.foldr_cons, ih bF h3]
      rw [← h1, ← h2]
      ring

theorem pol2_foldr_eq (X : List (List ℚ)) (xL : ZP) (n s : ℚ) (L : ℤ)
    (h : X.map (qeval n) = xL.map (zdiv L)) :
    X.foldr (fun l acc => l.foldr (fun c acc => c + n * acc) 0 + s * acc) 0
      = hornerQ xL s / L := by
  induction X generalizing xL with
  | nil =>
    cases xL with
    | nil => simp
    | cons _ _ => simp at h
  | cons l X ih =>
    cases xL with
    | nil => simp at h
    | cons c xL =>
      rw [List.map_cons, List.map_cons] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      simp only [qeval, zdiv] at h1
      simp only [List.foldr_cons, ih xL h2, hornerQ_cons, h1]
      ring

/-! ## The bridge -/

/-- **A kernel-checked point identity gives the h0 module's statement.**  The conclusion is,
verbatim, what `simp only [F_def, eval_sub, eval_mul, eval_add, afProd_eval, polB2_eval,
polB_eval]` makes of `(F t).eval n` in a `J = 3` base module; the hypotheses are the ℚ↔ℤ
data facts and the kernel verdict. -/
theorem h0_of_kernel
    {A B Cc P0 P1 P2 P3 : List (ℚ × ℚ × ℚ)} {X : List (List ℚ)} {a0 a1 a2 a3 : List ℚ} {n t : ℚ}
    {aF bF cF p0 p1 p2 p3 : List (ℤ × ℤ)} {xL : ZP} {m0 m1 m2 m3 L M : ℤ}
    (hL : (L : ℚ) ≠ 0) (hM : (M : ℚ) ≠ 0)
    (hA : A.map (qfac n) = aF.map zfac)
    (hB : B.map (qfacs n) = bF.map zfac)
    (hC : Cc.map (qfac n) = cF.map zfac)
    (hP0 : P0.map (qfac n) = p0.map zfac)
    (hP1 : P1.map (qfac n) = p1.map zfac)
    (hP2 : P2.map (qfac n) = p2.map zfac)
    (hP3 : P3.map (qfac n) = p3.map zfac)
    (hX : X.map (qeval n) = xL.map (zdiv L))
    (h0 : qeval n a0 = zdiv M m0)
    (h1 : qeval n a1 = zdiv M m1)
    (h2 : qeval n a2 = zdiv M m2)
    (h3 : qeval n a3 = zdiv M m3)
    (hker : ztrim (zsub
        (zscale M (zsub (zmul (zprod aF) (zshift1 xL)) (zmul (zprod bF) xL)))
        (zscale L (zmul (zprod cF)
          (zadd (zadd (zscale m0 (zprod p0)) (zscale m1 (zprod p1)))
                (zadd (zscale m2 (zprod p2)) (zscale m3 (zprod p3))))))) = []) :
    A.foldr (fun f acc => (f.1 * t + f.2.2 + f.2.1 * n) * acc) 1
        * X.foldr (fun l acc => l.foldr (fun c acc => c + n * acc) 0 + (t + 1) * acc) 0
      - B.foldr (fun f acc => (f.1 * (t - 1) + f.2.2 + f.2.1 * n) * acc) 1
        * X.foldr (fun l acc => l.foldr (fun c acc => c + n * acc) 0 + t * acc) 0
      - Cc.foldr (fun f acc => (f.1 * t + f.2.2 + f.2.1 * n) * acc) 1
        * (a0.foldr (fun c acc => c + n * acc) 0
              * P0.foldr (fun f acc => (f.1 * t + f.2.2 + f.2.1 * n) * acc) 1
          + a1.foldr (fun c acc => c + n * acc) 0
              * P1.foldr (fun f acc => (f.1 * t + f.2.2 + f.2.1 * n) * acc) 1
          + a2.foldr (fun c acc => c + n * acc) 0
              * P2.foldr (fun f acc => (f.1 * t + f.2.2 + f.2.1 * n) * acc) 1
          + a3.foldr (fun c acc => c + n * acc) 0
              * P3.foldr (fun f acc => (f.1 * t + f.2.2 + f.2.1 * n) * acc) 1) = 0 := by
  have hk := hornerQ_eq_of_ztrim_zsub _ _ t hker
  simp only [hornerQ_zscale, hornerQ_zadd, hornerQ_zsub, hornerQ_zmul, hornerQ_zshift1] at hk
  simp only [qeval, zdiv] at h0 h1 h2 h3
  rw [af_foldr_eq A aF n t hA, af_foldr_shift_eq B bF n t hB, af_foldr_eq Cc cF n t hC,
    af_foldr_eq P0 p0 n t hP0, af_foldr_eq P1 p1 n t hP1, af_foldr_eq P2 p2 n t hP2,
    af_foldr_eq P3 p3 n t hP3, pol2_foldr_eq X xL n (t + 1) L hX, pol2_foldr_eq X xL n t L hX,
    h0, h1, h2, h3]
  -- goal: a·(x₁/L) − b·(x₀/L) − c·(m₀/M·q₀ + …) = 0;  hk: M·(a·x₁ − b·x₀) = L·(c·(m₀q₀ + …))
  exact bridge_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hM hk

end StarKernel

#print axioms StarKernel.hornerQ_eq_of_ztrim_zsub
#print axioms StarKernel.h0_of_kernel
#print axioms StarKernel.qeval_map_zdivq
#print axioms StarKernel.qeval_map_of_kernel
