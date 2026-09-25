/-
# Anton's congruence — `C(a,b) / p^κ` mod `p` through the DIGIT FACTORIALS

Anton (1869), in Granville's form: for `p` prime, `b ≤ a`, `c := a − b` and `κ := v_p C(a,b)`
(Kummer: the number of carries when adding `b + c` in base `p`),

    C(a,b) / p^κ  ≡  (−1)^κ · Π_i  aᵢ! / (bᵢ! · cᵢ!)        (mod p),

the product over the base-`p` digits of `a`, `b` and `c` SEPARATELY.  Lucas' `Π_i C(aᵢ, bᵢ)` is the
carry-free case of this and is `0` mod `p` the moment a carry occurs, which is why the chain's
`φ̃ = 2` strata — one carry, the `p` divided out — need this file and not `Lucas.lean`.

MATHLIB CENSUS AT THE PIN (v4.34.0-rc2 / mathlib 5aedf732), both directions, whole tree:
  PRESENT  `Nat.choose_modEq_choose_mod_mul_choose_div` and its three siblings
           (`Data/Nat/Choose/Lucas.lean`:38, 68, 75, 88 — Lucas, i.e. no carry);
           `ZMod.wilsons_lemma`; `padicValNat_choose` (Kummer as a filter-card, `k ≤ n` form; the
           primed one is the `n + k` form); `padicValNat_factorial_mul` / `_mul_add` (one Legendre
           level); `Nat.ordCompl_mul`, `Nat.not_dvd_ordCompl`, `Nat.factorization_def`
           (`n.factorization p = padicValNat p n`); `padicValNat.mul` and
           `padicValNat.eq_zero_of_not_dvd` (PROTECTED, inside `namespace padicValNat` — a grep for
           `theorem padicValNat.mul` reports them absent).
  ABSENT   anything named `anton` or `granville` (0 lines, case-insensitive; the two `anton` hits
           are a bibliography author and the word "spelling"); `choose_div_prime_pow`;
           `choose_div_pow`; any `ordCompl`-of-a-factorial or of-a-binomial statement; any
           digit-factorial product; `Nat.Prime.lucas_theorem` under that name.

ROUTE.  The real lemma is per FACTORIAL, `pfree_factorial_digits`:

    n! / p^{v_p n!}  ≡  (−1)^{v_p n!} · Π_{i<N} (n_i)!      (mod p),   n < p^N,

built from ONE level, `pfree_factorial_step`,

    n! / p^{v_p n!}  ≡  (−1)^{⌊n/p⌋} · (n mod p)! · (⌊n/p⌋! / p^{v_p ⌊n/p⌋!}),

proved for `n = p·q + r` by induction on `q` with an inner induction on `r < p`: the inner step is
`(pq + r + 1) ≡ r + 1`, the outer step is Wilson.  It is iterated over the digits with the
one-level Legendre `v_p n! = ⌊n/p⌋ + v_p ⌊n/p⌋!`, so the sign closes to `(−1)^{v_p n!}` with no
digit-sum bookkeeping.  The binomial statement is then a quotient of three of these under
`a! = C(a,b) · b! · c!` and `v_p a! = κ + v_p b! + v_p c!` — no Kummer, no carry positions, and the
sign is `(−1)^κ` for EVERY `κ`, so the one-carry case is a specialisation rather than a separate
induction.  (The sketch's "`(−1)^{⌊a/p⌋}`" per factorial is the ONE-level sign; the closed form
needs every level, which is `v_p a!`.)

The `p`-free part is spelled `n / p ^ padicValNat p n` throughout — a Nat division with the
divisibility built in — so the consumer's `C(a,b) / p` is one `pow_one` away and no cast is ever
pushed through a division (the `Int.natCast_div` trap).  Internally it is `ordCompl[p] n`, bridged
once by `div_pow_padicValNat_eq_ordCompl`.

The consumer's exact statement is `AntonOneCarry p` at the foot of the file — two digits, the
carry at the units position, the quotient as `ZMod` inverses — and the theorem that delivers it is
`choose_div_p_modEq_of_one_carry (p) [Fact p.Prime] : AntonOneCarry p`, the name the `φ̃ = 2`
strata consume.  The every-digit-count forms carry the suffix `_of_padicValNat_eq_one`.

No chain vocabulary: this file imports Mathlib only and states nothing about `cTerm`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace Zeta2Anton

open Nat Finset

section General

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## The `p`-free part `n / p^{v_p n}` -/

/-- The `p`-free part written with `padicValNat` is Mathlib's `ordCompl[p] n`. -/
theorem div_pow_padicValNat_eq_ordCompl (n : ℕ) : n / p ^ padicValNat p n = ordCompl[p] n := by
  rw [Nat.factorization_def n hp.out]

/-- Multiplicativity, with no nonzero hypotheses (`0`'s `p`-free part is `0`). -/
theorem div_pow_padicValNat_mul (a b : ℕ) :
    a * b / p ^ padicValNat p (a * b) = a / p ^ padicValNat p a * (b / p ^ padicValNat p b) := by
  rw [div_pow_padicValNat_eq_ordCompl, div_pow_padicValNat_eq_ordCompl,
    div_pow_padicValNat_eq_ordCompl, Nat.ordCompl_mul]

/-- The `p`-free part of a nonzero number is a unit mod `p`. -/
theorem cast_div_pow_padicValNat_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((n / p ^ padicValNat p n : ℕ) : ZMod p) ≠ 0 := by
  rw [div_pow_padicValNat_eq_ordCompl, Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_ordCompl hp.out hn

omit hp in
theorem div_pow_padicValNat_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : n / p ^ padicValNat p n = n := by
  rw [padicValNat.eq_zero_of_not_dvd h, pow_zero, Nat.div_one]

theorem div_pow_padicValNat_prime_mul (n : ℕ) :
    p * n / p ^ padicValNat p (p * n) = n / p ^ padicValNat p n := by
  rw [div_pow_padicValNat_mul, padicValNat_self, pow_one, Nat.div_self hp.out.pos, one_mul]

/-- `(k! : ZMod p) ≠ 0` for `k < p`. -/
theorem cast_factorial_ne_zero_of_lt {k : ℕ} (hk : k < p) : ((k ! : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial hp.out]
  omega

/-- A product of digit factorials is a unit mod `p`. -/
theorem prod_digit_factorial_ne_zero (n N : ℕ) :
    (∏ i ∈ range N, ((n / p ^ i % p)! : ZMod p)) ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ _ => cast_factorial_ne_zero_of_lt (Nat.mod_lt _ hp.out.pos)

/-! ## One Legendre level, one digit -/

/-- The inner induction: along `r < p` inside one block of `p`.  Each step multiplies by
`p·q + r + 1 ≡ r + 1`, which is `p`-free. -/
theorem pfree_factorial_block (q : ℕ)
    (h0 : (((p * q)! / p ^ padicValNat p (p * q)! : ℕ) : ZMod p)
        = (-1) ^ q * ((q ! / p ^ padicValNat p q ! : ℕ) : ZMod p)) :
    ∀ r, r < p →
      (((p * q + r)! / p ^ padicValNat p (p * q + r)! : ℕ) : ZMod p)
        = (-1) ^ q * ((r ! : ℕ) : ZMod p) * ((q ! / p ^ padicValNat p q ! : ℕ) : ZMod p) := by
  intro r
  induction r with
  | zero =>
    intro _
    simpa using h0
  | succ r ih =>
    intro hr
    have hr' : r < p := by omega
    have hnd : ¬ p ∣ p * q + r + 1 := by
      rw [add_assoc, Nat.dvd_add_right (dvd_mul_right p q)]
      intro h
      exact absurd (Nat.le_of_dvd (Nat.succ_pos r) h) (by omega)
    rw [show p * q + (r + 1) = (p * q + r) + 1 by ring, Nat.factorial_succ (p * q + r),
      div_pow_padicValNat_mul, div_pow_padicValNat_of_not_dvd hnd, Nat.cast_mul, ih hr',
      Nat.factorial_succ r]
    push_cast
    rw [ZMod.natCast_self]
    ring

/-- The outer induction: across the blocks.  Passing from block `q` to block `q + 1` multiplies by
`p·(q+1)`, whose `p`-free part is that of `q + 1`, and by the full block `(p−1)! ≡ −1` (Wilson). -/
theorem pfree_factorial_qr (q : ℕ) : ∀ r, r < p →
    (((p * q + r)! / p ^ padicValNat p (p * q + r)! : ℕ) : ZMod p)
      = (-1) ^ q * ((r ! : ℕ) : ZMod p) * ((q ! / p ^ padicValNat p q ! : ℕ) : ZMod p) := by
  induction q with
  | zero =>
    apply pfree_factorial_block
    simp
  | succ q ih =>
    apply pfree_factorial_block
    have h1 := ih (p - 1) (Nat.sub_lt hp.out.pos one_pos)
    have hpq : p * (q + 1) = (p * q + (p - 1)) + 1 := by
      have := hp.out.pos
      rw [Nat.mul_succ]
      omega
    have hfac : (p * (q + 1))! = (p * (q + 1)) * (p * q + (p - 1))! := by
      rw [hpq]
      exact Nat.factorial_succ _
    rw [hfac, div_pow_padicValNat_mul, div_pow_padicValNat_prime_mul, Nat.cast_mul, h1,
      ZMod.wilsons_lemma, Nat.factorial_succ q, div_pow_padicValNat_mul, Nat.cast_mul]
    ring

/-- **One level of the digit expansion.**
`n! / p^{v_p n!} ≡ (−1)^{⌊n/p⌋} · (n mod p)! · ⌊n/p⌋! / p^{v_p ⌊n/p⌋!}  (mod p)`. -/
theorem pfree_factorial_step (n : ℕ) :
    ((n ! / p ^ padicValNat p n ! : ℕ) : ZMod p)
      = (-1) ^ (n / p) * (((n % p)! : ℕ) : ZMod p)
        * (((n / p)! / p ^ padicValNat p (n / p)! : ℕ) : ZMod p) := by
  have h := pfree_factorial_qr (n / p) (n % p) (Nat.mod_lt n hp.out.pos)
  rwa [Nat.div_add_mod n p] at h

/-- One Legendre level: `v_p n! = ⌊n/p⌋ + v_p ⌊n/p⌋!`. -/
theorem padicValNat_factorial_step (n : ℕ) :
    padicValNat p n ! = n / p + padicValNat p (n / p)! := by
  conv_lhs => rw [← Nat.div_add_mod n p]
  rw [padicValNat_factorial_mul_add (n / p) (Nat.mod_lt n hp.out.pos), padicValNat_factorial_mul,
    add_comm]

/-! ## The per-factorial lemma -/

/-- **The `p`-free part of a factorial, mod `p`, through its digits** (Anton–Granville's
factorial form).  For `n < p^N`,
`n! / p^{v_p n!} ≡ (−1)^{v_p n!} · Π_{i<N} (n_i)!  (mod p)`, `n_i := ⌊n/p^i⌋ mod p`. -/
theorem pfree_factorial_digits (N : ℕ) : ∀ n, n < p ^ N →
    ((n ! / p ^ padicValNat p n ! : ℕ) : ZMod p)
      = (-1) ^ padicValNat p n ! * ∏ i ∈ range N, (((n / p ^ i % p)! : ℕ) : ZMod p) := by
  induction N with
  | zero =>
    intro n hn
    rw [pow_zero] at hn
    obtain rfl : n = 0 := by omega
    simp
  | succ N ih =>
    intro n hn
    have hq : n / p < p ^ N := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]
      exact hn
    rw [pfree_factorial_step, ih (n / p) hq, prod_range_succ', padicValNat_factorial_step n,
      pow_add]
    have hd : ∀ i, n / p / p ^ i = n / p ^ (i + 1) := fun i => by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
    simp only [hd, pow_zero, Nat.div_one]
    ring

/-! ## Anton's congruence for the binomial, every `κ` -/

/-- **Anton–Granville, multiplicative form, every `κ`.**  With `κ := v_p C(a,b)` and `a < p^N`,
`(C(a,b) / p^κ) · Π bᵢ! · Π cᵢ! ≡ (−1)^κ · Π aᵢ!  (mod p)`, `c := a − b`. -/
theorem choose_div_pow_mul_eq {a b : ℕ} (hb : b ≤ a) {N : ℕ} (haN : a < p ^ N) :
    ((a.choose b / p ^ padicValNat p (a.choose b) : ℕ) : ZMod p)
        * (∏ i ∈ range N, (((b / p ^ i % p)! : ℕ) : ZMod p))
        * (∏ i ∈ range N, ((((a - b) / p ^ i % p)! : ℕ) : ZMod p))
      = (-1) ^ padicValNat p (a.choose b) * ∏ i ∈ range N, (((a / p ^ i % p)! : ℕ) : ZMod p) := by
  have hfact : a.choose b * b ! * (a - b)! = a ! := Nat.choose_mul_factorial_mul_factorial hb
  have hC : a.choose b ≠ 0 := (Nat.choose_pos hb).ne'
  have hv : padicValNat p a ! =
      padicValNat p (a.choose b) + padicValNat p b ! + padicValNat p (a - b)! := by
    rw [← hfact, padicValNat.mul (mul_ne_zero hC (factorial_ne_zero b)) (factorial_ne_zero _),
      padicValNat.mul hC (factorial_ne_zero b)]
  have hsplit : ((a ! / p ^ padicValNat p a ! : ℕ) : ZMod p)
      = ((a.choose b / p ^ padicValNat p (a.choose b) : ℕ) : ZMod p)
        * ((b ! / p ^ padicValNat p b ! : ℕ) : ZMod p)
        * (((a - b)! / p ^ padicValNat p (a - b)! : ℕ) : ZMod p) := by
    rw [← hfact, div_pow_padicValNat_mul, div_pow_padicValNat_mul, Nat.cast_mul, Nat.cast_mul]
  rw [pfree_factorial_digits N a haN, pfree_factorial_digits N b (lt_of_le_of_lt hb haN),
    pfree_factorial_digits N (a - b) (lt_of_le_of_lt (Nat.sub_le a b) haN), hv, pow_add, pow_add]
    at hsplit
  have hs : ((-1 : ZMod p) ^ padicValNat p b ! * (-1) ^ padicValNat p (a - b)!) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  apply mul_left_cancel₀ hs
  linear_combination hsplit.symm

/-- **Anton–Granville, quotient form, every `κ`.**
`C(a,b) / p^κ ≡ (−1)^κ · Π aᵢ! / (Π bᵢ! · Π cᵢ!)  (mod p)`. -/
theorem choose_div_pow_eq {a b : ℕ} (hb : b ≤ a) {N : ℕ} (haN : a < p ^ N) :
    ((a.choose b / p ^ padicValNat p (a.choose b) : ℕ) : ZMod p)
      = (-1) ^ padicValNat p (a.choose b)
        * (∏ i ∈ range N, (((a / p ^ i % p)! : ℕ) : ZMod p))
        / ((∏ i ∈ range N, (((b / p ^ i % p)! : ℕ) : ZMod p))
            * ∏ i ∈ range N, ((((a - b) / p ^ i % p)! : ℕ) : ZMod p)) := by
  rw [eq_div_iff (mul_ne_zero (prod_digit_factorial_ne_zero b N)
    (prod_digit_factorial_ne_zero (a - b) N))]
  linear_combination choose_div_pow_mul_eq hb haN

/-! ## The one-carry case, every digit count -/

/-- **Anton's congruence, one carry (`κ = 1`), multiplicative form.**
`(C(a,b) / p) · Π bᵢ! · Π cᵢ! ≡ −Π aᵢ!  (mod p)`. -/
theorem choose_div_p_mul_eq_of_padicValNat_eq_one {a b : ℕ} (hb : b ≤ a) {N : ℕ} (haN : a < p ^ N)
    (hκ : padicValNat p (a.choose b) = 1) :
    ((a.choose b / p : ℕ) : ZMod p)
        * (∏ i ∈ range N, (((b / p ^ i % p)! : ℕ) : ZMod p))
        * (∏ i ∈ range N, ((((a - b) / p ^ i % p)! : ℕ) : ZMod p))
      = -∏ i ∈ range N, (((a / p ^ i % p)! : ℕ) : ZMod p) := by
  have h := choose_div_pow_mul_eq hb haN
  rw [hκ] at h
  simp only [pow_one] at h
  rw [h]
  ring

/-- **Anton's congruence, one carry (`κ = 1`), quotient form**, any number of digits:
`C(a,b) / p ≡ −Π aᵢ! / (Π bᵢ! · Π cᵢ!)  (mod p)`, `c := a − b`, `a < p^N`.  The two-digit
consumer shape `AntonOneCarry` below is this at `N = 2`. -/
theorem choose_div_p_modEq_of_padicValNat_eq_one {a b : ℕ} (hb : b ≤ a) {N : ℕ} (haN : a < p ^ N)
    (hκ : padicValNat p (a.choose b) = 1) :
    ((a.choose b / p : ℕ) : ZMod p)
      = -((∏ i ∈ range N, (((a / p ^ i % p)! : ℕ) : ZMod p))
          / ((∏ i ∈ range N, (((b / p ^ i % p)! : ℕ) : ZMod p))
              * ∏ i ∈ range N, ((((a - b) / p ^ i % p)! : ℕ) : ZMod p))) := by
  have h := choose_div_pow_eq hb haN
  rw [hκ] at h
  simp only [pow_one] at h
  rw [h]
  ring

/-! ## Two digits: `a < p²`, where the carry is Kummer's units-digit test -/

/-- Kummer below `p²`: `v_p C(a,b) = [p ≤ b mod p + (a−b) mod p]`. -/
theorem padicValNat_choose_two_digits {a b : ℕ} (hb : b ≤ a) (ha : a < p ^ 2) :
    padicValNat p (a.choose b) = if p ≤ b % p + (a - b) % p then 1 else 0 := by
  have hlog : Nat.log p a < 2 := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, Nat.log_zero_right]
      norm_num
    · exact Nat.log_lt_of_lt_pow h0.ne' ha
  rw [padicValNat_choose hb hlog, show Finset.Ico 1 2 = {1} from Nat.Ico_succ_singleton 1,
    Finset.filter_singleton]
  simp only [pow_one]
  split_ifs <;> simp

theorem div_mod_self_of_lt_sq {n : ℕ} (hn : n < p ^ 2) : n / p % p = n / p :=
  Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul hp.out.pos, ← sq]; exact hn)

/-- **Anton's congruence with two digits.**  For `a < p²`, `b ≤ a` and the units-digit carry
`p ≤ b mod p + (a−b) mod p`:
`C(a,b) / p ≡ −(a₀! a₁!) / (b₀! b₁! · c₀! c₁!)  (mod p)` with `x₀ = x mod p`, `x₁ = ⌊x/p⌋`. -/
theorem choose_div_p_modEq_two_digits {a b : ℕ} (hb : b ≤ a) (ha : a < p ^ 2)
    (hcarry : p ≤ b % p + (a - b) % p) :
    ((a.choose b / p : ℕ) : ZMod p)
      = -((((a % p)! : ℕ) : ZMod p) * (((a / p)! : ℕ) : ZMod p)
          / (((((b % p)! : ℕ) : ZMod p) * (((b / p)! : ℕ) : ZMod p))
              * (((((a - b) % p)! : ℕ) : ZMod p) * ((((a - b) / p)! : ℕ) : ZMod p)))) := by
  have hκ : padicValNat p (a.choose b) = 1 := by
    rw [padicValNat_choose_two_digits hb ha]
    simp [hcarry]
  have h := choose_div_p_modEq_of_padicValNat_eq_one hb ha hκ
  simp only [prod_range_succ, prod_range_zero, pow_zero, pow_one, Nat.div_one, one_mul,
    div_mod_self_of_lt_sq ha, div_mod_self_of_lt_sq (lt_of_le_of_lt hb ha),
    div_mod_self_of_lt_sq (lt_of_le_of_lt (Nat.sub_le a b) ha)] at h
  exact h

end General

/-! ## The consumer's shape — two digits, the carry at the units position, `ZMod` inverses

`AntonOneCarry p` is stated VERBATIM as the `φ̃ = 2` strata consume it (`Zeta2PtpS2a`, relayed
2026-09-23): `S = S₀ + p·S₁`, `A = A₀ + p·A₁`, digits below `p`; `S₀ < A₀` is the units carry and
`A₁ < S₁` says the tens does not, so the digits of `S − A` are `S₀ + p − A₀` and `S₁ − 1 − A₁`,
`v_p C(S,A) = 1` (Kummer) and the division is exact.  The inverses are of factorials of digits
below `p`, hence of units in `ZMod p`, which is what makes the right-hand side well defined.  The
consumer defines the same `Prop` under its own name and discharges it with the theorem below; it
imports this file, never the reverse. -/

def AntonOneCarry (p : ℕ) : Prop :=
  ∀ S₀ S₁ A₀ A₁ : ℕ, S₀ < A₀ → A₀ < p → S₁ < p → A₁ < S₁ →
    ((((S₀ + p * S₁).choose (A₀ + p * A₁)) / p : ℕ) : ZMod p)
      = -(((S₀ ! : ℕ) : ZMod p) * ((((S₀ + p - A₀)! : ℕ) : ZMod p))⁻¹ * (((A₀ ! : ℕ) : ZMod p))⁻¹)
        * (((S₁ ! : ℕ) : ZMod p) * (((A₁ ! : ℕ) : ZMod p))⁻¹ * ((((S₁ - 1 - A₁)! : ℕ) : ZMod p))⁻¹)

/-- **Anton's congruence, one carry, in the consumer's shape** — `choose_div_p_modEq_two_digits`
with the digits read off `S₀ + p·S₁` and `A₀ + p·A₁` and the quotient split into inverses. -/
theorem choose_div_p_modEq_of_one_carry (p : ℕ) [hp : Fact p.Prime] : AntonOneCarry p := by
  intro S₀ S₁ A₀ A₁ h0 hA0 hS1 hA1
  have hp0 := hp.out.pos
  have dS0 : (S₀ + p * S₁) % p = S₀ := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have dS1 : (S₀ + p * S₁) / p = S₁ := by
    rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt (by omega), zero_add]
  have dA0 : (A₀ + p * A₁) % p = A₀ := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA0]
  have dA1 : (A₀ + p * A₁) / p = A₁ := by
    rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hA0, zero_add]
  have hsub : S₀ + p * S₁ - (A₀ + p * A₁) = (S₀ + p - A₀) + p * (S₁ - 1 - A₁) := by
    obtain ⟨T, rfl⟩ : ∃ T, S₁ = T + A₁ + 1 := ⟨S₁ - 1 - A₁, by omega⟩
    rw [show T + A₁ + 1 - 1 - A₁ = T by omega, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  have dC0 : (S₀ + p * S₁ - (A₀ + p * A₁)) % p = S₀ + p - A₀ := by
    rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have dC1 : (S₀ + p * S₁ - (A₀ + p * A₁)) / p = S₁ - 1 - A₁ := by
    rw [hsub, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt (by omega), zero_add]
  have hb : A₀ + p * A₁ ≤ S₀ + p * S₁ := by
    have h : p * (A₁ + 1) ≤ p * S₁ := Nat.mul_le_mul_left p hA1
    rw [Nat.mul_add, Nat.mul_one] at h
    omega
  have ha : S₀ + p * S₁ < p ^ 2 := by
    have h : p * (S₁ + 1) ≤ p * p := Nat.mul_le_mul_left p hS1
    rw [Nat.mul_add, Nat.mul_one] at h
    rw [sq]
    omega
  have hcarry : p ≤ (A₀ + p * A₁) % p + (S₀ + p * S₁ - (A₀ + p * A₁)) % p := by
    rw [dA0, dC0]
    omega
  have h := choose_div_p_modEq_two_digits hb ha hcarry
  rw [dS0, dS1, dA0, dA1, dC0, dC1] at h
  rw [h]
  ring

end Zeta2Anton

#print axioms Zeta2Anton.pfree_factorial_step
#print axioms Zeta2Anton.pfree_factorial_digits
#print axioms Zeta2Anton.choose_div_pow_mul_eq
#print axioms Zeta2Anton.choose_div_pow_eq
#print axioms Zeta2Anton.choose_div_p_mul_eq_of_padicValNat_eq_one
#print axioms Zeta2Anton.choose_div_p_modEq_of_padicValNat_eq_one
#print axioms Zeta2Anton.padicValNat_choose_two_digits
#print axioms Zeta2Anton.choose_div_p_modEq_two_digits
#print axioms Zeta2Anton.choose_div_p_modEq_of_one_carry
#check @Zeta2Anton.pfree_factorial_digits
#check @Zeta2Anton.choose_div_pow_eq
#check @Zeta2Anton.choose_div_p_modEq_of_padicValNat_eq_one
#check @Zeta2Anton.choose_div_p_mul_eq_of_padicValNat_eq_one
#check @Zeta2Anton.choose_div_p_modEq_two_digits
#check @Zeta2Anton.AntonOneCarry
#check @Zeta2Anton.choose_div_p_modEq_of_one_carry
#print Zeta2Anton.AntonOneCarry
