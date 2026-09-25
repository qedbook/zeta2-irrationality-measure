/-
# Row PAIR-4R — the four open residue obligations, and the UNCONDITIONAL `hat_rep`

`docs/future/zeta2-lean-chain.md` row PAIR-4R, §PAIR-4R attempt 2/3.

`Zeta2HatPoles.hat_rep_of_residues` is the row's statement for every `n` from THREE named
residue hypotheses; across the four-row pole table those decompose into SIX local obligations,
of which two — `hat_res_cancelled` and `hat_res_lo_double`, the ones the numerator's own
`(2t+l)` zeros make free — are landed there.  This file discharges the other four and closes
the row:

| run              | order | obligation                  | here                       |
|------------------|-------|-----------------------------|----------------------------|
| `[7n+1, 9n]`     | 1     | `h₁`, residue `0`           | `Zeta2HatPoles` (landed)   |
| `[18n+2, 20n+1]` | 1     | `h₁` = `hatBhi`             | `hat_res_hi`               |
| `[9n+1, 10n]`    | 2     | `h₂`, coefficient `0`       | `Zeta2HatPoles` (landed)   |
| `[9n+1, 10n]`    | 2     | `h₃` = `hatBlo`             | `hat_res_lo_deriv`         |
| `[10n+1, 18n+1]` | 2     | `h₂` = `hatA`               | `hat_res_double`           |
| `[10n+1, 18n+1]` | 2     | `h₃` = `hatLam`             | `hat_res_double_deriv`     |

**Every one of them is a factorial identity and nothing structural** — that was the second
pass's finding and it survived contact.  The shape is the same four times: the numerator's
value (or its derivative) at `t = −κ` collapses to a ratio of factorials through
`Zeta2PE.prod_Icc_sub_below` / `prod_Icc_sub_above`, the cofactor `polePf1`/`polePf2` collapses
the same way over the pole table's runs, and the two meet after clearing.

**Where the signs go, and why the statements are shaped around them.**  Each run contributes
`(−1)^(len)`, and the four exponents cancel in pairs — `(−1)^(17n)·(−1)^(5n)` on the numerator,
`(−1)^(2n)` on the cancelled run, `((−1)^(9n+1))²` on a squared cofactor.  `ring` does NOT know
`(−1)^m·(−1)^m = 1`, so a proof that leaves one standing cannot be closed by `field_simp; ring`
however true it is: every lemma below therefore pairs its signs explicitly (`Even.neg_one_pow`)
before any field reasoning, and `polePf1_hi` carries `hatBhi`'s own `(−1)^i` on its LEFT-hand
side so that the two annihilate inside one statement rather than across two.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2HatPoles

namespace Zeta2HatResidues

open Zeta2Defs Zeta2Hat Zeta2HatRep Zeta2HatPoles Polynomial Finset Nat

set_option profiler true
set_option profiler.threshold 100

/-! ## The one helper this file adds

The other side condition every clearing step needs — a factorial cast is never `0` — lives with
the atoms, as `Zeta2PE.cast_factorial_ne_zero`; `cast_fac_ne` is a local abbreviation for it
because it appears a dozen times below. -/

/-- Local short name for `Zeta2PE.cast_factorial_ne_zero`. -/
theorem cast_fac_ne (m : ℕ) : (((m)! : ℕ) : ℚ) ≠ 0 := Zeta2PE.cast_factorial_ne_zero m

/-- A binomial as a quotient of factorial casts, with the COMPLEMENTARY index named rather than
left as `m − k`.  `Nat.choose_mul_factorial_mul_factorial` is the cleared ℕ statement; naming
the complement is what lets `ring` see `(11n)!` and `(8n−j)!` as the same atoms the pole table
produces. -/
theorem choose_cast_div (m k c : ℕ) (hk : k ≤ m) (hc : m - k = c) :
    ((m.choose k : ℕ) : ℚ) = (((m)! : ℕ) : ℚ) / ((((k)! : ℕ) : ℚ) * (((c)! : ℕ) : ℚ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  rw [hc] at h
  rw [eq_div_iff (mul_ne_zero (cast_fac_ne k) (cast_fac_ne c)), ← mul_assoc,
    ← Nat.cast_mul, ← Nat.cast_mul, h]

/-! ## The numerator at a pole, and its derivative there

`hatNum` is a product of linear forms in `t`, so its value at `t = −κ` is a product of two runs
of consecutive integers reflected about `2κ` and `κ`.  Three lemmas serve the four obligations:
the plain value when `2κ` lies ABOVE the `(2t+l)` index range (rows 2 and 3 of the table), the
derivative at a SIMPLE ZERO (row `[9n+1,10n]`, where `2κ` is inside that range), and the
log-derivative form (row `[10n+1,18n+1]`). -/

theorem hatNum_eval_neg (n κ : ℕ) :
    (hatNum n).eval (-((κ : ℕ) : ℚ))
      = (∏ l ∈ Icc (3 * n + 2) (20 * n + 1), (((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ)))
        * ∏ l ∈ Icc 1 (5 * n), (((l : ℕ) : ℚ) - ((κ : ℕ) : ℚ)) := by
  rw [hatNum_eval]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact Finset.prod_congr rfl fun l _ => by push_cast; ring
  · exact Finset.prod_congr rfl fun l _ => by push_cast; ring

/-- `Û(−κ)` when `2κ` lies ABOVE the `(2t+l)` index range: no factor vanishes, and the two runs'
signs — `(−1)^(17n)` on the doubled run and `(−1)^(5n)` on the plain one — cancel, because
`17n + 5n = 22n` is even at every `n`.  Cleared, so no nonvanishing side condition travels. -/
theorem hatNum_eval_neg_above (n κ : ℕ) (h2 : 20 * n + 1 < 2 * κ) (h5 : 5 * n < κ) :
    (hatNum n).eval (-((κ : ℕ) : ℚ))
        * ((((2 * κ - 20 * n - 2)! : ℕ) : ℚ) * (((κ - 5 * n - 1)! : ℕ) : ℚ))
      = (((2 * κ - 3 * n - 2)! : ℕ) : ℚ) * (((κ - 1)! : ℕ) : ℚ) := by
  have e1 := Zeta2PE.prod_Icc_sub_below (2 * κ) (3 * n + 2) (20 * n + 1) (by omega) (by omega)
  have e2 := Zeta2PE.prod_Icc_sub_below κ 1 (5 * n) (by omega) (by omega)
  rw [show 2 * κ - (20 * n + 1) - 1 = 2 * κ - 20 * n - 2 from by omega,
    show 20 * n + 1 + 1 - (3 * n + 2) = 17 * n from by omega,
    show 2 * κ - (3 * n + 2) = 2 * κ - 3 * n - 2 from by omega] at e1
  rw [show 5 * n + 1 - 1 = 5 * n from by omega] at e2
  have hsign : ((-1 : ℚ)) ^ (17 * n) * ((-1 : ℚ)) ^ (5 * n) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨11 * n, by omega⟩
  rw [hatNum_eval_neg]
  set p := ∏ l ∈ Icc (3 * n + 2) (20 * n + 1), (((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ)) with hp
  set q := ∏ l ∈ Icc 1 (5 * n), (((l : ℕ) : ℚ) - ((κ : ℕ) : ℚ)) with hq
  calc p * q * ((((2 * κ - 20 * n - 2)! : ℕ) : ℚ) * (((κ - 5 * n - 1)! : ℕ) : ℚ))
      = (p * (((2 * κ - 20 * n - 2)! : ℕ) : ℚ)) * (q * (((κ - 5 * n - 1)! : ℕ) : ℚ)) := by ring
    _ = (((-1 : ℚ)) ^ (17 * n) * (((2 * κ - 3 * n - 2)! : ℕ) : ℚ))
          * (((-1 : ℚ)) ^ (5 * n) * (((κ - 1)! : ℕ) : ℚ)) := by rw [e1, e2]
    _ = (((-1 : ℚ)) ^ (17 * n) * ((-1 : ℚ)) ^ (5 * n))
          * ((((2 * κ - 3 * n - 2)! : ℕ) : ℚ) * (((κ - 1)! : ℕ) : ℚ)) := by ring
    _ = (((2 * κ - 3 * n - 2)! : ℕ) : ℚ) * (((κ - 1)! : ℕ) : ℚ) := by rw [hsign, one_mul]

/-- The derivative at a SIMPLE ZERO of the numerator.  `Zeta2PE.eval_derivative_prod_linear`
does not serve here — it needs every factor nonvanishing — so the vanishing factor is pulled out
by `Finset.mul_prod_erase` and the product rule leaves exactly its slope, `2`. -/
theorem hatNum_derivative_eval_neg_zero (n κ : ℕ)
    (hm : 2 * κ ∈ Icc (3 * n + 2) (20 * n + 1)) :
    (derivative (hatNum n)).eval (-((κ : ℕ) : ℚ))
      = 2 * ((∏ l ∈ (Icc (3 * n + 2) (20 * n + 1)).erase (2 * κ),
              (((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ)))
          * ∏ l ∈ Icc 1 (5 * n), (((l : ℕ) : ℚ) - ((κ : ℕ) : ℚ))) := by
  classical
  have hsplit : hatNum n = (C (2 : ℚ) * X + C ((2 * κ : ℕ) : ℚ))
      * ((∏ l ∈ (Icc (3 * n + 2) (20 * n + 1)).erase (2 * κ),
            (C (2 : ℚ) * X + C ((l : ℕ) : ℚ)))
        * ∏ l ∈ Icc 1 (5 * n), (X + C ((l : ℕ) : ℚ))) := by
    rw [hatNum, ← Finset.mul_prod_erase _ _ hm, mul_assoc]
  rw [hsplit, derivative_mul]
  simp only [derivative_add, derivative_C_mul, derivative_X, derivative_C, add_zero, mul_one,
    eval_add, eval_mul, eval_C, eval_X, eval_prod]
  rw [show (2 : ℚ) * -((κ : ℕ) : ℚ) + ((2 * κ : ℕ) : ℚ) = 0 from by push_cast; ring]
  rw [Finset.prod_congr rfl (fun l _ => by push_cast; ring :
    ∀ l ∈ (Icc (3 * n + 2) (20 * n + 1)).erase (2 * κ),
      (2 : ℚ) * -((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ) = ((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ))]
  rw [Finset.prod_congr rfl (fun l _ => by push_cast; ring :
    ∀ l ∈ Icc 1 (5 * n),
      -((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ) = ((l : ℕ) : ℚ) - ((κ : ℕ) : ℚ))]
  ring

/-- The LOG-DERIVATIVE form, for a pole where the numerator does NOT vanish: `Û′(−κ) = Û(−κ)·L`
with `L` a sum of reciprocals, the `(2t+l)` factors contributing `2/(l−2κ)` and the `(t+l)`
factors `1/(l−κ)`.  Both come out of the ONE atom `Zeta2PE.eval_derivative_prod_linear`, which is
exactly why it was stated with a per-factor slope `c i`. -/
theorem hatNum_derivative_eval_neg_above (n κ : ℕ) (h2 : 20 * n + 1 < 2 * κ) (h5 : 5 * n < κ) :
    (derivative (hatNum n)).eval (-((κ : ℕ) : ℚ))
      = (hatNum n).eval (-((κ : ℕ) : ℚ))
        * (2 * (∑ l ∈ Icc (3 * n + 2) (20 * n + 1),
                (1 : ℚ) / (((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ)))
          + ∑ l ∈ Icc 1 (5 * n), (1 : ℚ) / (((l : ℕ) : ℚ) - ((κ : ℕ) : ℚ))) := by
  classical
  have hneP : ∀ l ∈ Icc (3 * n + 2) (20 * n + 1),
      (2 : ℚ) * -((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ) ≠ 0 := by
    intro l hl
    simp only [Finset.mem_Icc] at hl
    have : ((l : ℕ) : ℚ) < ((2 * κ : ℕ) : ℚ) := by exact_mod_cast (by omega : l < 2 * κ)
    push_cast at this ⊢
    intro hz
    linarith
  have hneQ : ∀ l ∈ Icc 1 (5 * n), (1 : ℚ) * -((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ) ≠ 0 := by
    intro l hl
    simp only [Finset.mem_Icc] at hl
    have : ((l : ℕ) : ℚ) < ((κ : ℕ) : ℚ) := by exact_mod_cast (by omega : l < κ)
    intro hz
    linarith
  have hQform : (∏ l ∈ Icc 1 (5 * n), (X + C ((l : ℕ) : ℚ)))
      = ∏ l ∈ Icc 1 (5 * n), (C (1 : ℚ) * X + C ((l : ℕ) : ℚ)) :=
    Finset.prod_congr rfl fun l _ => by simp
  have hPd := Zeta2PE.eval_derivative_prod_linear (Icc (3 * n + 2) (20 * n + 1))
    (fun _ => (2 : ℚ)) (fun l => ((l : ℕ) : ℚ)) (-((κ : ℕ) : ℚ)) hneP
  have hQd := Zeta2PE.eval_derivative_prod_linear (Icc 1 (5 * n))
    (fun _ => (1 : ℚ)) (fun l => ((l : ℕ) : ℚ)) (-((κ : ℕ) : ℚ)) hneQ
  rw [← hQform] at hQd
  simp only [one_mul] at hQd
  -- the RHS's `Û(−κ)` goes FIRST: `rw [hatNum]` unfolds every occurrence, and after it there is
  -- no `eval (−κ) (hatNum n)` left for `hatNum_eval_neg` to find.
  rw [hatNum_eval_neg, hatNum, derivative_mul]
  simp only [eval_add, eval_mul, eval_prod, eval_C, eval_X]
  rw [hPd, hQd]
  rw [Finset.prod_congr rfl (fun l _ => by push_cast; ring :
    ∀ l ∈ Icc (3 * n + 2) (20 * n + 1),
      (2 : ℚ) * -((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ) = ((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ))]
  rw [Finset.prod_congr rfl (fun l _ => by push_cast; ring :
    ∀ l ∈ Icc 1 (5 * n),
      -((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ) = ((l : ℕ) : ℚ) - ((κ : ℕ) : ℚ))]
  rw [Finset.sum_congr rfl (fun l _ => by
      rw [show (2 : ℚ) * -((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ)
        = ((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ) by push_cast; ring] :
    ∀ l ∈ Icc (3 * n + 2) (20 * n + 1),
      (2 : ℚ) / ((2 : ℚ) * -((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ))
        = (2 : ℚ) / (((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ)))]
  rw [Finset.sum_congr rfl (fun l _ => by
      rw [show -((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ) = ((l : ℕ) : ℚ) - ((κ : ℕ) : ℚ) by ring] :
    ∀ l ∈ Icc 1 (5 * n),
      (1 : ℚ) / (-((κ : ℕ) : ℚ) + ((l : ℕ) : ℚ))
        = (1 : ℚ) / (((l : ℕ) : ℚ) - ((κ : ℕ) : ℚ)))]
  rw [show (2 : ℚ) * ∑ l ∈ Icc (3 * n + 2) (20 * n + 1),
        (1 : ℚ) / (((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ))
      = ∑ l ∈ Icc (3 * n + 2) (20 * n + 1),
        (2 : ℚ) / (((l : ℕ) : ℚ) - ((2 * κ : ℕ) : ℚ)) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring]
  ring

/-! ## Row 2 of the pole table — `h₁` on the HI run `[18n+2, 20n+1]`, i.e. `hatBhi`

The row's NAMED next probe (LEAN.md §9), and the cheapest of the four because every run of the
cofactor lies on ONE side of the pole: no split at `κ` in the numerator, only in the erased
simple set.  The seven factorials `hatBhi` is written with are produced exactly — `κ−1 =
18n+1+i`, `κ−9n−1 = 9n+1+i`, `κ−7n−1 = 11n+1+i`, `κ−18n−2 = i`, `κ−5n−1 = 13n+1+i`,
`2κ−3n−2 = 33n+2+2i`, `2κ−20n−2 = 16n+2+2i`, `20n+1−κ = 2n−1−i` — and nothing is left over. -/

theorem idxS1_erase_hi (n i : ℕ) (hi : i < 2 * n) :
    (idxS1 n).erase (18 * n + 2 + i)
      = (Icc (7 * n + 1) (9 * n) ∪ Icc (18 * n + 2) (18 * n + 1 + i))
        ∪ Icc (18 * n + 3 + i) (20 * n + 1) := by
  ext x
  simp only [idxS1, Finset.mem_erase, Finset.mem_union, Finset.mem_Icc]
  omega

/-- The cofactor at a hi simple pole, with `hatBhi`'s own `(−1)^i` carried on the LEFT.  Pairing
the two signs inside ONE statement is what keeps the assembly closable: left apart, `ring` meets
`(−1)^i·(−1)^i` and cannot reduce it. -/
theorem polePf1_hi (n i : ℕ) (hi : i < 2 * n) :
    ((-1 : ℚ)) ^ i * (polePf1 n (18 * n + 2 + i) * ((i ! : ℕ) : ℚ))
      = (((11 * n + 1 + i)! : ℕ) : ℚ) * (((2 * n - 1 - i)! : ℕ) : ℚ)
        * (((9 * n + 1 + i)! : ℕ) : ℚ) := by
  classical
  have hd12 : Disjoint (Icc (7 * n + 1) (9 * n) ∪ Icc (18 * n + 2) (18 * n + 1 + i))
      (Icc (18 * n + 3 + i) (20 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_union, Finset.mem_Icc] at hx hy
    omega
  have hd1 : Disjoint (Icc (7 * n + 1) (9 * n)) (Icc (18 * n + 2) (18 * n + 1 + i)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have q1 := Zeta2PE.prod_Icc_sub_below (18 * n + 2 + i) (7 * n + 1) (9 * n) (by omega) (by omega)
  have q2 := Zeta2PE.prod_Icc_sub_below (18 * n + 2 + i) (18 * n + 2) (18 * n + 1 + i)
    (by omega) (by omega)
  have q3 := Zeta2PE.prod_Icc_sub_above (18 * n + 2 + i) (18 * n + 3 + i) (20 * n + 1)
    (by omega) (by omega)
  have q4 := Zeta2PE.prod_Icc_sub_below (18 * n + 2 + i) (9 * n + 1) (18 * n + 1)
    (by omega) (by omega)
  have h2n : ((-1 : ℚ)) ^ (2 * n) = 1 := Even.neg_one_pow ⟨n, by omega⟩
  rw [show 18 * n + 2 + i - 9 * n - 1 = 9 * n + 1 + i from by omega,
    show 9 * n + 1 - (7 * n + 1) = 2 * n from by omega,
    show 18 * n + 2 + i - (7 * n + 1) = 11 * n + 1 + i from by omega, h2n, one_mul] at q1
  rw [show 18 * n + 2 + i - (18 * n + 1 + i) - 1 = 0 from by omega,
    show 18 * n + 1 + i + 1 - (18 * n + 2) = i from by omega,
    show 18 * n + 2 + i - (18 * n + 2) = i from by omega,
    Nat.factorial_zero, Nat.cast_one, mul_one] at q2
  rw [show 18 * n + 3 + i - (18 * n + 2 + i) - 1 = 0 from by omega,
    show 20 * n + 1 - (18 * n + 2 + i) = 2 * n - 1 - i from by omega,
    Nat.factorial_zero, Nat.cast_one, mul_one] at q3
  rw [show 18 * n + 2 + i - (18 * n + 1) - 1 = i from by omega,
    show 18 * n + 1 + 1 - (9 * n + 1) = 9 * n + 1 from by omega,
    show 18 * n + 2 + i - (9 * n + 1) = 9 * n + 1 + i from by omega] at q4
  have hsi : ((-1 : ℚ)) ^ i * ((-1 : ℚ)) ^ i = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨i, by omega⟩
  have h9 : ((-1 : ℚ)) ^ (9 * n + 1) * ((-1 : ℚ)) ^ (9 * n + 1) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨9 * n + 1, by omega⟩
  have hfne : (((9 * n + 1 + i)! : ℕ) : ℚ) ≠ 0 := cast_fac_ne _
  have hine : ((i ! : ℕ) : ℚ) ≠ 0 := cast_fac_ne _
  rw [polePf1, idxS1_erase_hi n i hi, Finset.prod_union hd12, Finset.prod_union hd1, sq, q2, q3]
  refine mul_right_cancel₀ (mul_ne_zero hfne (mul_ne_zero hine hine)) ?_
  calc ((-1 : ℚ)) ^ i
        * ((∏ x ∈ Icc (7 * n + 1) (9 * n), ((x : ℚ) - ((18 * n + 2 + i : ℕ) : ℚ)))
            * (((-1 : ℚ)) ^ i * ((i ! : ℕ) : ℚ)) * (((2 * n - 1 - i)! : ℕ) : ℚ)
          * ((∏ x ∈ Icc (9 * n + 1) (18 * n + 1), ((x : ℚ) - ((18 * n + 2 + i : ℕ) : ℚ)))
            * ∏ x ∈ Icc (9 * n + 1) (18 * n + 1), ((x : ℚ) - ((18 * n + 2 + i : ℕ) : ℚ)))
          * ((i ! : ℕ) : ℚ))
        * ((((9 * n + 1 + i)! : ℕ) : ℚ) * (((i ! : ℕ) : ℚ) * (((i ! : ℕ) : ℚ))))
      = (((-1 : ℚ)) ^ i * ((-1 : ℚ)) ^ i)
          * (((∏ x ∈ Icc (7 * n + 1) (9 * n), ((x : ℚ) - ((18 * n + 2 + i : ℕ) : ℚ)))
                * (((9 * n + 1 + i)! : ℕ) : ℚ))
            * (((2 * n - 1 - i)! : ℕ) : ℚ)
            * (((∏ x ∈ Icc (9 * n + 1) (18 * n + 1), ((x : ℚ) - ((18 * n + 2 + i : ℕ) : ℚ)))
                  * ((i ! : ℕ) : ℚ))
              * ((∏ x ∈ Icc (9 * n + 1) (18 * n + 1), ((x : ℚ) - ((18 * n + 2 + i : ℕ) : ℚ)))
                  * ((i ! : ℕ) : ℚ)))
            * (((i ! : ℕ) : ℚ) * ((i ! : ℕ) : ℚ))) := by ring
    _ = (((-1 : ℚ)) ^ i * ((-1 : ℚ)) ^ i)
          * ((((11 * n + 1 + i)! : ℕ) : ℚ)
            * (((2 * n - 1 - i)! : ℕ) : ℚ)
            * ((((-1 : ℚ)) ^ (9 * n + 1) * (((9 * n + 1 + i)! : ℕ) : ℚ))
              * (((-1 : ℚ)) ^ (9 * n + 1) * (((9 * n + 1 + i)! : ℕ) : ℚ)))
            * (((i ! : ℕ) : ℚ) * ((i ! : ℕ) : ℚ))) := by rw [q1, q4]
    _ = ((((-1 : ℚ)) ^ i * ((-1 : ℚ)) ^ i)
          * (((-1 : ℚ)) ^ (9 * n + 1) * ((-1 : ℚ)) ^ (9 * n + 1)))
          * ((((11 * n + 1 + i)! : ℕ) : ℚ) * (((2 * n - 1 - i)! : ℕ) : ℚ)
              * (((9 * n + 1 + i)! : ℕ) : ℚ)
            * ((((9 * n + 1 + i)! : ℕ) : ℚ) * (((i ! : ℕ) : ℚ) * ((i ! : ℕ) : ℚ)))) := by ring
    _ = (((11 * n + 1 + i)! : ℕ) : ℚ) * (((2 * n - 1 - i)! : ℕ) : ℚ)
          * (((9 * n + 1 + i)! : ℕ) : ℚ)
        * ((((9 * n + 1 + i)! : ℕ) : ℚ) * (((i ! : ℕ) : ℚ) * ((i ! : ℕ) : ℚ))) := by
        rw [hsi, h9, one_mul, one_mul]

theorem repHatB_hi (n i : ℕ) (hi : i < 2 * n) :
    repHatB n (18 * n + 2 + i) = hatBhi n i := by
  have hn1 : ¬ (10 * n + 1 ≤ 18 * n + 2 + i ∧ 18 * n + 2 + i < 10 * n + 1 + (8 * n + 1)) := by
    omega
  have hn2 : ¬ (9 * n + 1 ≤ 18 * n + 2 + i ∧ 18 * n + 2 + i < 9 * n + 1 + n) := by omega
  have hn3 : 18 * n + 2 ≤ 18 * n + 2 + i ∧ 18 * n + 2 + i < 18 * n + 2 + 2 * n := by omega
  rw [repHatB_apply, if_neg hn1, if_neg hn2, if_pos hn3,
    show 18 * n + 2 + i - (18 * n + 2) = i from by omega]
  ring

/-- **`h₁` on the hi run** — the first of the four. -/
theorem hat_res_hi (n κ : ℕ) (hκ : κ ∈ Icc (18 * n + 2) (20 * n + 1)) :
    hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ)) = repHatB n κ * polePf1 n κ := by
  rw [Finset.mem_Icc] at hκ
  obtain ⟨i, rfl⟩ : ∃ i, κ = 18 * n + 2 + i := ⟨κ - (18 * n + 2), by omega⟩
  have hi : i < 2 * n := by omega
  have hN := hatNum_eval_neg_above n (18 * n + 2 + i) (by omega) (by omega)
  rw [show 2 * (18 * n + 2 + i) - 20 * n - 2 = 16 * n + 2 + 2 * i from by omega,
    show 18 * n + 2 + i - 5 * n - 1 = 13 * n + 1 + i from by omega,
    show 2 * (18 * n + 2 + i) - 3 * n - 2 = 33 * n + 2 + 2 * i from by omega,
    show 18 * n + 2 + i - 1 = 18 * n + 1 + i from by omega] at hN
  have hP := polePf1_hi n i hi
  have hB : hatBhi n i
      * ((((16 * n + 2 + 2 * i)! : ℕ) : ℚ) * (((13 * n + 1 + i)! : ℕ) : ℚ)
        * (((11 * n + 1 + i)! : ℕ) : ℚ) * (((9 * n + 1 + i)! : ℕ) : ℚ)
        * (((2 * n - 1 - i)! : ℕ) : ℚ))
      = ((-1 : ℚ)) ^ i * hatPi n
        * ((((33 * n + 2 + 2 * i)! : ℕ) : ℚ) * (((18 * n + 1 + i)! : ℕ) : ℚ)
          * ((i ! : ℕ) : ℚ)) := by
    have d1 := cast_fac_ne (16 * n + 2 + 2 * i)
    have d2 := cast_fac_ne (13 * n + 1 + i)
    have d3 := cast_fac_ne (11 * n + 1 + i)
    have d4 := cast_fac_ne (9 * n + 1 + i)
    have d5 := cast_fac_ne (2 * n - 1 - i)
    rw [hatBhi]
    push_cast
    field_simp
  rw [repHatB_hi n i hi]
  refine mul_right_cancel₀ (show (((16 * n + 2 + 2 * i)! : ℕ) : ℚ)
      * (((13 * n + 1 + i)! : ℕ) : ℚ) * (((11 * n + 1 + i)! : ℕ) : ℚ)
      * (((9 * n + 1 + i)! : ℕ) : ℚ) * (((2 * n - 1 - i)! : ℕ) : ℚ) * ((i ! : ℕ) : ℚ) ≠ 0 from by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (cast_fac_ne _) (cast_fac_ne _)) (cast_fac_ne _)) (cast_fac_ne _)) (cast_fac_ne _))
      (cast_fac_ne _)) ?_
  linear_combination
    (hatPi n * (((11 * n + 1 + i)! : ℕ) : ℚ) * (((9 * n + 1 + i)! : ℕ) : ℚ)
      * (((2 * n - 1 - i)! : ℕ) : ℚ) * ((i ! : ℕ) : ℚ)) * hN
    - (polePf1 n (18 * n + 2 + i) * ((i ! : ℕ) : ℚ)) * hB
    - (hatPi n * (((33 * n + 2 + 2 * i)! : ℕ) : ℚ) * (((18 * n + 1 + i)! : ℕ) : ℚ)
        * ((i ! : ℕ) : ℚ)) * hP

/-! ## Row 3 of the pole table — `h₂` on the DOUBLE run `[10n+1, 18n+1]`, i.e. `hatA`

Here `polePf2` has NO division at all once the four runs are collapsed: the two `1/(·)!` from
the simple runs are cancelled exactly by the squared erased set.  What the clearing needs
instead is `hatA`'s four binomials as factorial quotients, and the `(11n)!²/((17n)!(5n)!)` of
`hatPi` — the `(17n)!`, `(11n)!` and `(5n)!` cancel across the two sides and NOTHING about the
size of `n` is used. -/

theorem idxS2_erase_double (n j : ℕ) (hj : j ≤ 8 * n) :
    (idxS2 n).erase (10 * n + 1 + j)
      = Icc (9 * n + 1) (10 * n + j) ∪ Icc (10 * n + 2 + j) (18 * n + 1) := by
  ext x
  simp only [idxS2, Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
  omega

/-- The double-pole cofactor on the `[10n+1, 18n+1]` run, as a product of four factorials —
no division and no sign: the cancelled run's `(−1)^(2n)` is even and the erased set's `(−1)^(n+j)`
is squared. -/
theorem polePf2_double (n j : ℕ) (hj : j ≤ 8 * n) :
    polePf2 n (10 * n + 1 + j)
      = (((3 * n + j)! : ℕ) : ℚ) * (((10 * n - j)! : ℕ) : ℚ) * (((n + j)! : ℕ) : ℚ)
        * (((8 * n - j)! : ℕ) : ℚ) := by
  classical
  have hdS1 : Disjoint (Icc (7 * n + 1) (9 * n)) (Icc (18 * n + 2) (20 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have hdE : Disjoint (Icc (9 * n + 1) (10 * n + j)) (Icc (10 * n + 2 + j) (18 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have r1 := Zeta2PE.prod_Icc_sub_below (10 * n + 1 + j) (7 * n + 1) (9 * n) (by omega) (by omega)
  have r2 := Zeta2PE.prod_Icc_sub_above (10 * n + 1 + j) (18 * n + 2) (20 * n + 1)
    (by omega) (by omega)
  have r3 := Zeta2PE.prod_Icc_sub_below (10 * n + 1 + j) (9 * n + 1) (10 * n + j)
    (by omega) (by omega)
  have r4 := Zeta2PE.prod_Icc_sub_above (10 * n + 1 + j) (10 * n + 2 + j) (18 * n + 1)
    (by omega) (by omega)
  have h2n : ((-1 : ℚ)) ^ (2 * n) = 1 := Even.neg_one_pow ⟨n, by omega⟩
  rw [show 10 * n + 1 + j - 9 * n - 1 = n + j from by omega,
    show 9 * n + 1 - (7 * n + 1) = 2 * n from by omega,
    show 10 * n + 1 + j - (7 * n + 1) = 3 * n + j from by omega, h2n, one_mul] at r1
  rw [show 18 * n + 2 - (10 * n + 1 + j) - 1 = 8 * n - j from by omega,
    show 20 * n + 1 - (10 * n + 1 + j) = 10 * n - j from by omega] at r2
  rw [show 10 * n + 1 + j - (10 * n + j) - 1 = 0 from by omega,
    show 10 * n + j + 1 - (9 * n + 1) = n + j from by omega,
    show 10 * n + 1 + j - (9 * n + 1) = n + j from by omega,
    Nat.factorial_zero, Nat.cast_one, mul_one] at r3
  rw [show 10 * n + 2 + j - (10 * n + 1 + j) - 1 = 0 from by omega,
    show 18 * n + 1 - (10 * n + 1 + j) = 8 * n - j from by omega,
    Nat.factorial_zero, Nat.cast_one, mul_one] at r4
  have hnj : ((-1 : ℚ)) ^ (n + j) * ((-1 : ℚ)) ^ (n + j) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨n + j, by omega⟩
  have e1 : (((n + j)! : ℕ) : ℚ) ≠ 0 := cast_fac_ne _
  have e2 : (((8 * n - j)! : ℕ) : ℚ) ≠ 0 := cast_fac_ne _
  rw [polePf2, idxS2_erase_double n j hj, Finset.prod_union hdE, idxS1, Finset.prod_union hdS1,
    sq, r3, r4]
  refine mul_right_cancel₀ (mul_ne_zero e1 e2) ?_
  calc ((∏ x ∈ Icc (7 * n + 1) (9 * n), ((x : ℚ) - ((10 * n + 1 + j : ℕ) : ℚ)))
          * ∏ x ∈ Icc (18 * n + 2) (20 * n + 1), ((x : ℚ) - ((10 * n + 1 + j : ℕ) : ℚ)))
        * ((((-1 : ℚ)) ^ (n + j) * (((n + j)! : ℕ) : ℚ)) * (((8 * n - j)! : ℕ) : ℚ)
          * ((((-1 : ℚ)) ^ (n + j) * (((n + j)! : ℕ) : ℚ)) * (((8 * n - j)! : ℕ) : ℚ)))
        * ((((n + j)! : ℕ) : ℚ) * (((8 * n - j)! : ℕ) : ℚ))
      = (((-1 : ℚ)) ^ (n + j) * ((-1 : ℚ)) ^ (n + j))
        * (((∏ x ∈ Icc (7 * n + 1) (9 * n), ((x : ℚ) - ((10 * n + 1 + j : ℕ) : ℚ)))
              * (((n + j)! : ℕ) : ℚ))
          * ((∏ x ∈ Icc (18 * n + 2) (20 * n + 1), ((x : ℚ) - ((10 * n + 1 + j : ℕ) : ℚ)))
              * (((8 * n - j)! : ℕ) : ℚ))
          * ((((n + j)! : ℕ) : ℚ) * (((8 * n - j)! : ℕ) : ℚ))
          * ((((n + j)! : ℕ) : ℚ) * (((8 * n - j)! : ℕ) : ℚ))) := by ring
    _ = (((-1 : ℚ)) ^ (n + j) * ((-1 : ℚ)) ^ (n + j))
        * ((((3 * n + j)! : ℕ) : ℚ) * (((10 * n - j)! : ℕ) : ℚ)
          * ((((n + j)! : ℕ) : ℚ) * (((8 * n - j)! : ℕ) : ℚ))
          * ((((n + j)! : ℕ) : ℚ) * (((8 * n - j)! : ℕ) : ℚ))) := by rw [r1, r2]
    _ = (((3 * n + j)! : ℕ) : ℚ) * (((10 * n - j)! : ℕ) : ℚ) * (((n + j)! : ℕ) : ℚ)
          * (((8 * n - j)! : ℕ) : ℚ) * ((((n + j)! : ℕ) : ℚ) * (((8 * n - j)! : ℕ) : ℚ)) := by
        rw [hnj, one_mul]; ring

theorem repHatA_double (n j : ℕ) (hj : j ≤ 8 * n) :
    repHatA n (10 * n + 1 + j) = ((hatA n j : ℕ) : ℚ) := by
  have hc : 10 * n + 1 ≤ 10 * n + 1 + j ∧ 10 * n + 1 + j < 10 * n + 1 + (8 * n + 1) := by omega
  rw [repHatA_apply, if_pos hc, show 10 * n + 1 + j - (10 * n + 1) = j from by omega]

theorem repHatB_double (n j : ℕ) (hj : j ≤ 8 * n) :
    repHatB n (10 * n + 1 + j) = ((hatA n j : ℕ) : ℚ) * hatLam n j := by
  have hc1 : 10 * n + 1 ≤ 10 * n + 1 + j ∧ 10 * n + 1 + j < 10 * n + 1 + (8 * n + 1) := by omega
  have hc2 : ¬ (9 * n + 1 ≤ 10 * n + 1 + j ∧ 10 * n + 1 + j < 9 * n + 1 + n) := by omega
  have hc3 : ¬ (18 * n + 2 ≤ 10 * n + 1 + j ∧ 10 * n + 1 + j < 18 * n + 2 + 2 * n) := by omega
  rw [repHatB_apply, if_pos hc1, if_neg hc2, if_neg hc3,
    show 10 * n + 1 + j - (10 * n + 1) = j from by omega]
  ring

/-- **`h₂` on the double run** — the second of the four.  `hatA`'s four binomials are exactly the
four factorial ratios the pole table produces. -/
theorem hat_res_double (n κ : ℕ) (hκ : κ ∈ Icc (10 * n + 1) (18 * n + 1)) :
    hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ)) = repHatA n κ * polePf2 n κ := by
  rw [Finset.mem_Icc] at hκ
  obtain ⟨j, rfl⟩ : ∃ j, κ = 10 * n + 1 + j := ⟨κ - (10 * n + 1), by omega⟩
  have hj : j ≤ 8 * n := by omega
  have hN := hatNum_eval_neg_above n (10 * n + 1 + j) (by omega) (by omega)
  rw [show 2 * (10 * n + 1 + j) - 20 * n - 2 = 2 * j from by omega,
    show 10 * n + 1 + j - 5 * n - 1 = 5 * n + j from by omega,
    show 2 * (10 * n + 1 + j) - 3 * n - 2 = 17 * n + 2 * j from by omega,
    show 10 * n + 1 + j - 1 = 10 * n + j from by omega] at hN
  have hNv : (hatNum n).eval (-((10 * n + 1 + j : ℕ) : ℚ))
      = ((((17 * n + 2 * j)! : ℕ) : ℚ) * (((10 * n + j)! : ℕ) : ℚ))
        / ((((2 * j)! : ℕ) : ℚ) * (((5 * n + j)! : ℕ) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero (cast_fac_ne _) (cast_fac_ne _))]
    exact hN
  have hu : hatPi n = ((((11 * n)! : ℕ) : ℚ) * (((11 * n)! : ℕ) : ℚ))
      / ((((17 * n)! : ℕ) : ℚ) * (((5 * n)! : ℕ) : ℚ)) := by
    rw [hatPi]
    push_cast
    ring
  have c1 := choose_cast_div (17 * n + 2 * j) (2 * j) (17 * n) (by omega) (by omega)
  have c2 := choose_cast_div (11 * n) (3 * n + j) (8 * n - j) (by omega) (by omega)
  have c3 := choose_cast_div (11 * n) (n + j) (10 * n - j) (by omega) (by omega)
  have c4 := choose_cast_div (10 * n + j) (5 * n) (5 * n + j) (by omega) (by omega)
  have d1 := cast_fac_ne (2 * j)
  have d2 := cast_fac_ne (5 * n + j)
  have d3 := cast_fac_ne (17 * n)
  have d4 := cast_fac_ne (5 * n)
  have d5 := cast_fac_ne (3 * n + j)
  have d6 := cast_fac_ne (8 * n - j)
  have d7 := cast_fac_ne (n + j)
  have d8 := cast_fac_ne (10 * n - j)
  rw [repHatA_double n j hj, polePf2_double n j hj, hNv, hu, hatA]
  push_cast
  rw [c1, c2, c3, c4]
  field_simp

/-! ## Row 1 of the pole table, order 1 — `h₃` on the LO run `[9n+1, 10n]`, i.e. `hatBlo`

`repHatA` is `0` here (the order-2 family starts at `10n+1`), so the order-1 condition reduces to
`Π̂·Û′(−κ) = hatBlo·V₂(−κ)` with no log-derivative in sight — and `Û` has a SIMPLE ZERO at
`t = −κ`, because `2κ ∈ [18n+2, 20n]` is inside the `(2t+l)` index range.  That is why this run
needs `hatNum_derivative_eval_neg_zero` and not the log-derivative form. -/

theorem idxS2_erase_lo (n i : ℕ) (hi : i < n) :
    (idxS2 n).erase (9 * n + 1 + i)
      = Icc (9 * n + 1) (9 * n + i) ∪ Icc (9 * n + 2 + i) (18 * n + 1) := by
  ext x
  simp only [idxS2, Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
  omega

theorem polePf2_lo (n i : ℕ) (hi : i < n) :
    polePf2 n (9 * n + 1 + i)
      = (((2 * n + i)! : ℕ) : ℚ) * (((11 * n - i)! : ℕ) : ℚ) * ((i ! : ℕ) : ℚ)
        * (((9 * n - i)! : ℕ) : ℚ) := by
  classical
  have hdS1 : Disjoint (Icc (7 * n + 1) (9 * n)) (Icc (18 * n + 2) (20 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have hdE : Disjoint (Icc (9 * n + 1) (9 * n + i)) (Icc (9 * n + 2 + i) (18 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have r1 := Zeta2PE.prod_Icc_sub_below (9 * n + 1 + i) (7 * n + 1) (9 * n) (by omega) (by omega)
  have r2 := Zeta2PE.prod_Icc_sub_above (9 * n + 1 + i) (18 * n + 2) (20 * n + 1)
    (by omega) (by omega)
  have r3 := Zeta2PE.prod_Icc_sub_below (9 * n + 1 + i) (9 * n + 1) (9 * n + i)
    (by omega) (by omega)
  have r4 := Zeta2PE.prod_Icc_sub_above (9 * n + 1 + i) (9 * n + 2 + i) (18 * n + 1)
    (by omega) (by omega)
  have h2n : ((-1 : ℚ)) ^ (2 * n) = 1 := Even.neg_one_pow ⟨n, by omega⟩
  rw [show 9 * n + 1 + i - 9 * n - 1 = i from by omega,
    show 9 * n + 1 - (7 * n + 1) = 2 * n from by omega,
    show 9 * n + 1 + i - (7 * n + 1) = 2 * n + i from by omega, h2n, one_mul] at r1
  rw [show 18 * n + 2 - (9 * n + 1 + i) - 1 = 9 * n - i from by omega,
    show 20 * n + 1 - (9 * n + 1 + i) = 11 * n - i from by omega] at r2
  rw [show 9 * n + 1 + i - (9 * n + i) - 1 = 0 from by omega,
    show 9 * n + i + 1 - (9 * n + 1) = i from by omega,
    show 9 * n + 1 + i - (9 * n + 1) = i from by omega,
    Nat.factorial_zero, Nat.cast_one, mul_one] at r3
  rw [show 9 * n + 2 + i - (9 * n + 1 + i) - 1 = 0 from by omega,
    show 18 * n + 1 - (9 * n + 1 + i) = 9 * n - i from by omega,
    Nat.factorial_zero, Nat.cast_one, mul_one] at r4
  have hii : ((-1 : ℚ)) ^ i * ((-1 : ℚ)) ^ i = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨i, by omega⟩
  have e1 : ((i ! : ℕ) : ℚ) ≠ 0 := cast_fac_ne _
  have e2 : (((9 * n - i)! : ℕ) : ℚ) ≠ 0 := cast_fac_ne _
  rw [polePf2, idxS2_erase_lo n i hi, Finset.prod_union hdE, idxS1, Finset.prod_union hdS1,
    sq, r3, r4]
  refine mul_right_cancel₀ (mul_ne_zero e1 e2) ?_
  calc ((∏ x ∈ Icc (7 * n + 1) (9 * n), ((x : ℚ) - ((9 * n + 1 + i : ℕ) : ℚ)))
          * ∏ x ∈ Icc (18 * n + 2) (20 * n + 1), ((x : ℚ) - ((9 * n + 1 + i : ℕ) : ℚ)))
        * ((((-1 : ℚ)) ^ i * ((i ! : ℕ) : ℚ)) * (((9 * n - i)! : ℕ) : ℚ)
          * ((((-1 : ℚ)) ^ i * ((i ! : ℕ) : ℚ)) * (((9 * n - i)! : ℕ) : ℚ)))
        * (((i ! : ℕ) : ℚ) * (((9 * n - i)! : ℕ) : ℚ))
      = (((-1 : ℚ)) ^ i * ((-1 : ℚ)) ^ i)
        * (((∏ x ∈ Icc (7 * n + 1) (9 * n), ((x : ℚ) - ((9 * n + 1 + i : ℕ) : ℚ)))
              * ((i ! : ℕ) : ℚ))
          * ((∏ x ∈ Icc (18 * n + 2) (20 * n + 1), ((x : ℚ) - ((9 * n + 1 + i : ℕ) : ℚ)))
              * (((9 * n - i)! : ℕ) : ℚ))
          * (((i ! : ℕ) : ℚ) * (((9 * n - i)! : ℕ) : ℚ))
          * (((i ! : ℕ) : ℚ) * (((9 * n - i)! : ℕ) : ℚ))) := by ring
    _ = (((-1 : ℚ)) ^ i * ((-1 : ℚ)) ^ i)
        * ((((2 * n + i)! : ℕ) : ℚ) * (((11 * n - i)! : ℕ) : ℚ)
          * (((i ! : ℕ) : ℚ) * (((9 * n - i)! : ℕ) : ℚ))
          * (((i ! : ℕ) : ℚ) * (((9 * n - i)! : ℕ) : ℚ))) := by rw [r1, r2]
    _ = (((2 * n + i)! : ℕ) : ℚ) * (((11 * n - i)! : ℕ) : ℚ) * ((i ! : ℕ) : ℚ)
          * (((9 * n - i)! : ℕ) : ℚ) * (((i ! : ℕ) : ℚ) * (((9 * n - i)! : ℕ) : ℚ)) := by
        rw [hii, one_mul]; ring

theorem hatNum_derivative_lo (n i : ℕ) (hi : i < n) :
    (derivative (hatNum n)).eval (-((9 * n + 1 + i : ℕ) : ℚ))
        * (((4 * n + i)! : ℕ) : ℚ)
      = 2 * ((((15 * n + 2 * i)! : ℕ) : ℚ) * (((2 * n - 1 - 2 * i)! : ℕ) : ℚ)
        * (((9 * n + i)! : ℕ) : ℚ)) := by
  classical
  have hm : 2 * (9 * n + 1 + i) ∈ Icc (3 * n + 2) (20 * n + 1) := by
    rw [Finset.mem_Icc]; omega
  have hsplit : (Icc (3 * n + 2) (20 * n + 1)).erase (2 * (9 * n + 1 + i))
      = Icc (3 * n + 2) (18 * n + 1 + 2 * i) ∪ Icc (18 * n + 3 + 2 * i) (20 * n + 1) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdE : Disjoint (Icc (3 * n + 2) (18 * n + 1 + 2 * i))
      (Icc (18 * n + 3 + 2 * i) (20 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have s1 := Zeta2PE.prod_Icc_sub_below (2 * (9 * n + 1 + i)) (3 * n + 2) (18 * n + 1 + 2 * i)
    (by omega) (by omega)
  have s2 := Zeta2PE.prod_Icc_sub_above (2 * (9 * n + 1 + i)) (18 * n + 3 + 2 * i) (20 * n + 1)
    (by omega) (by omega)
  have s3 := Zeta2PE.prod_Icc_sub_below (9 * n + 1 + i) 1 (5 * n) (by omega) (by omega)
  rw [show 2 * (9 * n + 1 + i) - (18 * n + 1 + 2 * i) - 1 = 0 from by omega,
    show 18 * n + 1 + 2 * i + 1 - (3 * n + 2) = 15 * n + 2 * i from by omega,
    show 2 * (9 * n + 1 + i) - (3 * n + 2) = 15 * n + 2 * i from by omega,
    Nat.factorial_zero, Nat.cast_one, mul_one] at s1
  rw [show 18 * n + 3 + 2 * i - 2 * (9 * n + 1 + i) - 1 = 0 from by omega,
    show 20 * n + 1 - 2 * (9 * n + 1 + i) = 2 * n - 1 - 2 * i from by omega,
    Nat.factorial_zero, Nat.cast_one, mul_one] at s2
  rw [show 9 * n + 1 + i - 5 * n - 1 = 4 * n + i from by omega,
    show 5 * n + 1 - 1 = 5 * n from by omega,
    show 9 * n + 1 + i - 1 = 9 * n + i from by omega] at s3
  have hsign : ((-1 : ℚ)) ^ (15 * n + 2 * i) * ((-1 : ℚ)) ^ (5 * n) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨10 * n + i, by omega⟩
  rw [hatNum_derivative_eval_neg_zero n (9 * n + 1 + i) hm, hsplit, Finset.prod_union hdE, s1, s2]
  calc 2 * (((((-1 : ℚ)) ^ (15 * n + 2 * i) * (((15 * n + 2 * i)! : ℕ) : ℚ))
          * (((2 * n - 1 - 2 * i)! : ℕ) : ℚ))
        * ∏ x ∈ Icc 1 (5 * n), ((x : ℚ) - ((9 * n + 1 + i : ℕ) : ℚ)))
        * (((4 * n + i)! : ℕ) : ℚ)
      = 2 * ((((-1 : ℚ)) ^ (15 * n + 2 * i) * (((15 * n + 2 * i)! : ℕ) : ℚ))
          * (((2 * n - 1 - 2 * i)! : ℕ) : ℚ))
        * ((∏ x ∈ Icc 1 (5 * n), ((x : ℚ) - ((9 * n + 1 + i : ℕ) : ℚ)))
          * (((4 * n + i)! : ℕ) : ℚ)) := by ring
    _ = 2 * ((((-1 : ℚ)) ^ (15 * n + 2 * i) * (((15 * n + 2 * i)! : ℕ) : ℚ))
          * (((2 * n - 1 - 2 * i)! : ℕ) : ℚ))
        * (((-1 : ℚ)) ^ (5 * n) * (((9 * n + i)! : ℕ) : ℚ)) := by rw [s3]
    _ = (((-1 : ℚ)) ^ (15 * n + 2 * i) * ((-1 : ℚ)) ^ (5 * n))
        * (2 * ((((15 * n + 2 * i)! : ℕ) : ℚ) * (((2 * n - 1 - 2 * i)! : ℕ) : ℚ)
          * (((9 * n + i)! : ℕ) : ℚ))) := by ring
    _ = 2 * ((((15 * n + 2 * i)! : ℕ) : ℚ) * (((2 * n - 1 - 2 * i)! : ℕ) : ℚ)
          * (((9 * n + i)! : ℕ) : ℚ)) := by rw [hsign, one_mul]

theorem repHatA_lo (n i : ℕ) (hi : i < n) : repHatA n (9 * n + 1 + i) = 0 := by
  have hc : ¬ (10 * n + 1 ≤ 9 * n + 1 + i ∧ 9 * n + 1 + i < 10 * n + 1 + (8 * n + 1)) := by omega
  rw [repHatA_apply, if_neg hc]

theorem repHatB_lo (n i : ℕ) (hi : i < n) :
    repHatB n (9 * n + 1 + i) = hatBlo n i := by
  have hc1 : ¬ (10 * n + 1 ≤ 9 * n + 1 + i ∧ 9 * n + 1 + i < 10 * n + 1 + (8 * n + 1)) := by omega
  have hc2 : 9 * n + 1 ≤ 9 * n + 1 + i ∧ 9 * n + 1 + i < 9 * n + 1 + n := by omega
  have hc3 : ¬ (18 * n + 2 ≤ 9 * n + 1 + i ∧ 9 * n + 1 + i < 18 * n + 2 + 2 * n) := by omega
  rw [repHatB_apply, if_neg hc1, if_pos hc2, if_neg hc3,
    show 9 * n + 1 + i - (9 * n + 1) = i from by omega]
  ring

/-- **`h₃` on the lo run** — the third of the four. -/
theorem hat_res_lo_deriv (n κ : ℕ) (hκ : κ ∈ Icc (9 * n + 1) (10 * n)) :
    hatPi n * (derivative (hatNum n)).eval (-((κ : ℕ) : ℚ))
      = repHatA n κ * (polePf2 n κ * poleLam n κ) + repHatB n κ * polePf2 n κ := by
  rw [Finset.mem_Icc] at hκ
  obtain ⟨i, rfl⟩ : ∃ i, κ = 9 * n + 1 + i := ⟨κ - (9 * n + 1), by omega⟩
  have hi : i < n := by omega
  have hD := hatNum_derivative_lo n i hi
  have hDv : (derivative (hatNum n)).eval (-((9 * n + 1 + i : ℕ) : ℚ))
      = 2 * ((((15 * n + 2 * i)! : ℕ) : ℚ) * (((2 * n - 1 - 2 * i)! : ℕ) : ℚ)
          * (((9 * n + i)! : ℕ) : ℚ)) / (((4 * n + i)! : ℕ) : ℚ) := by
    rw [eq_div_iff (cast_fac_ne _)]
    exact hD
  have d1 := cast_fac_ne (4 * n + i)
  have d2 := cast_fac_ne (2 * n + i)
  have d3 := cast_fac_ne (9 * n - i)
  have d4 := cast_fac_ne i
  have d5 := cast_fac_ne (11 * n - i)
  rw [repHatA_lo n i hi, repHatB_lo n i hi, polePf2_lo n i hi, hDv, hatBlo]
  push_cast
  field_simp
  ring

/-! ## Row 4 of the pole table, order 1 — `h₃` on the DOUBLE run, i.e. `hatLam`

This is the ONE obligation that is not factorial algebra: the numerator does not vanish at the
pole, so `Û′(−κ) = Û(−κ)·L` and — `h₂` on the same run being already discharged — the whole
content is the HARMONIC identity `L = poleLam n κ + hatLam n j`.  Both sides are differences of
harmonic numbers over the same runs; the four `Zeta2PE` reciprocal atoms collapse each run, and
what is left cancels exactly. -/

theorem harm_one (m : ℕ) : harm 1 m = ∑ x ∈ range m, (1 : ℚ) / ((x : ℚ) + 1) := by
  simp [harm]

/-- `poleLam` at a double pole of the `[10n+1, 18n+1]` run, in harmonic numbers: the cancelled
run and the hi run contribute one difference each, and the erased double set — counted TWICE by
the log-derivative — contributes `−H(n+j) + H(8n−j)`. -/
theorem poleLam_double (n j : ℕ) (hj : j ≤ 8 * n) :
    poleLam n (10 * n + 1 + j)
      = -harm 1 (3 * n + j) - harm 1 (n + j) + harm 1 (10 * n - j) + harm 1 (8 * n - j) := by
  classical
  have hdS1 : Disjoint (Icc (7 * n + 1) (9 * n)) (Icc (18 * n + 2) (20 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have hdE : Disjoint (Icc (9 * n + 1) (10 * n + j)) (Icc (10 * n + 2 + j) (18 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have t1 := Zeta2PE.sum_Icc_sub_inv_below (10 * n + 1 + j) (7 * n + 1) (9 * n)
    (by omega) (by omega)
  have t2 := Zeta2PE.sum_Icc_sub_inv_above (10 * n + 1 + j) (18 * n + 2) (20 * n + 1)
    (by omega) (by omega)
  have t3 := Zeta2PE.sum_Icc_sub_inv_below (10 * n + 1 + j) (9 * n + 1) (10 * n + j)
    (by omega) (by omega)
  have t4 := Zeta2PE.sum_Icc_sub_inv_above (10 * n + 1 + j) (10 * n + 2 + j) (18 * n + 1)
    (by omega) (by omega)
  rw [show 10 * n + 1 + j - (7 * n + 1) = 3 * n + j from by omega,
    show 10 * n + 1 + j - 9 * n - 1 = n + j from by omega] at t1
  rw [show 20 * n + 1 - (10 * n + 1 + j) = 10 * n - j from by omega,
    show 18 * n + 2 - (10 * n + 1 + j) - 1 = 8 * n - j from by omega] at t2
  rw [show 10 * n + 1 + j - (9 * n + 1) = n + j from by omega,
    show 10 * n + 1 + j - (10 * n + j) - 1 = 0 from by omega] at t3
  rw [show 18 * n + 1 - (10 * n + 1 + j) = 8 * n - j from by omega,
    show 10 * n + 2 + j - (10 * n + 1 + j) - 1 = 0 from by omega] at t4
  rw [poleLam, idxS1, Finset.sum_union hdS1, idxS2_erase_double n j hj, Finset.sum_union hdE,
    t1, t2, t3, t4, harm_one, harm_one, harm_one, harm_one]
  simp only [Finset.range_zero, Finset.sum_empty]
  ring

/-- The log-derivative of `Û` at a double pole of the `[10n+1, 18n+1]` run IS
`poleLam + hatLam` — the row's `h₃` reduced to one stated equation, and the reason
`Zeta2Hat.hatLam`'s four harmonic differences are the right four. -/
theorem logDeriv_double (n j : ℕ) (hj : j ≤ 8 * n) :
    2 * (∑ l ∈ Icc (3 * n + 2) (20 * n + 1),
          (1 : ℚ) / (((l : ℕ) : ℚ) - ((2 * (10 * n + 1 + j) : ℕ) : ℚ)))
        + ∑ l ∈ Icc 1 (5 * n), (1 : ℚ) / (((l : ℕ) : ℚ) - ((10 * n + 1 + j : ℕ) : ℚ))
      = poleLam n (10 * n + 1 + j) + hatLam n j := by
  have u1 := Zeta2PE.sum_Icc_sub_inv_below (2 * (10 * n + 1 + j)) (3 * n + 2) (20 * n + 1)
    (by omega) (by omega)
  have u2 := Zeta2PE.sum_Icc_sub_inv_below (10 * n + 1 + j) 1 (5 * n) (by omega) (by omega)
  rw [show 2 * (10 * n + 1 + j) - (3 * n + 2) = 17 * n + 2 * j from by omega,
    show 2 * (10 * n + 1 + j) - (20 * n + 1) - 1 = 2 * j from by omega] at u1
  rw [show 10 * n + 1 + j - 1 = 10 * n + j from by omega,
    show 10 * n + 1 + j - 5 * n - 1 = 5 * n + j from by omega] at u2
  rw [u1, u2, poleLam_double n j hj, hatLam, harm_one, harm_one, harm_one, harm_one,
    harm_one, harm_one, harm_one, harm_one]
  ring

/-- **`h₃` on the double run** — the last of the four. -/
theorem hat_res_double_deriv (n κ : ℕ) (hκ : κ ∈ Icc (10 * n + 1) (18 * n + 1)) :
    hatPi n * (derivative (hatNum n)).eval (-((κ : ℕ) : ℚ))
      = repHatA n κ * (polePf2 n κ * poleLam n κ) + repHatB n κ * polePf2 n κ := by
  have hmem := hκ
  rw [Finset.mem_Icc] at hκ
  obtain ⟨j, rfl⟩ : ∃ j, κ = 10 * n + 1 + j := ⟨κ - (10 * n + 1), by omega⟩
  have hj : j ≤ 8 * n := by omega
  rw [hatNum_derivative_eval_neg_above n (10 * n + 1 + j) (by omega) (by omega), ← mul_assoc,
    hat_res_double n (10 * n + 1 + j) hmem, logDeriv_double n j hj,
    repHatA_double n j hj, repHatB_double n j hj]
  ring

/-! ## The row's statement, UNCONDITIONAL

`hat_rep_of_residues`'s three hypotheses, each assembled from the two runs that make it up, and
nothing left over.  This is the shape PAIR-6 consumes: one `∀ k ∈ Icc` over the WRITTEN
denominator's roots (PAIR-4R's row, hypothesis shape fixed 2026-09-12), not "off the poles". -/

/-- **`h₁` over the whole simple-pole set**, the two runs assembled.  Named rather than left
inline in `hat_rep`: row PAIR-4L feeds the SAME three hypotheses to `hat_cleared` to read the
cleared identity's top coefficient, and an inline copy is how the two consumers drift. -/
theorem hat_h1 (n : ℕ) : ∀ κ ∈ idxS1 n, hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ))
    = repHatB n κ * polePf1 n κ := by
  intro κ hκ
  rw [mem_idxS1] at hκ
  rcases hκ with h | h
  · exact hat_res_cancelled n κ (Finset.mem_Icc.2 h)
  · exact hat_res_hi n κ (Finset.mem_Icc.2 h)

/-- **`h₂` over the whole double-pole set** — the genuinely double run and the lo sub-run where
the order-2 coefficient is `0`. -/
theorem hat_h2 (n : ℕ) : ∀ κ ∈ idxS2 n, hatPi n * (hatNum n).eval (-((κ : ℕ) : ℚ))
    = repHatA n κ * polePf2 n κ := by
  intro κ hκ
  rw [mem_idxS2] at hκ
  rcases Nat.lt_or_ge (10 * n) κ with h | h
  · exact hat_res_double n κ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  · exact hat_res_lo_double n κ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)

/-- **`h₃` over the whole double-pole set** — the derivative condition on both runs. -/
theorem hat_h3 (n : ℕ) : ∀ κ ∈ idxS2 n,
    hatPi n * (derivative (hatNum n)).eval (-((κ : ℕ) : ℚ))
      = repHatA n κ * (polePf2 n κ * poleLam n κ) + repHatB n κ * polePf2 n κ := by
  intro κ hκ
  rw [mem_idxS2] at hκ
  rcases Nat.lt_or_ge (10 * n) κ with h | h
  · exact hat_res_double_deriv n κ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  · exact hat_res_lo_deriv n κ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)

theorem hat_rep (n : ℕ) (t : ℚ)
    (ht : ∀ k ∈ Icc (7 * n + 1) (20 * n + 1), t + (k : ℚ) ≠ 0) :
    evalRep (repHat n) t = hatPi n * hatMember n t :=
  hat_rep_of_residues n (hat_h1 n) (hat_h2 n) (hat_h3 n) t ht

end Zeta2HatResidues

#print axioms Zeta2HatResidues.cast_fac_ne
#print axioms Zeta2HatResidues.choose_cast_div
#print axioms Zeta2HatResidues.hatNum_eval_neg
#print axioms Zeta2HatResidues.hatNum_eval_neg_above
#print axioms Zeta2HatResidues.hatNum_derivative_eval_neg_zero
#print axioms Zeta2HatResidues.hatNum_derivative_eval_neg_above
#print axioms Zeta2HatResidues.idxS1_erase_hi
#print axioms Zeta2HatResidues.polePf1_hi
#print axioms Zeta2HatResidues.repHatB_hi
#print axioms Zeta2HatResidues.hat_res_hi
#print axioms Zeta2HatResidues.idxS2_erase_double
#print axioms Zeta2HatResidues.polePf2_double
#print axioms Zeta2HatResidues.repHatA_double
#print axioms Zeta2HatResidues.repHatB_double
#print axioms Zeta2HatResidues.hat_res_double
#print axioms Zeta2HatResidues.idxS2_erase_lo
#print axioms Zeta2HatResidues.polePf2_lo
#print axioms Zeta2HatResidues.hatNum_derivative_lo
#print axioms Zeta2HatResidues.repHatA_lo
#print axioms Zeta2HatResidues.repHatB_lo
#print axioms Zeta2HatResidues.hat_res_lo_deriv
#print axioms Zeta2HatResidues.harm_one
#print axioms Zeta2HatResidues.poleLam_double
#print axioms Zeta2HatResidues.logDeriv_double
#print axioms Zeta2HatResidues.hat_res_double_deriv
#print axioms Zeta2HatResidues.hat_h1
#print axioms Zeta2HatResidues.hat_h2
#print axioms Zeta2HatResidues.hat_h3
#print axioms Zeta2HatResidues.hat_rep
