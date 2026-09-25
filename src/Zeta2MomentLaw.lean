/-
# Row L7ID — THE PER-MONOMIAL MOMENT LAW

    ∫ℝ (C + i s)^j · π² sech²(π s) ds  =  2π · B_j(C + ½)

for every REAL `C` and every `j : ℕ`, hypothesis-free.  With `C = −4n − ½` the right-hand side
is `2π · B_j(−4n) = 2π · Zeta2Defs.momI (cell n) j`, which is what
`Zeta2L7IdSum.PpolMomentValue` is an identity between; that instantiation is
`Zeta2PpolMoment.lean` and this file stays free of every chain object.

## What it costs, and the Mathlib gap it fills

Three pieces, and only the first is real work.

1. **The Bernoulli ADDITION theorem** `B_j(x+y) = Σ_k C(j,k)·B_k(x)·y^{j−k}`, over an arbitrary
   commutative ℚ-algebra.  `Polynomial.bernoulli_eval_add` is ABSENT at this pin — measured
   twice, by two censuses — and only `_one_add` (`y = 1`) and `_one_sub` exist.  It is pure
   algebra over ℚ: expand both sides by `Polynomial.bernoulli_def` plus `add_pow` and reindex
   the double sum along the INVOLUTION `(i,l) ↦ (j − i + l, l)`.  Its residue is the trinomial
   revision `C(j,i)·C(i,l) = C(j,k)·C(k,l)`, and that IS in Mathlib — as `Nat.choose_mul`, a
   name neither earlier census tried (`Nat.choose_mul_choose_eq` and `_le` are both absent).
2. **The odd moments vanish**, from `integral_neg_eq_self` and `Odd.neg_pow`; matched on the
   Bernoulli side by `B_k(½) = 0` at odd `k`, from `Polynomial.bernoulli_eval_one_sub`.  The two
   together make the law uniform in `j` rather than a statement about even `j` only.
3. **`Complex.ofReal` through the integral**, which is `integral_ofReal` — at the ROOT and not
   under `MeasureTheory`, which is why the first census of it reported ABSENT.  LEAN.md §8: an
   unknown constant is more often the wrong namespace than a rename.

## What is NOT here

No estimate.  Obligation 2 of row L7ID is a decay RATE on `rₙ` and this law is a VALUE; nothing
in this file bounds anything.
-/
import Mathlib
import Zeta2SechMoment

namespace Zeta2MomentLaw

open MeasureTheory Filter Set

/-! ## §1. The Bernoulli ADDITION theorem — ABSENT at this pin, built here

Stated over an arbitrary commutative ℚ-algebra so that the ℚ instance (where `Polynomial.eval`
lives) and the ℝ instance (where the moment law needs it) are ONE theorem and not two. -/

/-- The trinomial revision, both sides being `j! / (l! · (i−l)! · (j−i)!)`.  `Nat.choose_mul`
twice and `Nat.choose_symm` once; the ℕ-subtraction side conditions are `omega`'s. -/
theorem choose_revision {j i l : ℕ} (hij : i ≤ j) (hli : l ≤ i) :
    j.choose i * i.choose l = j.choose (j - i + l) * (j - i + l).choose l := by
  have h1 : j.choose i * i.choose l = j.choose l * (j - l).choose (i - l) :=
    Nat.choose_mul hli
  have hlk : l ≤ j - i + l := Nat.le_add_left l (j - i)
  have h2 : j.choose (j - i + l) * (j - i + l).choose l
      = j.choose l * (j - l).choose ((j - i + l) - l) := Nat.choose_mul hlk
  have h3 : (j - i + l) - l = j - i := by omega
  have h4 : (j - l) - (i - l) = j - i := by omega
  have h5 : i - l ≤ j - l := by omega
  have h6 : (j - l).choose ((j - l) - (i - l)) = (j - l).choose (i - l) := Nat.choose_symm h5
  rw [h1, h2, h3, ← h4, h6]

/-- **`B_j(x + y) = Σ_k C(j,k)·B_k(x)·y^{j−k}`** — the theorem `Polynomial.bernoulli_eval_add`
would be if it existed.  Over any commutative ℚ-algebra, so one statement serves ℚ and ℝ. -/
theorem bernoulli_aeval_add {A : Type*} [CommRing A] [Algebra ℚ A] (j : ℕ) (x y : A) :
    Polynomial.aeval (x + y) (Polynomial.bernoulli j)
      = ∑ k ∈ Finset.range (j + 1),
          (j.choose k : A) * Polynomial.aeval x (Polynomial.bernoulli k) * y ^ (j - k) := by
  classical
  have hexp : ∀ (n : ℕ) (z : A), Polynomial.aeval z (Polynomial.bernoulli n)
      = ∑ i ∈ Finset.range (n + 1),
          (algebraMap ℚ A) (bernoulli (n - i)) * (n.choose i : A) * z ^ i := by
    intro n z
    rw [Polynomial.bernoulli_def, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.aeval_monomial, map_mul, map_natCast]
  have hL : Polynomial.aeval (x + y) (Polynomial.bernoulli j)
      = ∑ i ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (i + 1),
          (algebraMap ℚ A) (bernoulli (j - i)) * (j.choose i : A) * (i.choose l : A)
            * x ^ l * y ^ (i - l) := by
    rw [hexp j (x + y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hR : (∑ k ∈ Finset.range (j + 1),
        (j.choose k : A) * Polynomial.aeval x (Polynomial.bernoulli k) * y ^ (j - k))
      = ∑ k ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (k + 1),
          (algebraMap ℚ A) (bernoulli (k - l)) * (j.choose k : A) * (k.choose l : A)
            * x ^ l * y ^ (j - k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hexp k x, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hL, hR, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun p => (⟨j - p.1 + p.2, p.2⟩ : (_ : ℕ) × ℕ))
    (fun p => (⟨j - p.1 + p.2, p.2⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_sigma, Finset.mem_range] at hab ⊢
    omega
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_sigma, Finset.mem_range] at hab ⊢
    omega
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_sigma, Finset.mem_range] at hab
    have h : j - (j - a + b) + b = a := by omega
    rw [h]
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_sigma, Finset.mem_range] at hab
    have h : j - (j - a + b) + b = a := by omega
    rw [h]
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_sigma, Finset.mem_range] at hab
    have hab1 : a ≤ j := by omega
    have hab2 : b ≤ a := by omega
    have hbern : j - a = (j - a + b) - b := by omega
    have hy : a - b = j - (j - a + b) := by omega
    have hch := choose_revision hab1 hab2
    have hcast : (j.choose a : A) * (a.choose b : A)
        = (j.choose (j - a + b) : A) * ((j - a + b).choose b : A) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : A)) hch
    simp only []
    rw [← hbern, ← hy]
    linear_combination ((algebraMap ℚ A) (bernoulli (j - a)) * x ^ b * y ^ (a - b)) * hcast

/-- `B_k(½) = 0` at every ODD `k` — what makes the moment law uniform in `j`.  From
`Polynomial.bernoulli_eval_one_sub` at `x = ½`, where `1 − x = x`. -/
theorem bernoulli_eval_half_odd {k : ℕ} (hk : Odd k) :
    (Polynomial.bernoulli k).eval (1 / 2 : ℚ) = 0 := by
  have h := Polynomial.bernoulli_eval_one_sub k (1 / 2 : ℚ)
  rw [hk.neg_one_pow] at h
  have h2 : (1 : ℚ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h2] at h
  linarith

/-! ## §2. Integrability of `s^m · π² sech²(π s)` at EVERY `m`

`Zeta2SechMoment.integrable_moment` is stated at `2*m` because the even split is what it needs;
the law below expands a binomial and so meets odd powers too.  The majorant is `|s|^m` times
the exponential, which IS even, so `Zeta2SechMoment.integrable_of_even` applies to IT and the
integrand is then bounded by it. -/

theorem integrableOn_pow_mul_sechKer (m : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ m * Zeta2SechMoment.sechKer s) (Ioi 0) volume := by
  have hpi := Real.pi_pos
  have hmaj : IntegrableOn
      (fun s : ℝ => (4 * Real.pi ^ 2) * (s ^ m * Real.exp (-(2 * Real.pi * s))))
      (Ioi 0) volume :=
    (Zeta2SechMoment.integrableOn_pow_mul_exp m (by positivity : (0:ℝ) < 2 * Real.pi)).const_mul _
  refine Integrable.mono' hmaj
    (((continuous_pow m).mul Zeta2SechMoment.continuous_sechKer).aestronglyMeasurable) ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with s hs
  have hs0 : (0:ℝ) < s := hs
  have habs : |s| = s := abs_of_pos hs0
  have hker : Zeta2SechMoment.sechKer s ≤ 4 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi * s)) := by
    have := Zeta2SechMoment.sechKer_le s
    rwa [habs] at this
  have hpow : (0:ℝ) ≤ s ^ m := by positivity
  have hnn : (0:ℝ) ≤ s ^ m * Zeta2SechMoment.sechKer s :=
    mul_nonneg hpow (Zeta2SechMoment.sechKer_nonneg s)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  nlinarith [hker, hpow]

theorem integrable_abs_pow_majorant (m : ℕ) :
    Integrable (fun s : ℝ => (4 * Real.pi ^ 2) * (|s| ^ m * Real.exp (-(2 * Real.pi * |s|))))
      volume := by
  have hpi := Real.pi_pos
  refine Zeta2SechMoment.integrable_of_even (fun s => by rw [abs_neg]) ?_
  have h : IntegrableOn
      (fun s : ℝ => (4 * Real.pi ^ 2) * (s ^ m * Real.exp (-(2 * Real.pi * s))))
      (Ioi 0) volume :=
    (Zeta2SechMoment.integrableOn_pow_mul_exp m (by positivity : (0:ℝ) < 2 * Real.pi)).const_mul _
  refine h.congr_fun ?_ measurableSet_Ioi
  intro s hs
  have hs0 : (0:ℝ) < s := hs
  simp only [abs_of_pos hs0]

theorem integrable_pow_mul_sechKer (m : ℕ) :
    Integrable (fun s : ℝ => s ^ m * Zeta2SechMoment.sechKer s) volume := by
  have hpi := Real.pi_pos
  refine Integrable.mono' (integrable_abs_pow_majorant m)
    (((continuous_pow m).mul Zeta2SechMoment.continuous_sechKer).aestronglyMeasurable) ?_
  filter_upwards with s
  have hker : Zeta2SechMoment.sechKer s ≤ 4 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi * |s|)) :=
    Zeta2SechMoment.sechKer_le s
  have habs : |s ^ m * Zeta2SechMoment.sechKer s| = |s| ^ m * Zeta2SechMoment.sechKer s := by
    rw [abs_mul, abs_pow, abs_of_nonneg (Zeta2SechMoment.sechKer_nonneg s)]
  have hpow : (0:ℝ) ≤ |s| ^ m := by positivity
  rw [Real.norm_eq_abs, habs]
  nlinarith [hker, hpow]

/-! ## §3. The uniform moment — one statement covering even and odd `j` -/

/-- The odd moments VANISH.  `integral_neg_eq_self` needs no integrability, so this is four
lines and not a dominated-convergence argument. -/
theorem integral_odd_moment {m : ℕ} (hm : Odd m) :
    (∫ s : ℝ, s ^ m * Zeta2SechMoment.sechKer s) = 0 := by
  have hodd : ∀ s : ℝ, (-s) ^ m * Zeta2SechMoment.sechKer (-s)
      = -(s ^ m * Zeta2SechMoment.sechKer s) := by
    intro s
    rw [hm.neg_pow, Zeta2SechMoment.sechKer_even]
    ring
  have h := integral_neg_eq_self (fun s : ℝ => s ^ m * Zeta2SechMoment.sechKer s) volume
  have hL : (∫ s : ℝ, (-s) ^ m * Zeta2SechMoment.sechKer (-s))
      = ∫ s : ℝ, -(s ^ m * Zeta2SechMoment.sechKer s) :=
    integral_congr_ae (Filter.Eventually.of_forall hodd)
  rw [integral_neg] at hL
  rw [hL] at h
  linarith

/-- **`∫ℝ (i s)^m · π² sech²(π s) ds = 2π · B_m(½)`, at EVERY `m`.**  At even `m` the two
`(−1)^{m/2}` — one from `i^m`, one from the table — cancel; at odd `m` both sides are zero, the
left by parity and the right by `bernoulli_eval_half_odd`. -/
theorem integral_I_pow (m : ℕ) :
    (∫ s : ℝ, ((s : ℂ) * Complex.I) ^ m * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ))
      = ((2 * Real.pi * (((Polynomial.bernoulli m).eval (1 / 2 : ℚ) : ℚ) : ℝ) : ℝ) : ℂ) := by
  have hof : (∫ s : ℝ, ((s ^ m * Zeta2SechMoment.sechKer s : ℝ) : ℂ))
      = (((∫ s : ℝ, s ^ m * Zeta2SechMoment.sechKer s : ℝ)) : ℂ) := integral_ofReal
  have hsplit : (∫ s : ℝ, ((s : ℂ) * Complex.I) ^ m * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ))
      = Complex.I ^ m * (((∫ s : ℝ, s ^ m * Zeta2SechMoment.sechKer s : ℝ)) : ℂ) := by
    rw [← hof, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    push_cast
    ring
  rw [hsplit]
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨p, hp⟩ := he
    have hm2 : m = 2 * p := by omega
    subst hm2
    have htab : (∫ s : ℝ, s ^ (2 * p) * Zeta2SechMoment.sechKer s)
        = (-1 : ℝ) ^ p * (2 * Real.pi)
            * (((Polynomial.bernoulli (2 * p)).eval (1 / 2 : ℚ) : ℚ) : ℝ) :=
      Zeta2SechMoment.sech_moment_table p
    rw [htab]
    have hI : (Complex.I ^ (2 * p) : ℂ) = (-1 : ℂ) ^ p := by
      rw [pow_mul, Complex.I_sq]
    rw [hI]
    -- The TWO `(−1)^p` — one from `I^{2p}`, one from the table — cancel, and that cancellation
    -- is the whole content of the even branch.  `ring` cannot see it (the exponent is
    -- symbolic), so it is supplied as `hsq` and consumed by `linear_combination`.
    have hsq : (-1 : ℂ) ^ p * (-1 : ℂ) ^ p = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    push_cast
    linear_combination
      (2 * (Real.pi : ℂ) * (((Polynomial.bernoulli (2 * p)).eval (1 / 2 : ℚ) : ℚ) : ℂ)) * hsq
  · rw [integral_odd_moment ho, bernoulli_eval_half_odd ho]
    push_cast
    ring

/-! ## §4. THE LAW

The binomial expansion and its termwise integrability are named rather than inlined, because
the consumer (`Zeta2PpolMoment`) needs the INTEGRABILITY as well as the value — a finite sum
under an integral sign needs both, and a second copy of the expansion is how two spellings of
one object appear (LEAN.md §6). -/

/-- The binomial expansion of the integrand, pointwise. -/
theorem line_pow_eq_sum (C : ℝ) (j : ℕ) (s : ℝ) :
    ((C : ℂ) + (s : ℂ) * Complex.I) ^ j * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ)
      = ∑ m ∈ Finset.range (j + 1),
          ((C : ℂ) ^ (j - m) * (j.choose m : ℂ))
            * (((s : ℂ) * Complex.I) ^ m * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ)) := by
  rw [add_comm ((C : ℂ)) ((s : ℂ) * Complex.I), add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem integrable_line_term (C : ℝ) (j m : ℕ) : Integrable
    (fun s : ℝ => ((C : ℂ) ^ (j - m) * (j.choose m : ℂ))
      * (((s : ℂ) * Complex.I) ^ m * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ))) volume := by
  have hbase : Integrable
      (fun s : ℝ => (((s ^ m * Zeta2SechMoment.sechKer s : ℝ)) : ℂ)) volume :=
    (integrable_pow_mul_sechKer m).ofReal
  have h2 : Integrable
      (fun s : ℝ => Complex.I ^ m * (((s ^ m * Zeta2SechMoment.sechKer s : ℝ)) : ℂ)) volume :=
    hbase.const_mul _
  have h3 := h2.const_mul ((C : ℂ) ^ (j - m) * (j.choose m : ℂ))
  refine h3.congr (Filter.Eventually.of_forall fun s => ?_)
  push_cast
  ring

/-- The integrand itself is integrable — the finite sum of §4's terms, and what the consumer
needs to pull the `Ppol` coefficients out of the integral. -/
theorem integrable_line_pow (C : ℝ) (j : ℕ) :
    Integrable (fun s : ℝ => ((C : ℂ) + (s : ℂ) * Complex.I) ^ j
      * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ)) volume := by
  have hsum : Integrable (fun s : ℝ => ∑ m ∈ Finset.range (j + 1),
      ((C : ℂ) ^ (j - m) * (j.choose m : ℂ))
        * (((s : ℂ) * Complex.I) ^ m * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ))) volume := by
    first
    | exact integrable_finsetSum _ (fun m _ => integrable_line_term C j m)
    | exact integrable_finset_sum _ (fun m _ => integrable_line_term C j m)
  exact hsum.congr (Filter.Eventually.of_forall fun s => (line_pow_eq_sum C j s).symm)

/-- **`∫ℝ (C + i s)^j · π² sech²(π s) ds = 2π · B_j(C + ½)`**, at every REAL `C` and every `j`,
hypothesis-free.  The binomial expansion turns the integral into a FINITE sum of the moments of
§3, and the Bernoulli addition theorem of §1 re-assembles them at `C + ½`. -/
theorem integral_line_pow (C : ℝ) (j : ℕ) :
    (∫ s : ℝ, ((C : ℂ) + (s : ℂ) * Complex.I) ^ j * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ))
      = ((2 * Real.pi
            * Polynomial.aeval ((1 / 2 : ℝ) + C) (Polynomial.bernoulli j) : ℝ) : ℂ) := by
  have hterm : ∀ (s : ℝ), ((C : ℂ) + (s : ℂ) * Complex.I) ^ j
        * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ)
      = ∑ m ∈ Finset.range (j + 1),
          ((C : ℂ) ^ (j - m) * (j.choose m : ℂ))
            * (((s : ℂ) * Complex.I) ^ m * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ)) :=
    line_pow_eq_sum C j
  have hint : ∀ m ∈ Finset.range (j + 1), Integrable
      (fun s : ℝ => ((C : ℂ) ^ (j - m) * (j.choose m : ℂ))
        * (((s : ℂ) * Complex.I) ^ m * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ))) volume :=
    fun m _ => integrable_line_term C j m
  rw [integral_congr_ae (Filter.Eventually.of_forall hterm), integral_finsetSum _ hint]
  have hsum : ∀ m ∈ Finset.range (j + 1),
      (∫ s : ℝ, ((C : ℂ) ^ (j - m) * (j.choose m : ℂ))
        * (((s : ℂ) * Complex.I) ^ m * ((Zeta2SechMoment.sechKer s : ℝ) : ℂ)))
      = ((C : ℂ) ^ (j - m) * (j.choose m : ℂ))
          * ((2 * Real.pi * (((Polynomial.bernoulli m).eval (1 / 2 : ℚ) : ℚ) : ℝ) : ℝ) : ℂ) := by
    intro m _
    rw [integral_const_mul, integral_I_pow m]
  rw [Finset.sum_congr rfl hsum]
  have hadd := bernoulli_aeval_add (A := ℝ) j (1 / 2 : ℝ) C
  have hhalf : ∀ k : ℕ, Polynomial.aeval (1 / 2 : ℝ) (Polynomial.bernoulli k)
      = (((Polynomial.bernoulli k).eval (1 / 2 : ℚ) : ℚ) : ℝ) := by
    intro k
    rw [← Polynomial.eval_map_algebraMap]
    exact Zeta2SechMoment.eval_bernoulli_half_real k
  rw [hadd]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hhalf m]
  push_cast
  ring

end Zeta2MomentLaw

/-! ## RECEIPTS — the footprint AND the type, for every theorem (LEAN.md §1).

`integral_line_pow` and `bernoulli_aeval_add` take NO hypothesis; the two that do (`Odd m`,
`Odd k`) print it. -/

#print axioms Zeta2MomentLaw.choose_revision
#check @Zeta2MomentLaw.choose_revision
#print axioms Zeta2MomentLaw.bernoulli_aeval_add
#check @Zeta2MomentLaw.bernoulli_aeval_add
#print axioms Zeta2MomentLaw.bernoulli_eval_half_odd
#check @Zeta2MomentLaw.bernoulli_eval_half_odd
#print axioms Zeta2MomentLaw.integrableOn_pow_mul_sechKer
#check @Zeta2MomentLaw.integrableOn_pow_mul_sechKer
#print axioms Zeta2MomentLaw.integrable_abs_pow_majorant
#check @Zeta2MomentLaw.integrable_abs_pow_majorant
#print axioms Zeta2MomentLaw.integrable_pow_mul_sechKer
#check @Zeta2MomentLaw.integrable_pow_mul_sechKer
#print axioms Zeta2MomentLaw.integral_odd_moment
#check @Zeta2MomentLaw.integral_odd_moment
#print axioms Zeta2MomentLaw.integral_I_pow
#check @Zeta2MomentLaw.integral_I_pow
#print axioms Zeta2MomentLaw.line_pow_eq_sum
#check @Zeta2MomentLaw.line_pow_eq_sum
#print axioms Zeta2MomentLaw.integrable_line_term
#check @Zeta2MomentLaw.integrable_line_term
#print axioms Zeta2MomentLaw.integrable_line_pow
#check @Zeta2MomentLaw.integrable_line_pow
#print axioms Zeta2MomentLaw.integral_line_pow
#check @Zeta2MomentLaw.integral_line_pow
