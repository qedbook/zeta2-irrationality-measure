/-
# Row PT-P, layer 8 — the STRATUM-FREE toolkit for the φ̃ = 2 run strata: polynomial DIVISION
# by the dropped factor's non-carry residues, and Anton's unit part as a RECIPROCAL polynomial

On a φ̃ = 2 run stratum the run's terms carry EXACTLY one binomial (the dropped index of
`Zeta2PtpCong.dropped_S*`), and `p² ∣ blockSum` needs `Σ_{u<p} term(u)/p ≡ 0 (mod p)`.  The φ̃ = 1
file `Zeta2PtpS7` wrote `term = κ_t · Π(u)` with `Π` a PRODUCT of four polynomials; here that
product has degree `≥ p` (`ptp_s2_mechanism_probe.py` control R1), so it cannot feed
`dvd_sum_of_poly`.  The mechanism the probe measured (arms M1–M7 ALL GREEN on all four strata,
controls R1–R3 fired) is a QUOTIENT:

    term(u)/p  ≡  κ_t · N(u) / Den(u)        (mod p), for EVERY u < p,

`N` the three uncarried factors' polynomials and `Den` the linear factors over the residues where
the dropped factor does NOT carry — exact, because on the stratum every such residue has at least
two OTHER carries (`v_p ≥ 2`), so `N` has a double root there.  `deg Q = deg N − deg Den =
a+b+c−e−1 ≤ p−2` is then the stratum's own inequality.  The reciprocal comes from Anton's
one-carry unit part: for a carried TOP argument with units digit `u < c`, `u!/(c!(u+p−c)!) =
(1/c!) / Π_{j=1}^{p−c}(u+j)`; for a carried LOWER argument `X₀ > e` against the constant top digit
`e`, `e!/(X₀!(e+p−X₀)!) = (−1)^{e+X₀} e! / X₀(X₀−1)⋯(X₀−e)` (Wilson's reflection, twice).

THIS FILE, stratum-free:
1. `linProd s = Π_{a ∈ s}(X − a)`: monic, degree `card s`, `linProd_dvd_of_roots` (a nodup root
   multiset divides), `quot N s = N /ₘ linProd s` with `quot_natDegree`, `quot_eval_of_not_mem`
   (`Q(x) = N(x)/Den(x)` off the roots) and **`quot_eval_zero_of_double`** (`Q(a) = 0` at a root
   `a` of `Den` where `(X − a)² ∣ N`) — the one lemma the whole φ̃ = 2 program turns on.
2. `denTop p c` / `denLow p e`, the two denominators, with their evaluations as `ascFactorial` /
   `descFactorial`, and the two factorial bridges `factorial_inv_eq_denTop` /
   `factorial_inv_eq_denLow` that turn Anton's factorial form into `(Den.eval u)⁻¹`.
3. `sq_dvd_sum_of_poly` and `blockSum_sq_dvd_of_poly`: `p² ∣ blockSum n p t` from the identity on
   `term/p`, in the exact shape a stratum file discharges residue by residue.

WHAT THIS DOES NOT DO.  No stratum is closed here.  Anton's congruence itself is NOT here — it is
being built as `Zeta2Anton.choose_div_p_modEq_of_one_carry`; until it lands each stratum file
states the instance it consumes as a named hypothesis `hanton`.  `PolyHalfOpen` is untouched;
PT-P stays OPEN and `Zeta2Target.zeta2_not_liouvilleWith` stays `sorry`.

Probe: `ptp_s2_mechanism_probe.py` / `.out`.  Falsifier: `falsify_ptps2kit.sh` / `out_ptps2kit_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2PhiT
import Zeta2PtpBlock
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Factorial.BigOperators

set_option maxRecDepth 20000

namespace Zeta2PtpS2Kit

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpBlock Nat Finset Polynomial

section LinProd
variable {p : ℕ} [hp : Fact p.Prime]

/-- `Π_{a ∈ s} (X − a)`. -/
noncomputable def linProd (s : Multiset (ZMod p)) : (ZMod p)[X] :=
  (s.map fun a => X - C a).prod

theorem linProd_monic (s : Multiset (ZMod p)) : (linProd s).Monic :=
  monic_multiset_prod_of_monic s _ fun a _ => monic_X_sub_C a

theorem linProd_natDegree (s : Multiset (ZMod p)) : (linProd s).natDegree = Multiset.card s :=
  natDegree_multiset_prod_X_sub_C_eq_card s

theorem linProd_eval (s : Multiset (ZMod p)) (x : ZMod p) :
    (linProd s).eval x = (s.map fun a => x - a).prod := by
  unfold linProd
  rw [eval_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]

theorem linProd_eval_ne_zero {s : Multiset (ZMod p)} {x : ZMod p} (hx : x ∉ s) :
    (linProd s).eval x ≠ 0 := by
  rw [linProd_eval, Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  rintro ⟨a, ha, h⟩
  exact hx (by rwa [sub_eq_zero.1 h])

/-- A nodup multiset of roots divides. -/
theorem linProd_dvd_of_roots {s : Multiset (ZMod p)} {N : (ZMod p)[X]} (hN : N ≠ 0)
    (hs : s.Nodup) (h : ∀ a ∈ s, N.IsRoot a) : linProd s ∣ N :=
  (Multiset.prod_X_sub_C_dvd_iff_le_roots hN s).2
    ((Multiset.le_iff_subset hs).2 fun a ha => (mem_roots hN).2 (h a ha))

/-- The same with the `N ≠ 0` side condition discharged: `0` is divisible by everything. -/
theorem linProd_dvd_of_roots' {s : Multiset (ZMod p)} {N : (ZMod p)[X]} (hs : s.Nodup)
    (h : ∀ a ∈ s, N.IsRoot a) : linProd s ∣ N := by
  by_cases hN : N = 0
  · rw [hN]; exact dvd_zero _
  · exact linProd_dvd_of_roots hN hs h

/-- The exact quotient `N / Π(X − a)`. -/
noncomputable def quot (N : (ZMod p)[X]) (s : Multiset (ZMod p)) : (ZMod p)[X] :=
  N /ₘ linProd s

theorem linProd_mul_quot {s : Multiset (ZMod p)} {N : (ZMod p)[X]} (hd : linProd s ∣ N) :
    linProd s * quot N s = N := by
  have h := modByMonic_add_div N (linProd s)
  rwa [(modByMonic_eq_zero_iff_dvd (linProd_monic s)).2 hd, zero_add] at h

theorem quot_natDegree (N : (ZMod p)[X]) (s : Multiset (ZMod p)) :
    (quot N s).natDegree = N.natDegree - Multiset.card s := by
  rw [quot, natDegree_divByMonic _ (linProd_monic s), linProd_natDegree]

/-- Off the roots, `Q(x) = N(x) · Den(x)⁻¹`. -/
theorem quot_eval_of_not_mem {s : Multiset (ZMod p)} {N : (ZMod p)[X]} (hd : linProd s ∣ N)
    {x : ZMod p} (hx : x ∉ s) :
    (quot N s).eval x = N.eval x * ((linProd s).eval x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq₀ (linProd_eval_ne_zero hx), mul_comm, ← eval_mul, linProd_mul_quot hd]

/-- **At a root of `Den` where `N` has a DOUBLE root, the quotient vanishes.**  Cancel one
`(X − a)` from `Q · (X − a) · Den' = (X − a)² · N₁` and evaluate at `a`, where `Den'(a) ≠ 0`
because the roots are distinct. -/
theorem quot_eval_zero_of_double {s : Multiset (ZMod p)} {N : (ZMod p)[X]} (hd : linProd s ∣ N)
    (hs : s.Nodup) {a : ZMod p} (ha : a ∈ s) (h2 : (X - C a) ^ 2 ∣ N) :
    (quot N s).eval a = 0 := by
  classical
  obtain ⟨N₁, hN₁⟩ := h2
  have hsplit : linProd s = (X - C a) * linProd (s.erase a) := by
    unfold linProd
    conv_lhs => rw [← Multiset.cons_erase ha]
    rw [Multiset.map_cons, Multiset.prod_cons]
  have hne : (linProd (s.erase a)).eval a ≠ 0 :=
    linProd_eval_ne_zero fun h => ((hs.mem_erase_iff).1 h).1 rfl
  have hq : (X - C a) * (linProd (s.erase a) * quot N s) = (X - C a) * ((X - C a) * N₁) := by
    rw [← mul_assoc, ← hsplit, linProd_mul_quot hd, ← mul_assoc, ← pow_two]
    exact hN₁
  have hq' := mul_left_cancel₀ (X_sub_C_ne_zero a) hq
  have h := congrArg (eval a) hq'
  rw [eval_mul, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at h
  exact (mul_eq_zero.1 h).resolve_left hne

/-- A double root of a three-factor product from two of its factors (the other pairings are
`mul_right_comm` / `mul_comm` away at the call site). -/
theorem X_sub_C_sq_dvd_of_two {f g h : (ZMod p)[X]} {a : ZMod p} (hf : f.IsRoot a)
    (hg : g.IsRoot a) : (X - C a) ^ 2 ∣ f * g * h := by
  rw [pow_two]
  exact (mul_dvd_mul (dvd_iff_isRoot.2 hf) (dvd_iff_isRoot.2 hg)).mul_right h

end LinProd

/-! ## 2. The two denominators and Anton's factorial forms as their reciprocals -/

section Den
variable {p : ℕ}

/-- Roots `−1, −2, …, −(p−c)`: where a TOP argument's units digit `u ≥ c` does not carry. -/
noncomputable def topRoots (p c : ℕ) : Multiset (ZMod p) :=
  (Finset.range (p - c)).val.map fun j : ℕ => -((j + 1 : ℕ) : ZMod p)

/-- `Π_{j=1}^{p−c}(X + j)`. -/
noncomputable def denTop (p : ℕ) [Fact p.Prime] (c : ℕ) : (ZMod p)[X] := linProd (topRoots p c)

theorem topRoots_nodup (c : ℕ) (hc : 0 < c) : (topRoots p c).Nodup := by
  refine Multiset.Nodup.map_on ?_ (Finset.range (p - c)).nodup
  intro i hi j hj hij
  rw [Finset.mem_val, Finset.mem_range] at hi hj
  have h1 := neg_injective hij
  have h := ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).eq_of_lt_of_lt (by omega) (by omega)
  omega

theorem topRoots_card (c : ℕ) : Multiset.card (topRoots p c) = p - c := by
  unfold topRoots
  rw [Multiset.card_map, Finset.card_val, Finset.card_range]

theorem denTop_eval [Fact p.Prime] (c u : ℕ) :
    (denTop p c).eval (u : ZMod p) = (((u + 1).ascFactorial (p - c) : ℕ) : ZMod p) := by
  unfold denTop topRoots
  rw [linProd_eval, Multiset.map_map, Nat.ascFactorial_eq_prod_range,
    Nat.cast_prod, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

/-- **Anton's unit part for a carried TOP argument is `(1/c!)·Den(u)⁻¹`**: `u!/(u+p−c)!` is the
reciprocal of `(u+1)(u+2)⋯(u+p−c)`. -/
theorem factorial_inv_eq_denTop [hp : Fact p.Prime] {u c : ℕ} (hu : u < c) (hc : c < p) :
    ((u ! : ℕ) : ZMod p) * (((u + p - c)! : ℕ) : ZMod p)⁻¹
      = ((denTop p c).eval (u : ZMod p))⁻¹ := by
  have h := Nat.factorial_mul_ascFactorial u (p - c)
  have e : u + (p - c) = u + p - c := by omega
  rw [e] at h
  rw [denTop_eval c u, ← h, Nat.cast_mul, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (factorial_cast_ne_zero (by omega : u < p)), one_mul]

/-- Roots `e, e+1, …, 2e`: the residues `u = e + X₀` with `X₀ ≤ e`, where a LOWER argument
against the constant top digit `e` does not carry. -/
noncomputable def lowRoots (p e : ℕ) : Multiset (ZMod p) :=
  (Finset.range (e + 1)).val.map fun i : ℕ => ((e + i : ℕ) : ZMod p)

/-- `Π_{i=0}^{e}(X − (e + i))`. -/
noncomputable def denLow (p : ℕ) [Fact p.Prime] (e : ℕ) : (ZMod p)[X] := linProd (lowRoots p e)

theorem lowRoots_nodup (e : ℕ) (he : 2 * e < p) : (lowRoots p e).Nodup := by
  refine Multiset.Nodup.map_on ?_ (Finset.range (e + 1)).nodup
  intro i hi j hj hij
  rw [Finset.mem_val, Finset.mem_range] at hi hj
  have h := ((ZMod.natCast_eq_natCast_iff _ _ _).1 hij).eq_of_lt_of_lt (by omega) (by omega)
  omega

theorem lowRoots_card (e : ℕ) : Multiset.card (lowRoots p e) = e + 1 := by
  unfold lowRoots
  rw [Multiset.card_map, Finset.card_val, Finset.card_range]

theorem denLow_eval [Fact p.Prime] (e X₀ : ℕ) (hX : e < X₀) :
    (denLow p e).eval ((X₀ + e : ℕ) : ZMod p) = ((X₀.descFactorial (e + 1) : ℕ) : ZMod p) := by
  unfold denLow lowRoots
  rw [linProd_eval, Multiset.map_map, Nat.descFactorial_eq_prod_range,
    Nat.cast_prod, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i hi => ?_
  simp only [Function.comp_apply]
  rw [Finset.mem_val, Finset.mem_range] at hi
  rw [Nat.cast_sub (by omega : i ≤ X₀)]
  push_cast
  ring

/-- **Anton's unit part for a carried LOWER argument is `(−1)^{e+X₀} e! · Den(u)⁻¹`**, through
Wilson's reflection at `e+p−X₀` and `(X₀−e−1)! · X₀.descFactorial (e+1) = X₀!`. -/
theorem factorial_inv_eq_denLow [hp : Fact p.Prime] {e X₀ : ℕ} (he : e < X₀) (hX : X₀ < p)
    (h2 : p ≠ 2) :
    ((e ! : ℕ) : ZMod p) * ((X₀ ! : ℕ) : ZMod p)⁻¹ * (((e + p - X₀)! : ℕ) : ZMod p)⁻¹
      = (-1) ^ (e + X₀) * ((e ! : ℕ) : ZMod p)
          * (((X₀.descFactorial (e + 1) : ℕ) : ZMod p))⁻¹ := by
  have hodd : Odd p := hp.out.odd_of_ne_two h2
  set F : ZMod p := (((e + p - X₀)! : ℕ) : ZMod p) with hFdef
  set G : ZMod p := (((X₀ - e - 1)! : ℕ) : ZMod p) with hGdef
  set s : ZMod p := (-1) ^ (e + p - X₀ + 1) with hsdef
  set D : ZMod p := ((X₀.descFactorial (e + 1) : ℕ) : ZMod p) with hDdef
  have hW : F * G = s := by
    have h := factorial_reflect (p := p) (e + p - X₀) (by omega)
    have e1 : p - 1 - (e + p - X₀) = X₀ - e - 1 := by omega
    rw [e1] at h
    exact h
  have hF : G * D = ((X₀ ! : ℕ) : ZMod p) := by
    rw [hGdef, hDdef, ← Nat.cast_mul]
    have h := Nat.factorial_mul_descFactorial (show e + 1 ≤ X₀ by omega)
    have e1 : X₀ - (e + 1) = X₀ - e - 1 := by omega
    rw [e1] at h
    rw [h]
  have hs : s * s = 1 := by
    rw [hsdef, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hdesc : D = ((X₀ ! : ℕ) : ZMod p) * F * s := by
    linear_combination (F * s) * hF - D * hs - D * s * hW
  have hsign : (-1 : ZMod p) ^ (e + X₀) * s = 1 := by
    have hp1 : p % 2 = 1 := Nat.odd_iff.1 hodd
    have e1 : e + X₀ + (e + p - X₀ + 1) = 2 * (e + (p + 1) / 2) := by omega
    rw [hsdef, ← pow_add, e1, pow_mul, neg_one_sq, one_pow]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [hdesc, mul_inv, mul_inv, hsinv]
  linear_combination (-(((e ! : ℕ) : ZMod p) * ((X₀ ! : ℕ) : ZMod p)⁻¹ * F⁻¹)) * hsign

end Den

/-! ## 3. `p² ∣ blockSum` from an identity on `term/p` -/

section Block
variable {p : ℕ} [hp : Fact p.Prime]

/-- `dvd_sum_of_poly` one power up: if every `g u` is divisible by `p` and the quotients agree
mod `p` with `κ·f(u)`, `deg f ≤ p−2`, then `p² ∣ Σ g u`. -/
theorem sq_dvd_sum_of_poly (g : ℕ → ℤ) (κ : ZMod p) (f : (ZMod p)[X]) (hf : f.natDegree ≤ p - 2)
    (hdiv : ∀ u < p, (p : ℤ) ∣ g u)
    (h : ∀ u < p, ((g u / (p : ℤ) : ℤ) : ZMod p) = κ * f.eval (u : ZMod p)) :
    (p : ℤ) ^ 2 ∣ ∑ u ∈ Finset.range p, g u := by
  have h1 := dvd_sum_of_poly (fun u => g u / (p : ℤ)) κ f hf h
  have h2 : ∑ u ∈ Finset.range p, g u = (p : ℤ) * ∑ u ∈ Finset.range p, g u / (p : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    exact (Int.mul_ediv_cancel' (hdiv u (Finset.mem_range.1 hu))).symm
  rw [h2, pow_two]
  exact mul_dvd_mul_left _ h1

/-- The residue shape of a block (`blockSum_eq_sum_range`) with the exponent `2`: a stratum file
discharges `hdiv` and `h` residue by residue. -/
theorem blockSum_sq_dvd_of_poly {n : ℕ} (t : ℕ) (κ : ZMod p) (f : (ZMod p)[X])
    (hf : f.natDegree ≤ p - 2)
    (hdiv : ∀ u < p, (p : ℤ) ∣ (if t * p + u + 4 * n + 1 ∈ candidateM.window n
      then (-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
            * (cTerm n (t * p + u + 4 * n + 1) : ℤ)
      else 0))
    (h : ∀ u < p, (((if t * p + u + 4 * n + 1 ∈ candidateM.window n
      then (-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
            * (cTerm n (t * p + u + 4 * n + 1) : ℤ)
      else 0) / (p : ℤ) : ℤ) : ZMod p) = κ * f.eval (u : ZMod p)) :
    (p : ℤ) ^ 2 ∣ blockSum n p t := by
  rw [blockSum_eq_sum_range hp.out.pos t]
  exact sq_dvd_sum_of_poly _ κ f hf hdiv h

end Block

/-! ## 4. Pins -/

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `denTop 7 3 = (X+1)(X+2)(X+3)(X+4)` has degree `p − c = 4`. -/
theorem denTop_natDegree_7_3 : (denTop 7 3).natDegree = 4 := by
  unfold denTop
  rw [linProd_natDegree, topRoots_card]

/-- The LOWER bridge at `p = 7, e = 1, X₀ = 3`, inverse-free (`ZMod.inv` is an extended gcd,
which `decide` cannot unfold): `e!·X₀(X₀−1) = (−1)^{e+X₀}·e!·X₀!·(e+p−X₀)!`, i.e.
`6 ≡ 1·6·120 = 720 ≡ 6 (mod 7)`. -/
theorem bridge_pin_7_1_3 :
    ((1 ! : ℕ) : ZMod 7) * (((3).descFactorial 2 : ℕ) : ZMod 7)
      = (-1) ^ (1 + 3) * ((1 ! : ℕ) : ZMod 7) * ((3 ! : ℕ) : ZMod 7) * ((5 ! : ℕ) : ZMod 7) := by
  decide

/-- The bridge's sign `(−1)^{e+X₀}` is load-bearing: one more sign flip is false at the same
numerals (`−6 ≡ 1 ≠ 6`). -/
theorem bridge_sharp_7_1_3 :
    ((1 ! : ℕ) : ZMod 7) * (((3).descFactorial 2 : ℕ) : ZMod 7)
      ≠ (-1) ^ (1 + 3 + 1) * ((1 ! : ℕ) : ZMod 7) * ((3 ! : ℕ) : ZMod 7) * ((5 ! : ℕ) : ZMod 7) := by
  decide

end Zeta2PtpS2Kit

#print axioms Zeta2PtpS2Kit.linProd_monic
#check @Zeta2PtpS2Kit.linProd_monic
#print axioms Zeta2PtpS2Kit.linProd_natDegree
#check @Zeta2PtpS2Kit.linProd_natDegree
#print axioms Zeta2PtpS2Kit.linProd_eval
#check @Zeta2PtpS2Kit.linProd_eval
#print axioms Zeta2PtpS2Kit.linProd_eval_ne_zero
#check @Zeta2PtpS2Kit.linProd_eval_ne_zero
#print axioms Zeta2PtpS2Kit.linProd_dvd_of_roots
#check @Zeta2PtpS2Kit.linProd_dvd_of_roots
#print axioms Zeta2PtpS2Kit.linProd_dvd_of_roots'
#check @Zeta2PtpS2Kit.linProd_dvd_of_roots'
#print axioms Zeta2PtpS2Kit.linProd_mul_quot
#check @Zeta2PtpS2Kit.linProd_mul_quot
#print axioms Zeta2PtpS2Kit.quot_natDegree
#check @Zeta2PtpS2Kit.quot_natDegree
#print axioms Zeta2PtpS2Kit.quot_eval_of_not_mem
#check @Zeta2PtpS2Kit.quot_eval_of_not_mem
#print axioms Zeta2PtpS2Kit.quot_eval_zero_of_double
#check @Zeta2PtpS2Kit.quot_eval_zero_of_double
#print axioms Zeta2PtpS2Kit.X_sub_C_sq_dvd_of_two
#check @Zeta2PtpS2Kit.X_sub_C_sq_dvd_of_two
#print axioms Zeta2PtpS2Kit.topRoots_nodup
#check @Zeta2PtpS2Kit.topRoots_nodup
#print axioms Zeta2PtpS2Kit.topRoots_card
#check @Zeta2PtpS2Kit.topRoots_card
#print axioms Zeta2PtpS2Kit.denTop_eval
#check @Zeta2PtpS2Kit.denTop_eval
#print axioms Zeta2PtpS2Kit.factorial_inv_eq_denTop
#check @Zeta2PtpS2Kit.factorial_inv_eq_denTop
#print axioms Zeta2PtpS2Kit.lowRoots_nodup
#check @Zeta2PtpS2Kit.lowRoots_nodup
#print axioms Zeta2PtpS2Kit.lowRoots_card
#check @Zeta2PtpS2Kit.lowRoots_card
#print axioms Zeta2PtpS2Kit.denLow_eval
#check @Zeta2PtpS2Kit.denLow_eval
#print axioms Zeta2PtpS2Kit.factorial_inv_eq_denLow
#check @Zeta2PtpS2Kit.factorial_inv_eq_denLow
#print axioms Zeta2PtpS2Kit.sq_dvd_sum_of_poly
#check @Zeta2PtpS2Kit.sq_dvd_sum_of_poly
#print axioms Zeta2PtpS2Kit.blockSum_sq_dvd_of_poly
#check @Zeta2PtpS2Kit.blockSum_sq_dvd_of_poly
#print axioms Zeta2PtpS2Kit.denTop_natDegree_7_3
#check @Zeta2PtpS2Kit.denTop_natDegree_7_3
#print axioms Zeta2PtpS2Kit.bridge_pin_7_1_3
#check @Zeta2PtpS2Kit.bridge_pin_7_1_3
#print axioms Zeta2PtpS2Kit.bridge_sharp_7_1_3
#check @Zeta2PtpS2Kit.bridge_sharp_7_1_3
