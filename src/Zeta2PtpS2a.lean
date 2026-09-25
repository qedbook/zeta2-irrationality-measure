/-
# Row PT-P, layer 9a — the run congruence on the φ̃ = 2 run stratum `[1/9, 2/17)` (the dropped
# arc is `I3`), CONDITIONAL on Anton's one-carry congruence, and piece 2 `[1/11, 2/17)`
# discharged for the harmonic side under the same hypothesis

`Zeta2PtpS2Kit` holds the stratum-free mechanism; this file spends it on the stratum
`1/9 ≤ r/p < 2/17`, `r = n mod p`, where (`Zeta2PtpCong.dropped_S1b`) the run is exactly the `u`
with `bit1 = bit2 = bit4 = 0`, on which `bit3 = 1`: the THIRD binomial `C(m, 5n)` carries once
and the other three do not.

THE MECHANISM.  With `n = p·n₁ + r` the eight floors are fixed —
`⌊2x⌋ = ⌊4x⌋ = ⌊5x⌋ = ⌊7x⌋ = 0`, `⌊9x⌋ = ⌊11x⌋ = ⌊13x⌋ = 1`, `⌊22x⌋ = 2` — so the digits are affine:

    a = 13r − p,  b = 9r − p,  c = 5r,  e = 11r − p,        2e = 22r − 2p < c ⟺ 17r < 2p.

The run is `e ≤ u ≤ 2e` with `u + 4r < p` (`ptp_s2_mechanism_probe.py`, M1–M7 GREEN at 154 cells
of `n ≤ 60`).  On it, with `m = tp + u`,

    term(u)/p = (−1)^{t+u} · C(t+4n₁, 13n₁+1)·binPoly a(u+4r) · C(t+2n₁, 9n₁+1)·binPoly b(u+2r)
                · [ −u!/(c!(u+p−c)!) · t!/((5n₁)!(t−1−5n₁)!) ]          (Anton, `hanton`)
                · C(11n₁+1, t−11n₁−1)·(−1)^{u−e}C(e, u−e)

and `u!/(u+p−c)! = 1/((u+1)⋯(u+p−c)) = denTop(u)⁻¹`, so `term/p = κ_t · N(u)/denTop(u)` with
`N = binPoly a(X+4r)·binPoly b(X+2r)·signChoosePoly e(X−e)`.  Off the run `term/p ≡ 0` (two
carries) and `N/denTop` vanishes too: below `c` because a factor of `N` vanishes, at or above `c`
— the roots of `denTop` — because TWO factors vanish there (`dropped_S1b`: `bit3 = 0` forces
two of `bit1, bit2, bit4`), so `N` has a double root and `quot_eval_zero_of_double` applies.
`deg (N /ₘ denTop) ≤ a + b + (p−1−e) − (p−c) = 16r − p − 1 ≤ p − 2 ⟺ 16r < 2p`.

WHAT IS ASSUMED, in the TYPE.  `AntonOneCarry p` — the one-carry unit part
`C(S₀+pS₁, A₀+pA₁)/p ≡ −S₀!/(A₀!(S₀+p−A₀)!) · S₁!/(A₁!(S₁−1−A₁)!)` for `S₀ < A₀ < p`, `S₁ < p`,
`A₁ < S₁` — is a named hypothesis `hanton` on every theorem below that needs it.  It is being
built as `Zeta2Anton.choose_div_p_modEq_of_one_carry`; when it lands the binder becomes an import
and nothing else in this file moves.  `#print axioms` cannot see a binder (LEAN.md §1), so read
the `#check @` lines: `blockSum_dvd_sq` and `piece2_blocks` carry `hanton`, everything else here
is unconditional.

Probe: `ptp_s2_mechanism_probe.py` / `.out` (arm M5 checks this exact `hanton` instance verbatim).
Falsifier: `falsify_ptps2a.sh` / `out_ptps2a_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2Profile
import Zeta2PhiT
import Zeta2PtpPolar
import Zeta2PtpRun
import Zeta2PtpStratum
import Zeta2PtpCong
import Zeta2PtpBlock
import Zeta2PtpS7
import Zeta2PtpS2Kit
import Zeta2CarryFull

set_option maxRecDepth 20000

namespace Zeta2PtpS2a

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpPolar Zeta2PtpBlock Zeta2PtpS7 Zeta2PtpS2Kit
  Zeta2PtpCong Zeta2PtpRun Zeta2PtpStratum Nat Finset Polynomial

/-! ## 1. The hypothesis, named -/

/-- **Anton's one-carry congruence, the instance this file consumes.**  Both arguments below
`p²`, the units addition carries (`S₀ < A₀`), the tens addition does not (`A₁ < S₁`, one carry
in).  In the Anton–Granville digit-factorial form, mod `p`. -/
def AntonOneCarry (p : ℕ) : Prop :=
  ∀ S₀ S₁ A₀ A₁ : ℕ, S₀ < A₀ → A₀ < p → S₁ < p → A₁ < S₁ →
    ((((S₀ + p * S₁).choose (A₀ + p * A₁)) / p : ℕ) : ZMod p)
      = -(((S₀ ! : ℕ) : ZMod p) * ((((S₀ + p - A₀)! : ℕ) : ZMod p))⁻¹
            * (((A₀ ! : ℕ) : ZMod p))⁻¹)
        * (((S₁ ! : ℕ) : ZMod p) * (((A₁ ! : ℕ) : ZMod p))⁻¹
            * ((((S₁ - 1 - A₁)! : ℕ) : ZMod p))⁻¹)

/-! ## 2. The polynomial, the block constant, and the degree -/

/-- The three uncarried factors. -/
noncomputable def numer (p : ℕ) [Fact p.Prime] (r : ℕ) : (ZMod p)[X] :=
  (binPoly p (13 * r - p)).comp (X + C ((4 * r : ℕ) : ZMod p))
    * (binPoly p (9 * r - p)).comp (X + C ((2 * r : ℕ) : ZMod p))
    * (signChoosePoly p (11 * r - p)).comp (X - C ((11 * r - p : ℕ) : ZMod p))

/-- `Q = N /ₘ denTop`. -/
noncomputable def runPoly2 (p : ℕ) [Fact p.Prime] (r : ℕ) : (ZMod p)[X] :=
  quot (numer p r) (topRoots p (5 * r))

/-- `κ_t`: the sign, the three top-digit binomials, and Anton's `u`-free part. -/
def kappa2 (p n₁ r t : ℕ) : ZMod p :=
  (-1) ^ t * (-1) ^ (11 * r - p)
    * (((t + 4 * n₁).choose (13 * n₁ + 1) : ℕ) : ZMod p)
    * (((t + 2 * n₁).choose (9 * n₁ + 1) : ℕ) : ZMod p)
    * (-((((5 * r)! : ℕ) : ZMod p))⁻¹ * ((t ! : ℕ) : ZMod p)
        * ((((5 * n₁)! : ℕ) : ZMod p))⁻¹ * ((((t - 1 - 5 * n₁)! : ℕ) : ZMod p))⁻¹)
    * (((11 * n₁ + 1).choose (t - 11 * n₁ - 1) : ℕ) : ZMod p)

section Stratum
variable {p : ℕ} [hp : Fact p.Prime]

theorem numer_natDegree_le {r : ℕ} (_hr : r < p) (_hlo : p ≤ 9 * r) (_hhi : 17 * r < 2 * p) :
    (numer p r).natDegree ≤ (13 * r - p) + (9 * r - p) + (p - 1 - (11 * r - p)) := by
  unfold numer
  have hA : ((binPoly p (13 * r - p)).comp (X + C ((4 * r : ℕ) : ZMod p))).natDegree
      ≤ 13 * r - p := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact binPoly_natDegree_le _
  have hB : ((binPoly p (9 * r - p)).comp (X + C ((2 * r : ℕ) : ZMod p))).natDegree
      ≤ 9 * r - p := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_add_C, mul_one]
    exact binPoly_natDegree_le _
  have hD : ((signChoosePoly p (11 * r - p)).comp
      (X - C ((11 * r - p : ℕ) : ZMod p))).natDegree ≤ p - 1 - (11 * r - p) := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_sub_C, mul_one]
    exact signChoosePoly_natDegree_le _
  exact Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hA hB) hD

theorem isRoot_mul_of_left {f g : (ZMod p)[X]} {a : ZMod p} (h : f.IsRoot a) :
    (f * g).IsRoot a := by
  rw [IsRoot.def, eval_mul, IsRoot.def.1 h, zero_mul]

theorem isRoot_mul_of_right {f g : (ZMod p)[X]} {a : ZMod p} (h : g.IsRoot a) :
    (f * g).IsRoot a := by
  rw [IsRoot.def, eval_mul, IsRoot.def.1 h, mul_zero]

omit hp in
/-- The six residues the stratum's bit lemmas are spelled in.  (`omit hp in` sits ABOVE the
docstring, for the same parse-recovery reason as the `set_option` below.) -/
theorem residues {r : ℕ} (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p) :
    (13 * r) % p = 13 * r - p ∧ (9 * r) % p = 9 * r - p ∧ (5 * r) % p = 5 * r
    ∧ (11 * r) % p = 11 * r - p ∧ (4 * r) % p = 4 * r ∧ (2 * r) % p = 2 * r := by
  have hA := mod_eq_sub (p := p) (a := 13 * r) (q := 1) (by omega) (by omega)
  have hB := mod_eq_sub (p := p) (a := 9 * r) (q := 1) (by omega) (by omega)
  have hE := mod_eq_sub (p := p) (a := 11 * r) (q := 1) (by omega) (by omega)
  rw [one_mul] at hA hB hE
  exact ⟨hA, hB, Nat.mod_eq_of_lt (by omega), hE, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)⟩

/-! ### The three factors vanish where their bit is `1` -/

theorem root1 {r u : ℕ} (_hr : r < p) (_hlo : p ≤ 9 * r) (_hhi : 17 * r < 2 * p)
    (h : (u + 4 * r) % p < 13 * r - p) :
    ((binPoly p (13 * r - p)).comp (X + C ((4 * r : ℕ) : ZMod p))).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_add, eval_X, eval_C, ← Nat.cast_add, ← ZMod.natCast_mod,
    ← choose_cast_eq_binPoly ((u + 4 * r) % p) (13 * r - p) (by omega),
    Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

theorem root2 {r u : ℕ} (_hr : r < p) (_hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p)
    (h : (u + 2 * r) % p < 9 * r - p) :
    ((binPoly p (9 * r - p)).comp (X + C ((2 * r : ℕ) : ZMod p))).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_add, eval_X, eval_C, ← Nat.cast_add, ← ZMod.natCast_mod,
    ← choose_cast_eq_binPoly ((u + 2 * r) % p) (9 * r - p) (by omega),
    Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

/-- The residue `(u − e) mod p`, as `bit4` spells it. -/
theorem cast_sub_e {r u : ℕ} (_hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p) :
    (u : ZMod p) - ((11 * r - p : ℕ) : ZMod p)
      = (((u + (p - (11 * r - p))) % p : ℕ) : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (by omega : 11 * r - p ≤ p),
    ZMod.natCast_self]
  ring

theorem root4 {r u : ℕ} (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p)
    (h : 11 * r - p < (u + (p - (11 * r - p))) % p) :
    ((signChoosePoly p (11 * r - p)).comp
      (X - C ((11 * r - p : ℕ) : ZMod p))).IsRoot (u : ZMod p) := by
  rw [IsRoot.def, eval_comp, eval_sub, eval_X, eval_C, cast_sub_e hr hlo hhi,
    ← signChoose_eq (p := p) (11 * r - p) ((u + (p - (11 * r - p))) % p) (by omega)
      (Nat.mod_lt _ hp.out.pos),
    Nat.choose_eq_zero_of_lt h]
  simp

/-! ### The stratum's carry structure, in the bits' own spelling -/

omit hp in
/-- On the stratum, at `u ≥ c` (the roots of `denTop`) at least TWO of `bit1, bit2, bit4` are
`1`, spelled as the residue inequalities `root1/root2/root4` consume. -/
theorem two_of_three {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p)
    (hcu : 5 * r ≤ u) :
    ((u + 4 * r) % p < 13 * r - p ∧ (u + 2 * r) % p < 9 * r - p)
    ∨ ((u + 4 * r) % p < 13 * r - p ∧ 11 * r - p < (u + (p - (11 * r - p))) % p)
    ∨ ((u + 2 * r) % p < 9 * r - p ∧ 11 * r - p < (u + (p - (11 * r - p))) % p) := by
  have hp0 : 0 < p := by omega
  have hd := dropped_S1b hu hr hlo hhi
  obtain ⟨hA, hB, hC, hE, hD, hF⟩ := residues hr hlo hhi
  have h1 : (u + 4 * r) % p = if u + 4 * r < p then u + 4 * r else u + 4 * r - p :=
    add_mod_split hu (by omega)
  have h2 : (u + 2 * r) % p = if u + 2 * r < p then u + 2 * r else u + 2 * r - p :=
    add_mod_split hu (by omega)
  have h4 : (u + (p - (11 * r - p))) % p
      = if u + (p - (11 * r - p)) < p then u + (p - (11 * r - p))
        else u + (p - (11 * r - p)) - p := add_mod_split hu (by omega)
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE] at hd
  unfold bitsR at hd
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE] at hd
  rw [h1, h2, h4]
  split_ifs at hd ⊢ <;> omega

omit hp in
/-- On the stratum every residue carries at least once, and every residue OFF the run carries at
least twice — `carries ≥ 1` always, `carries ≥ 2` unless `e ≤ u ≤ 2e` and `u + 4r < p`. -/
theorem bits_ge {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p) :
    1 ≤ bitsR p r u
    ∧ (¬ (11 * r - p ≤ u ∧ u ≤ 2 * (11 * r - p) ∧ u + 4 * r < p) → 2 ≤ bitsR p r u) := by
  have hp0 : 0 < p := by omega
  obtain ⟨hA, hB, hC, hE, hD, hF⟩ := residues hr hlo hhi
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> omega

end Stratum

/-! ## 3. The identity on the run -/

section Run
variable {p : ℕ} [hp : Fact p.Prime]

/-- `u < c` is off the roots of `denTop`. -/
theorem not_mem_topRoots {c u : ℕ} (hu : u < c) (hc : c ≤ p) : (u : ZMod p) ∉ topRoots p c := by
  intro h
  unfold topRoots at h
  rw [Multiset.mem_map] at h
  obtain ⟨j, hj, hj'⟩ := h
  rw [Finset.mem_val, Finset.mem_range] at hj
  have h0 : ((u + (j + 1) : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
    rw [Nat.cast_add, ← hj']
    push_cast
    ring
  have := ((ZMod.natCast_eq_natCast_iff _ _ _).1 h0).eq_of_lt_of_lt (by omega) (by omega)
  omega

/-- The roots of `denTop` are the residues `c, …, p−1`. -/
theorem mem_topRoots {c : ℕ} {a : ZMod p} (ha : a ∈ topRoots p c) :
    ∃ u₀ : ℕ, c ≤ u₀ ∧ u₀ < p ∧ a = (u₀ : ZMod p) := by
  unfold topRoots at ha
  rw [Multiset.mem_map] at ha
  obtain ⟨j, hj, hj'⟩ := ha
  rw [Finset.mem_val, Finset.mem_range] at hj
  refine ⟨p - (j + 1), by omega, by omega, ?_⟩
  rw [← hj', Nat.cast_sub (by omega : j + 1 ≤ p), ZMod.natCast_self]
  ring

/-- **`denTop` divides `numer`** on the stratum: every root `u₀ ≥ c` has two vanishing factors. -/
theorem denTop_dvd_numer {r : ℕ} (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p) :
    linProd (topRoots p (5 * r)) ∣ numer p r := by
  refine linProd_dvd_of_roots' (topRoots_nodup _ (by omega)) fun a ha => ?_
  obtain ⟨u₀, hcu, hu, rfl⟩ := mem_topRoots ha
  unfold numer
  rcases two_of_three hu hr hlo hhi hcu with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h4⟩
  · exact isRoot_mul_of_left (isRoot_mul_of_left (root1 hr hlo hhi h1))
  · exact isRoot_mul_of_left (isRoot_mul_of_left (root1 hr hlo hhi h1))
  · exact isRoot_mul_of_right (root4 hr hlo hhi h4)

/-- **`Q` vanishes at every root of `denTop`**, by the double root. -/
theorem runPoly2_eval_zero_of_ge {r u : ℕ} (hu : u < p) (hr : r < p) (hlo : p ≤ 9 * r)
    (hhi : 17 * r < 2 * p) (hcu : 5 * r ≤ u) : (runPoly2 p r).eval (u : ZMod p) = 0 := by
  unfold runPoly2
  have hmem : (u : ZMod p) ∈ topRoots p (5 * r) := by
    unfold topRoots
    rw [Multiset.mem_map]
    refine ⟨p - 1 - u, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_range]; omega
    · have e : (p - 1 - u + 1 : ℕ) = p - u := by omega
      rw [e, Nat.cast_sub hu.le, ZMod.natCast_self]
      ring
  refine quot_eval_zero_of_double (denTop_dvd_numer hr hlo hhi) (topRoots_nodup _ (by omega))
    hmem ?_
  unfold numer
  rcases two_of_three hu hr hlo hhi hcu with ⟨h1, h2⟩ | ⟨h1, h4⟩ | ⟨h2, h4⟩
  · exact X_sub_C_sq_dvd_of_two (root1 hr hlo hhi h1) (root2 hr hlo hhi h2)
  · rw [mul_right_comm]
    exact X_sub_C_sq_dvd_of_two (root1 hr hlo hhi h1) (root4 hr hlo hhi h4)
  · rw [mul_assoc, mul_comm]
    exact X_sub_C_sq_dvd_of_two (root2 hr hlo hhi h2) (root4 hr hlo hhi h4)

/-- **`Q` below `c` is `N(u)/denTop(u)`**, and it vanishes wherever a factor of `N` does. -/
theorem runPoly2_eval_of_lt {r u : ℕ} (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p)
    (hcu : u < 5 * r) :
    (runPoly2 p r).eval (u : ZMod p)
      = (numer p r).eval (u : ZMod p) * ((denTop p (5 * r)).eval (u : ZMod p))⁻¹ :=
  quot_eval_of_not_mem (denTop_dvd_numer hr hlo hhi) (not_mem_topRoots hcu (by omega))

theorem runPoly2_natDegree_le {r : ℕ} (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p) :
    (runPoly2 p r).natDegree ≤ p - 2 := by
  unfold runPoly2
  rw [quot_natDegree, topRoots_card]
  have h := numer_natDegree_le hr hlo hhi
  omega

-- The `set_option … in` sits ABOVE the docstring: below it, the parser reads `set_option` where it
-- expects `lemma` and recovers by dropping the line (LEAN.md §1; measured again here, draft 2).
set_option maxHeartbeats 1000000 in
/-- **The identity on the run**: `term/p = κ_t · Q(u)` for `e ≤ u ≤ 2e`, `u + 4r < p`, on every
in-window block, from Lucas on three factors and Anton on the third. -/
theorem term_div_eq_of_run (hanton : AntonOneCarry p) {n n₁ r t u : ℕ}
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p)
    (hu : u < p) (hue : 11 * r - p ≤ u) (hu2 : u ≤ 2 * (11 * r - p)) (hu4 : u + 4 * r < p)
    (ht : 11 * n₁ + 1 ≤ t) (htp : t < p) :
    ((((-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
        * (cTerm n (t * p + u + 4 * n + 1) : ℤ) : ℤ) / (p : ℤ) : ℤ) : ZMod p)
      = kappa2 p n₁ r t * (runPoly2 p r).eval (u : ZMod p) := by
  have hp0 := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hpn : (p : ZMod p) = 0 := ZMod.natCast_self p
  -- affine decompositions
  have hk1 : t * p + u + 4 * n = (u + 4 * r) + (t + 4 * n₁) * p := by
    have e : (t + 4 * n₁) * p = t * p + 4 * (p * n₁) := by ring
    omega
  have hk2 : t * p + u + 4 * n + 1 - 2 * n - 1 = (u + 2 * r) + (t + 2 * n₁) * p := by
    have e : (t + 2 * n₁) * p = t * p + 2 * (p * n₁) := by ring
    omega
  have hk3 : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
  have hk4 : t * p + u + 4 * n + 1 - 15 * n - 1 = (u - (11 * r - p)) + (t - 11 * n₁ - 1) * p := by
    have e : (t - 11 * n₁ - 1) * p = t * p - (11 * n₁ + 1) * p := by
      rw [show t - 11 * n₁ - 1 = t - (11 * n₁ + 1) by omega, Nat.sub_mul]
    have e2 : (11 * n₁ + 1) * p = 11 * (p * n₁) + p := by ring
    have e3 : (11 * n₁ + 1) * p ≤ t * p := Nat.mul_le_mul_right p ht
    omega
  have h13 : 13 * n = (13 * r - p) + (13 * n₁ + 1) * p := by
    have e : (13 * n₁ + 1) * p = 13 * (p * n₁) + p := by ring
    omega
  have h9 : 9 * n = (9 * r - p) + (9 * n₁ + 1) * p := by
    have e : (9 * n₁ + 1) * p = 9 * (p * n₁) + p := by ring
    omega
  have h5 : 5 * n = 5 * r + p * (5 * n₁) := by
    have e : p * (5 * n₁) = 5 * (p * n₁) := by ring
    omega
  have h11 : 11 * n = (11 * r - p) + (11 * n₁ + 1) * p := by
    have e : (11 * n₁ + 1) * p = 11 * (p * n₁) + p := by ring
    omega
  obtain ⟨d1q, d1r⟩ := digits_of_decomp hp0 hk1 (by omega)
  obtain ⟨d2q, d2r⟩ := digits_of_decomp hp0 hk2 (by omega)
  obtain ⟨d4q, d4r⟩ := digits_of_decomp hp0 hk4 (by omega)
  obtain ⟨a13q, a13r⟩ := digits_of_decomp hp0 h13 (by omega)
  obtain ⟨a9q, a9r⟩ := digits_of_decomp hp0 h9 (by omega)
  obtain ⟨a11q, a11r⟩ := digits_of_decomp hp0 h11 (by omega)
  -- the three uncarried factors' residue classes
  have c1 : ((t * p + u + 4 * n : ℕ) : ZMod p) = (u : ZMod p) + ((4 * r : ℕ) : ZMod p) := by
    rw [cast_of_decomp hk1]; push_cast; ring
  have c2 : ((t * p + u + 4 * n + 1 - 2 * n - 1 : ℕ) : ZMod p)
      = (u : ZMod p) + ((2 * r : ℕ) : ZMod p) := by
    rw [cast_of_decomp hk2]; push_cast; ring
  -- the sign
  have hsign : (-1 : ZMod p) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
      = (-1) ^ t * ((-1) ^ (11 * r - p) * (-1) ^ (u - (11 * r - p))) := by
    have e : 12 * n + (t * p + u + 4 * n + 1) - 1
        = 2 * (8 * n) + t * p + ((11 * r - p) + (u - (11 * r - p))) := by omega
    have hp1 : (-1 : ZMod p) ^ (t * p) = (-1) ^ t := by
      rw [pow_mul' (-1 : ZMod p) t p, hodd.neg_one_pow]
    have hp2 : (-1 : ZMod p) ^ (2 * (8 * n)) = 1 := by
      rw [pow_mul (-1 : ZMod p) 2 (8 * n), neg_one_sq, one_pow]
    rw [e, pow_add, pow_add, pow_add, hp1, hp2]
    ring
  -- the fourth factor through the reflection
  have hsc := signChoose_eq (p := p) (11 * r - p) (u - (11 * r - p)) (by omega) (by omega)
  have c4 : ((u - (11 * r - p) : ℕ) : ZMod p) = (u : ZMod p) - ((11 * r - p : ℕ) : ZMod p) :=
    Nat.cast_sub hue
  rw [c4] at hsc
  -- the third factor: one carry, Anton
  have hA := hanton u t (5 * r) (5 * n₁) (by omega) (by omega) htp (by omega)
  -- `omega` does not identify `p * t` with `t * p` (measured, draft 1's `351:64`)
  have hm : u + p * t = t * p + u + 4 * n + 1 - 4 * n - 1 := by rw [hk3, mul_comm]
  rw [hm, ← h5] at hA
  -- `p` divides the carried binomial (Kummer with one digit), so the term divides exactly
  have hdvd : p ∣ (t * p + u + 4 * n + 1 - 4 * n - 1).choose (5 * n) := by
    have hle : 5 * n ≤ t * p + u + 4 * n + 1 - 4 * n - 1 := by
      have e3 : (11 * n₁ + 1) * p ≤ t * p := Nat.mul_le_mul_right p ht
      have e : (11 * n₁ + 1) * p = 11 * (p * n₁) + p := by ring
      omega
    have hlog : Nat.log p (t * p + u + 4 * n + 1 - 4 * n - 1) ≤ 1 := by
      have hlt : t * p + u + 4 * n + 1 - 4 * n - 1 < p ^ 2 := by
        rw [hk3, pow_two]
        have h1 : (t + 1) * p ≤ p * p := Nat.mul_le_mul_right p htp
        have h2 : (t + 1) * p = t * p + p := by ring
        omega
      have hne : t * p + u + 4 * n + 1 - 4 * n - 1 ≠ 0 := by
        have e3 : (11 * n₁ + 1) * p ≤ t * p := Nat.mul_le_mul_right p ht
        have e : (11 * n₁ + 1) * p = 11 * (p * n₁) + p := by ring
        omega
      have := Nat.log_lt_of_lt_pow hne hlt
      omega
    have hv := vp_choose_eq_cb (p := p) hle hlog
    have hmod1 : (t * p + u + 4 * n + 1 - 4 * n - 1) % p = u := by
      rw [hk3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
    have hmod2 : (5 * n) % p = 5 * r := by
      rw [h5, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 5 * r < p)]
    have hcb : cb p (t * p + u + 4 * n + 1 - 4 * n - 1) (5 * n) = 1 := by
      unfold cb
      rw [hmod1, hmod2]
      split_ifs with h
      · rfl
      · exfalso; omega
    rw [hcb] at hv
    have := (padicValNat_dvd_iff_le (p := p) (n := 1)
      (Nat.choose_pos hle).ne').2 (by omega)
    simpa using this
  obtain ⟨q, hq⟩ := hdvd
  have hq' : (t * p + u + 4 * n + 1 - 4 * n - 1).choose (5 * n) / p = q := by
    rw [hq, Nat.mul_div_cancel_left _ hp0]
  -- the exact division of the whole term
  have hterm : (-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
      * (cTerm n (t * p + u + 4 * n + 1) : ℤ)
      = (p : ℤ) * ((-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
          * (((t * p + u + 4 * n).choose (13 * n)
              * (t * p + u + 4 * n + 1 - 2 * n - 1).choose (9 * n) * q
              * (11 * n).choose (t * p + u + 4 * n + 1 - 15 * n - 1) : ℕ) : ℤ)) := by
    rw [cTerm, hq, Nat.add_sub_cancel (n := t * p + u + 4 * n) (m := 1)]; push_cast; ring
  rw [hterm, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp0.ne')]
  push_cast
  rw [hsign, lucas_factor (t * p + u + 4 * n) (13 * n),
    lucas_factor (t * p + u + 4 * n + 1 - 2 * n - 1) (9 * n),
    lucas_raw (11 * n) (t * p + u + 4 * n + 1 - 15 * n - 1),
    d1q, d2q, d4q, d4r, a13q, a13r, a9q, a9r, a11q, a11r, c1, c2, ← hq', hA,
    factorial_inv_eq_denTop (by omega : u < 5 * r) (by omega : 5 * r < p)]
  rw [runPoly2_eval_of_lt hr hlo hhi (by omega)]
  unfold kappa2 numer
  simp only [eval_mul, eval_comp, eval_add, eval_sub, eval_X, eval_C]
  rw [← hsc]
  ring

end Run

/-! ## 4. The block congruence on `[1/9, 2/17)`, at every block -/

section Block
variable {p : ℕ} [hp : Fact p.Prime]

/-- `p² ∣ cTerm` off the run, from `bits_ge` through Kummer. -/
theorem sq_dvd_cTerm_of_not_run {n n₁ r t u : ℕ} (hp' : p ∈ phiWindow n)
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p) (hu : u < p)
    (hk : t * p + u + 4 * n + 1 ∈ candidateM.window n)
    (hnot : ¬ (11 * r - p ≤ u ∧ u ≤ 2 * (11 * r - p) ∧ u + 4 * r < p)) :
    p ^ 2 ∣ cTerm n (t * p + u + 4 * n + 1) := by
  have hp0 := hp.out.pos
  refine pow_dvd_cTerm_of_units hp' hk ?_
  have h := carries_eq_bitsR hp0 hk
  unfold carries at h
  rw [h]
  have hk3 : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
  have hr' : n % p = r := by rw [hn, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [hk3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu, hr']
  exact (bits_ge hu hr hlo hhi).2 hnot

/-- `p ∣ cTerm` everywhere on the stratum. -/
theorem dvd_cTerm_of_stratum {n n₁ r t u : ℕ} (hp' : p ∈ phiWindow n)
    (hn : n = p * n₁ + r) (hr : r < p) (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p) (hu : u < p)
    (hk : t * p + u + 4 * n + 1 ∈ candidateM.window n) :
    p ∣ cTerm n (t * p + u + 4 * n + 1) := by
  have hp0 := hp.out.pos
  have := pow_dvd_cTerm_of_units (v := 1) hp' hk ?_
  · simpa using this
  have h := carries_eq_bitsR hp0 hk
  unfold carries at h
  rw [h]
  have hk3 : t * p + u + 4 * n + 1 - 4 * n - 1 = u + t * p := by omega
  have hr' : n % p = r := by rw [hn, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [hk3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu, hr']
  exact (bits_ge hu hr hlo hhi).1

theorem cast_div_eq_zero_of_sq_dvd {z : ℤ} (h : (p : ℤ) ^ 2 ∣ z) :
    ((z / (p : ℤ) : ℤ) : ZMod p) = 0 := by
  obtain ⟨q, hq⟩ := h
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [hq, pow_two, mul_assoc, Int.mul_ediv_cancel_left _ hp0]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- **THE BLOCK CONGRUENCE ON `[1/9, 2/17)` AT EVERY BLOCK, conditional on Anton.** -/
theorem blockSum_dvd_sq (hanton : AntonOneCarry p) {n : ℕ} (hp' : p ∈ phiWindow n)
    (hlo : p ≤ 9 * (n % p)) (hhi : 17 * (n % p) < 2 * p) (t : ℕ) :
    (p : ℤ) ^ 2 ∣ blockSum n p t := by
  have hp0 := hp.out.pos
  have hn : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hr : n % p < p := Nat.mod_lt _ hp0
  generalize n / p = n₁ at hn
  generalize n % p = r at hn hr hlo hhi
  -- an empty block: every `u` is off the window
  have hzero : (∀ u < p, t * p + u + 4 * n + 1 ∉ candidateM.window n) →
      (p : ℤ) ^ 2 ∣ blockSum n p t := by
    intro hoff
    rw [blockSum_eq_sum_range hp0 t]
    have hz : ∀ u ∈ Finset.range p,
        (if t * p + u + 4 * n + 1 ∈ candidateM.window n
          then (-1 : ℤ) ^ (12 * n + (t * p + u + 4 * n + 1) - 1)
                * (cTerm n (t * p + u + 4 * n + 1) : ℤ)
          else 0) = 0 := by
      intro u hu
      split_ifs with hmem
      · exact absurd hmem (hoff u (Finset.mem_range.mp hu))
      · rfl
    rw [Finset.sum_eq_zero hz]
    exact dvd_zero _
  rcases Nat.lt_or_ge t (11 * n₁ + 1) with hlt | hge
  · refine hzero fun u hu hmem => ?_
    rw [mem_window_iff] at hmem
    have e1 : (t + 1) * p ≤ (11 * n₁ + 1) * p := Nat.mul_le_mul_right p (by omega)
    have e2 : (t + 1) * p = t * p + p := by ring
    have e3 : (11 * n₁ + 1) * p = 11 * (p * n₁) + p := by ring
    omega
  rcases Nat.lt_or_ge (22 * n₁ + 2) t with hgt | hle
  · refine hzero fun u hu hmem => ?_
    rw [mem_window_iff] at hmem
    have e1 : (22 * n₁ + 3) * p ≤ t * p := Nat.mul_le_mul_right p (by omega)
    have e3 : (22 * n₁ + 3) * p = 22 * (p * n₁) + 3 * p := by ring
    omega
  have htp : t < p := by
    -- `t ≤ 22n₁ + 2` and the block index is below `p` at a window prime; take the in-window `k`
    -- at `u = 0` of the FIRST block... simpler: the window's last member has block index `< p`.
    have hk : 26 * n + 1 ∈ candidateM.window n := (mem_window_iff n _).2 ⟨by omega, le_rfl⟩
    have hb := block_lt hp' hk
    have e : 26 * n + 1 - 4 * n - 1 = 22 * n := by omega
    rw [e] at hb
    have e2 : (22 * n₁ + 2) * p ≤ 22 * n := by
      have : (22 * n₁ + 2) * p = 22 * (p * n₁) + 2 * p := by ring
      omega
    have : 22 * n₁ + 2 ≤ 22 * n / p := (Nat.le_div_iff_mul_le hp0).2 e2
    omega
  refine blockSum_sq_dvd_of_poly t (kappa2 p n₁ r t) (runPoly2 p r)
    (runPoly2_natDegree_le hr hlo hhi) ?_ ?_
  · -- every term is divisible by `p`
    intro u hu
    split_ifs with hmem
    · have h := dvd_cTerm_of_stratum hp' hn hr hlo hhi hu hmem
      exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 h) _
    · exact dvd_zero _
  · intro u hu
    by_cases hrun : 11 * r - p ≤ u ∧ u ≤ 2 * (11 * r - p) ∧ u + 4 * r < p
    · obtain ⟨hue, hu2, hu4⟩ := hrun
      -- on the run and on a block from the first, `u` is in the window
      have hmem : t * p + u + 4 * n + 1 ∈ candidateM.window n := by
        rw [mem_window_iff]
        have e1 : (11 * n₁ + 1) * p ≤ t * p := Nat.mul_le_mul_right p (by omega)
        have e2 : t * p ≤ (22 * n₁ + 2) * p := Nat.mul_le_mul_right p (by omega)
        have e3 : (11 * n₁ + 1) * p = 11 * (p * n₁) + p := by ring
        have e4 : (22 * n₁ + 2) * p = 22 * (p * n₁) + 2 * p := by ring
        constructor <;> omega
      split_ifs
      exact term_div_eq_of_run hanton hn hr hlo hhi hu hue hu2 hu4 (by omega) htp
    · -- off the run: the term is `0 mod p²` (or `0`), and `Q(u) = 0`
      have hQ : (runPoly2 p r).eval (u : ZMod p) = 0 := by
        rcases Nat.lt_or_ge u (5 * r) with hcu | hcu
        · rw [runPoly2_eval_of_lt hr hlo hhi hcu]
          -- a factor of `N` vanishes: which one, by which condition fails
          have hp0' : 0 < p := hp0
          have hN : (numer p r).eval (u : ZMod p) = 0 := by
            unfold numer
            simp only [eval_mul]
            by_cases hb4 : 11 * r - p < (u + (p - (11 * r - p))) % p
            · have := root4 hr hlo hhi hb4
              rw [IsRoot.def] at this
              rw [this, mul_zero]
            · by_cases hb1 : (u + 4 * r) % p < 13 * r - p
              · have := root1 hr hlo hhi hb1
                rw [IsRoot.def] at this
                rw [this, zero_mul, zero_mul]
              · exfalso
                apply hrun
                have h4 : (u + (p - (11 * r - p))) % p
                    = if u + (p - (11 * r - p)) < p then u + (p - (11 * r - p))
                      else u + (p - (11 * r - p)) - p := add_mod_split hu (by omega)
                have h1 : (u + 4 * r) % p = if u + 4 * r < p then u + 4 * r else u + 4 * r - p :=
                  add_mod_split hu (by omega)
                rw [h4] at hb4
                rw [h1] at hb1
                split_ifs at hb4 hb1 <;> omega
          rw [hN, zero_mul]
        · exact runPoly2_eval_zero_of_ge hu hr hlo hhi hcu
      rw [hQ, mul_zero]
      split_ifs with hmem
      · exact cast_div_eq_zero_of_sq_dvd (by
          have h := sq_dvd_cTerm_of_not_run hp' hn hr hlo hhi hu hmem hrun
          have h' : ((p ^ 2 : ℕ) : ℤ) ∣ ((cTerm n (t * p + u + 4 * n + 1) : ℕ) : ℤ) :=
            Int.natCast_dvd_natCast.2 h
          push_cast at h'
          exact Dvd.dvd.mul_left h' _)
      · simp

end Block

/-! ## 5. The φ̃ wire on piece 2, and the piece for the harmonic side -/

/-- `φ̃ = 2` on piece 2, `[1/11, 2/17)`. -/
theorem phiT_piece2 {x : ℚ} (h1 : 1 / 11 ≤ x) (h2 : x < 2 / 17) : phiT x = 2 := by
  have h := phiT_of_mem (a := 1 / 11) (b := 2 / 17) (v := 2) (by decide +kernel) h1 h2
  exact h

theorem phiT_piece2_res {n p : ℕ} (hp : 0 < p) (hlo : p ≤ 11 * (n % p))
    (hhi : 17 * (n % p) < 2 * p) : phiT (Int.fract ((n : ℚ) / (p : ℚ))) = 2 := by
  refine phiT_piece2 ?_ ?_
  · have h := (fract_ge_iff n p 1 11 hp (by norm_num)).2 (by omega)
    exact_mod_cast h
  · have h := (fract_lt_iff n p 2 17 hp (by norm_num)).2 (by omega)
    exact_mod_cast h

/-- **PROFILE PIECE 2 `[1/11, 2/17)` FOR THE HARMONIC SIDE, conditional on Anton**: the run-free
stratum `[1/11, 1/9)` through `Zeta2PtpCong.noShort_S1`, the run stratum through
`blockSum_dvd_sq`. -/
theorem piece2_blocks {p n : ℕ} [Fact p.Prime] (hanton : AntonOneCarry p) (hp : p ∈ phiWindow n)
    (hlo : p ≤ 11 * (n % p)) (hhi : 17 * (n % p) < 2 * p) (t : ℕ) :
    (p : ℤ) ^ (phiT (Int.fract ((n : ℚ) / (p : ℚ)))) ∣ blockSum n p t := by
  have hp0 := (prime_of_mem_phiWindow hp).pos
  rw [phiT_piece2_res hp0 hlo hhi]
  rcases Nat.lt_or_ge (9 * (n % p)) p with h9 | h9
  · exact blockSum_dvd_of_noShort hp (Zeta2PtpCong.noShort_S1 hp0 hlo h9) t
  · exact blockSum_dvd_sq hanton hp h9 hhi t

/-! ## 6. Non-vacuity -/

/-- The stratum is inhabited by a window cell: `n = 5`, `p = 43`, `r = 5` (`5/43 ∈ [1/9, 2/17)`). -/
theorem witness_5_43 : 43 ∈ phiWindow 5 ∧ 43 ≤ 9 * (5 % 43) ∧ 17 * (5 % 43) < 2 * 43 := by
  refine ⟨by decide +kernel, by decide, by decide⟩

end Zeta2PtpS2a

#print axioms Zeta2PtpS2a.numer_natDegree_le
#check @Zeta2PtpS2a.numer_natDegree_le
#print axioms Zeta2PtpS2a.root1
#check @Zeta2PtpS2a.root1
#print axioms Zeta2PtpS2a.root2
#check @Zeta2PtpS2a.root2
#print axioms Zeta2PtpS2a.root4
#check @Zeta2PtpS2a.root4
#print axioms Zeta2PtpS2a.two_of_three
#check @Zeta2PtpS2a.two_of_three
#print axioms Zeta2PtpS2a.bits_ge
#check @Zeta2PtpS2a.bits_ge
#print axioms Zeta2PtpS2a.denTop_dvd_numer
#check @Zeta2PtpS2a.denTop_dvd_numer
#print axioms Zeta2PtpS2a.runPoly2_eval_zero_of_ge
#check @Zeta2PtpS2a.runPoly2_eval_zero_of_ge
#print axioms Zeta2PtpS2a.runPoly2_eval_of_lt
#check @Zeta2PtpS2a.runPoly2_eval_of_lt
#print axioms Zeta2PtpS2a.runPoly2_natDegree_le
#check @Zeta2PtpS2a.runPoly2_natDegree_le
#print axioms Zeta2PtpS2a.term_div_eq_of_run
#check @Zeta2PtpS2a.term_div_eq_of_run
#print axioms Zeta2PtpS2a.sq_dvd_cTerm_of_not_run
#check @Zeta2PtpS2a.sq_dvd_cTerm_of_not_run
#print axioms Zeta2PtpS2a.dvd_cTerm_of_stratum
#check @Zeta2PtpS2a.dvd_cTerm_of_stratum
#print axioms Zeta2PtpS2a.blockSum_dvd_sq
#check @Zeta2PtpS2a.blockSum_dvd_sq
#print axioms Zeta2PtpS2a.phiT_piece2
#check @Zeta2PtpS2a.phiT_piece2
#print axioms Zeta2PtpS2a.phiT_piece2_res
#check @Zeta2PtpS2a.phiT_piece2_res
#print axioms Zeta2PtpS2a.piece2_blocks
#check @Zeta2PtpS2a.piece2_blocks
#print axioms Zeta2PtpS2a.witness_5_43
#check @Zeta2PtpS2a.witness_5_43
