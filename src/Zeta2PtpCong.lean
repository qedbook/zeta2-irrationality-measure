/-
# Row PT-P, layer 5 — THE STRATA AS STRATA, and the dropped index derived per stratum

`Zeta2PtpStratum.lean` landed the run-free dichotomy's easy side **at seven cells**, and said so
in its own header:

    "WHAT THIS DOES NOT DO, and the row is NOT closed.  It is a statement about SEVEN CELLS, one
     per run-free stratum, and NOT about the strata — the per-stratum statement quantifies over
     all `(r, p)` in the stratum and is not proved here in any of the seven."

**This file proves the per-stratum statement.**  For every one of the seven run-free strata,
`NoShort p n v` holds at EVERY `(n, p)` whose residue `r = n % p` lies in the stratum — not at a
pinned cell, and with no bound on `p`.  The seven landed cell pins become seven instances.

And it discharges the row's named obligation (1), the **dropped-index selection**, on all five
run-carrying strata: on each, the short set is EXACTLY one triple intersection of the four
no-carry arcs, and which arc is left out is a theorem about the stratum rather than a census
over cells.

## The mechanism, and why it is linear arithmetic rather than research

`Zeta2PtpRun.vp_cTerm_eq_units` makes the valuation four carry bits in two residues
`r = n % p`, `u = (k − 4n − 1) % p`.  Rewriting each bit's NO-carry condition as a cyclic
interval in `u` gives the four arcs

    I1 = [9r, −4r−1]    I2 = [7r, −2r−1]    I3 = [5r, −1]    I4 = [11r, 22r]   (all mod p)

and `carries = 4 − #{i : u ∈ I_i}`, so a term is short at `v` exactly when `u` lies in at least
`5 − v` of them.  The obstacle to proving anything about that in Lean is spelling: `omega`
reduces `%` and `/` only by integer LITERALS, so `(u − lo) % p < ln` with `p` a variable is
opaque to it and nothing built on that spelling can be discharged by linear arithmetic.

Three rewrites remove every such `%`.

* **`add_mod_split`** — for `u < p` and `c ≤ p`, `(u + c) % p = if u + c < p then u + c else
  u + c − p`.  One binary comparison, no `%`.  Applied to the three `u`-bearing residues
  `(u+4r) % p`, `(u+2r) % p` and `(u + 11(p−r)) % p`, whose offsets `(4r) % p`, `(2r) % p` and
  `p − (11r) % p` are PURE-`r`.
* **`mod_eq_sub`** — `q·p ≤ a < q·p + p` gives `a % p = a − q·p`.  A STRATUM is precisely a
  sub-interval of a profile piece on which every floor `⌊c·r/p⌋` is constant, so each of the six
  pure-`r` residues `(c·r) % p` becomes the affine form `c·r − j_c·p` with `j_c` a LITERAL.
* **`residue_spec`** — and then that affine form is handed over as an OPAQUE VARIABLE carrying
  two linear facts (`A + j·p = c·r`, `A < p`) rather than as the term `c·r − j·p`.  This third
  step is not cosmetic and it is where the first elaboration of this file failed: given
  `13·r − 1·p` verbatim, `omega` ATOMISED the truncated subtraction (its own report named the
  atom, `c := ↑(13 * r - 1 * p)`), lost the relation to `p`, and produced spurious
  counterexamples.  Behind `residue_spec` there is no subtraction left to atomise.

After all three, every goal is linear in `(u, r, p, A, B, C, D, E, F)` and `split_ifs` plus
`omega` closes it.  That is the whole content of the phrase "a residue comparison rather than
research" — and the price it was missing: the stratum refinement, without which the floors are
not constant and the forms are not affine (`ptp_dropped_probe` arm N1 refuted "constant on the
PIECE" at all five run-carrying pieces).

**§5's tactic is `split_ifs <;> first | omega | simp` and the `simp` is load-bearing**, for a
reason that cost this file its second elaboration and is worth recording: on a resolved branch
`split_ifs` rewrites `1 = 0` to the PROPOSITION `False`, and `omega` cannot read `False` — it
reported a counterexample over a goal that was already closed by inspection.  The traced goal was

    (1 + 0 + 1 + 1 ≤ 1 ↔ False ∧ 0 = 0 ∧ False) ∧ (False → 0 = 0 → False → 1 = 1)

§3's goals are bare inequalities (`2 ≤ 1 + 0 + 1 + 1`), never contain `False`, and take `omega`
alone — which is why the split is by section and not uniform.  The two tactics divide the work
exactly: `omega` discharges the branches that are ARITHMETICALLY UNREACHABLE on the stratum (the
real content — it is what proves the quadruple intersection empty), `simp` the ones that are
reachable and whose goal is then true by evaluation.

## What this does NOT do, and the row is NOT closed

* **`Zeta2PtpPolar.AHalfOpen` is UNTOUCHED.**  This file shows the open congruence has empty
  support on seven of the twelve strata and names its support exactly on the other five; it does
  not prove the congruence on any stratum where the support is non-empty.  Obligation (2), the
  per-cell run congruence `Σ_{u ∈ run} (−1)^{k−1}·cTerm(n,k) ≡ 0 mod p^φ̃`, has no mechanism here
  and is still RESEARCH.
* **`Zeta2PtpPolar.PolyHalfOpen` is UNTOUCHED** and remains measured-only (366 of 366), so even a
  complete `AHalfOpen` would not close the row on its own.
* **The φ̃ WIRE IS NOT PROVED HERE.**  Each stratum theorem carries its exponent as a LITERAL
  (`NoShort p n 2` / `NoShort p n 1`), the value the profile takes on the piece the stratum
  refines.  `Zeta2PhiT.phiT` is a `List.find?` over 26 triples, and `phiT (Int.fract (n/p)) = v`
  on a symbolic stratum is a separate 26-way elimination that this file does not do.  A consumer
  therefore has to supply that equation; it is named here rather than assumed.
* **PT-P stays OPEN and `Zeta2Target.zeta2_not_liouvilleWith` stays `sorry`.**

## Non-vacuity

A stratum hypothesis is a conjunction of two inequalities in `(r, p)`, and a theorem whose
hypotheses no pair satisfies proves nothing — `omega` cannot tell the difference.  Every one of
the twelve strata therefore carries a WITNESS below (`witness_…`), by `decide` on numerals; the
seven run-free ones reuse `Zeta2PtpStratum`'s own pinned cells, so the two files' populations
are visibly the same.  `no_run_1_11` and `run_nonempty_3_13` separate the two sides of the
dichotomy at the level of `bitsR` itself, and `Zeta2PtpStratum.not_noShort_3_13` remains the
proof that `NoShort` can go red.

Probe: `ptp_cong_probe.py` / `.out` (12 arms, 6 kill controls, 1 recorded inert).
Falsifier: `falsify_ptpcong.sh` / `out_ptpcong_falsify.txt`.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2Arith
import Zeta2QnInt
import Zeta2Profile
import Zeta2PhiT
import Zeta2HatGap
import Zeta2PtpRun
import Zeta2PtpStratum

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace Zeta2PtpCong

open Zeta2Defs Zeta2Arith Zeta2PhiT Zeta2PtpRun Zeta2PtpStratum Nat Finset

/-! ## 1. The four carry bits as functions of the two residues -/

/-- Bit 1 — the `C(k−1, 13n)` carry, in residues.  `bit_i p r u = 0` is exactly `u ∈ I_i`. -/
def bit1 (p r u : ℕ) : ℕ := cb p (u + 4 * r) (13 * r)
/-- Bit 2 — the `C(k−2n−1, 9n)` carry. -/
def bit2 (p r u : ℕ) : ℕ := cb p (u + 2 * r) (9 * r)
/-- Bit 3 — the `C(k−4n−1, 5n)` carry. -/
def bit3 (p r u : ℕ) : ℕ := cb p u (5 * r)
/-- Bit 4 — the `C(11n, k−15n−1)` carry.  `11·(p − r) ≡ −11r`, which is the one step in this
file where a sign is easy to lose. -/
def bit4 (p r u : ℕ) : ℕ := cb p (11 * r) (u + 11 * (p - r))

/-- `Zeta2PtpStratum.carries`, as a function of `(r, u)` alone. -/
def bitsR (p r u : ℕ) : ℕ := bit1 p r u + bit2 p r u + bit3 p r u + bit4 p r u

/-- **`carries` IS `bitsR` at the two residues.**  `Zeta2PtpStratum.carries_eq_of_residues` says
the carry count depends only on `(r, u)`; this says WHAT it is as a function of them, which is
what a per-stratum argument quantifying over `u < p` needs. -/
theorem carries_eq_bitsR {n k p : ℕ} (hp : 0 < p) (hk : k ∈ candidateM.window n) :
    carries p n k = bitsR p (n % p) ((k - 4 * n - 1) % p) := by
  obtain ⟨h1, h2⟩ := (mem_window_iff n k).1 hk
  have hrlt : n % p < p := Nat.mod_lt _ hp
  have hult : (k - 4 * n - 1) % p < p := Nat.mod_lt _ hp
  have hridem : n % p % p = n % p := Nat.mod_eq_of_lt hrlt
  have huidem : (k - 4 * n - 1) % p % p = (k - 4 * n - 1) % p := Nat.mod_eq_of_lt hult
  have mul_r : ∀ c : ℕ, (c * n) % p = (c * (n % p)) % p := by
    intro c
    conv_lhs => rw [Nat.mul_mod]
    conv_rhs => rw [Nat.mul_mod, hridem]
  have e1 : (k - 1) % p = ((k - 4 * n - 1) % p + 4 * (n % p)) % p := by
    have a : k - 1 = (k - 4 * n - 1) + 4 * n := by omega
    rw [a]
    exact Nat.ModEq.add (Nat.mod_modEq _ _).symm
      (Nat.ModEq.mul_left 4 (Nat.mod_modEq _ _).symm)
  have e2 : (k - 2 * n - 1) % p = ((k - 4 * n - 1) % p + 2 * (n % p)) % p := by
    have a : k - 2 * n - 1 = (k - 4 * n - 1) + 2 * n := by omega
    rw [a]
    exact Nat.ModEq.add (Nat.mod_modEq _ _).symm
      (Nat.ModEq.mul_left 2 (Nat.mod_modEq _ _).symm)
  have e4 : (k - 15 * n - 1) % p
      = ((k - 4 * n - 1) % p + 11 * (p - n % p)) % p := by
    refine mod_cancel (b := 11 * n) (b' := 11 * (n % p)) (mul_r 11) ?_
    have a : (k - 15 * n - 1) + 11 * n = k - 4 * n - 1 := by omega
    have b : (k - 4 * n - 1) % p + 11 * (p - n % p) + 11 * (n % p)
        = (k - 4 * n - 1) % p + p * 11 := by omega
    rw [a, b, Nat.add_mul_mod_self_left, huidem]
  have hb1 : cb p (k - 1) (13 * n)
      = cb p ((k - 4 * n - 1) % p + 4 * (n % p)) (13 * (n % p)) := by
    unfold cb; rw [e1, mul_r 13]
  have hb2 : cb p (k - 2 * n - 1) (9 * n)
      = cb p ((k - 4 * n - 1) % p + 2 * (n % p)) (9 * (n % p)) := by
    unfold cb; rw [e2, mul_r 9]
  have hb3 : cb p (k - 4 * n - 1) (5 * n)
      = cb p ((k - 4 * n - 1) % p) (5 * (n % p)) := by
    unfold cb; rw [huidem, mul_r 5]
  have hb4 : cb p (11 * n) (k - 15 * n - 1)
      = cb p (11 * (n % p)) ((k - 4 * n - 1) % p + 11 * (p - n % p)) := by
    unfold cb; rw [e4, mul_r 11]
  unfold carries bitsR bit1 bit2 bit3 bit4
  rw [hb1, hb2, hb3, hb4]

/-- `NoShort` from the residue statement — the shape every stratum theorem below produces. -/
theorem noShort_of_bits {p n v : ℕ} (hp : 0 < p)
    (h : ∀ u, u < p → v ≤ bitsR p (n % p) u) : NoShort p n v := by
  intro k hk
  rw [carries_eq_bitsR hp hk]
  exact h _ (Nat.mod_lt _ hp)

/-! ## 2. Killing the `%` — the three rewrites that make `omega` applicable -/

/-- **`a % p` with a LITERAL quotient.**  `omega` reduces `%` only by integer literals, so a
variable modulus has to be eliminated before it; on a stratum every floor `⌊c·r/p⌋` is constant
and this is the lemma that cashes that in. -/
theorem mod_eq_sub {p a q : ℕ} (h1 : q * p ≤ a) (h2 : a < q * p + p) : a % p = a - q * p := by
  have hc : p * q = q * p := Nat.mul_comm p q
  have hlt : a - q * p < p := by omega
  have e : a = a - q * p + p * q := by omega
  conv_lhs => rw [e]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hlt

/-- **The residue as an OPAQUE VARIABLE.**  Handing `omega` the term `c·r − j·p` instead loses:
it atomises the truncated subtraction and the relation to `p` goes with it.  Behind this
existential `A` is a plain variable and the two facts below are all `omega` needs. -/
theorem residue_spec {p a q : ℕ} (hp : 0 < p) (h1 : q * p ≤ a) (h2 : a < q * p + p) :
    ∃ A, a % p = A ∧ A + q * p = a ∧ A < p :=
  ⟨a % p, rfl, by rw [mod_eq_sub h1 h2]; omega, Nat.mod_lt _ hp⟩

/-- **`(u + c) % p` as ONE binary comparison**, for `u < p` and `c ≤ p`. -/
theorem add_mod_split {p u c : ℕ} (hu : u < p) (hc : c ≤ p) :
    (u + c) % p = if u + c < p then u + c else u + c - p := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have e : (u + c) % p = (u + c - p) % p := by
      conv_lhs => rw [show u + c = u + c - p + p * 1 by omega]
      rw [Nat.add_mul_mod_self_left]
    rw [e]
    exact Nat.mod_eq_of_lt (by omega)

/-- `a % p ≤ p`.  **Needs `0 < p`**: at `p = 0` the statement is `a ≤ 0`, false for every
positive `a` — the first draft of this file omitted the hypothesis and the goal `a = 0` is what
came back. -/
theorem mod_le {a p : ℕ} (hp : 0 < p) : a % p ≤ p := le_of_lt (Nat.mod_lt _ hp)

/-! ### The four bits, split and then abstracted -/

theorem bit1_abstract {p r u A D : ℕ} (hu : u < p)
    (hA : (13 * r) % p = A) (hD : (4 * r) % p = D) :
    bit1 p r u = if (if u + D < p then u + D else u + D - p) < A then 1 else 0 := by
  have hp : 0 < p := by omega
  unfold bit1 cb
  rw [Nat.add_mod u (4 * r) p, Nat.mod_eq_of_lt hu, add_mod_split hu (mod_le hp), hA, hD]

theorem bit2_abstract {p r u B F : ℕ} (hu : u < p)
    (hB : (9 * r) % p = B) (hF : (2 * r) % p = F) :
    bit2 p r u = if (if u + F < p then u + F else u + F - p) < B then 1 else 0 := by
  have hp : 0 < p := by omega
  unfold bit2 cb
  rw [Nat.add_mod u (2 * r) p, Nat.mod_eq_of_lt hu, add_mod_split hu (mod_le hp), hB, hF]

theorem bit3_abstract {p r u C : ℕ} (hu : u < p) (hC : (5 * r) % p = C) :
    bit3 p r u = if u < C then 1 else 0 := by
  unfold bit3 cb
  rw [Nat.mod_eq_of_lt hu, hC]

/-- Bit 4's offset needs one extra step: `11·(p − r) ≡ −11r ≡ p − (11r) % p`, cancelled through
`Zeta2PtpRun.mod_cancel` rather than asserted. -/
theorem bit4_abstract {p r u E : ℕ} (hu : u < p) (hr : r < p) (hE : (11 * r) % p = E) :
    bit4 p r u
      = if E < (if u + (p - E) < p then u + (p - E) else u + (p - E) - p) then 1 else 0 := by
  have hp : 0 < p := by omega
  have hElt : (11 * r) % p < p := Nat.mod_lt _ hp
  have key : (u + 11 * (p - r)) % p = (u + (p - (11 * r) % p)) % p := by
    refine mod_cancel (b := 11 * r) (b' := (11 * r) % p) (Nat.mod_eq_of_lt hElt).symm ?_
    have a : u + 11 * (p - r) + 11 * r = u + p * 11 := by omega
    have b : u + (p - (11 * r) % p) + (11 * r) % p = u + p * 1 := by omega
    rw [a, b, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
  unfold bit4 cb
  rw [key, add_mod_split hu (by omega : p - (11 * r) % p ≤ p), hE]

/-! ## 3. The seven RUN-FREE strata, as strata

Each theorem quantifies over every `(r, p)` in the stratum.  The hypotheses are the stratum's
own endpoints cleared of denominators; the six `residue_spec` lines are its constant floors,
computed by `ptp_cong_probe.py` and never typed by hand. -/

/-- piece 1, stratum `[1/11, 1/9)`, φ̃ = 2. -/
theorem bits_S1 {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : p ≤ 11 * r) (hhi : 9 * r < p) : 2 ≤ bitsR p r u := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 1) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 0) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 0) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 1) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 0) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 0) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> omega

/-- piece 6, stratum `[1/5, 2/9)`, φ̃ = 1. -/
theorem bits_S2 {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : p ≤ 5 * r) (hhi : 9 * r < 2 * p) : 1 ≤ bitsR p r u := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 2) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 1) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 1) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 2) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 0) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 0) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> omega

/-- piece 6, stratum `[2/9, 5/22)`, φ̃ = 1. -/
theorem bits_S3 {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : 2 * p ≤ 9 * r) (hhi : 22 * r < 5 * p) : 1 ≤ bitsR p r u := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 2) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 2) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 1) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 2) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 0) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 0) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> omega

/-- piece 6, stratum `[5/22, 3/13)`, φ̃ = 1. -/
theorem bits_S4 {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : 5 * p ≤ 22 * r) (hhi : 13 * r < 3 * p) : 1 ≤ bitsR p r u := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 2) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 2) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 1) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 2) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 0) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 0) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> omega

/-- piece 12, stratum `[5/11, 6/13)`, φ̃ = 2. -/
theorem bits_S5 {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : 5 * p ≤ 11 * r) (hhi : 13 * r < 6 * p) : 2 ≤ bitsR p r u := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 5) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 4) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 2) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 5) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 1) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 0) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> omega

/-- piece 15, stratum `[6/11, 5/9)`, φ̃ = 2. -/
theorem bits_S6 {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : 6 * p ≤ 11 * r) (hhi : 9 * r < 5 * p) : 2 ≤ bitsR p r u := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 7) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 4) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 2) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 6) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 2) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 1) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> omega

/-- piece 24, stratum `[10/11, 12/13)`, φ̃ = 2. -/
theorem bits_S7 {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : 10 * p ≤ 11 * r) (hhi : 13 * r < 12 * p) : 2 ≤ bitsR p r u := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 11) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 8) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 4) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 10) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 3) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 1) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> omega

/-! ### The same seven, in `NoShort` vocabulary -/

theorem noShort_S1 {n p : ℕ} (hp : 0 < p)
    (hlo : p ≤ 11 * (n % p)) (hhi : 9 * (n % p) < p) : NoShort p n 2 :=
  noShort_of_bits hp fun _ hu => bits_S1 hu (Nat.mod_lt _ hp) hlo hhi

theorem noShort_S2 {n p : ℕ} (hp : 0 < p)
    (hlo : p ≤ 5 * (n % p)) (hhi : 9 * (n % p) < 2 * p) : NoShort p n 1 :=
  noShort_of_bits hp fun _ hu => bits_S2 hu (Nat.mod_lt _ hp) hlo hhi

theorem noShort_S3 {n p : ℕ} (hp : 0 < p)
    (hlo : 2 * p ≤ 9 * (n % p)) (hhi : 22 * (n % p) < 5 * p) : NoShort p n 1 :=
  noShort_of_bits hp fun _ hu => bits_S3 hu (Nat.mod_lt _ hp) hlo hhi

theorem noShort_S4 {n p : ℕ} (hp : 0 < p)
    (hlo : 5 * p ≤ 22 * (n % p)) (hhi : 13 * (n % p) < 3 * p) : NoShort p n 1 :=
  noShort_of_bits hp fun _ hu => bits_S4 hu (Nat.mod_lt _ hp) hlo hhi

theorem noShort_S5 {n p : ℕ} (hp : 0 < p)
    (hlo : 5 * p ≤ 11 * (n % p)) (hhi : 13 * (n % p) < 6 * p) : NoShort p n 2 :=
  noShort_of_bits hp fun _ hu => bits_S5 hu (Nat.mod_lt _ hp) hlo hhi

theorem noShort_S6 {n p : ℕ} (hp : 0 < p)
    (hlo : 6 * p ≤ 11 * (n % p)) (hhi : 9 * (n % p) < 5 * p) : NoShort p n 2 :=
  noShort_of_bits hp fun _ hu => bits_S6 hu (Nat.mod_lt _ hp) hlo hhi

theorem noShort_S7 {n p : ℕ} (hp : 0 < p)
    (hlo : 10 * p ≤ 11 * (n % p)) (hhi : 13 * (n % p) < 12 * p) : NoShort p n 2 :=
  noShort_of_bits hp fun _ hu => bits_S7 hu (Nat.mod_lt _ hp) hlo hhi

/-! ## 4. The wire: the open congruence has EMPTY SUPPORT on those seven strata -/

/-- The four run-free strata of φ̃ = 2, as one predicate on `(p, r)`. -/
def RunFreeTwo (p r : ℕ) : Prop :=
  (p ≤ 11 * r ∧ 9 * r < p)              -- [1/11, 1/9)
  ∨ (5 * p ≤ 11 * r ∧ 13 * r < 6 * p)   -- [5/11, 6/13)
  ∨ (6 * p ≤ 11 * r ∧ 9 * r < 5 * p)    -- [6/11, 5/9)
  ∨ (10 * p ≤ 11 * r ∧ 13 * r < 12 * p) -- [10/11, 12/13)

/-- The three run-free strata of φ̃ = 1, as one predicate on `(p, r)`. -/
def RunFreeOne (p r : ℕ) : Prop :=
  (p ≤ 5 * r ∧ 9 * r < 2 * p)           -- [1/5, 2/9)
  ∨ (2 * p ≤ 9 * r ∧ 22 * r < 5 * p)    -- [2/9, 5/22)
  ∨ (5 * p ≤ 22 * r ∧ 13 * r < 3 * p)   -- [5/22, 3/13)

theorem noShort_of_runFreeTwo {n p : ℕ} (hp : 0 < p) (h : RunFreeTwo p (n % p)) :
    NoShort p n 2 := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact noShort_S1 hp a b
  · exact noShort_S5 hp a b
  · exact noShort_S6 hp a b
  · exact noShort_S7 hp a b

theorem noShort_of_runFreeOne {n p : ℕ} (hp : 0 < p) (h : RunFreeOne p (n % p)) :
    NoShort p n 1 := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact noShort_S2 hp a b
  · exact noShort_S3 hp a b
  · exact noShort_S4 hp a b

/-- **THE OPEN CONGRUENCE HAS EMPTY SUPPORT ON THE FOUR φ̃ = 2 RUN-FREE STRATA, AS STRATA.**
`Zeta2PtpStratum.pow_dvd_signed_sum` divides every signed sum termwise; what is new is that its
`NoShort` hypothesis is now discharged for EVERY `(n, p)` in the stratum, at every `p`, rather
than at one pinned cell each. -/
theorem pow_dvd_signed_sum_runFreeTwo {n p : ℕ} (hp : p ∈ phiWindow n)
    (h : RunFreeTwo p (n % p)) (S : Finset ℕ) (hS : ∀ k ∈ S, k ∈ candidateM.window n)
    (ε : ℕ → ℤ) : (p : ℤ) ^ 2 ∣ ∑ k ∈ S, ε k * (cTerm n k : ℤ) :=
  pow_dvd_signed_sum hp
    (noShort_of_runFreeTwo (prime_of_mem_phiWindow hp).pos h) S hS ε

/-- The same, at φ̃ = 1. -/
theorem pow_dvd_signed_sum_runFreeOne {n p : ℕ} (hp : p ∈ phiWindow n)
    (h : RunFreeOne p (n % p)) (S : Finset ℕ) (hS : ∀ k ∈ S, k ∈ candidateM.window n)
    (ε : ℕ → ℤ) : (p : ℤ) ^ 1 ∣ ∑ k ∈ S, ε k * (cTerm n k : ℤ) :=
  pow_dvd_signed_sum hp
    (noShort_of_runFreeOne (prime_of_mem_phiWindow hp).pos h) S hS ε

/-! ## 5. Obligation (1) — the DROPPED INDEX on the five run-carrying strata

On a run-carrying stratum the short set is non-empty, and the cell's own words for what was
owed were: *"deriving the dropped index from the piece's own inequalities, which is a comparison
of residues rather than research"*.  Here it is, per STRATUM (the per-PIECE form is refuted —
`ptp_dropped_probe` arm N1).  Each φ̃ = 2 theorem states two things at once:

* the short set is EXACTLY the named triple intersection — `bitsR ≤ 1 ↔ three bits vanish`; and
* the dropped arc is DISJOINT from it, never partial: on the run the dropped bit is `1`.

The second half is what makes the first a SELECTION rather than a containment, and it is
`ptp_cong_probe` arm D4 (1322 of 1322) and `ptp_stratum_probe` D3a as a theorem. -/

/-- piece 1, stratum `[1/9, 2/17)`, φ̃ = 2 — **the dropped arc is `I3`**. -/
theorem dropped_S1b {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : p ≤ 9 * r) (hhi : 17 * r < 2 * p) :
    (bitsR p r u ≤ 1 ↔ (bit1 p r u = 0 ∧ bit2 p r u = 0 ∧ bit4 p r u = 0))
    ∧ (bit1 p r u = 0 → bit2 p r u = 0 → bit4 p r u = 0 → bit3 p r u = 1) := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 1) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 1) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 0) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 1) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 0) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 0) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> first | omega | simp

/-- piece 12, stratum `[6/13, 7/15)`, φ̃ = 2 — **the dropped arc is `I4`**. -/
theorem dropped_S12b {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : 6 * p ≤ 13 * r) (hhi : 15 * r < 7 * p) :
    (bitsR p r u ≤ 1 ↔ (bit1 p r u = 0 ∧ bit2 p r u = 0 ∧ bit3 p r u = 0))
    ∧ (bit1 p r u = 0 → bit2 p r u = 0 → bit3 p r u = 0 → bit4 p r u = 1) := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 6) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 4) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 2) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 5) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 1) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 0) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> first | omega | simp

/-- piece 15, stratum `[5/9, 9/16)`, φ̃ = 2 — **the dropped arc is `I3`**. -/
theorem dropped_S15b {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : 5 * p ≤ 9 * r) (hhi : 16 * r < 9 * p) :
    (bitsR p r u ≤ 1 ↔ (bit1 p r u = 0 ∧ bit2 p r u = 0 ∧ bit4 p r u = 0))
    ∧ (bit1 p r u = 0 → bit2 p r u = 0 → bit4 p r u = 0 → bit3 p r u = 1) := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 7) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 5) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 2) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 6) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 2) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 1) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> first | omega | simp

/-- piece 24, stratum `[12/13, 14/15)`, φ̃ = 2 — **the dropped arc is `I4`**. -/
theorem dropped_S24b {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : 12 * p ≤ 13 * r) (hhi : 15 * r < 14 * p) :
    (bitsR p r u ≤ 1 ↔ (bit1 p r u = 0 ∧ bit2 p r u = 0 ∧ bit3 p r u = 0))
    ∧ (bit1 p r u = 0 → bit2 p r u = 0 → bit3 p r u = 0 → bit4 p r u = 1) := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 12) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 8) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 4) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 10) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 3) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 1) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> first | omega | simp

/-- piece 6, stratum `[3/13, 4/17)`, the ONE run-carrying stratum with φ̃ = 1 — **`I1` is
REDUNDANT**.

At φ̃ = 1 the short set is the QUADRUPLE intersection by definition (`need = 5 − φ̃ = 4`), so
"which arc is dropped" is not the question this stratum answers, and
`ptp_stratum_probe`'s `dropped: none` means exactly that and no more.  What IS true here, and is
the same kind of reduction-to-three, is the OPPOSITE relation: `I1` contains the other three's
intersection, so the run is cut out by `I2 ∩ I3 ∩ I4` alone.  Measured at all 207 `(r, p)` of
the stratum (`ptp_cong_probe`'s stratum table, scratch `s6d.py`) and proved here.

The three negatives below say the other three arcs are NOT redundant, so this is a statement
about `I1` and not a vacuous one. -/
theorem redundant_S6d {p r u : ℕ} (hu : u < p) (hr : r < p)
    (hlo : 3 * p ≤ 13 * r) (hhi : 17 * r < 4 * p) :
    bitsR p r u = 0 ↔ (bit2 p r u = 0 ∧ bit3 p r u = 0 ∧ bit4 p r u = 0) := by
  have hp : 0 < p := by omega
  obtain ⟨A, hA, hA1, hA2⟩ := residue_spec (q := 3) (a := 13 * r) hp (by omega) (by omega)
  obtain ⟨B, hB, hB1, hB2⟩ := residue_spec (q := 2) (a := 9 * r) hp (by omega) (by omega)
  obtain ⟨C, hC, hC1, hC2⟩ := residue_spec (q := 1) (a := 5 * r) hp (by omega) (by omega)
  obtain ⟨E, hE, hE1, hE2⟩ := residue_spec (q := 2) (a := 11 * r) hp (by omega) (by omega)
  obtain ⟨D, hD, hD1, hD2⟩ := residue_spec (q := 0) (a := 4 * r) hp (by omega) (by omega)
  obtain ⟨F, hF, hF1, hF2⟩ := residue_spec (q := 0) (a := 2 * r) hp (by omega) (by omega)
  unfold bitsR
  rw [bit1_abstract hu hA hD, bit2_abstract hu hB hF, bit3_abstract hu hC,
    bit4_abstract hu hr hE]
  split_ifs <;> first | omega | simp

/-! ## 6. Non-vacuity, and the two negatives

A stratum theorem whose hypotheses no `(r, p)` meets proves nothing, and `omega` cannot tell the
difference.  The seven run-free witnesses are `Zeta2PtpStratum`'s own pinned cells; the five
run-carrying ones are small `(r, p)` in each stratum. -/

theorem witness_S1 : (0 : ℕ) < 11 ∧ 11 ≤ 11 * (1 % 11) ∧ 9 * (1 % 11) < 11 := by decide
theorem witness_S2 : (0 : ℕ) < 19 ∧ 19 ≤ 5 * (4 % 19) ∧ 9 * (4 % 19) < 2 * 19 := by decide
theorem witness_S3 : (0 : ℕ) < 31 ∧ 2 * 31 ≤ 9 * (7 % 31) ∧ 22 * (7 % 31) < 5 * 31 := by decide
theorem witness_S4 :
    (0 : ℕ) < 61 ∧ 5 * 61 ≤ 22 * (14 % 61) ∧ 13 * (14 % 61) < 3 * 61 := by decide
theorem witness_S5 :
    (0 : ℕ) < 37 ∧ 5 * 37 ≤ 11 * (17 % 37) ∧ 13 * (17 % 37) < 6 * 37 := by decide
theorem witness_S6 :
    (0 : ℕ) < 29 ∧ 6 * 29 ≤ 11 * (16 % 29) ∧ 9 * (16 % 29) < 5 * 29 := by decide
theorem witness_S7 :
    (0 : ℕ) < 37 ∧ 10 * 37 ≤ 11 * (34 % 37) ∧ 13 * (34 % 37) < 12 * 37 := by decide

theorem witness_S1b : (6 : ℕ) < 53 ∧ 53 ≤ 9 * 6 ∧ 17 * 6 < 2 * 53 := by decide
theorem witness_S6d : (3 : ℕ) < 13 ∧ 3 * 13 ≤ 13 * 3 ∧ 17 * 3 < 4 * 13 := by decide
theorem witness_S12b : (13 : ℕ) < 28 ∧ 6 * 28 ≤ 13 * 13 ∧ 15 * 13 < 7 * 28 := by decide
theorem witness_S15b : (14 : ℕ) < 25 ∧ 5 * 25 ≤ 9 * 14 ∧ 16 * 14 < 9 * 25 := by decide
theorem witness_S24b : (25 : ℕ) < 27 ∧ 12 * 27 ≤ 13 * 25 ∧ 15 * 25 < 14 * 27 := by decide

/-- **The run-carrying side really does carry a run.**  At `n = 3`, `p = 13` — the smallest
run-carrying cell, and `Zeta2PtpRun.run_at_3_13`'s own — `bitsR` reaches `0`, so
`redundant_S6d`'s left-hand side is satisfiable and the theorem is not about an empty set. -/
theorem run_nonempty_3_13 : bitsR 13 3 8 = 0 := by decide

/-- **And the run-free side really is run-free at the same spelling**: `bitsR` never falls below
`2` at `n = 1, p = 11`, which is `noShort_S1`'s own witness cell.  With the line above, `bitsR`
separates the two sides of the dichotomy. -/
theorem no_run_1_11 : ∀ u ∈ Finset.range 11, 2 ≤ bitsR 11 1 u := by decide

/-- **`I2` is NOT redundant on `[3/13, 4/17)`** — at `(p, r, u) = (13, 3, 7)` the other three
arcs contain `u` and `I2` does not. -/
theorem I2_not_redundant :
    bit1 13 3 7 = 0 ∧ bit3 13 3 7 = 0 ∧ bit4 13 3 7 = 0 ∧ bit2 13 3 7 = 1 := by decide

/-- **`I3` is NOT redundant on `[3/13, 4/17)`** — witness `(13, 3, 0)`. -/
theorem I3_not_redundant :
    bit1 13 3 0 = 0 ∧ bit2 13 3 0 = 0 ∧ bit4 13 3 0 = 0 ∧ bit3 13 3 0 = 1 := by decide

/-- **`I4` is NOT redundant on `[3/13, 4/17)`** — witness `(13, 3, 2)`. -/
theorem I4_not_redundant :
    bit1 13 3 2 = 0 ∧ bit2 13 3 2 = 0 ∧ bit3 13 3 2 = 0 ∧ bit4 13 3 2 = 1 := by decide

end Zeta2PtpCong

-- LEAN.md §1: `#print axioms` CANNOT see an undischarged hypothesis — a binder is not an axiom —
-- so acceptance is the receipt AND the printed TYPE, every binder read one by one.  Paired here
-- so the archive cannot carry one without the other.
#print axioms Zeta2PtpCong.carries_eq_bitsR
#check @Zeta2PtpCong.carries_eq_bitsR
#print axioms Zeta2PtpCong.mod_eq_sub
#check @Zeta2PtpCong.mod_eq_sub
#print axioms Zeta2PtpCong.residue_spec
#check @Zeta2PtpCong.residue_spec
#print axioms Zeta2PtpCong.add_mod_split
#check @Zeta2PtpCong.add_mod_split
#print axioms Zeta2PtpCong.bit4_abstract
#check @Zeta2PtpCong.bit4_abstract
#print axioms Zeta2PtpCong.noShort_S1
#check @Zeta2PtpCong.noShort_S1
#print axioms Zeta2PtpCong.noShort_S2
#check @Zeta2PtpCong.noShort_S2
#print axioms Zeta2PtpCong.noShort_S3
#check @Zeta2PtpCong.noShort_S3
#print axioms Zeta2PtpCong.noShort_S4
#check @Zeta2PtpCong.noShort_S4
#print axioms Zeta2PtpCong.noShort_S5
#check @Zeta2PtpCong.noShort_S5
#print axioms Zeta2PtpCong.noShort_S6
#check @Zeta2PtpCong.noShort_S6
#print axioms Zeta2PtpCong.noShort_S7
#check @Zeta2PtpCong.noShort_S7
#print axioms Zeta2PtpCong.pow_dvd_signed_sum_runFreeTwo
#check @Zeta2PtpCong.pow_dvd_signed_sum_runFreeTwo
#print axioms Zeta2PtpCong.pow_dvd_signed_sum_runFreeOne
#check @Zeta2PtpCong.pow_dvd_signed_sum_runFreeOne
#print axioms Zeta2PtpCong.dropped_S1b
#check @Zeta2PtpCong.dropped_S1b
#print axioms Zeta2PtpCong.dropped_S12b
#check @Zeta2PtpCong.dropped_S12b
#print axioms Zeta2PtpCong.dropped_S15b
#check @Zeta2PtpCong.dropped_S15b
#print axioms Zeta2PtpCong.dropped_S24b
#check @Zeta2PtpCong.dropped_S24b
#print axioms Zeta2PtpCong.redundant_S6d
#check @Zeta2PtpCong.redundant_S6d
#print axioms Zeta2PtpCong.run_nonempty_3_13
#check @Zeta2PtpCong.run_nonempty_3_13
#print axioms Zeta2PtpCong.no_run_1_11
#check @Zeta2PtpCong.no_run_1_11
#print axioms Zeta2PtpCong.I2_not_redundant
#check @Zeta2PtpCong.I2_not_redundant
