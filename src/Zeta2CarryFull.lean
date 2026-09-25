/-
# PT-QA clump 1 — the residue bridge, and piece 1 proved at the FULL residue range

Row PT-QA of `docs/future/zeta2-lean-chain.md` (registry `2B0.AV`).  PT-Q1
(`Zeta2CarryP1.lean`, 2026-09-15) proved piece 1 under the prime BRACKET `13n < p ≤ 15n` and
shipped, as theorems, the measurement that the bracket is STRICTLY STRONGER than PT-QA's
dispatcher condition `{n/p} ∈ [1/15, 1/13)`: 97 of 11558 cells at `n ≤ 300` sit outside it,
exactly the cells with `p < n`, and on them PT-Q1's route does not reach
(`piece1_offbracket_route_fails`).  The row was then re-priced "on the number of `p < n`
sub-cases, not on 26".

**This file discharges that debt, and it turns out not to be a sub-case count at all.**

## The reframe, measured before it was proved

Write `r := n % p`.  Every residue appearing in `Zeta2Legendre.padicValNat_cTerm`'s four carry
bits is a residue of `r`, not of `n` — `(13n) % p = (13r) % p`, and with `t := k - 15n - 1` the
offsets are `(t + 2n) % p`, `(t + 4n) % p`, `(t + 6n) % p`.  And `Int.fract ((n:ℚ)/p) = r/p`, so
the dispatcher condition `1/15 ≤ {n/p} < 1/13` is *exactly* `13r < p ≤ 15r` — PT-Q1's own
bracket, at `r` instead of at `n`.  The `p < n` cells are the cells with `r < n`; the ONLY thing
the lap count `⌊n/p⌋` changes is that `t` then runs over all of `ℤ/p` rather than over `[0, 11n]`.

So the sub-case population was the wrong question, and `ptqa_scope_probe.py` measures why:

* the multi-lap population is present at **all 26 pieces**, from 0.82 % at piece 1 (PT-Q1's own
  number, the SMALLEST of the 26) to 21.4 % at piece 23 — a per-piece pricing anchored on
  piece 1 would have been wrong by a factor of 25;
* at every one of the 2711 multi-lap cells with `n ≤ 220`, the window's carry-min EQUALS the
  min over all of `ℤ/p`, and at every one of the 49601 one-lap cells it is `≥` it (0 violations
  either way) — so ONE statement, at the full residue range, covers both laps;
* and it gives nothing away: over every one-lap cell with `n < 200` the window min equals the
  full-residue min (`ptqa_cover_probe.py`, MEASURED NEGATIVE).

`ptqa_cover_probe.py` then prints, per piece, the minimal subset of the four bits that covers
`ℤ/p` at every admissible `(p, r)`.  For piece 1 it is `{bit1, bit4}`, and neither alone
suffices (that probe's ARM E1/E2, 106 `(p, r)` against each).  **That two-branch cover is this
file's proof**, and it is what PT-Q1's single-bit route could not be: `bit4` fires exactly when
`τ := (k - 15n - 1) % p` exceeds `11r`, and on the complement `τ ≤ 11r` unwraps `bit1`'s second
residue to `τ + 2r ≤ 13r < p`, whence `bit1`'s sum is `15r + τ ≥ p`.

## What this file does NOT claim

`Zeta2Target.zeta2_not_liouvilleWith` is `sorry` and stays `sorry`.  This is piece 1 of PT-QA's
profile, at full scope; the other pieces, the `phiSingle` definition and the ultrametric fold
over the window are not here.

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732 (current), buildbox.
-/
import Zeta2Defs
import Zeta2QnInt
import Zeta2Legendre
import Zeta2CarryP1
import Mathlib.Tactic.NormNum.Prime

namespace Zeta2Arith

open Zeta2Defs Nat

/-! ## The residue bridge — `n` under `% p` is `r = n % p`, and `{n/p}` is `r/p` -/

/-- `a * n % p = a * (n % p)` whenever the right-hand side is already below `p`.  This is the
step `omega` cannot take: with a VARIABLE modulus it models `a % p` as an unconstrained atom
(PT-Q1, `out_carryp1_modidiom.txt` ARM A). -/
theorem mul_mod_small (a n p : ℕ) (h : a * (n % p) < p) : a * n % p = a * (n % p) := by
  have e : a * (n % p) ≡ a * n [MOD p] := Nat.ModEq.mul_left a (Nat.mod_modEq n p)
  calc a * n % p = a * (n % p) % p := e.symm
    _ = a * (n % p) := Nat.mod_eq_of_lt h

/-- **The object PT-QA dispatches on, as a residue.**  `Int.fract ((n:ℚ)/p) = (n % p)/p`.
Every piece condition is therefore a pair of `ℕ` inequalities in `p` and `n % p`, which is what
makes the 26-piece dispatcher and the carry analysis speak the same language. -/
theorem fract_eq_mod_div (n p : ℕ) (hp : 0 < p) :
    Int.fract ((n : ℚ) / p) = ((n % p : ℕ) : ℚ) / p := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hpne : (p : ℚ) ≠ 0 := hpQ.ne'
  have hnat : (n / p) * p + n % p = n := Nat.div_add_mod' n p
  have hcast : (n : ℚ) = ((n / p : ℕ) : ℚ) * p + ((n % p : ℕ) : ℚ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℚ)) hnat.symm
  have hsplit : (n : ℚ) / p = ((n / p : ℕ) : ℚ) + ((n % p : ℕ) : ℚ) / p := by
    field_simp
    linarith [hcast]
  -- `Int.fract_natCast_add`, not `Int.fract_int_add`: the latter does not exist at this pin
  -- (measured, `out_carryfull_apidrift.txt`), and the ℕ form needs no `ℤ` round-trip.
  rw [hsplit, Int.fract_natCast_add]
  refine Int.fract_eq_self.2 ⟨by positivity, ?_⟩
  rw [div_lt_one hpQ]
  exact_mod_cast Nat.mod_lt n hp

/-- A piece's LEFT bound, as a residue inequality.  Stated with exactly the shape the caller
produces (LEAN.md §3): the consumer has `(c:ℚ)/d ≤ Int.fract ((n:ℚ)/p)` and wants `ℕ`. -/
theorem fract_ge_iff (n p c d : ℕ) (hp : 0 < p) (hd : 0 < d) :
    ((c : ℚ) / d ≤ Int.fract ((n : ℚ) / p)) ↔ c * p ≤ (n % p) * d := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [fract_eq_mod_div n p hp, le_div_iff₀ hpQ, div_mul_eq_mul_div, div_le_iff₀ hdQ]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- A piece's RIGHT bound, as a residue inequality. -/
theorem fract_lt_iff (n p c d : ℕ) (hp : 0 < p) (hd : 0 < d) :
    (Int.fract ((n : ℚ) / p) < (c : ℚ) / d) ↔ (n % p) * d < c * p := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [fract_eq_mod_div n p hp, div_lt_iff₀ hpQ, div_mul_eq_mul_div, lt_div_iff₀ hdQ]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-! ## Piece 1 at the full residue range — the two-branch cover -/

/-- **The fourth carry bit's residue identity.**  The window's two offsets sum to `11n`, so
their residues sum to `11r` modulo `p`; both being `< p`, the sum is either `11r` or `11r + p`,
and the bit fires exactly in the second case.  This is what replaces PT-Q1's "the window's right
edge makes the residue trivial", which is only available in the one-lap case. -/
theorem bit4_sum_mod (n p k : ℕ) (hk : k ∈ candidateM.window n) (h11 : 11 * (n % p) < p) :
    ((k - 15 * n - 1) % p + (26 * n + 1 - k) % p) % p = 11 * (n % p) := by
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  have hsum : (k - 15 * n - 1) + (26 * n + 1 - k) = 11 * n := by omega
  rw [← Nat.add_mod, hsum, mul_mod_small 11 n p h11]

/-- **PT-QA, piece 1, at the full residue range.**  The hypotheses are `13r < p ≤ 15r` for
`r = n % p` — PT-Q1's bracket with `n` replaced by the residue — so this covers the `p < n`
cells PT-Q1's route provably could not reach (`Zeta2CarryP1.piece1_offbracket_route_fails`).

The proof is the measured cover `{bit1, bit4}`: `rcases` on whether the fourth bit's residue sum
reaches `p`; if it does, that bit carries the term; if it does not, the sum is exactly `11r`, so
`τ ≤ 11r`, so `bit1`'s second residue unwraps to `τ + 2r ≤ 13r < p` and `bit1`'s sum is
`15r + τ ≥ 15r ≥ p`.  Neither branch is dispensable: `ptqa_cover_probe.py` ARM E1/E2 exhibit
106 `(p, r)` on which `bit1` alone fails to cover `ℤ/p`, and 106 on which `bit4` alone fails. -/
theorem carry_ge_piece1_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 13 * (n % p) < p) (h2 : p ≤ 15 * (n % p)) (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) := mul_mod_small 13 n p h1
  have h2n : 2 * n % p = 2 * (n % p) := mul_mod_small 2 n p (by omega)
  have hA := bit4_sum_mod n p k hk (by omega)
  -- `Nat.lt_or_ge`, not `le_or_lt`: the latter is not an identifier at this pin (measured).
  rcases Nat.lt_or_ge ((k - 15 * n - 1) % p + (26 * n + 1 - k) % p) p with hb4 | hb4
  · -- the fourth bit does not fire, so the residue sum is exactly `11r` and the FIRST bit carries
    have hAeq : (k - 15 * n - 1) % p + (26 * n + 1 - k) % p = 11 * (n % p) := by
      rw [← hA, Nat.mod_eq_of_lt hb4]
    have htau : (k - 15 * n - 1) % p ≤ 11 * (n % p) := by omega
    have hoff : (k - 13 * n - 1) % p = (k - 15 * n - 1) % p + 2 * (n % p) := by
      have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
      rw [e, Nat.add_mod, h2n, Nat.mod_eq_of_lt (by omega)]
    have hbit1 : p ≤ 13 * n % p + (k - 13 * n - 1) % p := by rw [h13, hoff]; omega
    split_ifs <;> omega
  · -- the window's own fourth bit carries the term
    split_ifs <;> omega

/-- The same, stated at the object PT-QA's dispatcher actually holds: `Int.fract ((n:ℚ)/p)`.
This is the interface PT-QB and the ultrametric fold consume. -/
theorem carry_ge_piece1_fract (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (hlo : (1 : ℚ) / 15 ≤ Int.fract ((n : ℚ) / p))
    (hhi : Int.fract ((n : ℚ) / p) < (1 : ℚ) / 13) (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hge : 1 * p ≤ (n % p) * 15 := by
    have := (fract_ge_iff n p 1 15 hp (by norm_num)).1 (by exact_mod_cast hlo)
    exact_mod_cast this
  have hlt : (n % p) * 13 < 1 * p := by
    have := (fract_lt_iff n p 1 13 hp (by norm_num)).1 (by exact_mod_cast hhi)
    exact_mod_cast this
  exact carry_ge_piece1_res n p k hk (by omega) (by omega) hp2

/-- The divisibility form, matching `Zeta2CarryP1.dvd_cTerm_piece1`'s shape. -/
theorem dvd_cTerm_piece1_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 13 * (n % p) < p) (h2 : p ≤ 15 * (n % p)) (hp2 : 26 * n + 1 < p ^ 2) :
    p ∣ cTerm n k := by
  by_contra hnd
  have h0 := padicValNat.eq_zero_of_not_dvd hnd
  have hge := carry_ge_piece1_res n p k hk h1 h2 hp2
  omega

/-! ## This SUBSUMES PT-Q1, executed rather than asserted (LEAN.md §3) -/

/-- PT-Q1's bracket implies this file's residue hypotheses, so `Zeta2CarryP1.carry_ge_piece1`
is the `r = n` instance.  `13n < p` forces `n < p`, hence `n % p = n`. -/
theorem res_of_bracket (n p : ℕ) (h1 : 13 * n < p) (h2 : p ≤ 15 * n) :
    13 * (n % p) < p ∧ p ≤ 15 * (n % p) := by
  have hnp : n % p = n := Nat.mod_eq_of_lt (by omega)
  rw [hnp]
  exact ⟨h1, h2⟩

/-- The composition EXECUTED: PT-Q1's conclusion, re-derived from this file's theorem. -/
theorem carry_ge_piece1_of_bracket (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 13 * n < p) (h2 : p ≤ 15 * n) (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) :=
  carry_ge_piece1_res n p k hk (res_of_bracket n p h1 h2).1 (res_of_bracket n p h1 h2).2 hp2

/-! ## The cell PT-Q1 could NOT reach, now discharged -/

/-- `(n, p) = (31, 29)` is the smallest cell inside `PhiT`'s own product with
`{n/p} ∈ [1/15, 1/13)` but `p ≤ 13n` (`Zeta2CarryP1.piece1_bracket_lt_interval`), and at
`k = 491` the first carry bit is `0` there, so PT-Q1's route fails
(`Zeta2CarryP1.piece1_offbracket_route_fails`).  Its residue hypotheses hold:
`31 % 29 = 2`, `13·2 = 26 < 29 ≤ 30 = 15·2`. -/
theorem piece1_offbracket_hypotheses :
    13 * (31 % 29) < 29 ∧ 29 ≤ 15 * (31 % 29) ∧ ¬ (13 * 31 < 29) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The debt discharged at the witness.**  The exact `k` at which PT-Q1's first bit is `0` is
nevertheless covered here — by `bit4`, which is the branch PT-Q1 had no access to. -/
theorem piece1_offbracket_now_covered : 1 ≤ padicValNat 29 (cTerm 31 491) := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact carry_ge_piece1_res 31 29 491
    ((mem_window_iff 31 491).2 ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (by norm_num)

/-- And it really is the FOURTH bit that carries there — the first is `0`, as PT-Q1 measured.
Stated so that a later edit collapsing the two branches into one would red. -/
theorem piece1_offbracket_bit4_is_the_one :
    ¬ (29 ≤ (13 * 31) % 29 + (491 - 13 * 31 - 1) % 29)
      ∧ 29 ≤ (491 - 15 * 31 - 1) % 29 + (26 * 31 + 1 - 491) % 29 := by
  refine ⟨by decide, by decide⟩

/-! ## Non-vacuity and edges (LEAN.md §5) -/

/-- A MULTI-LAP cell satisfying every hypothesis — `p < n`, which is the population this file
exists for.  `31 % 29 = 2 ≠ 31`, so this is not a one-lap cell in disguise. -/
theorem multilap_hypotheses_satisfiable :
    Nat.Prime 29 ∧ 29 < 31 ∧ 31 % 29 = 2 ∧ 13 * (31 % 29) < 29 ∧ 29 ≤ 15 * (31 % 29)
      ∧ 26 * 31 + 1 < 29 ^ 2 ∧ 491 ∈ candidateM.window 31 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  exact (mem_window_iff 31 491).2 ⟨by norm_num, by norm_num⟩

/-- The residue bridge at that cell, so the `ℚ` and `ℕ` sides are pinned against each other on
a real number and not only in general. -/
theorem fract_bridge_witness :
    Int.fract (((31 : ℕ) : ℚ) / ((29 : ℕ) : ℚ)) = ((31 % 29 : ℕ) : ℚ) / ((29 : ℕ) : ℚ) :=
  fract_eq_mod_div 31 29 (by norm_num)

/-- `r = 0` is EXCLUDED by the hypotheses rather than handled by them: `p ≤ 15·0` is false.
So `p ∣ n` never reaches this file's piece — that case has `{n/p} = 0` and `phiT 0 = 0`
(`Zeta2PhiT.phiT_zero`), which is why the profile asks nothing there. -/
theorem piece1_excludes_zero_residue (n p : ℕ) (h : n % p = 0) :
    ¬ (13 * (n % p) < p ∧ p ≤ 15 * (n % p)) := by
  rw [h]; omega

/-! ## PT-QA clump 2a — the 12 value-2 pieces, mechanical off the refine-probe table

Row PT-QA (`docs/future/zeta2-lean-chain.md`, registry `2B0.AV`), continuing clump 1's `Zeta2CarryFull.lean`.  Clump 1 proved piece 1 (`carry_ge_piece1_res`) and the residue bridge; the
41-piece work list is `ptqa_refine_probe.out`, one row per piece with its minimal bit-cover and
the seven floor constants `j = ⌊m·x⌋` that `(m·n) % p = m·r − j·p` needs.  This landing does the
12 VALUE-2 pieces first (riskiest — two carry bits rather than one — so if any piece resists the
template it is one of these); the 29 value-1 pieces are a follow-up clump, landed separately so a
red does not strand 40 pieces behind one submission.

**The three lemmas below GENERALISE clump 1's machinery from floor 0 to an arbitrary constant
floor `j`, and they are what let the remaining 40 pieces be mechanical rather than 40 fresh
arguments — they are stated once here and reused by every later clump on this row:**

* `mul_mod_floor` generalises `mul_mod_small` — at floor `j`, `a·n % p = a·(n%p) − j·p`.  Stated
  with `hhi : a*(n%p) < j*p + p` (EXPANDED, not `(j+1)*p`): `omega` cannot distribute a product of
  two VARIABLES (`j`,`p` are both variables here), so `(j+1)*p` and `j*p` are two unrelated atoms
  to it unless the caller already expanded — the expanded form pays that cost once, in the lemma,
  rather than at all 40 call sites (measured: the unexpanded form fails `omega` with a spurious
  "could not prove" naming atoms `↑j*↑p` and `↑(j+1)*↑p` that never get related).
* `add_mod_two` is new: two values each `< p`, their sum's `%p` is the sum itself or the sum minus
  one `p` — packaged with the ordering fact so a caller gets both from one `rcases`, never a
  second comparison.  This is `carry_ge_piece1_res`'s `rcases Nat.lt_or_ge (...) p` pattern,
  factored out because clump 2 needs it up to FOUR times per piece (once per bit) rather than
  once.
* `bit4_sum_mod_gen` generalises `bit4_sum_mod` to floor `j11`.

**Every one of the 12 pieces below is proved by the SAME uniform recipe, validated first on the
hardest case in the table (piece 2: `[1/11, 1/9)`, value 2, four-bit cover) before generating the
rest, and the same recipe is what the follow-up clump will run over the 29 value-1 pieces**:
establish the six floor-adjusted values (`13,9,5,2,4,6` — `11` is `bit4_sum_mod_gen`'s
own), rewrite each of `padicValNat_cTerm`'s four raw `%p` terms into `τ`-relative form via the
window arithmetic (`k − 13n − 1 = (k − 15n − 1) + 2n`, etc. — pure `omega` on the window bounds),
then a SINGLE sixteen-way case split (`add_mod_two` on each of the three shifted terms and on
`bit4`'s own pair) resolves every `%p` term to a concrete linear expression in `r := n % p`, `p`
and `τ`, and `split_ifs <;> omega` closes every leaf.  **The proof does not restrict itself to
each piece's MINIMAL cover from the table** — doing so would need a different, cover-shaped case
split per piece (a real per-piece design decision: which bits' resolution can be skipped because
the OTHER established bits already force the count).  The uniform four-bit form is correct
regardless of the minimal cover (more established bits cannot make the count smaller), and it is
what makes the remaining pieces mechanical: same generator, same shape, no piece-by-piece
judgment call.  The cost is verbosity (16 branches even where the table's cover is 2 bits) and
elaboration time (~10-30s per piece — some pieces need `set_option maxHeartbeats 2000000 in`
above the 200000 default, measured on 8 of these 12 in the first attempt) rather than
correctness.

**What this clump does NOT claim**: the `_fract` wrapper form (`Int.fract`-stated, matching
`carry_ge_piece1_fract`) is not built here — only the `_res` (residue-`ℕ`) form the table calls
the template.  The 29 value-1 pieces are NOT in this file yet (follow-up clump).  The ultrametric
fold over the window (`padicValRat.min_le_padicValRat_add`) that turns these per-piece lemmas
into PT-QA's actual target, `padicValInt_qnInt_ge_phi`, is NOT started.
`Zeta2Target.zeta2_not_liouvilleWith` stays `sorry`.
-/


/-- generalized `mul_mod_small`: with a constant floor `j`, `a * n % p = a * (n % p) - j * p`.
Stated with `hhi` in EXPANDED form (`j*p + p`, not `(j+1)*p`) so a caller's `omega` never needs
to distribute a product of two variables — see the header note above. -/
theorem mul_mod_floor (a n p j : ℕ) (hlo : j * p ≤ a * (n % p)) (hhi : a * (n % p) < j * p + p) :
    a * n % p = a * (n % p) - j * p := by
  have e : a * (n % p) ≡ a * n [MOD p] := Nat.ModEq.mul_left a (Nat.mod_modEq n p)
  have e2 : a * n % p = a * (n % p) % p := e.symm
  have hsmall : a * (n % p) - j * p < p := by omega
  have hx : a * (n % p) = (a * (n % p) - j * p) + j * p := (Nat.sub_add_cancel hlo).symm
  have step : a * (n % p) % p = a * (n % p) - j * p := by
    conv_lhs => rw [hx]
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hsmall
  rw [e2, step]

/-- Two values each `< p`: their sum's `%p` is either the sum itself (no wrap) or the sum minus
`p` (one wrap) — packaged with the ordering fact so a caller never needs a second comparison.
This is `carry_ge_piece1_res`'s `rcases Nat.lt_or_ge (...) p` pattern, factored out because clump
2 needs it up to four times per piece (once per bit) rather than once. -/
theorem add_mod_two (X V p : ℕ) (hX : X < p) (hV : V < p) :
    (X + V < p ∧ (X + V) % p = X + V) ∨ (p ≤ X + V ∧ (X + V) % p = X + V - p) := by
  rcases Nat.lt_or_ge (X + V) p with h | h
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · refine Or.inr ⟨h, ?_⟩
    have hx : X + V = (X + V - p) + p := by omega
    have hsmall : X + V - p < p := by omega
    conv_lhs => rw [hx]
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hsmall

/-- generalized `bit4_sum_mod`: with floor `j11`, the window's two offsets' residues sum to
`11*(n%p) - j11*p` modulo `p`. -/
theorem bit4_sum_mod_gen (n p k j11 : ℕ) (hk : k ∈ candidateM.window n)
    (hlo : j11 * p ≤ 11 * (n % p)) (hhi : 11 * (n % p) < j11 * p + p) :
    ((k - 15 * n - 1) % p + (26 * n + 1 - k) % p) % p = 11 * (n % p) - j11 * p := by
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  have hsum : (k - 15 * n - 1) + (26 * n + 1 - k) = 11 * n := by omega
  rw [← Nat.add_mod, hsum, mul_mod_floor 11 n p j11 hlo hhi]

-- PT-QA piece 2: [1/11, 1/9), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece2_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 1 * p ≤ (n % p) * 11) (h2 : (n % p) * 9 < 1 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 1 * p := by
    have := mul_mod_floor 13 n p 1 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 0 * p := by
    have := mul_mod_floor 9 n p 0 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 0 * p := by
    have := mul_mod_floor 5 n p 0 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 0 * p := by
    have := mul_mod_floor 4 n p 0 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 0 * p := by
    have := mul_mod_floor 6 n p 0 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 0 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 0 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 0 * p < p := by omega
  have h6nlt : 6 * (n % p) - 0 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 1 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 0 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 0 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece2_res

-- PT-QA piece 5: [1/7, 2/13), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece5_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 1 * p ≤ (n % p) * 7) (h2 : (n % p) * 13 < 2 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 1 * p := by
    have := mul_mod_floor 13 n p 1 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 1 * p := by
    have := mul_mod_floor 9 n p 1 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 0 * p := by
    have := mul_mod_floor 5 n p 0 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 0 * p := by
    have := mul_mod_floor 4 n p 0 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 0 * p := by
    have := mul_mod_floor 6 n p 0 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 0 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 0 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 0 * p < p := by omega
  have h6nlt : 6 * (n % p) - 0 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 1 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 0 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 0 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece5_res

-- PT-QA piece 8: [2/11, 1/5), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece8_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 2 * p ≤ (n % p) * 11) (h2 : (n % p) * 5 < 1 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 2 * p := by
    have := mul_mod_floor 13 n p 2 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 1 * p := by
    have := mul_mod_floor 9 n p 1 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 0 * p := by
    have := mul_mod_floor 5 n p 0 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 0 * p := by
    have := mul_mod_floor 4 n p 0 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 1 * p := by
    have := mul_mod_floor 6 n p 1 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 0 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 1 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 0 * p < p := by omega
  have h6nlt : 6 * (n % p) - 1 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 2 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 0 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 1 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece8_res

-- PT-QA piece 12: [3/11, 4/13), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece12_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 3 * p ≤ (n % p) * 11) (h2 : (n % p) * 13 < 4 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 3 * p := by
    have := mul_mod_floor 13 n p 3 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 2 * p := by
    have := mul_mod_floor 9 n p 2 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 1 * p := by
    have := mul_mod_floor 5 n p 1 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 1 * p := by
    have := mul_mod_floor 6 n p 1 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 1 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 1 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 3 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 1 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece12_res

-- PT-QA piece 15: [4/11, 5/13), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece15_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 4 * p ≤ (n % p) * 11) (h2 : (n % p) * 13 < 5 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 4 * p := by
    have := mul_mod_floor 13 n p 4 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 3 * p := by
    have := mul_mod_floor 9 n p 3 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 1 * p := by
    have := mul_mod_floor 5 n p 1 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 2 * p := by
    have := mul_mod_floor 6 n p 2 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 2 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 2 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 4 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 2 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece15_res

-- PT-QA piece 19: [5/11, 6/13), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece19_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 5 * p ≤ (n % p) * 11) (h2 : (n % p) * 13 < 6 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 5 * p := by
    have := mul_mod_floor 13 n p 5 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 4 * p := by
    have := mul_mod_floor 9 n p 4 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 2 * p := by
    have := mul_mod_floor 5 n p 2 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 2 * p := by
    have := mul_mod_floor 6 n p 2 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 2 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 2 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 5 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 2 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece19_res

-- PT-QA piece 23: [6/11, 5/9), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece23_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 6 * p ≤ (n % p) * 11) (h2 : (n % p) * 9 < 5 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 7 * p := by
    have := mul_mod_floor 13 n p 7 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 4 * p := by
    have := mul_mod_floor 9 n p 4 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 2 * p := by
    have := mul_mod_floor 5 n p 2 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 3 * p := by
    have := mul_mod_floor 6 n p 3 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 3 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 3 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 6 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 3 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece23_res

-- PT-QA piece 27: [7/11, 11/17), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece27_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 7 * p ≤ (n % p) * 11) (h2 : (n % p) * 17 < 11 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 8 * p := by
    have := mul_mod_floor 13 n p 8 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 5 * p := by
    have := mul_mod_floor 9 n p 5 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 3 * p := by
    have := mul_mod_floor 5 n p 3 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 3 * p := by
    have := mul_mod_floor 6 n p 3 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 3 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 3 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 7 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 3 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece27_res

-- PT-QA piece 31: [8/11, 3/4), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece31_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 8 * p ≤ (n % p) * 11) (h2 : (n % p) * 4 < 3 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 9 * p := by
    have := mul_mod_floor 13 n p 9 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 6 * p := by
    have := mul_mod_floor 9 n p 6 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 3 * p := by
    have := mul_mod_floor 5 n p 3 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 4 * p := by
    have := mul_mod_floor 6 n p 4 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 4 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 4 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 8 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 4 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece31_res

-- PT-QA piece 32: [3/4, 10/13), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece32_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 3 * p ≤ (n % p) * 4) (h2 : (n % p) * 13 < 10 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 9 * p := by
    have := mul_mod_floor 13 n p 9 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 6 * p := by
    have := mul_mod_floor 9 n p 6 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 3 * p := by
    have := mul_mod_floor 5 n p 3 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 4 * p := by
    have := mul_mod_floor 6 n p 4 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 4 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 4 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 8 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 4 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece32_res

-- PT-QA piece 35: [9/11, 14/17), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece35_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 9 * p ≤ (n % p) * 11) (h2 : (n % p) * 17 < 14 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 10 * p := by
    have := mul_mod_floor 13 n p 10 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 7 * p := by
    have := mul_mod_floor 9 n p 7 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 4 * p := by
    have := mul_mod_floor 5 n p 4 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 4 * p := by
    have := mul_mod_floor 6 n p 4 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 4 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 4 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 9 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 4 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece35_res

-- PT-QA piece 40: [10/11, 12/13), value 2. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece40_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 10 * p ≤ (n % p) * 11) (h2 : (n % p) * 13 < 12 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    2 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 11 * p := by
    have := mul_mod_floor 13 n p 11 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 8 * p := by
    have := mul_mod_floor 9 n p 8 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 4 * p := by
    have := mul_mod_floor 5 n p 4 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 5 * p := by
    have := mul_mod_floor 6 n p 5 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 5 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 5 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 10 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 5 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece40_res

-- PT-QA clump 2b: 14 of the 28 remaining value-1 pieces (batch A of two — the value-1 pieces
-- are lower risk than clump 2a's value-2 pieces, but landing all 28 in one submission would
-- strand the lot behind a single gate, so they land in two batches of 14). Same template,
-- same three helpers from clump 2a above; no new machinery.

-- PT-QA piece 3: [1/9, 2/17), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece3_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 1 * p ≤ (n % p) * 9) (h2 : (n % p) * 17 < 2 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 1 * p := by
    have := mul_mod_floor 13 n p 1 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 1 * p := by
    have := mul_mod_floor 9 n p 1 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 0 * p := by
    have := mul_mod_floor 5 n p 0 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 0 * p := by
    have := mul_mod_floor 4 n p 0 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 0 * p := by
    have := mul_mod_floor 6 n p 0 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 0 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 0 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 0 * p < p := by omega
  have h6nlt : 6 * (n % p) - 0 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 1 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 0 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 0 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece3_res

-- PT-QA piece 4: [2/17, 1/7), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece4_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 2 * p ≤ (n % p) * 17) (h2 : (n % p) * 7 < 1 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 1 * p := by
    have := mul_mod_floor 13 n p 1 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 1 * p := by
    have := mul_mod_floor 9 n p 1 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 0 * p := by
    have := mul_mod_floor 5 n p 0 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 0 * p := by
    have := mul_mod_floor 4 n p 0 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 0 * p := by
    have := mul_mod_floor 6 n p 0 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 0 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 0 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 0 * p < p := by omega
  have h6nlt : 6 * (n % p) - 0 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 1 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 0 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 0 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece4_res

-- PT-QA piece 6: [2/13, 1/6), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece6_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 2 * p ≤ (n % p) * 13) (h2 : (n % p) * 6 < 1 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 2 * p := by
    have := mul_mod_floor 13 n p 2 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 1 * p := by
    have := mul_mod_floor 9 n p 1 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 0 * p := by
    have := mul_mod_floor 5 n p 0 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 0 * p := by
    have := mul_mod_floor 4 n p 0 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 0 * p := by
    have := mul_mod_floor 6 n p 0 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 0 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 0 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 0 * p < p := by omega
  have h6nlt : 6 * (n % p) - 0 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 1 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 0 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 0 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece6_res

-- PT-QA piece 7: [1/6, 2/11), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece7_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 1 * p ≤ (n % p) * 6) (h2 : (n % p) * 11 < 2 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 2 * p := by
    have := mul_mod_floor 13 n p 2 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 1 * p := by
    have := mul_mod_floor 9 n p 1 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 0 * p := by
    have := mul_mod_floor 5 n p 0 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 0 * p := by
    have := mul_mod_floor 4 n p 0 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 1 * p := by
    have := mul_mod_floor 6 n p 1 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 0 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 1 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 0 * p < p := by omega
  have h6nlt : 6 * (n % p) - 1 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 1 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 0 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 1 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece7_res

-- PT-QA piece 9: [1/5, 2/9), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece9_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 1 * p ≤ (n % p) * 5) (h2 : (n % p) * 9 < 2 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 2 * p := by
    have := mul_mod_floor 13 n p 2 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 1 * p := by
    have := mul_mod_floor 9 n p 1 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 1 * p := by
    have := mul_mod_floor 5 n p 1 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 0 * p := by
    have := mul_mod_floor 4 n p 0 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 1 * p := by
    have := mul_mod_floor 6 n p 1 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 0 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 1 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 0 * p < p := by omega
  have h6nlt : 6 * (n % p) - 1 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 2 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 0 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 1 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece9_res

-- PT-QA piece 10: [2/9, 3/13), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece10_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 2 * p ≤ (n % p) * 9) (h2 : (n % p) * 13 < 3 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 2 * p := by
    have := mul_mod_floor 13 n p 2 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 2 * p := by
    have := mul_mod_floor 9 n p 2 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 1 * p := by
    have := mul_mod_floor 5 n p 1 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 0 * p := by
    have := mul_mod_floor 4 n p 0 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 1 * p := by
    have := mul_mod_floor 6 n p 1 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 0 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 1 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 0 * p < p := by omega
  have h6nlt : 6 * (n % p) - 1 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 2 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 0 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 1 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece10_res

-- PT-QA piece 13: [4/13, 1/3), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece13_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 4 * p ≤ (n % p) * 13) (h2 : (n % p) * 3 < 1 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 4 * p := by
    have := mul_mod_floor 13 n p 4 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 2 * p := by
    have := mul_mod_floor 9 n p 2 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 1 * p := by
    have := mul_mod_floor 5 n p 1 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 1 * p := by
    have := mul_mod_floor 6 n p 1 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 1 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 1 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 3 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 1 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece13_res

-- PT-QA piece 14: [1/3, 4/11), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece14_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 1 * p ≤ (n % p) * 3) (h2 : (n % p) * 11 < 4 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 4 * p := by
    have := mul_mod_floor 13 n p 4 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 3 * p := by
    have := mul_mod_floor 9 n p 3 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 1 * p := by
    have := mul_mod_floor 5 n p 1 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 2 * p := by
    have := mul_mod_floor 6 n p 2 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 2 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 2 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 3 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 2 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece14_res

-- PT-QA piece 16: [5/13, 2/5), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece16_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 5 * p ≤ (n % p) * 13) (h2 : (n % p) * 5 < 2 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 5 * p := by
    have := mul_mod_floor 13 n p 5 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 3 * p := by
    have := mul_mod_floor 9 n p 3 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 1 * p := by
    have := mul_mod_floor 5 n p 1 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 2 * p := by
    have := mul_mod_floor 6 n p 2 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 2 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 2 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 4 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 2 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece16_res

-- PT-QA piece 17: [3/7, 4/9), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece17_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 3 * p ≤ (n % p) * 7) (h2 : (n % p) * 9 < 4 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 5 * p := by
    have := mul_mod_floor 13 n p 5 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 3 * p := by
    have := mul_mod_floor 9 n p 3 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 2 * p := by
    have := mul_mod_floor 5 n p 2 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 2 * p := by
    have := mul_mod_floor 6 n p 2 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 2 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 2 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 4 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 2 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece17_res

-- PT-QA piece 18: [4/9, 5/11), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece18_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 4 * p ≤ (n % p) * 9) (h2 : (n % p) * 11 < 5 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 5 * p := by
    have := mul_mod_floor 13 n p 5 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 4 * p := by
    have := mul_mod_floor 9 n p 4 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 2 * p := by
    have := mul_mod_floor 5 n p 2 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 2 * p := by
    have := mul_mod_floor 6 n p 2 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 2 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 2 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 4 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 2 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece18_res

-- PT-QA piece 20: [6/13, 7/15), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece20_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 6 * p ≤ (n % p) * 13) (h2 : (n % p) * 15 < 7 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 6 * p := by
    have := mul_mod_floor 13 n p 6 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 4 * p := by
    have := mul_mod_floor 9 n p 4 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 2 * p := by
    have := mul_mod_floor 5 n p 2 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 2 * p := by
    have := mul_mod_floor 6 n p 2 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 2 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 2 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 5 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 2 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece20_res

-- PT-QA piece 21: [7/15, 8/17), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece21_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 7 * p ≤ (n % p) * 15) (h2 : (n % p) * 17 < 8 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 6 * p := by
    have := mul_mod_floor 13 n p 6 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 4 * p := by
    have := mul_mod_floor 9 n p 4 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 2 * p := by
    have := mul_mod_floor 5 n p 2 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 0 * p := by
    have := mul_mod_floor 2 n p 0 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 1 * p := by
    have := mul_mod_floor 4 n p 1 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 2 * p := by
    have := mul_mod_floor 6 n p 2 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 0 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 1 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 2 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 0 * p < p := by omega
  have h4nlt : 4 * (n % p) - 1 * p < p := by omega
  have h6nlt : 6 * (n % p) - 2 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 5 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 0 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 1 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 2 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece21_res

-- PT-QA piece 22: [8/15, 7/13), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece22_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 8 * p ≤ (n % p) * 15) (h2 : (n % p) * 13 < 7 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 6 * p := by
    have := mul_mod_floor 13 n p 6 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 4 * p := by
    have := mul_mod_floor 9 n p 4 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 2 * p := by
    have := mul_mod_floor 5 n p 2 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 3 * p := by
    have := mul_mod_floor 6 n p 3 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 3 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 3 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 5 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 3 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece22_res

-- PT-QA clump 2c: the last 14 of the 28 value-1 pieces (batch B). Same template, same
-- three helpers from clump 2a; no new machinery. This completes all 41 pieces of the
-- refine-probe table (piece 1 in clump 1, the other 40 across clumps 2a/2b/2c).

-- PT-QA piece 24: [5/9, 9/16), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece24_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 5 * p ≤ (n % p) * 9) (h2 : (n % p) * 16 < 9 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 7 * p := by
    have := mul_mod_floor 13 n p 7 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 5 * p := by
    have := mul_mod_floor 9 n p 5 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 2 * p := by
    have := mul_mod_floor 5 n p 2 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 3 * p := by
    have := mul_mod_floor 6 n p 3 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 3 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 3 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 6 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 3 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece24_res

-- PT-QA piece 25: [9/16, 3/5), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece25_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 9 * p ≤ (n % p) * 16) (h2 : (n % p) * 5 < 3 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 7 * p := by
    have := mul_mod_floor 13 n p 7 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 5 * p := by
    have := mul_mod_floor 9 n p 5 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 2 * p := by
    have := mul_mod_floor 5 n p 2 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 3 * p := by
    have := mul_mod_floor 6 n p 3 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 3 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 3 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 6 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 3 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece25_res

-- PT-QA piece 26: [3/5, 8/13), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece26_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 3 * p ≤ (n % p) * 5) (h2 : (n % p) * 13 < 8 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 7 * p := by
    have := mul_mod_floor 13 n p 7 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 5 * p := by
    have := mul_mod_floor 9 n p 5 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 3 * p := by
    have := mul_mod_floor 5 n p 3 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 3 * p := by
    have := mul_mod_floor 6 n p 3 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 3 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 3 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 6 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 3 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece26_res

-- PT-QA piece 28: [11/17, 2/3), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece28_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 11 * p ≤ (n % p) * 17) (h2 : (n % p) * 3 < 2 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 8 * p := by
    have := mul_mod_floor 13 n p 8 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 5 * p := by
    have := mul_mod_floor 9 n p 5 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 3 * p := by
    have := mul_mod_floor 5 n p 3 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 3 * p := by
    have := mul_mod_floor 6 n p 3 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 3 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 3 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 7 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 3 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece28_res

-- PT-QA piece 29: [2/3, 9/13), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece29_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 2 * p ≤ (n % p) * 3) (h2 : (n % p) * 13 < 9 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 8 * p := by
    have := mul_mod_floor 13 n p 8 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 6 * p := by
    have := mul_mod_floor 9 n p 6 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 3 * p := by
    have := mul_mod_floor 5 n p 3 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 4 * p := by
    have := mul_mod_floor 6 n p 4 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 4 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 4 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 7 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 4 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece29_res

-- PT-QA piece 30: [5/7, 8/11), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece30_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 5 * p ≤ (n % p) * 7) (h2 : (n % p) * 11 < 8 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 9 * p := by
    have := mul_mod_floor 13 n p 9 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 6 * p := by
    have := mul_mod_floor 9 n p 6 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 3 * p := by
    have := mul_mod_floor 5 n p 3 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 2 * p := by
    have := mul_mod_floor 4 n p 2 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 4 * p := by
    have := mul_mod_floor 6 n p 4 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 2 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 4 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 2 * p < p := by omega
  have h6nlt : 6 * (n % p) - 4 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 7 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 2 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 4 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece30_res

-- PT-QA piece 33: [10/13, 7/9), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece33_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 10 * p ≤ (n % p) * 13) (h2 : (n % p) * 9 < 7 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 10 * p := by
    have := mul_mod_floor 13 n p 10 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 6 * p := by
    have := mul_mod_floor 9 n p 6 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 3 * p := by
    have := mul_mod_floor 5 n p 3 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 4 * p := by
    have := mul_mod_floor 6 n p 4 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 4 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 4 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 8 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 4 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece33_res

-- PT-QA piece 34: [7/9, 4/5), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece34_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 7 * p ≤ (n % p) * 9) (h2 : (n % p) * 5 < 4 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 10 * p := by
    have := mul_mod_floor 13 n p 10 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 7 * p := by
    have := mul_mod_floor 9 n p 7 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 3 * p := by
    have := mul_mod_floor 5 n p 3 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 4 * p := by
    have := mul_mod_floor 6 n p 4 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 4 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 4 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 8 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 4 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece34_res

-- PT-QA piece 36: [14/17, 5/6), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece36_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 14 * p ≤ (n % p) * 17) (h2 : (n % p) * 6 < 5 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 10 * p := by
    have := mul_mod_floor 13 n p 10 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 7 * p := by
    have := mul_mod_floor 9 n p 7 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 4 * p := by
    have := mul_mod_floor 5 n p 4 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 4 * p := by
    have := mul_mod_floor 6 n p 4 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 4 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 4 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 9 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 4 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece36_res

-- PT-QA piece 37: [5/6, 11/13), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece37_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 5 * p ≤ (n % p) * 6) (h2 : (n % p) * 13 < 11 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 10 * p := by
    have := mul_mod_floor 13 n p 10 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 7 * p := by
    have := mul_mod_floor 9 n p 7 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 4 * p := by
    have := mul_mod_floor 5 n p 4 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 5 * p := by
    have := mul_mod_floor 6 n p 5 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 5 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 5 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 9 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 5 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece37_res

-- PT-QA piece 38: [11/13, 8/9), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece38_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 11 * p ≤ (n % p) * 13) (h2 : (n % p) * 9 < 8 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 11 * p := by
    have := mul_mod_floor 13 n p 11 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 7 * p := by
    have := mul_mod_floor 9 n p 7 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 4 * p := by
    have := mul_mod_floor 5 n p 4 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 5 * p := by
    have := mul_mod_floor 6 n p 5 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 5 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 5 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 9 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 5 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece38_res

-- PT-QA piece 39: [8/9, 10/11), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece39_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 8 * p ≤ (n % p) * 9) (h2 : (n % p) * 11 < 10 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 11 * p := by
    have := mul_mod_floor 13 n p 11 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 8 * p := by
    have := mul_mod_floor 9 n p 8 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 4 * p := by
    have := mul_mod_floor 5 n p 4 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 5 * p := by
    have := mul_mod_floor 6 n p 5 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 5 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 5 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 9 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 5 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece39_res

-- PT-QA piece 41: [12/13, 14/15), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece41_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 12 * p ≤ (n % p) * 13) (h2 : (n % p) * 15 < 14 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 12 * p := by
    have := mul_mod_floor 13 n p 12 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 8 * p := by
    have := mul_mod_floor 9 n p 8 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 4 * p := by
    have := mul_mod_floor 5 n p 4 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 5 * p := by
    have := mul_mod_floor 6 n p 5 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 5 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 5 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 10 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 5 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece41_res

-- PT-QA piece 42: [14/15, 16/17), value 1. Uniform full-4-bit cover
-- (cover-minimal proof not attempted; this is a correct, if non-minimal, closing).
set_option maxHeartbeats 2000000 in
theorem carry_ge_piece42_res (n p k : ℕ) [Fact p.Prime] (hk : k ∈ candidateM.window n)
    (h1 : 14 * p ≤ (n % p) * 15) (h2 : (n % p) * 17 < 16 * p)
    (hp2 : 26 * n + 1 < p ^ 2) :
    1 ≤ padicValNat p (cTerm n k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨w1, w2⟩ := (mem_window_iff n k).1 hk
  rw [padicValNat_cTerm p n k hk hp2]
  have h13 : 13 * n % p = 13 * (n % p) - 12 * p := by
    have := mul_mod_floor 13 n p 12 (by omega) (by omega); simpa using this
  have h9 : 9 * n % p = 9 * (n % p) - 8 * p := by
    have := mul_mod_floor 9 n p 8 (by omega) (by omega); simpa using this
  have h5 : 5 * n % p = 5 * (n % p) - 4 * p := by
    have := mul_mod_floor 5 n p 4 (by omega) (by omega); simpa using this
  have h2n : 2 * n % p = 2 * (n % p) - 1 * p := by
    have := mul_mod_floor 2 n p 1 (by omega) (by omega); simpa using this
  have h4n : 4 * n % p = 4 * (n % p) - 3 * p := by
    have := mul_mod_floor 4 n p 3 (by omega) (by omega); simpa using this
  have h6n : 6 * n % p = 6 * (n % p) - 5 * p := by
    have := mul_mod_floor 6 n p 5 (by omega) (by omega); simpa using this
  have hta : (k - 15 * n - 1) % p < p := Nat.mod_lt _ hp
  set τ := (k - 15 * n - 1) % p with hτdef
  have hoff1 : (k - 13 * n - 1) % p = (τ + (2 * (n % p) - 1 * p)) % p := by
    have e : k - 13 * n - 1 = (k - 15 * n - 1) + 2 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h2n]
  have hoff2 : (k - 11 * n - 1) % p = (τ + (4 * (n % p) - 3 * p)) % p := by
    have e : k - 11 * n - 1 = (k - 15 * n - 1) + 4 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h4n]
  have hoff3 : (k - 9 * n - 1) % p = (τ + (6 * (n % p) - 5 * p)) % p := by
    have e : k - 9 * n - 1 = (k - 15 * n - 1) + 6 * n := by omega
    rw [e, Nat.add_mod, ← hτdef, h6n]
  have h2nlt : 2 * (n % p) - 1 * p < p := by omega
  have h4nlt : 4 * (n % p) - 3 * p < p := by omega
  have h6nlt : 6 * (n % p) - 5 * p < p := by omega
  have hvlt : (26 * n + 1 - k) % p < p := Nat.mod_lt _ hp
  have hb4 := bit4_sum_mod_gen n p k 10 hk (by omega) (by omega)
  rw [← hτdef] at hb4
  rcases add_mod_two τ (2 * (n % p) - 1 * p) p hta h2nlt with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
  rcases add_mod_two τ (4 * (n % p) - 3 * p) p hta h4nlt with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
  rcases add_mod_two τ (6 * (n % p) - 5 * p) p hta h6nlt with ⟨c3, e3⟩ | ⟨c3, e3⟩ <;>
  rcases add_mod_two τ ((26 * n + 1 - k) % p) p hta hvlt with ⟨c4, e4⟩ | ⟨c4, e4⟩ <;>
  (rw [hoff1, hoff2, hoff3, h13, h9, h5, e1, e2, e3]
   rw [e4] at hb4
   split_ifs <;> omega)

#print axioms Zeta2Arith.carry_ge_piece42_res

end Zeta2Arith

#print axioms Zeta2Arith.mul_mod_small
#print axioms Zeta2Arith.fract_eq_mod_div
#print axioms Zeta2Arith.fract_ge_iff
#print axioms Zeta2Arith.fract_lt_iff
#print axioms Zeta2Arith.bit4_sum_mod
#print axioms Zeta2Arith.carry_ge_piece1_res
#print axioms Zeta2Arith.carry_ge_piece1_fract
#print axioms Zeta2Arith.dvd_cTerm_piece1_res
#print axioms Zeta2Arith.res_of_bracket
#print axioms Zeta2Arith.carry_ge_piece1_of_bracket
#print axioms Zeta2Arith.piece1_offbracket_hypotheses
#print axioms Zeta2Arith.piece1_offbracket_now_covered
#print axioms Zeta2Arith.piece1_offbracket_bit4_is_the_one
#print axioms Zeta2Arith.multilap_hypotheses_satisfiable
#print axioms Zeta2Arith.fract_bridge_witness
#print axioms Zeta2Arith.piece1_excludes_zero_residue
#print axioms Zeta2Arith.mul_mod_floor
#print axioms Zeta2Arith.add_mod_two
#print axioms Zeta2Arith.bit4_sum_mod_gen
#print axioms Zeta2Arith.carry_ge_piece2_res
#print axioms Zeta2Arith.carry_ge_piece5_res
#print axioms Zeta2Arith.carry_ge_piece8_res
#print axioms Zeta2Arith.carry_ge_piece12_res
#print axioms Zeta2Arith.carry_ge_piece15_res
#print axioms Zeta2Arith.carry_ge_piece19_res
#print axioms Zeta2Arith.carry_ge_piece23_res
#print axioms Zeta2Arith.carry_ge_piece27_res
#print axioms Zeta2Arith.carry_ge_piece31_res
#print axioms Zeta2Arith.carry_ge_piece32_res
#print axioms Zeta2Arith.carry_ge_piece35_res
#print axioms Zeta2Arith.carry_ge_piece40_res
#print axioms Zeta2Arith.carry_ge_piece3_res
#print axioms Zeta2Arith.carry_ge_piece4_res
#print axioms Zeta2Arith.carry_ge_piece6_res
#print axioms Zeta2Arith.carry_ge_piece7_res
#print axioms Zeta2Arith.carry_ge_piece9_res
#print axioms Zeta2Arith.carry_ge_piece10_res
#print axioms Zeta2Arith.carry_ge_piece13_res
#print axioms Zeta2Arith.carry_ge_piece14_res
#print axioms Zeta2Arith.carry_ge_piece16_res
#print axioms Zeta2Arith.carry_ge_piece17_res
#print axioms Zeta2Arith.carry_ge_piece18_res
#print axioms Zeta2Arith.carry_ge_piece20_res
#print axioms Zeta2Arith.carry_ge_piece21_res
#print axioms Zeta2Arith.carry_ge_piece22_res
#print axioms Zeta2Arith.carry_ge_piece24_res
#print axioms Zeta2Arith.carry_ge_piece25_res
#print axioms Zeta2Arith.carry_ge_piece26_res
#print axioms Zeta2Arith.carry_ge_piece28_res
#print axioms Zeta2Arith.carry_ge_piece29_res
#print axioms Zeta2Arith.carry_ge_piece30_res
#print axioms Zeta2Arith.carry_ge_piece33_res
#print axioms Zeta2Arith.carry_ge_piece34_res
#print axioms Zeta2Arith.carry_ge_piece36_res
#print axioms Zeta2Arith.carry_ge_piece37_res
#print axioms Zeta2Arith.carry_ge_piece38_res
#print axioms Zeta2Arith.carry_ge_piece39_res
#print axioms Zeta2Arith.carry_ge_piece41_res
#print axioms Zeta2Arith.carry_ge_piece42_res
