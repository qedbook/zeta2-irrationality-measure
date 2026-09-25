/-
THE CANDIDATE'S phi~ PROFILE, encoded — the data leg B's theorems are instantiated at.

Source: `extract_profile.py`, which pulls this table from the landed `z2a` engine and gates itself
on the archived density pin `dmax = 15.98087907`. Cross-checked back against that output by
`check_profile_encoding.py`, which parses THIS file and compares triple by triple — a data-entry
error here would otherwise be SILENT, since every theorem below would still compile.

Candidate: alpha = (13,11,9,15), beta = (0,2,4,26); gamma = (16,15);
Whipple hat = (20,5,7,9)/(3,0,18,20).

26 INTERVALS (not 52 — the source's "52 breakpoints" counts endpoints).

VINTAGE: toolchain leanprover/lean4:v4.34.0-rc2, mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace Zeta2Profile

/-- The candidate's `φ̃` table as `(a, b, v)` triples: `φ̃ = v` on `[a, b)`, and `0` elsewhere. -/
def candidateProfile : List (ℚ × ℚ × ℚ) :=
  [ (1/15,  1/13,  1), (1/11,  2/17,  2), (2/17,  1/7,   1), (1/7,   2/13,  2)
  , (2/13,  2/11,  1), (2/11,  1/5,   2), (1/5,   4/17,  1), (3/11,  4/13,  2)
  , (4/13,  4/11,  1), (4/11,  5/13,  2), (5/13,  2/5,   1), (3/7,   5/11,  1)
  , (5/11,  7/15,  2), (7/15,  8/17,  1), (8/15,  7/13,  1), (6/11,  9/16,  2)
  , (9/16,  8/13,  1), (7/11,  11/17, 2), (11/17, 9/13,  1), (5/7,   8/11,  1)
  , (8/11,  10/13, 2), (10/13, 4/5,   1), (9/11,  14/17, 2), (14/17, 10/11, 1)
  , (10/11, 14/15, 2), (14/15, 16/17, 1) ]

/-- The profile has 26 pieces. -/
theorem candidateProfile_length : candidateProfile.length = 26 := rfl

/-- **Every hypothesis leg B's lemmas assume, verified on the REAL table.**

`0 < a` is what `summable_density` and the `hka : 0 < k + a` side conditions need — and it is the
load-bearing one: a piece starting at `0` would make `hka` fail at `k = 0` and force a special
case in the block decomposition. `a < b ≤ 1` is `block_of_mem_interval`'s hypothesis, and
`b ≤ a + 1` follows from it but is stated because `summable_density` asks for it by name. -/
theorem candidateProfile_valid :
    ∀ t ∈ candidateProfile, 0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 ≤ 1 ∧ t.2.1 ≤ t.1 + 1 := by
  intro t ht
  fin_cases ht <;> norm_num

/-- The values are the profile's weights `vᵢ`, all positive. -/
theorem candidateProfile_values_pos : ∀ t ∈ candidateProfile, 0 < t.2.2 := by
  intro t ht
  fin_cases ht <;> norm_num

end Zeta2Profile
