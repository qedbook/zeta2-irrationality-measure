/-
# Receipts — the axioms and the statement of each theorem claimed

`lake build` elaborates every module below `Zeta2Target`. This file then asks Lean, for each theorem
below, which axioms it depends on (`#print axioms`) and what it states (`#check`), and prints the
definitions of `Zeta2Defs.zeta2` and `LiouvilleWith`.

`scripts/check_receipts.py` accepts the output only when every `#print axioms` line reads exactly
`[propext, Classical.choice, Quot.sound]` and the type of every theorem below is printed. It does
not judge the types: each `#check` line prints the theorem's statement so that a reader can see that
it is the statement claimed, with no premise added. A premise would not show in the axioms line,
since a theorem that takes what it needs as a hypothesis depends on the same axioms.
`Zeta2Hpsi.hψ`'s statement prints as the name of a definition, `Zeta2LegA.psiErrorBoundStatement`,
which this file does not print; it is in src/Zeta2LegA.lean.
-/
import Zeta2Target

#print axioms Zeta2Target.zeta2_not_liouvilleWith
#check @Zeta2Target.zeta2_not_liouvilleWith
#print axioms Zeta2Target.zeta2_irrationality_measure_le
#check @Zeta2Target.zeta2_irrationality_measure_le
#print axioms Zeta2Unconditional.zeta2_rational_approximation
#check @Zeta2Unconditional.zeta2_rational_approximation
#print axioms Zeta2Hpsi.hψ
#check @Zeta2Hpsi.hψ
#print axioms MediumPNT
#check @MediumPNT
#print axioms Zeta2Final.zeta2_eq_riemannZeta_two
#check @Zeta2Final.zeta2_eq_riemannZeta_two
#print axioms Zeta2Final.zeta2_eq_tsum_from_one
#check @Zeta2Final.zeta2_eq_tsum_from_one
#print Zeta2Defs.zeta2
#print LiouvilleWith
