/-
# Receipts — the whole claim, checked in one place

`lake build` elaborates every module below `Zeta2Target`; this file then asks the kernel what
each headline theorem depends on and prints its type. Acceptance (both channels, neither alone):
every `#print axioms` line reads exactly `[propext, Classical.choice, Quot.sound]`, and every
`#check` type names NO hypothesis.
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
#print axioms Zeta2Final.zeta2_eq_riemannZeta_two
#check @Zeta2Final.zeta2_eq_riemannZeta_two
#print axioms Zeta2Final.zeta2_eq_tsum_from_one
#check @Zeta2Final.zeta2_eq_tsum_from_one
#print Zeta2Defs.zeta2
#print LiouvilleWith
