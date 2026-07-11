import RGF.Generative.Locking.PentagonComplete
import RGF.Generative.Locking.PentagonNew
import RGF.Generative.Locking.RGFPentagonGolden
import RGF.Generative.Locking.RGFPentagonGoldenExt
import RGF.Generative.Locking.RGFPentagonGoldenExt2

/-! Unified deduplication acceptance audit file (Deduplication acceptance audit). -/

-- Check 1: axiom dependencies of the authoritative shared module itself
#print axioms RGF.PentagonComplete.cos_two_pi_div_five
#print axioms RGF.PentagonComplete.golden_sq_eq_golden_add_one
#print axioms RGF.PentagonComplete.golden_pow_succ
#print axioms RGF.PentagonComplete.psi_pow_succ
#print axioms RGF.PentagonNew.pentagon_new_identities

-- Check 6/7: submodule summary theorems and consistency
#print axioms RGFPentagonGolden.pentagon_locking_unification
#print axioms RGFPentagonGoldenExt.pentagon_golden_ext_complete
#print axioms RGFPentagonGoldenExt2.pentagon_golden_ext2_complete

-- Consistency: the values referenced by submodules equal the shared-module definitions (defeq check)
example : RGFPentagonGolden.alpha = Real.cos (2 * Real.pi / 5) := rfl
example : (Real.goldenConj) = RGF.PentagonComplete.psi := rfl
