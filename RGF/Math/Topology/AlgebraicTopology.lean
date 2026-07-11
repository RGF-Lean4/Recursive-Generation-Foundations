/-
  Modern/AlgebraicTopology.lean

  **Algebraic topology over the RGF reals.**

  Using the metric/topology instances from `Modern.RealInstances`, the RGF real
  line is homeomorphic to `ℝ`.  We transport homotopy-theoretic structure across
  this homeomorphism to obtain genuine algebraic-topology statements about the
  RGF real line:

  * `RGFReal'` is **contractible** (it deformation-retracts to a point);
  * hence it is **path-connected** and **simply connected** (its fundamental
    group is trivial).

  This addresses the criticism that algebraic topology was untouched.
-/
import Mathlib
import RGF.Math.Real.RealInstances

namespace RGF
namespace RGFReal'

/-- The RGF real line is homeomorphic to the standard real line. -/
noncomputable def homeomorphReal : RGFReal' ≃ₜ ℝ := isometryEquivReal.toHomeomorph

/-
**The RGF real line is contractible.**
-/
instance rgf_contractible : ContractibleSpace RGFReal' :=
  Homeomorph.contractibleSpace homeomorphReal

/-- The RGF real line is path-connected. -/
instance rgf_pathConnected : PathConnectedSpace RGFReal' := inferInstance

/-- **The RGF real line is simply connected**: its fundamental group is trivial. -/
instance rgf_simplyConnected : SimplyConnectedSpace RGFReal' := inferInstance

end RGFReal'
end RGF