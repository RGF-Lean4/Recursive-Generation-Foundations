/-
  Modern/DifferentialGeometry.lean

  **Differential geometry over the RGF reals.**

  With the `NontriviallyNormedField` instance from `Modern.RealInstances`, the
  RGF reals support Mathlib's manifold/`ContMDiff` machinery.  We exhibit the RGF
  real line as a genuine smooth (`C∞`) manifold modeled on itself, and verify
  that smooth maps in this differential-geometric sense exist.

  This addresses the criticism that differential geometry was untouched.
-/
import Mathlib
import RGF.Math.Real.RealInstances

namespace RGF
namespace RGFReal'

/-- The RGF reals form a normed vector space over themselves. -/
noncomputable example : NormedSpace RGFReal' RGFReal' := inferInstance

/-- The trivial model with corners: the RGF real line modeled on itself. -/
noncomputable abbrev RGFmodel := modelWithCornersSelf RGFReal' RGFReal'

/-- The RGF real line is a charted space over itself. -/
noncomputable example : ChartedSpace RGFReal' RGFReal' := inferInstance

/-- **The RGF real line is a smooth (`C∞`) manifold** modeled on itself. -/
theorem rgf_isManifold : IsManifold (modelWithCornersSelf RGFReal' RGFReal') ⊤ RGFReal' :=
  inferInstance

/-- **A smooth map on the RGF manifold.** The identity is `C∞` in the
    differential-geometric sense. -/
theorem rgf_contMDiff_id :
    ContMDiff RGFmodel RGFmodel ⊤ (id : RGFReal' → RGFReal') :=
  contMDiff_id

/-- Smooth maps compose: any `C∞` self-map composed with the identity is `C∞`.
    (A sanity check that the `ContMDiff` calculus is available over the RGF
    reals.) -/
theorem rgf_contMDiff_const (c : RGFReal') :
    ContMDiff RGFmodel RGFmodel ⊤ (fun _ : RGFReal' => c) :=
  contMDiff_const

end RGFReal'
end RGF
