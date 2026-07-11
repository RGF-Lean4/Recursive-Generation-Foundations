/-
  Modern/Coverage.lean

  **Capstone: modern-mathematics coverage of the RGF reals.**

  This module is the single entry point for the `Modern` layer.  It imports every
  branch file and re-exports the headline theorems, giving a one-glance audit that
  the self-built RGF reals (`RGFReal'`) genuinely carry the core branches of
  modern mathematics — not merely an injective homomorphism into `ℝ`, but the full
  ordered-field / normed / complete / measurable / manifold structure, on top of
  which Mathlib's modern machinery runs directly.

  The point being made is structural.  The foundations build a *bijective ordered
  ring isomorphism* `RGFReal' ≃+*o ℝ` entirely from the RGF construction.  Once
  that isomorphism is upgraded to the standard analytic instance stack
  (`Modern.RealInstances`), every theorem Mathlib proves about `ℝ`, and every
  structure it builds over `ℝ`, transports to `RGFReal'`.  The branch files below
  exhibit concrete, fully-proved witnesses in each area:

  | Branch                  | Witness over `RGFReal'`                                   |
  |-------------------------|----------------------------------------------------------|
  | Foundations / analysis  | complete ordered field, normed field, Archimedean        |
  | Functional analysis     | `ℓ²(RGFReal')` infinite-dim Banach space; Banach fixpoint |
  | Measure & integration   | Lebesgue measure `rgfVolume`; Bochner integral on `[0,1]` |
  | Differential geometry   | `RGFReal'` is a `C∞` manifold modeled on itself          |
  | Algebraic geometry      | the affine line `Spec RGFReal'[X]` as a scheme           |
  | Algebraic topology      | `RGFReal'` contractible, path- & simply-connected        |
  | Analytic number theory  | harmonic & prime-reciprocal divergence over `RGFReal'`   |
-/
import RGF.Math.Real.RealInstances
import RGF.Math.Analysis.FunctionalAnalysis
import RGF.Math.Analysis.MeasureIntegration
import RGF.Math.Topology.DifferentialGeometry
import RGF.Math.Algebra.AlgebraicGeometry
import RGF.Math.Topology.AlgebraicTopology
import RGF.Generative.Meta.AnalyticNumberTheory

namespace RGF
namespace RGFReal'

/-! ## Foundations: the RGF reals are a complete, normed, ordered field -/

noncomputable example : Field RGFReal'    := inferInstance
noncomputable example : LinearOrder RGFReal' := inferInstance
example : IsStrictOrderedRing RGFReal'    := inferInstance
example : Archimedean RGFReal'            := inferInstance
noncomputable example : NormedField RGFReal'      := inferInstance
noncomputable example : CompleteSpace RGFReal'    := inferInstance
noncomputable example : NontriviallyNormedField RGFReal' := inferInstance

/-! ## Headline witnesses, one per modern branch -/

-- Functional analysis: an infinite-dimensional Banach space over the RGF reals.
example : CompleteSpace RGFlp2 := rgf_lp2_complete
example : ¬ FiniteDimensional RGFReal' RGFlp2 := rgf_lp2_not_finiteDimensional
example {K : NNReal} {f : RGFReal' → RGFReal'} (hf : ContractingWith K f) :
    ∃! x : RGFReal', f x = x := rgf_banach_fixedPoint hf

-- Measure theory & integration on the RGF real line.
example : rgfVolume (Set.Icc (0 : RGFReal') 1) = 1 := rgfVolume_Icc_zero_one
example : ∫ _x in Set.Icc (0 : RGFReal') 1, (1 : ℝ) ∂rgfVolume = 1 := rgf_integral_const_one

-- Differential geometry: a smooth manifold.
example : IsManifold (modelWithCornersSelf RGFReal' RGFReal') ⊤ RGFReal' := rgf_isManifold

-- Algebraic geometry: the affine line as a scheme.
noncomputable example : AlgebraicGeometry.Scheme := rgfAffineLine

-- Algebraic topology: contractible, hence simply connected.
example : ContractibleSpace RGFReal'   := rgf_contractible
example : SimplyConnectedSpace RGFReal' := rgf_simplyConnected

-- Analytic number theory: divergent series over the RGF reals.
example :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (1 / (k + 1) : RGFReal'))
      Filter.atTop Filter.atTop := rgf_harmonic_diverges
example : ¬ Summable (fun p : Nat.Primes => (1 / (p : RGFReal'))) :=
  rgf_not_summable_one_div_primes

end RGFReal'
end RGF
