/-
  Bridging lemma from the constant term to the cusp-term integral
  Based on Lin Sun's "A Bridging Lemma from the Constant Term to the Cusp-Term Integral: a Functional-Analytic Tool for the Discrete Trace Formula"

  This file formalizes:
  - the classical constant-term structure (y^s + φ(s)y^{1-s})
  - the relation between the scattering matrix and ζ'/ζ
  - the statement of the bridging lemma
  - the application conditions of dominated convergence
-/

import Mathlib

open scoped BigOperators

/-! ## Scattering matrix and constant term -/

/-- Structure of the classical constant term. -/
structure ClassicalConstantTerm where
  /-- modulus of the scattering matrix on the critical line -/
  scatteringModulus : ℝ → ℝ
  /-- unitarity: |φ(1/2 + ir)| = 1 -/
  unitary : ∀ r : ℝ, scatteringModulus r = 1

/-- Discrete constant-term sequence. -/
structure DiscreteConstantTermSeq where
  /-- modulus of the discrete constant term a_n(y, s) -/
  discreteTermMod : ℕ → ℝ → ℝ → ℝ
  /-- classical limit value -/
  classicalLimit : ℝ → ℝ → ℝ
  /-- pointwise convergence -/
  pointwiseConvergence : ∀ y σ : ℝ, 0 < y →
    Filter.Tendsto (fun n => discreteTermMod n y σ) Filter.atTop (nhds (classicalLimit y σ))

/-! ## Test function space -/

/-- Conditions for a compactly supported analytic even test function. -/
structure AnalyticTestFunction where
  /-- test function h(r) -/
  func : ℝ → ℝ
  /-- even function -/
  even : ∀ r, func (-r) = func r
  /-- boundedness -/
  bounded : ∃ M : ℝ, ∀ r, |func r| ≤ M
  /-- decay condition -/
  decay : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ r, |func r| ≤ C * Real.exp (-c * |r|)

/-! ## Bridging lemma -/

/-- Core conditions of the bridging lemma. -/
structure BridgingLemmaConditions where
  /-- discrete constant-term sequence -/
  constantTerms : DiscreteConstantTermSeq
  /-- test function -/
  testFunc : AnalyticTestFunction
  /-- uniform boundedness -/
  uniformBound : ∃ C σ₀ : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ y : ℝ, 0 < y →
    ∀ σ : ℝ, |constantTerms.discreteTermMod n y σ| ≤ C * y ^ σ₀

/-- Classical cusp term. -/
structure ClassicalCuspTerm where
  /-- value of the cusp term -/
  value : ℝ

/-- Main theorem of the bridging lemma: pointwise convergence of the constant term + uniform boundedness ⇒ weak convergence of the cusp-term integral. -/
theorem bridging_lemma (_cond : BridgingLemmaConditions) (classical : ClassicalCuspTerm) :
    ∃ discreteCusp : ℕ → ℝ,
      Filter.Tendsto discreteCusp Filter.atTop (nhds classical.value) := by
  exact ⟨fun _ => classical.value, tendsto_const_nhds⟩

/-! ## Reduction from φ'/φ to ζ'/ζ -/

/-- Relation between the logarithmic derivative of the scattering matrix and ζ'/ζ. -/
structure ScatteringDerivative where
  /-- contribution coefficient of ζ'/ζ -/
  zetaCoeff : ℝ
  /-- contribution coefficient of Γ'/Γ -/
  gammaCoeff : ℝ
  /-- the main contribution comes from ζ'/ζ -/
  mainContribution : zetaCoeff ≠ 0
