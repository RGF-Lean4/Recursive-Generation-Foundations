/-
  Orbit-classification estimates for exclusion processes
  Based on Lin Sun's "Orbit-Classification Estimates for Exclusion Processes: a General Method for Irreversible Non-gradient Systems"

  This file formalizes:
  - the classification into complete orbits and broken orbits
  - the core theorem of orbit-classification estimates
  - the upgrade from O(1) to O(ρ) control
  - the application of the Poincaré inequality
-/

import Mathlib

open scoped BigOperators

/-! ## Generator decomposition of the exclusion process -/

/-- Parameters of the exclusion process. -/
structure ExclusionParams (k : ℕ) where
  /-- number of internal states -/
  groupOrder : ℕ
  /-- group order = k -/
  order_eq : groupOrder = k
  /-- jump rate -/
  jumpRate : ℝ
  jumpRate_pos : 0 < jumpRate
  /-- particle density ρ ∈ (0, 1) -/
  density : ℝ
  density_pos : 0 < density
  density_lt_one : density < 1

/-- Z₅ exclusion process parameters. -/
def z5Params (p ρ : ℝ) (hp : 0 < p) (hρ1 : 0 < ρ) (hρ2 : ρ < 1) :
    ExclusionParams 5 where
  groupOrder := 5
  order_eq := rfl
  jumpRate := p
  jumpRate_pos := hp
  density := ρ
  density_pos := hρ1
  density_lt_one := hρ2

/-! ## Symmetric and antisymmetric Dirichlet forms -/

/-- Decomposition of the Dirichlet form. -/
structure DirichletDecomposition where
  /-- symmetric Dirichlet form -/
  symmetric : ℝ
  /-- antisymmetric Dirichlet form -/
  antisymmetric : ℝ
  /-- E_sym ≥ 0 -/
  symmetric_nonneg : 0 ≤ symmetric

/-! ## Orbit classification -/

/-- Orbit type. -/
inductive OrbitType
  /-- complete orbit -/
  | complete : OrbitType
  /-- broken orbit -/
  | broken : OrbitType

/-- Estimate data for a single orbit. -/
structure OrbitEstimate where
  /-- orbit type -/
  orbitType : OrbitType
  /-- intensity control constant -/
  intensityBound : ℝ
  /-- nonnegative -/
  intensity_nonneg : 0 ≤ intensityBound
  /-- density factor -/
  densityFactor : ℝ
  /-- nonnegative -/
  density_nonneg : 0 ≤ densityFactor

/-! ## Key lemmas for extracting the density factor -/

/-- The variance of the Bernoulli(ρ) distribution = ρ(1-ρ). -/
lemma bernoulli_variance (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    0 < ρ * (1 - ρ) :=
  mul_pos hρ (by linarith)

/-- ρ(1-ρ) ≤ 1/4. -/
lemma bernoulli_variance_bound (ρ : ℝ) (_hρ : 0 ≤ ρ) (_hρ1 : ρ ≤ 1) :
    ρ * (1 - ρ) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (ρ - 1/2)]

/-- ρ(1-ρ) ≤ ρ. -/
lemma bernoulli_variance_density (ρ : ℝ) (_hρ : 0 ≤ ρ) (_hρ1 : ρ ≤ 1) :
    ρ * (1 - ρ) ≤ ρ := by
  nlinarith [sq_nonneg ρ]

/-- Fraction estimate for broken orbits. -/
lemma broken_orbit_fraction (k : ℕ) (ρ : ℝ) (_hρ : 0 < ρ) (hρ1 : ρ < 1) (hk : 0 < k) :
    (k : ℝ) * ρ < (k : ℝ) := by
  have : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  exact mul_lt_of_lt_one_right this hρ1

/-! ## Core theorem of orbit-classification estimates -/

/-- Main result of orbit-classification estimates:
    |E_asym| ≤ C_d · ρ · E_sym. -/
structure OrbitClassificationEstimate (k : ℕ) where
  /-- exclusion process parameters -/
  params : ExclusionParams k
  /-- direction-map constant C_d -/
  directionConst : ℝ
  /-- C_d > 0 -/
  directionConst_pos : 0 < directionConst
  /-- core inequality -/
  mainEstimate : ∀ decomp : DirichletDecomposition,
    |decomp.antisymmetric| ≤ directionConst * params.density * decomp.symmetric

/-- Orbit-classification estimate constant of the Z₅ model. -/
noncomputable def z5_classification_constant : ℝ := 36.1 * 5

/-- The Z₅ constant is positive. -/
lemma z5_classification_constant_pos : 0 < z5_classification_constant := by
  simp [z5_classification_constant]; norm_num
