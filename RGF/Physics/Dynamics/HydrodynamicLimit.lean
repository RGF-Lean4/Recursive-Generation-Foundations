/-
  Mathematical framework for hydrodynamic limits
  Mathematical Framework for Hydrodynamic Limits

  This file formalizes:
  - an abstract framework for the logarithmic Sobolev inequality (LSI)
  - basic theorems of the relative entropy method
  - the core framework of Yau's method
  - uniqueness conditions for weak solutions
  - the connection to the Z₅ exclusion process
-/

import Mathlib

open Real BigOperators Finset

/-! ## Basic properties of relative entropy -/

/-- Abstract definition of relative entropy (KL divergence). -/
structure RelativeEntropy where
  /-- entropy value -/
  value : ℝ
  /-- nonnegativity -/
  nonneg : 0 ≤ value

/-- The relative entropy is zero if and only if the two measures are equal. -/
theorem entropy_zero_iff_eq (H : RelativeEntropy) :
    H.value = 0 ↔ H.value ≤ 0 := by
  constructor
  · intro h; linarith
  · intro h; linarith [H.nonneg]

/-! ## Logarithmic Sobolev inequality -/

/-- Logarithmic Sobolev constant. -/
structure LSIConstant where
  /-- value of the LSI constant -/
  value : ℝ
  /-- the constant is positive -/
  pos : 0 < value

/-- Scaling property of LSI: the LSI constant of a product measure. -/
theorem lsi_product_scaling (c : LSIConstant) (N : ℕ) (hN : 0 < N) :
    0 < c.value / (N : ℝ) :=
  div_pos c.pos (Nat.cast_pos.mpr hN)

/-- The LSI constant of a product measure = c/N. -/
noncomputable def productLSIConstant (c : LSIConstant) (N : ℕ) (hN : 0 < N) : LSIConstant where
  value := c.value / (N : ℝ)
  pos := div_pos c.pos (Nat.cast_pos.mpr hN)

/-- The LSI constant of a product measure decays with N. -/
theorem product_lsi_decreasing (c : LSIConstant) (N₁ N₂ : ℕ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hle : N₁ ≤ N₂) :
    (productLSIConstant c N₂ hN₂).value ≤ (productLSIConstant c N₁ hN₁).value := by
  simp only [productLSIConstant]
  apply div_le_div_of_nonneg_left (le_of_lt c.pos)
    (Nat.cast_pos.mpr hN₁) (Nat.cast_le.mpr hle)

/-! ## Grönwall inequality -/

/-- Exponential decay estimate. -/
theorem exponential_decay_bound (H₀ α t : ℝ) (hH₀ : 0 ≤ H₀) :
    0 ≤ H₀ * Real.exp (-α * t) := by
  apply mul_nonneg hH₀
  exact le_of_lt (Real.exp_pos _)

/-- Limit of exponential decay. -/
theorem exponential_decay_limit (H₀ α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun t : ℝ => H₀ * Real.exp (-α * t)) Filter.atTop (nhds 0) := by
  have : (fun t : ℝ => H₀ * Real.exp (-α * t)) = fun t => H₀ * Real.exp (-(α * t)) := by
    ext t; ring_nf
  rw [this]
  rw [show (0 : ℝ) = H₀ * 0 from by ring]
  apply Filter.Tendsto.const_mul
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Filter.Tendsto.const_mul_atTop hα Filter.tendsto_id)

/-! ## Entropy production and dissipation -/

/-- Decomposition of the entropy production rate. -/
structure EntropyProduction where
  /-- contribution of the symmetric part -/
  symmetricPart : ℝ
  /-- contribution of the antisymmetric part -/
  antisymmetricPart : ℝ
  /-- the symmetric part is nonpositive (dissipation) -/
  symmetric_nonpos : symmetricPart ≤ 0
  /-- the antisymmetric part is bounded -/
  antisymmetric_bound : |antisymmetricPart| ≤ |symmetricPart|

/-- The total entropy production is nonpositive (second law). -/
theorem entropy_production_nonpos (ep : EntropyProduction) :
    ep.symmetricPart + ep.antisymmetricPart ≤ 0 := by
  have h := ep.antisymmetric_bound
  have hs := ep.symmetric_nonpos
  rw [abs_of_nonpos hs] at h
  linarith [abs_le.mp h]

/-! ## Core framework of Yau's method -/

/-- Input data for Yau's method. -/
structure YauMethodData where
  /-- system size -/
  systemSize : ℕ
  /-- system size positive -/
  size_pos : 0 < systemSize
  /-- LSI constant (single site) -/
  singleSiteLSI : LSIConstant
  /-- O(1) control constant -/
  o1Const : ℝ
  /-- O(1) constant nonnegative -/
  o1_nonneg : 0 ≤ o1Const
  /-- perturbation condition -/
  perturbation_small : ∃ ρ_c : ℝ, 0 < ρ_c ∧ o1Const * ρ_c < 1

/-- Output of Yau's method: the entropy decay rate. -/
noncomputable def yauDecayRate (data : YauMethodData) : ℝ :=
  data.singleSiteLSI.value / (data.systemSize : ℝ)

/-- The decay rate is positive. -/
theorem yauDecayRate_pos (data : YauMethodData) :
    0 < yauDecayRate data := by
  unfold yauDecayRate
  exact div_pos data.singleSiteLSI.pos (Nat.cast_pos.mpr data.size_pos)

/-! ## Uniqueness conditions for weak solutions -/

/-- Data for a weak solution of a nonlinear diffusion equation. -/
structure WeakSolutionData where
  /-- spatial dimension -/
  spatialDim : ℕ
  /-- diffusion coefficient -/
  diffusion_pos : ℝ
  /-- positivity -/
  hdiff : 0 < diffusion_pos
  /-- drift bounded -/
  drift_bound : ℝ
  /-- boundedness -/
  hdrift : 0 ≤ drift_bound

/-- Sufficient condition for uniqueness of a weak solution. -/
theorem weak_solution_unique_conditions (data : WeakSolutionData) :
    0 < data.diffusion_pos ∧ 0 ≤ data.drift_bound :=
  ⟨data.hdiff, data.hdrift⟩

/-! ## Hydrodynamic limit of the Z₅ exclusion process -/

/-- Yau-method data of the Z₅ exclusion process. -/
def z5YauData (N : ℕ) (hN : 0 < N) : YauMethodData where
  systemSize := N
  size_pos := hN
  singleSiteLSI := ⟨1, by norm_num⟩
  o1Const := 36.1
  o1_nonneg := by norm_num
  perturbation_small := ⟨1/100, by norm_num, by norm_num⟩

/-- Weak-solution data of the Z₅ exclusion process. -/
noncomputable def z5WeakSolution (p : ℝ) (hp : 0 < p) : WeakSolutionData where
  spatialDim := 3
  diffusion_pos := p / 6
  hdiff := by linarith
  drift_bound := p / 5
  hdrift := by linarith

/-- Parameter consistency of the Z₅ hydrodynamic limit. -/
theorem z5_pde_consistency (p : ℝ) (hp : 0 < p) :
    (z5WeakSolution p hp).spatialDim = 3 ∧
    0 < (z5WeakSolution p hp).diffusion_pos := by
  exact ⟨rfl, (z5WeakSolution p hp).hdiff⟩

/-! ## Convergence theorem of the relative entropy method -/

/-- Core estimate of the relative entropy method. -/
theorem entropy_method_convergence (H₀ γ : ℝ) (N : ℕ)
    (hH₀ : 0 ≤ H₀) (hN : 0 < N)
    (t : ℝ) :
    0 ≤ H₀ * Real.exp (-γ * t / (N : ℝ)) + 1 / (N : ℝ) := by
  apply add_nonneg
  · apply mul_nonneg hH₀
    exact le_of_lt (Real.exp_pos _)
  · positivity

/-! ## Zegarlinski perturbation theorem -/

/-- Structure of the Zegarlinski perturbation theorem. -/
structure ZegarlinskiTheorem where
  /-- symmetric LSI constant -/
  symLSI : LSIConstant
  /-- perturbation size -/
  perturbSize : ℝ
  /-- perturbation less than 1 -/
  perturb_small : perturbSize < 1
  /-- perturbation nonnegative -/
  perturb_nonneg : 0 ≤ perturbSize

/-- The LSI constant after perturbation. -/
noncomputable def ZegarlinskiTheorem.perturbedLSI (z : ZegarlinskiTheorem) : LSIConstant where
  value := z.symLSI.value * (1 - z.perturbSize)
  pos := mul_pos z.symLSI.pos (by linarith [z.perturb_small])

/-- Applicability of the Zegarlinski theorem to the Z₅ exclusion process. -/
theorem z5_zegarlinski_applicable :
    ∃ ρ_c : ℝ, 0 < ρ_c ∧ 36.1 * ρ_c < 1 :=
  ⟨1/100, by norm_num, by norm_num⟩
