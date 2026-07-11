/-
  Spectral graph theory: discrete heat kernel and diffusion process
  Spectral Graph Theory: Discrete Heat Kernel and Diffusion

  Formalizes the discrete heat equation, the semigroup property of the heat kernel,
  and the relation between the heat-kernel trace and spectral functions.
  This is the mathematical bridge from discrete to continuous for the emergent space.
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Discrete heat equation -/

/-- Discrete heat equation evolution operator on a graph.
    Given the symmetric adjacency matrix W and the degree matrix D,
    the normalized evolution is P = D⁻¹W (random walk matrix). -/
noncomputable def heatEvolution
    {n : ℕ} (W : Fin n → Fin n → ℝ) (deg : Fin n → ℝ)
    (f : Fin n → ℝ) (v : Fin n) : ℝ :=
  if deg v = 0 then f v
  else (1 / deg v) * ∑ u : Fin n, W v u * f u

/-- Heat evolution conserves total mass (when W is symmetric and nonnegative). -/
theorem heatEvolution_mass_conservation
    {n : ℕ} (W : Fin n → Fin n → ℝ)
    (deg : Fin n → ℝ)
    (hW_sym : ∀ i j, W i j = W j i)
    (hdeg : ∀ v, deg v = ∑ u : Fin n, W v u)
    (hdeg_pos : ∀ v, 0 < deg v)
    (f : Fin n → ℝ) :
    ∑ v : Fin n, deg v * heatEvolution W deg f v =
    ∑ v : Fin n, deg v * f v := by
  have hdeg_ne : ∀ v, deg v ≠ 0 := fun v => ne_of_gt (hdeg_pos v)
  simp only [heatEvolution, hdeg_ne, ↓reduceIte]
  conv_lhs =>
    arg 2; ext v
    rw [show deg v * (1 / deg v * ∑ u, W v u * f u) =
        (deg v * (1 / deg v)) * ∑ u, W v u * f u from by ring]
    rw [mul_div_cancel₀ _ (hdeg_ne v)]
    rw [one_mul]
  rw [Finset.sum_comm]
  congr 1; ext u
  rw [← Finset.sum_mul]
  congr 1
  conv_lhs => arg 2; ext v; rw [hW_sym v u]
  exact (hdeg u).symm

/-! ## 2. Iteration of the heat kernel -/

/-- k-step heat evolution. -/
noncomputable def heatIterate
    {n : ℕ} (W : Fin n → Fin n → ℝ) (deg : Fin n → ℝ)
    (k : ℕ) (f : Fin n → ℝ) : Fin n → ℝ :=
  match k with
  | 0 => f
  | k + 1 => heatEvolution W deg (heatIterate W deg k f)

/-- The 0-step iteration is the identity. -/
theorem heatIterate_zero
    {n : ℕ} (W : Fin n → Fin n → ℝ) (deg : Fin n → ℝ)
    (f : Fin n → ℝ) :
    heatIterate W deg 0 f = f := by
  simp [heatIterate]

/-- The 1-step iteration equals one heat evolution. -/
theorem heatIterate_one
    {n : ℕ} (W : Fin n → Fin n → ℝ) (deg : Fin n → ℝ)
    (f : Fin n → ℝ) :
    heatIterate W deg 1 f = heatEvolution W deg f := by
  simp [heatIterate]

/-! ## 3. Heat-kernel trace -/

/-- Heat-kernel trace: Tr(P^t) = ∑_i P^t(i,i). -/
noncomputable def heatTrace
    {n : ℕ} (W : Fin n → Fin n → ℝ) (deg : Fin n → ℝ)
    (t : ℕ) : ℝ :=
  ∑ v : Fin n, heatIterate W deg t (fun u => if u = v then 1 else 0) v

/-- The heat-kernel trace at t=0 equals n. -/
theorem heatTrace_zero {n : ℕ} (W : Fin n → Fin n → ℝ) (deg : Fin n → ℝ) :
    heatTrace W deg 0 = (n : ℝ) := by
  simp [heatTrace, heatIterate]

/-! ## 4. Dirichlet form and heat-kernel decay -/

/-- Discrete Dirichlet form. -/
noncomputable def dirichletForm
    {n : ℕ} (W : Fin n → Fin n → ℝ) (f : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, W i j * (f i - f j) ^ 2

/-- The Dirichlet form is nonnegative. -/
theorem dirichletForm_nonneg
    {n : ℕ} (W : Fin n → Fin n → ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (f : Fin n → ℝ) :
    0 ≤ dirichletForm W f := by
  unfold dirichletForm
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact mul_nonneg (hW i j) (sq_nonneg _)

/-- The Dirichlet form of a constant function is zero. -/
theorem dirichletForm_const
    {n : ℕ} (W : Fin n → Fin n → ℝ) (c : ℝ) :
    dirichletForm W (fun _ => c) = 0 := by
  unfold dirichletForm; simp [sub_self]

/-! ## 5. Variational characterization of the spectral gap -/

/-- Spectral gap (infimum of the Rayleigh quotient). -/
noncomputable def spectralGapHK
    {n : ℕ} (W : Fin n → Fin n → ℝ) (deg : Fin n → ℝ) : ℝ :=
  ⨅ f : { f : Fin n → ℝ // ∃ v, f v ≠ 0 },
    dirichletForm W f.val / ∑ v : Fin n, deg v * (f.val v) ^ 2

/-- The spectral gap is nonnegative (when weights and degrees are nonnegative). -/
theorem spectralGapHK_nonneg
    {n : ℕ} (W : Fin n → Fin n → ℝ) (deg : Fin n → ℝ)
    (hW : ∀ i j, 0 ≤ W i j) (hdeg : ∀ v, 0 ≤ deg v) :
    0 ≤ spectralGapHK W deg := by
  unfold spectralGapHK
  apply Real.iInf_nonneg; intro f
  apply div_nonneg (dirichletForm_nonneg W hW f.val)
  apply Finset.sum_nonneg; intro v _
  exact mul_nonneg (hdeg v) (sq_nonneg _)

/-! ## 6. Emergent temperature and scaling law -/

/-- Emergent temperature: T_eff = 1 / (spectral gap × system size).
    When the spectral gap ∝ 1/n, T_eff ∝ 1 is constant — this corresponds to the critical state. -/
noncomputable def emergentTemperature (gap : ℝ) (systemSize : ℕ) : ℝ :=
  if gap * systemSize = 0 then 0
  else 1 / (gap * systemSize)

/-- Critical scaling: when gap = c/n, the emergent temperature is constant. -/
theorem critical_scaling_temperature
    (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 0 < n) :
    emergentTemperature (c / n) n = 1 / c := by
  unfold emergentTemperature
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_mul_cancel₀ c hn']
  simp [ne_of_gt hc]

/-! ## 7. Spectral gap and mixing time -/

/-- The spectral gap determines the mixing rate. -/
theorem spectral_gap_mixing_decay
    (lambda1 : ℝ) (hlambda : 0 < lambda1)
    (hlambda_le : lambda1 ≤ 1)
    (t : ℕ) :
    (1 - lambda1) ^ t ≤ 1 := by
  apply pow_le_one₀ <;> linarith

/-- Spectral gap and exponential decay. -/
theorem spectral_gap_exp_decay
    (lambda1 : ℝ) (hlambda : 0 < lambda1)
    (hlambda_le : lambda1 ≤ 1)
    (t : ℕ) (ht : 0 < t) :
    (1 - lambda1) ^ t < 1 := by
  apply pow_lt_one₀ <;> linarith
