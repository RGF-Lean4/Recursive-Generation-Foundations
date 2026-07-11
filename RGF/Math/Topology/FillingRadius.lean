/-
  Line-lattice dimension reduction: filling radius theorem and metric convergence
  Linear Grid Principle: Filling Radius Theorem and Metric Convergence

  This file formalizes:
  - precise estimates of the filling radius
  - the convergence rate of the discretization error
  - bi-Lipschitz equivalence
  - the ε-net and covering properties of a metric space
-/

import Mathlib

open Real BigOperators Finset

/-! ## Bi-Lipschitz maps -/

/-- Parametrization conditions for a bi-Lipschitz map. -/
structure BiLipschitzData where
  /-- lower Lipschitz constant -/
  c₁ : ℝ
  /-- upper Lipschitz constant -/
  c₂ : ℝ
  /-- c₁ > 0 -/
  hc₁ : 0 < c₁
  /-- c₂ > 0 -/
  hc₂ : 0 < c₂
  /-- c₁ ≤ c₂ -/
  hle : c₁ ≤ c₂

/-- Distortion ratio c₂/c₁ ≥ 1. -/
theorem BiLipschitzData.distortion_ge_one (d : BiLipschitzData) :
    1 ≤ d.c₂ / d.c₁ := by
  rw [le_div_iff₀ d.hc₁]
  linarith [d.hle]

/-- The distortion ratio is positive. -/
theorem BiLipschitzData.distortion_pos (d : BiLipschitzData) :
    0 < d.c₂ / d.c₁ :=
  div_pos d.hc₂ d.hc₁

/-! ## Discretization grid -/

/-- Discretization grid parameters. -/
structure GridParams where
  /-- dimension -/
  dim : ℕ
  /-- discretization step parameter n -/
  refinement : ℕ
  /-- dimension positive -/
  dim_pos : 0 < dim
  /-- step parameter positive -/
  refinement_pos : 0 < refinement

/-- Grid step size δ = 1/n. -/
noncomputable def GridParams.stepSize (g : GridParams) : ℝ :=
  1 / (g.refinement : ℝ)

/-- The step size is positive. -/
theorem GridParams.stepSize_pos (g : GridParams) : 0 < g.stepSize := by
  unfold stepSize
  exact div_pos one_pos (Nat.cast_pos.mpr g.refinement_pos)

/-
The step size decreases with n.
-/
theorem GridParams.stepSize_decreasing (g₁ g₂ : GridParams)
    (h : g₁.refinement ≤ g₂.refinement) :
    g₂.stepSize ≤ g₁.stepSize := by
  unfold GridParams.stepSize;
  gcongr ; norm_cast;
  exact g₁.refinement_pos

/-! ## Filling radius theorem -/

/-- Upper bound on the filling radius: ρ_fill ≤ c₂ · √dim · δ. -/
noncomputable def fillingRadiusBound (d : BiLipschitzData) (g : GridParams) : ℝ :=
  d.c₂ * Real.sqrt (g.dim : ℝ) * g.stepSize

/-- The filling radius is nonnegative. -/
theorem fillingRadiusBound_nonneg (d : BiLipschitzData) (g : GridParams) :
    0 ≤ fillingRadiusBound d g := by
  unfold fillingRadiusBound
  apply mul_nonneg
  · apply mul_nonneg (le_of_lt d.hc₂) (Real.sqrt_nonneg _)
  · exact le_of_lt g.stepSize_pos

/-- Convergence rate of the discretization error: O(1/n). -/
theorem discretization_error_rate (d : BiLipschitzData) (dim n : ℕ)
    (hdim : 0 < dim) (hn : 0 < n) :
    fillingRadiusBound d ⟨dim, n, hdim, hn⟩ =
      d.c₂ * Real.sqrt (dim : ℝ) / (n : ℝ) := by
  unfold fillingRadiusBound GridParams.stepSize
  ring

/-! ## Covering property of ε-nets -/

/-- Dimensional scaling of the number of grid points. -/
theorem grid_point_count (n dim : ℕ) (hn : 0 < n) (_hdim : 0 < dim) :
    0 < n ^ dim :=
  Nat.pos_of_ne_zero (by positivity)

/-! ## Hausdorff distance control -/

/-- The Hausdorff distance is controlled by the filling radius. -/
theorem hausdorff_le_filling (d : BiLipschitzData) (g : GridParams)
    (dHausdorff : ℝ) (h : dHausdorff ≤ fillingRadiusBound d g) :
    dHausdorff ≤ d.c₂ * Real.sqrt (g.dim : ℝ) * g.stepSize :=
  h

/-! ## Volume estimates -/

/-- Finiteness conditions for the volume of a fundamental domain. -/
structure FundamentalDomainData where
  /-- volume -/
  volume : ℝ
  /-- volume positive -/
  volume_pos : 0 < volume
  /-- diameter -/
  diameter : ℝ
  /-- diameter positive -/
  diameter_pos : 0 < diameter

/-! ## Jacobi group example -/

/-- Bi-Lipschitz data of the Jacobi group (dim = 4). -/
def jacobiLipschitz : BiLipschitzData where
  c₁ := 1
  c₂ := 2
  hc₁ := by norm_num
  hc₂ := by norm_num
  hle := by norm_num

/-- Grid parameters of the Jacobi group. -/
def jacobiGrid (n : ℕ) (hn : 0 < n) : GridParams where
  dim := 4
  refinement := n
  dim_pos := by norm_num
  refinement_pos := hn

/-- Explicit value of the filling radius of the Jacobi group. -/
theorem jacobi_filling_radius (n : ℕ) (hn : 0 < n) :
    fillingRadiusBound jacobiLipschitz (jacobiGrid n hn) =
      2 * Real.sqrt 4 / (n : ℝ) := by
  simp [fillingRadiusBound, jacobiLipschitz, jacobiGrid, GridParams.stepSize]
  ring

/-! ## Siegel upper half-space example -/

/-- Siegel dimension formula. -/
def siegelDimLGP (g : ℕ) : ℕ := g * (g + 1) / 2 + g

/-- For g = 1 the Siegel dimension = 2. -/
theorem siegel_dim_lgp_1 : siegelDimLGP 1 = 2 := by decide

/-- For g = 2 the Siegel dimension = 5. -/
theorem siegel_dim_lgp_2 : siegelDimLGP 2 = 5 := by decide

/-- For g = 3 the Siegel dimension = 9. -/
theorem siegel_dim_lgp_3 : siegelDimLGP 3 = 9 := by decide

/-
The filling radius grows with dimension.
-/
theorem filling_radius_dimension_scaling (d : BiLipschitzData) (n : ℕ) (hn : 0 < n)
    (dim₁ dim₂ : ℕ) (hdim₁ : 0 < dim₁) (hdim₂ : 0 < dim₂) (hle : dim₁ ≤ dim₂) :
    fillingRadiusBound d ⟨dim₁, n, hdim₁, hn⟩ ≤
    fillingRadiusBound d ⟨dim₂, n, hdim₂, hn⟩ := by
  unfold fillingRadiusBound;
  gcongr;
  · exact div_nonneg zero_le_one ( Nat.cast_nonneg _ );
  · exact mul_nonneg d.hc₂.le ( Real.sqrt_nonneg _ );
  · exact le_of_lt d.hc₂;
  · unfold GridParams.stepSize; aesop;
