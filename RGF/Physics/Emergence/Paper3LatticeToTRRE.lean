/-
  Paper 3 — "From RCD lattice rules to the time-domain recursion equation: a first-principles derivation"
  (From RCD lattice rules to the time-domain recursion equation), L. Sun 2026.

  Placed in the RGF **Physics** layer (Layer 3 / Physics dynamics).
  Complements the supplement anchor `Paper3SCoarseGraining`.

  Formalizes cleanly-statable cores of the derivation chain from the three
  parameter-free lattice rules G1–G3 to the time-domain recursion equation:

  * the density-field **diffusion coefficient** `D = p/(2d)` and coarse-grained
    **noise variance** `σ² = p(1−p)/(2d)`;
  * the **FORS kernel** `K(k) = [1 + (k/Λ)^{5/2}]⁻¹` takes values in `(0,1]`;
  * **anomalous scaling homogeneity** of degree `5/2`:
    `Σ(λk) = λ^{5/2} Σ(k)` for `Σ(k) = k^{5/2}`;
  * **spatial dimension `d = 3`** from the self-duality `dim 𝔰𝔬(d) = d`.
-/
import Mathlib

namespace RGF.Paper3

/-- Density-field diffusion coefficient `D = p/(2d)` (step (1)). -/
noncomputable def diffusionCoeff (p : ℝ) (d : ℕ) : ℝ := p / (2 * d)

/-- Coarse-grained noise variance `σ² = p(1−p)/(2d)` (step (6)). -/
noncomputable def noiseVariance (p : ℝ) (d : ℕ) : ℝ := p * (1 - p) / (2 * d)

/-- FORS kernel `K(k) = [1 + (k/Λ)^{5/2}]⁻¹` (step (4)). -/
noncomputable def forsKernel (Λ k : ℝ) : ℝ := (1 + (k / Λ) ^ ((5 : ℝ) / 2))⁻¹

/-- The FORS kernel is a genuine cutoff profile: `K(k) ∈ (0,1]` for `k ≥ 0`,
`Λ > 0`. -/
theorem forsKernel_mem_Ioc (Λ k : ℝ) (hΛ : 0 < Λ) (hk : 0 ≤ k) :
    0 < forsKernel Λ k ∧ forsKernel Λ k ≤ 1 :=
  ⟨inv_pos.mpr (by positivity),
    inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))⟩

/-- Anomalous scaling homogeneity of degree `5/2`: the self-energy
`Σ(k) = k^{5/2}` satisfies `Σ(λk) = λ^{5/2} Σ(k)` (step (3)). -/
theorem scaling_homogeneous (lam k : ℝ) (hlam : 0 ≤ lam) (hk : 0 ≤ k) :
    (lam * k) ^ ((5 : ℝ) / 2) = lam ^ ((5 : ℝ) / 2) * k ^ ((5 : ℝ) / 2) :=
  Real.mul_rpow hlam hk

/-- Spatial dimension is locked to 3 by the self-duality `dim 𝔰𝔬(d) = d`, i.e.
`d(d−1) = 2d`, which for `d ≥ 1` holds iff `d = 3` (the exact value in the
dimension argument). -/
theorem dimension_three (d : ℕ) (hd : 1 ≤ d) :
    d * (d - 1) = 2 * d ↔ d = 3 := by
  rcases d with (_ | _ | _ | _ | d) <;> simp_all +arith +decide [mul_comm]

end RGF.Paper3
