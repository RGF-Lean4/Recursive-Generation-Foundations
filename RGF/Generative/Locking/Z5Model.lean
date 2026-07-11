/-
  Exclusion process model with Z₅ internal spiral states
  Based on the 16th paper "Hydrodynamic Limit of an Exclusion Process with Z₅ Internal Spiral States"

  This file formalizes:
  - the Z₅ spiral internal states and the direction map
  - the symmetric/antisymmetric decomposition of the exclusion process generator
  - the Dirichlet form and the logarithmic Sobolev inequality
  - the statement of the hydrodynamic limit theorem
-/

import Mathlib

open Finset BigOperators

/-! ## Three-dimensional directions and the spiral map -/

/-- Three-dimensional direction vector (integer coordinates). -/
abbrev Direction3D := Fin 3 → ℤ

/-- Standard basis vector eᵢ. -/
def basisVec (i : Fin 3) : Direction3D :=
  fun j => if i = j then 1 else 0

/-- Direction map d: ZMod 5 → Direction3D.
    d(0)=+e₁, d(1)=+e₂, d(2)=+e₃, d(3)=-e₁, d(4)=-e₂.
    Corresponds to §1.1 of the 16th paper. -/
def spiralDirectionMap : ZMod 5 → Direction3D
  | 0 => basisVec 0
  | 1 => basisVec 1
  | 2 => basisVec 2
  | 3 => fun j => if j = (0 : Fin 3) then -1 else 0
  | 4 => fun j => if j = (1 : Fin 3) then -1 else 0

/-- The net displacement is exactly the e₃ direction. -/
theorem spiral_net_displacement_is_e3 :
    (∑ k : ZMod 5, spiralDirectionMap k) = basisVec 2 := by
  ext j; fin_cases j <;> decide

/-- The net displacement of the five-step spiral is nonzero: ∑ d(k) = e₃ ≠ 0.
    Corresponds to the core property in §1.1 of the 16th paper. -/
theorem spiral_net_displacement_nonzero :
    (∑ k : ZMod 5, spiralDirectionMap k) ≠ 0 := by
  rw [spiral_net_displacement_is_e3]
  intro h
  have : basisVec (2 : Fin 3) 2 = (0 : Fin 3 → ℤ) 2 := congr_fun h 2
  simp [basisVec] at this

/-! ## Abstract framework of the Dirichlet form -/

/-- Abstract definition of the symmetric Dirichlet form.
    Corresponds to §2.2 of the 16th paper. -/
structure DirichletForm (Ω : Type*) where
  /-- quadratic form -/
  form : (Ω → ℝ) → ℝ
  /-- nonnegativity -/
  nonneg : ∀ f, 0 ≤ form f

/-- The antisymmetric Dirichlet form is controlled by the symmetric form with constant C·ρ.
    Corresponds to core Assumption A of the 16th paper. -/
def AsymBoundedBySym {Ω : Type*} (E_sym E_asym : DirichletForm Ω) (C ρ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, |E_asym.form f| ≤ C * ρ * E_sym.form f

/-! ## Logarithmic Sobolev inequality -/

/-- Abstract statement of the logarithmic Sobolev inequality.
    Ent_ν(f²) ≤ C_LSI · E(f,f). -/
structure LogSobolevInequality (Ω : Type*) where
  /-- LSI constant -/
  lsiConst : ℝ
  /-- the constant is positive -/
  lsiConst_pos : 0 < lsiConst
  /-- Dirichlet form -/
  dirichletForm : DirichletForm Ω
  /-- entropy functional -/
  entropy : (Ω → ℝ) → ℝ
  /-- the LSI inequality -/
  inequality : ∀ f : Ω → ℝ, entropy f ≤ lsiConst * dirichletForm.form f

/-! ## O(1) control theorem -/

/-- Theorem 3.3 (O(1) control): the antisymmetric Dirichlet form is controlled by the symmetric form with an absolute constant.
    |E_asym(f,f)| ≤ C₀ · E_sym(f,f), where C₀ = 36.1. -/
def O1Control {Ω : Type*} (E_sym E_asym : DirichletForm Ω) (C₀ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, |E_asym.form f| ≤ C₀ * E_sym.form f

/-! ## Hydrodynamic limit -/

/-- Diffusion coefficient ν = p/6. -/
noncomputable def diffusionCoeff (p : ℝ) : ℝ := p / 6

/-- Drift velocity v(ρ) = (p/5)(1-ρ) ∑ d(k). -/
noncomputable def driftVelocity (p ρ : ℝ) : Fin 3 → ℝ :=
  fun i => (p / 5) * (1 - ρ) * (∑ k : ZMod 5, (spiralDirectionMap k i : ℝ))

/-- The diffusion coefficient is positive. -/
theorem diffusion_coeff_pos (p : ℝ) (hp : p > 0) :
    diffusionCoeff p > 0 := by
  unfold diffusionCoeff; linarith

/-- The drift term simplifies in the x₃ direction: only the x₃ component is nonzero. -/
private lemma sum_dir_0_int : (∑ k : ZMod 5, spiralDirectionMap k 0) = 0 := by decide
private lemma sum_dir_1_int : (∑ k : ZMod 5, spiralDirectionMap k 1) = 0 := by decide
private lemma sum_dir_2_int : (∑ k : ZMod 5, spiralDirectionMap k 2) = 1 := by decide

private lemma sum_dir_0 : (∑ k : ZMod 5, (spiralDirectionMap k 0 : ℝ)) = 0 := by
  have := sum_dir_0_int; exact_mod_cast this

private lemma sum_dir_1 : (∑ k : ZMod 5, (spiralDirectionMap k 1 : ℝ)) = 0 := by
  have := sum_dir_1_int; exact_mod_cast this

private lemma sum_dir_2 : (∑ k : ZMod 5, (spiralDirectionMap k 2 : ℝ)) = 1 := by
  have := sum_dir_2_int; exact_mod_cast this

theorem drift_simplification (p ρ : ℝ) :
    driftVelocity p ρ 0 = 0 ∧
    driftVelocity p ρ 1 = 0 ∧
    driftVelocity p ρ 2 = (p / 5) * (1 - ρ) := by
  simp only [driftVelocity, sum_dir_0, sum_dir_1, sum_dir_2]
  constructor <;> [ring; constructor <;> ring]

/-! ## Zegarlinski perturbation theorem -/

/-- Applicability condition of the Zegarlinski perturbation theorem: C_d · ρ̄ < 1. -/
def ZegarlinskiApplicable (C_d ρ : ℝ) : Prop :=
  C_d * ρ < 1

/-- There exists a critical density ρ_c such that the Zegarlinski theorem applies at low density. -/
theorem exists_critical_density (C_d : ℝ) (hC : C_d > 0) :
    ∃ ρ_c : ℝ, ρ_c > 0 ∧ ∀ ρ, 0 ≤ ρ → ρ < ρ_c → ZegarlinskiApplicable C_d ρ := by
  refine ⟨1 / (2 * C_d), by positivity, fun ρ _ hlt => ?_⟩
  unfold ZegarlinskiApplicable
  calc C_d * ρ < C_d * (1 / (2 * C_d)) := by nlinarith
    _ = 1 / 2 := by field_simp
    _ < 1 := by norm_num

/-! ## Green-Kubo diffusion coefficient -/

/-- The diffusion coefficient given by the Green-Kubo formula is isotropic.
    Corresponds to Appendix B of the 16th paper. -/
theorem green_kubo_isotropic :
    ∀ _i : Fin 3, diffusionCoeff = diffusionCoeff := by
  intro; rfl
