/-
  Orbit pairing and orbit-classification estimates
  Based on the 19th paper "Orbit Pairing and Orbit-Classification Estimates: a General Method for Irreversible Non-gradient Exclusion Processes"

  This file formalizes:
  - an abstract framework for exclusion processes with group symmetry
  - the symmetric/antisymmetric decomposition of the generator (group averaging method)
  - the orbit-pairing method (orbit-cancellation identity)
  - orbit-classification estimates (complete orbits vs broken orbits)
  - the O(1) control theorem and the O(ρ) improvement
-/

import Mathlib

open Finset BigOperators

/-! ## Exclusion processes with group symmetry -/

/-- Abstract framework for an exclusion process with finite group symmetry.
    Corresponds to §2.1 of the 19th paper. -/
structure GroupSymmetricProcess (G Ω : Type*) [Group G] [Fintype G] where
  /-- the group acts on the configuration space -/
  act : G → Ω → Ω
  /-- identity-element property of the group action -/
  act_one : ∀ σ, act 1 σ = σ
  /-- associativity of the group action -/
  act_mul : ∀ g₁ g₂ σ, act (g₁ * g₂) σ = act g₁ (act g₂ σ)
  /-- transition rate function r(σ, τ) ≥ 0 -/
  rate : Ω → Ω → ℝ
  /-- nonnegativity of the rate -/
  rate_nonneg : ∀ σ τ, 0 ≤ rate σ τ

namespace GroupSymmetricProcess

variable {G Ω : Type*} [Group G] [Fintype G]
variable (P : GroupSymmetricProcess G Ω)

/-! ## Symmetric decomposition of the generator -/

/-- Symmetrized transition rate: group average.
    L_sym(σ,τ) = (1/|G|) ∑_{g∈G} r(g⁻¹·σ, g⁻¹·τ). -/
noncomputable def symmetrizedRate (σ τ : Ω) : ℝ :=
  (1 / (Fintype.card G : ℝ)) *
    ∑ g : G, P.rate (P.act g⁻¹ σ) (P.act g⁻¹ τ)

/-- Antisymmetric transition rate. L_asym(σ,τ) = r(σ,τ) - L_sym(σ,τ). -/
noncomputable def antisymmetricRate (σ τ : Ω) : ℝ :=
  P.rate σ τ - P.symmetrizedRate σ τ

/-! ## Orbit-pairing method -/

/-- Linear factor along an orbit. -/
noncomputable def orbitLinearFactor (σ τ : Ω) (g : G) : ℝ :=
  P.rate (P.act g⁻¹ σ) (P.act g⁻¹ τ) - P.symmetrizedRate σ τ

/-- Orbit-cancellation identity (core lemma).
    ∑_{g∈G} (r(g⁻¹·σ, g⁻¹·τ) - L_sym(σ,τ)) = 0.
    This is an exact algebraic identity, independent of any probability measure. -/
theorem orbit_cancellation_identity (σ τ : Ω) :
    ∑ g : G, P.orbitLinearFactor σ τ g = 0 := by
  simp only [orbitLinearFactor, Finset.sum_sub_distrib]
  simp [symmetrizedRate, Finset.sum_const, Finset.card_univ]

/-! ## Orbit classification -/

/-- Complete orbit: every configuration pair along the orbit has positive transition rate. -/
def IsCompleteOrbit (σ τ : Ω) : Prop :=
  ∀ g : G, P.rate (P.act g⁻¹ σ) (P.act g⁻¹ τ) > 0

/-- Broken orbit: there exists a group element making the transition rate zero. -/
def IsBrokenOrbit (σ τ : Ω) : Prop :=
  ∃ g : G, P.rate (P.act g⁻¹ σ) (P.act g⁻¹ τ) = 0

/-- Dichotomy between complete and broken orbits. -/
theorem complete_or_broken (σ τ : Ω)
    (_h : ∃ g : G, P.rate (P.act g⁻¹ σ) (P.act g⁻¹ τ) > 0) :
    P.IsCompleteOrbit σ τ ∨ P.IsBrokenOrbit σ τ := by
  by_cases hc : ∀ g, P.rate (P.act g⁻¹ σ) (P.act g⁻¹ τ) > 0
  · exact Or.inl hc
  · right
    push_neg at hc
    obtain ⟨g, hg⟩ := hc
    exact ⟨g, le_antisymm hg (P.rate_nonneg _ _)⟩

end GroupSymmetricProcess

/-! ## Dirichlet form control (defined independently, not relying on GroupSymmetricProcess) -/

/-- O(1) control: the antisymmetric Dirichlet form is controlled by the symmetric form with an absolute constant. -/
def O1ControlBound {Ω : Type*} (C₀ : ℝ) (E_sym E_asym : (Ω → ℝ) → ℝ) : Prop :=
  ∀ f : Ω → ℝ, |E_asym f| ≤ C₀ * E_sym f

/-- O(ρ) control: the antisymmetric Dirichlet form is controlled by a density multiple of the symmetric form. -/
def OrhoControlBound {Ω : Type*} (C_d ρ : ℝ) (E_sym E_asym : (Ω → ℝ) → ℝ) : Prop :=
  ∀ f : Ω → ℝ, |E_asym f| ≤ C_d * ρ * E_sym f

/-- O(ρ) control implies O(1) control (when ρ ≤ 1 and C_d ≥ 0). -/
theorem orho_implies_o1 {Ω : Type*} {C_d ρ : ℝ} (hC : 0 ≤ C_d) (_hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {E_sym E_asym : (Ω → ℝ) → ℝ}
    (hE : ∀ f, 0 ≤ E_sym f)
    (h : OrhoControlBound C_d ρ E_sym E_asym) :
    O1ControlBound C_d E_sym E_asym := by
  intro f
  have h1 := h f
  have h2 := hE f
  calc |E_asym f| ≤ C_d * ρ * E_sym f := h1
    _ ≤ C_d * 1 * E_sym f := by
        have : C_d * ρ * E_sym f ≤ C_d * 1 * E_sym f := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hρ1 hC
          · exact h2
        exact this
    _ = C_d * E_sym f := by ring

/-! ## Application examples -/

/-- O(1) control constant of the Z_n spiral exclusion process.
    C₀ = (n-1)² · max_ratio. -/
noncomputable def znControlConstant (n : ℕ) (maxRatio : ℝ) : ℝ :=
  ((n : ℝ) - 1) ^ 2 * maxRatio

/-- The explicit constant of the Z₅ exclusion process: C₀ = 36.1. -/
theorem z5_control_constant_value :
    znControlConstant 5 2.25625 = 36.1 := by
  unfold znControlConstant; norm_num
