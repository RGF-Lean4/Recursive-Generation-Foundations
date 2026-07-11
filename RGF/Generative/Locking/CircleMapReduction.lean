/-
  Reduction of the phase dynamics of an exclusion process to a Circle Map
  Based on the 17th paper "Reduction of the Phase Dynamics of an Exclusion Process to a Circle Map"

  This file formalizes:
  - the single-particle phase variable φ = (k-1)/5
  - the effective phase advance and the exclusion-constraint correction
  - the standard form of the Circle Map
  - the effective coupling strength K_eff ∝ ρ²
  - the mode-locking critical condition K_eff = 1
-/

import Mathlib

open Real

/-! ## Phase variable -/

/-- Single-particle phase variable: φ = k/5 ∈ [0, 1).
    Corresponds to §2.1 of the 17th paper. -/
noncomputable def spiralPhase (k : ZMod 5) : ℝ :=
  (k.val : ℝ) / 5

/-- The phase variable takes values in [0, 1). -/
theorem spiralPhase_range (k : ZMod 5) :
    0 ≤ spiralPhase k ∧ spiralPhase k < 1 := by
  constructor
  · unfold spiralPhase; positivity
  · unfold spiralPhase
    have hk := k.val_lt
    rw [div_lt_one (by norm_num : (5 : ℝ) > 0)]
    exact mod_cast hk

/-- On each successful transition, the phase advances by Δφ = 1/5. -/
noncomputable def phaseIncrement : ℝ := 1 / 5

/-! ## Effective phase advance -/

/-- The mean effective phase advance under the product measure.
    E[Δφ] = (1-ρ̄)/5. -/
noncomputable def meanPhaseAdvance (ρ : ℝ) : ℝ :=
  (1 - ρ) / 5

/-- The phase advance approaches 1/5 at low density. -/
theorem meanPhaseAdvance_low_density :
    meanPhaseAdvance 0 = 1 / 5 := by
  unfold meanPhaseAdvance; ring

/-- The phase advance is 0 at full density. -/
theorem meanPhaseAdvance_full_density :
    meanPhaseAdvance 1 = 0 := by
  unfold meanPhaseAdvance; ring

/-! ## Circle Map -/

/-- Standard Circle Map: θ_{n+1} = θ_n + Ω - (K/2π) sin(2πθ_n) (mod 1).
    Corresponds to §4 of the 17th paper. -/
noncomputable def spiralCircleMap (omega K theta : ℝ) : ℝ :=
  theta + omega - (K / (2 * π)) * sin (2 * π * theta)

/-- Effective coupling strength K_eff = A · ρ². -/
noncomputable def effectiveCoupling (A ρ : ℝ) : ℝ :=
  A * ρ ^ 2

/-- The effective coupling strength is zero at zero density. -/
theorem effectiveCoupling_zero_density (A : ℝ) :
    effectiveCoupling A 0 = 0 := by
  unfold effectiveCoupling; ring

/-! ## Mode-locking condition -/

/-- Mode-locking critical condition: the system is mode-locked when K_eff ≥ 1. -/
def IsLocked (K_eff : ℝ) : Prop := K_eff ≥ 1

/-- Quasiperiodic condition: the system is in the quasiperiodic phase when K_eff < 1. -/
def IsQuasiperiodic (K_eff : ℝ) : Prop := K_eff < 1

/-- Mode-locking and quasiperiodicity are complementary. -/
theorem locked_or_quasiperiodic (K_eff : ℝ) :
    IsLocked K_eff ∨ IsQuasiperiodic K_eff := by
  by_cases h : K_eff ≥ 1
  · exact Or.inl h
  · exact Or.inr (by push_neg at h; exact h)

/-- Critical density scaling: the mode-locking condition A·ρ² = 1 gives ρ_c = 1/√A. -/
noncomputable def lockingCriticalDensity (A : ℝ) : ℝ :=
  1 / Real.sqrt A

/-- At the critical density the coupling strength is exactly 1. -/
theorem coupling_at_critical (A : ℝ) (hA : A > 0) :
    effectiveCoupling A (lockingCriticalDensity A) = 1 := by
  unfold effectiveCoupling lockingCriticalDensity
  rw [div_pow, one_pow, Real.sq_sqrt hA.le]
  field_simp

/-! ## Z₅ Fourier analysis -/

/-- Discrete Fourier modes on Z₅.
    e_m(k) = exp(2πi·m·k/5), m = 0,1,2,3,4. -/
noncomputable def z5FourierMode (m k : ZMod 5) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (m.val : ℂ) * (k.val : ℂ) / 5)

/-- The fundamental-wave component f̂₁ of the deviation function controls the amplitude of the sine coupling.
    K_eff ∝ |f̂₁|². -/
noncomputable def fundamentalFourierAmplitude
    (deviationFunc : ZMod 5 → ℝ) : ℝ :=
  Complex.normSq (∑ k : ZMod 5, (deviationFunc k : ℂ) * z5FourierMode 1 k)

/-! ## Correspondence with Recursive Generation Formalism -/

/-- Circle Map correspondence structure.
    The deterministic version (14th paper) and the stochastic version (this paper) share the same technical backbone. -/
structure CircleMapCorrespondence where
  /-- base frequency Ω -/
  baseFrequency : ℝ
  /-- effective coupling strength K -/
  couplingStrength : ℝ
  /-- frequency positive -/
  freq_pos : baseFrequency > 0
  /-- coupling nonnegative -/
  coupling_nonneg : 0 ≤ couplingStrength

/-- The Circle Map parameters given by the exclusion process (at low density). -/
noncomputable def exclusionProcessCircleMap (ρ A : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) :
    CircleMapCorrespondence where
  baseFrequency := meanPhaseAdvance ρ
  couplingStrength := effectiveCoupling A ρ
  freq_pos := by unfold meanPhaseAdvance; linarith
  coupling_nonneg := by unfold effectiveCoupling; positivity
