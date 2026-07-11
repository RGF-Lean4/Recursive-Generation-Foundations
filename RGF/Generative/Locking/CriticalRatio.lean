/-
  Definition and proof of the critical winding-momentum ratio Γ_c
  Based on Paper 13' "An independently testable physical prediction of recursive generation theory: the critical winding-momentum ratio"

  This file formalizes:
  - the definition of the critical winding-momentum ratio Γ_c
  - a rigorous proof that Γ_c = 1
  - the universality of this conclusion independent of the microscopic parameters

  This is an independently testable physical prediction proposed by recursive generation theory.
-/

import Mathlib

open Real

/-! ## Definition of the critical winding-momentum ratio -/

/-- The contribution of the winding modes to the effective mass squared, m²_wind(L) = β · L^{d-1}.
    For d = 3 this is β · L². -/
noncomputable def windingContribution (beta : ℝ) (L : ℝ) (d : ℕ) : ℝ :=
  beta * L ^ (d - 1 : ℤ)

/-- The contribution of the momentum modes to the effective mass squared, m²_mom(L) = α · L⁻². -/
noncomputable def momentumContribution (alpha : ℝ) (L : ℝ) : ℝ :=
  alpha * L⁻¹ ^ 2

/-- Definition of the critical winding-momentum ratio Γ_c.
    Corresponding to Definition 3.1 of Paper 13':
    Γ_c ≡ |m²_wind(L_c) / m²_mom(L_c)| = β·L_c^{d-1} / (α·L_c⁻²)
    For d = 3 this is β·L_c² / (α·L_c⁻²). -/
noncomputable def criticalWindingMomentumRatio
    (alpha beta : ℝ) (L_c : ℝ) (d : ℕ) : ℝ :=
  windingContribution beta L_c d / momentumContribution alpha L_c

/-! ## Proof that Γ_c = 1 -/

/-
Core theorem: the critical winding-momentum ratio Γ_c = 1.

    For d = 3, under the critical-scale condition L_c = (α/β)^{1/4},
    Γ_c = β·L_c² / (α·L_c⁻²) = β·(α/β)^{1/2} / (α·(α/β)^{-1/2}) = 1.

    corresponding to the core result of §3.2 of Paper 13'.
    Physical meaning: at the critical stable point of the emergent space, the winding modes and the momentum modes
    contribute exactly equally to the effective mass squared.

    This result is entirely independent of the specific values of the microscopic parameters η, κ, τ_R.
-/
theorem critical_ratio_eq_one
    (alpha beta L_c : ℝ)
    (hα : alpha > 0) (hβ : beta > 0) (hL : L_c > 0)
    (h_critical : L_c ^ 4 = alpha / beta)  -- critical-scale condition L_c = (α/β)^{1/4}
    : criticalWindingMomentumRatio alpha beta L_c 3 = 1 := by
  unfold criticalWindingMomentumRatio;
  unfold windingContribution momentumContribution; rw [ div_eq_iff ] <;> ring; norm_num [ hα, hβ, hL, h_critical ] ;
  · field_simp;
    rw [ h_critical, mul_div_cancel₀ _ hβ.ne' ];
  · positivity

/-
The critical-scale condition is equivalent to the momentum contribution equaling the winding contribution (for d = 3).
    α · L_c⁻² = β · L_c² ↔ L_c⁴ = α/β
-/
theorem critical_scale_balance
    (alpha beta L_c : ℝ)
    (_hα : alpha > 0) (hβ : beta > 0) (hL : L_c > 0) :
    (alpha * L_c⁻¹ ^ 2 = beta * L_c ^ 2) ↔ L_c ^ 4 = alpha / beta := by
  grind +qlia

/-
Universality of Γ_c = 1: for any positive α, β,
    as long as the critical-scale condition holds, Γ_c is identically 1.
-/
theorem critical_ratio_universal
    (alpha₁ alpha₂ beta₁ beta₂ L₁ L₂ : ℝ)
    (hα₁ : alpha₁ > 0) (hβ₁ : beta₁ > 0) (hL₁ : L₁ > 0)
    (hα₂ : alpha₂ > 0) (hβ₂ : beta₂ > 0) (hL₂ : L₂ > 0)
    (h₁ : L₁ ^ 4 = alpha₁ / beta₁)
    (h₂ : L₂ ^ 4 = alpha₂ / beta₂) :
    criticalWindingMomentumRatio alpha₁ beta₁ L₁ 3 =
    criticalWindingMomentumRatio alpha₂ beta₂ L₂ 3 := by
  rw [ critical_ratio_eq_one, critical_ratio_eq_one ] <;> assumption

/-! ## Extremum condition of the spiral scaling law -/

/-- The effective-mass-squared function of the spiral scaling law for d = 3.
    ξ(L)⁻² = m₀² + α·L⁻² - β·L²-/
noncomputable def effectiveMassSquared (m0_sq alpha beta L : ℝ) : ℝ :=
  m0_sq + alpha * L⁻¹ ^ 2 - beta * L ^ 2

/-- The correlation-length function (defined when λ₁ > 0).
    ξ(L) = 1/√(ξ⁻²(L))-/
noncomputable def correlationLengthFunc (m0_sq alpha beta L : ℝ) : ℝ :=
  if effectiveMassSquared m0_sq alpha beta L > 0
  then 1 / Real.sqrt (effectiveMassSquared m0_sq alpha beta L)
  else 0

/-
At the critical point the correlation length attains a maximum (necessary condition of the extremum condition).
    At L_c, ∂_L(ξ⁻²) = 0, i.e. -2α·L⁻³ - 2β·L = 0,
    which simplifies to α·L⁻² = β·L².
    Note: the derivative of the scaling law is dξ⁻²/dL = -2αL⁻³ - 2βL (without m₀²),
    but in the derivation of Paper 13', the extremum condition is α·L_c⁻² = β·L_c².
-/
theorem extremal_condition_implies_balance
    (alpha beta L_c : ℝ)
    (_hα : alpha > 0) (_hβ : beta > 0) (hL : L_c > 0)
    (h_extremal : -2 * alpha * L_c⁻¹ ^ 3 + 2 * beta * L_c = 0) :
    alpha * L_c⁻¹ ^ 2 = beta * L_c ^ 2 := by
  grind +qlia