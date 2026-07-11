/-
  Layer 2: the dimension-locking theorem — d = 3 is the unique stable dimension
  Recursive Generation Foundations (RGF)

  This file formalizes:
  - the behavior of the spiral scaling law in a general dimension d
  - the formula Γ_c(d) = 2/(d-1)
  - d = 3 is the unique dimension with Γ_c = 1
  - exclusion of the other dimensions

  Corresponding to Paper 6 "The dimension and topology of the emergent space".
-/

import Mathlib

open Real

/-! ## Core formula of dimension locking -/

/-- The winding-momentum ratio formula in a general dimension d.
    The extremum condition ∂_L(ξ⁻²) = 0 gives 2α·L_c⁻³ = (d-1)·β·L_c^{d-2}
    substituting into Γ_c = β·L_c^{d-1}/(α·L_c⁻²) gives Γ_c(d) = 2/(d-1). -/
noncomputable def gammaCritical (d : ℕ) : ℝ :=
  2 / ((d : ℝ) - 1)

/-- For d = 3, Γ_c = 1. -/
theorem gamma_c_d3 : gammaCritical 3 = 1 := by
  simp [gammaCritical]; norm_num

/-- For d = 2, Γ_c = 2. -/
theorem gamma_c_d2 : gammaCritical 2 = 2 := by
  simp [gammaCritical]; norm_num

/-- For d = 4, Γ_c = 2/3. -/
theorem gamma_c_d4 : gammaCritical 4 = 2 / 3 := by
  simp [gammaCritical]; norm_num

/-- For d = 5, Γ_c = 1/2. -/
theorem gamma_c_d5 : gammaCritical 5 = 1 / 2 := by
  simp [gammaCritical]; norm_num

/-- For d = 6, Γ_c = 2/5. -/
theorem gamma_c_d6 : gammaCritical 6 = 2 / 5 := by
  simp [gammaCritical]; norm_num

/-! ## Dimension-locking theorem -/

/-
Core dimension-locking theorem: Γ_c = 1 if and only if d = 3.
    The constraint d ≥ 2 guarantees d-1 ≠ 0.
-/
theorem dimension_locking (d : ℕ) (hd : 2 ≤ d) :
    gammaCritical d = 1 ↔ d = 3 := by
  unfold gammaCritical;
  exact ⟨ fun h => by rw [ div_eq_iff ( sub_ne_zero_of_ne <| by norm_cast; linarith ) ] at h; rcases d with ( _ | _ | _ | _ | d ) <;> norm_num at * ; linarith, fun h => by norm_num [ h ] ⟩

/-
d = 3 is the unique natural number with Γ_c = 1 (within the range d ≥ 2).
-/
theorem dimension_locking_unique :
    ∃! (d : ℕ), 2 ≤ d ∧ d ≤ 100 ∧ gammaCritical d = 1 := by
  exact ⟨ 3, by norm_num [ gamma_c_d3 ], fun d ⟨ hd₁, hd₂, hd₃ ⟩ => dimension_locking d hd₁ |>.1 hd₃ ⟩

/-! ## Exclusion of d = 2 -/

/-- For d = 2, Γ_c ≠ 1. -/
theorem d2_excluded : gammaCritical 2 ≠ 1 := by
  rw [gamma_c_d2]; norm_num

/-- For d = 4, Γ_c ≠ 1. -/
theorem d4_excluded : gammaCritical 4 ≠ 1 := by
  rw [gamma_c_d4]; norm_num

/-- For d = 5, Γ_c ≠ 1. -/
theorem d5_excluded : gammaCritical 5 ≠ 1 := by
  rw [gamma_c_d5]; norm_num

/-- For d = 6, Γ_c ≠ 1. -/
theorem d6_excluded : gammaCritical 6 ≠ 1 := by
  rw [gamma_c_d6]; norm_num

/-! ## Three-dimensional effective mass squared -/

/-- The effective-mass-squared function for d = 3. -/
noncomputable def effectiveMassSq3D (alpha beta L : ℝ) : ℝ :=
  alpha * L⁻¹ ^ 2 - beta * L ^ 2

/-
The extremum condition for d = 3 gives L_c⁴ = α/β.
-/
theorem d3_extremal_gives_Lc4 (alpha beta L_c : ℝ)
    (_hα : 0 < alpha) (hβ : 0 < beta) (hL : 0 < L_c)
    (h_balance : alpha * L_c⁻¹ ^ 2 = beta * L_c ^ 2) :
    L_c ^ 4 = alpha / beta := by
  grind

/-
For d = 3, Γ_c = β·L_c²/(α·L_c⁻²) = 1.
-/
theorem d3_gamma_eq_one (alpha beta L_c : ℝ)
    (_hα : 0 < alpha) (hβ : 0 < beta) (hL : 0 < L_c)
    (h_critical : L_c ^ 4 = alpha / beta) :
    beta * L_c ^ 2 / (alpha * L_c⁻¹ ^ 2) = 1 := by
  grind +revert

/-! ## Connection with the topology of the emergent space -/

/-- The three-dimensional emergence theorem of RGF:
    under the momentum-winding competition mechanism, d = 3 is the unique dimension at which the two modes
    are perfectly balanced at the critical point. This provides a purely mathematical explanation for
    "why physical space is three-dimensional". -/
theorem rgf_three_dimensions :
    gammaCritical 3 = 1 ∧
    gammaCritical 2 ≠ 1 ∧
    gammaCritical 4 ≠ 1 ∧
    gammaCritical 5 ≠ 1 ∧
    gammaCritical 6 ≠ 1 :=
  ⟨gamma_c_d3, d2_excluded, d4_excluded, d5_excluded, d6_excluded⟩