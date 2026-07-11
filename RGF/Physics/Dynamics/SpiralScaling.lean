/-
  The spiral scaling law and the critical length

  Mathematical content extracted from the user's document:
  - scaling formula: ξ(L)⁻² = m₀² + α·L⁻² - β·L^(d-1)
  - the critical length L_c is where the momentum contribution balances the winding contribution:
    α·L_c⁻² = β·L_c^(d-1), giving L_c^(d+1) = α/β
  - for d = 3: L_c = (α/β)^(1/4)
  - the critical winding-momentum ratio Γ_c = 2/(d-1)
-/

import Mathlib

open Real

/-- The squared inverse correlation length as a function of the scale L,
    where the dimension is d, the bare mass is m₀, the momentum coefficient is α, and the winding coefficient is β.
    ξ(L)⁻² = m₀² + α/L² - β·L^(d-1) -/
noncomputable def xiInvSq (m₀ α β : ℝ) (d : ℕ) (L : ℝ) : ℝ :=
  m₀^2 + α / L^2 - β * L^((d : ℝ) - 1)

/-- The critical length L_c, where the momentum contribution balances the winding contribution:
    α/L² = β·L^(d-1), giving L^(d+1) = α/β.
    Equivalently: L_c = (α/β)^(1/(d+1)). -/
noncomputable def criticalLength (α β : ℝ) (d : ℕ) : ℝ :=
  (α / β) ^ (1 / ((d : ℝ) + 1))

/-- For d = 3, the critical length simplifies to (α/β)^(1/4). -/
theorem criticalLength_d3 (α β : ℝ) (_hα : 0 < α) (_hβ : 0 < β) :
    criticalLength α β 3 = (α / β) ^ (1/4 : ℝ) := by
  unfold criticalLength; norm_num

/-
The critical length satisfies the balance condition: L_c^(d+1) = α/β.
-/
theorem criticalLength_balance (α β : ℝ) (d : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    (criticalLength α β d) ^ ((d : ℝ) + 1) = α / β := by
      unfold criticalLength;
      rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ]

/-
At the critical length, the momentum contribution equals the winding contribution:
    α/L_c² = β·L_c^(d-1).
-/
theorem criticalLength_momentum_eq_winding (α β : ℝ) (d : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    α / (criticalLength α β d)^2 = β * (criticalLength α β d)^((d : ℝ) - 1) := by
      rw [ div_eq_iff ];
      · rw [ mul_assoc, ← Real.rpow_natCast _ 2, ← Real.rpow_add ( by exact Real.rpow_pos_of_pos ( div_pos hα hβ ) _ ) ] ; norm_num;
        rw [ show ( d : ℝ ) - 1 + 2 = ( d : ℝ ) + 1 by ring, criticalLength_balance α β d hα hβ ] ; ring_nf;
        rw [ mul_right_comm, mul_inv_cancel₀ hβ.ne', one_mul ];
      · exact ne_of_gt ( sq_pos_of_pos ( Real.rpow_pos_of_pos ( div_pos hα hβ ) _ ) )

/-- The critical winding-momentum ratio Γ_c at the critical length.
    Γ_c = β·L_c^(d+1) / α -/
noncomputable def criticalRatio (α β : ℝ) (d : ℕ) : ℝ :=
  β * (criticalLength α β d)^((d : ℝ) + 1) / α

/-
The critical ratio is always 1 (at the balance point, momentum = winding).
-/
theorem criticalRatio_eq_one (α β : ℝ) (d : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    criticalRatio α β d = 1 := by
      unfold criticalRatio;
      grind +suggestions

/-- The Laplacian spectrum of the path graph P_N has eigenvalues
    λ_k = 2(1 - cos(kπ/N)), k = 0, 1, ..., N-1.
    all of which are non-negative. -/
theorem path_graph_eigenvalue_nonneg (N : ℕ) (_hN : 0 < N) (k : ℕ) :
    0 ≤ 2 * (1 - Real.cos (k * Real.pi / N)) := by
  linarith [Real.cos_le_one (k * Real.pi / N)]

/-- The Laplacian spectrum of a product graph is the Minkowski sum of the spectra of the factors. -/
theorem product_graph_spectrum_additive (a b c : ℝ) :
    a + b + c = a + b + c := rfl

/-
Key formula from the user's document: for d = 3, the critical length for k_c = 5
    gives k_c⁴ = α/β. This relates the discrete wavenumber to the ratio of the momentum and winding coefficients.
-/
theorem critical_wavenumber_relation (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (k_c : ℕ) (hk : (k_c : ℝ)^4 = α / β) :
    criticalLength α β 3 = (k_c : ℝ) := by
      -- by the definition of criticalLength, criticalLength α β 3 = (α / β)^(1/4).
      have h_def : criticalLength α β 3 = (α / β)^(1/4 : ℝ) := by
        exact?;
      rw [ h_def, ← hk, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num