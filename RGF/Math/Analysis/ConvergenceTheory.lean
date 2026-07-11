/-
  RGF convergence theory
  Convergence Theory for Recursive Generation Foundations

  This file formalizes:
  1. convergence-rate estimates for contraction maps
  2. stability analysis of fixed points
  3. geometric-series bounds for the iteration distance
-/

import Mathlib
import RGF.Math.Real.BanachContraction

open scoped BigOperators
open Finset RGFRuleLayer

variable {α : Type*} [Fintype α]

/-! ## 1. Geometric-series bound -/

/-- The finite sum of a geometric series is ≤ 1/(1-q). -/
theorem geom_sum_le_inv (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑ k ∈ range N, q ^ k ≤ 1 / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  rw [le_div_iff₀ h1q]
  have := geom_sum_mul_of_le_one (le_of_lt hq1) N
  linarith [pow_nonneg hq0 N]

/-! ## 2. Stability of fixed points -/

/-- The fixed point is Lyapunov stable. -/
theorem fixpoint_stable (sys : RGFContraction α)
    (zstar : RGFRuleLayer α) (hstar : sys.IsFixedPoint zstar)
    (z : RGFRuleLayer α) (n : ℕ) :
    l1Dist (sys.iterate z n) zstar ≤ sys.contractCoeff ^ n * l1Dist z zstar :=
  sys.convergence_rate z zstar hstar n

/-- An upper bound on the diameter of the fixed point's basin of attraction. -/
theorem fixpoint_basin_diameter (sys : RGFContraction α)
    (z₁ z₂ : RGFRuleLayer α) (n : ℕ) :
    l1Dist (sys.iterate z₁ n) (sys.iterate z₂ n) ≤
    sys.contractCoeff ^ n * l1Dist z₁ z₂ :=
  sys.iterate_distance_bound z₁ z₂ n

/-! ## 3. Convergence to the fixed point -/

/-
For any ε > 0, there exists N such that for n ≥ N the iterate is within ε of the fixed point
-/
theorem fixpoint_convergence_eps (sys : RGFContraction α)
    (zstar : RGFRuleLayer α) (hstar : sys.IsFixedPoint zstar)
    (z : RGFRuleLayer α) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      l1Dist (sys.iterate z n) zstar < ε := by
        obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, sys.contractCoeff ^ n * RGFRuleLayer.l1Dist z zstar < ε := by
          simpa using ( summable_geometric_of_lt_one ( sys.coeff_nonneg ) sys.coeff_lt_one ) |> fun h => h.mul_right _ |> fun h => h.tendsto_atTop_zero.eventually ( gt_mem_nhds hε );
        exact ⟨ N, fun n hn => lt_of_le_of_lt ( fixpoint_stable sys zstar hstar z n ) ( hN n hn ) ⟩

/-! ## 4. Mixing-time bound -/

/-- If q^n * D < ε, then after n steps the iterate is within ε of the fixed point. -/
theorem mixing_time_bound (sys : RGFContraction α)
    (zstar z : RGFRuleLayer α) (hstar : sys.IsFixedPoint zstar)
    (ε : ℝ) (n : ℕ)
    (hn : sys.contractCoeff ^ n * l1Dist z zstar < ε) :
    l1Dist (sys.iterate z n) zstar < ε :=
  lt_of_le_of_lt (fixpoint_stable sys zstar hstar z n) hn

/-! ## 5. Comparison of convergence rates -/

/-- A smaller contraction coefficient gives faster convergence. -/
theorem smaller_contraction_faster
    (q₁ q₂ : ℝ) (hq1 : 0 ≤ q₁)
    (hlt : q₁ ≤ q₂) (D : ℝ) (hD : 0 ≤ D) (n : ℕ) :
    q₁ ^ n * D ≤ q₂ ^ n * D :=
  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq1 hlt n) hD

/-- As the number of iterations increases, the upper bound on the distance does not increase. -/
theorem iterate_bound_monotone (sys : RGFContraction α)
    (zstar : RGFRuleLayer α) (_hstar : sys.IsFixedPoint zstar)
    (z : RGFRuleLayer α) (m n : ℕ) (hmn : m ≤ n) :
    sys.contractCoeff ^ n * l1Dist z zstar ≤
    sys.contractCoeff ^ m * l1Dist z zstar := by
  apply mul_le_mul_of_nonneg_right _ (l1Dist_nonneg z zstar)
  exact pow_le_pow_of_le_one sys.coeff_nonneg (le_of_lt sys.coeff_lt_one) hmn

/-- Summary of convergence rates. -/
theorem exponential_convergence_summary (sys : RGFContraction α)
    (zstar : RGFRuleLayer α) (hstar : sys.IsFixedPoint zstar)
    (z : RGFRuleLayer α) :
    (∀ n, l1Dist (sys.iterate z n) zstar ≤ sys.contractCoeff ^ n * l1Dist z zstar) ∧
    (∀ z', sys.IsFixedPoint z' → l1Dist zstar z' = 0) ∧
    (l1Dist z zstar ≤ 2) :=
  ⟨fun n => fixpoint_stable sys zstar hstar z n,
   fun z' hz' => sys.fixedPoint_unique_l1 zstar z' hstar hz',
   l1Dist_le_two z zstar⟩