/-
  Layer 2: application of the Banach contraction-mapping principle to the rule layer
  Recursive Generation Foundations (RGF)
-/

import Mathlib

open scoped BigOperators
open Finset

structure RGFRuleLayer (α : Type*) [Fintype α] where
  weight : α → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a : α, weight a = 1

namespace RGFRuleLayer

variable {α : Type*} [Fintype α]

noncomputable def l1Dist (μ ν : RGFRuleLayer α) : ℝ :=
  ∑ a : α, |μ.weight a - ν.weight a|

theorem l1Dist_nonneg (μ ν : RGFRuleLayer α) : 0 ≤ l1Dist μ ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1Dist_symm (μ ν : RGFRuleLayer α) : l1Dist μ ν = l1Dist ν μ := by
  simp only [l1Dist, abs_sub_comm]

theorem l1Dist_triangle (μ ν ρ : RGFRuleLayer α) :
    l1Dist μ ρ ≤ l1Dist μ ν + l1Dist ν ρ := by
  unfold RGFRuleLayer.l1Dist;
  simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun a _ => abs_sub_le _ _ _

theorem l1Dist_eq_zero_of_eq (μ ν : RGFRuleLayer α) (h : μ.weight = ν.weight) :
    l1Dist μ ν = 0 := by
  unfold l1Dist; simp [h]

theorem l1Dist_le_two (μ ν : RGFRuleLayer α) : l1Dist μ ν ≤ 2 := by
  refine' le_trans ( Finset.sum_le_sum fun a _ => show |μ.weight a - ν.weight a| ≤ μ.weight a + ν.weight a from _ ) _;
  · exact abs_le.mpr ⟨ by linarith [ μ.weight_nonneg a, ν.weight_nonneg a ], by linarith [ μ.weight_nonneg a, ν.weight_nonneg a ] ⟩;
  · rw [ Finset.sum_add_distrib, μ.weight_sum, ν.weight_sum ] ; norm_num

structure RGFContraction (α : Type*) [Fintype α] where
  step : RGFRuleLayer α → RGFRuleLayer α
  contractCoeff : ℝ
  coeff_nonneg : 0 ≤ contractCoeff
  coeff_lt_one : contractCoeff < 1
  contract : ∀ μ ν : RGFRuleLayer α,
    l1Dist (step μ) (step ν) ≤ contractCoeff * l1Dist μ ν

def RGFContraction.iterate (sys : RGFContraction α) (z : RGFRuleLayer α) : ℕ → RGFRuleLayer α
  | 0 => z
  | n + 1 => sys.step (sys.iterate z n)

def RGFContraction.IsFixedPoint (sys : RGFContraction α) (z : RGFRuleLayer α) : Prop :=
  sys.step z = z

/-- The iteration distance decays exponentially. -/
theorem RGFContraction.iterate_distance_bound (sys : RGFContraction α)
    (μ ν : RGFRuleLayer α) (n : ℕ) :
    l1Dist (sys.iterate μ n) (sys.iterate ν n) ≤ sys.contractCoeff ^ n * l1Dist μ ν := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    simp only [iterate]
    calc l1Dist (sys.step (sys.iterate μ n)) (sys.step (sys.iterate ν n))
        ≤ sys.contractCoeff * l1Dist (sys.iterate μ n) (sys.iterate ν n) := sys.contract _ _
      _ ≤ sys.contractCoeff * (sys.contractCoeff ^ n * l1Dist μ ν) :=
          mul_le_mul_of_nonneg_left ih sys.coeff_nonneg
      _ = sys.contractCoeff ^ (n + 1) * l1Dist μ ν := by ring

/-
Uniqueness of the fixed point (in the L¹ sense)
-/
theorem RGFContraction.fixedPoint_unique_l1 (sys : RGFContraction α)
    (z₁ z₂ : RGFRuleLayer α)
    (h₁ : sys.IsFixedPoint z₁) (h₂ : sys.IsFixedPoint z₂) :
    l1Dist z₁ z₂ = 0 := by
  have := sys.contract z₁ z₂;
  by_cases h_pos : 0 < z₁.l1Dist z₂;
  · rw [ h₁, h₂ ] at this ; nlinarith [ sys.coeff_lt_one ];
  · exact le_antisymm ( le_of_not_gt h_pos ) ( RGFRuleLayer.l1Dist_nonneg _ _ )

/-- The fixed point is invariant under iteration. -/
theorem RGFContraction.iterate_fixedPoint (sys : RGFContraction α)
    (zstar : RGFRuleLayer α) (hstar : sys.IsFixedPoint zstar) :
    ∀ n, sys.iterate zstar n = zstar := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact show sys.step (sys.iterate zstar n) = zstar by rw [ih, hstar]

/-- Convergence rate. -/
theorem RGFContraction.convergence_rate (sys : RGFContraction α)
    (z zstar : RGFRuleLayer α) (hstar : sys.IsFixedPoint zstar) (n : ℕ) :
    l1Dist (sys.iterate z n) zstar ≤ sys.contractCoeff ^ n * l1Dist z zstar := by
  have h := sys.iterate_distance_bound z zstar n
  rw [sys.iterate_fixedPoint zstar hstar n] at h
  exact h

noncomputable def uniformRuleLayer [Nonempty α] : RGFRuleLayer α where
  weight := fun _ => 1 / (Fintype.card α : ℝ)
  weight_nonneg := fun _ => by positivity
  weight_sum := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_div_cancel₀]
    exact_mod_cast Fintype.card_pos.ne'

end RGFRuleLayer