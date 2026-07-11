/-
  Foundations/RGFvsZFC.lean — genuine RGF theorems

  All results are derived from the genuine dual-layer iteration axioms defined in Axioms.Basic:
  RGF, RuleLayer, DualLayerSystem.
  nothing is assumed — every theorem follows from genuine RGF.
-/

import Mathlib
import RGF.Generative.Core.RGFBasic

open scoped BigOperators
open Finset

noncomputable section

/-! ## Part 1: the metric-space structure of RuleLayer

  The genuine RGF RuleLayer carries a natural L¹ metric.
  We prove it satisfies the metric-space axioms. -/

/-- The L¹ distance on RuleLayer. -/
def RuleLayer.l1Dist {α : Type} [Fintype α] (μ ν : RuleLayer α) : ℝ :=
  ∑ a : α, |μ.weight a - ν.weight a|

theorem RuleLayer.l1Dist_nonneg {α : Type} [Fintype α] (μ ν : RuleLayer α) :
    0 ≤ μ.l1Dist ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem RuleLayer.l1Dist_symm {α : Type} [Fintype α] (μ ν : RuleLayer α) :
    μ.l1Dist ν = ν.l1Dist μ := by
  simp only [l1Dist, abs_sub_comm]

theorem RuleLayer.l1Dist_self {α : Type} [Fintype α] (μ : RuleLayer α) :
    μ.l1Dist μ = 0 := by
  simp [l1Dist]

/-- The L¹ distance is bounded above by 2 (since the weights sum to 1). -/
theorem RuleLayer.l1Dist_le_two {α : Type} [Fintype α] (μ ν : RuleLayer α) :
    μ.l1Dist ν ≤ 2 := by
  unfold l1Dist
  have h1 : ∑ a : α, |μ.weight a - ν.weight a| ≤ ∑ a : α, (μ.weight a + ν.weight a) := by
    apply Finset.sum_le_sum; intro a _
    rw [abs_le]
    constructor <;> linarith [μ.weight_nonneg a, ν.weight_nonneg a]
  have h2 : ∑ a : α, (μ.weight a + ν.weight a) = 2 := by
    rw [Finset.sum_add_distrib, μ.weight_sum, ν.weight_sum]; ring
  linarith

/-- The triangle inequality for the L¹ distance on RuleLayer. -/
theorem RuleLayer.l1Dist_triangle {α : Type} [Fintype α]
    (μ ν ρ : RuleLayer α) :
    μ.l1Dist ρ ≤ μ.l1Dist ν + ν.l1Dist ρ := by
  unfold l1Dist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro a _
  exact abs_sub_le (μ.weight a) (ν.weight a) (ρ.weight a)

/-! ## Part 2: dual-layer iteration — the core dynamics

  Theorems about the iteration of a genuine DualLayerSystem. -/

/-- A fixed point is preserved under iteration. -/
theorem DualLayerSystem.iterate_of_fixedPoint {α : Type} [Fintype α]
    (sys : DualLayerSystem α) (z : RuleLayer α)
    (hz : sys.IsFixedPoint z) (n : ℕ) :
    sys.iterate z n = z := by
  induction n with
  | zero => rfl
  | succ n ih => exact show sys.step (sys.iterate z n) = z by rw [ih, hz]

/-- Two iterations starting from a fixed point always agree. -/
theorem DualLayerSystem.iterate_fixedPoint_const {α : Type} [Fintype α]
    (sys : DualLayerSystem α) (z : RuleLayer α)
    (hz : sys.IsFixedPoint z) (n m : ℕ) :
    sys.iterate z n = sys.iterate z m := by
  rw [sys.iterate_of_fixedPoint z hz n, sys.iterate_of_fixedPoint z hz m]

/-! ## Part 3: contractive dual-layer systems

  When the dual-layer step is a contraction in L¹, we obtain
  exponential convergence and a unique fixed point. -/

/-- A distance-contracting DualLayerSystem. -/
structure ContractiveDLS (α : Type) [Fintype α] where
  sys : DualLayerSystem α
  c : ℝ
  hc_nn : 0 ≤ c
  hc_lt : c < 1
  hcontract : ∀ μ ν : RuleLayer α,
    (sys.step μ).l1Dist (sys.step ν) ≤ c * μ.l1Dist ν

/-- Exponential decay of the distance under contractive iteration. -/
theorem ContractiveDLS.iterate_decay {α : Type} [Fintype α]
    (S : ContractiveDLS α) (μ ν : RuleLayer α) (n : ℕ) :
    (S.sys.iterate μ n).l1Dist (S.sys.iterate ν n) ≤ S.c ^ n * μ.l1Dist ν := by
  induction n with
  | zero => simp [DualLayerSystem.iterate]
  | succ n ih =>
    simp only [DualLayerSystem.iterate, DualLayerSystem.step]
    calc (S.sys.modify (S.sys.generate (S.sys.iterate μ n))).l1Dist
          (S.sys.modify (S.sys.generate (S.sys.iterate ν n)))
        ≤ S.c * (S.sys.iterate μ n).l1Dist (S.sys.iterate ν n) :=
          S.hcontract _ _
      _ ≤ S.c * (S.c ^ n * μ.l1Dist ν) := by
          apply mul_le_mul_of_nonneg_left ih S.hc_nn
      _ = S.c ^ (n + 1) * μ.l1Dist ν := by ring

/-- Uniqueness of the fixed point: the L¹ distance between two fixed points is 0. -/
theorem ContractiveDLS.fixedPoint_unique {α : Type} [Fintype α]
    (S : ContractiveDLS α) (z₁ z₂ : RuleLayer α)
    (h₁ : S.sys.IsFixedPoint z₁) (h₂ : S.sys.IsFixedPoint z₂) :
    z₁.l1Dist z₂ = 0 := by
  have hc := S.hcontract z₁ z₂
  rw [h₁, h₂] at hc
  by_contra h
  have hpos : 0 < z₁.l1Dist z₂ :=
    lt_of_le_of_ne (RuleLayer.l1Dist_nonneg z₁ z₂) (Ne.symm h)
  nlinarith [S.hc_lt]

/-- Convergence to the fixed point: the distance to z* decays exponentially. -/
theorem ContractiveDLS.convergence_rate {α : Type} [Fintype α]
    (S : ContractiveDLS α) (z zstar : RuleLayer α)
    (hstar : S.sys.IsFixedPoint zstar) (n : ℕ) :
    (S.sys.iterate z n).l1Dist zstar ≤ S.c ^ n * z.l1Dist zstar := by
  have h := S.iterate_decay z zstar n
  rw [S.sys.iterate_of_fixedPoint zstar hstar n] at h
  exact h

/-! ## Part 4: boundedness of weights (probability conservation)

  Dual-layer iteration preserves the probability structure at every step. -/

/-- The weights always lie in [0,1] at every step. -/
theorem DualLayerSystem.iterate_weights_in_unit {α : Type} [Fintype α]
    (sys : DualLayerSystem α) (r : RuleLayer α) (n : ℕ) (a : α) :
    0 ≤ (sys.iterate r n).weight a ∧ (sys.iterate r n).weight a ≤ 1 :=
  ⟨(sys.iterate r n).weight_nonneg a, (sys.iterate r n).weight_le_one a⟩

/-- The weights sum to 1 at every step (total probability is conserved). -/
theorem DualLayerSystem.iterate_total_weight {α : Type} [Fintype α]
    (sys : DualLayerSystem α) (r : RuleLayer α) (n : ℕ) :
    ∑ a : α, (sys.iterate r n).weight a = 1 :=
  (sys.iterate r n).weight_sum

/-! ## Part 5: the symmetry factor from orbit-stabilizer

  The RGF symmetry factor σ(s) = |orbit(s)|/|G|
  connects the dual-layer system with group actions. -/

/-- The symmetry factor based on orbit-stabilizer. -/
def rgfSymmetryFactor' {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s : S) : ℝ :=
  1 / (Nat.card (MulAction.stabilizer G s) : ℝ)

/-- The symmetry factor is positive. -/
theorem rgfSymmetryFactor'_pos {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s : S) :
    0 < rgfSymmetryFactor' (G := G) s := by
  unfold rgfSymmetryFactor'
  apply div_pos one_pos
  exact_mod_cast Nat.card_pos

/-- The symmetry factor is at most 1. -/
theorem rgfSymmetryFactor'_le_one {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s : S) :
    rgfSymmetryFactor' (G := G) s ≤ 1 := by
  unfold rgfSymmetryFactor'
  rw [div_le_one (by exact_mod_cast @Nat.card_pos (MulAction.stabilizer G s) ⟨⟨1, one_mem _⟩⟩ _)]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'

/-- The symmetry factor is invariant along an orbit. -/
theorem rgfSymmetryFactor'_orbit_inv {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s : S) (g : G) :
    rgfSymmetryFactor' (G := G) (g • s) = rgfSymmetryFactor' (G := G) s := by
  unfold rgfSymmetryFactor'
  congr 1
  exact_mod_cast Nat.card_congr
    (MulAction.stabilizerEquivStabilizerOfOrbitRel
      (show s ∈ MulAction.orbit G (g • s) from ⟨g⁻¹, by simp⟩)).toEquiv.symm

/-! ## Part 6: the emergent-probability functional

  The RGF emergent probability ρ(n)·ξ(s) factors into
  a temporal factor and a spatial factor. -/

/-- Emergent probability: the product of the temporal density and the spatial weight. -/
def emergProb (ρ : ℕ → ℝ) (ξ : α → ℝ) (s : α) (n : ℕ) : ℝ :=
  ρ n * ξ s

/-- If the temporal density decays exponentially and the spatial weight is bounded,
    then the emergent probability is controlled by an exponential envelope. -/
theorem emergProb_exp_bound {α : Type}
    (c : ℝ) (hc0 : 0 ≤ c)
    (ρ₀ : ℝ) (hρ₀ : 0 ≤ ρ₀)
    (ξ : α → ℝ) (hξ : ∀ s, |ξ s| ≤ 1)
    (s : α) (n : ℕ) :
    |emergProb (fun n => ρ₀ * c ^ n) ξ s n| ≤ ρ₀ * c ^ n := by
  unfold emergProb
  rw [abs_mul]
  calc |ρ₀ * c ^ n| * |ξ s|
      ≤ |ρ₀ * c ^ n| * 1 := by
        apply mul_le_mul_of_nonneg_left (hξ s) (abs_nonneg _)
    _ = |ρ₀ * c ^ n| := mul_one _
    _ = ρ₀ * c ^ n := abs_of_nonneg (mul_nonneg hρ₀ (pow_nonneg hc0 n))

/-- The total emergent probability over all states equals ρ(n) times the total spatial weight. -/
theorem emergProb_total_sum {α : Type} [Fintype α]
    (ρ : ℕ → ℝ) (ξ : α → ℝ) (n : ℕ) :
    ∑ s : α, emergProb ρ ξ s n = ρ n * ∑ s : α, ξ s := by
  simp [emergProb, Finset.mul_sum]

end
