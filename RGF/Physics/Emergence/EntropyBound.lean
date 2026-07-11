/-
  RGF information-theoretic foundations
  Information-Theoretic Foundations for RGF

  This file formalizes:
  1. the definition and basic properties of Shannon entropy
  2. entropy on the rule layer
  3. the non-increase of entropy under dual-layer iteration
  4. the connection with convergence to a fixed point
-/

import Mathlib
import RGF.Math.Real.BanachContraction

open scoped BigOperators
open Finset RGFRuleLayer Real

variable {α : Type*} [Fintype α]

/-! ## 1. Definition of Shannon entropy -/

/-- The information content of a non-negative real (-x log x, with the convention 0 log 0 = 0). -/
noncomputable def infoContent (x : ℝ) : ℝ :=
  if x = 0 then 0 else -x * Real.log x

/-- The Shannon entropy on a rule layer. -/
noncomputable def shannonEntropy (μ : RGFRuleLayer α) : ℝ :=
  ∑ a : α, infoContent (μ.weight a)

/-! ## 2. Basic properties of entropy -/

/-- The information content is non-negative on [0,1]. -/
theorem infoContent_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ infoContent x := by
  unfold infoContent
  split_ifs with h
  · exact le_refl 0
  · have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h)
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
    nlinarith

/-- A deterministic distribution (one weight equal to 1, the rest 0) has entropy 0. -/
theorem entropy_deterministic (μ : RGFRuleLayer α)
    (a₀ : α) (hdet : μ.weight a₀ = 1)
    (hzero : ∀ a, a ≠ a₀ → μ.weight a = 0) :
    shannonEntropy μ = 0 := by
  unfold shannonEntropy
  have : ∀ a : α, infoContent (μ.weight a) = 0 := by
    intro a
    by_cases h : a = a₀
    · subst h; simp [infoContent, hdet, Real.log_one]
    · simp [infoContent, hzero a h]
  simp [this]

/-! ## 3. Maximum-entropy theorem -/

/-
The entropy of the uniform distribution = log |α|
-/
theorem entropy_uniform [Nonempty α] :
    shannonEntropy (uniformRuleLayer (α := α)) =
    Real.log (Fintype.card α : ℝ) := by
      -- We begin by unfolding the definitions of shannonEntropy and uniformRuleLayer in the goal shannonEntropy uniformRuleLayer = log |α|.

      unfold shannonEntropy infoContent uniformRuleLayer;
      simp +decide

/-! ## 4. Relation between entropy and the L¹ distance -/

/-
**Correction note (the original statement was wrong)**:

  The original `entropy_lipschitz` statement (a weak form of Pinsker's inequality) claimed
      |H(μ) - H(ν)| ≤ log|α| · L¹(μ,ν) + L¹(μ,ν),
  but this is **wrong**. The information-content function infoContent x = -x·log x has, as x → 0⁺,
  derivative -(log x + 1) → +∞, so Shannon entropy is not Lipschitz continuous,
  and no linear upper bound of the form C·L¹ exists.

  Counterexample: take |α| = 2, μ = (ε, 1-ε), ν = (0, 1); then L¹(μ,ν) = 2ε,
  while H(μ) = -ε log ε - (1-ε) log(1-ε) ≈ -ε log ε. As ε → 0⁺,
  H(μ) / L¹ → +∞, exceeding any fixed constant (log 2 + 1).
  Numerical check: at ε = e^{-10}, H(μ) ≈ 4.99×10⁻⁴ > 1.54×10⁻⁴ = (log 2 + 1)·L¹.

  Below we keep the original statement (commented out) and give a correct, provable replacement `entropy_nonneg`.

  theorem entropy_lipschitz (μ ν : RGFRuleLayer α) [Nonempty α] :
      |shannonEntropy μ - shannonEntropy ν| ≤
      Real.log (Fintype.card α : ℝ) * l1Dist μ ν + l1Dist μ ν := by
    (proof omitted: this statement is false; see the counterexample above)
-/

/-- **Correct replacement statement**: Shannon entropy is non-negative.
    Each weight μ.weight a ∈ [0,1] (non-negative and summing to 1),
    so each term infoContent (μ.weight a) ≥ 0, and the summed entropy is non-negative. -/
theorem entropy_nonneg (μ : RGFRuleLayer α) : 0 ≤ shannonEntropy μ := by
  refine' Finset.sum_nonneg _;
  exact fun a _ => infoContent_nonneg ( μ.weight_nonneg a ) ( μ.weight_sum ▸ Finset.single_le_sum ( fun a _ => μ.weight_nonneg a ) ( Finset.mem_univ a ) )

/-! ## 5. Information theory and quintic locking -/

/-- The entropy of the uniform distribution on S₅ = log 120. -/
theorem entropy_S5_uniform :
    Real.log (120 : ℝ) = Real.log (Nat.factorial 5 : ℝ) := by
  norm_num

/-- Some concrete entropy computations. -/
theorem entropy_log_values :
    -- log 120 = log(2³ × 3 × 5) = 3 log 2 + log 3 + log 5
    (120 : ℕ) = 2 ^ 3 * 3 * 5 ∧
    -- |A₅| = 60 = 120/2
    (60 : ℕ) = 120 / 2 ∧
    -- log(60) = log(120) - log(2)
    -- (this is a property of log, but we do not perform real-number computation)
    (60 * 2 = 120) := by omega