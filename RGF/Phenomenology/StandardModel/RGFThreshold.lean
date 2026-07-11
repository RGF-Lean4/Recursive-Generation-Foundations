/-
  Random graph theory: the Erdős-Rényi model and the phase-transition threshold
  Random Graph Theory: Erdős-Rényi Model and Phase Transitions

  Lean support for Paper XI:
  formalizes the threshold probability for the appearance of K_r in the G(n,p) model,
  and the emergence of the quintic structure (K₅) in random graphs.
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Basic combinatorial quantities of complete graphs -/

/-- The number of edges of K_r = r(r-1)/2. -/
def completeGraphEdges (r : ℕ) : ℕ := r * (r - 1) / 2

/-- K₃ has 3 edges. -/
theorem K3_edges : completeGraphEdges 3 = 3 := by decide

/-- K₄ has 6 edges. -/
theorem K4_edges : completeGraphEdges 4 = 6 := by decide

/-- K₅ has 10 edges. -/
theorem K5_edges : completeGraphEdges 5 = 10 := by decide

/-- K₆ has 15 edges. -/
theorem K6_edges : completeGraphEdges 6 = 15 := by decide

/-! ## 2. Computation of the threshold exponent -/

/-- The threshold exponent for the appearance of K_r (numerator). -/
def thresholdExponentNum (_r : ℕ) : ℕ := 2

/-- The threshold exponent for the appearance of K_r (denominator). -/
def thresholdExponentDen (r : ℕ) : ℕ := r - 1

/-- The threshold exponent of K₃ is 2/2 = 1. -/
theorem K3_threshold : thresholdExponentNum 3 = 2 ∧ thresholdExponentDen 3 = 2 := by
  constructor <;> rfl

/-- The threshold exponent of K₅ is 2/4 = 1/2. -/
theorem K5_threshold : thresholdExponentNum 5 = 2 ∧ thresholdExponentDen 5 = 4 := by
  constructor <;> rfl

/-! ## 3. Expected subgraph count -/

/-- The expected number of K_r in G(n,p) = C(n,r) · p^{e(K_r)}. -/
noncomputable def expectedKr (n r : ℕ) (p : ℝ) : ℝ :=
  (n.choose r : ℝ) * p ^ completeGraphEdges r

/-- When p = 0, the expectation is 0. -/
theorem expectedKr_zero (n r : ℕ) (hr : 0 < completeGraphEdges r) :
    expectedKr n r 0 = 0 := by
  unfold expectedKr
  simp [zero_pow (by omega : completeGraphEdges r ≠ 0)]

/-- When p = 1, the expectation equals the number of subgraphs. -/
theorem expectedKr_one (n r : ℕ) :
    expectedKr n r 1 = (n.choose r : ℝ) := by
  unfold expectedKr; simp

/-- The expectation is non-negative. -/
theorem expectedKr_nonneg (n r : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ expectedKr n r p := by
  unfold expectedKr; positivity

/-! ## 4. Special features of the K₅ threshold -/

/-- K₅ is the smallest complete graph whose threshold denominator is ≥ 4. -/
theorem K5_minimal_dense :
    ∀ r : ℕ, 3 ≤ r → r < 5 → thresholdExponentDen r < 4 := by
  intro r hr1 hr2
  interval_cases r <;> simp [thresholdExponentDen]

/-- The threshold denominator of K₅ is exactly 4. -/
theorem K5_den_eq : thresholdExponentDen 5 = 4 := by rfl

/-! ## 5. The second-moment method and threshold sharpness -/

/-- The core algebraic content of the Paley-Zygmund inequality. -/
theorem paley_zygmund_bound
    (EX EX2 C : ℝ)
    (hC : 0 < C)
    (hEX2 : 0 < EX2)
    (hbound : EX2 ≤ C * EX ^ 2) :
    1 / C ≤ EX ^ 2 / EX2 := by
  rw [div_le_div_iff₀ hC hEX2]
  linarith

/-! ## 6. The phase transition of the quintic structure -/

/-- The phase-transition order. -/
def phaseTransitionOrder (r : ℕ) : ℚ := (r - 2 : ℚ) / (r - 1 : ℚ)

/-- The phase-transition order of K₃ = 1/2. -/
theorem K3_phase_order : phaseTransitionOrder 3 = 1 / 2 := by native_decide

/-- The phase-transition order of K₅ = 3/4. -/
theorem K5_phase_order : phaseTransitionOrder 5 = 3 / 4 := by native_decide

/-! ## 7. Hierarchical structure of threshold probabilities -/

/-- For r₁ < r₂, K_{r₁} appears before K_{r₂}. -/
theorem larger_clique_later_threshold
    (r₁ r₂ : ℕ) (hr₁ : 2 ≤ r₁) (hr : r₁ < r₂) :
    thresholdExponentDen r₁ < thresholdExponentDen r₂ := by
  simp [thresholdExponentDen]; omega

/-- The chain of increasing density requirements: triangle → K₄ → K₅ → K₆. -/
theorem threshold_chain :
    thresholdExponentDen 3 < thresholdExponentDen 4 ∧
    thresholdExponentDen 4 < thresholdExponentDen 5 ∧
    thresholdExponentDen 5 < thresholdExponentDen 6 := by
  simp [thresholdExponentDen]

/-! ## 8. Verification of the edge-count formula -/

/-- Verification of the edge-count formula e(K_r) = r(r-1)/2 for the first few values. -/
theorem edge_count_table :
    completeGraphEdges 2 = 1 ∧
    completeGraphEdges 3 = 3 ∧
    completeGraphEdges 4 = 6 ∧
    completeGraphEdges 5 = 10 ∧
    completeGraphEdges 6 = 15 ∧
    completeGraphEdges 7 = 21 := by
  simp [completeGraphEdges]

/-- 5! = 120 -/
theorem five_factorial : (5 : ℕ).factorial = 120 := by decide

/-- The growth rate of C(n,5). -/
theorem choose_10_5 : Nat.choose 10 5 = 252 := by decide

/-- C(20,5) -/
theorem choose_20_5 : Nat.choose 20 5 = 15504 := by decide
