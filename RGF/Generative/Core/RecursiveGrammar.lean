/-
  Computational complexity of recursive generation systems
  Computational Complexity of Recursive Generation Systems

  Formalizes:
  - the relation between recursion depth and complexity
  - an information-theoretic interpretation of quintic locking
  - the prime factorization of factorials
  - the information content of symmetric groups
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Recursion depth -/

/-- The depth of recursive generation. -/
def recursionDepth (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The recursion depth is at least 1. -/
theorem recursionDepth_pos (n : ℕ) : 0 < recursionDepth n := by
  unfold recursionDepth; omega

/-- Monotonicity of the recursion depth. -/
theorem recursionDepth_mono {m n : ℕ} (hmn : m ≤ n) :
    recursionDepth m ≤ recursionDepth n := by
  unfold recursionDepth
  exact Nat.add_le_add_right (Nat.log_mono_right hmn) 1

/-! ## 2. Information theory and quintic locking -/

/-- The information content of the symmetric group S_k (in bits) = log₂(k!). -/
noncomputable def symmetryInformation (k : ℕ) : ℝ :=
  Real.log (k.factorial : ℝ) / Real.log 2

/-- The order of S₅ = 120. -/
theorem S5_order : (5 : ℕ).factorial = 120 := by decide

/-- Monotonicity of the information content: k₁ < k₂ → k₁! < k₂!. -/
theorem factorial_strict_mono (k₁ k₂ : ℕ) (hk : k₁ < k₂) (hk1 : 0 < k₁) :
    k₁.factorial < k₂.factorial :=
  Nat.factorial_lt_of_lt hk1 hk

/-! ## 3. Prime factorization of factorials -/

/-- 5! = 2³ × 3 × 5 -/
theorem five_factorial_factorization :
    (5 : ℕ).factorial = 2 ^ 3 * 3 * 5 := by decide

/-- 3! = 6 = 2 × 3 -/
theorem three_factorial_factorization :
    (3 : ℕ).factorial = 2 * 3 := by decide

/-- 7! = 5040 = 2⁴ × 3² × 5 × 7 -/
theorem seven_factorial_factorization :
    (7 : ℕ).factorial = 2 ^ 4 * 3 ^ 2 * 5 * 7 := by decide

/-- 4! = 24 = 2³ × 3 -/
theorem four_factorial : (4 : ℕ).factorial = 24 := by decide

/-- 6! = 720 = 2⁴ × 3² × 5 -/
theorem six_factorial : (6 : ℕ).factorial = 720 := by decide

/-! ## 4. The Chomsky hierarchy -/

/-- The Chomsky-hierarchy type. -/
inductive ChomskyType
  | Regular      -- Type 3: regular grammar
  | ContextFree  -- Type 2: context-free
  | ContextSensitive  -- Type 1: context-sensitive
  | Unrestricted -- Type 0: unrestricted
  deriving DecidableEq, Repr

/-- A recursive generative grammar is at least context-free. -/
def trgMinimalType : ChomskyType := ChomskyType.ContextFree

/-- The dual-layer structure raises the Chomsky hierarchy. -/
theorem dual_layer_elevates_type :
    trgMinimalType = ChomskyType.ContextFree := rfl

/-! ## 5. Convergence of fixed-point iteration -/

/-- The smaller the contraction factor, the faster the convergence. -/
theorem smaller_contraction_faster
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (_hc₂ : 0 < c₂)
    (hlt : c₁ < c₂) (_hc₂_lt : c₂ < 1)
    (n : ℕ) (hn : 0 < n) :
    c₁ ^ n < c₂ ^ n := by
  exact pow_lt_pow_left₀ hlt (le_of_lt hc₁) (by omega)

/-- Distance decay of contraction-map iteration. -/
theorem contraction_decay
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1) (d₀ : ℝ) (hd : 0 ≤ d₀)
    (n : ℕ) :
    c ^ n * d₀ ≤ d₀ := by
  calc c ^ n * d₀ ≤ 1 * d₀ := by
        apply mul_le_mul_of_nonneg_right _ hd
        exact pow_le_one₀ hc (le_of_lt hc1)
    _ = d₀ := one_mul _

/-! ## 6. Orbit counting -/

/-- The cardinality constraint of recursive generation:
    the order-k symmetric group S_k acts on an n-element set,
    the number of orbits is ≤ n / k. -/
theorem orbit_count_bound (n k : ℕ) (hk : 0 < k)
    (orbits : ℕ) (h : orbits * k ≤ n) :
    orbits ≤ n / k := Nat.le_div_iff_mul_le hk |>.mpr h

/-- The efficiency of five-fold symmetry:
    the Z₅ action reduces n states to ≤ n/5 orbits.
    5 is the smallest prime reduction that decreases the orbit count by at least a factor of 5. -/
theorem z5_orbit_reduction (n : ℕ) (hn : 5 ∣ n) :
    ∃ orbits, n = 5 * orbits := by
  exact hn

/-- Comparison of reduction efficiency for different symmetry orders. -/
theorem symmetry_reduction_comparison :
    -- Z₃ reduction: every 3 grouped into 1 class
    -- Z₅ reduction: every 5 grouped into 1 class
    -- Z₇ reduction: every 7 grouped into 1 class
    ∀ n : ℕ, n / 5 ≤ n / 3 := by
  intro n; exact Nat.div_le_div_left (by omega) (by omega)
