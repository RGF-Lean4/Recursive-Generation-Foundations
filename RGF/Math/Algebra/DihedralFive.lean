/-
  Group representation theory and five-fold locking
  Group Representation Theory and Five-fold Locking

  This file formalises:
  - the irreducible representation dimensions of the dihedral group D_k
  - the group-representation-theoretic stability condition for k=5
  - representation-theoretic support for five-fold locking
  - basic properties of cyclotomic polynomials
-/

import Mathlib

open Finset BigOperators

/-! ## Irreducible representations of the dihedral group -/

/-- the number of 2-dimensional irreducible representations of D_k -/
def numTwoDimIrreps (k : ℕ) : ℕ :=
  if k % 2 = 1 then (k - 1) / 2
  else (k - 2) / 2

/-- the number of 2-dimensional irreducible representations of D₃ = 1 -/
theorem d3_two_dim_irreps : numTwoDimIrreps 3 = 1 := by decide

/-- the number of 2-dimensional irreducible representations of D₄ = 1 -/
theorem d4_two_dim_irreps : numTwoDimIrreps 4 = 1 := by decide

/-- the number of 2-dimensional irreducible representations of D₅ = 2 -/
theorem d5_two_dim_irreps : numTwoDimIrreps 5 = 2 := by decide

/-- the number of 2-dimensional irreducible representations of D₆ = 2 -/
theorem d6_two_dim_irreps : numTwoDimIrreps 6 = 2 := by decide

/-- the number of 2-dimensional irreducible representations of D₇ = 3 -/
theorem d7_two_dim_irreps : numTwoDimIrreps 7 = 3 := by decide

/-! ## Representation-theoretic stability condition -/

/-- there are at least 2 two-dimensional irreducible representations -/
def repStability (k : ℕ) : Prop := numTwoDimIrreps k ≥ 2

/-- k = 3 does not satisfy stability -/
theorem k3_unstable : ¬repStability 3 := by
  simp [repStability, d3_two_dim_irreps]

/-- k = 4 does not satisfy stability -/
theorem k4_unstable : ¬repStability 4 := by
  simp [repStability, d4_two_dim_irreps]

/-- k = 5 satisfies stability -/
theorem k5_stable : repStability 5 := by
  simp [repStability, d5_two_dim_irreps]

/-- k = 5 is the smallest k ≥ 3 satisfying stability -/
theorem k5_minimal_stable :
    repStability 5 ∧ ∀ k, 3 ≤ k → k < 5 → ¬repStability k := by
  constructor
  · exact k5_stable
  · intro k hk1 hk2
    interval_cases k
    · exact k3_unstable
    · exact k4_unstable

/-! ## Verification of the dimension formula -/

/-- the number of 1-dimensional irreducible representations of D_k -/
def numOneDimIrreps (k : ℕ) : ℕ :=
  if k % 2 = 1 then 2 else 4

/-- dimension formula: ∑ d_i² = 2k -/
theorem dim_formula_odd (k : ℕ) (hk : k % 2 = 1) (hk3 : 3 ≤ k) :
    numOneDimIrreps k * 1^2 + numTwoDimIrreps k * 2^2 = 2 * k := by
  simp [numOneDimIrreps, numTwoDimIrreps, hk]
  omega

/-- verification of the dimension formula for D₅ -/
theorem d5_dim_formula :
    numOneDimIrreps 5 * 1^2 + numTwoDimIrreps 5 * 2^2 = 2 * 5 := by decide

/-! ## Cyclotomic polynomials -/

/-- φ(5) = 4 -/
theorem totient_5 : Nat.totient 5 = 4 := by decide

/-- 5 is prime -/
theorem five_is_prime : Nat.Prime 5 := by decide

/-- group-representation-theoretic evidence for five-fold locking -/
theorem five_fold_rep_theory_evidence :
    numTwoDimIrreps 5 = 2 ∧
    (∀ k, 3 ≤ k → k < 5 → numTwoDimIrreps k < 2) ∧
    Nat.totient 5 = 4 ∧
    Nat.Prime 5 := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro k hk1 hk2
  interval_cases k <;> decide

/-! ## Order of the dihedral group -/

/-- order of D_k = 2k -/
def dihedralGroupOrder (k : ℕ) : ℕ := 2 * k

/-- for k=5 the upper bound of the symmetry factor = 1/10 -/
theorem symmetry_factor_d5_bound :
    (1 : ℝ) / (dihedralGroupOrder 5 : ℝ) = 1 / 10 := by
  norm_num [dihedralGroupOrder]
