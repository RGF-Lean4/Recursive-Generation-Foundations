/-
  RGFMoreTheorems.lean — yet another batch of new theorems from the locking-membrane framework
  More New Theorems from the RGF Locking-Membrane Framework

  Building on `Invariants.LockingMembrane` (`num2DIrreps`, the three locking conditions L1-L3)
  and `RGFNewTheorems` (step recursion, sum of squares of dimensions, group-theoretic characterization of k=5),
  this file derives a further batch of previously unstated new theorems, further enriching the RGF mathematical system.

  Main new results:
  ──────────────────────────────────────────────────────────
  D. Monotonicity and range structure of num2DIrreps
     · one-by-one stepping formula: n₂(k+1) = n₂(k) + [k even] (alternating parity growth)
     · monotone non-decreasing: 3 ≤ a ≤ b ⇒ n₂(a) ≤ n₂(b)
     · unboundedness: ∀ N, ∃ k ≥ 3, n₂(k) ≥ N
     · surjectivity: ∀ m ≥ 1, ∃ k ≥ 3, n₂(k) = m
     · parity pairing: n₂(2m+1) = n₂(2m+2) = m

  E. Dihedral group dimension-sum theorem (first power, not square)
     · dimension sum: n₁·1 + n₂·2 = k+1 (k odd) / k+2 (k even)

  F. The value set of n₂ = 2 and a refined characterization of k=5
     · {k ≥ 3 | n₂(k) = 2} = {5, 6}
     · total number of irreps of D₅ = 4
  ──────────────────────────────────────────────────────────
-/

import Mathlib
import RGF.Generative.Locking.LockingMembrane
import RGF.Phenomenology.TestSuite.RGFNewTheorems

open Finset BigOperators Equiv Function

noncomputable section

/-! ============================================================
    D. Monotonicity and range structure of num2DIrreps
    ============================================================ -/

/-
**One-by-one stepping (at even k)**: for even k ≥ 3, n₂(k+1) = n₂(k) + 1.
-/
theorem num2DIrreps_succ_even (k : ℕ) (hk : k ≥ 3) (he : Even k) :
    num2DIrreps (k + 1) = num2DIrreps k + 1 := by
  unfold num2DIrreps;
  grind

/-
**One-by-one stepping (at odd k)**: for odd k ≥ 3, n₂(k+1) = n₂(k).
-/
theorem num2DIrreps_succ_odd (k : ℕ) (ho : Odd k) :
    num2DIrreps (k + 1) = num2DIrreps k := by
  unfold num2DIrreps;
  grind

/-
**Parity pairing**: the adjacent odd 2m+1 and even 2m+2 give the same n₂ value m.
-/
theorem num2DIrreps_odd_even_pair (m : ℕ) :
    num2DIrreps (2 * m + 1) = m ∧ num2DIrreps (2 * m + 2) = m := by
  unfold num2DIrreps; simp +arith +decide [ Nat.add_div ] ;

/-
**Monotone non-decreasing**: for 3 ≤ a ≤ b, n₂(a) ≤ n₂(b).
-/
theorem num2DIrreps_monotone (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) :
    num2DIrreps a ≤ num2DIrreps b := by
  unfold num2DIrreps;
  grind +extAll

/-
**Surjectivity**: for any m ≥ 1, there exists k ≥ 3 with n₂(k) = m (take k = 2m+1).
-/
theorem num2DIrreps_surjective (m : ℕ) (hm : m ≥ 1) :
    ∃ k, k ≥ 3 ∧ num2DIrreps k = m := by
  exact ⟨ 2 * m + 1, by linarith, (num2DIrreps_odd_even_pair m).1 ⟩

/-
**Unboundedness**: n₂ is unbounded on k ≥ 3.
-/
theorem num2DIrreps_unbounded (N : ℕ) :
    ∃ k, k ≥ 3 ∧ num2DIrreps k ≥ N := by
  obtain ⟨ k, hk₁, hk₂ ⟩ := num2DIrreps_surjective ( N + 1 ) ( by linarith ) ; exact ⟨ k, hk₁, by linarith ⟩ ;

/-! ============================================================
    E. Dihedral group dimension-sum theorem
    ============================================================ -/

/-
**Dimension sum (odd k)**: n₁·1 + n₂·2 = k + 1.
-/
theorem dihedral_dim_sum_odd (k : ℕ) (hk : k ≥ 3) (hodd : Odd k) :
    num1DIrreps k * 1 + num2DIrreps k * 2 = k + 1 := by
  unfold num1DIrreps num2DIrreps;
  grind

/-
**Dimension sum (even k)**: n₁·1 + n₂·2 = k + 2.
-/
theorem dihedral_dim_sum_even (k : ℕ) (hk : k ≥ 3) (heven : Even k) :
    num1DIrreps k * 1 + num2DIrreps k * 2 = k + 2 := by
  unfold num1DIrreps num2DIrreps; simp_all +arith +decide [ Nat.even_iff ] ;
  grind +locals

/-! ============================================================
    F. The value set of n₂ = 2 and a refined characterization of k = 5
    ============================================================ -/

/-
**The value set of n₂ = 2**: within k ≥ 3, n₂(k) = 2 corresponds exactly to {5, 6}.
-/
theorem n2_eq_two_set :
    {k : ℕ | k ≥ 3 ∧ num2DIrreps k = 2} = {5, 6} := by
  ext k;
  by_cases hk : 3 ≤ k <;> simp +decide [ hk, num2DIrreps_eq_two_iff ];
  interval_cases k <;> trivial

/-
**Total number of irreps of D₅ = 4** (2 one-dimensional + 2 two-dimensional).
-/
theorem D5_num_irreps :
    num1DIrreps 5 + num2DIrreps 5 = 4 := by
  decide

/-! ============================================================
    Axiom audit
    ============================================================ -/

#print axioms num2DIrreps_succ_even
#print axioms num2DIrreps_monotone
#print axioms num2DIrreps_surjective
#print axioms dihedral_dim_sum_odd
#print axioms n2_eq_two_set
#print axioms D5_num_irreps

end
