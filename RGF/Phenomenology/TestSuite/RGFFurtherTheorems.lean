/-
  RGFFurtherTheorems.lean — another batch of new theorems from the locking-membrane framework
  Further New Theorems from the RGF Locking-Membrane Framework

  Building on `Invariants.LockingMembrane` (`num2DIrreps`, the three locking conditions L1-L3),
  `RGFNewTheorems` (step recursion, sum of squares of dimensions, group-theoretic characterization of k=5) and
  `RGFMoreTheorems` (monotonicity, surjectivity, pairing, dimension sum),
  this file derives a further batch of previously unstated new theorems, and for the first time connects the abstract counting formula with
  the order of the real dihedral group `DihedralGroup` in Mathlib.

  Main new results:
  ──────────────────────────────────────────────────────────
  G. Unified (parity-independent) formula and refined stepping of num2DIrreps
     · unified formula: n₂(k) = (k - 1) / 2 (for all k, independent of parity)
     · double-step formula: n₂(k + 4) = n₂(k) + 2 (k ≥ 3)
     · complete characterization of n₂ = 3: for k ≥ 3, n₂(k) = 3 ⇔ k ∈ {7, 8}
     · increment upper bound: n₂(k + 1) ≤ n₂(k) + 1 (each step grows by at most 1)

  H. Connection to the real Mathlib dihedral group DihedralGroup
     · group order: |Dₖ| = Nat.card (DihedralGroup k) = 2k
     · the sum of squares of dimensions equals the real group order: n₁·1 + n₂·4 = Nat.card (DihedralGroup k) (k ≥ 3)

  I. Equivalent characterization of locking uniqueness (summary)
     · for k ≥ 3, the three locking conditions ⇔ k = 5
  ──────────────────────────────────────────────────────────
-/

import Mathlib
import RGF.Generative.Locking.LockingMembrane
import RGF.Phenomenology.TestSuite.RGFNewTheorems
import RGF.Phenomenology.TestSuite.RGFMoreTheorems

open Finset BigOperators Equiv Function

noncomputable section

/-! ============================================================
    G. Unified formula and refined stepping of num2DIrreps
    ============================================================ -/

/-
**Unified formula**: for all k, regardless of parity, n₂(k) = (k - 1) / 2 (natural-number division).
This collapses the parity-split definition of num2DIrreps into a single concise parity-independent closed form.
-/
theorem num2DIrreps_eq_pred_div_two (k : ℕ) :
    num2DIrreps k = (k - 1) / 2 := by
  by_contra h;
  contrapose! h; unfold num2DIrreps; split_ifs <;> simp_all +decide ;
  grind

/-
**Double-step formula**: for k ≥ 3, increasing k by 4 (spanning one full parity cycle) increases n₂ by exactly 2.
-/
theorem num2DIrreps_double_step (k : ℕ) (hk : k ≥ 3) :
    num2DIrreps (k + 4) = num2DIrreps k + 2 := by
  rw [ num2DIrreps_step_two, num2DIrreps_step_two ] <;> linarith

/-
**Complete characterization of n₂ = 3**: k ≥ 3 and n₂(k) = 3 if and only if k ∈ {7, 8}.
-/
theorem num2DIrreps_eq_three_iff (k : ℕ) (hk : k ≥ 3) :
    num2DIrreps k = 3 ↔ (k = 7 ∨ k = 8) := by
  rw [num2DIrreps_eq_pred_div_two]; omega

/-
**Increment upper bound**: each increase by 1 grows n₂ by at most 1 (consistent with the one-by-one stepping formula).
-/
theorem num2DIrreps_succ_le (k : ℕ) :
    num2DIrreps (k + 1) ≤ num2DIrreps k + 1 := by
  unfold num2DIrreps;
  grind

/-! ============================================================
    H. Connection to the real Mathlib dihedral group DihedralGroup
    ============================================================ -/

/-
**Group order**: the order of the dihedral group Dₖ is 2k. Taken directly from Mathlib's `DihedralGroup.nat_card`,
recorded here explicitly as a "reference fact" of the RGF framework, for use by the next theorem.
-/
theorem dihedral_card_eq (k : ℕ) :
    Nat.card (DihedralGroup k) = 2 * k := by
  convert DihedralGroup.nat_card using 1

/-
**The sum of squares of dimensions equals the real group order**: for k ≥ 3,
      1²·n₁ + 2²·n₂ = Nat.card (DihedralGroup k).
This for the first time replaces the right-hand side 2k of the abstract counting formula `dihedral_dim_sq_sum`
with the group order of the real dihedral group in Mathlib, completing the connection "abstract count ↔ real group-theoretic object".
-/
theorem dihedral_dim_sq_sum_eq_card (k : ℕ) (hk : k ≥ 3) :
    num1DIrreps k * 1 + num2DIrreps k * 4 = Nat.card (DihedralGroup k) := by
  rw [ dihedral_dim_sq_sum k hk, dihedral_card_eq ]

/-! ============================================================
    I. Equivalent characterization of locking uniqueness
    ============================================================ -/

/-
**Locking uniqueness (equivalent form)**: the locking conditions hold if and only if k = 5.
This merges `locking_unique` (necessity) and `five_satisfies_locking` (sufficiency) into a single iff.
-/
theorem locking_iff_five (k : ℕ) :
    LockingMembraneConditions k ↔ k = 5 := by
  rw [locking_reduces_to_two k]; exact locking_value_refined k

/-! ============================================================
    Axiom audit
    ============================================================ -/

#print axioms num2DIrreps_eq_pred_div_two
#print axioms num2DIrreps_double_step
#print axioms num2DIrreps_eq_three_iff
#print axioms num2DIrreps_succ_le
#print axioms dihedral_card_eq
#print axioms dihedral_dim_sq_sum_eq_card
#print axioms locking_iff_five

end
