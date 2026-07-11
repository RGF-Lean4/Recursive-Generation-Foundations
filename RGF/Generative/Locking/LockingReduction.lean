/-
  Invariants/LockingReduction.lean — the locking-condition reduction theorem
  Locking Membrane Condition Reduction Theorem

  Proves that the three locking conditions L1 (Sₖ not solvable) ∧ L2 (n₂(k) = 2) ∧ L3 (k odd)
  are equivalent to L2 ∧ L3. That is, L1 is a logical consequence of L2 and L3, reducing the locking conditions from three to two.

  Note: this file reuses the existing `num2DIrreps`, `LockingMembraneConditions`,
  and auxiliary lemmas from `Invariants.LockingMembrane`
  (in particular `odd_n2_eq_two_implies_five`), abstracting the three locking conditions L1–L3
  into independent propositional predicates and giving the reduction relation between them.
-/

import Mathlib
import RGF.Generative.Locking.LockingMembrane

namespace LockingMembrane

/-- L1: Sₖ is not solvable. -/
def L1 (k : ℕ) : Prop := ¬ IsSolvable (Equiv.Perm (Fin k))

/-- L2: the number of two-dimensional irreducible representations n₂(k) = 2. -/
def L2 (k : ℕ) : Prop := num2DIrreps k = 2

/-- L3: k is odd (spiral non-degeneracy). -/
def L3 (k : ℕ) : Prop := Odd k

end LockingMembrane

namespace RGF

open LockingMembrane

variable (k : ℕ)

/-- L2 and L3 together uniquely lock k = 5. -/
theorem L2_L3_imply_k_eq_five (hL2 : L2 k) (hL3 : L3 k) : k = 5 :=
  odd_n2_eq_two_implies_five k hL3 hL2

/-- When k = 5, S₅ is not solvable (an existing Mathlib theorem). -/
theorem S5_not_solvable : ¬ IsSolvable (Equiv.Perm (Fin 5)) :=
  Equiv.Perm.fin_5_not_solvable

/-- L2 ∧ L3 ⇒ L1: the core theorem of the locking-condition reduction. -/
theorem L2_L3_imply_L1 (hL2 : L2 k) (hL3 : L3 k) : L1 k := by
  have hk5 : k = 5 := L2_L3_imply_k_eq_five k hL2 hL3
  subst hk5
  exact S5_not_solvable

/-- The three locking conditions are equivalent to two: L1 ∧ L2 ∧ L3 ↔ L2 ∧ L3. -/
theorem locking_reduces_to_two :
    (L1 k ∧ L2 k ∧ L3 k) ↔ (L2 k ∧ L3 k) := by
  constructor
  · rintro ⟨_, hL2, hL3⟩
    exact ⟨hL2, hL3⟩
  · rintro ⟨hL2, hL3⟩
    exact ⟨L2_L3_imply_L1 k hL2 hL3, hL2, hL3⟩

/-- Equivalent form: the locking conditions = L2 ∧ L3. -/
theorem locking_iff_L2_L3 : LockingMembraneConditions k ↔ (L2 k ∧ L3 k) := by
  constructor
  · intro h
    exact ⟨h.L2, h.L3⟩
  · rintro ⟨hL2, hL3⟩
    exact
      { L2 := hL2
        L3 := hL3 }

/-- k = 5 is the unique natural number satisfying L2 ∧ L3. -/
theorem five_unique_for_L2_L3 (hL2 : L2 k) (hL3 : L3 k) : k = 5 :=
  L2_L3_imply_k_eq_five k hL2 hL3

end RGF
