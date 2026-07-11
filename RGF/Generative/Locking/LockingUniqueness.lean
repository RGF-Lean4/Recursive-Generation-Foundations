import Mathlib

/-!
# The three RGF locking-membrane conditions uniquely determine k = 5

The three locking-membrane conditions:
- L1: S_k is not solvable
- L2: (k-1)/2 = 2
- L3: k is odd
-/

open Equiv

/-- L1: S_k is not solvable. -/
def L1 (k : ℕ) : Prop := ¬ IsSolvable (Perm (Fin k))

/-- L2: arithmetic condition (k-1)/2 = 2. -/
def L2 (k : ℕ) : Prop := (k - 1) / 2 = 2

/-- L3: k is odd. -/
def L3 (k : ℕ) : Prop := k % 2 = 1

/-- Theorem: any k satisfying L2 and L3 must equal 5. -/
theorem locking_membrane_uniqueness (k : ℕ) (hL2 : L2 k) (hL3 : L3 k) : k = 5 := by
  unfold L2 at hL2; unfold L3 at hL3; omega

/-- L1 holds for k ≥ 5: if |Fin k| ≥ 5 then Perm(Fin k) is not solvable. -/
theorem L1_of_ge_five {k : ℕ} (hk : 5 ≤ k) : L1 k := by
  unfold L1
  apply Equiv.Perm.not_solvable
  simp
  exact_mod_cast hk

theorem five_satisfies_L1 : L1 5 := L1_of_ge_five (le_refl 5)

theorem five_satisfies_L2 : L2 5 := by unfold L2; decide

theorem five_satisfies_L3 : L3 5 := by unfold L3; decide

/-- Unique-existence theorem: the only natural number k satisfying L1 ∧ L2 ∧ L3 is exactly 5. -/
theorem locking_membrane_exists_unique :
    ∃! k : ℕ, L1 k ∧ L2 k ∧ L3 k :=
  ⟨5, ⟨five_satisfies_L1, five_satisfies_L2, five_satisfies_L3⟩,
    fun k ⟨_, h2, h3⟩ => locking_membrane_uniqueness k h2 h3⟩

/- Note: L1 is not actually used in the uniqueness proof (only for existence), since L2 and L3 already uniquely determine k = 5.
   The role of L1 is to guarantee k ≥ 5, but L2 already implies k = 5, so L1 is redundant.
   It is kept for completeness of the three locking-membrane conditions. -/
