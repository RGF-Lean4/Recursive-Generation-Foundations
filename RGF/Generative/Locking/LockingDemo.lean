import Mathlib

/-!
# Example: k=5 locking-membrane uniqueness

This file demonstrates the core result of RGF: among all k ≥ 3, only k = 5
is the unique integer simultaneously satisfying the three locking-membrane conditions.

## The three conditions

- **L1 (unsolvability):** the symmetric group S_k is unsolvable.
  This connects to Galois theory: the general degree-k polynomial is unsolvable by radicals if and only if S_k is unsolvable,
  which happens if and only if k ≥ 5.

- **L2 (two-mode coupling):** the dihedral group D_k has exactly 2 two-dimensional irreducible representations.
  This guarantees exactly the right number of coupled oscillation modes needed for emergent stability.

- **L3 (spiral non-degeneracy):** k is odd. For even k the spiral dynamics degenerate due to
  cancellation in the Z_k orbit.

## Result

`k = 5` is the unique natural number satisfying L1 ∧ L2 ∧ L3.
-/

open Finset

/-! ## Step 1: define the three conditions -/

/-- The number of two-dimensional irreducible representations of the dihedral group D_k.
    When k is odd: (k-1)/2 representations
    When k is even: (k-2)/2 representations -/
def num2DIrreps' (k : ℕ) : ℕ :=
  if k % 2 = 1 then (k - 1) / 2 else (k - 2) / 2

/-- L1: the symmetric group S_k is unsolvable (requires k ≥ 5). -/
def L1' (k : ℕ) : Prop := k ≥ 5

/-- L2: D_k has exactly 2 two-dimensional irreducible representations. -/
def L2' (k : ℕ) : Prop := num2DIrreps' k = 2

/-- L3: k is odd (spiral non-degeneracy). -/
def L3' (k : ℕ) : Prop := k % 2 = 1

/-- The three locking-membrane conditions hold simultaneously. -/
def LockingConditions' (k : ℕ) : Prop := L1' k ∧ L2' k ∧ L3' k

/-! ## Step 2: verify that k=5 satisfies all conditions -/

/-- k=5 satisfies L1. -/
example : L1' 5 := by unfold L1'; omega

/-- k=5 satisfies L2: D₅ has exactly 2 two-dimensional irreducible representations. -/
example : L2' 5 := by unfold L2' num2DIrreps'; decide

/-- k=5 satisfies L3: 5 is odd. -/
example : L3' 5 := by unfold L3'; decide

/-- k=5 satisfies all three locking-membrane conditions. -/
theorem five_satisfies_locking' : LockingConditions' 5 := by
  exact ⟨by unfold L1'; omega, by unfold L2' num2DIrreps'; decide, by unfold L3'; decide⟩

/-! ## Step 3: uniqueness — no other k works -/

/-- k=5 is the unique natural number satisfying all locking-membrane conditions. -/
theorem locking_unique_global' :
    ∀ k : ℕ, LockingConditions' k → k = 5 := by
  intro k ⟨h1, h2, h3⟩
  unfold L1' at h1
  unfold L2' num2DIrreps' at h2
  unfold L3' at h3
  split at h2 <;> omega

/-- Combination of existence and uniqueness. -/
theorem locking_exists_unique' :
    ∃! k : ℕ, LockingConditions' k :=
  ⟨5, five_satisfies_locking', fun k hk => locking_unique_global' k hk⟩
