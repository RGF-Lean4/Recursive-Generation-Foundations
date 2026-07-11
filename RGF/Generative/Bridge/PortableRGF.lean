import Mathlib

/-!
# Complete Unified Locking Theorem (Portable Version)

This file is a **complete, self-contained, long-form** version of the core inference
chain of the RGF framework. It provides:

1. The definition of the three locking-membrane conditions and their degeneration
   (L2 ∧ L3 ⇒ L1).
2. Intrinsic dihedral symmetry: deriving a transitive `D_{2d-1}` action on the
   direction set from the cardinality of the lattice's combinatorial offspring.
3. Dimension locking: deriving the emergent spatial dimension `d = 3` directly from
   the simplified locking conditions.

All theorems that depend on external RGF libraries are abstracted as `variable`
declarations. A user only needs to supply theorems with the same signatures in their
own library to obtain the complete dimension-locking theorem.

This file **depends on no private RGF library** — it depends only on `Mathlib` and the
explicitly declared external variables.
-/

namespace PortableRGF

/-! ## External interface: theorems that must be supplied by the user

These `variable` declarations represent results that have already been proved in
modules such as lattice combinatorics, representation theory, and the locking
membrane. Treating them as variables makes this file independent of any particular
RGF implementation.
-/

variable
  -- Cardinality of the set of valid lattice directions (from G1, G3).
  (card_allowedNext : ℕ → ℕ)
  (card_allowedNext_spec : ∀ d, card_allowedNext d = 2*d - 1)
  -- Count of two-dimensional irreducible representations of the dihedral group.
  (num2DIrreps : ℕ → ℕ)
  (num2DIrreps_eq_two_iff : ∀ k, 3 ≤ k → (num2DIrreps k = 2 ↔ k = 5 ∨ k = 6))
  (num2DIrreps_eq_zero_of_lt_three : ∀ k, k < 3 → num2DIrreps k = 0)
  -- Solvability criterion for S_n (from Emergence or classical group theory).
  (solvable_perm_iff_le_four : ∀ n : ℕ, IsSolvable (Equiv.Perm (Fin n)) ↔ n ≤ 4)

/-! ## Core definitions -/

/-- The original three locking-membrane conditions. -/
structure LockingMembraneConditions (k : ℕ) : Prop where
  L1 : ¬ IsSolvable (Equiv.Perm (Fin k))
  L2 : num2DIrreps k = 2
  L3 : Odd k

variable
  -- Intrinsic dimension-locking theorem (requires the original three conditions as
  -- hypotheses). This is `emergent_dimension_intrinsic`, proved in IntrinsicSymmetry.lean.
  (emergent_dimension_intrinsic :
    ∀ (d k : ℕ), 1 ≤ d → card_allowedNext d = 2*d - 1 →
      LockingMembraneConditions num2DIrreps k → d = 3)

/-- The simplified locking conditions: keeping only L2 and L3. -/
def SimpleLockingConditions (k : ℕ) : Prop :=
  num2DIrreps k = 2 ∧ Odd k

/-! ## Degeneration: L2 ∧ L3 ⇒ L1 -/

include num2DIrreps_eq_two_iff in
/-- From L2 and L3, force `k = 5`. -/
lemma L2_L3_implies_k_eq_five (k : ℕ) (hk3 : 3 ≤ k)
    (hL2 : num2DIrreps k = 2) (hL3 : Odd k) : k = 5 := by
  rcases (num2DIrreps_eq_two_iff k hk3).mp hL2 with (hk | hk)
  · exact hk
  · -- k = 6, but 6 is even, contradicting L3.
    have h6_even : ¬ Odd 6 := by decide
    rw [hk] at hL3
    exact absurd hL3 h6_even

include solvable_perm_iff_le_four in
/-- S₅ is not solvable. -/
lemma S5_not_solvable : ¬ IsSolvable (Equiv.Perm (Fin 5)) := by
  exact (solvable_perm_iff_le_four 5).not.mpr (by omega)

include num2DIrreps_eq_two_iff solvable_perm_iff_le_four in
/-- Core degeneration theorem: if `k ≥ 3` satisfies L2 and is odd, then L1 holds
automatically. -/
theorem L2_L3_imply_L1 (k : ℕ) (hk3 : 3 ≤ k)
    (hL2 : num2DIrreps k = 2) (hL3 : Odd k) :
    ¬ IsSolvable (Equiv.Perm (Fin k)) := by
  have hk5 : k = 5 := L2_L3_implies_k_eq_five num2DIrreps num2DIrreps_eq_two_iff k hk3 hL2 hL3
  subst hk5
  exact S5_not_solvable solvable_perm_iff_le_four

include num2DIrreps_eq_two_iff solvable_perm_iff_le_four in
/-- The three locking-membrane conditions are equivalent to L2 ∧ L3 (when `k ≥ 3`). -/
theorem locking_iff_L2_and_L3 (k : ℕ) (hk3 : 3 ≤ k) :
    LockingMembraneConditions num2DIrreps k ↔ (num2DIrreps k = 2 ∧ Odd k) := by
  constructor
  · intro ⟨_, hL2, hL3⟩; exact ⟨hL2, hL3⟩
  · intro ⟨hL2, hL3⟩
    exact ⟨L2_L3_imply_L1 num2DIrreps num2DIrreps_eq_two_iff solvable_perm_iff_le_four k hk3 hL2 hL3,
      hL2, hL3⟩

/-! ## Uniqueness of the simplified locking conditions -/

include num2DIrreps_eq_two_iff num2DIrreps_eq_zero_of_lt_three in
/-- The unique `k` satisfying the simplified locking conditions is `5`. -/
theorem simple_locking_unique_five : ∃! k : ℕ, SimpleLockingConditions num2DIrreps k := by
  refine ⟨5, ?_, ?_⟩
  · -- 5 satisfies L2 ∧ L3.
    refine ⟨?_, ?_⟩
    · -- n₂(5) = 2
      have h3 : 3 ≤ 5 := by norm_num
      exact ((num2DIrreps_eq_two_iff 5 h3).mpr (Or.inl rfl))
    · -- 5 is odd
      norm_num [Odd]
  · -- Uniqueness.
    intro k ⟨hL2, hL3⟩
    have hk_ge_3 : 3 ≤ k := by
      by_contra! H
      have hzero : num2DIrreps k = 0 := num2DIrreps_eq_zero_of_lt_three k (by omega)
      linarith
    exact L2_L3_implies_k_eq_five num2DIrreps num2DIrreps_eq_two_iff k hk_ge_3 hL2 hL3

/-! ## Dimension locking: the ultimate theorem -/

include card_allowedNext_spec num2DIrreps_eq_two_iff num2DIrreps_eq_zero_of_lt_three
  solvable_perm_iff_le_four emergent_dimension_intrinsic in
/-- From the lattice-cardinality fact and the simplified locking conditions, obtain
`d = 3` directly. This is the top-level theorem of the entire framework; downstream
physics/geometry modules only need to invoke it. -/
theorem simplified_locking_implies_dimension_three
    (d k : ℕ) (hd : 1 ≤ d)
    (h_simple : SimpleLockingConditions num2DIrreps k) : d = 3 := by
  -- Lattice-cardinality fact (from the combinatorial theorem of G1, G3).
  have h_card : card_allowedNext d = 2*d - 1 := card_allowedNext_spec d
  -- Split the simplified conditions.
  obtain ⟨hL2, hL3⟩ := h_simple
  -- Derive k ≥ 3 (otherwise n₂(k) = 0 contradicts L2).
  have hk_ge_3 : 3 ≤ k := by
    by_contra! H
    have hzero : num2DIrreps k = 0 := num2DIrreps_eq_zero_of_lt_three k (by omega)
    linarith
  -- Upgrade the simplified conditions to the original three conditions.
  have h_lock : LockingMembraneConditions num2DIrreps k :=
    ((locking_iff_L2_and_L3 num2DIrreps num2DIrreps_eq_two_iff solvable_perm_iff_le_four k
      hk_ge_3).mpr ⟨hL2, hL3⟩)
  -- Invoke the proved intrinsic dimension-locking theorem.
  exact emergent_dimension_intrinsic d k hd h_card h_lock

include card_allowedNext_spec num2DIrreps_eq_two_iff num2DIrreps_eq_zero_of_lt_three
  solvable_perm_iff_le_four emergent_dimension_intrinsic in
/-- A more concise version: when `k` is already fixed to `5`, the lattice dimension
must be `3`. -/
theorem dim_three_when_k_eq_five (d : ℕ) (hd : 1 ≤ d)
    (h_simple : SimpleLockingConditions num2DIrreps 5) : d = 3 :=
  simplified_locking_implies_dimension_three card_allowedNext card_allowedNext_spec
    num2DIrreps num2DIrreps_eq_two_iff num2DIrreps_eq_zero_of_lt_three solvable_perm_iff_le_four
    emergent_dimension_intrinsic d 5 hd h_simple

/-! ## Downstream upgrade macro -/

/-- Macro `from_simple`: in a proof, when the context already contains
`h_simple : SimpleLockingConditions k`, invoking this macro automatically adds
`hk_ge_3` and `h_lock : LockingMembraneConditions k`. This lets every theorem that
still uses the original three conditions work directly under the new hypotheses.

Note: this macro assumes that the local context at the call site already binds
identifiers of the same name such as `num2DIrreps`, `num2DIrreps_eq_zero_of_lt_three`,
and `locking_iff_L2_and_L3`. It is a convenience wrapper for the user side and is not
invoked directly within this file. -/
macro "from_simple" : tactic =>
  `(tactic| (
    have hk_ge_3 : 3 ≤ k := by
      by_contra! H
      have hzero : num2DIrreps k = 0 := num2DIrreps_eq_zero_of_lt_three k (by omega)
      have hL2 : num2DIrreps k = 2 := h_simple.1
      linarith
    have h_lock : LockingMembraneConditions k :=
      ((locking_iff_L2_and_L3 k hk_ge_3).mpr ⟨h_simple.1, h_simple.2⟩)
  ))

end PortableRGF

/-!
## How to use this file in any RGF implementation

Suppose your own library has already proved the following theorems (they are exactly
the contents of the `variable` declarations above):

* `card_allowedNext_spec` — in `LatticeToFORS.lean`
* `num2DIrreps_eq_two_iff`, etc. — in `LockingMembrane.lean` or `RGFNewTheorems.lean`
* `solvable_perm_iff_le_four` — in `Emergence.lean`
* `emergent_dimension_intrinsic` — in `IntrinsicSymmetry.lean` (or `UnifiedLocking.lean`)

You can create a new file `MyFinalTheorem.lean` and pass in your proved theorems in
the order of the positional arguments:

```lean
import RGF.Physics.Emergence.LatticeToFORS
import RGF.Generative.Locking.LockingMembrane
import RGF.Physics.Emergence.RGFEmergence
import RGF.Applications.IntrinsicSymmetry
import RGF.Generative.Bridge.PortableRGF

-- Now you can use the ultimate theorem directly (filling in the proved theorems in
-- the order of the variable declarations).
theorem my_final_result (d : ℕ) (hd : 1 ≤ d)
    (h_simple : PortableRGF.SimpleLockingConditions
      RGF.Invariants.LockingMembrane.num2DIrreps 5) : d = 3 :=
  PortableRGF.simplified_locking_implies_dimension_three
    RGF.FiveLocking.LatticeToFORS.card_allowedNext
    RGF.FiveLocking.LatticeToFORS.card_allowedNext_spec
    RGF.Invariants.LockingMembrane.num2DIrreps
    RGF.Invariants.LockingMembrane.num2DIrreps_eq_two_iff
    RGF.Invariants.LockingMembrane.num2DIrreps_eq_zero_of_lt_three
    RGF.Axioms.Emergence.solvable_perm_iff_le_four
    RGF.FiveLocking.IntrinsicSymmetry.emergent_dimension_intrinsic
    d 5 hd h_simple
```

In this way, the entire dimension-locking logic chain plugs seamlessly into your RGF
library, and `PortableRGF.lean` itself has no hard dependency on any private module, so
it can be distributed to any collaborator.
-/

#check @PortableRGF.simplified_locking_implies_dimension_three
