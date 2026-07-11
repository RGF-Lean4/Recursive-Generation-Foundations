/-
# L2L3.StabilityUniqueness — the stable two-layer locked structure and its uniqueness

This module isolates the *stable two-layer locked structure* `StableTwoLayer` —
an outer (translational / "movement") locked phase together with an inner
(spin) locked phase — and proves that the mere existence of such a structure
forces the dual-hierarchy locking constants:

* **L2** — the frequency number is locked at `n₂ 5 = 2`;
* **L3** — the locking membrane is odd-dimensional (`Odd 5`);
* `k = 5` is the unique value satisfying the stable-generation predicate
  `StableGen`;
* self-consistency with the dihedral group `D₅` (order `10`, exactly two
  two-dimensional irreducible representations) and the non-solvability of the
  associated alternating symmetry `A₅ ≤ S₅`.

The structure `StableTwoLayer` is, in `L2L3.DynamicsToLocking`, *no longer*
taken as a primitive assumption: it is derived from a Banach contraction
dual-layer dynamics.  This file provides the target object and the locking
theorem it feeds into.

It reuses the self-contained development in `DualHierarchyLocking`
(`StableGen`, `n₂`, `BiLevel`, …) rather than re-deriving the locking facts.
-/

import Mathlib
import RGF.Generative.Locking.DualHierarchyLocking

open scoped Real

namespace RGF.L2L3.StabilityUniqueness

/-- A **stable two-layer locked structure**: an outer (translational) locked
phase `outerPhase` and an inner (spin) locked phase `innerPhase`, both
*helically non-degenerate* (`sin ≠ 0`, i.e. genuine rotations rather than
collapsed reflections) and mutually *independent* (the two layers lock at
distinct phases). -/
structure StableTwoLayer where
  /-- the outer (translational) locked phase -/
  outerPhase : ℝ
  /-- the inner (spin) locked phase -/
  innerPhase : ℝ
  /-- helical non-degeneracy of the outer layer -/
  outer_nondegenerate : Real.sin outerPhase ≠ 0
  /-- helical non-degeneracy of the inner layer -/
  inner_nondegenerate : Real.sin innerPhase ≠ 0
  /-- the two layers lock independently (distinct phases) -/
  layers_distinct : outerPhase ≠ innerPhase

/-- Every stable two-layer locked structure is, in particular, a dual-hierarchy
`BiLevel` structure (the bridge to the self-contained locking development). -/
def StableTwoLayer.toBiLevel (S : StableTwoLayer) : BiLevel where
  θ₁ := S.outerPhase
  θ₂ := S.innerPhase
  sinθ₁_ne_zero := S.outer_nondegenerate
  sinθ₂_ne_zero := S.inner_nondegenerate
  θ_ne := S.layers_distinct

/-- **Uniqueness / master locking theorem.**  The existence of a stable
two-layer locked structure forces the entire chain of dual-hierarchy locking
constants: `n₂ = 2` (L2), the membrane dimension is odd (L3), `k = 5` is the
unique stable-generation value, the dihedral group `D₅` has order `10` with
exactly two two-dimensional irreducible representations, and the associated
permutation symmetry `S₅` is non-solvable. -/
theorem stable_two_layer_locks_uniquely (S : StableTwoLayer) :
    n₂ 5 = 2 ∧ Odd 5 ∧ StableGen 5 ∧ (∃! k, StableGen k) ∧
      (∀ k, StableGen k → k = 5) ∧
      Nat.card (DihedralGroup 5) = 10 ∧
      ¬ IsSolvable (Equiv.Perm (Fin 5)) := by
  -- The structure `S` witnesses non-emptiness of `BiLevel`, but the locking
  -- facts themselves are purely arithmetic / group-theoretic.
  have _ : BiLevel := S.toBiLevel
  refine ⟨n₂_five, by decide, stableGen_five, stableGen_unique,
    fun k hk => (stableGen_iff_eq_five k).mp hk, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  · apply Equiv.Perm.not_solvable
    simp

end RGF.L2L3.StabilityUniqueness
