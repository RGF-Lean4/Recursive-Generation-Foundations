/-
# RGF.CritiqueResolution — machine-checked answers to the three standard critiques

This file gathers, as clean stand-alone theorems, the mathematical content that
addresses the three recurring criticisms of the RGF programme.  It introduces no
new axioms and reuses results already proved elsewhere in the repository.

The three critiques and the corresponding "hard evidence" assembled here are:

* **Critique 1 (the self-consistency condition looks ad hoc).**  The condition
  used to lock the spatial dimension is `dim 𝔰𝔬(d) = d`, i.e.
  `d(d-1)/2 = d`.  This is not a number juggled to produce `3`: it is exactly the
  statement that the space of rotation generators (bivectors) is in bijection with
  vectors — equivalently, that a vector cross product exists.  Its **complete**
  solution set is `{0, 3}` (`dim_so_eq_dim_iff_zero_or_three`,
  `dim_so_solution_set`), so after discarding the trivial `d = 0` the unique
  nontrivial dimension is `3` (`dim_so_lock`).  The honest claim is therefore *not*
  "we derived `3` from nothing", but "a natural self-dual condition has exactly the
  two solutions `0` and `3`".

* **Critique 2 (uniqueness is only conditional / the definitions are tailored).**
  The locked values are robust under *independent* natural criteria.  The spatial
  dimension `3` is selected simultaneously by an **algebraic** criterion
  (`rotGen d = d`, bivector ↔ vector) and by a logically independent
  **combinatorial** criterion (the cubic-lattice forward-direction count
  `2d - 1 = 5`); the two agree exactly (`dimension_three_convergent`).  The mode
  order `5` is selected both by the **group-theoretic** minimal-emergence criterion
  (`MinimalEmergent 5`, the Abel–Ruffini threshold) and, independently, by the
  **crystallographic** criterion (`5` is the smallest prime rotation order
  incompatible with any lattice) — see `five_two_independent_characterizations`.
  Convergent independent definitions are the antidote to the "tailored definition"
  objection.

* **Critique 3 (no gain in logical strength; what is the framework *for*?).**  The
  honest answer is unification and transparency, not consistency strength.  The
  classically *unrelated* facts "the general quintic is unsolvable (degree `5`)"
  and "a cross product exists only in dimension `3`" are two faces of a *single*
  locking principle: the unique pair `(k, d)` satisfying minimal emergence and the
  self-dual cross-product condition is `(5, 3)`
  (`abelRuffini_crossProduct_unified`).  As a transparent by-product the framework
  reproduces the group-theoretic root of Abel–Ruffini in one line
  (`quintic_solvability_threshold`).  (For the consistency-strength boundary
  `Con(ZFC) → Con(RGF)` see `RGFConsistencyStrength.consistency`.)
-/

import Mathlib
import RGF.Physics.Emergence.FirstPrinciples
import RGF.Physics.Emergence.LatticeUniquenessGap
import RGF.Generative.Locking.DimensionThreeUnique

namespace RGF.CritiqueResolution

open RGF.FirstPrinciples RGF.LatticeUniquenessGap FeasibilityLattice

/-! ## 1. Naturality of the self-dual dimension condition (Critique 1) -/

/-
**The complete solution set of the self-dual condition `dim 𝔰𝔬(d) = d`.**
    Over `ℕ`, the equation `d(d-1) = 2d` (equivalently `d(d-1)/2 = d`, i.e. the
    number of rotation planes equals the number of axes) holds *iff* `d ∈ {0, 3}`.
    This exhibits the condition as a genuine, target-free algebraic constraint
    rather than a fitted number.
-/
theorem dim_so_eq_dim_iff_zero_or_three (d : ℕ) :
    d * (d - 1) = 2 * d ↔ d = 0 ∨ d = 3 := by
  rcases d with ( _ | _ | _ | _ | d ) <;> simp_all +arith +decide [ mul_add, mul_comm ]

/-
The same fact phrased through `rotGen d = d(d-1)/2` (the Lie-algebra dimension
    of `𝔰𝔬(d)`): `rotGen d = d ↔ d ∈ {0, 3}`.
-/
theorem rotGen_eq_dim_iff_zero_or_three (d : ℕ) :
    rotGen d = d ↔ d = 0 ∨ d = 3 := by
  unfold rotGen; rcases d with ( _ | _ | _ | _ | d ) <;> simp +arith +decide [ Nat.mul_succ ] ;
  exact ne_of_gt ( Nat.le_div_iff_mul_le zero_lt_two |>.2 ( by nlinarith ) )

/-
**Finite enumeration exhibit.**  Among the first fifty dimensions, the ones
    satisfying `rotGen d = d` are precisely `{0, 3}` — a directly checkable witness
    that the condition is not silently satisfied by many values.
-/
theorem dim_so_solution_set :
    (Finset.range 50).filter (fun d => rotGen d = d) = {0, 3} := by
  decide

/-
**Nontrivial dimension lock.**  Discarding the trivial solution `d = 0`, the
    self-dual condition has the unique solution `d = 3`.
-/
theorem dim_so_lock {d : ℕ} (hd : 0 < d) : d * (d - 1) = 2 * d ↔ d = 3 := by
  rcases d with ( _ | _ | _ | _ | d ) <;> simp_all +arith +decide [ Nat.mul_succ ]

/-! ## 2. Robustness: independent criteria converge on the locked values
    (Critique 2) -/

/-
**Two independent criteria agree on `d = 3`.**  For any nonzero dimension the
    *algebraic* criterion `rotGen d = d` (bivector ↔ vector) holds iff the logically
    independent *combinatorial* criterion `latticeForward d = 5` (cubic-lattice
    forward-direction count `2d - 1 = 5`) holds.  Neither definition mentions the
    other, yet both pick out exactly `d = 3`.
-/
theorem dimension_three_convergent {d : ℕ} (hd : 0 < d) :
    rotGen d = d ↔ latticeForward d = 5 := by
  rw [ rotGen_eq_dim_iff hd, latticeForward_eq_five_iff ]

/-
**Two independent characterizations of the mode order `5`.**  The group-theoretic
    minimal-emergence criterion (`MinimalEmergent 5`, i.e. `S₅` is the smallest
    non-solvable symmetric group — the Abel–Ruffini threshold) and the
    crystallographic criterion (`5` is the smallest prime rotation order
    incompatible with a lattice, i.e. `Nat.totient 5 > 2`, while every smaller
    prime order has `Nat.totient p ≤ 2` and is compatible) are independent, yet
    both single out `5`.
-/
theorem five_two_independent_characterizations :
    MinimalEmergent 5 ∧
      (Nat.Prime 5 ∧ 2 < Nat.totient 5 ∧
        ∀ p : ℕ, Nat.Prime p → p < 5 → Nat.totient p ≤ 2) := by
  exact ⟨ minimalEmergent_iff_five.mpr rfl, by decide, by decide, fun p hp hp' => by interval_cases p <;> trivial ⟩

/-! ## 3. Unification and transparency (Critique 3) -/

/-
**Unification of Abel–Ruffini and the cross product.**  The classically
    unrelated facts "degree `5` is the threshold of unsolvability by radicals" and
    "a vector cross product exists only in dimension `3`" are two projections of a
    single locking principle: the unique pair `(k, d)` satisfying minimal emergence
    `MinimalEmergent k` and the self-dual cross-product condition `CP d` is
    `(5, 3)`.
-/
theorem abelRuffini_crossProduct_unified :
    ∃! p : ℕ × ℕ, MinimalEmergent p.1 ∧ CP p.2 := by
  -- We need to show that the pair (5, 3) is unique.
  use (5, 3);
  -- We need to show that (5, 3) is the unique pair satisfying the conditions.
  simp [minimalEmergent_iff_five, cp_iff_three]

/-
**Transparent re-derivation (a "simplified proof" instance).**  The framework's
    emergence lemma reproduces the group-theoretic root of Abel–Ruffini in one
    step: the symmetric group on four letters is solvable, while the symmetric group
    on five letters is not.
-/
theorem quintic_solvability_threshold :
    IsSolvable (Equiv.Perm (Fin 4)) ∧ ¬ IsSolvable (Equiv.Perm (Fin 5)) := by
  convert S4_solvable using 1;
  exact ⟨ fun h => h.1, fun h => ⟨ h, S5_not_solvable ⟩ ⟩

end RGF.CritiqueResolution