import Mathlib
import RGF.Physics.Emergence.LatticeUniqueness

/-!
# Joint uniqueness of `(d, R) = (3, 1)` from two independent first principles

This file extends `Feasibility/LatticeUniqueness.lean`.  The companion file
isolates the *single* combinatorial criterion (lattice coordination →
effective-direction count) behind the locking of the ambient dimension at
`d = 3`.  Here we strengthen that to a **joint uniqueness theorem** that fuses
two genuinely *independent* first-principles criteria, each of which is required
to equal the magic number `5`:

1. **Lattice forward-repulsion direction count.**  On the cubic lattice family
   `ℤ^d`, the FORS exclusivity/recovery rules leave `2*d − 1` admissible
   *forward* repulsion directions (`latticeForward d`).  This is a purely
   combinatorial / lattice-geometric quantity.

2. **FORS pole order.**  The FORS memory-kernel pole order is `d + 2*R`, where
   `R` is the recovery/recursion order of the renormalization step
   (`forsPoleOrder d R`).  This is a purely analytic / field-theoretic quantity,
   independent of the lattice combinatorics above.

Requiring **both** independent quantities to equal `5` simultaneously has a
**unique** solution: `(d, R) = (3, 1)`.  The dimension `d = 3` is locked by the
*intersection* of the two independent criteria (the lattice criterion fixes
`d = 3` on its own; the pole criterion then fixes `R = 1`), rather than being
fitted by a single tunable count.

* `latticeForward_eq_five_iff` — `2*d − 1 = 5 ↔ d = 3`.
* `forsPoleOrder_one_eq_five_iff` — at recovery order `R = 1`, `d + 2 = 5 ↔ d = 3`.
* `dimension_three_unique_lattice` — the lattice criterion alone selects a unique
  dimension `d = 3`.
* `dimension_three_unique` — the joint criterion selects the unique pair
  `(d, R) = (3, 1)`.
-/

namespace FeasibilityLattice

/-- **Lattice forward-repulsion direction count** on the cubic family `ℤ^d`:
    of the `2*d` nearest-neighbour directions, the single back-step direction is
    forbidden by the G1 (exclusivity) / G3 (one-step recovery) rules, leaving
    `2*d − 1` admissible forward repulsion directions.  This coincides with
    `forsCount cubicCoord d`. -/
def latticeForward (d : ℕ) : ℕ := 2 * d - 1

/-- `latticeForward` is exactly the cubic-family FORS effective-direction count. -/
theorem latticeForward_eq_forsCount (d : ℕ) :
    latticeForward d = forsCount cubicCoord d := by
      rfl

/-- **FORS pole order.**  The FORS memory-kernel pole order is `d + 2*R`, where
    `R` is the recovery/recursion order of the renormalization step.  This is an
    analytic quantity independent of the lattice combinatorics. -/
def forsPoleOrder (d R : ℕ) : ℕ := d + 2 * R

/-- **Lattice criterion.**  The forward-repulsion direction count equals `5` iff
    the spatial dimension is `3`. -/
theorem latticeForward_eq_five_iff {d : ℕ} : latticeForward d = 5 ↔ d = 3 := by
  rcases d with ( _ | _ | _ | _ | _ | d ) <;> simp_all +arith +decide [ latticeForward ]

/-- **Pole criterion at recovery order `R = 1`.**  The FORS pole order equals `5`
    iff the spatial dimension is `3`. -/
theorem forsPoleOrder_one_eq_five_iff {d : ℕ} :
    forsPoleOrder d 1 = 5 ↔ d = 3 := by
      grind +locals

/-- **Lattice-only uniqueness.**  Among all dimensions, exactly one — namely
    `d = 3` — yields the five-fold forward-repulsion count.  (Restatement of the
    cubic locking in terms of `latticeForward`.) -/
theorem dimension_three_unique_lattice :
    ∃! d : ℕ, latticeForward d = 5 := by
      exact ⟨ 3, by decide, by rintro d hd; exact ( latticeForward_eq_five_iff.mp hd ) ⟩

/-- **Joint uniqueness theorem.**  Under the two independent first-principles
    criteria — the cubic-lattice forward-repulsion direction count `2*d − 1` and
    the FORS pole order `d + 2*R` — simultaneously requiring *both* to equal `5`
    has the **unique** solution `(d, R) = (3, 1)`.  Thus `d = 3` is locked by the
    intersection of two independent criteria, not by a single tunable number. -/
theorem dimension_three_unique :
    ∃! p : ℕ × ℕ, latticeForward p.1 = 5 ∧ forsPoleOrder p.1 p.2 = 5 := by
      refine' ⟨ ⟨ 3, 1 ⟩, _, _ ⟩ <;> norm_num;
      · decide +revert;
      · grind +locals

end FeasibilityLattice