/-
# RCDxRGF.Dimension — bridging the RCD `d = 3` core to RGF's multi-path locking

This file belongs to the **optional bridge library** `RCDxRGF`.  Unlike the `RCD`
library (which imports only `Mathlib` and is deliberately decoupled from the RGF
spine), this library may see *both* systems at once.  Its sole purpose is to
"inject" RGF's machine-verified results into RCD, **without touching the pristine,
independently auditable `RCD` library itself**.

Here we connect the RCD dimensional core
`dim_three_unique`
— which fixes the spatial dimension as the unique solution of the three physical
constraints `(d ≤ 3 ∧ Odd d ∧ d ≠ 1)` — to **three logically independent**
RGF derivations of the same `d = 3`:

* the **algebraic** self-dual / cross-product condition `CP d`
  (`RGF.FirstPrinciples.cp_iff_three`);
* the **combinatorial** cubic-lattice forward-direction count `2d - 1 = 5`
  (`FeasibilityLattice.latticeForward_eq_five_iff`);
* the **analytic** FORS pole order `d + 2R = 5` at recovery order `R = 1`
  (`FeasibilityLattice.forsPoleOrder_one_eq_five_iff`).

The upshot is that RCD's `d = 3` is no longer pinned by a single arithmetic
intersection but is bracketed by three independent machine-checked routes.
-/

import Mathlib
import RGF.Physics.Emergence.FirstPrinciples
import RGF.Generative.Locking.DimensionThreeUnique

namespace RCDxRGF.Dimension

open RGF.FirstPrinciples FeasibilityLattice

/-- Arithmetic characterisation of the spatial dimension: constraint I (`d ≤ 3`)
    together with constraint II (`d` odd and `d ≠ 1`) holds iff `d = 3`. -/
theorem dim_three_unique (d : ℕ) :
    (d ≤ 3 ∧ Odd d ∧ d ≠ 1) ↔ d = 3 := by
  rcases d with ( _ | _ | _ | _ | d ) <;> simp_all +arith +decide [ parity_simps ]

/-- **Algebraic route.**  RCD's three-constraint characterisation of the spatial
    dimension is *equivalent* to RGF's first-principles cross-product condition
    `CP d` (`d(d-1) = 2d`, the bivector ↔ vector self-duality). -/
theorem rcd_dim3_iff_rgf_crossProduct (d : ℕ) :
    (d ≤ 3 ∧ Odd d ∧ d ≠ 1) ↔ CP d := by
  rw [dim_three_unique]
  exact cp_iff_three.symm

/-- **Combinatorial route.**  RCD's three-constraint characterisation is equivalent
    to the RGF cubic-lattice forward-repulsion count being `5` (i.e. `2d - 1 = 5`). -/
theorem rcd_dim3_iff_rgf_lattice (d : ℕ) :
    (d ≤ 3 ∧ Odd d ∧ d ≠ 1) ↔ latticeForward d = 5 := by
  rw [dim_three_unique]
  exact latticeForward_eq_five_iff.symm

/-- **Analytic route.**  RCD's three-constraint characterisation is equivalent to
    the RGF FORS pole order (at recovery order `R = 1`) being `5`. -/
theorem rcd_dim3_iff_rgf_forsPole (d : ℕ) :
    (d ≤ 3 ∧ Odd d ∧ d ≠ 1) ↔ forsPoleOrder d 1 = 5 := by
  rw [dim_three_unique]
  exact forsPoleOrder_one_eq_five_iff.symm

/-- **Multi-path robustness (the upgrade).**  RCD's spatial-dimension core is
    simultaneously equivalent to *all three* independent RGF criteria.  Thus the
    RCD value `d = 3` is bracketed by an algebraic, a combinatorial and an analytic
    machine-verified route at once — none of which references the others. -/
theorem rcd_dim3_multipath (d : ℕ) :
    (d ≤ 3 ∧ Odd d ∧ d ≠ 1) ↔
      (CP d ∧ latticeForward d = 5 ∧ forsPoleOrder d 1 = 5) := by
  rw [dim_three_unique]
  constructor
  · rintro rfl
    exact ⟨cp_iff_three.mpr rfl, latticeForward_eq_five_iff.mpr rfl,
      forsPoleOrder_one_eq_five_iff.mpr rfl⟩
  · rintro ⟨h, _, _⟩
    exact cp_iff_three.mp h

end RCDxRGF.Dimension
