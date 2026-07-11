/-
# L2L3.G1Exclusivity — the G1-exclusivity derivation and the key step 2d − 1 = k

Each nearest-neighbor direction is mapped to an integer vector `toVec` (`±e_i`), and G1
exclusivity is characterized as "one step returns to the previous lattice point ⟺ the step is
reversed". This pins the excluded-direction set down to a single point, so the "−1" in
"number of effective forward directions = 2d − 1" is no longer a convention but a
machine-checkable combinatorial conclusion. The bridge to the mode-locking order `k` is
stated explicitly, internally deriving `d = 3` when `k = 5`.

* `toVec` / `toVec_injective`: injective encoding of directions as integer vectors `±e_i`.
* `rev` / `revisitsPrevious` / `revisitsPrevious_iff_rev`: "returns to the previous lattice
  point ⟺ reverses the step".
* `excludedByG1_eq_singleton` / `card_excludedByG1`: the directions excluded by G1 form exactly
  a single point.
* `allowedForward` / `card_allowedForward`: number of effective forward directions `= 2d − 1`.
* `card_allowedForward_eq_latticeForward`: agreement with `FeasibilityLattice.latticeForward`.
* `dimension_three_from_G1_and_locking` / `g1_dimension_master`: the bridge to the
  mode-locking order `k`, deriving `d = 3` when `k = 5`.
-/

import Mathlib
import RGF.Generative.Locking.DimensionThreeUnique
import RGF.Generative.Locking.LockingMembrane

open scoped BigOperators
open Classical

namespace RGF.L2L3.G1Exclusivity

/-! ## Integer-vector encoding of directions -/

/-- A nearest-neighbor direction `(i, b)` on the cubic lattice `ℤ^d`: `i` selects the
    coordinate axis, `b` selects the positive (`true`) / negative (`false`) orientation.
    Encoded as the integer vector `±e_i`. -/
def toVec {d : ℕ} (s : Fin d × Bool) : Fin d → ℤ :=
  Pi.single s.1 (if s.2 then 1 else -1)

/-
**`toVec_injective`.** The encoding of directions as `±e_i` is injective.
-/
theorem toVec_injective {d : ℕ} : Function.Injective (toVec (d := d)) := by
  intro x y h; have := congr_fun h x.1; have := congr_fun h y.1; simp_all +decide ;
  unfold toVec at h; simp_all +decide [ funext_iff ] ;
  specialize h x.1; by_cases hx : x.1 = y.1 <;> simp_all +decide [ Pi.single_apply ] ;
  · grind;
  · grind

/-! ## G1 exclusivity: returning to the previous lattice point ⟺ reversing the step -/

/-- Direction reversal: same axis, opposite orientation. -/
def rev {d : ℕ} (s : Fin d × Bool) : Fin d × Bool := (s.1, !s.2)

/-- After taking one step along direction `s`, a candidate next direction `t` "returns to the
    previous lattice point" if and only if its displacement vector is opposite to that of `s`,
    i.e. `toVec t = - toVec s`. -/
def revisitsPrevious {d : ℕ} (s t : Fin d × Bool) : Prop :=
  toVec t = - toVec s

/-
**`revisitsPrevious_iff_rev`.** "One step returns to the previous lattice point ⟺ the step is
    reversed".
-/
theorem revisitsPrevious_iff_rev {d : ℕ} (s t : Fin d × Bool) :
    revisitsPrevious s t ↔ t = rev s := by
  convert toVec_injective.eq_iff using 1;
  unfold revisitsPrevious toVec rev; simp +decide [ funext_iff ] ;
  grind +qlia

/-- The set of candidate directions excluded by the G1-exclusivity rule (directions that
    return to the previous lattice point). -/
noncomputable def excludedByG1 {d : ℕ} (s : Fin d × Bool) : Finset (Fin d × Bool) :=
  Finset.univ.filter (fun t => revisitsPrevious s t)

/-
**`excludedByG1_eq_singleton`.** The set of directions excluded by G1 is exactly the single
    point `{rev s}`, so the "−1" is a combinatorial conclusion rather than a convention.
-/
theorem excludedByG1_eq_singleton {d : ℕ} (s : Fin d × Bool) :
    excludedByG1 s = {rev s} := by
  ext t;
  simp +decide [ excludedByG1, revisitsPrevious_iff_rev ]

/-- **`card_excludedByG1`.** Exactly one direction is excluded by G1. -/
theorem card_excludedByG1 {d : ℕ} (s : Fin d × Bool) :
    (excludedByG1 s).card = 1 := by
  rw [excludedByG1_eq_singleton]; simp

/-! ## Number of effective forward directions = 2d − 1 -/

/-- The set of effective forward directions allowed after one step along direction `s`: from
    the `2d` nearest-neighbor directions, remove the unique return-step direction. -/
def allowedForward {d : ℕ} (s : Fin d × Bool) : Finset (Fin d × Bool) :=
  Finset.univ.erase (rev s)

/-
**`card_allowedForward`.** Number of effective forward directions `= 2d − 1` (internal
    theorem).
-/
theorem card_allowedForward {d : ℕ} (s : Fin d × Bool) :
    (allowedForward s).card = 2 * d - 1 := by
  convert Finset.card_erase_of_mem ( Finset.mem_univ ( rev s ) ) using 1 ; norm_num [ Fintype.card_prod, Fintype.card_fin ] ; ring;

/-- **`card_allowedForward_eq_latticeForward`.** The internal count agrees with
    `FeasibilityLattice.latticeForward d`. -/
theorem card_allowedForward_eq_latticeForward {d : ℕ} (s : Fin d × Bool) :
    (allowedForward s).card = FeasibilityLattice.latticeForward d := by
  rw [card_allowedForward]; rfl

/-! ## Bridge to the mode-locking order k -/

/-
**`dimension_three_from_G1_and_locking`.** Bridging condition (in the sense of "`Z_{2d−1}`
    directional symmetry is compatible with `Z_k` mode-locking symmetry"): when the order
    `2d − 1` of the forward-direction star equals the mode-locking order `k`, and `k = 5`
    (given independently by locking-membrane uniqueness), the spatial dimension is internally
    locked to `d = 3`.
-/
theorem dimension_three_from_G1_and_locking {d k : ℕ} (s : Fin d × Bool)
    (hbridge : (allowedForward s).card = k) (hk : k = 5) : d = 3 := by
  convert FeasibilityLattice.latticeForward_eq_five_iff.mp _;
  rw [ ← hk, ← hbridge, card_allowedForward_eq_latticeForward ]

/-- **`g1_dimension_master`.** Synthesis of the G1 internal chain: exactly one direction is
    excluded, the number of effective forward directions `= 2d − 1`, and when this is
    compatible with the direction-star order at mode-locking order `k = 5` it yields `d = 3`. -/
theorem g1_dimension_master {d : ℕ} (s : Fin d × Bool) :
    (excludedByG1 s).card = 1 ∧
    (allowedForward s).card = 2 * d - 1 ∧
    ((allowedForward s).card = 5 → d = 3) := by
  refine ⟨card_excludedByG1 s, card_allowedForward s, fun h => ?_⟩
  exact dimension_three_from_G1_and_locking s h rfl

end RGF.L2L3.G1Exclusivity