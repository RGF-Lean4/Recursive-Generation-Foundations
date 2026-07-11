import Mathlib

/-!
# Feasibility demonstration: uniqueness of `d = 3` in lattice families

This file accompanies `FEASIBILITY_ANALYSIS.md`.  It substantiates, with a
fully machine-checked (0-`sorry`) development, the assessment that the problem

> *"uniqueness of `d = 3` within specific lattice families"*

is **tractable with existing group-theoretic / combinatorial tools** (rated
*medium*).

The existing project already proves, for the hypercubic family, that the FORS
core has `2*d - 1` admissible directions and that this equals `5` iff `d = 3`
(`LatticeToFORS.dimension_locked_to_three`).  Here we isolate the *general
mechanism* behind that result as a clean, reusable theorem and re-derive the
hypercubic statement as a special case:

* `dim_unique_of_strictMono` — for **any** lattice family whose nearest-neighbour
  coordination number is strictly monotone in the dimension, the FORS
  effective-direction count `coord d - 1` determines the dimension uniquely.
  This is the genuine reason `d = 3` is singled out: it is a monotonicity /
  injectivity fact, not an arithmetic coincidence.
* `cubic_five_iff_three`, `cubic_dim_three_unique` — the hypercubic
  specialisation `coord d = 2*d`: exactly one dimension (`d = 3`) yields the
  five-fold orbit recursion structure.
* `coord_eq_five_unique` — the general "target count" version: if a monotone
  family hits a given effective-direction count `c` at all, it does so at a
  unique dimension.

These are stated generically (over an arbitrary `coord : ℕ → ℕ`) precisely so
that other lattice families (FCC, BCC, root-lattice nearest-neighbour graphs,
…) can reuse the same uniqueness engine simply by supplying their coordination
function and a monotonicity proof.
-/

namespace FeasibilityLattice

/-- Effective FORS direction count for a lattice family with coordination
    function `coord`: the coordination number minus the single back-step
    direction forbidden by the G1 (exclusivity) / G3 (one-step recovery) rules. -/
def forsCount (coord : ℕ → ℕ) (d : ℕ) : ℕ := coord d - 1

/-- **Uniqueness from monotone coordination.**  If the coordination number is
    strictly monotone in the dimension (a strictly larger dimension has strictly
    more nearest neighbours) and every dimension has at least one neighbour, then
    the effective-direction count `coord d - 1` determines the dimension
    uniquely.  This is the abstract core of all "`d = 3` uniqueness" statements in
    the RGF lattice layer. -/
theorem dim_unique_of_strictMono
    (coord : ℕ → ℕ) (hmono : StrictMono coord)
    (hpos : ∀ d, 1 ≤ coord d)
    {d₁ d₂ : ℕ} (h : forsCount coord d₁ = forsCount coord d₂) : d₁ = d₂ := by
  have h1 := hpos d₁
  have h2 := hpos d₂
  unfold forsCount at h
  have : coord d₁ = coord d₂ := by omega
  exact hmono.injective this

/-- **General target-count uniqueness.**  For a strictly monotone coordination
    family with at least one neighbour everywhere, any prescribed
    effective-direction count `c` is attained at no more than one dimension. -/
theorem coord_eq_five_unique
    (coord : ℕ → ℕ) (hmono : StrictMono coord) (hpos : ∀ d, 1 ≤ coord d)
    (c : ℕ) {d₁ d₂ : ℕ}
    (h₁ : forsCount coord d₁ = c) (h₂ : forsCount coord d₂ = c) : d₁ = d₂ :=
  dim_unique_of_strictMono coord hmono hpos (h₁.trans h₂.symm)

/-! ## The hypercubic family `ℤ^d` -/

/-- Hypercubic coordination number: each of the `d` coordinate axes contributes
    the two directions `±1`, giving `2*d` nearest neighbours. -/
def cubicCoord (d : ℕ) : ℕ := 2 * d

theorem cubicCoord_strictMono : StrictMono cubicCoord := by
  intro a b hab; unfold cubicCoord; omega

theorem cubicCoord_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ cubicCoord d := by
  unfold cubicCoord; omega

/-- **Hypercubic five-fold locking.**  On the hypercubic family the FORS core has
    exactly `5` admissible directions **iff** the spatial dimension is `3`. -/
theorem cubic_five_iff_three {d : ℕ} (hd : 1 ≤ d) :
    forsCount cubicCoord d = 5 ↔ d = 3 := by
  unfold forsCount cubicCoord; omega

/-- **Uniqueness of `d = 3`.**  Among all dimensions `d ≥ 1`, exactly one — namely
    `d = 3` — yields the five-direction FORS core on the hypercubic lattice.  This
    re-proves `LatticeToFORS.dimension_locked_to_three` as an instance of the
    general monotone-coordination mechanism. -/
theorem cubic_dim_three_unique :
    ∃! d : ℕ, 1 ≤ d ∧ forsCount cubicCoord d = 5 := by
  refine ⟨3, ⟨by norm_num, by unfold forsCount cubicCoord; norm_num⟩, ?_⟩
  rintro d ⟨hd, h5⟩
  exact (cubic_five_iff_three hd).1 h5

/-! ## A second, contrasting family

To show the uniqueness is genuinely *family-dependent* (the target value `5`
selects different dimensions in different lattice families), consider an
"even-coordination" family with `coord d = 2*d + 2` (e.g. an extra pair of
body-diagonal-type neighbours).  There the FORS core has `2*d + 1` directions, so
the five-fold count is reached at `d = 2`, not `d = 3` — yet it is still unique,
again by the same monotone-coordination engine. -/

def shiftedCoord (d : ℕ) : ℕ := 2 * d + 2

theorem shiftedCoord_strictMono : StrictMono shiftedCoord := by
  intro a b hab; unfold shiftedCoord; omega

theorem shifted_five_iff_two {d : ℕ} :
    forsCount shiftedCoord d = 5 ↔ d = 2 := by
  unfold forsCount shiftedCoord; omega

theorem shifted_dim_two_unique :
    ∃! d : ℕ, forsCount shiftedCoord d = 5 := by
  refine ⟨2, by unfold forsCount shiftedCoord; norm_num, ?_⟩
  intro d h5
  exact (shifted_five_iff_two).1 h5

end FeasibilityLattice
