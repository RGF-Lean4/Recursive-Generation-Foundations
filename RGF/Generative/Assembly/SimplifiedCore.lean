import Mathlib
import RGF.Generative.Locking.LockingMembrane
import RGF.Physics.Emergence.LatticeUniquenessGap

/-!
# A simplified logical core for RGF: two independent locks plus a dictionary

This file is an answer, in machine-checked form, to the question *"can the logical
architecture be made simpler?"*.  It does **not** introduce any new mathematics and
it does **not** weaken the existing results: it merely *re-presents* the spine of the
derivation in the smallest faithful shape, reusing the lemmas already proved in
`Invariants.LockingMembrane` and `RGF.LatticeUniquenessGap`.

The key structural observation is that the whole locked conclusion
`(k, dim, coord) = (5, 3, 6)` **factors as a product of two completely independent
one-line uniqueness statements**, glued by a small translation dictionary:

* **Lock A (the quintic lock).**  Purely arithmetic; it mentions only the mode
  order `k` (and the auxiliary mode count `n₂`).  A two-layer dynamics squeezes
  `n₂ = 2`, oddness and the dihedral count then force `k = 5`.  See
  `quintic_lock`.

* **Lock B (the dimension lock).**  Purely geometric; it mentions only the spatial
  dimension `d`.  The "rotations are vectors" criterion `rotGen d = d` forces
  `d = 3`.  See `dimension_lock`.

Crucially, the *statement* of Lock A never mentions `d`, and the *statement* of
Lock B never mentions `k`.  So the two halves of the system are logically
orthogonal — this is exactly what `core_independence` records.  The remaining
content (`coord = 6`) is not a third lock but a one-step **dictionary** translating
the mode order into a lattice coordination number (`coordination_dictionary`).

Finally `simplified_core` regroups the eight load-bearing assumptions of
`RGF.AssumptionMinimality.RGFCoreAssumptions` into just **three conceptual
bundles** — dynamics, geometry, dictionary — and re-derives `(5, 3, 6)`.  This is
the precise sense in which the architecture can be simplified: not by deleting any
assumption (each is provably necessary), but by collapsing its *conceptual surface*
from eight scattered hypotheses to two independent locks and a dictionary.
-/

open RGF.LatticeUniquenessGap

namespace RGF.SimplifiedCore

/-! ## Lock A — the quintic lock (arithmetic; mentions only `k`) -/

/-- **Lock A.**  The two-layer squeeze `2 ≤ n₂ ≤ 2` together with oddness of the
    mode order and the dihedral representation count `n₂ = num2DIrreps k` forces
    `k = 5`.  Note the statement involves only `k` and the auxiliary `n₂`; it makes
    no reference to any spatial dimension or lattice. -/
theorem quintic_lock {k n₂ : ℕ} (hlow : 2 ≤ n₂) (hup : n₂ ≤ 2)
    (hodd : Odd k) (hrep : n₂ = num2DIrreps k) : k = 5 := by
  have hn2 : n₂ = 2 := le_antisymm hup hlow
  exact odd_n2_eq_two_implies_five k hodd (by rw [← hrep, hn2])

/-! ## Lock B — the dimension lock (geometric; mentions only `d`) -/

/-- **Lock B.**  The intrinsic criterion "rotations are representable as vectors"
    (`rotGen d = d`, i.e. `d(d−1)/2 = d`) forces `d = 3`.  The statement involves
    only the dimension `d`; it makes no reference to the mode order or any
    representation theory. -/
theorem dimension_lock {d : ℕ} (hd : 0 < d) (hrot : rotGen d = d) : d = 3 :=
  (rotGen_eq_dim_iff hd).mp hrot

/-! ## The two locks are logically independent -/

/-- **Independence / factorization.**  The two locks can be discharged in either
    order from disjoint data: the quintic lock uses only `(k, n₂)` information and
    the dimension lock uses only `d` information.  Hence the architecture *factors*
    as the product of two orthogonal uniqueness statements — there is no hidden
    cross-dependence forcing them to be proved together. -/
theorem core_independence {k n₂ d : ℕ}
    (hlow : 2 ≤ n₂) (hup : n₂ ≤ 2) (hodd : Odd k) (hrep : n₂ = num2DIrreps k)
    (hd : 0 < d) (hrot : rotGen d = d) :
    k = 5 ∧ d = 3 :=
  ⟨quintic_lock hlow hup hodd hrep, dimension_lock hd hrot⟩

/-! ## The dictionary — translating mode order into coordination number -/

/-- **Coordination dictionary.**  Once `k = 5` is known, a centrally symmetric
    lattice whose forward-direction count equals the mode order (`forwardCount L = k`)
    automatically has coordination number `6`.  This is a definitional translation,
    not an independent locking step. -/
theorem coordination_dictionary {k : ℕ} {L : LatticeCandidate}
    (hk : k = 5) (hsym : L.invSym = true) (hlock : forwardCount L = k) :
    L.coord = 6 := by
  rw [hk] at hlock
  simp only [forwardCount, hsym, if_true] at hlock
  omega

/-! ## The simplified core: three conceptual bundles -/

/-- **Three-bundle repackaging of the RGF core.**  The eight load-bearing
    assumptions of `RGF.AssumptionMinimality.RGFCoreAssumptions` are regrouped into
    three conceptual blocks:

    * `dynamics` — the two-layer iteration data that pins the mode count `n₂ = 2`;
    * `geometry` — the oddness of the generator, positivity of the dimension and the
      rotation-vector criterion that pin `d = 3`;
    * `dictionary` — the algebra↔geometry translation (representation count, the
      symmetry→direction bridge, central symmetry) that pins the coordination
      number.

    This is strictly the same content as the eight-assumption bundle, only with a
    smaller conceptual surface. -/
structure CoreBundle (k n₂ : ℕ) (L : LatticeCandidate) : Prop where
  /-- Two-layer dynamics: the mode count is squeezed to `n₂ = 2`. -/
  dynamics  : 2 ≤ n₂ ∧ n₂ ≤ 2
  /-- Geometry: odd generator, positive dimension, rotations-are-vectors. -/
  geometry  : Odd k ∧ 0 < L.dim ∧ rotGen L.dim = L.dim
  /-- Algebra↔geometry dictionary. -/
  dictionary : n₂ = num2DIrreps k ∧ forwardCount L = k ∧ L.invSym = true

/-- **The simplified core derives the locked invariants.**  From the three bundles
    above, `(k, dim, coord) = (5, 3, 6)`. -/
theorem simplified_core_conclusion {k n₂ : ℕ} {L : LatticeCandidate}
    (h : CoreBundle k n₂ L) : k = 5 ∧ L.dim = 3 ∧ L.coord = 6 := by
  obtain ⟨hlow, hup⟩ := h.dynamics
  obtain ⟨hodd, hdim, hrot⟩ := h.geometry
  obtain ⟨hrep, hlock, hsym⟩ := h.dictionary
  have hk : k = 5 := quintic_lock hlow hup hodd hrep
  have hd : L.dim = 3 := dimension_lock hdim hrot
  have hc : L.coord = 6 := coordination_dictionary hk hsym hlock
  exact ⟨hk, hd, hc⟩

/-- **Satisfiability.**  The 3D simple-cubic lattice at `k = 5`, `n₂ = 2` realizes
    the simplified core, so the repackaging is not vacuous. -/
theorem simplified_core_satisfiable :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate), CoreBundle k n₂ L :=
  ⟨5, 2, simpleCubic,
    { dynamics  := ⟨le_refl 2, le_refl 2⟩
      geometry  := ⟨by decide, by decide, by decide⟩
      dictionary := ⟨by decide, by decide, rfl⟩ }⟩

end RGF.SimplifiedCore
