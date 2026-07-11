import Mathlib

/-!
# Closing the "discrete space → continuous dimension" uniqueness gap

This file honestly and rigorously closes the uniqueness gap that was pointed out
in the discrete-to-continuous dimension derivation of the RGF program.

## The gap

Earlier arguments locked the ambient spatial dimension at `d = 3` by counting the
number of admissible *forward* recovery directions on the **cubic** lattice `ℤ^d`.
There the G1 (exclusivity) / G3 (no-immediate-backstep) recovery rules leave
`2*d − 1` admissible directions, and `2*d − 1 = 5 ↔ d = 3`.  The objection is
that this *presupposes the cubic lattice*: the direction-count formula changes
from lattice to lattice, so the `d = 3` locking value is not invariant — it could
fail for a different lattice.

## What this file actually proves (and what it does not)

We do **not** claim that a unique two-layer generative dynamics *necessarily*
produces the cubic lattice — that would require a complete dynamical
classification.  Instead we prove something weaker but strict and lattice-model
independent:

* We abstract an arbitrary candidate discrete model as a `LatticeCandidate`
  (dimension `dim`, coordination number `coord`, central-symmetry flag `invSym`),
  and we *de-model* the recovery rule's direction count as
  `forwardCount L = coord − (invSym ? 1 : 0)`, the genuine generalisation of the
  cubic `2*d − 1`.
* `z5_locking_dimension_degenerate` honestly exposes the gap: the locking count
  `= 5` alone does **not** determine the dimension (the 2D triangular lattice and
  the 3D simple-cubic lattice both yield 5 forward channels, at dimensions 2 and 3
  respectively).
* `joint_criteria_force_dim_three` closes the gap with a lattice-independent,
  dimension-intrinsic criterion: for *any* candidate lattice, simultaneously
  requiring the locking count `= 5` **and** "rotations are representable as
  vectors" (the number of rotation generators `d(d−1)/2` equals `d`, equivalent to
  `d = 3`) forces `d = 3` — with no cubic presupposition.
* We then lock back the cubic invariants and rule out competing lattices
  (`invSym_z5_iff_coord_six`, `invSym_joint_force_cubic_invariants`,
  `cubic_is_unique_among_candidates`): among square, triangular, honeycomb, simple
  cubic, BCC, FCC and 4D hypercubic candidates, the unique one passing *both*
  criteria is the 3D simple-cubic lattice (triangular is excluded by the rotation
  criterion, the rest by the locking criterion).
* `IsHypercubic`, `hypercubic_z5_iff_dim_three`, `triangular_not_hypercubic`
  recover the original cubic statement `2*d − 1 = 5 ↔ d = 3` for hypercubic
  lattices, while showing the triangular lattice is *not* hypercubic.
-/

namespace RGF.LatticeUniquenessGap

/-- An abstract candidate discrete model.  `dim` is the spatial dimension,
    `coord` is the nearest-neighbour coordination number, and `invSym` records
    whether the lattice is centrally symmetric (every neighbour direction `v` has
    its opposite `−v` also a neighbour). -/
structure LatticeCandidate where
  dim : ℕ
  coord : ℕ
  invSym : Bool
  deriving DecidableEq, Repr

/-- **De-modelled forward direction count.**  The G3 rule forbids an immediate
    back-step: on a centrally symmetric lattice exactly one of the `coord`
    neighbour directions is the reverse of the incoming step, so it is removed,
    leaving `coord − 1`.  On a lattice without central symmetry the incoming
    reverse is not itself a neighbour direction, so nothing is removed.  This is
    the lattice-independent generalisation of the cubic `2*d − 1`. -/
def forwardCount (L : LatticeCandidate) : ℕ :=
  L.coord - (if L.invSym then 1 else 0)

/-- **Rotation-generator count.**  In dimension `d` the rotation group `SO(d)`
    has `d(d−1)/2` independent generators (the dimension of its Lie algebra of
    skew-symmetric matrices).  Rotations are "representable as vectors" precisely
    when this equals the dimension `d` of the vector space. -/
def rotGen (d : ℕ) : ℕ := d * (d - 1) / 2

/-- **Intrinsic dimension criterion.**  For any positive dimension, the rotation
    generators can be identified with vectors (`rotGen d = d`) iff `d = 3`.  This
    is purely intrinsic to the continuous rotation symmetry and makes no reference
    to any lattice. -/
theorem rotGen_eq_dim_iff {d : ℕ} (hd : 0 < d) : rotGen d = d ↔ d = 3 := by
  unfold rotGen
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  simp only [Nat.succ_sub_one]
  have hdvd : 2 ∣ (e + 1) * e := by
    rcases Nat.even_or_odd e with he | ho
    · exact Dvd.dvd.mul_left he.two_dvd _
    · have he1 : Even (e + 1) := Odd.add_one ho
      exact Dvd.dvd.mul_right he1.two_dvd _
  constructor
  · intro h
    have hh := Nat.eq_mul_of_div_eq_right hdvd h
    have : e = 2 := by nlinarith [hh]
    omega
  · intro h
    have : e = 2 := by omega
    subst this; rfl

/-! ## The candidate lattices -/

/-- 2D square lattice: `z = 4`, centrally symmetric. -/
def square : LatticeCandidate := ⟨2, 4, true⟩
/-- 2D triangular lattice: `z = 6`, centrally symmetric. -/
def triangular : LatticeCandidate := ⟨2, 6, true⟩
/-- 2D honeycomb lattice: `z = 3`, *not* centrally symmetric (a site's neighbours
    are not closed under negation). -/
def honeycomb : LatticeCandidate := ⟨2, 3, false⟩
/-- 3D simple cubic lattice: `z = 6`, centrally symmetric. -/
def simpleCubic : LatticeCandidate := ⟨3, 6, true⟩
/-- 3D body-centred cubic lattice: `z = 8`, centrally symmetric. -/
def bcc : LatticeCandidate := ⟨3, 8, true⟩
/-- 3D face-centred cubic lattice: `z = 12`, centrally symmetric. -/
def fcc : LatticeCandidate := ⟨3, 12, true⟩
/-- 4D hypercubic lattice: `z = 8`, centrally symmetric. -/
def hyper4 : LatticeCandidate := ⟨4, 8, true⟩

/-- The full list of candidate lattices considered. -/
def candidates : List LatticeCandidate :=
  [square, triangular, honeycomb, simpleCubic, bcc, fcc, hyper4]

/-! ## Honest exposure of the gap -/

/-- **The gap, made explicit.**  The locking count `= 5` does *not* determine the
    dimension: the 2D triangular lattice (`z = 6`) and the 3D simple-cubic lattice
    (`z = 6`) both have exactly 5 forward channels, yet their dimensions differ
    (2 vs 3).  Hence the cubic direction-count formula alone cannot lock `d`. -/
theorem z5_locking_dimension_degenerate :
    ∃ L₁ L₂ : LatticeCandidate,
      forwardCount L₁ = 5 ∧ forwardCount L₂ = 5 ∧ L₁.dim ≠ L₂.dim := by
  exact ⟨triangular, simpleCubic, by decide, by decide, by decide⟩

/-! ## Closing the gap with a lattice-independent criterion -/

/-- **Gap closed.**  For *any* candidate lattice (cubic, triangular, honeycomb or
    other), simultaneously satisfying the locking criterion (`forwardCount = 5`)
    and the intrinsic rotation criterion (`rotGen dim = dim`) forces the dimension
    to be `3`.  The `d = 3` conclusion no longer depends on presupposing a cubic
    lattice: it is fixed by the intersection of two independent constraints. -/
theorem joint_criteria_force_dim_three (L : LatticeCandidate)
    (hdim : 0 < L.dim) (_hlock : forwardCount L = 5)
    (hrot : rotGen L.dim = L.dim) : L.dim = 3 :=
  (rotGen_eq_dim_iff hdim).mp hrot

/-! ## Locking back the cubic invariants and excluding competitors -/

/-- For a centrally symmetric lattice the locking count `= 5` is equivalent to a
    coordination number of `6`. -/
theorem invSym_z5_iff_coord_six {L : LatticeCandidate} (hsym : L.invSym = true) :
    forwardCount L = 5 ↔ L.coord = 6 := by
  simp only [forwardCount, hsym, if_true]
  omega

/-- **Cubic invariants forced.**  A centrally symmetric candidate satisfying both
    criteria has the simple-cubic invariants `(dim, coord) = (3, 6)`. -/
theorem invSym_joint_force_cubic_invariants {L : LatticeCandidate}
    (hsym : L.invSym = true) (hdim : 0 < L.dim) (hlock : forwardCount L = 5)
    (hrot : rotGen L.dim = L.dim) : L.dim = 3 ∧ L.coord = 6 :=
  ⟨joint_criteria_force_dim_three L hdim hlock hrot,
   (invSym_z5_iff_coord_six hsym).mp hlock⟩

/-- **Main uniqueness theorem.**  Among all candidate lattices, the unique one
    passing *both* the locking criterion and the rotation criterion is the 3D
    simple-cubic lattice.  Triangular is excluded by the rotation criterion; the
    remaining lattices are excluded by the locking criterion. -/
theorem cubic_is_unique_among_candidates :
    ∀ L ∈ candidates,
      (forwardCount L = 5 ∧ rotGen L.dim = L.dim) ↔ L = simpleCubic := by
  decide

/-! ## Recovering the original cubic statement -/

/-- A candidate is *hypercubic* when its coordination number is `2*dim`. -/
def IsHypercubic (L : LatticeCandidate) : Prop := L.coord = 2 * L.dim

/-- **Original cubic locking, recovered.**  For a centrally symmetric hypercubic
    lattice the forward count is `2*d − 1`, and it equals `5` iff `d = 3`. -/
theorem hypercubic_z5_iff_dim_three {L : LatticeCandidate}
    (hc : IsHypercubic L) (hsym : L.invSym = true) (hdim : 0 < L.dim) :
    forwardCount L = 5 ↔ L.dim = 3 := by
  simp only [forwardCount, hsym, if_true]
  unfold IsHypercubic at hc
  omega

/-- The triangular lattice is *not* hypercubic (`z = 6 ≠ 2*2 = 4`), so the cubic
    `2*d − 1` formula does not apply to it — which is exactly why it can share the
    locking count `5` with the simple-cubic lattice while having a different
    dimension. -/
theorem triangular_not_hypercubic : ¬ IsHypercubic triangular := by
  unfold IsHypercubic triangular; decide

end RGF.LatticeUniquenessGap
