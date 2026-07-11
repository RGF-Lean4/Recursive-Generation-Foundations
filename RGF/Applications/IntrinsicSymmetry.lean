import Mathlib
import RGF.Physics.Emergence.LatticeToFORS
import RGF.Generative.Locking.StrengthenedFiveLocking
import RGF.Applications.OrbitCounting

/-!
# Intrinsic Theorem: The Critical Symmetry Structure Grows From the Foundation, Rather Than Being Imported Externally
# Intrinsic Theorem: The Critical Symmetry Structure Grows From the Foundation

## Background: the gap left by the previous step

`OrbitCounting.lean` / `EmergentDimensionRelation.lean` replaced the "numerical bridging hypothesis"
(`MembraneCoreBridge`) by a **structural hypothesis**: the set of admissible directions at the critical fixed point *carries*
a transitive `D_k` action whose direction stabiliser is a reflection. There, this structure was
**imported externally** in the form of `variable`s (an abstract type `Dir` + `[MulAction (DihedralGroup k) Dir]` +
`[IsPretransitive ...]` + `realize : Dir ≃ ↥(allowedNext)`):
the template did not yet grow out of the lattice foundation.

This file closes that gap. We turn the statement "the critical symmetry structure exists" **into a theorem in its own right**:

* We no longer introduce an abstract `Dir`; the action **lives directly on the lattice's set of admissible directions `↥(allowedNext incoming)`**
  (via `equivPullbackAction`, which pulls the dihedral action on `ZMod (2d-1)` back to
  the direction set itself).
* The dihedral group's **order `2d-1` is not an externally prescribed `k`; it is the lattice coordination number `2d` minus the one back-step direction forbidden by G3,**
  **i.e. the intrinsic count supplied by the combinatorial theorem `card_allowedNext`.**

Main conclusion `intrinsic_dihedral`:

> For every dimension `d ≥ 1`, the lattice's set of admissible directions `↥(allowedNext incoming)` **naturally** carries a
> dihedral action of order `2d-1` that is transitive and whose direction stabiliser is a reflection -- **with no external hypothesis whatsoever**.

Furthermore, `dihedral_iff` reduces the entire *structural* premise to a single **transparent scalar equality**:

> `↥(allowedNext incoming)` carries a (transitive, reflection-stabiliser) dihedral action of order `k`
> `⟺ 2d-1 = k`.

This shows that the "critical symmetry structure", imported as a black box in the previous version, has its entire content **exactly equivalent to**
the numerical condition `2d-1 = k`, while its **constructible half** ("existence") is now a **theorem**. Combining it with
the order `k = 5` given by the locking-membrane representation theory (the unique order selected by `n₂ = (k-1)/2 = 2`), one immediately obtains
`d = 3` (`emergent_dimension_intrinsic`, `dihedral_five_iff_three`).

## Logical chain (everything with zero `sorry` and zero custom `axiom`)

```
lattice (coordination number 2d, G1 exclusivity, G3 recovery time R=1)
   │  card_allowedNext
   ↓
number of admissible directions = 2d-1            [combinatorial theorem]
   │  intrinsic_dihedral (pull back the D_{2d-1} action on ZMod)
   ↓
direction set intrinsically carries a transitive D_{2d-1} action, reflection stabiliser   [theorem, not hypothesis]
   │  HasDihedralReflection.card_eq (orbit-stabiliser)
   ↓
carries D_k (transitive + reflection stabiliser)  ⟺  2d-1 = k       [equivalence theorem dihedral_iff]
   │  + locking membrane n₂=2 ⟹ k=5 (locking_membrane_uniqueness)
   ↓
d = 3                                          [emergent_dimension_intrinsic]
```

The only remaining physical input is the single *scalar* neutral-mode / spectral condition "the order `k` of the locking symmetry equals the order `2d-1` of the direction symmetry";
it is no longer an opaque structural template, but is
completely characterised by `dihedral_iff` as the scalar equality `2d-1 = k`.
-/

open MulAction DihedralGroup LatticeToFORS

namespace RGF.IntrinsicSymmetry

/-! ## Part 1: pulling the action back to an arbitrary type (no external template needed)

`equivPullbackAction` pulls a group action on `Y` back along a bijection `e : X ≃ Y` to an action on `X`,
`g • x := e.symm (g • e x)`. This lets the dihedral action **live directly on the lattice direction set**,
without having to stay on the abstract `ZMod k` and then use an equivalence to "match" it. -/

/-- Pull a group action on `Y` back along a bijection `e : X ≃ Y` to a group action on `X`. -/
def equivPullbackAction {G X Y : Type*} [Group G] [MulAction G Y] (e : X ≃ Y) :
    MulAction G X where
  smul g x := e.symm (g • e x)
  one_smul x := by show e.symm ((1 : G) • e x) = x; simp
  mul_smul g h x := by
    show e.symm ((g * h) • e x) = e.symm (g • e (e.symm (h • e x)))
    simp [mul_smul]

/-! ## Part 2: the critical symmetry structure as a **provable proposition**

`HasDihedralReflection k X`: the type `X` carries a dihedral action of order `k` that is
**transitive**, and such that **the stabiliser of some point has order 2** (a reflection `≅ C₂`). This is exactly the "critical symmetry structure" that the previous version
assumed in `variable` form, now written as a proposition that can be proved/refuted. -/

/-- **Critical symmetry structure (propositional form)**: `X` carries a transitive dihedral action of order `k`,
    and there exists a point whose stabiliser has order 2 (a reflection). -/
def HasDihedralReflection (k : ℕ) (X : Type*) : Prop :=
  ∃ act : MulAction (DihedralGroup k) X,
    (@IsPretransitive (DihedralGroup k) X act.toSMul) ∧
    ∃ x : X, @Nat.card (@stabilizer (DihedralGroup k) X _ act x) = 2

/-- `ZMod k` (vertices of the regular k-gon / k directions) satisfies the critical symmetry structure under the natural `D_k` action. -/
theorem hasDihedralReflection_zmod (k : ℕ) [NeZero k] :
    HasDihedralReflection k (ZMod k) :=
  ⟨RGF.OrbitCounting.dihMulAction k, RGF.OrbitCounting.instIsPretransitive k,
    ⟨0, RGF.OrbitCounting.stab_card_two k 0⟩⟩

/-- **Structure transports along a bijection**: if `Y` has the critical symmetry structure and `e : X ≃ Y`, then after pulling the action back
    `X` also has the critical symmetry structure (both transitivity and the reflection stabiliser transport). -/
theorem hasDihedralReflection_of_equiv {k : ℕ} {X Y : Type*} (e : X ≃ Y)
    (h : HasDihedralReflection k Y) : HasDihedralReflection k X := by
  obtain ⟨act, htrans, x0, hstab⟩ := h
  letI := act
  letI act' := equivPullbackAction (G := DihedralGroup k) e
  refine ⟨act', ?_, e.symm x0, ?_⟩
  · letI := act'
    refine ⟨fun a b => ?_⟩
    obtain ⟨g, hg⟩ := htrans.exists_smul_eq (e a) (e b)
    exact ⟨g, by show e.symm (g • e a) = b; rw [hg]; simp⟩
  · have heq : (@stabilizer (DihedralGroup k) X _ act' (e.symm x0))
        = stabilizer (DihedralGroup k) x0 := by
      ext g
      rw [mem_stabilizer_iff, mem_stabilizer_iff]
      constructor
      · intro hh
        have h2 : e.symm (g • e (e.symm x0)) = e.symm x0 := hh
        simpa using congrArg e h2
      · intro hh
        show e.symm (g • e (e.symm x0)) = e.symm x0
        simp only [Equiv.apply_symm_apply]
        rw [hh]
    rw [heq]; exact hstab

/-- **Every finite type of cardinality `k` intrinsically carries the critical symmetry structure** (constructible direction):
    `Fintype.equivOfCardEq` gives `X ≃ ZMod k`, and then the dihedral action on `ZMod k` is pulled back.
    This shows that "carries a transitive `D_k` action + reflection stabiliser" is **always realisable** for a set of cardinality `k`,
    and is not an externally imposed template. -/
theorem hasDihedralReflection_of_card {k : ℕ} [NeZero k] {X : Type*} [Fintype X]
    (h : Fintype.card X = k) : HasDihedralReflection k X :=
  hasDihedralReflection_of_equiv (Fintype.equivOfCardEq (by rw [h, ZMod.card]))
    (hasDihedralReflection_zmod k)

/-- **Rigidity (orbit-stabiliser)**: conversely, if `X` carries the critical symmetry structure, then its cardinality **must be** `k`.
    (`|X| = |orbit| = |D_k| / |Stab| = 2k / 2 = k`.) -/
theorem HasDihedralReflection.card_eq {k : ℕ} [NeZero k] {X : Type*}
    (h : HasDihedralReflection k X) : Nat.card X = k := by
  obtain ⟨act, htrans, x0, hstab⟩ := h
  letI := act
  letI := htrans
  exact RGF.OrbitCounting.card_of_transitive_dihedral k X x0 hstab

/-! ## Part 3: the intrinsic theorem -- the critical symmetry structure grows from the lattice -/

/-- **Intrinsic theorem**: for every dimension `d ≥ 1`, the lattice's set of admissible directions `↥(allowedNext incoming)`
    **naturally carries** a dihedral action of order `2d-1` that is transitive and whose direction stabiliser is a reflection.

    Key point: the dihedral order `2d-1` is **not an externally prescribed** `k`; it is the lattice coordination number `2d` minus the one back-step direction forbidden by G3,
    i.e. the **intrinsic count** given by the combinatorial theorem `card_allowedNext`. This turns the "critical symmetry structure",
    imported in `variable` form by the previous version, into a **theorem** -- the structure grows from the foundation. -/
theorem intrinsic_dihedral {d : ℕ} (hd : 1 ≤ d) (incoming : LatticeDir d) :
    HasDihedralReflection (2 * d - 1) ↥(allowedNext incoming) := by
  haveI : NeZero (2 * d - 1) := ⟨by omega⟩
  apply hasDihedralReflection_of_card
  rw [Fintype.card_coe, card_allowedNext]

/-- **The relation becomes a theorem (structure lives on the direction set)**: if the lattice's set of admissible directions carries a critical symmetry
    structure of order `k`, then `2d - 1 = k`. Here there is **no longer any abstract `Dir` or `realize`** -- the structure lives directly on
    `↥(allowedNext incoming)`, and the relation is derived from rigidity `card_eq` + `card_allowedNext`. -/
theorem relation_intrinsic {d k : ℕ} [NeZero k] (incoming : LatticeDir d)
    (h : HasDihedralReflection k ↥(allowedNext incoming)) : 2 * d - 1 = k := by
  have hc := h.card_eq
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, card_allowedNext] at hc

/-- **Structural hypothesis ⟺ scalar equality**: the lattice's set of admissible directions carries a critical symmetry structure of order `k`
    **if and only if** `2d - 1 = k`.

    This equivalence is the core transparency result of this file: the entire *structural* premise imported as a black box by the previous version
    (transitive `D_k` action + reflection stabiliser) has its full logical content **exactly equal to** the scalar equality
    `2d-1 = k`; and its "existence" half (`mpr`) is now **proved** by `intrinsic_dihedral`. -/
theorem dihedral_iff {d : ℕ} (hd : 1 ≤ d) {k : ℕ} [NeZero k] (incoming : LatticeDir d) :
    HasDihedralReflection k ↥(allowedNext incoming) ↔ 2 * d - 1 = k := by
  refine ⟨relation_intrinsic incoming, fun hk => ?_⟩
  rw [← hk]; exact intrinsic_dihedral hd incoming

/-! ## Part 4: dimension locking to three dimensions (intrinsic + locking membrane) -/

/-- **Dimension locking (intrinsic version)**: given the three locking-membrane conditions `StrengthenedLockingMembraneConditions k`
    (whose unique representation-theoretic solution is `k = 5`), together with the lattice's set of admissible directions **intrinsically carrying** a critical
    symmetry structure of order `k` (the neutral-mode / spectral condition: locking symmetry = direction symmetry), one simultaneously obtains
    `2d - 1 = k`, `k = 5`, `d = 3`.

    Compared with the previous version: the critical symmetry structure is no longer an external template on an abstract `Dir`, but the proposition
    **living directly on the lattice direction set** `HasDihedralReflection k ↥(allowedNext incoming)`, and its "existence"
    half is already established as a theorem by `intrinsic_dihedral`. -/
theorem emergent_dimension_intrinsic {d k : ℕ} [NeZero k]
    (hk : StrengthenedLockingMembraneConditions k) {_hd : 1 ≤ d} (incoming : LatticeDir d)
    (hsym : HasDihedralReflection k ↥(allowedNext incoming)) :
    (2 * d - 1 = k) ∧ k = 5 ∧ d = 3 := by
  have hrel := relation_intrinsic incoming hsym
  have hk5 := locking_membrane_uniqueness k hk
  exact ⟨hrel, hk5, by omega⟩

/-- **Equivalent characterisation of dimension locking at k = 5**: on the cubic lattice with `d ≥ 1`, the direction set carries the (transitive,
    reflection-stabiliser) critical symmetry structure of `D₅` **if and only if** `d = 3`.

    `mpr` follows from `intrinsic_dihedral`, giving that the structure **really exists** when `d = 3` (non-vacuous);
    `mp` follows from rigidity, giving that only `d = 3` is possible. -/
theorem dihedral_five_iff_three {d : ℕ} (hd : 1 ≤ d) (incoming : LatticeDir d) :
    HasDihedralReflection 5 ↥(allowedNext incoming) ↔ d = 3 := by
  rw [dihedral_iff hd incoming]; omega

/-! ## Part 5: non-vacuous witness -- the three-dimensional direction set really does intrinsically carry the D₅ structure -/

/-- **Non-vacuous (intrinsic construction)**: on the three-dimensional cubic lattice, the set of admissible directions `↥(allowedNext incoming)`
    **really does** intrinsically carry a transitive dihedral action of order 5 with reflection stabiliser -- given directly by `intrinsic_dihedral`
    at `d = 3`, with **no external hypothesis and no extra input beyond the bijection imported via `equivOfCardEq`**
    (the pulled-back bijection comes from the lattice's own `card_allowedNext = 5`). -/
theorem intrinsic_witness (incoming : LatticeDir 3) :
    HasDihedralReflection 5 ↥(allowedNext incoming) :=
  (dihedral_five_iff_three (by norm_num) incoming).mpr rfl

/-- **Complete intrinsic chain (three-dimensional, explicit)**: the three-dimensional lattice simultaneously gives
    `2·3 - 1 = 5`, `k = 5`, `d = 3`, with the critical symmetry structure provided intrinsically by `intrinsic_witness`,
    with no external structural hypothesis. -/
theorem emergent_dimension_intrinsic_witness (incoming : LatticeDir 3) :
    (2 * 3 - 1 = 5) ∧ (5 : ℕ) = 5 ∧ (3 : ℕ) = 3 :=
  emergent_dimension_intrinsic (d := 3) (k := 5) five_satisfies_locking_membrane
    (_hd := by norm_num) incoming (intrinsic_witness incoming)

end RGF.IntrinsicSymmetry
