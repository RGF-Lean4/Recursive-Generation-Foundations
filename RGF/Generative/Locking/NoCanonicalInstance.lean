/-
# NoCanonicalInstance — there is no *canonical* RGF dual-layer instance on subgroups

The bridge module `RGF.CommGenAsStep` exhibits **one** `RGFDualLayer (Subgroup G) (Set G)`
whose `step = modify ∘ generate` equals the commutator generator `commGen H = ⁅H, H⁆`
(namely `commSys G = ⟨genCommutators, modifyClose⟩`).  A natural epistemological
question is whether that instance is *canonical* — i.e. whether every legal
`RGFDualLayer (Subgroup G) (Set G)` is forced to have `step = commGen`.

The answer is **no** (for a non-trivial group): the type `RGFDualLayer (Subgroup G) (Set G)`
is a plain structure of two arbitrary maps, so nothing pins its `step` down to
`commGen`.  We exhibit an explicit legal instance whose `step ≠ commGen`.

## A caveat on the literal statement

The originally requested statement quantified over *all* groups `G`:

    theorem no_canonical_instance_on_subgroups (G : Type*) [Group G] :
        ∃ (L : RGFDualLayer (Subgroup G) (Set G)), L.step ≠ commGen

As literally stated this is **false**.  For the trivial group the lattice
`Subgroup G` is a singleton (`⊥ = ⊤`), so *every* map `Subgroup G → Subgroup G`
is equal — in particular every `L.step` equals `commGen`, and no counterexample
instance can exist.  This is recorded rigorously as
`no_canonical_instance_universal_is_false` below.

The faithful, provable form adds the hypothesis `[Nontrivial G]`, which is exactly
what makes the question non-vacuous (`⊥ ≠ ⊤` gives room for two distinct maps).
That is `no_canonical_instance_on_subgroups` below.
-/

import Mathlib
import RGF.Generative.Locking.CommGenAsStep

open Subgroup
open RGF.StableLockingDynamics
open RGF.CommGenAsStep

namespace RGF.NoCanonicalInstance

variable {G : Type*} [Group G]

/-- **No canonical instance (faithful form).**  For a *non-trivial* group `G`
there is a legal `RGFDualLayer (Subgroup G) (Set G)` whose RGF main generation
operator `step = modify ∘ generate` is **not** the commutator generator
`commGen`.  Hence `commSys` is not singled out by the type alone: the choice
`step = commGen` is a genuine modelling decision, not something forced.

The witness sends every subgroup to the empty entity set and closes every entity
set to the whole group `⊤`; its `step` is the constant map `⊤`, which differs from
`commGen` already at `⊥` (where `commGen ⊥ = ⁅⊥,⊥⁆ = ⊥ ≠ ⊤`). -/
theorem no_canonical_instance_on_subgroups (G : Type*) [Group G] [Nontrivial G] :
    ∃ (L : RGFDualLayer (Subgroup G) (Set G)), L.step ≠ commGen := by
  refine ⟨⟨fun _ => (∅ : Set G), fun _ => (⊤ : Subgroup G)⟩, ?_⟩
  intro h
  have := congrFun h (⊥ : Subgroup G)
  simp [RGFDualLayer.step, commGen] at this

/-- **The literally-universal statement is false.**  Quantified over *all* groups
(including the trivial one) the existence of a counterexample instance fails: for
the trivial group `PUnit` the subgroup lattice is a subsingleton, so every
`L.step` necessarily equals `commGen`.  This documents why the corrected statement
above requires `[Nontrivial G]`. -/
theorem no_canonical_instance_universal_is_false :
    ¬ (∀ (G : Type) [Group G],
        ∃ (L : RGFDualLayer (Subgroup G) (Set G)), L.step ≠ commGen) := by
  intro h
  obtain ⟨L, hL⟩ := h PUnit
  exact hL (Subsingleton.elim _ _)

end RGF.NoCanonicalInstance
