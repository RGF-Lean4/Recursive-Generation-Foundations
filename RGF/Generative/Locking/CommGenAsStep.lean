/-
# CommGenAsStep — the `commGen` criterion *is* the RGF main generation operator `step`

The audit (`RGF.LockingAudit`) flags one remaining gap in
`StableLockingFromDynamics`:

> `commGen` (the commutator generator on the subgroup lattice) is never connected
> to the **RGF main generation operator** `step = modify ∘ generate`.  The claim
> "commutator iteration *is* the RGF generation dynamics on the symmetry group"
> was *asserted*, not *proved*: `commGen` lives on `Subgroup G`, while the RGF
> `step` (defined in `RGFBasic` / `RGFUniversality` / `BilayerDuality`) is a
> `modify ∘ generate` composition, and no theorem tied the two together.

This module closes that gap.  It exhibits `commGen` **as a genuine instance of the
RGF dual-layer generation operator** `step = modify ∘ generate`, with a
*mathematically meaningful* two-layer factorisation (not the trivial
`modify = id` universality):

* **generate** (`genCommutators`): a subgroup (rule layer) `H` produces its set of
  commutators `{⁅a, b⁆ | a, b ∈ H}` — the "offspring" / entity layer.
* **modify** (`modifyClose`): a set of entities is closed back into a subgroup
  (a new rule layer) via `Subgroup.closure`.

Because Mathlib *defines* the commutator subgroup as exactly this closure
(`Subgroup.commutator_def`), the composition `modify ∘ generate` is *literally*
`commGen`:

    `commSys.step H = commGen H = ⁅H, H⁆`   (`commSys_step`).

Consequences, all now theorems rather than assertions:

* iterating the RGF `step` from the whole group `⊤` reproduces the derived series
  (`commSys_iterate`), so the derived series *is* the orbit of the RGF main
  generation operator;
* RGF fixed points of `commSys` are exactly the perfect subgroups
  (`commSys_isFixedPoint`);
* the dynamical `StableLocking` criterion is exactly "the RGF main generation
  operator, iterated from `⊤`, reaches a non-trivial fixed point"
  (`stableLocking_iff_step`);
* hence, for a finite group, `StableLocking` — now stated purely through the RGF
  `step` operator — is equivalent to non-solvability
  (`rgf_step_locking_iff_not_solvable`), and for the symmetric group to `k ≥ 5`
  (`rgf_step_symmetric_iff_five_le`).

Everything is machine-checked with no `sorry` and no custom `axiom`.
-/

import Mathlib
import RGF.Generative.Locking.StableLockingFromDynamics
import RGF.Generative.Meta.RGFUniversality
import RGF.Physics.Dynamics.BilayerDuality

open Subgroup

namespace RGF.CommGenAsStep

open RGF.StableLockingDynamics

variable {G : Type*} [Group G]

/-! ## 1. The two layers of the commutator generator -/

/-- **Generate (entity layer).**  A rule layer — here a subgroup `H` — generates
its *offspring*: the set of commutators `⁅a, b⁆` with `a, b ∈ H`.  This is the
entity/output layer of the RGF dual-layer step. -/
def genCommutators (H : Subgroup G) : Set G := {g | ∃ g₁ ∈ H, ∃ g₂ ∈ H, ⁅g₁, g₂⁆ = g}

/-- **Modify (rule layer reconstruction).**  A set of generated entities is closed
back into a subgroup (a new rule layer) via `Subgroup.closure`. -/
def modifyClose (S : Set G) : Subgroup G := Subgroup.closure S

/-- The commutator generator packaged as an **RGF dual-layer system**
(`RGFDualLayer`), with `generate = genCommutators` and `modify = modifyClose`.
Its `step = modify ∘ generate` is the RGF main generation operator. -/
def commSys (G : Type*) [Group G] : RGFDualLayer (Subgroup G) (Set G) :=
  ⟨genCommutators, modifyClose⟩

/-! ## 2. Main bridge: the RGF `step` of `commSys` is exactly `commGen` -/

/-- **Main bridge (pointwise).**  The RGF main generation operator
`step = modify ∘ generate` of `commSys` applied to a subgroup `H` is exactly the
commutator generator `commGen H = ⁅H, H⁆`.  This is where the RGF generation
dynamics and the commutator recursion are *identified* — as a theorem, using
`Subgroup.commutator_def`, not by fiat. -/
theorem commSys_step (H : Subgroup G) : (commSys G).step H = commGen H := by
  simp only [RGFDualLayer.step, commSys, modifyClose, genCommutators, commGen,
    Subgroup.commutator_def]

/-- **Main bridge (functional).**  As maps on the subgroup lattice, the RGF main
generation operator of `commSys` and the commutator generator coincide. -/
theorem commSys_step_eq : (commSys G).step = commGen := funext commSys_step

/-- The RGF `step` of `commSys` is also literally the bilayer `step`
`modify ∘ generate` (as defined in `BilayerDuality`), for the same two layers. -/
theorem commSys_step_eq_bilayer :
    (commSys G).step = RGF.Bilayer.step (genCommutators (G := G)) modifyClose := rfl

/-! ## 3. Consequences: the derived series is the RGF orbit -/

/-- **The derived series is the RGF orbit.**  Iterating the RGF main generation
operator `step` of `commSys` from the whole group `⊤` reproduces the derived
series.  Thus the derived series is *exactly* the trajectory of the RGF
generation dynamics. -/
theorem commSys_iterate (n : ℕ) : (commSys G).step^[n] ⊤ = derivedSeries G n := by
  rw [commSys_step_eq]; exact (derivedSeries_eq_iterate G n).symm

/-- **RGF fixed point = perfect subgroup.**  A subgroup is a fixed point of the
RGF main generation operator `commSys.step` iff it is a fixed point of `commGen`
(i.e. a perfect subgroup). -/
theorem commSys_isFixedPoint (H : Subgroup G) :
    (commSys G).IsFixedPoint H ↔ IsCommFixedPoint H := by
  rw [RGFDualLayer.IsFixedPoint, commSys_step, IsCommFixedPoint]

/-! ## 4. The `StableLocking` criterion, stated through the RGF `step` operator -/

/-- **The `commGen` locking criterion is a statement about the RGF `step`
operator.**  Stable locking holds iff iterating the RGF main generation operator
from `⊤` reaches a *non-trivial* fixed point: some stage `H = step^[n] ⊤` is fixed
by `step` and non-trivial. -/
theorem stableLocking_iff_step (G : Type*) [Group G] :
    StableLocking G ↔
      ∃ n, (commSys G).step ((commSys G).step^[n] ⊤) = (commSys G).step^[n] ⊤ ∧
           (commSys G).step^[n] ⊤ ≠ ⊥ := by
  unfold StableLocking
  simp only [← commSys_iterate, Function.iterate_succ_apply']

/-- **`StableLocking` (RGF-step form) ⟺ non-solvability.**  Combining the bridge
with `stableLocking_iff_not_solvable`: for a finite group, the RGF main
generation operator reaching a non-trivial fixed point is equivalent to
non-solvability. -/
theorem rgf_step_locking_iff_not_solvable (G : Type*) [Group G] [Finite G] :
    (∃ n, (commSys G).step ((commSys G).step^[n] ⊤) = (commSys G).step^[n] ⊤ ∧
          (commSys G).step^[n] ⊤ ≠ ⊥) ↔ ¬ IsSolvable G := by
  rw [← stableLocking_iff_step]; exact stableLocking_iff_not_solvable G

/-- **Headline (symmetric group), via the RGF `step` operator.**  The RGF main
generation operator on the subgroup lattice of `S_k`, iterated from `⊤`, reaches
a non-trivial fixed point iff `k ≥ 5`. -/
theorem rgf_step_symmetric_iff_five_le (k : ℕ) :
    (∃ n, (commSys (Equiv.Perm (Fin k))).step ((commSys (Equiv.Perm (Fin k))).step^[n] ⊤)
            = (commSys (Equiv.Perm (Fin k))).step^[n] ⊤ ∧
          (commSys (Equiv.Perm (Fin k))).step^[n] ⊤ ≠ ⊥) ↔ 5 ≤ k := by
  rw [← stableLocking_iff_step]; exact stable_locking_symmetric_iff_five_le k

/-- **Summary.**  In one statement: the RGF main generation operator `step` of
`commSys` *is* the commutator generator `commGen`; iterating it from `⊤` *is* the
derived series; and the resulting non-trivial-fixed-point (stable-locking)
criterion is equivalent to non-solvability and, for `S_k`, to `k ≥ 5`. -/
theorem commGen_step_master (G : Type*) [Group G] [Finite G] :
    ((commSys G).step = commGen) ∧
    (∀ n, (commSys G).step^[n] ⊤ = derivedSeries G n) ∧
    (StableLocking G ↔
      ∃ n, (commSys G).step ((commSys G).step^[n] ⊤) = (commSys G).step^[n] ⊤ ∧
           (commSys G).step^[n] ⊤ ≠ ⊥) ∧
    ((∃ n, (commSys G).step ((commSys G).step^[n] ⊤) = (commSys G).step^[n] ⊤ ∧
           (commSys G).step^[n] ⊤ ≠ ⊥) ↔ ¬ IsSolvable G) :=
  ⟨commSys_step_eq, commSys_iterate, stableLocking_iff_step G,
   rgf_step_locking_iff_not_solvable G⟩

end RGF.CommGenAsStep
