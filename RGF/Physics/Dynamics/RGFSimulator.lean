/-
  RGF/RGFSimulator.lean

  Direction III(a) — Executable semantics: an RGF dynamics simulator.

  Lean 4 is also a functional programming language, so the RGF lattice dynamics
  can be *run*, not only reasoned about.  This file gives fully **computable**
  models of the two core RGF processes together with machine-checked invariants.

  * **`Z₅` clock dynamics.**  `clockStep` advances each site's internal phase by
    one unit of `ZMod 5`.  The dynamics has period five — five-fold locking as an
    executable fact: `clockStep^[5] = id` (`clockStep_period`), and the closed
    form `clockStep^[n] σ = σ + n` (`clockStep_iterate`).

  * **`Z₅` ASEP (asymmetric simple exclusion).**  `hop` is the totally
    asymmetric hop on a ring of occupancies (a cyclic rotation); it conserves the
    particle number (`shift_conserves`), the hydrodynamic conservation law.  A
    concrete run is checked by `decide` (`asep_run_example`).

  * **Renormalisation-group flow.**  `rgMap x = x²` is a toy `β`-function whose
    fixed points are exactly `0` and `1` (`rgMap_fixedPoints`); `0 < x < 1` is
    irrelevant (flows toward `0`), `x > 1` relevant (`rgMap_irrelevant`,
    `rgMap_relevant`).
-/
import Mathlib

open scoped BigOperators
open Finset

namespace RGF.Simulator

/-! ## 1. Executable `Z₅` clock dynamics -/

/-- The five internal phases, as the computable ring `ZMod 5`. -/
abbrev Z5 := ZMod 5

/-- One RGF clock step: every site's phase advances by one (mod 5). -/
def clockStep {L : ℕ} (σ : Fin L → Z5) : Fin L → Z5 := fun i => σ i + 1

/-
Closed form of the iterated clock: after `n` steps every phase is `+ n`.
-/
theorem clockStep_iterate {L : ℕ} (σ : Fin L → Z5) (n : ℕ) :
    (clockStep)^[n] σ = fun i => σ i + (n : Z5) := by
  induction n <;> simp_all +decide [ Function.iterate_succ_apply' ];
  exact funext fun i => by simp +decide [ clockStep, add_assoc ] ;

/-
**Five-fold locking, executably:** the clock dynamics has period five.
-/
theorem clockStep_period {L : ℕ} (σ : Fin L → Z5) :
    (clockStep)^[5] σ = σ := by
  exact funext fun i => by erw [ clockStep_iterate ] ; simp +decide ;

/-! ## 2. Executable `Z₅` ASEP on a ring -/

/-- Site occupancies on a ring, as a (cyclic) list of Booleans. -/
abbrev Occ := List Bool

/-- The totally asymmetric hop on the ring: rotate the occupancies by one site. -/
def hop (σ : Occ) : Occ := σ.rotate 1

/-- The number of particles in a configuration. -/
def particleCount (σ : Occ) : ℕ := σ.count true

/-
**Conservation law:** the asymmetric hop preserves the particle number.
-/
theorem shift_conserves (σ : Occ) :
    particleCount (hop σ) = particleCount σ := by
  exact List.Perm.count_eq ( List.rotate_perm σ 1 ) true

/-- A concrete ASEP run on five sites: one hop rotates the profile, checked by
    the kernel. -/
theorem asep_run_example :
    hop [true, false, true, false, false]
      = [false, true, false, false, true] := by
  decide

/-! ## 3. Executable renormalisation-group flow -/

/-- A toy RG map (decimation `β`-function) `x ↦ x²`. -/
def rgMap (x : ℝ) : ℝ := x^2

/-
The RG fixed points are exactly the trivial (`0`) and Gaussian (`1`) ones.
-/
theorem rgMap_fixedPoints (x : ℝ) : rgMap x = x ↔ x = 0 ∨ x = 1 := by
  exact ⟨ fun h => or_iff_not_imp_left.mpr fun h0 => mul_left_cancel₀ h0 <| by unfold rgMap at h; linarith, fun h => by rcases h with ( rfl | rfl ) <;> unfold rgMap <;> norm_num ⟩

/-
Couplings in `(0,1)` are irrelevant: one RG step decreases them toward `0`.
-/
theorem rgMap_irrelevant {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : rgMap x < x := by
  exact pow_lt_self_of_lt_one₀ h0 h1 ( by norm_num )

/-
Couplings above `1` are relevant: one RG step increases them.
-/
theorem rgMap_relevant {x : ℝ} (h : 1 < x) : x < rgMap x := by
  exact lt_self_pow₀ h ( by norm_num )

end RGF.Simulator