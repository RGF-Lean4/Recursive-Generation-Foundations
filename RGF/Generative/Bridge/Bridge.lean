/-
# RGF.Bridge — the single external facade (one exit)

This is the *facade* described in the optimal plan (step P2): the single, stable
external exit of the load-bearing core.  Downstream "applications" only ever refer to
the **name and type** of `RGF.Bridge.answer` and `RGF.Bridge.core_result`; they never
import a concrete proof file.  Should the load-bearing proof ever be re-based, only
this one file changes.
-/

import Mathlib
import RGF.Generative.Assembly.SimplifiedCore
import RGF.Generative.Uniqueness.AssumptionMinimalityV2
import RGF.Physics.Emergence.FirstPrinciples

namespace RGF.Bridge

open RGF.LatticeUniquenessGap

/-- The framework's **numerical answer**: the locked triple `(mode order k,
    spatial dimension d, coordination number z) = (5, 3, 6)`. -/
def answer : ℕ × ℕ × ℕ := (5, 3, 6)

/-- **The single external load-bearing exit.**  From the simplified core bundle
    (two independent locks + one dictionary) the locked triple equals `answer`. -/
theorem core_result {k n₂ : ℕ} {L : LatticeCandidate}
    (h : RGF.SimplifiedCore.CoreBundle k n₂ L) :
    (k, L.dim, L.coord) = answer := by
  obtain ⟨hk, hd, hc⟩ := RGF.SimplifiedCore.simplified_core_conclusion h
  simp [answer, hk, hd, hc]

/-- The facade is not vacuous: the simplified core is realized by the 3D simple-cubic
    lattice, so some bundle reaches `answer`. -/
theorem core_result_satisfiable :
    ∃ (k _n₂ : ℕ) (L : LatticeCandidate), (k, L.dim, L.coord) = answer := by
  obtain ⟨k, _n₂, L, h⟩ := RGF.SimplifiedCore.simplified_core_satisfiable
  exact ⟨k, _n₂, L, core_result h⟩

/-- **The upgraded (P6) external exit.**  The same numerical `answer` `(5,3,6)`
    now follows from the *single* structural primitive
    `RGF.AssumptionMinimalityV2.AntisymDualLayerCore` — i.e. without taking the
    three dynamical scalar inputs `coupling`, `depth2`, `oddk` as separate
    assumptions, since the primitive *derives* them as theorems.  The original
    `core_result` is kept verbatim, so no downstream consumer breaks. -/
theorem core_result_v2 {k n₂ : ℕ} {L : LatticeCandidate}
    (C : RGF.AssumptionMinimalityV2.AntisymDualLayerCore k n₂ L) :
    (k, L.dim, L.coord) = answer := by
  obtain ⟨hk, hd, hc⟩ := C.conclusion
  simp [answer, hk, hd, hc]

/-- **The first-principle external exit.**  The same numerical `answer` `(5, 3, 6)`
    now follows from the *two first principles only* —
    `RGF.FirstPrinciples.MinimalEmergent k` (Axiom M, minimal non-solvable order)
    and `RGF.FirstPrinciples.CP d` (Axiom G, the `SO(d)` rotation-equals-vector
    dimension equation) — with no target numeral assumed anywhere.  The mode order
    is `k`, the spatial dimension `d`, and the coordination number is the
    simple-cubic nearest-neighbour count `2 * d`. -/
theorem core_result_first_principle {k d : ℕ}
    (hM : RGF.FirstPrinciples.MinimalEmergent k) (hG : RGF.FirstPrinciples.CP d) :
    (k, d, 2 * d) = answer := by
  obtain ⟨hk, hd, hz, _⟩ :=
    RGF.FirstPrinciples.first_principle_forces_k_five_d_three hM hG
  simp [answer, hk, hd]

/-- The first-principle facade is non-vacuous: `k = 5`, `d = 3` realise both
    first principles, giving `answer`. -/
theorem core_result_first_principle_satisfiable :
    ∃ k d : ℕ, RGF.FirstPrinciples.MinimalEmergent k ∧ RGF.FirstPrinciples.CP d ∧
      (k, d, 2 * d) = answer :=
  ⟨5, 3, RGF.FirstPrinciples.minimalEmergent_iff_five.mpr rfl,
    RGF.FirstPrinciples.cp_iff_three.mpr rfl, by simp [answer]⟩

/-- The upgraded facade is also non-vacuous. -/
theorem core_result_v2_satisfiable :
    ∃ (k _n₂ : ℕ) (L : LatticeCandidate), (k, L.dim, L.coord) = answer := by
  obtain ⟨k, _n₂, L, ⟨C⟩⟩ :=
    RGF.AssumptionMinimalityV2.antisymDualLayerCore_satisfiable
  exact ⟨k, _n₂, L, core_result_v2 C⟩

end RGF.Bridge
