/-
# Tests.CrossValidation — numerical cross-validation (independent re-check)

This file belongs to the **separate `RGFTests` library** (optimal plan step P3): it is
*not* part of the main library, so the main library can never depend on it.  Its value
is a genuine redundant check: **two independent derivations both reach the same numerical
answer `(5, 3, 6)`**.

* `intrinsic_answer` — the answer obtained from the main path (the intrinsic
  simplified-core criterion, via the `RGF.Bridge` facade).
* `orthogonal_answer` — the answer obtained from the *orthogonal* generation-axis rule
  (`OrthoStepRule`), an independent geometric derivation.
* `cross_validation` — the two independent paths point to the **same** numerical answer.

The point is "two independent derivations both reach `(5,3,6)`", not "two proof terms are
equal" (which would be content-free by proof irrelevance).
-/

import Mathlib
import RGF.Generative.Bridge.Bridge
import RGF.Generative.Assembly.SimplifiedCore
import RGF.Generative.Locking.OrthogonalStepRule

namespace RGF.Tests

open RGF.LatticeUniquenessGap
open RGF.OrthogonalStepRule

/-- **Main path.**  The numerical answer obtained from the intrinsic simplified core. -/
theorem intrinsic_answer {k n₂ : ℕ} {L : LatticeCandidate}
    (h : RGF.SimplifiedCore.CoreBundle k n₂ L) :
    (k, L.dim, L.coord) = RGF.Bridge.answer :=
  RGF.Bridge.core_result h

/-- **Orthogonal path.**  The numerical answer obtained from the orthogonal
    generation-axis rule: a genuine orthonormal axis family with `forwardCount = 5`
    forces the cubic lattice `(dim, coord) = (3, 6)`, and the mode order is the
    forward count `5`. -/
theorem orthogonal_answer {d : ℕ} (R : OrthoStepRule d) (hd : 0 < d)
    (hlock : forwardCount (OrthoStepRule.toCandidate R) = 5) :
    (forwardCount (OrthoStepRule.toCandidate R),
      (OrthoStepRule.toCandidate R).dim, (OrthoStepRule.toCandidate R).coord)
      = RGF.Bridge.answer := by
  obtain ⟨hdim, hcoord⟩ := OrthoStepRule.ortho_locking_forces_cubic R hd hlock
  rw [hlock, hdim, hcoord]; rfl

/-- **Cross-validation.**  The intrinsic path and the orthogonal path point to the
    same numerical answer `(5, 3, 6)`. -/
theorem cross_validation
    {k n₂ : ℕ} {L : LatticeCandidate} (h : RGF.SimplifiedCore.CoreBundle k n₂ L)
    {d : ℕ} (R : OrthoStepRule d) (hd : 0 < d)
    (hlock : forwardCount (OrthoStepRule.toCandidate R) = 5) :
    (k, L.dim, L.coord)
      = (forwardCount (OrthoStepRule.toCandidate R),
          (OrthoStepRule.toCandidate R).dim, (OrthoStepRule.toCandidate R).coord) := by
  rw [intrinsic_answer h, orthogonal_answer R hd hlock]

end RGF.Tests
