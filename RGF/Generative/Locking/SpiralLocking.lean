import Mathlib

/-!
# Spiral-locking derivation: the non-degeneracy external condition (U)

This file provides the type interface on which the final output of the FORS layer
depends. The FORS module `LockingNonDegeneracy.lean` imports
`RGF.SpiralLocking` and uses `LockingNonDegenerate` and `ZetaNontrivialZero`
from the namespace `RGF.SpiralLocking`.

* `ZetaNontrivialZero`: the set of zeros of the Riemann zeta function lying in the
  critical strip `0 < Re s < 1`.
* `spiralDual`: the spiral-duality map `σ(s) = 1 - conj s`.
* `LockingNonDegenerate S`: the locking non-degeneracy property on a set `S` — if
  `s` and its spiral dual `σ(s)` both belong to `S`, then they are equal (note that
  `s = 1 - conj s ↔ Re s = 1/2`).
-/

namespace RGF.SpiralLocking

/-- The set of nontrivial zeros of the Riemann zeta function (the zeros inside the
    critical strip). -/
def ZetaNontrivialZero : Set ℂ :=
  {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- The spiral-duality map `σ(s) = 1 - conj s`. -/
def spiralDual (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

/-- **Locking non-degeneracy**: for any `s` in the set `S`, if its spiral dual
    `σ(s) = 1 - conj s` is also in `S`, then `s = σ(s)` (equivalently, `Re s = 1/2`). -/
def LockingNonDegenerate (S : Set ℂ) : Prop :=
  ∀ s ∈ S, spiralDual s ∈ S → s = spiralDual s

end RGF.SpiralLocking
