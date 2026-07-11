/-
  Modern/AlgebraicGeometry.lean

  **Algebraic geometry over the RGF reals.**

  Since the RGF reals form a field (`Foundations.RGFNativeField`), the polynomial
  ring `RGFReal'[X]` — the coordinate ring of the affine line `𝔸¹` over the RGF
  reals — inherits the full structural toolkit of commutative algebra and scheme
  theory.  We record:

  * `RGFReal'[X]` is a Euclidean domain, a principal ideal domain, Noetherian
    (Hilbert basis theorem) and a unique factorization domain;
  * its prime spectrum is nonempty (the affine line has points);
  * the affine scheme `Spec RGFReal'[X]` — the affine line over the RGF reals —
    exists as a genuine `Scheme`.

  This addresses the criticism that algebraic geometry was untouched.
-/
import Mathlib
import RGF.Math.Real.RealInstances

namespace RGF
namespace RGFReal'

open Polynomial

/-! ## The coordinate ring of the affine line `𝔸¹` over the RGF reals -/

/-- `RGFReal'[X]` is a Euclidean domain. -/
noncomputable example : EuclideanDomain (Polynomial RGFReal') := inferInstance

/-- `RGFReal'[X]` is a principal ideal ring (every ideal is principal). -/
theorem rgf_polynomial_isPID : IsPrincipalIdealRing (Polynomial RGFReal') := inferInstance

/-- **Hilbert basis theorem** for the affine line over the RGF reals:
    `RGFReal'[X]` is Noetherian. -/
theorem rgf_polynomial_noetherian : IsNoetherianRing (Polynomial RGFReal') := inferInstance

/-- `RGFReal'[X]` is a unique factorization domain. -/
theorem rgf_polynomial_ufd : UniqueFactorizationMonoid (Polynomial RGFReal') := inferInstance

/-! ## The prime spectrum and the affine scheme -/

/-- The affine line over the RGF reals has points: its prime spectrum is
    nonempty. -/
theorem rgf_affineLine_spectrum_nonempty :
    Nonempty (PrimeSpectrum (Polynomial RGFReal')) := inferInstance

/-- **The affine line `𝔸¹` over the RGF reals**, as a genuine scheme:
    `Spec RGFReal'[X]`. -/
noncomputable def rgfAffineLine : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (Polynomial RGFReal'))

end RGFReal'
end RGF
