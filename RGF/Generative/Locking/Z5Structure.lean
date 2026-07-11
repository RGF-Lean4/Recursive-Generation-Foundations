/-
# RCDxRGF.Z5Structure — bridging the RCD `Z₅` arithmetic to RGF's general cancellation and central spectrum

Part of the optional bridge library `RCDxRGF`.

RCD papers 2/3/5 formalise single-point arithmetic of the `Z₅` structure:
`Paper5.five_roots_sum` (`5 ∤ p ⇒ Σ over five consecutive phases = 0`),
`Paper5.nonselfconjugate` / `Paper3.nontrivial_chars_paired` (`k ≠ -k`),
`Paper3.real_fifth_root_eq_one` (the only real fifth root of unity is `1`).

RGF generalises these:

* `sum_shift_Z5` — the general cyclic-shift invariance of any `Z₅`-indexed sum
  (the structural reason behind the orbit cancellation);
* `ModeLocking.CentralSpectrum.{eigPair_conj, eigPair_abs, eigPair_not_real}` —
  the central conjugate pair `ρ₀ e^{±iθ₀}`: conjugate, common modulus `ρ₀`, and
  non-real, i.e. the `|σ_c| = 2` / "no real critical eigenvalue" content of paper 3.
-/

import Mathlib
import RGF.Generative.Locking.Z5Cancellation
import RGF.Generative.Locking.ModeLocking

namespace RCDxRGF.Z5Structure

/-- The only real fifth root of unity is `1` (5 is odd, so `-1` is not a fifth
    root of unity). -/
theorem real_fifth_root_eq_one (x : ℝ) (hx : x ^ 5 = 1) : x = 1 := by
  nlinarith [ sq_nonneg ( x^2 - 1 ), sq_nonneg ( x^2 ) ]

/-- **General `Z₅` shift invariance.**  Any `Z₅`-indexed sum is invariant under a
    cyclic shift of the index.  This is the general structural identity behind the
    `Z₅` orbit cancellation that RCD only uses at the level of fifth roots of unity
    (`Paper5.five_roots_sum`). -/
theorem rcd_z5_shift_invariance {β : Type*} [AddCommMonoid β] (f : ZMod 5 → β)
    (j : ZMod 5) :
    ∑ k : ZMod 5, f (k + j) = ∑ k : ZMod 5, f k :=
  sum_shift_Z5 f j

/-- **General orbit cancellation.**  For a genuine `Z₅` group action, the
    antisymmetric part of the generator cancels over each orbit — the general form
    of the asymmetric-coupling cancellation invoked in RCD's low-energy projection. -/
theorem rcd_z5_orbit_cancellation {Ω : Type*} (gen : Ω → Ω → ℝ)
    (action : ZMod 5 → Ω → Ω)
    (action_add : ∀ j k σ, action (j + k) σ = action j (action k σ))
    (σ τ : Ω) :
    ∑ j : ZMod 5, asymPart gen action (action j σ) (action j τ) = 0 :=
  orbit_cancellation gen action action_add σ τ

/-- **Central spectrum structure (the upgrade).**  RCD paper 3's central-spectrum
    claims — a conjugate pair of common modulus with no real critical eigenvalue
    (`|σ_c| = 2`, Bogdanov–Takens excluded) — hold *structurally* for every RGF
    `CentralSpectrum`:

    * `eigPair 0` and `eigPair 1` are complex conjugates;
    * both have modulus `ρ₀`;
    * neither is real.

    This upgrades RCD's single arithmetic fact `real_fifth_root_eq_one` (no real
    fifth root of unity besides `1`) to a full structural description of the
    central conjugate pair. -/
theorem rcd_paper3_central_spectrum (S : ModeLocking.CentralSpectrum) :
    (starRingEnd ℂ) (S.eigPair 0) = S.eigPair 1
      ∧ (∀ i, ‖S.eigPair i‖ = S.rho0)
      ∧ (∀ i, (S.eigPair i).im ≠ 0) :=
  ⟨S.eigPair_conj, S.eigPair_abs, S.eigPair_not_real⟩

/-- **Consistency of RCD's real-root core with the structural non-reality.**  RCD's
    `Paper3.real_fifth_root_eq_one` and the structural `eigPair_not_real` together
    confirm: the only real fifth root of unity is `1`, and the genuine central pair
    is non-real. -/
theorem rcd_no_real_critical_eigenvalue (S : ModeLocking.CentralSpectrum)
    (x : ℝ) (hx : x ^ 5 = 1) :
    x = 1 ∧ (∀ i, (S.eigPair i).im ≠ 0) :=
  ⟨real_fifth_root_eq_one x hx, S.eigPair_not_real⟩

end RCDxRGF.Z5Structure
