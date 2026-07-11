/-
  Paper 10 — "Effective emergence of fundamental physics under time-domain coarse-graining renormalization flow: from discrete dynamics to
  the information-localization phase diagram"
  (Effective emergence of fundamental physics under temporal coarse-graining
  renormalization flow: the information-localization phase diagram), L. Sun 2026.

  Placed in the RGF **Physics** layer (Layer 3 / Physics dynamics).

  Formalizes cleanly-statable cores of the TRCG framework:

  * the **Born rule** `P(i) = |c_i|²`, derived from the Markov limit of local
    transition rates, is a genuine probability distribution when the amplitudes
    are normalized (`∑ |c_i|² = 1`): each `P(i) ∈ [0,1]` and `∑ P(i) = 1`;
  * the **effective graviton mass** `m_g = κ/ξ` decreases as the infrared
    correlation length `ξ` grows, so an IR lower bound on `ξ` yields an upper
    bound on `m_g` (the mechanism behind the LIGO/Virgo constraint
    `ξ > 1.07×10¹³ m`, `m_g ≤ 3.27×10⁻⁵⁶ kg`).
-/
import Mathlib

namespace RGF.Paper10

/-- Born-rule probability weight `P(i) = |c_i|²`. -/
noncomputable def bornProb {n : ℕ} (c : Fin n → ℂ) (i : Fin n) : ℝ := ‖c i‖ ^ 2

/-- The Born rule yields a genuine probability distribution when the amplitudes
are normalized: each weight lies in `[0,1]` and they sum to 1. -/
theorem bornProb_is_probability {n : ℕ} (c : Fin n → ℂ)
    (h : ∑ i, ‖c i‖ ^ 2 = 1) :
    (∀ i, 0 ≤ bornProb c i ∧ bornProb c i ≤ 1) ∧ ∑ i, bornProb c i = 1 :=
  ⟨fun i => ⟨sq_nonneg _,
      h ▸ Finset.single_le_sum (fun i _ => sq_nonneg (‖c i‖)) (Finset.mem_univ i)⟩, h⟩

/-- Effective graviton mass `m_g = κ/ξ` decreases with the IR correlation length:
if `ξ₀ ≤ ξ` (with `κ ≥ 0`, `ξ₀ > 0`) then `κ/ξ ≤ κ/ξ₀`, so an IR lower bound on
`ξ` gives an upper bound on the graviton mass. -/
theorem graviton_mass_bound (κ ξ ξ₀ : ℝ) (hκ : 0 ≤ κ) (hξ₀ : 0 < ξ₀)
    (h : ξ₀ ≤ ξ) : κ / ξ ≤ κ / ξ₀ := by
  gcongr

end RGF.Paper10
