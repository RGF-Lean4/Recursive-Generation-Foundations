/-
  RGF/PlanckPhenomenology.lean

  Direction I(b) — Planck-scale phenomenology of discrete gravity.

  Building on `ReggeCalculus.lean` (a simplicial discretisation of gravity),
  this file formalises the leading observable imprints of a *non-continuous*
  space-time grid at the Planck length `ℓ`:

  * **Modified graviton dispersion.**  On a discrete lattice the graviton
    dispersion acquires a cubic Planck correction
      `ω(k) = c·k − (c·ℓ²/2)·k³`
    (`dispersion`).  Its exact derivative is the energy-dependent group velocity
    `v_g(k) = c − (3c ℓ²/2) k²` (`dispersion_hasDerivAt`), which equals `c` in the
    continuum limit `k → 0` (`groupVelocity_at_zero`) and is strictly *subluminal*
    for any nonzero momentum (`groupVelocity_lt_c`) — a falsifiable GW time-delay.

  * **GW arrival-time delay.**  Two modes of momenta `k₁ < k₂` from a source at
    distance `d` arrive with a positive relative delay
    `Δt = (3ℓ²/2c)(k₂²−k₁²)·d > 0` (`arrival_delay_pos`).

  * **Quantum-corrected black-hole entropy.**  The horizon entropy carries a
    logarithmic Planck correction `S(A) = A/4 + α·log A` (`bhEntropy`), with exact
    derivative `1/4 + α/A` (`bhEntropy_hasDerivAt`) and Bekenstein–Hawking leading
    behaviour `S(A)/A → 1/4` (`bhEntropy_leading`).
-/
import Mathlib

open Real Filter Topology

namespace RGF.Planck

noncomputable section

variable (c ℓ : ℝ)

/-! ## 1. Modified graviton dispersion relation -/

/-- Lattice-corrected dispersion `ω(k) = c·k − (c·ℓ²/2)·k³`. -/
def dispersion (k : ℝ) : ℝ := c * k - (c * ℓ^2 / 2) * k^3

/-
Exact derivative of the dispersion: the group velocity `c − (3c ℓ²/2) k²`.
-/
theorem dispersion_hasDerivAt (k : ℝ) :
    HasDerivAt (dispersion c ℓ) (c - (3 * c * ℓ^2 / 2) * k^2) k := by
  convert HasDerivAt.sub ( HasDerivAt.const_mul c ( hasDerivAt_id k ) ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_pow 3 k ) ) using 1 ; ring!

/-- In the continuum limit `k → 0` the group velocity is exactly the light speed. -/
theorem groupVelocity_at_zero : (c - (3 * c * ℓ^2 / 2) * (0:ℝ)^2) = c := by
  ring

/-
For any nonzero momentum and positive Planck scale the group velocity is
    strictly subluminal.
-/
theorem groupVelocity_lt_c (hc : 0 < c) (hℓ : 0 < ℓ) {k : ℝ} (hk : k ≠ 0) :
    c - (3 * c * ℓ^2 / 2) * k^2 < c := by
  nlinarith [ show 0 < 3 * c * ℓ ^ 2 / 2 * k ^ 2 by positivity ]

/-! ## 2. Gravitational-wave arrival-time delay -/

/-- The relative arrival delay between two GW modes `k₁ < k₂` over distance `d`. -/
def arrivalDelay (k₁ k₂ d : ℝ) : ℝ := (3 * ℓ^2 / (2 * c)) * (k₂^2 - k₁^2) * d

/-
The higher-momentum mode is delayed: `Δt > 0` for `0 ≤ k₁ < k₂`, `d > 0`.
-/
theorem arrival_delay_pos (hc : 0 < c) (hℓ : 0 < ℓ) {k₁ k₂ d : ℝ}
    (hk1 : 0 ≤ k₁) (hk : k₁ < k₂) (hd : 0 < d) :
    0 < arrivalDelay c ℓ k₁ k₂ d := by
  exact mul_pos ( mul_pos ( by positivity ) ( by nlinarith ) ) hd

/-! ## 3. Quantum-corrected black-hole entropy -/

/-- Horizon entropy with a logarithmic Planck correction `S(A) = A/4 + α·log A`. -/
def bhEntropy (α A : ℝ) : ℝ := A / 4 + α * Real.log A

/-
Exact derivative of the corrected entropy: `dS/dA = 1/4 + α/A`.
-/
theorem bhEntropy_hasDerivAt (α : ℝ) {A : ℝ} (hA : A ≠ 0) :
    HasDerivAt (bhEntropy α) (1/4 + α / A) A := by
  convert HasDerivAt.add ( HasDerivAt.div_const ( hasDerivAt_id A ) _ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_log hA ) ) using 1 ; ring!

/-
**Bekenstein–Hawking leading law.**  The log correction is subleading:
    `S(A)/A → 1/4` as `A → ∞`.
-/
theorem bhEntropy_leading (α : ℝ) :
    Tendsto (fun A => bhEntropy α A / A) atTop (𝓝 (1/4)) := by
  -- Rewrite the function as eventually equal to 1/4 + α*(log A/A) (for A ≠ 0) via Tendsto.congr'.
  suffices h_eventually : ∀ᶠ A in Filter.atTop, (bhEntropy α A) / A = 1 / 4 + α * (Real.log A / A) by
    -- Since $\frac{\log A}{A} \to 0$ as $A \to \infty$, we can use the fact that multiplication by a constant preserves limits.
    have h_log_div_A_zero : Filter.Tendsto (fun A => Real.log A / A) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim _{y \rightarrow 0^{+}} \frac{\ln (1 / y)}{1 / y}$.
      suffices h_change_var : Filter.Tendsto (fun y => Real.log (1 / y) * y) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
        exact h_change_var.congr ( by aesop );
      norm_num [ mul_comm ];
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    rw [ Filter.tendsto_congr' h_eventually ] ; simpa using tendsto_const_nhds.add ( h_log_div_A_zero.const_mul α ) ;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with A hA using by unfold bhEntropy; ring_nf; norm_num [ hA.ne' ] ;

end

end RGF.Planck