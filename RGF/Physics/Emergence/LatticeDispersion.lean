/-
  FORS lattice-to-continuum dispersion convergence

  The finite-difference (lattice) dispersion `(2 − 2cos(h·k))/h²` converges, as the
  lattice spacing `h → 0`, to the continuum dispersion `k²`. This is the analytic step
  linking the discrete lattice model to the FORS continuum field theory.
-/

import Mathlib

open Filter Topology

namespace RGF.FORS

/-- Lattice (finite-difference) dispersion converges to the continuum dispersion:
    `(2 − 2cos(h·k))/h² → k²` as `h → 0`. -/
theorem latticeDispersion_tendsto (k : ℝ) :
    Tendsto (fun h => (2 - 2 * Real.cos (h * k)) / (h ^ 2)) (𝓝[≠] 0) (𝓝 (k ^ 2)) := by
  -- Use the fact that $2 - 2 \cos(hk) = 4 \sin^2(hk/2)$ and $\sin(hk/2) \sim hk/2$ as $h \to 0$.
  have h_sin : Filter.Tendsto (fun h => 4 * (Real.sin (h * k / 2))^2 / h^2) (nhdsWithin 0 {0}ᶜ) (nhds (k^2)) := by
    -- Use the fact that $\sin(hk/2) \sim hk/2$ as $h \to 0$.
    have h_sin_approx : Filter.Tendsto (fun h => Real.sin (h * k / 2) / h) (𝓝[≠] 0) (𝓝 (k / 2)) := by
      simpa [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm ] using HasDerivAt.tendsto_slope_zero ( HasDerivAt.sin ( HasDerivAt.div_const ( HasDerivAt.mul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ k ) ) 2 ) );
    convert h_sin_approx.pow 2 |> Filter.Tendsto.const_mul 4 using 2 <;> ring;
  exact h_sin.congr fun x => by rw [ Real.sin_sq, Real.cos_sq ] ; ring;

end RGF.FORS
