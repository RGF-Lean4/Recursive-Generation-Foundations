/-
# L2L3.Main — aggregation entry point

This module collects the internalization results for the three remaining L2/L3 gaps:
* `RGF.L2L3.AnalyticInputs` — the two analytic inputs (Doeblin ergodicity and the
  Hadamard–Perron central manifold) are downgraded from exogenous assumptions to
  machine-checkable consequences of kernel positivity / contraction rate (spectral gap);
* `RGF.L2L3.G1Exclusivity` — the G1-exclusivity derivation and the internal chain
  "number of effective forward directions = 2d − 1", together with the bridge to the
  mode-locking order `k` (`k = 5` ⇒ `d = 3`);
* `RGF.L2L3.ComplexNecessity` — the contrapositive argument for the necessity of a
  complex base field.
-/

import RGF.Math.Analysis.AnalyticInputs
import RGF.Generative.Uniqueness.G1Exclusivity
import RGF.Generative.Uniqueness.ComplexNecessity

namespace RGF.L2L3

/-- Aggregated statement of the three internalization results. -/
theorem l2l3_internalized_summary :
    -- (1) Doeblin ergodicity ⇐ kernel positivity: a strictly positive kernel ⇒ Doeblin
    (∀ {n : ℕ}, 0 < n → ∀ (S : AnalyticInputs.Stochastic n),
      (∀ i j, 0 < S.P i j) → ∃ (ε : ℝ) (q : Fin n → ℝ), AnalyticInputs.Doeblin S ε q) ∧
    -- (1') central manifold ⇐ contraction rate: |λ| < 1 ⇒ a unique fixed point exists
    (∀ {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
      (lam : ℝ), |lam| < 1 → ∀ (φ : Equiv.Perm X) (g : X → ℝ),
        ∃! h : X → ℝ, AnalyticInputs.graphTransform lam φ g h = h) ∧
    -- (2) G1 exclusivity ⇒ number of effective forward directions = 2d − 1, and k = 5 ⇒ d = 3
    (∀ {d : ℕ} (s : Fin d × Bool),
      (G1Exclusivity.excludedByG1 s).card = 1 ∧
      (G1Exclusivity.allowedForward s).card = 2 * d - 1 ∧
      ((G1Exclusivity.allowedForward s).card = 5 → d = 3)) ∧
    -- (3) necessity of a complex base field
    ((∀ x : ℝ, x ^ 5 = 1 → x = 1) ∧
      ∃ ω : ℂ, ω ^ 5 = 1 ∧ ω.im ≠ 0 ∧
        ω ^ 4 = (starRingEnd ℂ) ω ∧ (starRingEnd ℂ) ω ≠ ω) := by
  refine ⟨fun hn S hpos => AnalyticInputs.posKernel_doeblin hn S hpos,
    fun lam hlam φ g => AnalyticInputs.center_manifold_exists_unique lam hlam φ g,
    fun s => G1Exclusivity.g1_dimension_master s, ?_⟩
  exact ⟨ComplexNecessity.real_fifth_root_unique,
    ComplexNecessity.omega, ComplexNecessity.omega_pow_five, ComplexNecessity.omega_not_real,
    ComplexNecessity.omega_conj_pair_distinct.1, ComplexNecessity.omega_conj_pair_distinct.2⟩

end RGF.L2L3
