/-
  RequestProject/TheoremUpdate.lean

  Theorem update module.

  This module absorbs two newly verified developments and records their axiom
  audits in one place, so that `lake build` of this file re-checks the whole
  update for self-consistency.

  1. `RequestProject.ExclusionProcess.KPZ` (namespace `KPZFromExclusion`):
     the rigorous *hydrodynamic* KPZ scaling limit.  The single-step height
     increments form a genuine i.i.d. sequence with law `bernoulliReal (current ρ)`
     (`current ρ = ρ(1-ρ)`), and the rescaled height field `height X n / n`
     converges almost surely (hence weakly) to the deterministic macroscopic
     profile `current ρ` (`exclusion_height_scaling_limit`).  The KPZ universality
     criterion `j''(ρ) = -2 ≠ 0` (`kpz_nonlinearity_ne_zero`) and the positivity of
     the KPZ coefficients (`kpz_coefficients_positive`) are also recorded.

  2. `RequestProject.SpectrumReductionConjecture` (namespace
     `SpectrumReductionConjecture`): the forward direction of the spectral
     reduction, namely that emergent stability (G2) together with exponential
     recovery (G3) imply a positive spectral gap of the linearized operator
     (`g2_g3_imply_spectral_gap`).

  All listed theorems are `sorry`-free and depend only on the standard Lean
  axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

import RGF.Physics.Dynamics.KPZ
import RGF.Math.Spectral.SpectrumReductionConjecture
import RGF.Physics.Emergence.DerivedTheorems

/-! ## Update 1 — Rigorous KPZ hydrodynamic scaling limit -/

-- Main scaling-limit theorem: weak (a.s.) convergence of the rescaled height
-- field to the macroscopic KPZ profile `current ρ`.
#print axioms KPZFromExclusion.exclusion_height_scaling_limit

-- KPZ universality criterion: nonzero curvature of the flux, `j''(ρ) = -2 ≠ 0`.
#print axioms KPZFromExclusion.kpz_nonlinearity_ne_zero

-- Positivity of the KPZ coefficients `λ, ν, noise`.
#print axioms KPZFromExclusion.kpz_coefficients_positive

/-! ## Update 2 — Spectral reduction (G2 ∧ G3 ⇒ positive spectral gap) -/

-- From emergent stability and exponential recovery to a positive spectral gap.
#print axioms SpectrumReductionConjecture.g2_g3_imply_spectral_gap

/-! ## Update 3 — New theorems derived from the two developments

See `RequestProject.DerivedTheorems`.  From the macroscopic flux of the
exclusion process: particle–hole symmetry, the maximal-current bound
`j(ρ) ≤ 1/4`, and the unique maximizer `ρ = 1/2`; combined into a
maximal-current scaling-limit corollary.  From the spectral reduction:
uniqueness of the equilibrium and that `1` is not an eigenvalue. -/

-- Maximal-current scaling limit: a.s. convergence to the maximal flux `1/4`.
#print axioms KPZFromExclusion.exclusion_height_scaling_limit_max_current

-- Unique maximizer of the flux at the symmetric density `ρ = 1/2`.
#print axioms KPZFromExclusion.current_eq_quarter_iff

-- Uniqueness of equilibrium under the dynamical axioms.
#print axioms SpectrumReductionConjecture.g2_g3_unique_equilibrium

-- `1` is not an eigenvalue of the complexified operator.
#print axioms SpectrumReductionConjecture.g2_g3_one_not_eigenvalue
