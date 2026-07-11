/-
  FORS coarse-graining: the FORS energy density and its weak convergence

  This file specialises the general coarse-graining weak-convergence engine
  (`RGF.Analysis.coarseGraining_weak_convergence_antitone`) to the FORS energy density
  `forsDensity s = 1/(1+s⁵)`, the five-pole kernel forced by the quintic locking `k = 5`.

  Because `forsDensity` is antitone on `[0,∞)`, its coarse-grained lattice average over
  `[0,a]` converges to the continuous FORS energy integral `∫₀ᵃ 1/(1+s⁵) ds`.

  Dependencies: `Analysis/CoarseGraining.lean`.
-/

import Mathlib
import RGF.Physics.Dynamics.AnalysisCoarseGraining

open Filter Topology

namespace RGF.FORS

open RGF.Analysis

/-- FORS energy density: the five-pole kernel `1/(1+s⁵)`, antitone on `[0,∞)`. -/
noncomputable def forsDensity (s : ℝ) : ℝ := 1 / (1 + s ^ 5)

/-- The FORS density `1/(1+s⁵)` is antitone on `[0,∞)`. -/
lemma forsDensity_antitoneOn : AntitoneOn forsDensity (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  unfold forsDensity
  apply one_div_le_one_div_of_le
  · have h5 : (0:ℝ) ≤ x ^ 5 := pow_nonneg hx 5
    linarith
  · have h5 : x ^ 5 ≤ y ^ 5 := by gcongr
    linarith

/-- The coarse-grained average of the FORS energy density converges to the continuous
    FORS energy integral. -/
theorem forsDensity_coarseGraining {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => coarseAvg forsDensity a n) atTop (𝓝 (contInt forsDensity a)) :=
  coarseGraining_weak_convergence_antitone ha forsDensity_antitoneOn

end RGF.FORS
