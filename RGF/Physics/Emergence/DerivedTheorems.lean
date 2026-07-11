/-
  RequestProject/DerivedTheorems.lean

  New theorems derived from two previously absorbed developments:

    * `RequestProject.ExclusionProcess.KPZ` (namespace `KPZFromExclusion`):
      the rigorous hydrodynamic KPZ scaling limit and the macroscopic flux
      `current ρ = ρ(1-ρ)`.
    * `RequestProject.SpectrumReductionConjecture` (namespace
      `SpectrumReductionConjecture`): the spectral-gap reduction
      `G2 ∧ G3 ⇒ spectral_gap_positive`.

  The goal of this file is *not* to restate the two inputs but to derive genuinely
  new consequences of them.

  ## New flux theorems (KPZ side)

  * `current_symm`        : particle–hole symmetry `j(ρ) = j(1-ρ)`.
  * `current_le_quarter`  : the maximal-current bound `j(ρ) ≤ 1/4`.
  * `current_half`        : `j(1/2) = 1/4`, the maximal value.
  * `current_eq_quarter_iff` : `j(ρ) = 1/4 ↔ ρ = 1/2` (unique maximizer).
  * `exclusion_height_scaling_limit_max_current` : at the maximal-current density
    `ρ = 1/2`, the rescaled height field converges almost surely to the maximal
    macroscopic flux `1/4`, which dominates the flux of every other density.

  ## New spectral theorems (spectrum side)

  * `g2_g3_unique_equilibrium` : under the dynamical axioms, the only (real) fixed
    point of `A` is `0` — the equilibrium is unique.
  * `g2_g3_one_not_eigenvalue` : under the dynamical axioms, `1` is not an
    eigenvalue of the complexified operator, hence `(I - A)` is "spectrally
    nonsingular".
-/

import Mathlib
import RGF.Physics.Dynamics.KPZ
import RGF.Math.Spectral.SpectrumReductionConjecture

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix

/-! ## New flux theorems (KPZ side) -/

namespace KPZFromExclusion

/-
Particle–hole symmetry of the macroscopic flux: `j(ρ) = j(1-ρ)`.
-/
theorem current_symm (ρ : ℝ) : current ρ = current (1 - ρ) := by
  unfold current; ring;

/-
Maximal-current bound: the macroscopic flux never exceeds `1/4`.
-/
theorem current_le_quarter (ρ : ℝ) : current ρ ≤ 1 / 4 := by
  unfold current; linarith [ sq_nonneg ( ρ - 1 / 2 ) ] ;

/-
The flux attains the value `1/4` at the symmetric density `ρ = 1/2`.
-/
theorem current_half : current (1 / 2) = 1 / 4 := by
  unfold current; norm_num;

/-
`ρ = 1/2` is the unique maximizer of the flux: `j(ρ) = 1/4 ↔ ρ = 1/2`.
-/
theorem current_eq_quarter_iff (ρ : ℝ) : current ρ = 1 / 4 ↔ ρ = 1 / 2 := by
  constructor <;> intro h <;> unfold current at * <;> nlinarith [ sq_nonneg ( ρ - 1 / 2 ) ]

/-
**New corollary (maximal-current scaling limit).**

At the maximal-current density `ρ = 1/2` there is a genuine i.i.d. increment
sequence with law `bernoulliReal (1/4)` whose rescaled height field converges
almost surely to the macroscopic flux `1/4`; moreover this value is the maximal
possible macroscopic flux, dominating `current ρ` for every density `ρ`.
-/
theorem exclusion_height_scaling_limit_max_current :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧
      (∀ i, Measurable (X i)) ∧
      (∀ i, HasLaw (X i) (bernoulliReal (1 / 4)) P) ∧
      iIndepFun X P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => height X n ω / n) atTop (𝓝 (1 / 4))) ∧
      (∀ ρ : ℝ, current ρ ≤ 1 / 4) := by
        obtain ⟨ Ω, mΩ, P, X, hP, hX, hX', hX'', hX''' ⟩ := exclusion_height_scaling_limit ( show 0 ≤ 1 / 2 by norm_num ) ( show 1 / 2 ≤ 1 by norm_num ) ; use Ω, mΩ, P, X; norm_num at *;
        exact ⟨ hP, hX, by simpa only [ current_half ] using hX', hX'', by simpa only [ current_half ] using hX''', current_le_quarter ⟩

end KPZFromExclusion

/-! ## New spectral theorems (spectrum side) -/

namespace SpectrumReductionConjecture

variable {n : ℕ}

/-
**New corollary (uniqueness of equilibrium).**

Under the dynamical axioms G2 ∧ G3, the only real fixed point of `A` is `0`:
if `A.mulVec x = x` then `x = 0`.
-/
theorem g2_g3_unique_equilibrium (A : Matrix (Fin n) (Fin n) ℝ)
    (hax : RGFDynamicalAxioms A) (x : Fin n → ℝ) (hx : A.mulVec x = x) :
    x = 0 := by
      have h_induction : ∀ m : ℕ, (A ^ m).mulVec x = x := by
        intro m; induction m <;> simp_all +decide [ pow_succ' ] ;
        simp_all +decide [ ← Matrix.mulVec_mulVec ];
      exact tendsto_nhds_unique ( tendsto_const_nhds.congr fun m => by aesop ) ( hax.g3_holds x )

/-
**New corollary (`1` is not an eigenvalue).**

Under the dynamical axioms G2 ∧ G3, the complexified operator does not have `1`
as an eigenvalue, since every eigenvalue has norm `< 1`.
-/
theorem g2_g3_one_not_eigenvalue (A : Matrix (Fin n) (Fin n) ℝ)
    (hax : RGFDynamicalAxioms A) :
    (1 : ℂ) ∉ eigenvalues (A.map (algebraMap ℝ ℂ)) := by
      convert g2_g3_imply_spectral_gap A hax 1 using 1 ; norm_num [ eigenvalues ]

end SpectrumReductionConjecture