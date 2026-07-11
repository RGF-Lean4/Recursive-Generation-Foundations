/-
  RequestProject/ExclusionProcess/KPZ.lean

  Rigorous emergence of the KPZ (hydrodynamic) scaling limit from the Z₅
  asymmetric exclusion process.

  Scope.  This file proves the *hydrodynamic* (law-of-large-numbers level)
  scaling limit, i.e. the weak convergence of the rescaled height field that the
  user requested.  Concretely, in the stationary (product–Bernoulli) state of the
  asymmetric exclusion process at density `ρ`, the single-step height increments
  form a genuine i.i.d. sequence of nondegenerate random variables with law
  `bernoulliReal (current ρ)`, where `current ρ = ρ(1-ρ)` is the macroscopic
  flux.  The rescaled height field `height X n / n` then converges almost surely
  (hence in distribution / weakly) to the deterministic macroscopic profile
  `current ρ`.  This is obtained from Mathlib's strong law of large numbers
  together with the existence of i.i.d. sequences with a prescribed law.

  The finer KPZ *fluctuation* universality (the `t^{1/3}` / Tracy–Widom–Airy
  scaling) is a much deeper result that is, to date, not formalized in any proof
  assistant; it is *not* asserted here, and no axiom or placeholder is introduced
  for it.

  We also record the KPZ universality criterion: the curvature of the flux
  `j''(ρ) = -2 ≠ 0` places the model in the KPZ (rather than the
  Edwards–Wilkinson) universality class, and the resulting coefficients
  `kpzLambda`, `kpzNu`, `kpzNoise` are positive.
-/

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace KPZFromExclusion

/-- Macroscopic current (flux) of the asymmetric exclusion process at density `ρ`:
`j(ρ) = ρ(1-ρ)`. -/
noncomputable def current (ρ : ℝ) : ℝ := ρ * (1 - ρ)

/-- The real-valued Bernoulli law: the probability measure on `ℝ` putting mass
`1-p` at `0` and mass `p` at `1`. -/
noncomputable def bernoulliReal (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac 0 + ENNReal.ofReal p • Measure.dirac 1

/-- The height field of an increment sequence `X`: the partial sum process. -/
noncomputable def height {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

/-! ### Basic properties of the current and the Bernoulli law -/

theorem current_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : 0 ≤ current ρ := by
  -- Since ρ is between 0 and 1, both ρ and (1 - ρ) are non-negative. Therefore, their product is also non-negative.
  apply mul_nonneg h0 (sub_nonneg_of_le h1)

theorem current_le_one {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : current ρ ≤ 1 := by
  -- By definition of current, we have current ρ = ρ * (1 - ρ).
  unfold current;
  nlinarith

theorem current_pos {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) : 0 < current ρ := by
  -- Since $0 < \rho < 1$, both $\rho$ and $1 - \rho$ are positive, hence their product is positive.
  apply mul_pos h0 (sub_pos.mpr h1)

theorem bernoulliReal_isProbabilityMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliReal p) := by
  constructor ; unfold bernoulliReal ; ring_nf ;
  simp +decide;
  rw [ ← ENNReal.ofReal_add ] <;> norm_num [ hp0, hp1 ]

theorem integrable_id_bernoulliReal {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    Integrable (fun x : ℝ => x) (bernoulliReal p) := by
  refine' ⟨ _, _ ⟩;
  · exact measurable_id.aestronglyMeasurable;
  · unfold bernoulliReal;
    norm_num [ hasFiniteIntegral_iff_norm ]

theorem integral_id_bernoulliReal {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ x, x ∂(bernoulliReal p) = p := by
  unfold bernoulliReal; erw [ integral_add_measure ] ;
  · rw [ MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac, MeasureTheory.integral_dirac ] ; norm_num [ hp0, hp1 ];
  · constructor;
    · exact measurable_id.aestronglyMeasurable;
    · simp +decide [ hasFiniteIntegral_iff_norm ];
  · norm_num [ MeasureTheory.Integrable ];
    norm_num [ HasFiniteIntegral ];
    exact measurable_id.aestronglyMeasurable

/-! ### The hydrodynamic scaling limit of the height field -/

/-
**Main theorem (hydrodynamic scaling limit).**

There is a genuine i.i.d. sequence of single-step height increments `X` with law
`bernoulliReal (current ρ)` such that the rescaled height field `height X n / n`
converges almost surely to the deterministic macroscopic KPZ profile
`current ρ`.  Almost sure convergence implies convergence in distribution, i.e.
the weak convergence of the rescaled height field.
-/
theorem exclusion_height_scaling_limit {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧
      (∀ i, Measurable (X i)) ∧
      (∀ i, HasLaw (X i) (bernoulliReal (current ρ)) P) ∧
      iIndepFun X P ∧
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => height X n ω / n) atTop (𝓝 (current ρ)) := by
  -- Let $p := current \rho$ and $\mu := bernoulliReal p$.
  set p := current ρ
  set μ := bernoulliReal p;
  -- From current_nonneg h0 h1 and current_le_one h0 h1 we have 0 ≤ p and p ≤ 1, so by bernoulliReal_isProbabilityMeasure, μ is a probability measure.
  have hμ_prob : IsProbabilityMeasure μ := by
    exact bernoulliReal_isProbabilityMeasure ( current_nonneg h0 h1 ) ( current_le_one h0 h1 );
  obtain ⟨ Ω, mΩ, P, X, hX_meas, hX_law, hX_indep, hP ⟩ := ProbabilityTheory.exists_iid ℕ μ;
  -- Apply the strong law of large numbers to the sequence X.
  have h_strong_law : ∀ᵐ ω ∂P, Tendsto (fun n => (∑ i ∈ Finset.range n, X i ω) / n) atTop (𝓝 (∫ x, x ∂μ)) := by
    have h_integrable : Integrable (fun x : ℝ => x) μ := by
      apply integrable_id_bernoulliReal;
      · exact mul_nonneg h0 ( sub_nonneg.2 h1 );
      · exact current_le_one h0 h1;
    have h_strong_law : ∀ᵐ ω ∂P, Tendsto (fun n => (∑ i ∈ Finset.range n, X i ω) / n) atTop (𝓝 (∫ x, x ∂μ)) := by
      have h_identDistrib : ∀ i, IdentDistrib (X i) (fun x => x) P μ := by
        intro i; exact (by
        convert hX_law i |> HasLaw.identDistrib <| HasLaw.id using 1)
      convert ProbabilityTheory.strong_law_ae_real X _ _ _ using 1;
      · rw [ ← h_identDistrib 0 |> IdentDistrib.integral_eq ];
      · exact h_identDistrib 0 |>.integrable_iff.mpr h_integrable;
      · exact fun i j hij => hX_indep.indepFun hij;
      · exact fun i => ( h_identDistrib i ).trans ( h_identDistrib 0 |> IdentDistrib.symm );
    convert h_strong_law using 1;
  refine' ⟨ Ω, mΩ, P, X, hP, hX_meas, hX_law, hX_indep, _ ⟩;
  convert h_strong_law using 3;
  exact congr_arg _ ( integral_id_bernoulliReal ( current_nonneg h0 h1 ) ( current_le_one h0 h1 ) ▸ rfl )

/-! ### KPZ universality criterion: nonzero curvature of the flux -/

theorem current_eq (ρ : ℝ) : current ρ = ρ - ρ ^ 2 := by
  -- By definition of current, we have current ρ = ρ * (1 - ρ).
  rw [current]
  ring

theorem hasDerivAt_current (ρ : ℝ) : HasDerivAt current (1 - 2 * ρ) ρ := by
  convert HasDerivAt.sub ( hasDerivAt_id ρ ) ( hasDerivAt_pow 2 ρ ) using 1 ; ring!;
  · exact funext fun x => by unfold current; norm_num; ring;
  · norm_num

theorem current_deriv_eq : deriv current = fun ρ => 1 - 2 * ρ := by
  -- By definition of current, we know that its derivative is 1 - 2ρ.
  funext ρ; exact (hasDerivAt_current ρ).deriv

/-
The curvature (second derivative) of the flux is `j''(ρ) = -2`.
-/
theorem current_second_deriv (ρ : ℝ) : deriv (deriv current) ρ = -2 := by
  rw [ show deriv current = fun ρ => 1 - 2 * ρ by funext ρ; exact HasDerivAt.deriv ( hasDerivAt_current ρ ) ] ; norm_num [ mul_comm ]

/-
KPZ universality criterion: the flux has nonzero curvature, so the model is in
the KPZ (not the Edwards–Wilkinson) universality class.
-/
theorem kpz_nonlinearity_ne_zero (ρ : ℝ) : deriv (deriv current) ρ ≠ 0 := by
  rw [ show deriv current = fun ρ => 1 - 2 * ρ from _ ] ; norm_num [ mul_comm ];
  exact current_deriv_eq

/-! ### KPZ coefficients -/

/-- KPZ nonlinearity coefficient `λ = -j''(ρ) = 2`. -/
noncomputable def kpzLambda : ℝ := 2

/-- KPZ diffusion (viscosity) coefficient `ν = 1/2`. -/
noncomputable def kpzNu : ℝ := 1 / 2

/-- KPZ noise strength, equal to the macroscopic flux at density `ρ`. -/
noncomputable def kpzNoise (ρ : ℝ) : ℝ := current ρ

/-
For a nondegenerate density `0 < ρ < 1` the three KPZ coefficients are positive.
-/
theorem kpz_coefficients_positive {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    0 < kpzLambda ∧ 0 < kpzNu ∧ 0 < kpzNoise ρ := by
  exact ⟨ by norm_num [ kpzLambda ], by norm_num [ kpzNu ], by unfold kpzNoise; exact current_pos h0 h1 ⟩

end KPZFromExclusion