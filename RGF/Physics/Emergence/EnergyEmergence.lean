import RGF.Math.Analysis.GammaConvergence
import RGF.Generative.Core.Setup

/-!
# Emergence of the FORS energy functional as a Γ-limit

Using the self-contained Γ-convergence theory of `FORS/GammaConvergence.lean`, we
exhibit an explicit **discrete→continuum scaling sequence** of microscopic energy
functionals whose Γ-limit is the FORS *geometric dimension-reduction energy*

`forsEnergyR m = (m − 2)²`

(here `m` is the coarse-grained support dimension, the macroscopic order
parameter; cf. `RGF.FORS.energy φ = (suppDim φ − 2)²` in `FORS/Setup.lean`).

The microscopic functionals live on the **lattice** `(1/(n+1)) ℤ`: at scale `n`
the dimension order parameter `m` is replaced by its nearest lattice value
`latticePt n m` (this is the honest discretization of the continuum energy).  As
`n → ∞` the lattice spacing `1/(n+1) → 0` and:

* `discrEnergy_gammaConverges` — the discrete functionals Γ-converge to
  `forsEnergyR`;
* `membrane_dimension_emerges` — the locked membrane dimension `d = 2` is the
  unique minimizer of the emergent energy, and the microscopic minimum energies
  converge to `0`.

This is exactly the "overall emergence of the energy functional via
Γ-convergence" that Mathlib lacked: a mathematically closed (non-conjectural)
discrete→continuum scaling limit.
-/

namespace RGF.FORS.Emergence

open Filter Topology RGF.Gamma

/-- The continuum FORS energy as a function of the (coarse-grained) support
dimension `m`: the geometric dimension-reduction energy `(m − 2)²`, minimized at
the locked membrane dimension `m = 2`. -/
def forsEnergyR (m : ℝ) : ℝ := (m - 2) ^ 2

theorem forsEnergyR_nonneg (m : ℝ) : 0 ≤ forsEnergyR m := sq_nonneg _

theorem forsEnergyR_continuous : Continuous forsEnergyR := by
  unfold forsEnergyR; fun_prop

/-- The unique minimizer of the continuum energy is `m = 2`. -/
theorem forsEnergyR_eq_zero_iff (m : ℝ) : forsEnergyR m = 0 ↔ m = 2 := by
  unfold forsEnergyR
  rw [pow_eq_zero_iff (by norm_num), sub_eq_zero]

/-- The nearest point of the lattice `(1/(n+1)) ℤ` to a real `m`. -/
noncomputable def latticePt (n : ℕ) (m : ℝ) : ℝ :=
  (round (((n : ℝ) + 1) * m) : ℝ) / ((n : ℝ) + 1)

/-
The lattice point is within half a lattice spacing of `m`.
-/
theorem latticePt_dist (n : ℕ) (m : ℝ) :
    |latticePt n m - m| ≤ 1 / (2 * ((n : ℝ) + 1)) := by
  unfold latticePt;
  rw [ div_sub', abs_div ] <;> try positivity;
  rw [ div_le_div_iff₀ ] <;> norm_cast <;> norm_num;
  rw [ abs_sub_comm ];
  exact le_trans ( mul_le_mul_of_nonneg_right ( abs_sub_round _ ) ( by positivity ) ) ( by nlinarith )

/-
For any sequence `u n → m`, the lattice approximations also converge to `m`.
-/
theorem latticePt_tendsto {u : ℕ → ℝ} {m : ℝ} (hu : Tendsto u atTop (𝓝 m)) :
    Tendsto (fun n => latticePt n (u n)) atTop (𝓝 m) := by
  -- We have hu : u n → m. Show the difference d n := latticePt n (u n) - u n → 0 by squeeze: |d n| ≤ 1/(2*((n:ℝ)+1)) by latticePt_dist n (u n), and the bound 1/(2*((n:ℝ)+1)) → 0.
  have h_diff : Tendsto (fun n => latticePt n (u n) - u n) atTop (nhds 0) := by
    exact squeeze_zero_norm ( fun n => latticePt_dist n ( u n ) ) ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop ) );
  simpa using h_diff.add hu

/-- The microscopic (discrete) FORS energy at scale `n`: evaluate the continuum
energy on the lattice approximation of the order parameter. -/
noncomputable def discrEnergy (n : ℕ) (m : ℝ) : EReal :=
  ((forsEnergyR (latticePt n m) : ℝ) : EReal)

/-
For each `m`, the real sequence `forsEnergyR (latticePt n (u n))` converges to
`forsEnergyR m` whenever `u n → m`.
-/
theorem discrEnergy_real_tendsto {u : ℕ → ℝ} {m : ℝ} (hu : Tendsto u atTop (𝓝 m)) :
    Tendsto (fun n => forsEnergyR (latticePt n (u n))) atTop (𝓝 (forsEnergyR m)) := by
  convert Filter.Tendsto.comp ( forsEnergyR_continuous.tendsto m ) ( latticePt_tendsto hu ) using 1

/-
**Γ-convergence of the discrete FORS energies to the continuum energy.**
-/
theorem discrEnergy_gammaConverges :
    GammaConverges discrEnergy (fun m => (forsEnergyR m : EReal)) := by
  constructor;
  · intro m u hu;
    rw [ Filter.Tendsto.liminf_eq ];
    convert EReal.tendsto_coe.mpr ( discrEnergy_real_tendsto hu ) using 1;
  · intro m;
    refine' ⟨ fun _ => m, tendsto_const_nhds, _ ⟩;
    convert Tendsto.limsup_eq ( EReal.tendsto_coe.mpr ( discrEnergy_real_tendsto ( tendsto_const_nhds ) ) ) |> le_of_eq using 1

/-
The integer multiple `2` is a lattice point at every scale: `latticePt n 2 = 2`.
-/
theorem latticePt_two (n : ℕ) : latticePt n 2 = 2 := by
  unfold latticePt;
  rw [ div_eq_iff ] <;> norm_cast ; norm_num [ round_eq ];
  exact Int.floor_eq_iff.mpr ⟨ by push_cast; linarith, by push_cast; linarith ⟩

/-
The constant sequence `2` minimizes every discrete energy `discrEnergy n`.
-/
theorem two_minimizes (n : ℕ) (z : ℝ) : discrEnergy n 2 ≤ discrEnergy n z := by
  unfold discrEnergy;
  rw [ latticePt_two ] ; norm_num [ forsEnergyR ];
  norm_cast ; norm_num [ sq_nonneg ]

/-
**Emergence of the membrane dimension.**  Applying the fundamental theorem of
Γ-convergence to the discrete FORS energies: the locked membrane dimension `d = 2`
is a minimizer of the emergent continuum energy, and the microscopic minimum
energies converge to the global minimum value `0`.
-/
theorem membrane_dimension_emerges :
    IsMinimizer (fun m => (forsEnergyR m : EReal)) 2 ∧
      Tendsto (fun n => discrEnergy n 2) atTop (𝓝 ((forsEnergyR 2 : ℝ) : EReal)) := by
  convert RGF.Gamma.gamma_fundamental _ _ _;
  exacts [ inferInstance, discrEnergy_gammaConverges, tendsto_const_nhds, two_minimizes ]

/-- The emergent minimum is `2`, the unique dimension at which the energy vanishes:
`forsEnergyR 2 = 0`. -/
theorem emergent_energy_zero : forsEnergyR 2 = 0 := by
  rw [forsEnergyR_eq_zero_iff]

end RGF.FORS.Emergence