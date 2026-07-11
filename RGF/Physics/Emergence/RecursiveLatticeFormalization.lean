import Mathlib
import RGF.Physics.Emergence.FORSEnergyFirstPrinciples

/-!
# Formalizable cores of the recursive-lattice framework

This file extracts the **rigorously formalizable mathematical cores** of the project's
first-principles recursive-lattice development and machine-checks them, integrating them into the
overall framework. Four themes (each a recurring, rigorously statable algebraic/analytic fact):

1. **Residue structure of the five poles of the FORS kernel.**
   On top of the existing `FORSEnergyFirstPrinciples.forsPole` (satisfying `w_j^5 = -1`), the
   residue computation is completed:
   - `fors_residue_w`: the residue of `1/(1+w⁵)` at the simple pole `w_j` is
     `1/(5 w_j⁴) = -w_j/5`;
   - `fors_pole_sum`: the sum of the five poles `∑ w_j = 0` (i.e. `w⁵+1` has no `w⁴` term, by
     Vieta);
   - `kPole`, `kPole_abs`: the physical momentum poles `k_j = Λ·w_j²` lie on the circle of
     radius `|Λ|`;
   - `fors_kResidue`: the physical residue `1/(10Λ w_j⁵) = -1/(10Λ)`;
   - `fors_kResidue_sum`: the sum of the residues `∑ = -1/(2Λ)`;
   - `fors_kResidue_abs`: equal moduli `‖Res‖ = 1/(10Λ)`.

2. **Selection law for the dimension and pole count.**
   - `dim_three_iff`: the intersection of constraints `{d≤3}∩{d odd}∩{d≥2}` uniquely selects
     `d=3`;
   - `poleCount`, `poleCount_three_one`: pole count `N = d + 2R`, `(d,R)=(3,1) ⟹ N=5`;
   - `coordination_three`: `d=3` feedback-locks the coordination number `Z = 2d = 6`.

3. **Diffusion coefficient and long-wave expansion.**
   - `diffusionCoeff`: `D = p/(2d)`;
   - `one_sub_cos_div_sq_limit`: `(1-cos k)/k² → 1/2`, so the leading coefficient of
     `(p/2d)·2∑(1-cos kμ)` is `α = p/(2d)`.

4. **L² isometry of the structural pullback operator.**
   - `pullback_L2_isometry`: the pullback `Tf = f∘R` induced by a measure-preserving map `R`
     preserves the `L²` energy `∫ (f∘R)² dμ = ∫ f² dμ` (the measure-theoretic cornerstone of
     the pullback invariance of the Cheeger energy).

All proofs depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PaperFormalization

open scoped BigOperators
open Filter Topology FORSEnergyFirstPrinciples

/-! ## 1 · Residue structure of the five poles of the FORS kernel -/

/-- `w_j ≠ 0` (since `|w_j| = 1`). -/
theorem forsPole_ne_zero (j : Fin 5) : forsPole j ≠ 0 := by
  intro h
  have := fors_pole_abs j
  rw [h] at this
  simp at this

/-- Core of the simple-pole residue formula: the residue of `1/(1+w⁵)` at `w_j` is
    `= 1/(5 w_j⁴) = -w_j/5`. -/
theorem fors_residue_w (j : Fin 5) :
    1 / (5 * (forsPole j) ^ 4) = - forsPole j / 5 := by
  have h5 := fors_pole j
  have hne := forsPole_ne_zero j
  field_simp [hne];
  linear_combination' h5

/-- The sum of the five poles is zero (the `w⁴` coefficient of `w⁵+1` is 0, by Vieta). -/
theorem fors_pole_sum : ∑ j : Fin 5, forsPole j = 0 := by
  -- The sum of the roots of unity $\zeta^j$ for $j = 0, 1, 2, 3, 4$ is zero because it is a complete cycle of the roots of unity.
  have h_sum_cycle : ∑ j ∈ Finset.range 5, Complex.exp (2 * Real.pi * Complex.I * j / 5) = 0 := by
    have h_geom_sum : ∑ j ∈ Finset.range 5, (Complex.exp (2 * Real.pi * Complex.I / 5)) ^ j = 0 := by
      rw [ geom_sum_eq ] <;> norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀ ];
      exact ne_of_apply_ne Complex.im ( by norm_num [ Complex.exp_im ] ; exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith [ Real.pi_pos ] ) ) );
    exact Eq.trans ( Finset.sum_congr rfl fun _ _ => by rw [ ← Complex.exp_nat_mul ] ; ring ) h_geom_sum;
  norm_num [ Finset.sum_range, forsPole ] at *;
  convert congr_arg ( fun x : ℂ => x * Complex.exp ( Complex.I * Real.pi / 5 ) ) h_sum_cycle using 1 <;> norm_num [ Finset.sum_mul _ _ _, ← Complex.exp_add ] ; ring;
  exact Finset.sum_congr rfl fun _ _ => by ring;

/-- The physical momentum pole `k_j = Λ · w_j²` (the algebraic realization of
    `k_j = Λ e^{i2π j/5}`). -/
noncomputable def kPole (Λ : ℂ) (j : Fin 5) : ℂ := Λ * (forsPole j) ^ 2

/-- The physical poles lie on the circle of radius `‖Λ‖`. -/
theorem kPole_abs (Λ : ℂ) (j : Fin 5) : ‖kPole Λ j‖ = ‖Λ‖ := by
  unfold kPole; norm_num [ forsPole_ne_zero, fors_pole_abs ] ;

/-- The physical residue value: `1/(10 Λ w_j⁵) = -1/(10 Λ)`. -/
theorem fors_kResidue (Λ : ℂ) (_hΛ : Λ ≠ 0) (j : Fin 5) :
    1 / (10 * Λ * (forsPole j) ^ 5) = -1 / (10 * Λ) := by
  rw [fors_pole j]; ring

/-- The sum of the five physical residues `= -1/(2Λ)`. -/
theorem fors_kResidue_sum (Λ : ℂ) (_hΛ : Λ ≠ 0) :
    ∑ _j : Fin 5, (-1 / (10 * Λ)) = -1 / (2 * Λ) := by
  norm_num [ div_eq_mul_inv ];
  ring

/-- Equal moduli of the residues: every physical residue has modulus `1/(10Λ)`. -/
theorem fors_kResidue_abs (Λ : ℝ) (hΛ : 0 < Λ) :
    ‖(-1 / (10 * (Λ : ℂ)))‖ = 1 / (10 * Λ) := by
  norm_num [ abs_of_pos, hΛ ]

/-! ## 2 · Selection law for the dimension and pole count -/

/-- The intersection of three constraints uniquely selects `d=3`: `{d≤3} ∩ {d odd} ∩ {d≥2}`. -/
theorem dim_three_iff (d : ℕ) : (2 ≤ d ∧ d ≤ 3 ∧ Odd d) ↔ d = 3 := by
  exact ⟨ fun h => by rcases h with ⟨ h₁, h₂, h₃ ⟩ ; interval_cases d <;> trivial, fun h => by subst h ; trivial ⟩

/-- The pole count of the FORS kernel `N = d + 2R`. -/
def poleCount (d R : ℕ) : ℕ := d + 2 * R

/-- For `(d,R) = (3,1)` the pole count is `N = 5`, consistent with `2d-1 = 5`. -/
theorem poleCount_three_one : poleCount 3 1 = 5 ∧ forsDegree 3 = 5 := by
  exact ⟨ rfl, rfl ⟩

/-- `d=3` feedback-locks the coordination number `Z = 2d = 6` of the 3D regular lattice. -/
theorem coordination_three : 2 * 3 = 6 := by norm_num

/-! ## 3 · Diffusion coefficient and long-wave expansion -/

/-- The coarse-grained diffusion coefficient `D = p/(2d)`. -/
noncomputable def diffusionCoeff (p : ℝ) (d : ℕ) : ℝ := p / (2 * d)

/-- The long-wave limit `(1 - cos k)/k² → 1/2`, so the leading-order coefficient of the lattice
    diffusion operator is `α = p/(2d)`. -/
theorem one_sub_cos_div_sq_limit :
    Tendsto (fun k : ℝ => (1 - Real.cos k) / k ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
  -- Use the fact that $1 - \cos k = 2 \sin^2 (k/2)$ and $\sin (k/2) \sim k/2$ as $k \to 0$.
  have h_sin : Filter.Tendsto (fun k => 2 * (Real.sin (k / 2)) ^ 2 / k ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
    -- Use the fact that $\sin(k/2) / k \to 1/2$ as $k \to 0$.
    have h_sin_k2 : Filter.Tendsto (fun k => Real.sin (k / 2) / k) (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
      simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero ( HasDerivAt.sin ( hasDerivAt_id 0 |> HasDerivAt.div_const <| 2 ) );
    convert h_sin_k2.pow 2 |> Filter.Tendsto.const_mul 2 using 2 <;> ring;
  exact h_sin.congr fun x => by rw [ Real.sin_sq, Real.cos_sq ] ; ring;

/-! ## 4 · L² isometry of the structural pullback operator -/

/-- `L²` isometry of the structural pullback operator `Tf = f∘R`: a measure-preserving map
    preserves the `L²` energy `∫ (f∘R)² dμ = ∫ f² dμ`. This is the measure-theoretic core of the
    pullback invariance of the Cheeger energy. -/
theorem pullback_L2_isometry {S : Type*} [MeasurableSpace S]
    {μ : MeasureTheory.Measure S} {R : S → S}
    (hR : MeasureTheory.MeasurePreserving R μ μ) (f : S → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable (fun x => (f x) ^ 2) μ) :
    ∫ x, (f (R x)) ^ 2 ∂μ = ∫ x, (f x) ^ 2 ∂μ := by
  convert MeasureTheory.integral_map ( f := fun x => f x ^ 2 ) _ _ using 1;
  · rw [ MeasureTheory.integral_map ];
    · have h_int_eq : ∫ x, (f (R x)) ^ 2 ∂μ = ∫ x, (f x) ^ 2 ∂(MeasureTheory.Measure.map R μ) := by
        rw [ MeasureTheory.integral_map ];
        · exact hR.measurable.aemeasurable;
        · rw [ hR.map_eq ] ; exact hf;
      rw [ h_int_eq, hR.map_eq ];
    · exact measurable_id.aemeasurable;
    · aesop;
  · exact measurable_id.aemeasurable;
  · aesop

end PaperFormalization