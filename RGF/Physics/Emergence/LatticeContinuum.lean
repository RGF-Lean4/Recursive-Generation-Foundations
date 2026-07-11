/-
  RGF/Physics/Emergence/LatticeContinuum.lean   (module `RGF.Physics.Emergence.LatticeContinuum`)

  **Direction 4.2 — math-layer kernel of the lattice → continuum field-equation
  limit.**

  The full programme of direction 4.2 (deriving the continuum spacetime metric /
  gauge field equations as the scaling limit of the discrete RGF lattice dynamics,
  via regularity structures and relative entropy) is a large research effort that
  requires stochastic-PDE infrastructure absent from Mathlib.  What *is* clean,
  faithful, and provable is the **kernel** of any such limit: the discrete
  difference operators on a lattice of spacing `h` converge, as `h → 0`, to the
  continuum differential operators.

  This file proves that kernel:

    * `centralDiff_tendsto_deriv`  — the discrete (central) gradient
      `(f(x+h) − f(x−h)) / (2h)` converges to the continuum derivative `f'(x)`;
    * `forwardDiff_tendsto_deriv`  — the forward difference `(f(x+h) − f(x))/h`
      converges to `f'(x)`;
    * `discreteLaplacian_tendsto`  — the discrete Laplacian
      `(f(x+h) − 2 f(x) + f(x−h)) / h²` converges to the continuum second
      derivative `f''(x)` (the kernel of a lattice wave/field equation).

  Together these say: the lattice field equations (built from difference operators)
  converge coefficient-by-coefficient to the continuum field equations (built from
  derivatives), which is the rigorous mathematical core of the "lattice to continuum field equation"
  claim.  The remaining (probabilistic scaling-limit) content is documented as
  out-of-scope research engineering.
-/
import Mathlib

open Filter Topology

namespace RGF
namespace Physics
namespace LatticeContinuum

/-
**Forward difference → derivative.**  For a function differentiable at `x`, the
lattice forward difference `(f(x+h) − f(x)) / h` converges to `f'(x)` as the lattice
spacing `h → 0`.
-/
theorem forwardDiff_tendsto_deriv (f : ℝ → ℝ) (x L : ℝ) (hf : HasDerivAt f L x) :
    Tendsto (fun h : ℝ => (f (x + h) - f x) / h) (𝓝[≠] 0) (𝓝 L) := by
  simpa [ div_eq_inv_mul ] using hf.tendsto_slope_zero

/-
**Central difference → derivative.**  For a function differentiable at `x`, the
lattice central gradient `(f(x+h) − f(x−h)) / (2h)` converges to `f'(x)`.
-/
theorem centralDiff_tendsto_deriv (f : ℝ → ℝ) (x L : ℝ) (hf : HasDerivAt f L x) :
    Tendsto (fun h : ℝ => (f (x + h) - f (x - h)) / (2 * h)) (𝓝[≠] 0) (𝓝 L) := by
  convert Tendsto.div_const ( Filter.Tendsto.add ( show Filter.Tendsto ( fun h => ( f ( x + h ) - f x ) / h ) ( 𝓝[≠] 0 ) ( 𝓝 L ) from ?_ ) ( show Filter.Tendsto ( fun h => ( f x - f ( x - h ) ) / h ) ( 𝓝[≠] 0 ) ( 𝓝 L ) from ?_ ) ) 2 using 2;
  · ring;
  · ring;
  · simpa [ div_eq_inv_mul ] using hf.tendsto_slope_zero;
  · rw [ hasDerivAt_iff_tendsto_slope_zero ] at hf;
    convert hf.comp ( show Filter.Tendsto ( fun h : ℝ => -h ) ( 𝓝[≠] 0 ) ( 𝓝[≠] 0 ) from Filter.Tendsto.inf ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) <| by aesop ) using 2 ; norm_num ; ring

/-
**Discrete Laplacian → second derivative.**  If `f` is differentiable in a
neighbourhood of `x` with derivative function `f'`, and `f'` is differentiable at
`x` with derivative `L` (so `L = f''(x)`), then the discrete Laplacian
`(f(x+h) − 2 f(x) + f(x−h)) / h²` converges to `L` as `h → 0`.  This is the kernel
of the lattice → continuum limit of a field/wave equation.
-/
set_option maxHeartbeats 1000000 in
theorem discreteLaplacian_tendsto (f f' : ℝ → ℝ) (x L : ℝ)
    (hf : ∀ᶠ y in 𝓝 x, HasDerivAt f (f' y) y) (hf' : HasDerivAt f' L x) :
    Tendsto (fun h : ℝ => (f (x + h) - 2 * f x + f (x - h)) / h ^ 2) (𝓝[≠] 0) (𝓝 L) := by
  revert hf' hf;
  intro h₀ h₁
  have h₂ : Filter.Tendsto (fun h => (f (x + h) - f x - h * f' x - (h ^ 2 / 2) * L) / h ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    obtain ⟨ ε, hε, H ⟩ := Metric.mem_nhds_iff.mp h₀;
    -- Apply the mean value theorem to the interval $[x, x+h]$.
    have h_mvt : ∀ h ∈ Set.Ioo (-ε) ε \ {0}, ∃ c ∈ Set.Ioo (min x (x + h)) (max x (x + h)), (f (x + h) - f x - h * f' x - (h ^ 2 / 2) * L) = (f' c - f' x - (c - x) * L) * h := by
      intro h hh
      have h_mvt : ∃ c ∈ Set.Ioo (min x (x + h)) (max x (x + h)), deriv (fun t => f t - f x - (t - x) * f' x - ((t - x) ^ 2 / 2) * L) c = (f (x + h) - f x - h * f' x - (h ^ 2 / 2) * L) / h := by
        cases max_cases x ( x + h ) <;> cases min_cases x ( x + h ) <;> simp_all +decide;
        · have := exists_deriv_eq_slope ( f := fun t => f t - f x - ( t - x ) * f' x - ( t - x ) ^ 2 / 2 * L ) ( show x + h < x from by linarith );
          convert this _ _ using 3 <;> norm_num;
          · rw [ ← neg_div_neg_eq ] ; ring;
          · exact continuousOn_of_forall_continuousAt fun t ht => by exact ContinuousAt.sub ( ContinuousAt.sub ( ContinuousAt.sub ( HasDerivAt.continuousAt ( H <| Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩ ) ) ( continuousAt_const ) ) ( ContinuousAt.mul ( continuousAt_id.sub continuousAt_const ) continuousAt_const ) ) ( ContinuousAt.mul ( ContinuousAt.div_const ( ContinuousAt.pow ( continuousAt_id.sub continuousAt_const ) 2 ) _ ) continuousAt_const ) ;
          · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.sub ( DifferentiableAt.sub ( H ( Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ) |> HasDerivAt.differentiableAt ) ( differentiableAt_const _ ) ) ( DifferentiableAt.mul ( differentiableAt_id.sub_const _ ) ( differentiableAt_const _ ) ) ) ( DifferentiableAt.mul ( DifferentiableAt.div_const ( DifferentiableAt.pow ( differentiableAt_id.sub_const _ ) 2 ) _ ) ( differentiableAt_const _ ) ) );
        · have := exists_deriv_eq_slope ( f := fun t => f t - f x - ( t - x ) * f' x - ( t - x ) ^ 2 / 2 * L ) ( show x < x + h by linarith );
          simp +zetaDelta at *;
          refine' this _ _;
          · exact continuousOn_of_forall_continuousAt fun t ht => by exact ContinuousAt.sub ( ContinuousAt.sub ( ContinuousAt.sub ( HasDerivAt.continuousAt ( H ( Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ) ) ) ( continuousAt_const ) ) ( ContinuousAt.mul ( continuousAt_id.sub continuousAt_const ) continuousAt_const ) ) ( ContinuousAt.mul ( ContinuousAt.div_const ( ContinuousAt.pow ( continuousAt_id.sub continuousAt_const ) 2 ) _ ) continuousAt_const ) ;
          · exact fun t ht => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.sub ( DifferentiableAt.sub ( H ( Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ) |> HasDerivAt.differentiableAt ) ( differentiableAt_const _ ) ) ( DifferentiableAt.mul ( differentiableAt_id.sub_const _ ) ( differentiableAt_const _ ) ) ) ( DifferentiableAt.mul ( DifferentiableAt.div_const ( DifferentiableAt.pow ( differentiableAt_id.sub_const _ ) 2 ) _ ) ( differentiableAt_const _ ) ) );
      obtain ⟨ c, hc₁, hc₂ ⟩ := h_mvt; use c; simp_all +decide [ sub_eq_iff_eq_add ] ;
      norm_num [ H ( show c ∈ Metric.ball x ε from by cases hc₁.1 <;> cases hc₁.2 <;> exact Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) |> HasDerivAt.differentiableAt ] at hc₂;
      rw [ eq_div_iff hh.2 ] at hc₂ ; rw [ H ( show c ∈ Metric.ball x ε from by cases hc₁.1 <;> cases hc₁.2 <;> exact Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) |> HasDerivAt.deriv ] at hc₂ ; linarith;
    -- Use the fact that $f'$ is differentiable at $x$ with derivative $L$ to bound the term $(f' c - f' x - (c - x) * L)$.
    have h_bound : ∀ ε' > 0, ∃ δ > 0, ∀ c, abs (c - x) < δ → abs (f' c - f' x - (c - x) * L) ≤ ε' * abs (c - x) := by
      intro ε' hε';
      have := Metric.tendsto_nhds_nhds.mp h₁.isLittleO.tendsto_div_nhds_zero ε' hε';
      simp_all +decide;
      obtain ⟨ δ, hδ, H ⟩ := this; exact ⟨ δ, hδ, fun c hc => if h : c = x then by simp +decide [ h ] else by have := H hc; rw [ div_lt_iff₀ ( abs_pos.mpr ( sub_ne_zero.mpr h ) ) ] at this; linarith ⟩ ;
    -- Use the bound to show that the term $(f' c - f' x - (c - x) * L)$ is small compared to $h^2$.
    have h_small : ∀ ε' > 0, ∃ δ > 0, ∀ h ∈ Set.Ioo (-ε) ε \ {0}, abs h < δ → abs ((f (x + h) - f x - h * f' x - (h ^ 2 / 2) * L) / h ^ 2) ≤ ε' := by
      intro ε' hε'; obtain ⟨ δ, hδ, H ⟩ := h_bound ε' hε'; use δ, hδ; intro h hh hh'; rcases h_mvt h hh with ⟨ c, hc₁, hc₂ ⟩ ; simp_all +decide [ abs_div, abs_mul ] ;
      rw [ div_le_iff₀ ] <;> cases abs_cases h <;> cases abs_cases ( c - x ) <;> cases hc₁.1 <;> cases hc₁.2 <;> first | linarith | simp_all +decide [ sq ];
      · exact le_trans ( mul_le_mul_of_nonneg_right ( H c ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ) ( abs_nonneg _ ) ) ( by rw [ abs_of_nonneg ( by linarith : 0 ≤ h ) ] ; rw [ abs_of_nonneg ( by linarith : 0 ≤ c - x ) ] ; nlinarith [ mul_le_mul_of_nonneg_left ( by linarith : c - x ≤ h ) hε'.le ] );
      · exact le_trans ( mul_le_mul_of_nonneg_right ( H c ( by rw [ abs_of_nonpos ] <;> linarith ) ) ( abs_nonneg _ ) ) ( by rw [ abs_of_nonpos ( by linarith : h ≤ 0 ) ] ; nlinarith [ mul_le_mul_of_nonneg_left ( show |c - x| ≤ -h by cases abs_cases ( c - x ) <;> linarith ) hε'.le ] );
    rw [ Metric.tendsto_nhdsWithin_nhds ];
    intro ε' hε'; rcases h_small ( ε' / 2 ) ( half_pos hε' ) with ⟨ δ, hδ, H ⟩ ; exact ⟨ Min.min δ ε, lt_min hδ hε, fun { h } hh₁ hh₂ => by simpa [ abs_div, abs_mul, abs_pow ] using lt_of_le_of_lt ( H h ⟨ ⟨ by linarith [ abs_lt.mp hh₂, min_le_left δ ε, min_le_right δ ε ], by linarith [ abs_lt.mp hh₂, min_le_left δ ε, min_le_right δ ε ] ⟩, hh₁ ⟩ ( by simpa using lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ) ) ( by linarith ) ⟩ ;
  have h₃ : Filter.Tendsto (fun h => (f (x - h) - f x + h * f' x - (h ^ 2 / 2) * L) / h ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    convert h₂.comp ( show Filter.Tendsto ( fun h : ℝ => -h ) ( 𝓝[≠] 0 ) ( 𝓝[≠] 0 ) by exact Filter.Tendsto.inf ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) <| by norm_num ) using 2 ; norm_num ; ring;
  convert h₂.add h₃ |> Filter.Tendsto.add_const L |> Filter.Tendsto.congr' _ using 2;
  · ring;
  · filter_upwards [ self_mem_nhdsWithin ] with h hh using by rw [ ← add_div, div_add', div_eq_div_iff ] <;> ring <;> aesop;

end LatticeContinuum
end Physics
end RGF