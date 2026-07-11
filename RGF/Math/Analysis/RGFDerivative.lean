/-
  RGF generative analysis system (III) — theory of derivatives
  Within the dual-layer iteration axiom framework, the derivative is defined via limits and the differentiation rules are proved.
-/

import Mathlib

open Set Filter

namespace RGF.Analysis

/-! ## The ε-δ definition of the derivative -/

/-- The function f is differentiable at the point a, with derivative L. -/
def HasDerivAt' (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| → |x - a| < δ →
    |((f x - f a) / (x - a)) - L| < ε

/-! ## Uniqueness of the derivative -/

/-
If differentiable, the derivative is unique
-/
theorem deriv_unique {f : ℝ → ℝ} {a L₁ L₂ : ℝ}
    (h₁ : HasDerivAt' f a L₁) (h₂ : HasDerivAt' f a L₂) : L₁ = L₂ := by
  by_contra! H; ( have := h₁ ( |L₁ - L₂|/2 ) ( half_pos ( abs_pos.mpr ( sub_ne_zero_of_ne H ) ) ) );
  rcases h₂ ( |L₁ - L₂|/2 ) ( half_pos ( abs_pos.mpr ( sub_ne_zero.mpr H ) ) ) with ⟨ δ', δ'_pos, H' ⟩ ; rcases this with ⟨ δ, δ_pos, H ⟩ ; have := H ( a + Min.min δ δ' / 2 ) ( by rw [ abs_of_pos ] <;> linarith [ lt_min δ_pos δ'_pos ] ) ( by rw [ abs_of_pos ] <;> linarith [ lt_min δ_pos δ'_pos, min_le_left δ δ', min_le_right δ δ' ] ) ; have := H' ( a + Min.min δ δ' / 2 ) ( by rw [ abs_of_pos ] <;> linarith [ lt_min δ_pos δ'_pos ] ) ( by rw [ abs_of_pos ] <;> linarith [ lt_min δ_pos δ'_pos, min_le_left δ δ', min_le_right δ δ' ] ) ; cases abs_cases ( L₁ - L₂ ) <;> cases abs_cases ( ( f ( a + Min.min δ δ' / 2 ) - f a ) / ( a + Min.min δ δ' / 2 - a ) - L₁ ) <;> cases abs_cases ( ( f ( a + Min.min δ δ' / 2 ) - f a ) / ( a + Min.min δ δ' / 2 - a ) - L₂ ) <;> linarith;

/-! ## Differentiability implies continuity -/

/-
A differentiable function is continuous at that point
-/
theorem HasDerivAt'.continuousAt {f : ℝ → ℝ} {a L : ℝ}
    (hf : HasDerivAt' f a L) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε := by
  intro ε hε;
  -- By definition of derivative, we know that for every ε > 0, there exists δ > 0 such that if |x - a| < δ, then |(f x - f a) / (x - a) - L| < ε.
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x, 0 < abs (x - a) → abs (x - a) < δ₁ → abs ((f x - f a) / (x - a) - L) < 1 := by
    exact hf 1 zero_lt_one;
  -- For any x ≠ a, we have |f x - f a| = |(f x - f a) / (x - a) * (x - a)| ≤ |(f x - f a) / (x - a) - L| * |x - a| + |L| * |x - a|.
  have h_bound : ∀ x, x ≠ a → abs (x - a) < δ₁ → abs (f x - f a) ≤ (1 + abs L) * abs (x - a) := by
    intro x hx hx'; specialize hδ₁ x ( abs_pos.mpr ( sub_ne_zero.mpr hx ) ) hx'; rw [ abs_le ] ; constructor <;> cases abs_cases ( x - a ) <;> cases abs_cases L <;> nlinarith [ abs_lt.mp hδ₁, mul_div_cancel₀ ( f x - f a ) ( sub_ne_zero.mpr hx ) ] ;
  exact ⟨ Min.min δ₁ ( ε / ( 1 + |L| ) ), lt_min hδ₁_pos ( div_pos hε ( by positivity ) ), fun x hx => if hx' : x = a then by simpa [ hx' ] using hε else by nlinarith [ min_le_left δ₁ ( ε / ( 1 + |L| ) ), min_le_right δ₁ ( ε / ( 1 + |L| ) ), h_bound x hx' ( lt_of_lt_of_le hx ( min_le_left _ _ ) ), abs_nonneg ( x - a ), mul_div_cancel₀ ε ( by positivity : ( 1 + |L| ) ≠ 0 ) ] ⟩

/-! ## Basic differentiation rules -/

/-
The derivative of a constant function is zero
-/
theorem deriv_const (c a : ℝ) : HasDerivAt' (fun _ => c) a 0 := by
  exact fun ε hε => ⟨ ε, hε, fun x hx₁ hx₂ => by simpa using hε ⟩

/-
The derivative of the identity function is 1
-/
theorem deriv_id (a : ℝ) : HasDerivAt' id a 1 := by
  intro ε hε; use ε; aesop;

/-
The derivative of the linear function f(x) = cx
-/
theorem deriv_const_mul_id (c a : ℝ) : HasDerivAt' (fun x => c * x) a c := by
  intro ε hε;
  exact ⟨ 1, by norm_num, fun x hx₁ hx₂ => by rw [ show ( c * x - c * a ) / ( x - a ) = c by rw [ div_eq_iff ( sub_ne_zero_of_ne <| by aesop ) ] ; ring ] ; simpa ⟩

/-
The sum rule for derivatives
-/
theorem deriv_add {f g : ℝ → ℝ} {a L₁ L₂ : ℝ}
    (hf : HasDerivAt' f a L₁) (hg : HasDerivAt' g a L₂) :
    HasDerivAt' (fun x => f x + g x) a (L₁ + L₂) := by
  intro ε hε; rcases hf ( ε / 2 ) ( half_pos hε ) with ⟨ δ₁, hδ₁, H₁ ⟩ ; rcases hg ( ε / 2 ) ( half_pos hε ) with ⟨ δ₂, hδ₂, H₂ ⟩ ; refine' ⟨ Min.min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx₁ hx₂ => _ ⟩ ; rw [ show ( f x + g x - ( f a + g a ) ) / ( x - a ) = ( f x - f a ) / ( x - a ) + ( g x - g a ) / ( x - a ) by ring ] ; exact abs_lt.2 ⟨ by linarith [ abs_lt.1 ( H₁ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ), abs_lt.1 ( H₂ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ ) ) ) ], by linarith [ abs_lt.1 ( H₁ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ), abs_lt.1 ( H₂ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ ) ) ) ] ⟩ ;

/-
The difference rule for derivatives
-/
theorem deriv_sub {f g : ℝ → ℝ} {a L₁ L₂ : ℝ}
    (hf : HasDerivAt' f a L₁) (hg : HasDerivAt' g a L₂) :
    HasDerivAt' (fun x => f x - g x) a (L₁ - L₂) := by
  intro ε hε;
  -- By the definition of the derivative, we know that for any ε > 0, there exists δ > 0 such that if 0 < |x - a| < δ, then |(f x - f a) / (x - a) - L₁| < ε / 2 and |(g x - g a) / (x - a) - L₂| < ε / 2.
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x, 0 < |x - a| → |x - a| < δ₁ → |(f x - f a) / (x - a) - L₁| < ε / 2 := by
    exact hf ( ε / 2 ) ( half_pos hε )
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x, 0 < |x - a| → |x - a| < δ₂ → |(g x - g a) / (x - a) - L₂| < ε / 2 := by
    exact hg _ ( half_pos hε );
  exact ⟨ Min.min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun x hx₁ hx₂ => by rw [ show ( ( fun x => f x - g x ) x - ( fun x => f x - g x ) a ) / ( x - a ) = ( f x - f a ) / ( x - a ) - ( g x - g a ) / ( x - a ) by ring ] ; exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( hδ₁ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ), abs_lt.mp ( hδ₂ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ ) ) ) ], by linarith [ abs_lt.mp ( hδ₁ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ), abs_lt.mp ( hδ₂ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ ) ) ) ] ⟩ ⟩

/-
The constant-multiple rule for derivatives
-/
theorem deriv_const_mul {f : ℝ → ℝ} {a L c : ℝ}
    (hf : HasDerivAt' f a L) :
    HasDerivAt' (fun x => c * f x) a (c * L) := by
  intro ε hε;
  obtain ⟨ δ, hδ, H ⟩ := hf ( ε / ( |c| + 1 ) ) ( div_pos hε ( by positivity ) );
  refine' ⟨ δ, hδ, fun x hx₁ hx₂ => _ ⟩ ; specialize H x hx₁ hx₂ ; rw [ show ( ( fun x => c * f x ) x - ( fun x => c * f x ) a ) / ( x - a ) - c * L = c * ( ( f x - f a ) / ( x - a ) - L ) by ring ] ; rw [ abs_mul ] ; exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( le_of_lt H ) ( abs_nonneg c ) ) ( by nlinarith [ abs_nonneg c, mul_div_cancel₀ ε ( by positivity : ( |c| + 1 ) ≠ 0 ) ] ) ;

/-
The product rule (Leibniz rule)
-/
theorem deriv_mul {f g : ℝ → ℝ} {a L₁ L₂ : ℝ}
    (hf : HasDerivAt' f a L₁) (hg : HasDerivAt' g a L₂) :
    HasDerivAt' (fun x => f x * g x) a (L₁ * g a + f a * L₂) := by
  intro ε hε;
  -- By the properties of the derivative, we can write
  have h_deriv : ∀ x, x ≠ a → ((f x * g x - f a * g a) / (x - a)) = ((f x - f a) / (x - a)) * g x + f a * ((g x - g a) / (x - a)) := by
    intro x hx; ring;
  -- By the properties of the derivative, we can write the limit expression.
  have h_limit : Filter.Tendsto (fun x => ((f x - f a) / (x - a)) * g x + f a * ((g x - g a) / (x - a))) (nhdsWithin a {a}ᶜ) (nhds (L₁ * g a + f a * L₂)) := by
    refine' Filter.Tendsto.add _ _;
    · refine' Filter.Tendsto.mul _ _;
      · rw [ Metric.tendsto_nhdsWithin_nhds ];
        exact fun ε hε => by rcases hf ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun x hx₁ hx₂ => H x ( abs_pos.mpr ( sub_ne_zero.mpr hx₁ ) ) hx₂ ⟩ ;
      · exact tendsto_nhdsWithin_of_tendsto_nhds ( by exact Metric.tendsto_nhds_nhds.mpr fun ε hε => by have := HasDerivAt'.continuousAt hg ε hε; aesop );
    · refine' Filter.Tendsto.mul tendsto_const_nhds _;
      rw [ Metric.tendsto_nhdsWithin_nhds ];
      exact fun ε hε => by rcases hg ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun x hx₁ hx₂ => H x ( abs_pos.mpr ( sub_ne_zero.mpr hx₁ ) ) hx₂ ⟩ ;
  rw [ Metric.tendsto_nhdsWithin_nhds ] at h_limit;
  exact Exists.elim ( h_limit ε hε ) fun δ hδ => ⟨ δ, hδ.1, fun x hx₁ hx₂ => by simpa only [ h_deriv x ( by aesop ) ] using hδ.2 ( by aesop ) hx₂ ⟩

/-! ## Equivalence with Mathlib's HasDerivAt -/

/-
Equivalent to Mathlib's HasDerivAt
-/
theorem hasDerivAt'_iff_hasDerivAt {f : ℝ → ℝ} {a L : ℝ} :
    HasDerivAt' f a L ↔ HasDerivAt f L a := by
  rw [ hasDerivAt_iff_tendsto_slope ];
  rw [ Metric.tendsto_nhdsWithin_nhds ] ; simp +decide [ HasDerivAt', slope_def_field ] ;
  simp +decide [ sub_eq_iff_eq_add, dist_eq_norm ]

/-! ## Derivatives of power functions -/

/-
The derivative of x² is 2x
-/
theorem deriv_sq (a : ℝ) : HasDerivAt' (fun x => x ^ 2) a (2 * a) := by
  convert hasDerivAt'_iff_hasDerivAt.mpr ( hasDerivAt_pow 2 ( a : ℝ ) ) using 1 ; ring_nf;

/-
The derivative of x³ is 3x²
-/
theorem deriv_cube (a : ℝ) : HasDerivAt' (fun x => x ^ 3) a (3 * a ^ 2) := by
  -- We can use the fact that $x^3 - a^3 = (x-a)(x^2 + ax + a^2)$ to simplify the expression.
  suffices h_simp : ∀ x, x ≠ a → |(x^3 - a^3) / (x - a) - 3 * a^2| = |(x - a) * (x + 2 * a)| by
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x, |x - a| < δ → |(x - a) * (x + 2 * a)| < ε := by
      simpa [ abs_mul ] using Metric.continuous_iff.mp ( show Continuous fun x : ℝ => ( x - a ) * ( x + 2 * a ) by continuity ) a ε hε;
    exact ⟨ δ, hδ_pos, fun x hx₁ hx₂ => h_simp x ( by aesop ) ▸ hδ x hx₂ ⟩;
  grind +qlia

end RGF.Analysis