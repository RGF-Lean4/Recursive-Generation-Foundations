/-
  RGF generative analysis system (IV) — theory of integration
  Within the dual-layer iteration axiom framework, the indefinite and definite (Riemann) integrals are defined,
  and the basic properties of integration are proved.
-/

import Mathlib

open Set MeasureTheory

namespace RGF.Analysis

/-! ## Indefinite integral (antiderivative) -/

/-- F is an antiderivative (indefinite integral) of f, i.e. F' = f. -/
def IsAntideriv (F f : ℝ → ℝ) : Prop :=
  ∀ x, HasDerivAt F (f x) x

/-
The difference of two antiderivatives is constant (uniqueness theorem for indefinite integrals)
-/
theorem antideriv_diff_const {F G f : ℝ → ℝ}
    (hF : IsAntideriv F f) (hG : IsAntideriv G f) :
    ∃ C : ℝ, ∀ x, F x - G x = C := by
  -- By the mean value theorem, a function with zero derivative everywhere is constant.
  have h_const : ∀ (h : ℝ → ℝ), (∀ x, HasDerivAt h 0 x) → ∃ C, ∀ x, h x = C := by
    intro h hh; use h 0; intro x; exact is_const_of_deriv_eq_zero ( fun x => ( hh x |> HasDerivAt.differentiableAt ) ) ( fun x => ( hh x |> HasDerivAt.deriv ) ) x 0;
  exact h_const _ fun x => by simpa using HasDerivAt.sub ( hF x ) ( hG x ) ;

/-! ## Definition of the definite integral (using Mathlib's intervalIntegral) -/

/-- The definite integral ∫_a^b f(x) dx, using Mathlib's intervalIntegral. -/
noncomputable def definiteIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, f x

/-! ## Basic properties of the definite integral -/

/-
Linearity of the integral: constant multiple
-/
theorem integral_const_mul (c : ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (_hf : IntervalIntegrable f MeasureTheory.MeasureSpace.volume a b) :
    definiteIntegral (fun x => c * f x) a b = c * definiteIntegral f a b := by
  unfold definiteIntegral; rw [ intervalIntegral.integral_const_mul ] ;

/-
Linearity of the integral: addition
-/
theorem integral_add' (f g : ℝ → ℝ) (a b : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.MeasureSpace.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.MeasureSpace.volume a b) :
    definiteIntegral (fun x => f x + g x) a b =
    definiteIntegral f a b + definiteIntegral g a b := by
  convert intervalIntegral.integral_add hf hg using 1

/-
Additivity over intervals
-/
theorem integral_add_adjacent (f : ℝ → ℝ) (a b c : ℝ)
    (hab : IntervalIntegrable f MeasureTheory.MeasureSpace.volume a b)
    (hbc : IntervalIntegrable f MeasureTheory.MeasureSpace.volume b c) :
    definiteIntegral f a b + definiteIntegral f b c = definiteIntegral f a c := by
  unfold definiteIntegral; rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> aesop;

/-
Swapping the limits of integration changes the sign
-/
theorem integral_symm (f : ℝ → ℝ) (a b : ℝ) :
    definiteIntegral f a b = -definiteIntegral f b a := by
  unfold definiteIntegral; rw [ intervalIntegral.integral_symm ] ;

/-
The integral of a constant function
-/
theorem integral_const' (c : ℝ) (a b : ℝ) :
    definiteIntegral (fun _ => c) a b = c * (b - a) := by
  -- Apply the integral_const_mul theorem with f = fun x => 1, hf = intervalIntegral.intervalIntegrable_const.
  simp [definiteIntegral, mul_comm]

/-
Monotonicity of the integral
-/
theorem integral_mono' {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.MeasureSpace.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.MeasureSpace.volume a b)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    definiteIntegral f a b ≤ definiteIntegral g a b := by
  apply_rules [ intervalIntegral.integral_mono_on ]

end RGF.Analysis