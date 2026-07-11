/-
  RGF generative analysis system (II) — theory of continuity
  Within the dual-layer iteration axiom framework, continuity is defined in the ε-δ language and the basic theorems are proved.
-/

import Mathlib

open Set Filter Topology

namespace RGF.Analysis

/-! ## The ε-δ definition of continuity -/

/-- The function f is continuous at the point a (ε-δ definition). -/
def ContinuousAt' (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

/-- The function is continuous on its entire domain. -/
def Continuous' (f : ℝ → ℝ) : Prop :=
  ∀ a, ContinuousAt' f a

/-! ## Basic continuous functions -/

/-
Constant functions are continuous
-/
theorem continuous_const' (c : ℝ) : Continuous' (fun _ => c) := by
  exact fun _ => fun ε hε => ⟨ 1, zero_lt_one, fun _ _ => by simpa using hε ⟩

/-
The identity function is continuous
-/
theorem continuous_id' : Continuous' id := by
  exact fun _ => fun _ _ => ⟨ _, ‹_›, fun x hx => hx ⟩

/-! ## Operations on continuous functions -/

/-
The sum of continuous functions is continuous
-/
theorem continuousAt_add {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt' f a) (hg : ContinuousAt' g a) :
    ContinuousAt' (fun x => f x + g x) a := by
  intro ε hε;
  rcases hf ( ε / 2 ) ( half_pos hε ) with ⟨ δ₁, hδ₁, H₁ ⟩ ; rcases hg ( ε / 2 ) ( half_pos hε ) with ⟨ δ₂, hδ₂, H₂ ⟩ ; exact ⟨ Min.min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx => abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( H₁ x ( lt_of_lt_of_le hx ( min_le_left _ _ ) ) ), abs_lt.mp ( H₂ x ( lt_of_lt_of_le hx ( min_le_right _ _ ) ) ) ], by linarith [ abs_lt.mp ( H₁ x ( lt_of_lt_of_le hx ( min_le_left _ _ ) ) ), abs_lt.mp ( H₂ x ( lt_of_lt_of_le hx ( min_le_right _ _ ) ) ) ] ⟩ ⟩ ;

/-
The difference of continuous functions is continuous
-/
theorem continuousAt_sub {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt' f a) (hg : ContinuousAt' g a) :
    ContinuousAt' (fun x => f x - g x) a := by
  exact fun ε hε => by rcases hf ( ε / 2 ) ( half_pos hε ) with ⟨ δ, hδ, H ⟩ ; rcases hg ( ε / 2 ) ( half_pos hε ) with ⟨ δ', hδ', H' ⟩ ; exact ⟨ Min.min δ δ', lt_min hδ hδ', fun x hx => abs_sub_lt_iff.mpr ⟨ by linarith [ abs_lt.mp ( H x ( lt_of_lt_of_le hx ( min_le_left _ _ ) ) ), abs_lt.mp ( H' x ( lt_of_lt_of_le hx ( min_le_right _ _ ) ) ) ], by linarith [ abs_lt.mp ( H x ( lt_of_lt_of_le hx ( min_le_left _ _ ) ) ), abs_lt.mp ( H' x ( lt_of_lt_of_le hx ( min_le_right _ _ ) ) ) ] ⟩ ⟩ ;

/-
A constant multiple of a continuous function is continuous
-/
theorem continuousAt_const_mul {f : ℝ → ℝ} {a : ℝ} (c : ℝ)
    (hf : ContinuousAt' f a) :
    ContinuousAt' (fun x => c * f x) a := by
  intro ε hε;
  rcases eq_or_ne c 0 with ( rfl | hc );
  · exact ⟨ ε, hε, fun x hx => by simpa using hε ⟩;
  · obtain ⟨ δ, hδ, H ⟩ := hf ( ε / |c| ) ( div_pos hε ( abs_pos.mpr hc ) ) ; exact ⟨ δ, hδ, fun x hx => by rw [ ← mul_sub, abs_mul ] ; nlinarith [ abs_pos.mpr hc, mul_div_cancel₀ ε ( ne_of_gt ( abs_pos.mpr hc ) ), H x hx ] ⟩ ;

/-
The product of continuous functions is continuous
-/
theorem continuousAt_mul {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt' f a) (hg : ContinuousAt' g a) :
    ContinuousAt' (fun x => f x * g x) a := by
  intro ε hε;
  obtain ⟨ δ₁, hδ₁, H₁ ⟩ := hf ( Min.min ( ε / ( 3 * ( |f a| + |g a| + 1 ) ) ) 1 ) ( lt_min ( by positivity ) zero_lt_one );
  obtain ⟨ δ₂, hδ₂, H₂ ⟩ := hg ( ε / ( 3 * ( |f a| + |g a| + 1 ) ) ) ( by positivity ) ; use Min.min δ₁ δ₂; simp_all +decide [ mul_add ];
  intro x hx₁ hx₂; rw [ abs_lt ] ; constructor <;> cases abs_cases ( f a ) <;> cases abs_cases ( g a ) <;> nlinarith [ abs_lt.mp ( H₁ x hx₁ |>.1 ), abs_lt.mp ( H₁ x hx₁ |>.2 ), abs_lt.mp ( H₂ x hx₂ ), mul_div_cancel₀ ε ( by linarith : ( 3 * |f a| + 3 * |g a| + 3 ) ≠ 0 ) ] ;

/-
The composition of continuous functions is continuous
-/
theorem continuousAt_comp {f g : ℝ → ℝ} {a : ℝ}
    (hg : ContinuousAt' g a) (hf : ContinuousAt' f (g a)) :
    ContinuousAt' (fun x => f (g x)) a := by
  exact fun ε hε => by rcases hf ε hε with ⟨ δ₁, hδ₁, H₁ ⟩ ; rcases hg δ₁ hδ₁ with ⟨ δ₂, hδ₂, H₂ ⟩ ; exact ⟨ δ₂, hδ₂, fun x hx => H₁ _ ( H₂ _ hx ) ⟩ ;

/-! ## Equivalence with Mathlib continuity -/

/-
Our ε-δ continuity is equivalent to Mathlib's ContinuousAt
-/
theorem continuousAt'_iff_continuousAt {f : ℝ → ℝ} {a : ℝ} :
    ContinuousAt' f a ↔ ContinuousAt f a := by
  rw [ Metric.continuousAt_iff ];
  rfl

/-! ## Intermediate value theorem (via Mathlib) -/

/-
Intermediate value theorem: a continuous function attains intermediate values on a closed interval
-/
theorem intermediate_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, ContinuousAt' f x)
    (y : ℝ) (hy : y ∈ Icc (min (f a) (f b)) (max (f a) (f b))) :
    ∃ c ∈ Icc a b, f c = y := by
  -- Apply the intermediate value theorem.
  have h_ivt : IsConnected (f '' Set.Icc a b) := by
    apply_rules [ IsConnected.image, isConnected_Icc ];
    exact fun x hx => continuousAt'_iff_continuousAt.mp ( hf x hx ) |> ContinuousAt.continuousWithinAt;
  cases le_total ( f a ) ( f b ) <;> simp_all +decide [ IsConnected ];
  · exact h_ivt.Icc_subset ( Set.mem_image_of_mem f <| Set.left_mem_Icc.mpr hab ) ( Set.mem_image_of_mem f <| Set.right_mem_Icc.mpr hab ) ⟨ hy.1, hy.2 ⟩;
  · exact h_ivt.Icc_subset ( Set.mem_image_of_mem f <| Set.right_mem_Icc.mpr hab ) ( Set.mem_image_of_mem f <| Set.left_mem_Icc.mpr hab ) ⟨ hy.1, hy.2 ⟩

end RGF.Analysis