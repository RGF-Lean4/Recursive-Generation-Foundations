/-
  RGF generative analysis system (I) — theory of limits
  Within the dual-layer iteration axiom framework, the theory of limits of real functions is built from the ε-δ language.
-/

import Mathlib

open Set Filter Topology

namespace RGF.Analysis

/-! ## The ε-δ definition of the limit of a function -/

/-- The limit of the function f at the point a is L (ε-δ definition). -/
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| → |x - a| < δ → |f x - L| < ε

/-! ## Uniqueness of limits -/

/-
If a limit exists, it is unique
-/
theorem limit_unique {f : ℝ → ℝ} {a L₁ L₂ : ℝ}
    (h₁ : HasLimitAt f a L₁) (h₂ : HasLimitAt f a L₂) : L₁ = L₂ := by
  contrapose! h₁;
  unfold HasLimitAt at *;
  simp +zetaDelta at *;
  exact ⟨ |L₁ - L₂| / 2, half_pos ( abs_pos.mpr ( sub_ne_zero.mpr h₁ ) ), fun ε ε_pos => by rcases h₂ ( |L₁ - L₂| / 2 ) ( half_pos ( abs_pos.mpr ( sub_ne_zero.mpr h₁ ) ) ) with ⟨ δ, δ_pos, H ⟩ ; exact ⟨ a + Min.min ε δ / 2, by linarith [ lt_min ε_pos δ_pos ], by rw [ abs_of_pos ] <;> linarith [ lt_min ε_pos δ_pos, min_le_left ε δ, min_le_right ε δ ], by cases abs_cases ( f ( a + Min.min ε δ / 2 ) - L₁ ) <;> cases abs_cases ( L₁ - L₂ ) <;> linarith [ abs_lt.mp ( H ( a + Min.min ε δ / 2 ) ( by linarith [ lt_min ε_pos δ_pos ] ) ( by rw [ abs_of_pos ] <;> linarith [ lt_min ε_pos δ_pos, min_le_left ε δ, min_le_right ε δ ] ) ) ] ⟩ ⟩

/-! ## Arithmetic of limits -/

/-
The limit of a constant function
-/
theorem limit_const (c a : ℝ) : HasLimitAt (fun _ => c) a c := by
  exact fun ε hε => ⟨ 1, by norm_num, fun _ _ _ => by simpa ⟩

/-
The limit of the identity function
-/
theorem limit_id (a : ℝ) : HasLimitAt id a a := by
  exact fun ε hε => ⟨ ε, hε, fun x hx₁ hx₂ => by simpa using hx₂ ⟩

/-
Addition of limits
-/
theorem limit_add {f g : ℝ → ℝ} {a L₁ L₂ : ℝ}
    (hf : HasLimitAt f a L₁) (hg : HasLimitAt g a L₂) :
    HasLimitAt (fun x => f x + g x) a (L₁ + L₂) := by
  exact fun ε ε_pos ↦ by rcases hf ( ε / 2 ) ( half_pos ε_pos ) with ⟨ δ₁, δ₁_pos, H₁ ⟩ ; rcases hg ( ε / 2 ) ( half_pos ε_pos ) with ⟨ δ₂, δ₂_pos, H₂ ⟩ ; exact ⟨ Min.min δ₁ δ₂, lt_min δ₁_pos δ₂_pos, fun x hx₁ hx₂ ↦ abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( H₁ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ), abs_lt.mp ( H₂ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ ) ) ) ], by linarith [ abs_lt.mp ( H₁ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ), abs_lt.mp ( H₂ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ ) ) ) ] ⟩ ⟩ ;

/-
Subtraction of limits
-/
theorem limit_sub {f g : ℝ → ℝ} {a L₁ L₂ : ℝ}
    (hf : HasLimitAt f a L₁) (hg : HasLimitAt g a L₂) :
    HasLimitAt (fun x => f x - g x) a (L₁ - L₂) := by
  intro ε hε;
  obtain ⟨ δ₁, hδ₁, H₁ ⟩ := hf ( ε / 2 ) ( half_pos hε ) ; obtain ⟨ δ₂, hδ₂, H₂ ⟩ := hg ( ε / 2 ) ( half_pos hε ) ; exact ⟨ Min.min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx₁ hx₂ => abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( H₁ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ), abs_lt.mp ( H₂ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ ) ) ) ], by linarith [ abs_lt.mp ( H₁ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ), abs_lt.mp ( H₂ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ ) ) ) ] ⟩ ⟩ ;

/-
Constant multiple of a limit
-/
theorem limit_const_mul {f : ℝ → ℝ} {a L c : ℝ}
    (hf : HasLimitAt f a L) :
    HasLimitAt (fun x => c * f x) a (c * L) := by
  intro ε hε;
  rcases eq_or_ne c 0 with ( rfl | hc );
  · aesop;
  · rcases hf ( ε / |c| ) ( by positivity ) with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun x hx₁ hx₂ => by rw [ ← mul_sub ] ; rw [ abs_mul ] ; exact lt_of_lt_of_le ( mul_lt_mul_of_pos_left ( H x hx₁ hx₂ ) ( abs_pos.mpr hc ) ) ( by nlinarith [ abs_pos.mpr hc, mul_div_cancel₀ ε ( ne_of_gt ( abs_pos.mpr hc ) ) ] ) ⟩ ;

/-
Multiplication of limits
-/
theorem limit_mul {f g : ℝ → ℝ} {a L₁ L₂ : ℝ}
    (hf : HasLimitAt f a L₁) (hg : HasLimitAt g a L₂) :
    HasLimitAt (fun x => f x * g x) a (L₁ * L₂) := by
  intro ε hε;
  -- Use the identity $f(x)g(x) - L₁L₂ = (f(x) - L₁)(g(x) - L₂) + L₁(g(x) - L₂) + (f(x) - L₁)L₂$.
  have h_identity : ∀ x, f x * g x - L₁ * L₂ = (f x - L₁) * (g x - L₂) + L₁ * (g x - L₂) + (f x - L₁) * L₂ := by
    exact fun x => by ring;
  -- Choose δ such that |f(x) - L₁| < δ and |g(x) - L₂| < δ for |x - a| < δ.
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ > 0, ∀ x, 0 < |x - a| → |x - a| < δ₁ → |f x - L₁| < min 1 (ε / (3 * (|L₁| + |L₂| + 1))) := by
    exact hf _ ( lt_min zero_lt_one ( div_pos hε ( by positivity ) ) );
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂ > 0, ∀ x, 0 < |x - a| → |x - a| < δ₂ → |g x - L₂| < min 1 (ε / (3 * (|L₁| + |L₂| + 1))) := by
    exact hg _ ( lt_min zero_lt_one ( div_pos hε ( by positivity ) ) );
  refine' ⟨ Min.min δ₁ δ₂, lt_min hδ₁.1 hδ₂.1, fun x hx₁ hx₂ => _ ⟩ ; simp_all +decide;
  refine' lt_of_le_of_lt ( abs_add_three _ _ _ ) _;
  rw [ abs_mul, abs_mul, abs_mul ];
  nlinarith [ hδ₁.2 x hx₁ hx₂.1, hδ₂.2 x hx₁ hx₂.2, abs_nonneg ( f x - L₁ ), abs_nonneg ( g x - L₂ ), abs_nonneg L₁, abs_nonneg L₂, mul_div_cancel₀ ε ( by positivity : ( 3 * ( |L₁| + |L₂| + 1 ) ) ≠ 0 ) ]

/-
Squeeze theorem (sandwich theorem)
-/
theorem limit_squeeze {f g h : ℝ → ℝ} {a L : ℝ}
    (hfg : ∃ δ₀ > 0, ∀ x, 0 < |x - a| → |x - a| < δ₀ → f x ≤ g x)
    (hgh : ∃ δ₀ > 0, ∀ x, 0 < |x - a| → |x - a| < δ₀ → g x ≤ h x)
    (hf : HasLimitAt f a L) (hh : HasLimitAt h a L) :
    HasLimitAt g a L := by
  intros ε hεpos
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ₀ > 0, ∀ x, 0 < |x - a| → |x - a| < δ₀ → f x ≤ g x := hfg
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x, 0 < |x - a| → |x - a| < δ₁ → g x ≤ h x := hgh;
  rcases hf ε hεpos with ⟨ δ₂, hδ₂pos, H₂ ⟩ ; rcases hh ε hεpos with ⟨ δ₃, hδ₃pos, H₃ ⟩ ; exact ⟨ Min.min δ₀ ( Min.min δ₁ ( Min.min δ₂ δ₃ ) ), lt_min hδ₀pos ( lt_min hδ₁pos ( lt_min hδ₂pos hδ₃pos ) ), fun x hx₁ hx₂ => abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( H₂ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ |> le_trans <| min_le_right _ _ |> le_trans <| min_le_left _ _ ) ) ), hδ₀ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ], by linarith [ abs_lt.mp ( H₃ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ |> le_trans <| min_le_right _ _ |> le_trans <| min_le_right _ _ ) ) ), hδ₁ x hx₁ ( lt_of_lt_of_le hx₂ ( min_le_right _ _ |> le_trans <| min_le_left _ _ ) ) ] ⟩ ⟩ ;

/-! ## Equivalence with Mathlib's Filter.Tendsto -/

/-
Our ε-δ limit is equivalent to Mathlib's Filter.Tendsto
-/
theorem hasLimitAt_iff_tendsto {f : ℝ → ℝ} {a L : ℝ} :
    HasLimitAt f a L ↔ Filter.Tendsto f (𝓝[≠] a) (𝓝 L) := by
  simp +decide only [HasLimitAt, Metric.tendsto_nhdsWithin_nhds];
  simp +decide [ Real.dist_eq, sub_eq_zero ]

end RGF.Analysis