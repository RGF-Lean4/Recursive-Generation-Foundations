/-
  Strict quasiconvexity/quasiconcavity and uniqueness of extremum points

  Mathematical content extracted from the user's document:
  - a strictly quasiconcave function on a compact convex set has a unique maximum point
  - the Weierstrass extreme value theorem guarantees existence
  - the evaluation functional E[G] is strictly convex in the parsimony component,
    so as a weighted sum it is strictly quasiconcave, yielding a unique optimal solution
-/

import Mathlib

open Set Filter Topology

/-- A function f on a convex set is strictly quasiconcave if, for any two distinct points,
    the value at any strict convex combination is strictly greater than the minimum of the two endpoint values.
    This is the condition guaranteeing uniqueness of the maximum point. -/
def StrictlyQuasiconcave {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Set E) (f : E → ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ t : ℝ, 0 < t → t < 1 →
    f (t • x + (1 - t) • y) > min (f x) (f y)

/-
Uniqueness of the maximum point: a strictly quasiconcave function on a convex set has at most one global maximum point.
    Proof: if x ≠ y are both maximum points, then f(x) = f(y) = M. Then f(midpoint) > min(M, M) = M,
    but M is the maximum, a contradiction.
-/
theorem strictlyQuasiconcave_unique_maximizer {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {s : Set E} {f : E → ℝ} (hs : Convex ℝ s)
    (hf : StrictlyQuasiconcave s f)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    (hxmax : ∀ z ∈ s, f z ≤ f x) (hymax : ∀ z ∈ s, f z ≤ f y) :
    x = y := by
      contrapose! hf;
      norm_num [ StrictlyQuasiconcave ];
      exact ⟨ x, hx, y, hy, hf, 1 / 2, by norm_num, by norm_num, by linarith [ hxmax ( ( 1 / 2 : ℝ ) • x + ( 1 - ( 1 / 2 ) : ℝ ) • y ) ( hs hx hy ( by norm_num ) ( by norm_num ) ( by norm_num ) ) ], by linarith [ hymax ( ( 1 / 2 : ℝ ) • x + ( 1 - ( 1 / 2 ) : ℝ ) • y ) ( hs hx hy ( by norm_num ) ( by norm_num ) ( by norm_num ) ) ] ⟩

/-
A strictly concave function is strictly quasiconcave.
-/
theorem strictConcaveOn_strictlyQuasiconcave {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    {s : Set E} {f : E → ℝ} (hf : StrictConcaveOn ℝ s f) :
    StrictlyQuasiconcave s f := by
      intro x hx y hy hxy t ht ht';
      have := hf.2 hx hy hxy ht ( show 0 < 1 - t by linarith ) ( by linarith );
      cases min_cases ( f x ) ( f y ) <;> simp_all +decide; all_goals nlinarith

/-
A strictly quasiconcave continuous function on a nonempty compact convex set has a unique global maximum.
-/
theorem unique_max_of_strictly_quasiconcave {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconv : Convex ℝ K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContinuousOn f K)
    (hSQC : StrictlyQuasiconcave K f) :
    ∃! x ∈ K, ∀ y ∈ K, f y ≤ f x := by
      obtain ⟨x, hx⟩ : ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
        exact hK.exists_isMaxOn hKne hf;
      exact ⟨ x, hx, fun y hy => strictlyQuasiconcave_unique_maximizer hKconv hSQC hy.1 hx.1 hy.2 hx.2 ⟩

/-
The parsimony function exp(-|G|/log|Surv|) is strictly convex (hence -Pars is strictly concave).
    Combined with a linear function, the evaluation functional is strictly concave, and the theorem above gives a unique optimal solution.
-/
theorem exp_neg_strictConvex : StrictConvexOn ℝ Set.univ (fun x : ℝ => Real.exp (-x)) := by
  fapply strictConvexOn_of_deriv2_pos' ( convex_univ );
  · fun_prop;
  · unfold deriv ; norm_num [ fderiv_apply_one_eq_deriv, Real.exp_neg ];
    exact fun x => by rw [ lt_div_iff₀ ( by positivity ) ] ; nlinarith [ Real.exp_pos x, pow_pos ( Real.exp_pos x ) 3 ] ;