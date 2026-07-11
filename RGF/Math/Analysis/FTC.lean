/-
  RGF generative analysis system (V) — the fundamental theorem of calculus
  Within the dual-layer iteration axiom framework, both parts of the fundamental theorem of calculus are proved.
-/

import Mathlib

open Set MeasureTheory

namespace RGF.Analysis

/-! ## Fundamental theorem of calculus, Part 1

  If f is continuous on [a,b], define F(x) = ∫_a^x f(t) dt;
  then F is differentiable on (a,b) and F'(x) = f(x).
-/

/-- The integral function with variable upper limit. -/
noncomputable def integralFunction (f : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  fun x => ∫ t in a..x, f t

/-
Fundamental theorem of calculus, Part 1: the derivative of the variable-upper-limit integral equals the integrand
    If f is continuous at x, then (∫_a^x f(t) dt)' = f(x)
-/
theorem ftc_part1 {f : ℝ → ℝ} {a x : ℝ}
    (hf : ContinuousAt f x)
    (hfi : ∀ y, IntervalIntegrable f MeasureTheory.MeasureSpace.volume a y) :
    HasDerivAt (integralFunction f a) (f x) x := by
  apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
  have h_measurable : MeasureTheory.AEStronglyMeasurable f volume := by
    have h_integrable : ∀ y, MeasureTheory.IntegrableOn f (Set.Icc (min a y) (max a y)) := by
      intro y; specialize hfi y; cases le_total a y <;> simp_all +decide [ intervalIntegrable_iff ] ;
      · rwa [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ] at *;
      · rwa [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ] at *;
    have h_measurable : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Measure.restrict volume (Set.Icc (-n + a) (n + a))) := by
      intro n;
      have := h_integrable ( -n + a ) ; have := h_integrable ( n + a ) ; simp_all +decide [ min_def, max_def ];
      have h_integrable : MeasureTheory.IntegrableOn f (Set.Icc (-n + a) (n + a)) := by
        convert MeasureTheory.IntegrableOn.union ‹IntegrableOn f ( Set.Icc ( -n + a ) a ) volume› ‹IntegrableOn f ( Set.Icc a ( n + a ) ) volume› using 1 ; rw [ Set.Icc_union_Icc_eq_Icc ] <;> linarith;
      exact h_integrable.1;
    have h_measurable : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Measure.restrict volume (⋃ n : ℕ, Set.Icc (-n + a) (n + a))) := by
      exact MeasureTheory.AEStronglyMeasurable.iUnion h_measurable;
    convert h_measurable using 1;
    rw [ MeasureTheory.Measure.restrict_eq_self_of_ae_mem ];
    filter_upwards [ ] with x using Set.mem_iUnion.2 ⟨ ⌈|x - a|⌉₊, ⟨ by cases abs_cases ( x - a ) <;> linarith [ Nat.le_ceil ( |x - a| ) ], by cases abs_cases ( x - a ) <;> linarith [ Nat.le_ceil ( |x - a| ) ] ⟩ ⟩;
  exact?

/-! ## Fundamental theorem of calculus, Part 2 (Newton-Leibniz formula)

  If F is an antiderivative of f on [a,b] (i.e. F' = f) and f is integrable,
  then ∫_a^b f(x) dx = F(b) - F(a).
-/

/-
Newton-Leibniz formula
-/
theorem ftc_part2 {F f : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f x) x)
    (hf : IntervalIntegrable f MeasureTheory.MeasureSpace.volume a b) :
    ∫ x in a..b, f x = F b - F a := by
  rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ]; all_goals assumption

/-! ## Corollaries -/

/-
A continuous function is integrable on a closed interval (via Mathlib)
-/
theorem continuous_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) :
    IntervalIntegrable f MeasureTheory.MeasureSpace.volume a b := by
  exact hf.intervalIntegrable a b

/-
Mean value theorem for integrals: if f is continuous on [a,b], then there exists c ∈ [a,b]
    such that ∫_a^b f(x) dx = f(c) * (b - a)
-/
theorem integral_mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, ∫ x in a..b, f x = f c * (b - a) := by
  -- By the properties of integrals, we know that ∫ x in a..b, f x is between m * (b - a) and M * (b - a).
  have h_integral_bounds : (∫ x in a..b, f x) ∈ Set.Icc (sInf (f '' Set.Icc a b) * (b - a)) (sSup (f '' Set.Icc a b) * (b - a)) := by
    rw [ intervalIntegral.integral_of_le hab.le ];
    exact ⟨ by rw [ mul_comm ] ; exact le_trans ( by norm_num [ hab.le ] ) ( MeasureTheory.setIntegral_mono_on ( by norm_num ) ( by exact hf.integrableOn_Icc.mono_set <| Set.Ioc_subset_Icc_self ) measurableSet_Ioc fun x hx => ( csInf_le ( IsCompact.bddBelow <| isCompact_Icc.image_of_continuousOn hf ) <| Set.mem_image_of_mem _ <| Set.Ioc_subset_Icc_self hx ) ), by rw [ mul_comm ] ; exact le_trans ( MeasureTheory.setIntegral_mono_on ( by exact hf.integrableOn_Icc.mono_set <| Set.Ioc_subset_Icc_self ) ( by norm_num ) measurableSet_Ioc fun x hx => ( le_csSup ( IsCompact.bddAbove <| isCompact_Icc.image_of_continuousOn hf ) <| Set.mem_image_of_mem _ <| Set.Ioc_subset_Icc_self hx ) ) ( by norm_num [ hab.le ] ) ⟩;
  -- By the properties of integrals, we know that there exists some $c \in [a, b]$ such that $f(c) = \frac{1}{b - a} \int_a^b f(x) \, dx$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Icc a b, f c = (∫ x in a..b, f x) / (b - a) := by
    have := hf.image_Icc hab.le;
    exact this.symm.subset ⟨ by rw [ le_div_iff₀ ] <;> linarith [ h_integral_bounds.1 ], by rw [ div_le_iff₀ ] <;> linarith [ h_integral_bounds.2 ] ⟩;
  exact ⟨ c, hc.1, by rw [ hc.2, div_mul_cancel₀ _ ( sub_ne_zero_of_ne hab.ne' ) ] ⟩

/-! ## Connection with RGF dual-layer iteration

  The fundamental theorem of calculus embodies the ancestor-offspring recursive structure of
  differentiation and integration as "mutually inverse operations":
  - ancestor layer (integration): the accumulated quantity F(x) = ∫_a^x f(t)dt
  - offspring layer (differentiation): the instantaneous rate of change F'(x) = f(x)
  - dual-layer iteration: differentiation and integration are mutual inverses, forming a closed recursion.
-/

/-
RGF perspective: the fundamental theorem of calculus shows that integration is the inverse of differentiation
-/
theorem rgf_calculus_duality {f : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) :
    HasDerivAt (integralFunction f a) (f a) a := by
  apply_rules [ ftc_part1 ];
  · exact hf.continuousAt;
  · exact fun y => hf.intervalIntegrable a y

end RGF.Analysis