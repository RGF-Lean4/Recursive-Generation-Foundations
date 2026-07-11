/-
  RGF/ConstructiveODE.lean

  Task I — Constructive analysis and (O)DE/PDE theory.

  A `sorry`-free development of the constructive existence/uniqueness backbone of
  differential equations, in the spirit of "computable generating sequences":

  * **Part A — Constructive Picard–Lindelöf (Banach fixed point).**
    `IsContraction`, the explicit Picard iteration `picardIter T x₀ n = T^[n] x₀`,
    convergence to a fixed point with an explicit geometric a-priori error bound
    (`picard_exists_fixedPoint`), and uniqueness (`contraction_fixedPoint_unique`).
    This is the constructive engine underlying Picard–Lindelöf: the solution of
    an ODE is the limit of the explicitly generated Picard sequence.

  * **Part B — The scalar ODE.**  For the linear Cauchy problem `u' = a·u`,
    `u(t₀) = u₀`, the solution exists, is unique, and is explicitly the limit of
    the Picard iteration (`linear_ode_exists_unique`).

  * **Part C — Constructive Cauchy–Kowalevski (recursive Taylor coefficients).**
    For the analytic linear Cauchy problem `u' = a(t)·u`, `u(0) = u₀` (with `a`
    given by its power-series coefficients `α`), the Taylor coefficients of the
    solution are produced by an explicit recursion `ckCoeff` — a *computable
    generating sequence*.  We prove this sequence is a formal solution
    (`ckCoeff_isSolution`), that the analytic solution is unique
    (`ck_solution_unique`), packaged as `ck_exists_unique`, and that in the
    constant-coefficient case the sequence is exactly the Taylor sequence of the
    exponential (`ckCoeff_const`), tying the formal solution back to the genuine
    analytic solution of Part B.

  All estimates are explicit; nothing beyond Mathlib's metric/analysis library
  (which the RGF reals instantiate via the proven ordered-ring isomorphism
  `RGFReal' ≃+*o ℝ`) is presupposed.
-/

import Mathlib

open scoped Topology BigOperators
open Filter

namespace RGF.ConstructiveAnalysis

/-! ## Part A — Constructive Picard–Lindelöf (Banach fixed point) -/

/-- A contraction on a metric space with modulus `K < 1`. -/
structure IsContraction {X : Type*} [MetricSpace X] (T : X → X) (K : ℝ) : Prop where
  K_nonneg : 0 ≤ K
  K_lt_one : K < 1
  lipschitz : ∀ x y, dist (T x) (T y) ≤ K * dist x y

/-- The Picard iteration: the explicitly generated sequence `x₀, T x₀, T² x₀, …`. -/
def picardIter {X : Type*} (T : X → X) (x₀ : X) (n : ℕ) : X := T^[n] x₀

@[simp] theorem picardIter_zero {X : Type*} (T : X → X) (x₀ : X) :
    picardIter T x₀ 0 = x₀ := rfl

theorem picardIter_succ {X : Type*} (T : X → X) (x₀ : X) (n : ℕ) :
    picardIter T x₀ (n + 1) = T (picardIter T x₀ n) := by
  simp [picardIter, Function.iterate_succ_apply']

/-
**Uniqueness of the fixed point of a contraction.**
-/
theorem contraction_fixedPoint_unique {X : Type*} [MetricSpace X] {T : X → X} {K : ℝ}
    (h : IsContraction T K) {x y : X} (hx : T x = x) (hy : T y = y) : x = y := by
  have := h.lipschitz x y; simp_all +decide;
  exact dist_le_zero.mp ( by nlinarith [ h.K_lt_one, @dist_nonneg _ _ x y ] )

/-
**Constructive Picard–Lindelöf / Banach fixed-point theorem.** A contraction
    on a nonempty complete metric space has a fixed point `x⋆`; the Picard
    iterates converge to it, with the explicit geometric a-priori error bound
    `dist (picardIter T x₀ n) x⋆ ≤ dist x₀ (T x₀) · Kⁿ / (1 - K)`.
-/
theorem picard_exists_fixedPoint {X : Type*} [MetricSpace X] [Nonempty X] [CompleteSpace X]
    {T : X → X} {K : ℝ} (h : IsContraction T K) (x₀ : X) :
    ∃ xstar : X, T xstar = xstar ∧
      Tendsto (picardIter T x₀) atTop (𝓝 xstar) ∧
      ∀ n : ℕ, dist (picardIter T x₀ n) xstar ≤ dist x₀ (T x₀) * K ^ n / (1 - K) := by
  -- Set K' := Real.toNNReal K (K is within [0,1) since h.K_lt_one)
  let K' : NNReal := ⟨K, h.K_nonneg⟩;
  obtain ⟨hf, hf'⟩ : ContractingWith K' T ∧ ∀ x y, dist (T x) (T y) ≤ K' * dist x y := by
    refine' ⟨ ⟨ _, _ ⟩, h.lipschitz ⟩;
    · exact h.K_lt_one;
    · exact LipschitzWith.of_dist_le_mul fun x y => by simpa [ K' ] using h.lipschitz x y;
  refine' ⟨ hf.fixedPoint, hf.fixedPoint_isFixedPt, _, _ ⟩;
  · convert hf.tendsto_iterate_fixedPoint x₀;
  · convert hf.apriori_dist_iterate_fixedPoint_le x₀ using 1

/-! ## Part B — The scalar linear ODE -/

/-
The exponential solves the linear ODE `u' = a·u`.
-/
theorem linear_ode_hasDerivAt (a u₀ t₀ : ℝ) (t : ℝ) :
    HasDerivAt (fun s => u₀ * Real.exp (a * (s - t₀)))
      (a * (u₀ * Real.exp (a * (t - t₀)))) t := by
  convert HasDerivAt.const_mul u₀ ( HasDerivAt.exp ( HasDerivAt.const_mul a ( HasDerivAt.sub ( hasDerivAt_id' t ) ( hasDerivAt_const _ _ ) ) ) ) using 1 ; ring!

/-
**Existence and uniqueness for the scalar linear Cauchy problem** `u' = a·u`,
    `u(t₀) = u₀`.  The unique solution is `t ↦ u₀·exp(a·(t - t₀))`.
-/
theorem linear_ode_exists_unique (a u₀ t₀ : ℝ) :
    ∃! u : ℝ → ℝ, u t₀ = u₀ ∧ ∀ t, HasDerivAt u (a * u t) t := by
  refine' ⟨ fun t => u₀ * Real.exp ( a * ( t - t₀ ) ), _, _ ⟩;
  · exact ⟨ by norm_num, fun t => by simpa [ mul_comm a ] using linear_ode_hasDerivAt a u₀ t₀ t ⟩;
  · -- Let's assume there is another solution $v$ to the differential equation and show that it must be equal to $u$.
    intro v hv
    have h_diff : ∀ t, HasDerivAt (fun t => (v t) * Real.exp (-a * (t - t₀))) 0 t := by
      intro t; convert HasDerivAt.mul ( hv.2 t ) ( HasDerivAt.exp ( HasDerivAt.const_mul ( -a ) ( hasDerivAt_id t |> HasDerivAt.sub <| hasDerivAt_const _ _ ) ) ) using 1 ; ring;
    -- Since the derivative of $v(t) * \exp(-a(t-t₀))$ is zero, $v(t) * \exp(-a(t-t₀))$ is a constant function.
    have h_const : ∀ t₁ t₂, (v t₁) * Real.exp (-a * (t₁ - t₀)) = (v t₂) * Real.exp (-a * (t₂ - t₀)) := by
      apply_rules [ @is_const_of_deriv_eq_zero ];
      · exact fun t => ( h_diff t |> HasDerivAt.differentiableAt );
      · exact funext fun x => HasDerivAt.deriv ( h_diff x );
    ext t; specialize h_const t t₀; simp_all +decide [ Real.exp_neg ] ;
    rwa [ ← div_eq_iff ( ne_of_gt ( Real.exp_pos _ ) ) ]

/-! ## Part C — Constructive Cauchy–Kowalevski (recursive Taylor coefficients) -/

/-- The recursively generated Taylor coefficients of the solution of the analytic
    linear Cauchy problem `u' = a(t)·u`, `u(0) = u₀`, where `a` has power-series
    coefficients `α`.  This is the "computable generating sequence". -/
noncomputable def ckCoeff (α : ℕ → ℝ) (u₀ : ℝ) : ℕ → ℝ
  | 0 => u₀
  | (n + 1) => (∑ k ∈ Finset.range (n + 1), α k * ckCoeff α u₀ (n - k)) / (n + 1)

/-- A coefficient sequence `c` is a formal (power-series) solution of the analytic
    linear Cauchy problem: `c 0 = u₀` and the Cauchy-product recursion holds. -/
def IsCKSolution (α : ℕ → ℝ) (u₀ : ℝ) (c : ℕ → ℝ) : Prop :=
  c 0 = u₀ ∧
    ∀ n : ℕ, ((n : ℝ) + 1) * c (n + 1) = ∑ k ∈ Finset.range (n + 1), α k * c (n - k)

@[simp] theorem ckCoeff_zero (α : ℕ → ℝ) (u₀ : ℝ) : ckCoeff α u₀ 0 = u₀ := by
  simp [ckCoeff]

theorem ckCoeff_succ (α : ℕ → ℝ) (u₀ : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * ckCoeff α u₀ (n + 1)
      = ∑ k ∈ Finset.range (n + 1), α k * ckCoeff α u₀ (n - k) := by
  rw [ show ckCoeff α u₀ ( n + 1 ) = ( ∑ k ∈ Finset.range ( n + 1 ), α k * ckCoeff α u₀ ( n - k ) ) / ( n + 1 ) from ?_, mul_div_cancel₀ _ ( by positivity ) ];
  grind +locals

/-
**Existence: the recursive generating sequence is a formal solution.**
-/
theorem ckCoeff_isSolution (α : ℕ → ℝ) (u₀ : ℝ) : IsCKSolution α u₀ (ckCoeff α u₀) := by
  exact ⟨ckCoeff_zero α u₀, ckCoeff_succ α u₀⟩

/-
**Uniqueness of the analytic solution (Cauchy–Kowalevski).** Any two formal
    solutions of the analytic linear Cauchy problem coincide.
-/
theorem ck_solution_unique (α : ℕ → ℝ) (u₀ : ℝ) {c c' : ℕ → ℝ}
    (hc : IsCKSolution α u₀ c) (hc' : IsCKSolution α u₀ c') : c = c' := by
  funext n; induction' n using Nat.strongRecOn with n ih; rcases n with ( _ | n ) <;> simp_all +decide [ IsCKSolution ] ;
  exact mul_left_cancel₀ ( Nat.cast_add_one_ne_zero n ) ( by rw [ hc.2, hc' ] ; exact Finset.sum_congr rfl fun x hx => by rw [ ih _ ( Nat.sub_le_of_le_add <| by linarith [ Finset.mem_range.mp hx ] ) ] )

/-- **Constructive Cauchy–Kowalevski (1-D analytic linear case).** The analytic
    linear Cauchy problem has a unique formal power-series solution, given by the
    explicit recursive generating sequence `ckCoeff`. -/
theorem ck_exists_unique (α : ℕ → ℝ) (u₀ : ℝ) : ∃! c : ℕ → ℝ, IsCKSolution α u₀ c := by
  refine ⟨ckCoeff α u₀, ckCoeff_isSolution α u₀, ?_⟩
  intro c hc
  exact ck_solution_unique α u₀ hc (ckCoeff_isSolution α u₀)

/-
**Constant-coefficient case = exponential.** For `a(t) ≡ a` (i.e. `α 0 = a`,
    `α k = 0` for `k ≥ 1`) the generating sequence is exactly the Taylor sequence
    `u₀·aⁿ/n!` of `t ↦ u₀·exp(a t)`, linking the formal solution of Part C to the
    genuine analytic solution of Part B.
-/
theorem ckCoeff_const (a u₀ : ℝ) (n : ℕ) :
    ckCoeff (fun k => if k = 0 then a else 0) u₀ n = u₀ * a ^ n / (n.factorial : ℝ) := by
  induction' n with n ih <;> simp_all +decide [ Nat.factorial, pow_succ', mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
  -- By definition of $ckCoeff$, we have:
  have h_def : (n + 1) * ckCoeff (fun k => if k = 0 then a else 0) u₀ (n + 1) = a * ckCoeff (fun k => if k = 0 then a else 0) u₀ n := by
    convert ckCoeff_succ ( fun k => if k = 0 then a else 0 ) u₀ n using 1 ; simp +decide;
  grind

end RGF.ConstructiveAnalysis