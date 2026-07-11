/-
# L2L3OpenItemsDerivation

First-principles derivation and machine proof of the three items previously marked explicitly as
"not yet closed" in the RGF dynamics derivation:

* **Item 1 — the L2 upper bound `n₂ ≤ 2` (frequency count of the antisymmetric generator)**
  - `skew_charpoly_eval_neg` / `skew_charpoly_comp_neg`: the characteristic polynomial of an
    odd-dimensional real antisymmetric matrix (`Mᵀ = -M`) is an odd function `p(-X) = -p(X)` (by
    transpose invariance of `det`, antisymmetry, and `(-1)^n = -1`).
  - `skew_odd_det_zero`: an odd-dimensional antisymmetric matrix has `det = 0`, hence a zero
    eigenvalue (a real chiral axis).
  - `skew5_charpoly_form`: in the 5×5 case the characteristic polynomial necessarily has the form
    `X⁵ + a·X³ + b·X` (the even-degree coefficients vanish).
  - `pos_quartic_roots_le_two` / `pentagon_n2_upper`: the nonzero eigenfrequencies satisfy
    `ω⁴ − a·ω² + b = 0`; setting `u = ω²` reduces to a quadratic equation, so there are at most
    two positive frequencies, i.e. `n₂ ≤ 2`.

* **Item 2 — first-principles derivation of the spectral gap**
  - `rayleigh_shift` / `spectral_gap_emerges`: the dissipation rate `g = γ₀ > 0` (rule G3 cooling)
    plus a negative-semidefinite coupling makes the Rayleigh quotient of the drift matrix
    `Γ = −g·I + S` satisfy `⟨v, Γv⟩ ≤ −g·⟨v, v⟩`, so the spectral gap emerges.
  - `neg_laplacian_neg_semidef`: a "negative graph Laplacian" coupling (symmetric, nonnegative
    off-diagonal, zero row sums) satisfies `⟨v, Bv⟩ = −½ Σ W_{ij}(v_i − v_j)² ≤ 0`.
  - `energy_hasDerivAt` / `energy_exponential_decay`: the energy `E = ⟨x,x⟩` satisfies
    `Ė ≤ −2g·E`, hence `E(t) ≤ E(0)·e^{−2g·t}`.

* **Item 3 — emergence of the dynamical equation itself**
  - `flow_hasDerivAt` / `flow_solves_linear_ode`: the flow `x(t) = exp(tΓ)·x₀` satisfies the
    linear differential equation `ẋ(t) = Γ·x(t)`, `x(0) = x₀`.
  - `generator_infinitesimal`: the generator `Γ = d/dt|₀ exp(tΓ)`.
  - `discrete_continuous_embedding`: the discrete `m`-step map `Pᵐ = exp(Γ)ᵐ = exp(mΓ)`.

Finally `l2l3_open_items_resolved` integrates the three items into a single proposition.
-/
import Mathlib

open Polynomial
open scoped Matrix BigOperators

namespace L2L3OpenItems

noncomputable section

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ## Item 1: the L2 upper bound n₂ ≤ 2 -/

/-
The characteristic polynomial of an odd-dimensional real antisymmetric matrix is an odd function
in the pointwise (evaluation) sense.
-/
theorem skew_charpoly_eval_neg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = -M) (hn : Odd n) (t : ℝ) :
    M.charpoly.eval (-t) = - M.charpoly.eval t := by
  -- Use Matrix.eval_charpoly: Polynomial.eval t M.charpoly = ((Matrix.scalar (Fin n)) t - M).det. So the goal becomes det (scalar (-t) - M) = - det (scalar t - M).
  have h_det : (Matrix.det ((Matrix.scalar (Fin n)) (-t) - M)) = - (Matrix.det ((Matrix.scalar (Fin n)) t - M)) := by
    -- By Matrix.det_neg, det(-(scalar t + M)) = (-1)^(Fintype.card (Fin n)) * det(scalar t + M).
    have h_det_neg : Matrix.det (-(Matrix.scalar (Fin n) t + M)) = (-1 : ℝ) ^ n * Matrix.det (Matrix.scalar (Fin n) t + M) := by
      rw [ ← neg_one_smul ℝ, Matrix.det_smul ] ; aesop;
    convert h_det_neg using 1;
    · congr ; ext i j ; by_cases hi : i = j <;> simp +decide [ hi ];
      ring;
    · rw [ ← Matrix.det_transpose ] ; norm_num [ hM, hn.neg_one_pow ] ;
  convert h_det using 1 <;> rw [ Matrix.eval_charpoly ]

/-
The characteristic polynomial of an odd-dimensional real antisymmetric matrix is an odd
polynomial `p(-X) = -p(X)`.
-/
theorem skew_charpoly_comp_neg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = -M) (hn : Odd n) :
    M.charpoly.comp (-X) = - M.charpoly := by
  refine' Polynomial.funext fun x => _;
  convert skew_charpoly_eval_neg M hM hn x using 1 <;> norm_num [ Polynomial.eval_comp ]

/-
An odd-dimensional antisymmetric matrix has determinant zero (hence a zero eigenvalue).
-/
theorem skew_odd_det_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = -M) (hn : Odd n) : M.det = 0 := by
  apply_fun Matrix.det at hM;
  norm_num [ Matrix.det_neg, hn.neg_one_pow ] at hM ; linarith

/-
An odd monic degree-5 polynomial necessarily has the form `X⁵ + a·X³ + b·X`.
-/
theorem odd_monic_deg5_form (p : ℝ[X]) (hodd : p.comp (-X) = -p)
    (hmon : p.Monic) (hdeg : p.natDegree = 5) :
    ∃ a b : ℝ, p = X ^ 5 + C a * X ^ 3 + C b * X := by
  -- Write $p$ as $p = a_5 X^5 + a_4 X^4 + a_3 X^3 + a_2 X^2 + a_1 X + a_0$ with $a_5 = 1$.
  obtain ⟨a_4, a_3, a_2, a_1, a_0, ha⟩ : ∃ a_4 a_3 a_2 a_1 a_0 : ℝ, p = Polynomial.monomial 5 1 + Polynomial.monomial 4 a_4 + Polynomial.monomial 3 a_3 + Polynomial.monomial 2 a_2 + Polynomial.monomial 1 a_1 + Polynomial.monomial 0 a_0 := by
    rw [ p.as_sum_range ];
    norm_num [ Finset.sum_range_succ', hdeg ];
    have := hmon.coeff_natDegree; aesop;
  subst ha; use a_3, a_1; norm_num [ ← Polynomial.C_mul_X_pow_eq_monomial ] ; ring;
  have eq₁ := congr_arg ( Polynomial.eval ( -2 ) ) hodd; have eq₂ := congr_arg ( Polynomial.eval ( -1 ) ) hodd; have eq₃ := congr_arg ( Polynomial.eval 0 ) hodd; have eq₄ := congr_arg ( Polynomial.eval 1 ) hodd; have eq₅ := congr_arg ( Polynomial.eval 2 ) hodd; norm_num at eq₁ eq₂ eq₃ eq₄ eq₅; exact Polynomial.funext fun x => by norm_num; cases le_or_gt x 0 <;> nlinarith [ sq_nonneg ( x^2 ) ] ;

/-
The characteristic polynomial of a 5×5 real antisymmetric matrix necessarily has the form
`X⁵ + a·X³ + b·X`.
-/
theorem skew5_charpoly_form (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : Mᵀ = -M) :
    ∃ a b : ℝ, M.charpoly = X ^ 5 + C a * X ^ 3 + C b * X := by
  apply odd_monic_deg5_form;
  · exact skew_charpoly_comp_neg M hM ( by decide );
  · exact Matrix.charpoly_monic M;
  · rw [ Matrix.charpoly_natDegree_eq_dim ] ; norm_num

/-
The biquadratic equation `ω⁴ − a·ω² + b = 0` has at most two positive roots: among any three
positive roots, two must coincide.
-/
theorem pos_quartic_roots_le_two (a b : ℝ) {ω₁ ω₂ ω₃ : ℝ}
    (h1 : 0 < ω₁) (h2 : 0 < ω₂) (h3 : 0 < ω₃)
    (e1 : ω₁ ^ 4 - a * ω₁ ^ 2 + b = 0) (e2 : ω₂ ^ 4 - a * ω₂ ^ 2 + b = 0)
    (e3 : ω₃ ^ 4 - a * ω₃ ^ 2 + b = 0) :
    ω₁ = ω₂ ∨ ω₁ = ω₃ ∨ ω₂ = ω₃ := by
  by_contra h;
  -- Since $ω₁$, $ω₂$, and $ω₃$ are distinct positive roots, we can write $ω₁^2 = u₁$, $ω₂^2 = u₂$, and $ω₃^2 = u₃$ for some distinct positive $u₁$, $u₂$, and $u₃$.
  set u₁ := ω₁^2
  set u₂ := ω₂^2
  set u₃ := ω₃^2
  have hu₁ : u₁ > 0 := by
    positivity
  have hu₂ : u₂ > 0 := by
    positivity
  have hu₃ : u₃ > 0 := by
    positivity
  have hu_distinct : u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ := by
    exact ⟨ fun h => h |> fun h => h1.ne' <| mul_left_cancel₀ ( sub_ne_zero_of_ne <| by tauto : ( ω₁ - ω₂ ) ≠ 0 ) <| by nlinarith, fun h => h |> fun h => h1.ne' <| mul_left_cancel₀ ( sub_ne_zero_of_ne <| by tauto : ( ω₁ - ω₃ ) ≠ 0 ) <| by nlinarith, fun h => h |> fun h => h2.ne' <| mul_left_cancel₀ ( sub_ne_zero_of_ne <| by tauto : ( ω₂ - ω₃ ) ≠ 0 ) <| by nlinarith ⟩;
  grind

/-
L2 upper bound: the set of positive frequencies satisfying the biquadratic equation has at most
two elements, i.e. `n₂ ≤ 2`.
-/
theorem pentagon_n2_upper (a b : ℝ) (S : Finset ℝ)
    (hS : ∀ ω ∈ S, 0 < ω ∧ ω ^ 4 - a * ω ^ 2 + b = 0) : S.card ≤ 2 := by
  -- Let $ω₁$, $ω₂$, and $ω₃$ be three distinct positive roots of the quartic equation.
  by_cases h_card : S.card ≥ 3
  obtain ⟨ω₁, ω₂, ω₃, hω₁, hω₂, hω₃, h_distinct⟩ : ∃ ω₁ ω₂ ω₃ : ℝ, ω₁ ∈ S ∧ ω₂ ∈ S ∧ ω₃ ∈ S ∧ ω₁ ≠ ω₂ ∧ ω₁ ≠ ω₃ ∧ ω₂ ≠ ω₃ := by
    rcases Finset.two_lt_card.1 h_card with ⟨ ω₁, hω₁, ω₂, hω₂, hne ⟩ ; use ω₁, ω₂ ; aesop;
  · have := pos_quartic_roots_le_two a b ( hS ω₁ hω₁ |>.1 ) ( hS ω₂ hω₂ |>.1 ) ( hS ω₃ hω₃ |>.1 ) ( hS ω₁ hω₁ |>.2 ) ( hS ω₂ hω₂ |>.2 ) ( hS ω₃ hω₃ |>.2 ) ; aesop;
  · linarith

/-! ## Item 2: first-principles derivation of the spectral gap -/

/-- The quadratic form `⟨v, A v⟩ = ∑ᵢ vᵢ (A v)ᵢ`. -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, v i * (Matrix.mulVec A v) i

/-
Rayleigh shift: a negative-semidefinite coupling `S` plus dissipation `−g·I` makes the Rayleigh
quotient bounded by `−g·‖v‖²`.
-/
theorem rayleigh_shift {n : ℕ} (g : ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ v, quadForm S v ≤ 0) (v : Fin n → ℝ) :
    quadForm (-(g • (1 : Matrix (Fin n) (Fin n) ℝ)) + S) v ≤ -g * ∑ i, (v i) ^ 2 := by
  unfold quadForm; simp +decide [ Finset.mul_sum _ _ _, pow_two ] ;
  simp_all +decide [ Matrix.add_mulVec, Matrix.smul_eq_diagonal_mul ];
  simpa [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ] using hS v

/-
Spectral gap emerges: the drift matrix `Γ = −g·I + S` (`g > 0`, `S` negative-semidefinite) has a
positive spectral gap `g`.
-/
theorem spectral_gap_emerges {n : ℕ} (g : ℝ) (hg : 0 < g)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : ∀ v, quadForm S v ≤ 0) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ v, quadForm (-(g • (1 : Matrix (Fin n) (Fin n) ℝ)) + S) v ≤ -gap * ∑ i, (v i) ^ 2 := by
  exact ⟨ g, hg, fun v => rayleigh_shift g S hS v ⟩

/-
A "negative graph Laplacian" (symmetric, nonnegative off-diagonal, zero row sums) is
negative-semidefinite.
-/
theorem neg_laplacian_neg_semidef {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hsym : Bᵀ = B) (hrow : ∀ i, ∑ j, B i j = 0)
    (hoff : ∀ i j, i ≠ j → 0 ≤ B i j) (v : Fin n → ℝ) :
    quadForm B v ≤ 0 := by
  -- By expanding the sum, we can rewrite it as $-\frac{1}{2} \sum_{i,j} B_{ij} (v_i - v_j)^2$.
  have h_expand : ∑ i, v i * (∑ j, B i j * v j) = -(1 / 2) * ∑ i, ∑ j, B i j * (v i - v j) ^ 2 := by
    simp +decide only [sub_sq, mul_comm, mul_left_comm, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib];
    simp +decide [ ← mul_assoc, ← Finset.sum_mul, ← Finset.sum_comm, hrow ] ; ring;
    simp_all +decide [ mul_comm, ← Matrix.ext_iff ];
  -- Since $B$ is symmetric and has non-negative off-diagonal entries, the sum $\sum_{i,j} B_{ij} (v_i - v_j)^2$ is non-negative.
  have h_nonneg : 0 ≤ ∑ i, ∑ j, B i j * (v i - v j) ^ 2 := by
    refine' Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => _;
    by_cases hij : i = j <;> [ simp +decide [ * ] ; exact mul_nonneg ( hoff i j hij ) ( sq_nonneg _ ) ];
  convert h_expand.le.trans ( mul_nonpos_of_nonpos_of_nonneg ( by norm_num ) h_nonneg ) using 1

/-
The derivative of the energy `E(t) = ∑ᵢ xᵢ(t)²` is `2⟨x, ẋ⟩`, where `ẋ = Γ x`.
-/
theorem energy_hasDerivAt {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ → Fin n → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) ((Matrix.mulVec Γ (x t)) i) t) :
    HasDerivAt (fun s => ∑ i, (x s i) ^ 2)
      (2 * ∑ i, (x t i) * (Matrix.mulVec Γ (x t)) i) t := by
  convert HasDerivAt.sum fun i _ => ( hx i ).mul ( hx i ) using 1;
  rotate_right;
  exacts [ Finset.univ, by ext; simp +decide [ sq ], by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring ]

/-
Exponential energy decay: `Ė ≤ −2g·E` implies `E(t) ≤ E(0)·e^{−2g·t}`.
(`hg : 0 < g` corresponds to the physically positive dissipation rate and is kept on request;
the inequality itself does not depend on this assumption.)
-/
theorem energy_exponential_decay (g : ℝ) (_hg : 0 < g) (E : ℝ → ℝ)
    (hE : Differentiable ℝ E) (hbd : ∀ t, deriv E t ≤ -2 * g * E t) :
    ∀ t, 0 ≤ t → E t ≤ E 0 * Real.exp (-2 * g * t) := by
  -- Define F t = E t * Real.exp (2*g*t). Show F is antitone.
  set F : ℝ → ℝ := fun t => E t * Real.exp (2 * g * t)
  have hF_antitone : Antitone F := by
    apply_rules [ antitone_of_deriv_nonpos ];
    · fun_prop;
    · intro t; norm_num [ F, hE.differentiableAt, mul_comm ] ; nlinarith [ hbd t, Real.exp_pos ( t * ( g * 2 ) ) ] ;
  intro t ht; have := hF_antitone ht; simp_all +decide [ Real.exp_neg ] ;
  rw [ ← div_eq_mul_inv, le_div_iff₀ ( Real.exp_pos _ ) ] ; aesop

/-! ## Item 3: emergence of the dynamical equation itself -/

/-- The derivative of the flow `Φ(t) = exp(tΓ)` is `Φ(t)·Γ`. -/
theorem flow_hasDerivAt {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Γ))
      (NormedSpace.exp (t • Γ) * Γ) t :=
  hasDerivAt_exp_smul_const Γ t

/-
Initial condition: `exp(0·Γ) = I`.
-/
theorem flow_zero {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) :
    NormedSpace.exp ((0 : ℝ) • Γ) = 1 := by
  simp +decide [ NormedSpace.exp_zero ]

/-
The flow `Φ(t) = exp(tΓ)` satisfies the linear differential equation `Φ̇ = Γ·Φ`.
-/
theorem flow_solves_linear_ode {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Γ))
      (Γ * NormedSpace.exp (t • Γ)) t := by
  have := @flow_hasDerivAt n Γ t;
  convert this using 1;
  have h_comm : Commute Γ (NormedSpace.exp (t • Γ)) := by
    convert Commute.exp_right ( Commute.smul_right ( Commute.refl Γ ) t ) using 1;
  exact h_comm.eq

/-
The generator is the infinitesimal of the flow at the origin: `Γ = d/dt|₀ exp(tΓ)`.
-/
theorem generator_infinitesimal {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Γ)) Γ 0 := by
  convert flow_hasDerivAt Γ 0 using 1 ; norm_num [ flow_zero ]

/-
Discrete–continuous embedding: the discrete `m`-step map `(exp Γ)ᵐ = exp(mΓ)`.
-/
theorem discrete_continuous_embedding {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    NormedSpace.exp ((m : ℝ) • Γ) = (NormedSpace.exp Γ) ^ m := by
  rw [ ← Matrix.exp_nsmul ];
  norm_cast

/-! ## Integration -/

/-- Integrated resolution of the three previously "not yet closed" problems. -/
theorem l2l3_open_items_resolved :
    -- Item 1: odd-dimensional antisymmetric det = 0, the 5-dimensional characteristic polynomial form, the L2 upper bound
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ), Mᵀ = -M → Odd n → M.det = 0) ∧
    (∀ (M : Matrix (Fin 5) (Fin 5) ℝ), Mᵀ = -M →
      ∃ a b : ℝ, M.charpoly = X ^ 5 + C a * X ^ 3 + C b * X) ∧
    (∀ (a b : ℝ) (S : Finset ℝ),
      (∀ ω ∈ S, 0 < ω ∧ ω ^ 4 - a * ω ^ 2 + b = 0) → S.card ≤ 2) ∧
    -- Item 2: spectral gap emerges, the negative Laplacian is negative-semidefinite, exponential energy decay
    (∀ (n : ℕ) (g : ℝ), 0 < g → ∀ (S : Matrix (Fin n) (Fin n) ℝ),
      (∀ v, quadForm S v ≤ 0) → ∃ gap : ℝ, 0 < gap ∧
        ∀ v, quadForm (-(g • (1 : Matrix (Fin n) (Fin n) ℝ)) + S) v ≤ -gap * ∑ i, (v i) ^ 2) ∧
    (∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ), Bᵀ = B → (∀ i, ∑ j, B i j = 0) →
      (∀ i j, i ≠ j → 0 ≤ B i j) → ∀ v, quadForm B v ≤ 0) ∧
    (∀ (g : ℝ), 0 < g → ∀ (E : ℝ → ℝ), Differentiable ℝ E →
      (∀ t, deriv E t ≤ -2 * g * E t) → ∀ t, 0 ≤ t → E t ≤ E 0 * Real.exp (-2 * g * t)) ∧
    -- Item 3: linear ODE emerges, the generator infinitesimal, discrete–continuous embedding
    (∀ (n : ℕ) (Γ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Γ)) (Γ * NormedSpace.exp (t • Γ)) t) ∧
    (∀ (n : ℕ) (Γ : Matrix (Fin n) (Fin n) ℝ),
      HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Γ)) Γ 0) ∧
    (∀ (n : ℕ) (Γ : Matrix (Fin n) (Fin n) ℝ) (m : ℕ),
      NormedSpace.exp ((m : ℝ) • Γ) = (NormedSpace.exp Γ) ^ m) := by
  refine ⟨fun n M h o => skew_odd_det_zero M h o, fun M h => skew5_charpoly_form M h,
    fun a b S hS => pentagon_n2_upper a b S hS,
    fun n g hg S hS => spectral_gap_emerges g hg S hS,
    fun n B hsym hrow hoff v => neg_laplacian_neg_semidef B hsym hrow hoff v,
    fun g hg E hE hbd => energy_exponential_decay g hg E hE hbd,
    fun n Γ t => flow_solves_linear_ode Γ t,
    fun n Γ => generator_infinitesimal Γ,
    fun n Γ m => discrete_continuous_embedding Γ m⟩

end

end L2L3OpenItems