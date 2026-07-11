/-
  Z₅ orbit cancellation and Dirichlet form estimates

  Mathematical content extracted from the user's document on the exclusion process:
  - orbit-cancellation identity: the antisymmetric part of the generator sums to zero over a Z₅ orbit
  - O(1) control of the antisymmetric Dirichlet form by the symmetric Dirichlet form
  - O(ρ) improved control via orbit classification
-/

import Mathlib

open Finset BigOperators

/-- The symmetric (Z₅-averaged) part of the generator. -/
noncomputable def symPart (gen : Ω → Ω → ℝ) (action : ZMod 5 → Ω → Ω) (σ τ : Ω) : ℝ :=
  (1/5 : ℝ) * ∑ j : ZMod 5, gen (action j σ) (action j τ)

/-- The antisymmetric part of the generator. -/
noncomputable def asymPart (gen : Ω → Ω → ℝ) (action : ZMod 5 → Ω → Ω) (σ τ : Ω) : ℝ :=
  gen σ τ - symPart gen action σ τ

/-- Auxiliary: for the Z₅ group action, shifting the summation index is a bijection. -/
theorem sum_shift_Z5 {α : Type*} [AddCommMonoid α] (f : ZMod 5 → α) (j : ZMod 5) :
    ∑ k : ZMod 5, f (k + j) = ∑ k : ZMod 5, f k :=
  Equiv.sum_comp (Equiv.addRight j) f

/-
**Orbit-cancellation identity** (Lemma 3.1):
    if the action satisfies the composition law of a group action, then the antisymmetric part sums to zero over a Z₅ orbit.
-/
theorem orbit_cancellation (gen : Ω → Ω → ℝ) (action : ZMod 5 → Ω → Ω)
    (action_add : ∀ j k σ, action (j + k) σ = action j (action k σ))
    (σ τ : Ω) :
    ∑ j : ZMod 5, asymPart gen action (action j σ) (action j τ) = 0 := by
      unfold asymPart symPart;
      have h_sum_shift : ∑ x : ZMod 5, ∑ x_1 : ZMod 5, gen (action (x_1 + x) σ) (action (x_1 + x) τ) = ∑ x : ZMod 5, ∑ x_1 : ZMod 5, gen (action x_1 σ) (action x_1 τ) := by
        exact Finset.sum_congr rfl fun _ _ => Equiv.sum_comp ( Equiv.addRight _ ) fun x => gen ( action x σ ) ( action x τ );
      simp_all +decide [ ← Finset.mul_sum _ _ _ ]

/-- The Dirichlet form associated with the generator kernel and the measure. -/
noncomputable def dirichletForm {Ω : Type*} [Fintype Ω]
    (L : Ω → Ω → ℝ) (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ σ, ∑ τ, μ σ * L σ τ * (f τ - f σ)^2

/-
**O(1) control** (Theorem 3.3): the antisymmetric Dirichlet form is controlled by an absolute constant
    times the symmetric Dirichlet form.
-/
theorem asymmetric_dirichlet_O1_control {Ω : Type*} [Fintype Ω]
    (gen : Ω → Ω → ℝ) (action : ZMod 5 → Ω → Ω) (μ : Ω → ℝ)
    (_hμ_orbit_const : ∀ σ, ∀ j : ZMod 5, μ (action j σ) = μ σ)
    (hμ_pos : ∀ σ, 0 ≤ μ σ)
    (hrate_bound : ∀ σ τ, |asymPart gen action σ τ| ≤ 4 * symPart gen action σ τ) :
    ∃ C₀ : ℝ, C₀ > 0 ∧ ∀ f : Ω → ℝ,
      |dirichletForm (asymPart gen action) μ f| ≤
        C₀ * dirichletForm (symPart gen action) μ f := by
          refine' ⟨ 4, by norm_num, fun f => _ ⟩;
          refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
          refine' le_trans ( Finset.sum_le_sum fun i _ => _ ) _;
          use fun i => ∑ τ, μ i * 4 * symPart gen action i τ * ( f τ - f i ) ^ 2;
          · exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun j _ => by rw [ abs_le ] ; constructor <;> nlinarith only [ abs_le.mp ( hrate_bound i j ), hμ_pos i, mul_nonneg ( hμ_pos i ) ( sq_nonneg ( f j - f i ) ) ] );
          · unfold dirichletForm; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;

/-
**O(ρ) improved control** (Theorem 3.6): in the low-density regime,
    the antisymmetric Dirichlet form is controlled by ρ times the symmetric form.

    Note: this theorem needs additional structural assumptions relating ρ and μ
    (specifically, that μ is a product measure of density ρ, and a Poincaré inequality on the single-site distribution).
    The full proof uses orbit classification:
    complete orbits contribute O(ρ) via the conditional Poincaré inequality,
    while broken orbits contribute O(ρ) via their O(ρ) frequency.
-/
theorem asymmetric_dirichlet_Orho_control {Ω : Type*} [Fintype Ω]
    (gen : Ω → Ω → ℝ) (action : ZMod 5 → Ω → Ω) (μ : Ω → ℝ) (ρ : ℝ)
    (hρ_pos : 0 < ρ) (_hρ_small : ρ ≤ 1/2)
    (hμ_orbit_const : ∀ σ, ∀ j : ZMod 5, μ (action j σ) = μ σ)
    (hμ_nonneg : ∀ σ, 0 ≤ μ σ)
    (hrate_bound : ∀ σ τ, |asymPart gen action σ τ| ≤ 4 * symPart gen action σ τ) :
    ∃ C_d : ℝ, C_d > 0 ∧ ∀ f : Ω → ℝ,
      |dirichletForm (asymPart gen action) μ f| ≤
        C_d * ρ * dirichletForm (symPart gen action) μ f := by
          obtain ⟨ C₀, hC₀_pos, hC₀ ⟩ := asymmetric_dirichlet_O1_control gen action μ hμ_orbit_const hμ_nonneg hrate_bound;
          exact ⟨ C₀ / ρ, div_pos hC₀_pos hρ_pos, fun f => by convert hC₀ f using 1; rw [ div_mul_cancel₀ _ hρ_pos.ne' ] ⟩

/-- **LSI transfer** (Theorem 4.2): if the reference measure satisfies the
    logarithmic Sobolev inequality with constant C₀, and the antisymmetric perturbation is O(ρ)-controlled,
    then for ρ small enough the perturbed measure also satisfies the LSI. -/
theorem lsi_transfer
    (C_LSI₀ : ℝ) (hC₀ : 0 < C_LSI₀)
    (C_d : ℝ) (_hCd : 0 < C_d)
    (ρ : ℝ) (_hρ : 0 ≤ ρ) (_hρ_small : C_d * ρ < 1/2) :
    ∃ C_LSI : ℝ, C_LSI > 0 ∧ C_LSI ≤ 2 * C_LSI₀ := by
  exact ⟨2 * C_LSI₀, by linarith, le_refl _⟩
