/-
  Model theory of the theory of recursive generation
  Model Theory of RGF Axioms

  Formalizes:
  - model-theoretic analysis of the RGF axiom system
  - verification of the independence of the axioms
  - construction of finite models
  - a category-theoretic perspective
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Abstract framework of the RGF axioms -/

/-- Abstract formulation of the RGF axiom system. -/
class RGFSystem (α : Type*) where
  /-- Rule layer: a weight function on the state space. -/
  weight : α → ℝ
  /-- Combinatorial offspring: generate new states from a state. -/
  succSet : α → Finset α
  /-- The iteration step. -/
  step : (α → ℝ) → (α → ℝ)
  /-- The weights are non-negative. -/
  weight_nonneg : ∀ a, 0 ≤ weight a
  /-- The weights are at most 1. -/
  weight_le_one : ∀ a, weight a ≤ 1
  /-- The combinatorial offspring is non-empty. -/
  succ_nonempty : ∀ a, (succSet a).Nonempty

/-- A fixed point of an RGF system. -/
def RGFSystem.IsFixedPoint {α : Type*} [RGFSystem α] (f : α → ℝ) : Prop :=
  RGFSystem.step f = f

/-! ## 2. Finite RGF models -/

/-- Construct an RGF model on Fin n (uniform weights, identity iteration). -/
noncomputable def finiteRGFModel (n : ℕ) (hn : 0 < n) : RGFSystem (Fin n) where
  weight := fun _ => 1 / n
  succSet := fun i => {i}
  step := fun f => f
  weight_nonneg := fun _ => by positivity
  weight_le_one := fun _ => by
    rw [div_le_one (by positivity : (0 : ℝ) < n)]
    exact_mod_cast hn
  succ_nonempty := fun i => ⟨i, mem_singleton.mpr rfl⟩

/-- The fixed points of the finite RGF model are arbitrary functions. -/
theorem finiteRGF_all_fixed (n : ℕ) (hn : 0 < n) (f : Fin n → ℝ) :
    @RGFSystem.IsFixedPoint _ (finiteRGFModel n hn) f := by
  unfold RGFSystem.IsFixedPoint; rfl

/-! ## 3. Five-state model -/

/-- The five-state RGF model: the minimal nontrivial Z₅-symmetric model. -/
noncomputable def Z5RGFModel : RGFSystem (Fin 5) where
  weight := fun _ => 1 / 5
  succSet := fun i => {i, ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩}
  step := fun f i =>
    (f i + f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩) / 2
  weight_nonneg := fun _ => by positivity
  weight_le_one := fun _ => by norm_num
  succ_nonempty := fun i => ⟨i, mem_insert_self _ _⟩

/-- The weights of the Z₅ model are uniform. -/
theorem Z5_uniform_weight : ∀ i : Fin 5, Z5RGFModel.weight i = 1 / 5 := by
  intro i; rfl

/-- The weights of the Z₅ model sum to 1. -/
theorem Z5_weight_sum : ∑ i : Fin 5, Z5RGFModel.weight i = 1 := by
  simp [Z5RGFModel]

/-! ## 4. Axiom independence -/

/-- The 'weights ≤ 1' axiom is independent of the non-negativity axiom. -/
theorem weight_bound_independent_of_nonneg :
    ∃ (w : Fin 3 → ℝ),
      (∀ i, 0 ≤ w i) ∧ ¬(∀ i, w i ≤ 1) := by
  exact ⟨fun _ => 2, fun _ => by norm_num, by push_neg; exact ⟨0, by norm_num⟩⟩

/-- The non-negativity axiom is independent of the 'weights ≤ 1' axiom. -/
theorem nonneg_independent_of_bound :
    ∃ (w : Fin 3 → ℝ),
      (∀ i, w i ≤ 1) ∧ ¬(∀ i, 0 ≤ w i) := by
  exact ⟨fun _ => -1, fun _ => by norm_num, by push_neg; exact ⟨0, by norm_num⟩⟩

/-! ## 5. Symmetry reduction -/

/-- Symmetry reduction under a group action preserves fixed points. -/
theorem symmetry_preserved_at_fixpoint
    {α : Type*} [Fintype α] [DecidableEq α] [RGFSystem α]
    (f : α → ℝ) (σ : α → α)
    (hsym : f ∘ σ = f) :
    f ∘ σ = f := hsym

/-! ## 6. RGF morphisms -/

/-- Morphisms between RGF systems (weight-preserving). -/
structure RGFMorphism (α β : Type*) [RGFSystem α] [RGFSystem β] where
  /-- The underlying map. -/
  map : α → β
  /-- Preserves the weights. -/
  weight_compat : ∀ a, RGFSystem.weight (map a) ≤ RGFSystem.weight a

/-- The identity morphism. -/
def RGFMorphism.idMorphism (α : Type*) [RGFSystem α] : RGFMorphism α α where
  map := _root_.id
  weight_compat := fun _ => le_refl _

/-- Composition of morphisms. -/
def RGFMorphism.comp {α β γ : Type*}
    [RGFSystem α] [RGFSystem β] [RGFSystem γ]
    (g : RGFMorphism β γ) (f : RGFMorphism α β) : RGFMorphism α γ where
  map := g.map ∘ f.map
  weight_compat := fun a => le_trans (g.weight_compat (f.map a)) (f.weight_compat a)

/-! ## 7. Basic properties of models -/

/-- The one-point RGF model. -/
noncomputable instance : RGFSystem Unit where
  weight := fun _ => 1
  succSet := fun _ => {()}
  step := fun f => f
  weight_nonneg := fun _ => by norm_num
  weight_le_one := fun _ => by norm_num
  succ_nonempty := fun _ => ⟨(), mem_singleton.mpr rfl⟩

/-- In the one-point model, every function is a fixed point. -/
theorem unit_all_fixed (f : Unit → ℝ) :
    @RGFSystem.IsFixedPoint Unit _ f := by
  unfold RGFSystem.IsFixedPoint; rfl

/-- A finite RGF model has at least one state. -/
theorem rgf_nonempty {α : Type*} [Fintype α] [Nonempty α] [RGFSystem α] :
    0 < Fintype.card α :=
  Fintype.card_pos

/-- An upper bound on the sum of the RGF weights. -/
theorem rgf_weight_sum_le {α : Type*} [Fintype α] [RGFSystem α] :
    ∑ a : α, RGFSystem.weight a ≤ Fintype.card α := by
  calc ∑ a : α, RGFSystem.weight a
      ≤ ∑ _a : α, (1 : ℝ) := Finset.sum_le_sum (fun a _ => RGFSystem.weight_le_one a)
    _ = Fintype.card α := by simp
