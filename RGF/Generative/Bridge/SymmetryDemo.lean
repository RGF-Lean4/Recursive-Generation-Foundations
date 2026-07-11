import Mathlib

/-!
# Example: symmetry in the rule layer

This file demonstrates how symmetry manifests in the RGF rule layer, and
why the symmetry factor plays a central role in this framework.

## Key ideas

1. A **symmetry** of the rule layer is a permutation of atoms that preserves the weights.
2. The **symmetry group** of the rule layer determines its structural complexity.
3. The uniform distribution has maximal symmetry (the full symmetry group).
4. RGF foundational theory studies how symmetry is preserved or broken under iteration.
-/

open Finset BigOperators Equiv

/-! ## Step 1: symmetry of a probability distribution -/

/-- A probability distribution over a finite type. -/
structure ProbDistEx (α : Type) [Fintype α] where
  weight : α → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a : α, weight a = 1

/-- A permutation σ is a symmetry of a distribution d if it preserves all weights. -/
def IsSymmetryEx {α : Type} [Fintype α]
    (d : ProbDistEx α) (σ : Perm α) : Prop :=
  ∀ a, d.weight (σ a) = d.weight a

/-! ## Step 2: the uniform distribution has full symmetry -/

/-- The uniform distribution over Fin n. -/
noncomputable def uniformDistEx (n : ℕ) [NeZero n] : ProbDistEx (Fin n) where
  weight := fun _ => 1 / n
  weight_nonneg := by intro _; positivity
  weight_sum := by simp [Finset.sum_const, nsmul_eq_mul]

/-- Every permutation is a symmetry of the uniform distribution. -/
theorem uniform_full_symmetry_ex (n : ℕ) [NeZero n] (σ : Perm (Fin n)) :
    IsSymmetryEx (uniformDistEx n) σ := by
  intro a; simp [uniformDistEx]

/-! ## Step 3: non-uniform distributions have fewer symmetries -/

/-- The distribution (1/2, 1/2, 0) over Fin 3. -/
noncomputable def halfHalfZeroEx : ProbDistEx (Fin 3) where
  weight := ![1/2, 1/2, 0]
  weight_nonneg := by
    intro a; fin_cases a <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  weight_sum := by
    simp [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

/-- The transposition (0 ↔ 1) is a symmetry of (1/2, 1/2, 0). -/
theorem swap01_is_symmetry_ex :
    IsSymmetryEx halfHalfZeroEx (Equiv.swap (0 : Fin 3) 1) := by
  intro a
  unfold halfHalfZeroEx; simp only
  fin_cases a <;> simp [swap_apply_left, swap_apply_right,
    show (swap (0 : Fin 3) 1) 2 = 2 from by decide,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## Step 4: the symmetry factor -/

/-- The symmetry factor |Sym(d)| / |S_n| measures "how symmetric" a distribution is.
    - value 1: maximal symmetry (the uniform distribution)
    - value 1/n!: minimal symmetry (all weights distinct) -/
noncomputable def symmetryFactorEx {α : Type} [Fintype α] [DecidableEq α]
    (d : ProbDistEx α) : ℝ :=
  (Finset.univ.filter (fun σ : Perm α => ∀ a, d.weight (σ a) = d.weight a)).card /
  (Fintype.card (Perm α) : ℝ)

/-- The symmetry factor is always at most 1. -/
theorem symmetryFactor_le_one_ex {α : Type} [Fintype α] [DecidableEq α]
    (d : ProbDistEx α) : symmetryFactorEx d ≤ 1 := by
  unfold symmetryFactorEx
  have hpos : (0 : ℝ) < Fintype.card (Perm α) := by exact_mod_cast Fintype.card_pos (α := Perm α)
  rw [div_le_one hpos]
  exact_mod_cast Finset.card_filter_le _ _

/-! ## Key insight

In RGF foundational theory, **symmetry is not merely a static property** — it evolves under dual-layer iteration.
The locking-membrane theorem shows that exactly at k=5 the symmetric structure is rich enough (S₅ unsolvable, D₅ has
the right representation theory) to support stable emergence, while being small enough to avoid over-constraint.

See the complete symmetry-factor theory in `Axioms/Properties.lean`, and how equivariant systems
preserve symmetry in `Invariants/Theorems.lean`.
-/
