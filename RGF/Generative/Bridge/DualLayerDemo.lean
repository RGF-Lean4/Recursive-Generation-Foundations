import Mathlib

/-!
# Example: dual-layer iteration system

This file demonstrates the core dynamical mechanism of RGF: **dual-layer iteration**.

## Concept

The dual-layer system acts on a probability distribution over a finite set of atoms (the rule layer):

1. **Rule layer → entities (Generate):** from the current probability distribution, sample or deterministically
   produce a list of entities.
2. **Entities → rule layer (Modify):** compute a new probability distribution from the generated entities.

The composition `modify ∘ generate` defines a single iteration step.
The fixed points of this iteration correspond to stable mathematical structures.

## This demonstration

We construct a concrete dual-layer system on `Fin 3` (three atoms) and
verify basic properties: normalization, boundedness, and iteration behavior.
-/

open Finset BigOperators

/-! ## Step 1: the rule layer — a probability distribution -/

/-- The rule layer is a probability distribution over a finite type. -/
structure RuleLayerEx (α : Type) [Fintype α] where
  weight : α → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a : α, weight a = 1

/-- Each weight is at most 1 (deduced from nonnegativity and the sum being 1). -/
theorem RuleLayerEx.weight_le_one {α : Type} [Fintype α] (r : RuleLayerEx α) (a : α) :
    r.weight a ≤ 1 := by
  have hle : r.weight a ≤ ∑ b : α, r.weight b :=
    Finset.single_le_sum (fun b _ => r.weight_nonneg b) (Finset.mem_univ a)
  linarith [r.weight_sum]

/-! ## Step 2: a concrete example — the uniform distribution over 3 atoms -/

/-- The uniform distribution over Fin 3: each atom has weight 1/3. -/
noncomputable def uniformLayer3 : RuleLayerEx (Fin 3) where
  weight := fun _ => 1 / 3
  weight_nonneg := by intro _; norm_num
  weight_sum := by simp [Finset.sum_const, nsmul_eq_mul]

/-- Verification: in the uniform distribution every weight is 1/3. -/
example : uniformLayer3.weight 0 = 1 / 3 := rfl
example : uniformLayer3.weight 1 = 1 / 3 := rfl
example : uniformLayer3.weight 2 = 1 / 3 := rfl

/-! ## Step 3: a non-uniform distribution -/

/-- A biased distribution: weights (1/2, 1/3, 1/6). -/
noncomputable def biasedLayer3 : RuleLayerEx (Fin 3) where
  weight := ![1/2, 1/3, 1/6]
  weight_nonneg := by
    intro a; fin_cases a <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  weight_sum := by
    simp [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

/-! ## Step 4: the dual-layer iteration step -/

/-- A simple "averaging" modification step: the new weight is the average of the old weight and the uniform weight 1/n.
    It describes a system tending toward uniformization. -/
noncomputable def averagingStep (n : ℕ) [NeZero n] (r : RuleLayerEx (Fin n)) :
    RuleLayerEx (Fin n) where
  weight := fun a => (r.weight a + 1 / n) / 2
  weight_nonneg := by
    intro a
    have h1 := r.weight_nonneg a
    have h2 : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
    positivity
  weight_sum := by
    have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have h1 : ∀ a : Fin n, (r.weight a + 1 / (n : ℝ)) / 2 =
      r.weight a / 2 + 1 / (2 * n) := by intro a; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.sum_div, r.weight_sum,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have : (n : ℝ) * 1 / (2 * n) = 1 / 2 := by field_simp
    linarith

/-! ## Step 5: iteration converges to the uniform distribution -/

/-- Iterate the averaging step k times. -/
noncomputable def iterateAveraging (n : ℕ) [NeZero n] (r : RuleLayerEx (Fin n)) :
    ℕ → RuleLayerEx (Fin n)
  | 0 => r
  | k + 1 => averagingStep n (iterateAveraging n r k)

/-- After one averaging step on the biased layer, weight 0 moves from 1/2 toward 1/3. -/
noncomputable example : (averagingStep 3 biasedLayer3).weight 0 = 5 / 12 := by
  simp [averagingStep, biasedLayer3, Matrix.cons_val_zero]; ring

/-! ## Key insight

The averaging step is a **contraction map** on the space of probability distributions (with respect to the L∞ metric). By the Banach fixed-point theorem,
the iteration converges to a unique fixed point — the uniform distribution.

This is exactly the mechanism formalized for general RGF dual-layer systems in `Axioms/BanachContraction.lean`.
-/
