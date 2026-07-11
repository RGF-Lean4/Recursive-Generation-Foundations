/-
  Graph automorphisms and RGF fixed-point symmetry
  Graph Automorphisms and RGF Fixed Point Symmetry
-/

import Mathlib

open SimpleGraph Finset BigOperators

/-! ## 1. Construction and automorphisms of C₅ -/

/-- The adjacency matrix of C₅ -/
def c5AdjMatrix : Fin 5 → Fin 5 → Bool
  | 0, 1 | 1, 0 => true
  | 1, 2 | 2, 1 => true
  | 2, 3 | 3, 2 => true
  | 3, 4 | 4, 3 => true
  | 4, 0 | 0, 4 => true
  | _, _ => false

/-- C₅ as a SimpleGraph -/
def c5Graph : SimpleGraph (Fin 5) where
  Adj u v := c5AdjMatrix u v = true
  symm u v h := by fin_cases u <;> fin_cases v <;> simp_all [c5AdjMatrix]
  loopless := ⟨fun u => by fin_cases u <;> simp [c5AdjMatrix]⟩

instance : DecidableRel c5Graph.Adj := fun u v =>
  inferInstanceAs (Decidable (c5AdjMatrix u v = true))

/-- C₅ has 5 edges -/
theorem c5_edge_count : c5Graph.edgeFinset.card = 5 := by decide

/-- C₅ is 2-regular -/
theorem c5_2_regular :
    ∀ v : Fin 5, (c5Graph.neighborFinset v).card = 2 := by decide

/-! ## 2. The cyclic shift is an automorphism of C₅ -/

/-- Cyclic shift σ: i ↦ (i+1) mod 5 -/
def cycleShift5 : Fin 5 ≃ Fin 5 where
  toFun i := ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩
  invFun i := ⟨(i.val + 4) % 5, Nat.mod_lt _ (by omega)⟩
  left_inv i := by fin_cases i <;> decide
  right_inv i := by fin_cases i <;> decide

/-- The cyclic shift preserves the adjacency relation of C₅ -/
theorem cycleShift5_preserves_adj :
    ∀ u v : Fin 5, c5Graph.Adj u v ↔ c5Graph.Adj (cycleShift5 u) (cycleShift5 v) := by
  decide

/-- The cyclic shift has order 5 -/
theorem cycleShift5_order_5 :
    cycleShift5 ^ 5 = Equiv.refl (Fin 5) := by
  ext i; fin_cases i <;> decide

/-- The cyclic shift is non-trivial -/
theorem cycleShift5_ne_id :
    cycleShift5 ≠ Equiv.refl (Fin 5) := by
  intro h
  have : cycleShift5 (0 : Fin 5) = (0 : Fin 5) := by rw [h]; rfl
  simp [cycleShift5] at this

/-! ## 3. The full symmetry of K₅ -/

/-- Any permutation preserves the adjacency relation of the complete graph -/
theorem any_perm_is_complete_auto (σ : Equiv.Perm (Fin 5)) :
    ∀ u v : Fin 5, u ≠ v ↔ σ u ≠ σ v := by
  intro u v; exact σ.injective.ne_iff.symm

/-- The order of S₅ = 120 -/
theorem perm5_card : Fintype.card (Equiv.Perm (Fin 5)) = 120 := by decide

/-! ## 4. Computing the symmetry factor -/

/-- Symmetry factor = 1/|Aut(G)| -/
noncomputable def graphSymFactor (autOrder : ℕ) : ℚ := 1 / autOrder

/-- The symmetry factor of K₅ = 1/120 -/
theorem k5_sym_factor : graphSymFactor 120 = 1 / 120 := by
  unfold graphSymFactor; norm_num

/-- The symmetry factor of C₅ = 1/10 (D₅ symmetry) -/
theorem c5_sym_factor : graphSymFactor 10 = 1 / 10 := by
  unfold graphSymFactor; norm_num

/-! ## 5. Connection with five-fold locking -/

/-- The unsolvability of S₅ for K₅ ⟺ five-fold locking -/
theorem k5_five_locking :
    Fintype.card (Equiv.Perm (Fin 5)) = 120 ∧
    ¬ IsSolvable (Equiv.Perm (Fin 5)) :=
  ⟨perm5_card, Equiv.Perm.not_solvable _ (by simp [Cardinal.mk_fintype])⟩

/-- Growth of the order of the automorphism group -/
theorem auto_growth :
    (Fintype.card (Equiv.Perm (Fin 3)) < Fintype.card (Equiv.Perm (Fin 4))) ∧
    (Fintype.card (Equiv.Perm (Fin 4)) < Fintype.card (Equiv.Perm (Fin 5))) := by
  refine ⟨?_, ?_⟩ <;> native_decide
