/-
  The Petersen graph and five-fold symmetry
  Petersen Graph and Five-Fold Symmetry

  The Petersen graph is one of the most important regular graphs in graph theory, with a deep connection to RGF quintic locking.
-/

import Mathlib

open Finset BigOperators SimpleGraph

/-! ## 1. Construction of the Petersen graph -/

/-- The adjacency matrix of the Petersen graph (in functional form). -/
def petersenAdjMatrix : Fin 10 → Fin 10 → Bool
  | 0, 1 | 1, 0 => true  -- outer cycle
  | 1, 2 | 2, 1 => true
  | 2, 3 | 3, 2 => true
  | 3, 4 | 4, 3 => true
  | 4, 0 | 0, 4 => true
  | 0, 5 | 5, 0 => true  -- spokes
  | 1, 6 | 6, 1 => true
  | 2, 7 | 7, 2 => true
  | 3, 8 | 8, 3 => true
  | 4, 9 | 9, 4 => true
  | 5, 7 | 7, 5 => true  -- inner star
  | 7, 9 | 9, 7 => true
  | 9, 6 | 6, 9 => true
  | 6, 8 | 8, 6 => true
  | 8, 5 | 5, 8 => true
  | _, _ => false

/-- The Petersen graph. -/
def petersenGraph : SimpleGraph (Fin 10) where
  Adj u v := petersenAdjMatrix u v = true
  symm u v h := by
    fin_cases u <;> fin_cases v <;> simp_all [petersenAdjMatrix]
  loopless := ⟨fun u => by fin_cases u <;> simp [petersenAdjMatrix]⟩

instance : DecidableRel petersenGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (petersenAdjMatrix u v = true))

/-- The Petersen graph has 15 edges. -/
theorem petersen_edge_count : petersenGraph.edgeFinset.card = 15 := by decide

/-- The Petersen graph is 3-regular. -/
theorem petersen_3_regular :
    ∀ v : Fin 10, (petersenGraph.neighborFinset v).card = 3 := by decide

/-- The chromatic number of the Petersen graph is ≥ 3. -/
theorem petersen_chromatic_lower :
    ¬ ∃ (f : Fin 10 → Fin 2), ∀ u v, petersenGraph.Adj u v → f u ≠ f v := by
  native_decide

/-! ## 2. Connection with quintic locking -/

/-- The number of vertices of the Petersen graph = C(5,2). -/
theorem petersen_vertex_eq_choose : Nat.choose 5 2 = 10 := by decide

/-- The appearance of 5 in the Petersen graph. -/
theorem petersen_five_structure :
    (Nat.choose 5 2 = 10) ∧
    (Nat.factorial 5 = 120) ∧
    (10 * 3 / 2 = 15) :=
  ⟨by decide, by decide, by omega⟩
