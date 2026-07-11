/-
  Category/ForgetfulFunctor.lean — the forgetful functor and the free RGF construction
  Forgetful Functor and Free RGF Construction

  Defines the forgetful functor U : RGF → Type (taking the underlying permutation group) and its free RGF construction.
-/

import Mathlib
import RGF.Math.Category.RGF_Category

open CategoryTheory Equiv Function

noncomputable section

/-! ============================================================
    Part 1: the forgetful functor (to permutation groups)
    ============================================================ -/

/-- The forgetful functor: takes the underlying permutation group Perm(Fin n) of an RGF system. -/
def RGF_forget : RGFObject ⥤ Type where
  obj := fun X => Perm (Fin X.n)
  map := fun f => f.f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-! ============================================================
    Part 2: the free RGF construction
    ============================================================ -/

/-- The trivial equivariant system: step = id. -/
def trivialEquivariantSystem (n : ℕ) : RGFState.EquivariantSystem n where
  step := _root_.id
  equivariant := fun _ _ => rfl

/-- The free RGF construction: for a vertex count n, generates the trivial equivariant system. -/
def freeRGF (n : ℕ) : RGFObject where
  n := n
  sys := trivialEquivariantSystem n

/-! ============================================================
    Part 3: basic properties of the forgetful functor
    ============================================================ -/

/-- The forgetful functor preserves the identity morphism. -/
theorem forget_map_id (X : RGFObject) :
    RGF_forget.map (𝟙 X) = _root_.id := rfl

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {X Y Z : RGFObject} (f : X ⟶ Y) (g : Y ⟶ Z) :
    RGF_forget.map (f ≫ g) = g.f ∘ f.f := rfl

/-- The vertex count of the free construction. -/
theorem freeRGF_vertexCount (n : ℕ) : (freeRGF n).n = n := rfl

/-- The free construction uses trivial dynamics. -/
theorem freeRGF_step_id (n : ℕ) (s : RGFState n) :
    (freeRGF n).sys.step s = s := rfl

end
