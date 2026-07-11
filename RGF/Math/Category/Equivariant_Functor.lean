/-
  Category/Equivariant_Functor.lean — group actions and the functoriality of equivariant systems
  Group Action and Equivariant System Functoriality

  Viewing group actions as functors, we exhibit the category-theoretic meaning of the equivariance condition.
-/

import Mathlib
import RGF.Math.Category.RGF_Category

open CategoryTheory Equiv Function

noncomputable section

/-! ============================================================
    Part 1: from permutation groups to endomorphisms in the RGF category
    ============================================================ -/

/-- For a fixed RGF object X, the permutation group Perm(Fin X.n) embeds into the endomorphisms of X.
    Each permutation σ gives an endomorphism (left multiplication by σ). -/
def permToEndomorphism (X : RGFObject) (σ : Perm (Fin X.n)) : X ⟶ X :=
  ⟨fun τ => σ * τ⟩

/-- permToEndomorphism preserves the identity. -/
theorem permToEnd_one (X : RGFObject) :
    permToEndomorphism X 1 = 𝟙 X := by
  apply RGFMorphism.ext; ext; simp [permToEndomorphism]

/-- permToEndomorphism preserves multiplication (reversing order: σ ∘ τ ↦ τ * σ). -/
theorem permToEnd_mul (X : RGFObject) (σ τ : Perm (Fin X.n)) :
    permToEndomorphism X σ ≫ permToEndomorphism X τ = permToEndomorphism X (τ * σ) := by
  apply RGFMorphism.ext; ext ρ
  simp [permToEndomorphism, mul_assoc]

/-! ============================================================
    Part 2: category-theoretic formulation of equivariance
    ============================================================ -/

/-- Category-theoretic restatement of the equivariance condition:
    the step function commutes with all symmetry endomorphisms. -/
def IsEquivariantCategorical (X : RGFObject) : Prop :=
  ∀ σ : Perm (Fin X.n), ∀ s : RGFState X.n,
    X.sys.step (RGFState.permAction σ s) = RGFState.permAction σ (X.sys.step s)

/-- The equivariance condition of an RGF object holds automatically (since EquivariantSystem already includes it). -/
theorem rgfObject_is_equivariant (X : RGFObject) : IsEquivariantCategorical X :=
  X.sys.equivariant

/-! ============================================================
    Part 3: invertible morphisms and conjugation
    ============================================================ -/

/-- An invertible morphism: an RGF morphism with an inverse. -/
structure InvertibleRGFMorphism (X Y : RGFObject) where
  /-- The forward morphism. -/
  hom : X ⟶ Y
  /-- The backward morphism. -/
  inv : Y ⟶ X
  /-- Left inverse. -/
  left_inv : inv ≫ hom = 𝟙 Y
  /-- Right inverse. -/
  right_inv : hom ≫ inv = 𝟙 X

/-- An invertible morphism induces conjugation of endomorphisms. -/
def conjugateByMorphism {X Y : RGFObject} (φ : InvertibleRGFMorphism X Y)
    (f : X ⟶ X) : Y ⟶ Y :=
  φ.inv ≫ f ≫ φ.hom

/-- Conjugation preserves the identity. -/
theorem conjugate_id {X Y : RGFObject} (φ : InvertibleRGFMorphism X Y) :
    conjugateByMorphism φ (𝟙 X) = 𝟙 Y := by
  simp only [conjugateByMorphism, Category.id_comp, φ.left_inv]

/-- Conjugation preserves composition. -/
theorem conjugate_comp {X Y : RGFObject} (φ : InvertibleRGFMorphism X Y)
    (f g : X ⟶ X) :
    conjugateByMorphism φ (f ≫ g) = conjugateByMorphism φ f ≫ conjugateByMorphism φ g := by
  simp only [conjugateByMorphism, Category.assoc]
  congr 1; congr 1
  conv_lhs => rw [← Category.id_comp g, ← φ.right_inv]
  simp only [Category.assoc]

/-! ============================================================
    Part 4: equivariant functors (declaration)
    ============================================================ -/

/-- An equivariant functor: a functor preserving the equivariance condition.
    This is the subcategory of endofunctors of the RGF category that satisfy equivariance. -/
def IsEquivariantFunctor (F : RGFObject ⥤ RGFObject) : Prop :=
  ∀ X : RGFObject, IsEquivariantCategorical (F.obj X)

/-- The identity functor is equivariant. -/
theorem id_functor_equivariant : IsEquivariantFunctor (𝟭 RGFObject) := by
  intro X
  exact rgfObject_is_equivariant X

end
