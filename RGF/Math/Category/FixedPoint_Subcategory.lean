/-
  Category/FixedPoint_Subcategory.lean — the fixed-point subcategory and embedding into the graph category
  Fixed-Point Subcategory and Graph Category Embedding

  Defines the fixed-point subcategory Fix(RGF) and constructs the encoding functor from fixed points to graphs.
-/

import Mathlib
import RGF.Math.Category.RGF_Category

open CategoryTheory Equiv Function

noncomputable section

/-! ============================================================
    Part 1: the fixed-point subcategory
    ============================================================ -/

/-- Fixed-point property: an RGF system has a fixed-point state. -/
def IsFixedPointRGF : ObjectProperty RGFObject :=
  fun X => ∃ s : RGFState X.n, X.sys.toRGFIterSystem.IsFixedPoint s

/-- The fixed-point subcategory Fix(RGF): contains only RGF systems that have a fixed point. -/
abbrev FixRGF := IsFixedPointRGF.FullSubcategory

/-- The embedding functor: Fix(RGF) ↪ RGF. -/
def fixInclusion : FixRGF ⥤ RGFObject := IsFixedPointRGF.ι

/-- The embedding functor is faithful. -/
theorem fixInclusion_faithful : fixInclusion.Faithful := by
  unfold fixInclusion; infer_instance

/-! ============================================================
    Part 2: the graph category (simple graphs + graph homomorphisms)
    ============================================================ -/

/-- Objects of the simple-graph category: a simple graph on some Fin n. -/
structure GraphObject where
  /-- Number of vertices. -/
  n : ℕ
  /-- The simple graph. -/
  graph : SimpleGraph (Fin n)

/-- Graph morphism: a structure-preserving map between graphs. -/
@[ext]
structure GraphMorphism (G H : GraphObject) where
  /-- The underlying map. -/
  f : Perm (Fin G.n) → Perm (Fin H.n)

namespace GraphCategory

def id (G : GraphObject) : GraphMorphism G G := ⟨_root_.id⟩

def comp {G H K : GraphObject} (f : GraphMorphism G H) (g : GraphMorphism H K) :
    GraphMorphism G K := ⟨g.f ∘ f.f⟩

theorem id_comp {G H : GraphObject} (f : GraphMorphism G H) :
    comp (id G) f = f := by ext; simp [comp, id]

theorem comp_id {G H : GraphObject} (f : GraphMorphism G H) :
    comp f (id H) = f := by ext; simp [comp, id]

theorem comp_assoc {A B C D : GraphObject}
    (f : GraphMorphism A B) (g : GraphMorphism B C) (h : GraphMorphism C D) :
    comp (comp f g) h = comp f (comp g h) := by ext; simp [comp]

end GraphCategory

instance : CategoryStruct GraphObject where
  Hom := GraphMorphism
  id := GraphCategory.id
  comp := fun f g => GraphCategory.comp f g

instance : Category GraphObject where
  id_comp := GraphCategory.id_comp
  comp_id := GraphCategory.comp_id
  assoc := GraphCategory.comp_assoc

/-! ============================================================
    Part 3: the functor from fixed points to graphs
    ============================================================ -/

/-- Extract from a fixed-point RGF system the graph corresponding to its fixed-point state. -/
noncomputable def extractFixedPointGraph (X : FixRGF) : GraphObject where
  n := X.obj.n
  graph := (Classical.choose X.property).toSimpleGraph

/-- The functor from fixed points to graphs. -/
noncomputable def fixToGraph : FixRGF ⥤ GraphObject where
  obj := extractFixedPointGraph
  map := fun f => ⟨(IsFixedPointRGF.ι.map f).f⟩
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- The fixToGraph functor is faithful. -/
theorem fixToGraph_faithful : fixToGraph.Faithful where
  map_injective := fun {X Y} {f g} h => by
    have hfg : (IsFixedPointRGF.ι.map f).f = (IsFixedPointRGF.ι.map g).f :=
      congr_arg GraphMorphism.f h
    exact (IsFixedPointRGF.ι).map_injective (RGFMorphism.ext hfg)

end
