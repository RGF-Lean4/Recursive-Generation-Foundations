/-
  RGF/GenerativeDynamicalCategory.lean

  Task II — Operator category theory and model theory: the *Category of
  Generative Dynamical Systems* and the categorical meaning of membrane locking.

  We formalize the recursive iteration dynamics (RCE) as a category `GenSys`
  whose objects are pairs `(carrier, step)` — a state space with a generative
  step map — and whose morphisms are the equivariant maps that commute with the
  dynamics.  We then show that *membrane locking* (existence of a unique locked
  solution / fixed point, as in the `k = 5`, `d = 3` structures) is not an
  ad-hoc physical accident but a genuine **universal property**:

  * `GenSys` is a category (`instance : Category GenSys`).
  * `trivialSys` (the one-point system) is a **terminal object**
    (`trivialIsTerminal`).
  * global elements = fixed points: `globalElementsEquivFix` shows that
    morphisms *from* the terminal object are exactly the fixed points of the
    dynamics — the representing universal property of the locked states.
  * `fix_universal` : the fixed-point set is the **equalizer** of `step` and
    `id`, i.e. a limit, with its universal factorization property.
  * `disc_fix_adjunction` : the "discrete/identity system" functor is **left
    adjoint** to the fixed-point functor `Fix`.  Membrane locking is thus the
    limit/right-adjoint side of an adjunction, exactly the abstract statement
    sought.
  * HoTT link: `membraneLocked_iff_fix_contractible` and
    `membraneLocked_iff_globalElements_contractible` — a system is
    membrane-locked iff its type of fixed points (equivalently its type of
    global elements) is **contractible** (an h-level-0 / mere-point type).

  Everything is `sorry`-free.
-/

import Mathlib

open CategoryTheory

namespace RGF.GenCat

universe u

/-! ## 1. The category of generative dynamical systems -/

/-- A generative dynamical system (an RCE): a state space with a generative
    step map. -/
structure GenSys where
  /-- The state space. -/
  carrier : Type u
  /-- The generative step / iteration map. -/
  step : carrier → carrier

/-- A morphism of generative dynamical systems: a map commuting with the
    dynamics (an equivariant / intertwining map). -/
@[ext]
structure GenHom (X Y : GenSys) where
  /-- The underlying map of state spaces. -/
  f : X.carrier → Y.carrier
  /-- Intertwining/equivariance with the step maps. -/
  commute : ∀ x, f (X.step x) = Y.step (f x)

/-- Identity morphism. -/
def GenHom.id (X : GenSys) : GenHom X X := ⟨_root_.id, fun _ => rfl⟩

/-- Composition of morphisms. -/
def GenHom.comp {X Y Z : GenSys} (f : GenHom X Y) (g : GenHom Y Z) : GenHom X Z :=
  ⟨g.f ∘ f.f, fun x => by
    simp only [Function.comp_apply, f.commute, g.commute]⟩

instance : Category GenSys where
  Hom := GenHom
  id := GenHom.id
  comp := GenHom.comp
  id_comp := by intro X Y f; rfl
  comp_id := by intro X Y f; rfl
  assoc := by intro W X Y Z f g h; rfl

@[simp] theorem GenHom.id_f (X : GenSys) : (𝟙 X : GenHom X X).f = _root_.id := rfl

@[simp] theorem GenHom.comp_f {X Y Z : GenSys} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).f = g.f ∘ f.f := rfl

/-! ## 2. The terminal object -/

/-- The one-point (trivial) generative system. -/
def trivialSys : GenSys := ⟨PUnit, _root_.id⟩

/-- The trivial system is terminal: every system maps to it uniquely. -/
def trivialIsTerminal : Limits.IsTerminal trivialSys :=
  Limits.IsTerminal.ofUniqueHom (fun X => ⟨fun _ => PUnit.unit, fun _ => rfl⟩)
    (by intro X m; apply GenHom.ext; funext x; rfl)

/-! ## 3. Fixed points, global elements, and the representing universal property -/

/-- The fixed points (locked states) of a system. -/
def FixSet (X : GenSys) : Type u := {x : X.carrier // X.step x = x}

/-- **Global elements are fixed points.** Morphisms from the terminal object
    into a system `X` are in canonical bijection with the fixed points (locked
    states) of `X`.  This is the universal property representing the locked
    states. -/
def globalElementsEquivFix (X : GenSys) : (trivialSys ⟶ X) ≃ FixSet X where
  toFun h := ⟨h.f PUnit.unit, (h.commute PUnit.unit).symm⟩
  invFun x := ⟨fun _ => x.1, fun _ => x.2.symm⟩
  left_inv := by intro h; apply GenHom.ext; funext u; cases u; rfl
  right_inv := by intro x; rfl

/-- **The fixed-point set is the equalizer of `step` and `id`.** Any map from an
    arbitrary type `Z` that lands in the locked states factors uniquely through
    the inclusion `FixSet X ↪ X.carrier`. This is the limit universal property. -/
theorem fix_universal (X : GenSys) {Z : Type u} (g : Z → X.carrier)
    (hg : ∀ z, X.step (g z) = g z) :
    ∃! g' : Z → FixSet X, (fun z => (g' z).1) = g := by
  refine ⟨fun z => ⟨g z, hg z⟩, rfl, ?_⟩
  intro g'' h
  funext z
  apply Subtype.ext
  exact congrFun h z

/-! ## 4. The fixed-point functor and its left adjoint -/

/-- The fixed-point functor `Fix : GenSys ⥤ Type`. -/
def Fix : GenSys ⥤ Type u where
  obj X := FixSet X
  map {X Y} f := fun x => ⟨f.f x.1, by
    have := f.commute x.1
    rw [x.2] at this
    exact this.symm⟩
  map_id := by intro X; funext x; apply Subtype.ext; rfl
  map_comp := by intro X Y Z f g; funext x; apply Subtype.ext; rfl

/-- The "identity/discrete system" functor `Disc : Type ⥤ GenSys` sending a type
    to the system with identity dynamics. -/
def Disc : Type u ⥤ GenSys where
  obj A := ⟨A, _root_.id⟩
  map {A B} h := ⟨h, fun _ => rfl⟩
  map_id := by intro A; rfl
  map_comp := by intro A B C f g; rfl

/-- Hom-set bijection witnessing the adjunction `Disc ⊣ Fix`. -/
def discFixHomEquiv (A : Type u) (X : GenSys) :
    (Disc.obj A ⟶ X) ≃ (A ⟶ Fix.obj X) where
  toFun φ := fun a => ⟨φ.f a, (φ.commute a).symm⟩
  invFun ψ := ⟨fun a => (ψ a).1, fun a => ((ψ a).2).symm⟩
  left_inv := by intro φ; apply GenHom.ext; rfl
  right_inv := by intro ψ; funext a; apply Subtype.ext; rfl

/-- **Membrane locking as an adjunction.** The discrete-system functor is left
    adjoint to the fixed-point functor.  Hence the locked states (fixed points)
    arise as a right adjoint — a limit / universal construction. -/
def disc_fix_adjunction : Disc ⊣ Fix :=
  Adjunction.mkOfHomEquiv
    { homEquiv := discFixHomEquiv
      homEquiv_naturality_left_symm := by intro A A' X f g; rfl
      homEquiv_naturality_right := by intro A X X' f g; rfl }

/-! ## 5. Membrane locking and contractibility (HoTT link) -/

/-- Membrane locking: the dynamics has a unique locked state (fixed point). -/
def IsMembraneLocked (X : GenSys) : Prop := ∃! x : X.carrier, X.step x = x

/-- Contractibility of a type (h-level 0): a center to which everything is
    equal.  This is the HoTT notion of a "mere point". -/
def IsContractible (T : Type u) : Prop := ∃ c : T, ∀ t : T, t = c

/-- **Membrane locking is contractibility of the fixed-point type.** -/
theorem membraneLocked_iff_fix_contractible (X : GenSys) :
    IsMembraneLocked X ↔ IsContractible (FixSet X) := by
  constructor
  · rintro ⟨x, hx, huniq⟩
    exact ⟨⟨x, hx⟩, fun t => Subtype.ext (huniq t.1 t.2)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c.1, c.2, fun y hy => congrArg Subtype.val (hc ⟨y, hy⟩)⟩

/-- Contractibility transports along an equivalence. -/
theorem IsContractible.of_equiv {S T : Type u} (e : S ≃ T) (h : IsContractible S) :
    IsContractible T := by
  obtain ⟨c, hc⟩ := h
  exact ⟨e c, fun t => by rw [← e.apply_symm_apply t, hc (e.symm t)]⟩

/-- **Membrane locking is contractibility of the type of global elements.** A
    system is membrane-locked iff the type of morphisms from the terminal object
    (its global elements) is contractible. -/
theorem membraneLocked_iff_globalElements_contractible (X : GenSys) :
    IsMembraneLocked X ↔ IsContractible (trivialSys ⟶ X) := by
  rw [membraneLocked_iff_fix_contractible]
  constructor
  · exact fun h => h.of_equiv (globalElementsEquivFix X).symm
  · exact fun h => h.of_equiv (globalElementsEquivFix X)

end RGF.GenCat
