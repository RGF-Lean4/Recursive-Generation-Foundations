/-
  RGF2/Core/WType.lean   (module `RGF2.Core.WType`) — layer 0: encoding domain

  **RGF 2.0 — Path 1: lifting the encoding domain from finite arithmetic codes to
  a lossless W-type of labelled branching trees.**

  The RGF 1.0 set-theoretic core (`RGFSetTheory.lean`, `RGFInfinity.lean`,
  `RGFZFBenchmark.lean`, `RGFConsistencyStrength.lean`) encodes sets as *finite*
  binary integers through the Ackermann map `a ∈ₐ b ↔ Nat.testBit b a`.  That
  one-dimensional numerical carrier can only ever host the hereditarily finite
  universe `HF = ZF − Infinity`: the Axiom of Infinity provably fails there
  (`RGFSet.not_infinity`).

  This file executes the first path of the RGF 2.0 reconstruction: the generative
  atom is upgraded from a *number* to a *tree*.  We define exactly the user's
  W-type of pre-sets

      inductive RGFPreSet | mk (α : Type u) (f : α → RGFPreSet)

  (branching trees with an index type at every node), quotient it by hereditary
  bisimulation (the extensional equivalence of pre-sets), and obtain the RGF 2.0
  set universe `RGFSet₂`.

  We prove that `RGFPreSet` is canonically equivalent to Mathlib's pre-set type
  `PSet` (`preEquiv`), hence the quotient `RGFSet₂` is equivalent to the standard
  von Neumann universe `ZFSet` (`equivZF`), with membership preserved on the nose
  (`Mem₂`).  Transporting along this equivalence we verify **every axiom of full
  ZFC** for `(RGFSet₂, Mem₂)`:

    * Extensionality           `ext₂`
    * Empty set                `empty₂`
    * Pairing                  `pairing₂`
    * Union                    `union₂`
    * Power set                `powerset₂`
    * Separation (schema)      `separation₂`
    * Replacement (schema)     `replacement₂`
    * Foundation / Regularity  `foundation₂`
    * **Infinity**             `infinity₂`   ← the defect eliminated
    * **Choice**               `choice₂`

  In particular the branching tree with index type `ℕ` realises `ω` internally,
  so Infinity — which genuinely *fails* for the RGF 1.0 arithmetic codes — now
  holds unconditionally.  The reals `RGFReal'` are no longer the carrier of the
  set universe; they become one ordinary internal object of the tree universe.
-/
import Mathlib

universe u

namespace RGF
namespace RGF2

/-! ## The RGF 2.0 pre-sets: labelled branching trees (a W-type) -/

/-- An RGF 2.0 pre-set is a well-founded branching tree: a node carries an index
type `α : Type u` together with a family of child pre-sets `f : α → RGFPreSet`.
This is the "multi-dimensional tree" encoding domain replacing the one-dimensional
Ackermann numerical codes of RGF 1.0. -/
inductive RGFPreSet : Type (u+1)
  | mk (α : Type u) (f : α → RGFPreSet) : RGFPreSet

/-- Every RGF 2.0 pre-set is, structurally, a Mathlib pre-set. -/
def toPSet : RGFPreSet.{u} → PSet.{u}
  | .mk α f => ⟨α, fun a => toPSet (f a)⟩

/-- ... and conversely. -/
def ofPSet : PSet.{u} → RGFPreSet.{u}
  | ⟨α, A⟩ => .mk α (fun a => ofPSet (A a))

theorem to_of (x : PSet.{u}) : toPSet (ofPSet x) = x := by
  induction x with
  | mk α A ih => simp only [ofPSet, toPSet]; congr 1; funext a; exact ih a

theorem of_to (x : RGFPreSet.{u}) : ofPSet (toPSet x) = x := by
  induction x with
  | mk α f ih => simp only [ofPSet, toPSet]; congr 1; funext a; exact ih a

/-- The RGF 2.0 pre-sets are canonically equivalent to Mathlib's pre-sets. -/
def preEquiv : RGFPreSet.{u} ≃ PSet.{u} where
  toFun := toPSet
  invFun := ofPSet
  left_inv := of_to
  right_inv := to_of

/-- Hereditary bisimulation of trees: two RGF 2.0 pre-sets are equivalent iff the
corresponding Mathlib pre-sets are extensionally equivalent. -/
instance instSetoid : Setoid RGFPreSet.{u} where
  r x y := PSet.Equiv (toPSet x) (toPSet y)
  iseqv :=
    ⟨fun _ => PSet.Equiv.refl _, fun h => PSet.Equiv.symm h,
      fun h1 h2 => PSet.Equiv.trans h1 h2⟩

/-! ## The RGF 2.0 set universe -/

/-- The RGF 2.0 sets: branching trees taken up to hereditary bisimulation. -/
def RGFSet₂ := Quotient (instSetoid.{u})

/-- The RGF 2.0 universe is equivalent to the standard von Neumann universe. -/
def equivZF : RGFSet₂.{u} ≃ ZFSet.{u} :=
  Quotient.congr preEquiv (fun _ _ => Iff.rfl)

/-- Internal membership on the RGF 2.0 universe. -/
def Mem₂ (a b : RGFSet₂.{u}) : Prop := equivZF a ∈ equivZF b

/-- Internal subset relation. -/
def Subset₂ (a b : RGFSet₂.{u}) : Prop := ∀ z, Mem₂ z a → Mem₂ z b

/-- Internal emptiness predicate. -/
def IsEmpty₂ (e : RGFSet₂.{u}) : Prop := ∀ z, ¬ Mem₂ z e

/-! ## The axioms of ZFC, verified internally for `(RGFSet₂, Mem₂)` -/

/-- **Extensionality.** -/
theorem ext₂ {x y : RGFSet₂.{u}} (h : ∀ z, Mem₂ z x ↔ Mem₂ z y) : x = y := by
  apply equivZF.injective; apply ZFSet.ext; intro z
  simpa [Mem₂, Equiv.apply_symm_apply] using h (equivZF.symm z)

/-- **Empty set.** -/
theorem empty₂ : ∃ e : RGFSet₂.{u}, IsEmpty₂ e :=
  ⟨equivZF.symm ∅, by intro z; simp [Mem₂, Equiv.apply_symm_apply]⟩

/-- **Pairing.** -/
theorem pairing₂ (a b : RGFSet₂.{u}) : ∃ p, ∀ z, Mem₂ z p ↔ (z = a ∨ z = b) := by
  refine ⟨equivZF.symm {equivZF a, equivZF b}, fun z => ?_⟩
  simp only [Mem₂, Equiv.apply_symm_apply, ZFSet.mem_pair]
  constructor
  · rintro (h | h) <;> [left; right] <;> exact equivZF.injective h
  · rintro (h | h) <;> [left; right] <;> rw [h]

/-- **Union.** -/
theorem union₂ (x : RGFSet₂.{u}) :
    ∃ u, ∀ z, Mem₂ z u ↔ ∃ w, Mem₂ w x ∧ Mem₂ z w := by
  refine ⟨equivZF.symm (ZFSet.sUnion (equivZF x)), fun z => ?_⟩
  simp only [Mem₂, Equiv.apply_symm_apply, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨w, hw, hz⟩
    exact ⟨equivZF.symm w, by simpa [Equiv.apply_symm_apply] using hw,
      by simpa [Equiv.apply_symm_apply] using hz⟩
  · rintro ⟨w, hw, hz⟩; exact ⟨equivZF w, hw, hz⟩

/-- **Power set.** -/
theorem powerset₂ (x : RGFSet₂.{u}) : ∃ p, ∀ z, Mem₂ z p ↔ Subset₂ z x := by
  refine ⟨equivZF.symm (equivZF x).powerset, fun z => ?_⟩
  simp only [Mem₂, Equiv.apply_symm_apply, ZFSet.mem_powerset, Subset₂, ZFSet.subset_def]
  constructor
  · intro h w hw; exact h hw
  · intro h w hw
    have := h (equivZF.symm w) (by simpa [Mem₂, Equiv.apply_symm_apply] using hw)
    simpa [Mem₂, Equiv.apply_symm_apply] using this

/-- **Separation** (full first-order schema, one instance per predicate `p`). -/
theorem separation₂ (p : RGFSet₂.{u} → Prop) (x : RGFSet₂.{u}) :
    ∃ s, ∀ z, Mem₂ z s ↔ (Mem₂ z x ∧ p z) := by
  classical
  refine ⟨equivZF.symm (ZFSet.sep (fun w => p (equivZF.symm w)) (equivZF x)), fun z => ?_⟩
  simp only [Mem₂, Equiv.apply_symm_apply, ZFSet.mem_sep, Equiv.symm_apply_apply]

/-- **Replacement** (full first-order schema, one instance per class function `f`). -/
theorem replacement₂ (f : RGFSet₂.{u} → RGFSet₂.{u}) (x : RGFSet₂.{u}) :
    ∃ y, ∀ z, Mem₂ z y ↔ ∃ w, Mem₂ w x ∧ f w = z := by
  classical
  set F : ZFSet.{u} → ZFSet.{u} := fun v => equivZF (f (equivZF.symm v)) with hF
  haveI : ZFSet.Definable₁ F := Classical.allZFSetDefinable (fun v => F (v 0))
  refine ⟨equivZF.symm (ZFSet.image F (equivZF x)), fun z => ?_⟩
  simp only [Mem₂, Equiv.apply_symm_apply, ZFSet.mem_image]
  constructor
  · rintro ⟨w, hw, hz⟩
    refine ⟨equivZF.symm w, by simpa [Mem₂, Equiv.apply_symm_apply] using hw, ?_⟩
    apply equivZF.injective; simpa [hF] using hz
  · rintro ⟨w, hw, hz⟩
    exact ⟨equivZF w, hw, by simp [hF, Equiv.symm_apply_apply, hz]⟩

/-- **Foundation / Regularity.** -/
theorem foundation₂ (x : RGFSet₂.{u}) (hx : ¬ IsEmpty₂ x) :
    ∃ y, Mem₂ y x ∧ ∀ z, Mem₂ z y → ¬ Mem₂ z x := by
  have hne : equivZF x ≠ ∅ := by
    intro h; apply hx; intro z hz; rw [Mem₂] at hz; rw [h] at hz; simp at hz
  obtain ⟨y, hy, hyx⟩ := ZFSet.regularity (equivZF x) hne
  refine ⟨equivZF.symm y, by simpa [Mem₂, Equiv.apply_symm_apply] using hy, ?_⟩
  intro z hz hzx
  have hzy : equivZF z ∈ y := by simpa [Mem₂, Equiv.apply_symm_apply] using hz
  have : equivZF z ∈ (equivZF x) ∩ y := ZFSet.mem_inter.2 ⟨hzx, hzy⟩
  rw [hyx] at this; simp at this

/-- **Infinity** — the defect that genuinely *fails* for the RGF 1.0 arithmetic
codes now holds unconditionally: there is an inductive set (empty element, closed
under von Neumann successor `x ↦ x ∪ {x}`). -/
theorem infinity₂ : ∃ I : RGFSet₂.{u},
    (∃ e, Mem₂ e I ∧ IsEmpty₂ e) ∧
    (∀ x, Mem₂ x I → ∃ s, Mem₂ s I ∧ ∀ z, Mem₂ z s ↔ (Mem₂ z x ∨ z = x)) := by
  refine ⟨equivZF.symm ZFSet.omega, ⟨equivZF.symm ∅, by
      simp [Mem₂, Equiv.apply_symm_apply, ZFSet.omega_zero], by
      intro z; simp [Mem₂, Equiv.apply_symm_apply]⟩, ?_⟩
  intro x hx
  refine ⟨equivZF.symm (insert (equivZF x) (equivZF x)), ?_, ?_⟩
  · simp only [Mem₂, Equiv.apply_symm_apply] at hx ⊢; exact ZFSet.omega_succ hx
  · intro z
    simp only [Mem₂, Equiv.apply_symm_apply, ZFSet.mem_insert_iff]
    constructor
    · rintro (h | h)
      · exact Or.inr (equivZF.injective h)
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by rw [h])

/-- **Choice.** Any RGF 2.0 set of non-empty sets admits a choice function. -/
theorem choice₂ (x : RGFSet₂.{u}) (h : ∀ a, Mem₂ a x → ∃ b, Mem₂ b a) :
    ∃ c : RGFSet₂.{u} → RGFSet₂.{u}, ∀ a, Mem₂ a x → Mem₂ (c a) a := by
  classical
  refine ⟨fun a => if ha : Mem₂ a x then Classical.choose (h a ha) else a, ?_⟩
  intro a ha; simp only [ha, dif_pos]; exact Classical.choose_spec (h a ha)

end RGF2
end RGF
