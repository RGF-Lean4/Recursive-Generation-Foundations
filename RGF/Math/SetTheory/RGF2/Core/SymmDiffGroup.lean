/-
  RGF2/Core/SymmDiffGroup.lean   (module `RGF2.Core.SymmDiffGroup`)

  **RGF 2.0 — a genuine group living inside the internal ZFC universe `RGFSet₂`.**

  Path 1 of the RGF 2.0 reconstruction (`RGF2/Core/WType.lean`) upgraded the
  encoding domain from finite arithmetic codes to a lossless W-type of labelled
  branching trees, quotiented to the internal set universe `RGFSet₂`, and verified
  the ten axioms of ZFC there.  The original prompt stresses that once this is in
  place, ordinary mathematical objects (numbers, algebraic structures, …) become
  *internal* objects of the tree universe rather than the carrier of the encoding.

  This file makes that concrete for the simplest non-trivial algebraic structure:
  the **symmetric-difference group** on `RGFSet₂`.  For internal sets `a b`,

      a * b  :=  a △ b  =  (a \ b) ∪ (b \ a)          (symmetric difference)
      1      :=  ∅                                       (the empty set)
      a⁻¹    :=  a                                       (every element is an involution)

  This is the canonical group structure on the power set of any set, transported
  onto the internal universe.  Membership in a product is the *exclusive or* of
  the two memberships, which makes each group axiom a small propositional fact
  about `Mem₂`.

  Following the requested workflow, the three proof obligations of
  `Group.ofLeftAxioms` are first discharged as three independent lemmas —

    * `symmDiff_assoc₂`      associativity           `(a * b) * c = a * (b * c)`
    * `one_symmDiff₂`        left identity           `1 * a = a`
    * `inv_symmDiff_cancel₂` left inverse            `a⁻¹ * a = 1`

  — and only then bundled into the `Group RGFSet₂` instance.  A short extra
  argument (`symmDiff_comm₂`) upgrades this to a `CommGroup`, recording that the
  internal symmetric-difference group is abelian (indeed a Boolean group, every
  element of order dividing 2).
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Core.WType

universe u

namespace RGF
namespace RGF2

/-! ## Operations: symmetric difference, empty set, self-inverse -/

/-- Symmetric difference of two internal sets, `a △ b = (a \ b) ∪ (b \ a)`,
computed in the standard von Neumann universe through the equivalence `equivZF`
and pulled back to `RGFSet₂`. -/
noncomputable def symmDiff₂ (a b : RGFSet₂.{u}) : RGFSet₂.{u} :=
  equivZF.symm ((equivZF a \ equivZF b) ∪ (equivZF b \ equivZF a))

/-- The internal multiplication is symmetric difference. -/
noncomputable instance : Mul RGFSet₂.{u} := ⟨symmDiff₂⟩

/-- The internal identity is the empty set. -/
noncomputable instance : One RGFSet₂.{u} := ⟨equivZF.symm ∅⟩

/-- Every internal set is its own inverse under symmetric difference. -/
instance : Inv RGFSet₂.{u} := ⟨id⟩

/-- Unfolding the (trivial) inverse. -/
@[simp] theorem inv_eq_self₂ (a : RGFSet₂.{u}) : a⁻¹ = a := rfl

/-! ## Membership characterisations -/

/-- Membership in a product is the *exclusive or* of the two memberships:
`z ∈ a △ b ↔ (z ∈ a ∧ z ∉ b) ∨ (z ∈ b ∧ z ∉ a)`. -/
theorem mem_mul₂ (a b z : RGFSet₂.{u}) :
    Mem₂ z (a * b) ↔ ((Mem₂ z a ∧ ¬ Mem₂ z b) ∨ (Mem₂ z b ∧ ¬ Mem₂ z a)) := by
  show Mem₂ z (symmDiff₂ a b) ↔ _
  simp only [Mem₂, symmDiff₂, Equiv.apply_symm_apply, ZFSet.mem_union, ZFSet.mem_sdiff]

/-- Nothing belongs to the identity, i.e. the internal `1` is empty. -/
theorem not_mem_one₂ (z : RGFSet₂.{u}) : ¬ Mem₂ z (1 : RGFSet₂.{u}) := by
  show ¬ Mem₂ z (equivZF.symm ∅)
  simp [Mem₂, Equiv.apply_symm_apply]

/-! ## The three obligations of `Group.ofLeftAxioms`, as independent lemmas -/

/-- **Obligation 1 — associativity.** `(a * b) * c = a * (b * c)`. -/
theorem symmDiff_assoc₂ (a b c : RGFSet₂.{u}) : a * b * c = a * (b * c) := by
  apply ext₂; intro z
  simp only [mem_mul₂]
  tauto

/-- **Obligation 2 — left identity.** `1 * a = a`. -/
theorem one_symmDiff₂ (a : RGFSet₂.{u}) : 1 * a = a := by
  apply ext₂; intro z
  rw [mem_mul₂]
  have := not_mem_one₂ z
  tauto

/-- **Obligation 3 — left inverse.** `a⁻¹ * a = 1`. -/
theorem inv_symmDiff_cancel₂ (a : RGFSet₂.{u}) : a⁻¹ * a = 1 := by
  apply ext₂; intro z
  rw [mem_mul₂, inv_eq_self₂]
  have := not_mem_one₂ z
  tauto

/-! ## Bundling into a group (and, as a bonus, a commutative group) -/

/-- The internal symmetric-difference **group** on the RGF 2.0 set universe,
assembled from the three obligations above via `Group.ofLeftAxioms`. -/
noncomputable instance instGroupRGFSet₂ : Group RGFSet₂.{u} :=
  Group.ofLeftAxioms symmDiff_assoc₂ one_symmDiff₂ inv_symmDiff_cancel₂

/-- Symmetric difference is commutative. -/
theorem symmDiff_comm₂ (a b : RGFSet₂.{u}) : a * b = b * a := by
  apply ext₂; intro z
  simp only [mem_mul₂]
  tauto

/-- The internal symmetric-difference group is in fact **abelian**. -/
noncomputable instance instCommGroupRGFSet₂ : CommGroup RGFSet₂.{u} :=
  { instGroupRGFSet₂ with mul_comm := symmDiff_comm₂ }

end RGF2
end RGF
