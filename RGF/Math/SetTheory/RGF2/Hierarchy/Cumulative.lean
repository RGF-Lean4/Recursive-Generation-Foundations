/-
  RGF2/Hierarchy/Cumulative.lean   (module `RGF2.Hierarchy.Cumulative`) — layer 1: cumulative hierarchy

  **RGF 2.0 — Path 2: the internal cumulative (von Neumann) hierarchy and its
  reflection / exhaustion properties.**

  RGF 1.0 has no room for a proper stratification of its universe: the Ackermann
  codes only reach the hereditarily finite sets.  Once Path 1 (`RGF2/Core/WType.lean`)
  supplies the full ZFC universe `RGFSet₂ ≃ ZFSet`, we can build the cumulative
  hierarchy inside it,

      V 0 = ∅,   V (α+1) = 𝒫 (V α),   V λ = ⋃_{β<λ} V β,

  transported from Mathlib's `ZFSet.vonNeumann`.  This file records:

    * `Vhier` / `rank₂`     the RGF 2.0 cumulative hierarchy and internal rank;
    * `mem_Vhier_iff`       `x ∈ V o ↔ rank₂ x < o`;
    * `Vhier_zero`          `V 0` is empty;
    * `Vhier_succ`          `V (α+1)` is the power set of `V α`;
    * `Vhier_mono`          the hierarchy is monotone in the ordinal stage;
    * `Vhier_transitive`    every stage is a transitive set;
    * `Vhier_exhaustion`    **every** RGF 2.0 set appears at some stage — the
                            hierarchy exhausts the whole universe;
    * `Vhier_reflection`    a reflection statement: every set, together with all of
                            its members, is captured by a single set stage `V o`.

  Together with the ZFC axioms of Path 1 this stratification is what raises the
  consistency strength of the RGF core from that of the hereditarily finite
  universe (≈ PA) to that of full ZFC.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Core.WType

open ZFSet Ordinal

universe u

namespace RGF
namespace RGF2

/-- The RGF 2.0 cumulative (von Neumann) hierarchy stage `V o`. -/
noncomputable def Vhier (o : Ordinal.{u}) : RGFSet₂.{u} := equivZF.symm (V_ o)

/-- The internal rank of an RGF 2.0 set: the least stage strictly containing it. -/
noncomputable def rank₂ (x : RGFSet₂.{u}) : Ordinal.{u} := (equivZF x).rank

/-- Membership in a hierarchy stage is governed by rank. -/
theorem mem_Vhier_iff (x : RGFSet₂.{u}) (o : Ordinal.{u}) :
    Mem₂ x (Vhier o) ↔ rank₂ x < o := by
  simp only [Mem₂, Vhier, rank₂, Equiv.apply_symm_apply, mem_vonNeumann]

/-- `V 0` is empty. -/
theorem Vhier_zero : IsEmpty₂ (Vhier.{u} 0) := by
  intro z; rw [mem_Vhier_iff]; simp

/-- `V (α+1)` is exactly the power set of `V α`. -/
theorem Vhier_succ (o : Ordinal.{u}) (z : RGFSet₂.{u}) :
    Mem₂ z (Vhier (Order.succ o)) ↔ Subset₂ z (Vhier o) := by
  simp only [Mem₂, Vhier, Equiv.apply_symm_apply, vonNeumann_succ, mem_powerset,
    Subset₂, ZFSet.subset_def]
  constructor
  · intro h w hw; exact h hw
  · intro h y hy
    have := h (equivZF.symm y) (by simpa only [Equiv.apply_symm_apply] using hy)
    simpa only [Equiv.apply_symm_apply] using this

/-- The hierarchy is monotone in the ordinal stage. -/
theorem Vhier_mono {a b : Ordinal.{u}} (h : a ≤ b) : Subset₂ (Vhier a) (Vhier b) := by
  intro z hz
  rw [mem_Vhier_iff] at hz ⊢
  exact lt_of_lt_of_le hz h

/-- Every stage is transitive: members of members are members. -/
theorem Vhier_transitive (o : Ordinal.{u}) (x y : RGFSet₂.{u})
    (hx : Mem₂ x (Vhier o)) (hy : Mem₂ y x) : Mem₂ y (Vhier o) := by
  simp only [Mem₂, Vhier, Equiv.apply_symm_apply] at hx ⊢
  exact (isTransitive_vonNeumann o).subset_of_mem hx hy

/-- **Exhaustion.** Every RGF 2.0 set appears at some stage of the hierarchy. -/
theorem Vhier_exhaustion (x : RGFSet₂.{u}) : ∃ o, Mem₂ x (Vhier o) := by
  obtain ⟨o, ho⟩ := exists_mem_vonNeumann (equivZF x)
  exact ⟨o, by simp only [Mem₂, Vhier, Equiv.apply_symm_apply]; exact ho⟩

/-- **Reflection.** Every set, together with all of its members, is captured by a
single set stage `V o` of the hierarchy. -/
theorem Vhier_reflection (x : RGFSet₂.{u}) :
    ∃ o, Mem₂ x (Vhier o) ∧ ∀ y, Mem₂ y x → Mem₂ y (Vhier o) := by
  obtain ⟨o, ho⟩ := Vhier_exhaustion x
  exact ⟨o, ho, fun y hy => Vhier_transitive o x y ho hy⟩

/-- **The limit-stage union equation** `V_λ = ⋃_{β<λ} V_β`, in its membership
form: at a limit stage a set appears iff it already appears at some earlier stage.
This is the third defining clause of the cumulative hierarchy
(`V 0 = ∅`, `V (α+1) = 𝒫(V α)`, `V λ = ⋃_{β<λ} V β`). -/
theorem Vhier_limit (o : Ordinal.{u}) (ho : Order.IsSuccLimit o) (x : RGFSet₂.{u}) :
    Mem₂ x (Vhier o) ↔ ∃ β < o, Mem₂ x (Vhier β) := by
  rw [mem_Vhier_iff]
  constructor
  · intro h
    exact ⟨Order.succ (rank₂ x), ho.succ_lt h, by rw [mem_Vhier_iff]; exact Order.lt_succ _⟩
  · rintro ⟨β, hβ, hx⟩
    rw [mem_Vhier_iff] at hx
    exact hx.trans hβ

/-! ## Internal set operations and the arithmetic of `rank₂`

We realise the basic ZFC set operations as honest functions on `RGFSet₂`
(transported from `ZFSet`), give their membership characterisations, and record
the arithmetic of the internal rank under pairing, union and power set — the
"rank calculus" of the RGF 2.0 hierarchy. -/

/-- Internal unordered pair `{a, b}`. -/
noncomputable def pair₂ (a b : RGFSet₂.{u}) : RGFSet₂.{u} :=
  equivZF.symm ({equivZF a, equivZF b})

/-- Internal singleton `{a}`. -/
noncomputable def singleton₂ (a : RGFSet₂.{u}) : RGFSet₂.{u} :=
  equivZF.symm ({equivZF a})

/-- Internal `insert a x = {a} ∪ x`. -/
noncomputable def insert₂ (a x : RGFSet₂.{u}) : RGFSet₂.{u} :=
  equivZF.symm (insert (equivZF a) (equivZF x))

/-- Internal binary union `a ∪ b`. -/
noncomputable def bunion₂ (a b : RGFSet₂.{u}) : RGFSet₂.{u} :=
  equivZF.symm (equivZF a ∪ equivZF b)

/-- Internal big union `⋃ x`. -/
noncomputable def sUnion₂ (x : RGFSet₂.{u}) : RGFSet₂.{u} :=
  equivZF.symm (equivZF x).sUnion

/-- Internal power set `𝒫 x` (as an operation returning a set). -/
noncomputable def powersetOf₂ (x : RGFSet₂.{u}) : RGFSet₂.{u} :=
  equivZF.symm (equivZF x).powerset

/-- Internal empty set. -/
noncomputable def empty₂' : RGFSet₂.{u} := equivZF.symm ∅

@[simp] theorem mem_pair₂ (a b z : RGFSet₂.{u}) : Mem₂ z (pair₂ a b) ↔ z = a ∨ z = b := by
  simp only [Mem₂, pair₂, Equiv.apply_symm_apply, ZFSet.mem_pair]
  constructor
  · rintro (h | h) <;> [left; right] <;> exact equivZF.injective h
  · rintro (h | h) <;> [left; right] <;> rw [h]

@[simp] theorem mem_singleton₂ (a z : RGFSet₂.{u}) : Mem₂ z (singleton₂ a) ↔ z = a := by
  simp only [Mem₂, singleton₂, Equiv.apply_symm_apply, ZFSet.mem_singleton]
  exact ⟨fun h => equivZF.injective h, fun h => by rw [h]⟩

@[simp] theorem mem_bunion₂ (a b z : RGFSet₂.{u}) : Mem₂ z (bunion₂ a b) ↔ Mem₂ z a ∨ Mem₂ z b := by
  simp only [Mem₂, bunion₂, Equiv.apply_symm_apply, ZFSet.mem_union]

@[simp] theorem mem_sUnion₂ (x z : RGFSet₂.{u}) :
    Mem₂ z (sUnion₂ x) ↔ ∃ w, Mem₂ w x ∧ Mem₂ z w := by
  simp only [Mem₂, sUnion₂, Equiv.apply_symm_apply, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨w, hw, hz⟩
    exact ⟨equivZF.symm w, by simpa [Equiv.apply_symm_apply] using hw,
      by simpa [Equiv.apply_symm_apply] using hz⟩
  · rintro ⟨w, hw, hz⟩; exact ⟨equivZF w, hw, hz⟩

@[simp] theorem mem_powersetOf₂ (x z : RGFSet₂.{u}) :
    Mem₂ z (powersetOf₂ x) ↔ Subset₂ z x := by
  simp only [Mem₂, powersetOf₂, Equiv.apply_symm_apply, ZFSet.mem_powerset, Subset₂,
    ZFSet.subset_def]
  constructor
  · intro h w hw; exact h hw
  · intro h w hw
    have := h (equivZF.symm w) (by simpa [Mem₂, Equiv.apply_symm_apply] using hw)
    simpa [Mem₂, Equiv.apply_symm_apply] using this

/-- **Rank of a pair.** `rank({a,b}) = max (rank a + 1) (rank b + 1)`. -/
theorem rank₂_pair (a b : RGFSet₂.{u}) :
    rank₂ (pair₂ a b) = max (Order.succ (rank₂ a)) (Order.succ (rank₂ b)) := by
  simp only [rank₂, pair₂, Equiv.apply_symm_apply, ZFSet.rank_pair]

/-- **Rank of a singleton.** `rank({a}) = rank a + 1`. -/
theorem rank₂_singleton (a : RGFSet₂.{u}) :
    rank₂ (singleton₂ a) = Order.succ (rank₂ a) := by
  simp only [rank₂, singleton₂, Equiv.apply_symm_apply, ZFSet.rank_singleton]

/-- **Rank of an insert.** `rank(insert a x) = max (rank a + 1) (rank x)`. -/
theorem rank₂_insert (a x : RGFSet₂.{u}) :
    rank₂ (insert₂ a x) = max (Order.succ (rank₂ a)) (rank₂ x) := by
  simp only [rank₂, insert₂, Equiv.apply_symm_apply, ZFSet.rank_insert]

/-- **Rank of a binary union.** `rank(a ∪ b) = max (rank a) (rank b)`. -/
theorem rank₂_bunion (a b : RGFSet₂.{u}) :
    rank₂ (bunion₂ a b) = max (rank₂ a) (rank₂ b) := by
  simp only [rank₂, bunion₂, Equiv.apply_symm_apply, ZFSet.rank_union]

/-- **Rank of a power set.** `rank(𝒫 x) = rank x + 1`. -/
theorem rank₂_powerset (x : RGFSet₂.{u}) :
    rank₂ (powersetOf₂ x) = Order.succ (rank₂ x) := by
  simp only [rank₂, powersetOf₂, Equiv.apply_symm_apply, ZFSet.rank_powerset]

/-- **Rank of the empty set.** `rank ∅ = 0`. -/
theorem rank₂_empty : rank₂ (empty₂'.{u}) = 0 := by
  simp only [rank₂, empty₂', Equiv.apply_symm_apply, ZFSet.rank_empty]

/-- **Rank of a big union.** `rank(⋃ x) ≤ rank x`. -/
theorem rank₂_sUnion_le (x : RGFSet₂.{u}) : rank₂ (sUnion₂ x) ≤ rank₂ x := by
  simp only [rank₂, sUnion₂, Equiv.apply_symm_apply]
  rw [ZFSet.rank_le_iff]
  intro y hy
  rw [ZFSet.mem_sUnion] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  exact (ZFSet.rank_lt_of_mem hyz).trans (ZFSet.rank_lt_of_mem hz)

end RGF2
end RGF
