/-
  RGF2/Core/InternalCardinal.lean   (module `RGF2.Core.InternalCardinal`)

  **RGF 2.0 — internal cardinal comparison inside the tree universe `RGFSet₂`.**

  ⚠️  Honest scope statement.  As with `InternalOrdinal.lean`, this is an
  *internal re-implementation of a standard construction*, not new mathematics.
  Cardinality of sets, cardinal comparison and Cantor's theorem are classical and
  fully present in Mathlib (`ZFSet.card`, `ZFSet.card_mono`, `ZFSet.card_powerset`,
  `Cardinal.cantor`).  Here we only record that the RGF 2.0 internal set universe
  `RGFSet₂` carries the same cardinal-comparison structure as an ordinary internal
  feature, transported across the equivalence `equivZF : RGFSet₂ ≃ ZFSet`.

  The internal power-set object `powersetOf₂` is *reused* from
  `RGF2.Hierarchy.Cumulative` rather than redefined.

  Contents (namespace `RGF.RGF2`):

    * `card₂`           the cardinality of an internal set (a `Cardinal`)
    * `Equinum₂` / `CardLE₂` / `CardLT₂`  internal equinumerosity and cardinal `≤`, `<`
    * `subset₂_iff`     internal `⊆` is the standard subset relation
    * `card₂_mono`      monotonicity of cardinality along internal `⊆`
    * `card₂_powersetOf` internal `|P(a)| = 2 ^ |a|`
    * `cantor₂`         **Cantor's theorem, internally**: `|a| < |P(a)|`
    * `cardLE₂_antisymm` Schröder–Bernstein direction (`≤` antisymmetric ⇒ equinumerous)
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Core.WType
import RGF.Math.SetTheory.RGF2.Hierarchy.Cumulative

open Cardinal

universe u

namespace RGF
namespace RGF2

/-! ## Internal cardinality and comparison -/

/-- The cardinality of an internal set, transported from `ZFSet.card`. -/
noncomputable def card₂ (a : RGFSet₂.{u}) : Cardinal.{u} := (equivZF a).card

/-- Internal equinumerosity: two internal sets have the same cardinality. -/
def Equinum₂ (a b : RGFSet₂.{u}) : Prop := card₂ a = card₂ b

/-- Internal cardinal comparison `|a| ≤ |b|`. -/
def CardLE₂ (a b : RGFSet₂.{u}) : Prop := card₂ a ≤ card₂ b

/-- Internal strict cardinal comparison `|a| < |b|`. -/
def CardLT₂ (a b : RGFSet₂.{u}) : Prop := card₂ a < card₂ b

/-! ## Basic facts -/

/-- The internal subset relation corresponds to the standard subset relation. -/
theorem subset₂_iff {a b : RGFSet₂.{u}} :
    Subset₂ a b ↔ equivZF a ⊆ equivZF b := by
  constructor
  · intro h w hw
    convert h (equivZF.symm w) _ <;> unfold Mem₂ <;> aesop
  · intro h x hx; exact h hx

/-- The empty internal set has cardinality `0`. -/
theorem card₂_empty : card₂ (equivZF.symm (∅ : ZFSet.{u})) = 0 := by
  simp [card₂, Equiv.apply_symm_apply, ZFSet.card_empty]

/-- **Monotonicity**: internal `⊆` implies `≤` on internal cardinalities. -/
theorem card₂_mono {a b : RGFSet₂.{u}} (h : Subset₂ a b) : CardLE₂ a b :=
  ZFSet.card_mono (subset₂_iff.mp h)

/-- The internal power-set has cardinality `2 ^ |a|`. -/
theorem card₂_powersetOf (a : RGFSet₂.{u}) :
    card₂ (powersetOf₂ a) = 2 ^ card₂ a := by
  convert ZFSet.card_powerset (equivZF a) using 1
  unfold card₂ powersetOf₂; rw [Equiv.apply_symm_apply]

/-- **Cantor's theorem, internally.** Every internal set is strictly dominated in
cardinality by its internal power-set. -/
theorem cantor₂ (a : RGFSet₂.{u}) : CardLT₂ a (powersetOf₂ a) :=
  (Cardinal.cantor _).trans_le (by rw [card₂_powersetOf])

/-- **Schröder–Bernstein direction.** Mutual internal cardinal domination implies
internal equinumerosity. -/
theorem cardLE₂_antisymm {a b : RGFSet₂.{u}}
    (h1 : CardLE₂ a b) (h2 : CardLE₂ b a) : Equinum₂ a b :=
  le_antisymm h1 h2

end RGF2
end RGF
