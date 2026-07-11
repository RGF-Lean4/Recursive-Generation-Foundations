/-
  RGF2/Core/InternalOrdinal.lean   (module `RGF2.Core.InternalOrdinal`)

  **RGF 2.0 — internal ordinal arithmetic inside the tree universe `RGFSet₂`.**

  ⚠️  Honest scope statement.  This file is an *internal re-implementation of a
  standard construction*, not a new mathematical discovery.  Von Neumann ordinals
  and their arithmetic are completely classical; Mathlib already contains the full
  theory (`Ordinal`, `ZFSet.IsOrdinal`, `Ordinal.toZFSet`, `Ordinal.toZFSetIso`).
  What is shown here is only that the RGF 2.0 internal set universe `RGFSet₂`
  (`RGF2/Core/WType.lean`), being equivalent to the standard von Neumann universe
  `ZFSet`, *carries* the ordinals as ordinary internal objects, with the ordinal
  order, successor and arithmetic transported faithfully across the equivalence
  `equivZF`.  This is another data point for "the internal universe can host
  standard mathematical structures", in the same spirit as the internal reals and
  the internal symmetric-difference group — nothing here is claimed to be original.

  Contents (namespace `RGF.RGF2`):

    * `toRGFOrd`        the internal image of a Mathlib ordinal (a `RGFSet₂` object)
    * `IsOrdinal₂`      the internal predicate "is a von Neumann ordinal"
    * `succOrd₂`        the internal von Neumann successor `a ↦ a ∪ {a}`
    * order facts       `toRGFOrd_mem_iff`, `toRGFOrd_subset_iff` (∈ is `<`, ⊆ is ≤)
    * `ordAdd₂`,`ordMul₂` internal ordinal addition/multiplication (transported)
    * arithmetic laws   associativity, and the *non-commutativity* witness
                        `ordAdd₂_one_omega` / `ordAdd₂_omega_one_ne` recording
                        `1 + ω = ω ≠ ω + 1` internally.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Core.WType

open Ordinal

universe u

namespace RGF
namespace RGF2

/-! ## The internal ordinals as objects of `RGFSet₂` -/

/-- The internal image of a Mathlib ordinal: a genuine element of the RGF 2.0 set
universe obtained by pulling the standard von Neumann ordinal `o.toZFSet` back
along `equivZF`. -/
noncomputable def toRGFOrd (o : Ordinal.{u}) : RGFSet₂.{u} :=
  equivZF.symm o.toZFSet

/-- The internal predicate "`a` is a von Neumann ordinal", i.e. the corresponding
standard set is a `ZFSet` ordinal. -/
def IsOrdinal₂ (a : RGFSet₂.{u}) : Prop := (equivZF a).IsOrdinal

/-- The internal von Neumann successor `a ↦ a ∪ {a}`. -/
noncomputable def succOrd₂ (a : RGFSet₂.{u}) : RGFSet₂.{u} :=
  equivZF.symm (insert (equivZF a) (equivZF a))

@[simp] theorem equivZF_toRGFOrd (o : Ordinal.{u}) :
    equivZF (toRGFOrd o) = o.toZFSet := Equiv.apply_symm_apply _ _

/-
`toRGFOrd` is injective (distinct ordinals give distinct internal sets).
-/
theorem toRGFOrd_injective : Function.Injective (toRGFOrd.{u}) := by
  intro a b h;
  apply Ordinal.toZFSet_injective;
  rw [ ← equivZF_toRGFOrd a, ← equivZF_toRGFOrd b, h ]

/-
Every internal image of an ordinal is an internal ordinal.
-/
theorem isOrdinal₂_toRGFOrd (o : Ordinal.{u}) : IsOrdinal₂ (toRGFOrd o) := by
  unfold IsOrdinal₂;
  rw [equivZF_toRGFOrd];
  grind +suggestions

/-
**Internal ∈ is ordinal `<`.**
-/
theorem toRGFOrd_mem_iff {a b : Ordinal.{u}} :
    Mem₂ (toRGFOrd a) (toRGFOrd b) ↔ a < b := by
      unfold Mem₂; aesop;

/-
**Internal ⊆ is ordinal `≤`.**
-/
theorem toRGFOrd_subset_iff {a b : Ordinal.{u}} :
    Subset₂ (toRGFOrd a) (toRGFOrd b) ↔ a ≤ b := by
      -- By definition of `IsOrdinal₂`, we know that `toRGFOrd a` is an ordinal.
      unfold Subset₂; simp [Mem₂, toRGFOrd];
      constructor <;> intro h;
      · convert Ordinal.toZFSet_subset_toZFSet_iff.mp _;
        intro x hx; specialize h ( equivZF.symm x ) ; aesop;
      · intro z hz;
        exact Ordinal.toZFSet_subset_toZFSet_iff.mpr h hz

/-
The internal image of `0` is internally empty.
-/
theorem toRGFOrd_zero_isEmpty : IsEmpty₂ (toRGFOrd (0 : Ordinal.{u})) := by
  intro z hz;
  contrapose! hz; simp_all +decide [ Mem₂ ] ;

/-
The internal successor agrees with ordinal successor under `toRGFOrd`.
-/
theorem succOrd₂_toRGFOrd (o : Ordinal.{u}) :
    succOrd₂ (toRGFOrd o) = toRGFOrd (Order.succ o) := by
      simp [succOrd₂, toRGFOrd]

/-! ## Internal ordinal arithmetic (transported from Mathlib `Ordinal`) -/

/-- Internal ordinal addition.  For internal ordinals it agrees with Mathlib's
ordinal addition; the rank recovers the underlying Mathlib ordinal. -/
noncomputable def ordAdd₂ (a b : RGFSet₂.{u}) : RGFSet₂.{u} :=
  toRGFOrd ((equivZF a).rank + (equivZF b).rank)

/-- Internal ordinal multiplication. -/
noncomputable def ordMul₂ (a b : RGFSet₂.{u}) : RGFSet₂.{u} :=
  toRGFOrd ((equivZF a).rank * (equivZF b).rank)

/-
`ordAdd₂` restricted to internal ordinals is exactly ordinal addition.
-/
theorem ordAdd₂_toRGFOrd (a b : Ordinal.{u}) :
    ordAdd₂ (toRGFOrd a) (toRGFOrd b) = toRGFOrd (a + b) := by
      unfold ordAdd₂;
      rw [equivZF_toRGFOrd, equivZF_toRGFOrd];
      rw [ Ordinal.rank_toZFSet, Ordinal.rank_toZFSet ]

/-
`ordMul₂` restricted to internal ordinals is exactly ordinal multiplication.
-/
theorem ordMul₂_toRGFOrd (a b : Ordinal.{u}) :
    ordMul₂ (toRGFOrd a) (toRGFOrd b) = toRGFOrd (a * b) := by
      unfold ordMul₂;
      simp +decide [ equivZF_toRGFOrd ]

/-
**Associativity** of internal ordinal addition (on internal ordinals).
-/
theorem ordAdd₂_assoc (a b c : Ordinal.{u}) :
    ordAdd₂ (ordAdd₂ (toRGFOrd a) (toRGFOrd b)) (toRGFOrd c)
      = ordAdd₂ (toRGFOrd a) (ordAdd₂ (toRGFOrd b) (toRGFOrd c)) := by
        convert ordAdd₂_toRGFOrd ( a + b ) c |> Eq.trans <| ?_ using 1;
        · rw [ ordAdd₂_toRGFOrd ];
        · rw [ add_assoc, ← ordAdd₂_toRGFOrd, ← ordAdd₂_toRGFOrd ]

/-
**Associativity** of internal ordinal multiplication (on internal ordinals).
-/
theorem ordMul₂_assoc (a b c : Ordinal.{u}) :
    ordMul₂ (ordMul₂ (toRGFOrd a) (toRGFOrd b)) (toRGFOrd c)
      = ordMul₂ (toRGFOrd a) (ordMul₂ (toRGFOrd b) (toRGFOrd c)) := by
        grind +suggestions

/-- The internal ordinal `ω`. -/
noncomputable def omegaOrd₂ : RGFSet₂.{u} := toRGFOrd Ordinal.omega0.{u}

/-
Internally, `1 + ω = ω`.
-/
theorem ordAdd₂_one_omega :
    ordAdd₂ (toRGFOrd (1 : Ordinal.{u})) omegaOrd₂ = omegaOrd₂ := by
      convert ordAdd₂_toRGFOrd 1 Ordinal.omega0 using 1;
      rw [ Ordinal.one_add_omega0 ];
      rfl

/-
Internally, `ω + 1 ≠ ω`; combined with `ordAdd₂_one_omega` this witnesses that
internal ordinal addition is genuinely **non-commutative** (it is the real
ordinal arithmetic, not a degenerate copy).
-/
theorem ordAdd₂_omega_one_ne :
    ordAdd₂ omegaOrd₂ (toRGFOrd (1 : Ordinal.{u})) ≠ omegaOrd₂ := by
      exact fun h => absurd ( RGF.RGF2.toRGFOrd_injective h ) ( by simp +decide [ omegaOrd₂ ] )

end RGF2
end RGF