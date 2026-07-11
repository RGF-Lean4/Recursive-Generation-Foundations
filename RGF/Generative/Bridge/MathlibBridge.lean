/-
  RGF/MathlibBridge.lean

  Direction V — Decoupling / fusion / refactoring against mainstream Mathlib.

  The RGF number systems `RGFNat`, `RGFInt`, `RGFRat` are built from scratch
  (`RGFNat.lean`, `RGFInt.lean`, `RGFRat.lean`) precisely to demonstrate that the
  framework does not *depend* on Mathlib's number library.  Their comparison maps
  `RGFNat.toNat`, `RGFInt.toInt`, `RGFRat.toRat` and the accompanying
  homomorphism / bijectivity lemmas were established in `RGFOrder.lean`.

  This module performs the **typeclass refactoring / isomorphic bridging** step:
  it packages those maps into first-class Mathlib isomorphisms, so that every RGF
  number system is *identified* with its Mathlib counterpart as an algebraic (and
  ordered) structure.  This is the "seamless bridge to the standard `ℕ / ℤ / ℚ`
  typeclasses" requested in Direction V, complementing the already-established
  ordered ring isomorphism `RGFReal' ≃+*o ℝ` (`RGFOrderReal.lean`).

  Contents (namespace `RGF.MathlibBridge`):

  * `natRingEquiv  : RGFNat ≃+* ℕ`  and the order iso `natOrderIso : RGFNat ≃o ℕ`.
  * `intRingEquiv  : RGFInt ≃+* ℤ`  and the order iso `intOrderIso : RGFInt ≃o ℤ`.
  * `ratRingEquiv  : RGFRat ≃+* ℚ`.
  * Naturality / compatibility lemmas tying the bridges to the canonical
    inclusions (`natRingEquiv (ofNat' n) = n`, `intRingEquiv ∘ ofRGFNat = ↑`, …).
-/
import Mathlib
import RGF.Math.Real.RGFOrder

namespace RGF.MathlibBridge

open RGF

attribute [local instance] RGFRat.commRing

/-! ## 1. `RGFNat ≃+* ℕ` -/

/-- The semiring isomorphism between the RGF naturals and Mathlib's `ℕ`,
    packaging `RGFNat.toNat` (a bijective additive/multiplicative homomorphism). -/
def natRingEquiv : RGFNat ≃+* ℕ where
  toFun := RGFNat.toNat
  invFun := RGFNat.ofNat'
  left_inv := RGFNat.ofNat_toNat
  right_inv := RGFNat.toNat_ofNat
  map_mul' := RGFNat.toNat_mul
  map_add' := RGFNat.toNat_add

@[simp] theorem natRingEquiv_apply (a : RGFNat) : natRingEquiv a = a.toNat := rfl

@[simp] theorem natRingEquiv_symm_apply (n : ℕ) :
    natRingEquiv.symm n = RGFNat.ofNat' n := rfl

/-- The order isomorphism `RGFNat ≃o ℕ`. -/
def natOrderIso : RGFNat ≃o ℕ where
  toEquiv := natRingEquiv.toEquiv
  map_rel_iff' := by
    intro a b
    exact RGFNat.toNat_le.symm

/-! ## 2. `RGFInt ≃+* ℤ` -/

/-- The ring isomorphism between the RGF integers and Mathlib's `ℤ`, built from
    the bijective ring homomorphism `RGFInt.toIntHom`. -/
noncomputable def intRingEquiv : RGFInt ≃+* ℤ :=
  RingEquiv.ofBijective RGFInt.toIntHom
    ⟨RGFInt.toInt_injective, RGFInt.toInt_surjective⟩

@[simp] theorem intRingEquiv_apply (a : RGFInt) : intRingEquiv a = a.toInt := rfl

/-- Compatibility of the integer bridge with the canonical inclusion of naturals. -/
theorem intRingEquiv_ofRGFNat (n : RGFNat) :
    intRingEquiv (RGFInt.ofRGFNat n) = (n.toNat : ℤ) := by
  simp [intRingEquiv_apply, RGFInt.toInt_ofRGFNat]

/-! ## 3. `RGFRat ≃+* ℚ` -/

/-- The ring homomorphism `RGFRat →+* ℚ` given by `RGFRat.toRat`. -/
def toRatHom : RGFRat →+* ℚ where
  toFun := RGFRat.toRat
  map_one' := RGFRat.toRat_one
  map_mul' := RGFRat.toRat_mul
  map_zero' := RGFRat.toRat_zero
  map_add' := RGFRat.toRat_add

/-- The ring isomorphism between the RGF rationals and Mathlib's `ℚ`, built from
    the bijective ring homomorphism `RGFRat.toRat`. -/
noncomputable def ratRingEquiv : RGFRat ≃+* ℚ :=
  RingEquiv.ofBijective toRatHom
    ⟨RGFRat.toRat_injective, RGFRat.toRat_surjective⟩

@[simp] theorem ratRingEquiv_apply (a : RGFRat) : ratRingEquiv a = a.toRat := rfl

end RGF.MathlibBridge
