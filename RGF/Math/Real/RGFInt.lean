/-
  Foundations/RGFInt.lean

  RGF integers: a difference-pair construction based on RGFNat.
  RGFInt is defined as a quotient type of RGFNat × RGFNat, where (a, b) represents a - b.

  Dependency note: import Mathlib is used for the ring tactic and algebraic-structure type classes.
  The core definitions do not depend on Mathlib's reals or analysis library.
-/
import Mathlib
import RGF.Math.Real.RGFNat

namespace RGF

open RGFNat

/-! ## Pre-integers: difference pairs -/

structure PreInt where
  pos : RGFNat
  neg : RGFNat

namespace PreInt

def Equiv (x y : PreInt) : Prop :=
  x.pos + y.neg = y.pos + x.neg

theorem equiv_refl (x : PreInt) : Equiv x x := rfl
theorem equiv_symm {x y : PreInt} (h : Equiv x y) : Equiv y x := h.symm

theorem equiv_trans {x y z : PreInt} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z := by
  unfold Equiv at *
  have key : (x.pos + z.neg) + (y.pos + y.neg) = (z.pos + x.neg) + (y.pos + y.neg) :=
    calc (x.pos + z.neg) + (y.pos + y.neg)
        = (x.pos + y.neg) + (y.pos + z.neg) := by ring
      _ = (y.pos + x.neg) + (y.pos + z.neg) := by rw [h1]
      _ = (y.pos + x.neg) + (z.pos + y.neg) := by rw [h2]
      _ = (z.pos + x.neg) + (y.pos + y.neg) := by ring
  exact RGFNat.add_right_cancel _ _ _ key

instance preIntSetoid : Setoid PreInt where
  r := Equiv
  iseqv := ⟨equiv_refl, fun h => equiv_symm h, fun h1 h2 => equiv_trans h1 h2⟩

end PreInt

def RGFInt := Quotient PreInt.preIntSetoid

namespace RGFInt

def ofRGFNat (n : RGFNat) : RGFInt := Quotient.mk _ ⟨n, RGFNat.zero⟩
def zero : RGFInt := ofRGFNat RGFNat.zero
def one : RGFInt := ofRGFNat (RGFNat.succ RGFNat.zero)

def neg : RGFInt → RGFInt :=
  Quotient.lift (fun x => Quotient.mk _ ⟨x.neg, x.pos⟩)
    (fun a b (h : PreInt.Equiv a b) => by
      apply Quotient.sound; show PreInt.Equiv _ _
      unfold PreInt.Equiv at *
      rw [RGFNat.add_comm a.neg, RGFNat.add_comm b.neg]; exact h.symm)

def add : RGFInt → RGFInt → RGFInt :=
  Quotient.lift₂ (fun x y => Quotient.mk _ ⟨x.pos + y.pos, x.neg + y.neg⟩)
    (fun a₁ b₁ a₂ b₂ (h1 : PreInt.Equiv a₁ a₂) (h2 : PreInt.Equiv b₁ b₂) => by
      apply Quotient.sound; show PreInt.Equiv _ _
      unfold PreInt.Equiv at *
      calc (a₁.pos + b₁.pos) + (a₂.neg + b₂.neg)
          = (a₁.pos + a₂.neg) + (b₁.pos + b₂.neg) := by ring
        _ = (a₂.pos + a₁.neg) + (b₂.pos + b₁.neg) := by rw [h1, h2]
        _ = (a₂.pos + b₂.pos) + (a₁.neg + b₁.neg) := by ring)

/-! ## Well-definedness of multiplication -/

private theorem mul_wd_left (a₁ a₂ b : PreInt) (h : PreInt.Equiv a₁ a₂) :
    PreInt.Equiv
      ⟨a₁.pos * b.pos + a₁.neg * b.neg, a₁.pos * b.neg + a₁.neg * b.pos⟩
      ⟨a₂.pos * b.pos + a₂.neg * b.neg, a₂.pos * b.neg + a₂.neg * b.pos⟩ := by
  unfold PreInt.Equiv at *
  have e1 : (a₁.pos + a₂.neg) * b.pos = (a₂.pos + a₁.neg) * b.pos := by rw [h]
  have e2 : (a₁.pos + a₂.neg) * b.neg = (a₂.pos + a₁.neg) * b.neg := by rw [h]
  rw [add_mul, add_mul] at e1 e2
  have e4 := congr (congr_arg HAdd.hAdd e1) e2.symm
  calc (a₁.pos * b.pos + a₁.neg * b.neg) + (a₂.pos * b.neg + a₂.neg * b.pos)
      = (a₁.pos * b.pos + a₂.neg * b.pos) + (a₂.pos * b.neg + a₁.neg * b.neg) := by ring
    _ = (a₂.pos * b.pos + a₁.neg * b.pos) + (a₁.pos * b.neg + a₂.neg * b.neg) := e4
    _ = (a₂.pos * b.pos + a₂.neg * b.neg) + (a₁.pos * b.neg + a₁.neg * b.pos) := by ring

private theorem mul_wd_right (a b₁ b₂ : PreInt) (h : PreInt.Equiv b₁ b₂) :
    PreInt.Equiv
      ⟨a.pos * b₁.pos + a.neg * b₁.neg, a.pos * b₁.neg + a.neg * b₁.pos⟩
      ⟨a.pos * b₂.pos + a.neg * b₂.neg, a.pos * b₂.neg + a.neg * b₂.pos⟩ := by
  unfold PreInt.Equiv at *
  have e1 : a.pos * (b₁.pos + b₂.neg) = a.pos * (b₂.pos + b₁.neg) := by rw [h]
  have e2 : a.neg * (b₁.pos + b₂.neg) = a.neg * (b₂.pos + b₁.neg) := by rw [h]
  rw [mul_add, mul_add] at e1 e2
  have e4 := congr (congr_arg HAdd.hAdd e1) e2.symm
  calc (a.pos * b₁.pos + a.neg * b₁.neg) + (a.pos * b₂.neg + a.neg * b₂.pos)
      = (a.pos * b₁.pos + a.pos * b₂.neg) + (a.neg * b₂.pos + a.neg * b₁.neg) := by ring
    _ = (a.pos * b₂.pos + a.pos * b₁.neg) + (a.neg * b₁.pos + a.neg * b₂.neg) := e4
    _ = (a.pos * b₂.pos + a.neg * b₂.neg) + (a.pos * b₁.neg + a.neg * b₁.pos) := by ring

def mul : RGFInt → RGFInt → RGFInt :=
  Quotient.lift₂ (fun x y => Quotient.mk _
    ⟨x.pos * y.pos + x.neg * y.neg, x.pos * y.neg + x.neg * y.pos⟩)
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound
      (PreInt.equiv_trans (mul_wd_left a₁ a₂ b₁ h1) (mul_wd_right a₂ b₁ b₂ h2)))

instance : Zero RGFInt where zero := zero
instance : One RGFInt where one := one
instance : Add RGFInt where add := add
instance : Neg RGFInt where neg := neg
instance : Mul RGFInt where mul := mul
instance : Sub RGFInt where sub a b := a + (-b)

/-! ## Algebraic properties -/

theorem add_comm (a b : RGFInt) : a + b = b + a := by
  induction a using Quotient.ind with | _ a => ?_
  induction b using Quotient.ind with | _ b => ?_
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv; ring

theorem add_assoc (a b c : RGFInt) : a + b + c = a + (b + c) := by
  induction a using Quotient.ind with | _ a => ?_
  induction b using Quotient.ind with | _ b => ?_
  induction c using Quotient.ind with | _ c => ?_
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv; ring

theorem zero_add (a : RGFInt) : 0 + a = a := by
  induction a using Quotient.ind with | _ a => ?_
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv; simp [RGFNat.zero_add]

theorem add_zero (a : RGFInt) : a + 0 = a := by rw [add_comm]; exact zero_add a

theorem add_neg_cancel (a : RGFInt) : a + (-a) = 0 := by
  induction a using Quotient.ind with | _ a => ?_
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv; ring

theorem neg_add_cancel (a : RGFInt) : (-a) + a = 0 := by
  rw [add_comm]; exact add_neg_cancel a

theorem mul_comm (a b : RGFInt) : a * b = b * a := by
  induction a using Quotient.ind with | _ a => ?_
  induction b using Quotient.ind with | _ b => ?_
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv; ring

theorem one_mul (a : RGFInt) : 1 * a = a := by
  induction a using Quotient.ind with | _ a => ?_
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv
  simp [RGFNat.one_mul, RGFNat.zero_mul, RGFNat.add_zero]

theorem mul_one (a : RGFInt) : a * 1 = a := by rw [mul_comm]; exact one_mul a

theorem mul_assoc (a b c : RGFInt) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind with | _ a => ?_
  induction b using Quotient.ind with | _ b => ?_
  induction c using Quotient.ind with | _ c => ?_
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv; ring

theorem mul_add (a b c : RGFInt) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind with | _ a => ?_
  induction b using Quotient.ind with | _ b => ?_
  induction c using Quotient.ind with | _ c => ?_
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv; ring

theorem add_mul (a b c : RGFInt) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

instance : AddCommGroup RGFInt where
  add := add; add_assoc := add_assoc; zero := zero
  zero_add := zero_add; add_zero := add_zero
  neg := neg; add_comm := add_comm; neg_add_cancel := neg_add_cancel
  nsmul := nsmulRec; zsmul := zsmulRec

private theorem zero_mul' (a : RGFInt) : 0 * a = 0 := by
  induction a using Quotient.ind with | _ a => ?_
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv
  simp [RGFNat.zero_mul, RGFNat.add_zero]

private theorem mul_zero' (a : RGFInt) : a * 0 = 0 := by
  rw [mul_comm]; exact zero_mul' a

instance : CommRing RGFInt where
  mul := mul; mul_assoc := mul_assoc; one := one
  one_mul := one_mul; mul_one := mul_one; mul_comm := mul_comm
  left_distrib := mul_add; right_distrib := add_mul
  zero_mul := zero_mul'; mul_zero := mul_zero'; npow := npowRec

/-! ## ofRGFNat preserves operations -/

theorem ofRGFNat_add (a b : RGFNat) : ofRGFNat (a + b) = ofRGFNat a + ofRGFNat b := by
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv; simp [RGFNat.add_zero]

theorem ofRGFNat_mul (a b : RGFNat) : ofRGFNat (a * b) = ofRGFNat a * ofRGFNat b := by
  apply Quotient.sound; show PreInt.Equiv _ _; unfold PreInt.Equiv
  simp [RGFNat.zero_mul, RGFNat.mul_zero, RGFNat.add_zero]

end RGFInt
end RGF
