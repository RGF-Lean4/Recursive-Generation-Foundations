/-
  Foundations/RGFRat.lean

  RGF rationals: a fraction-pair construction based on RGFInt.
  (a, b) represents a / (succ b).

  Dependency note: import Mathlib is used for tactic support.
  The core definitions do not depend on Mathlib's reals or analysis library.
-/
import Mathlib
import RGF.Math.Real.RGFInt

namespace RGF

open RGFNat RGFInt

structure PreRat where
  num : RGFInt
  den : RGFNat

namespace PreRat

def denom (x : PreRat) : RGFNat := RGFNat.succ x.den
def denomInt (x : PreRat) : RGFInt := RGFInt.ofRGFNat x.denom

def Equiv (x y : PreRat) : Prop := x.num * y.denomInt = y.num * x.denomInt

theorem equiv_refl (x : PreRat) : Equiv x x := rfl
theorem equiv_symm {x y : PreRat} (h : Equiv x y) : Equiv y x := h.symm

theorem equiv_trans {x y z : PreRat} (h1 : Equiv x y) (h2 : Equiv y z) :
    Equiv x z := by
  unfold Equiv at *; (
  have h_cancel : ∀ (a b c : RGFInt), a * RGFInt.ofRGFNat (RGFNat.succ y.den) = b * RGFInt.ofRGFNat (RGFNat.succ y.den) → a = b := by
    intros a b c h
    have h_cancel : ∀ (a b : RGFNat), a * RGFNat.succ y.den = b * RGFNat.succ y.den → a = b := by
      intros a b hab
      have h_cancel : a.toNat * (y.den.toNat + 1) = b.toNat * (y.den.toNat + 1) := by
        convert congr_arg RGFNat.toNat hab using 1;
        · -- By definition of multiplication in RGFNat, we have that (a * b).toNat = a.toNat * b.toNat.
          have h_mul_toNat : ∀ (a b : RGFNat), (a * b).toNat = a.toNat * b.toNat := by
            intros a b; induction' b with b ih generalizing a; aesop;
            -- By definition of multiplication in RGFNat, we have that (a * b.succ).toNat = (a * b + a).toNat.
            have h_mul_succ : (a * b.succ).toNat = (a * b + a).toNat := by
              grind +suggestions;
            have h_add : ∀ (a b : RGFNat), (a + b).toNat = a.toNat + b.toNat := by
              intros a b; induction' b with b ih generalizing a; aesop;
              convert congr_arg ( · + 1 ) ( ih a ) using 1;
            aesop;
          exact h_mul_toNat _ _ ▸ rfl;
        · have h_mul : ∀ (a b : RGFNat), (a * b).toNat = a.toNat * b.toNat := by
            intros a b; induction' b with b ih generalizing a; aesop;
            -- By definition of multiplication in RGFNat, we have that (a * b.succ).toNat = (a * b + a).toNat.
            have h_mul_succ : (a * b.succ).toNat = (a * b + a).toNat := by
              grind +suggestions;
            have h_add : ∀ (a b : RGFNat), (a + b).toNat = a.toNat + b.toNat := by
              intros a b; induction' b with b ih generalizing a; aesop;
              convert congr_arg ( · + 1 ) ( ih a ) using 1;
            aesop;
          rw [ h_mul, show y.den.succ.toNat = y.den.toNat + 1 from rfl ];
      exact RGFNat.ofNat_toNat a ▸ RGFNat.ofNat_toNat b ▸ by aesop;
    induction' a using Quotient.inductionOn' with a;
    induction' b using Quotient.inductionOn' with b;
    erw [ Quotient.eq'' ] at *;
    simp +decide [ PreInt.preIntSetoid ] at *;
    simp +decide [ PreInt.Equiv ] at *;
    contrapose! h_cancel;
    use a.pos * 1 + b.neg * 1, b.pos * 1 + a.neg * 1;
    grind +suggestions;
  convert h_cancel _ _ _ _ using 1;
  · exact 0;
  · convert congr_arg ( · * z.denomInt ) h1 using 1;
    · rw [ mul_right_comm ];
      rfl;
    · convert congr_arg ( · * x.denomInt ) h2.symm using 1 <;> ring!)

instance preRatSetoid : Setoid PreRat where
  r := Equiv
  iseqv := ⟨equiv_refl, fun h => equiv_symm h, fun h1 h2 => equiv_trans h1 h2⟩

end PreRat

def RGFRat := Quotient PreRat.preRatSetoid

namespace RGFRat

def ofRGFInt (n : RGFInt) : RGFRat := Quotient.mk _ ⟨n, RGFNat.zero⟩
def ofRGFNat (n : RGFNat) : RGFRat := ofRGFInt (RGFInt.ofRGFNat n)
def zero : RGFRat := ofRGFInt RGFInt.zero
def one : RGFRat := ofRGFInt RGFInt.one

def neg : RGFRat → RGFRat :=
  Quotient.lift (fun x => Quotient.mk _ ⟨-x.num, x.den⟩)
    (fun a b (h : PreRat.Equiv a b) => by
      apply Quotient.sound; show PreRat.Equiv _ _
      unfold PreRat.Equiv PreRat.denomInt PreRat.denom at *
      convert congr_arg Neg.neg h using 1 <;> ring)

def add : RGFRat → RGFRat → RGFRat :=
  Quotient.lift₂
    (fun x y => Quotient.mk _
      ⟨x.num * y.denomInt + y.num * x.denomInt, RGFNat.predSuccMul x.den y.den⟩)
    (fun _ _ _ _ _ _ => by apply Quotient.sound; show PreRat.Equiv _ _; (
    rename_i a b c d h₁ h₂;
    have hadd : (a.num * b.denomInt + b.num * a.denomInt) * (c.denomInt * d.denomInt) = (c.num * d.denomInt + d.num * c.denomInt) * (a.denomInt * b.denomInt) := by
      have hadd : a.num * c.denomInt = c.num * a.denomInt ∧ b.num * d.denomInt = d.num * b.denomInt := by
        exact ⟨ h₁, h₂ ⟩;
      grind +ring;
    unfold PreRat.Equiv;
    convert hadd using 1 <;> ring;
    · simp +decide [ PreRat.denomInt, PreRat.denom ] ; ring;
      grind +suggestions;
    · unfold PreRat.denomInt; ring;
      unfold PreRat.denom; ring;
      grind +suggestions))

def mul : RGFRat → RGFRat → RGFRat :=
  Quotient.lift₂
    (fun x y => Quotient.mk _ ⟨x.num * y.num, RGFNat.predSuccMul x.den y.den⟩)
    (fun _ _ _ _ _ _ => by apply Quotient.sound; show PreRat.Equiv _ _; (
    rename_i a b c d h₁ h₂;
    have h_mul : a.num * c.denomInt = c.num * a.denomInt ∧ b.num * d.denomInt = d.num * b.denomInt := by
      exact ⟨ h₁, h₂ ⟩;
    have h_mul : (a.num * b.num) * (c.denomInt * d.denomInt) = (c.num * d.num) * (a.denomInt * b.denomInt) := by
      grind +ring;
    unfold PreRat.Equiv;
    convert h_mul using 1;
    · simp +decide [ PreRat.denomInt, PreRat.denom ] ; ring;
      grind +suggestions;
    · simp +decide [ PreRat.denomInt, PreRat.denom ] ; ring;
      grind +suggestions))

instance : Zero RGFRat where zero := zero
instance : One RGFRat where one := one
instance : Add RGFRat where add := add
instance : Neg RGFRat where neg := neg
instance : Mul RGFRat where mul := mul
instance : Sub RGFRat where sub a b := a + neg b

/-! ## Algebraic properties -/

theorem add_comm (a b : RGFRat) : a + b = b + a := by
  induction a using Quotient.ind; induction b using Quotient.ind
  apply Quotient.sound; show PreRat.Equiv _ _; (
  simp +decide [ PreRat.denomInt, PreRat.denom, RGFNat.predSuccMul ] ; ring;
  grind +suggestions)

theorem mul_comm (a b : RGFRat) : a * b = b * a := by
  induction a using Quotient.ind; induction b using Quotient.ind
  apply Quotient.sound; show PreRat.Equiv _ _; (
  unfold PreRat.Equiv PreRat.denomInt PreRat.denom RGFNat.predSuccMul; ring;
  grind +suggestions)

theorem zero_add (a : RGFRat) : 0 + a = a := by
  induction a using Quotient.ind
  apply Quotient.sound; show PreRat.Equiv _ _; (
  rename_i x; unfold PreRat.Equiv; simp +decide [ PreRat.denomInt, PreRat.denom, RGFNat.predSuccMul ] ; ring;
  erw [ show ( RGFNat.zero.succ : RGFNat ) = 1 from rfl ] ; ring!;
  erw [ show ( RGFInt.ofRGFNat 1 : RGFInt ) = 1 from rfl ] ; ring!;
  erw [ show ( RGFInt.zero : RGFInt ) = 0 from rfl ] ; ring!;)

theorem add_zero (a : RGFRat) : a + 0 = a := by rw [add_comm]; exact zero_add a

theorem one_mul (a : RGFRat) : 1 * a = a := by
  induction a using Quotient.ind
  apply Quotient.sound; show PreRat.Equiv _ _; (
  erw [ show RGFInt.one = 1 from rfl ] ; ring!;
  rename_i a; unfold PreRat.Equiv; simp +decide [ PreRat.denomInt, PreRat.denom, RGFNat.predSuccMul ] ;
  grind +suggestions)

theorem mul_one (a : RGFRat) : a * 1 = a := by rw [mul_comm]; exact one_mul a

theorem add_neg_cancel (a : RGFRat) : a + neg a = 0 := by
  induction a using Quotient.ind
  apply Quotient.sound; show PreRat.Equiv _ _; (
  simp [PreRat.denomInt, PreRat.denom];
  exact Eq.symm ( zero_mul _ ))

theorem neg_add_cancel (a : RGFRat) : neg a + a = 0 := by
  rw [add_comm]; exact add_neg_cancel a

theorem add_assoc (a b c : RGFRat) : a + b + c = a + (b + c) := by
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind; apply Quotient.sound; show PreRat.Equiv _ _; (unfold PreRat.Equiv; simp +decide [ PreRat.denomInt, PreRat.denom ] ; );
  have h_mul : ∀ (a b : RGFNat), RGFInt.ofRGFNat (a.succ) = RGFInt.ofRGFNat a + 1 := by
    aesop;
  simp_all +decide [ RGFNat.predSuccMul ];
  simp_all +decide [ RGFInt.ofRGFNat_add, RGFInt.ofRGFNat_mul ];
  grind

theorem mul_assoc (a b c : RGFRat) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind; apply Quotient.sound; show PreRat.Equiv _ _; (unfold PreRat.Equiv; simp +decide [ PreRat.denomInt, PreRat.denom ] ; );
  unfold RGFNat.predSuccMul; ring;
  grind +suggestions

theorem mul_add (a b c : RGFRat) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind; (apply Quotient.sound; show PreRat.Equiv _ _; (unfold PreRat.Equiv PreRat.denomInt PreRat.denom RGFNat.predSuccMul; ring;));
  have h_mul : ∀ (a b : RGFNat), RGFInt.ofRGFNat (a.succ) = RGFInt.ofRGFNat a + 1 := by
    aesop;
  simp_all +decide [ RGFInt.ofRGFNat_add, RGFInt.ofRGFNat_mul ] ; ring

theorem add_mul (a b c : RGFRat) : (a + b) * c = a * c + b * c := by
  -- We prove distributivity by reducing to `RGFInt` ring identities via `Quotient.ind` and `Quotient.sound`.
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind; (apply Quotient.sound; show PreRat.Equiv _ _; (unfold PreRat.Equiv PreRat.denomInt PreRat.denom RGFNat.predSuccMul; ring;));
  have h_mul : ∀ (a b : RGFNat), RGFInt.ofRGFNat (a.succ) = RGFInt.ofRGFNat a + 1 := by
    aesop
  simp_all +decide [ RGFInt.ofRGFNat_add, RGFInt.ofRGFNat_mul ] ; ring

theorem zero_mul (a : RGFRat) : 0 * a = 0 := by
  induction a using Quotient.ind;
  convert Quotient.sound ?_ using 1;
  rename_i x; exact Eq.symm ( by simp +decide [ show ( RGFInt.zero : RGFInt ) = 0 from rfl, show ( RGFNat.zero : RGFNat ) = 0 from rfl ] ) ;

theorem mul_zero (a : RGFRat) : a * 0 = 0 := by
  rw [mul_comm]; exact zero_mul a

/-- The native commutative-ring structure on `RGFRat`, derived from scratch
    (reducing each axiom to the `CommRing RGFInt` structure via `Quotient.sound`),
    without any transport through the standard rationals `ℚ`.

    This is bundled as `RGFRat.commRing` (rather than a global `instance`) to
    avoid perturbing the bespoke `Zero/One/Add/Neg/Mul/Sub` instances that the
    downstream Cauchy-sequence development relies on definitionally. -/
def commRing : CommRing RGFRat where
  add := add
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add
  add_zero := add_zero
  neg := neg
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  mul := mul
  mul_assoc := mul_assoc
  one := one
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := mul_add
  right_distrib := add_mul
  mul_comm := mul_comm
  zero_mul := zero_mul
  mul_zero := mul_zero
  nsmul := nsmulRec
  zsmul := zsmulRec

end RGFRat
end RGF