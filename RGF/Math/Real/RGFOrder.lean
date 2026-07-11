/-
  Foundations/RGFOrder.lean

  Order, absolute value and the "smallness" predicate on RGFRat.

  The RGF number types (RGFNat, RGFInt, RGFRat) are defined from scratch in the
  preceding files. In this file we equip them with:

  * order-preserving ring homomorphisms to the standard `ℤ` / `ℚ`
    (`RGFInt.toInt`, `RGFRat.toRat`), shown to be bijective;
  * a native order `≤`, absolute value `RGFRat.abs`, and the smallness predicate
    `RGFRat.isSmall q n`, meaning `|q| ≤ 1 / (n + 1)`;
  * a transfer lemma `RGFRat.isSmall_iff` reducing smallness to an inequality in `ℚ`.

  The *definitions* of the number types stay independent of Mathlib's `ℤ`/`ℚ`;
  the standard types are used only to give short, reliable proofs of the analytic
  facts (this is mathematically equivalent to native proofs through the proven
  ring isomorphisms).
-/
import Mathlib
import RGF.Math.Real.RGFRat

namespace RGF

open RGFNat RGFInt RGFRat

/-! ## RGFNat → ℕ homomorphism facts -/

namespace RGFNat

theorem toNat_add (a b : RGFNat) : (a + b).toNat = a.toNat + b.toNat := by
  induction b with
  | zero => rfl
  | succ n ih => show (a + n).toNat + 1 = a.toNat + (n.toNat + 1); rw [ih]; omega

theorem toNat_mul (a b : RGFNat) : (a * b).toNat = a.toNat * b.toNat := by
  induction b with
  | zero => rfl
  | succ n ih =>
    show (a * n + a).toNat = a.toNat * (n.toNat + 1)
    rw [toNat_add, ih]; ring

theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  have := ofNat_toNat a
  rw [h, ofNat_toNat] at this
  exact this.symm

theorem toNat_le {a b : RGFNat} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  constructor
  · rintro ⟨k, rfl⟩; rw [toNat_add]; omega
  · intro h
    refine ⟨ofNat' (b.toNat - a.toNat), ?_⟩
    apply toNat_injective
    rw [toNat_add, toNat_ofNat]; omega

theorem toNat_succ (a : RGFNat) : (succ a).toNat = a.toNat + 1 := rfl

end RGFNat

/-! ## RGFInt → ℤ homomorphism -/

namespace RGFInt

/-- The canonical map `RGFInt → ℤ`. -/
def toInt : RGFInt → ℤ :=
  Quotient.lift (fun x : PreInt => (x.pos.toNat : ℤ) - (x.neg.toNat : ℤ))
    (by
      intro a b (h : PreInt.Equiv a b)
      unfold PreInt.Equiv at h
      have := congrArg RGFNat.toNat h
      rw [RGFNat.toNat_add, RGFNat.toNat_add] at this
      push_cast
      omega)

@[simp] theorem toInt_mk (p : PreInt) :
    toInt (Quotient.mk _ p) = (p.pos.toNat : ℤ) - (p.neg.toNat : ℤ) := rfl

theorem toInt_ofRGFNat (n : RGFNat) : toInt (ofRGFNat n) = (n.toNat : ℤ) := by
  show (n.toNat : ℤ) - (RGFNat.zero.toNat : ℤ) = _
  simp [RGFNat.toNat]

theorem toInt_zero : toInt 0 = 0 := rfl
theorem toInt_one : toInt 1 = 1 := rfl

theorem toInt_add (a b : RGFInt) : toInt (a + b) = toInt a + toInt b := by
  induction a using Quotient.ind with | _ a => ?_
  induction b using Quotient.ind with | _ b => ?_
  show toInt (Quotient.mk _ ⟨a.pos + b.pos, a.neg + b.neg⟩) = _
  simp only [toInt_mk, RGFNat.toNat_add]; push_cast; ring

theorem toInt_neg (a : RGFInt) : toInt (-a) = - toInt a := by
  induction a using Quotient.ind with | _ a => ?_
  show toInt (Quotient.mk _ ⟨a.neg, a.pos⟩) = _
  simp only [toInt_mk]; ring

theorem toInt_mul (a b : RGFInt) : toInt (a * b) = toInt a * toInt b := by
  induction a using Quotient.ind with | _ a => ?_
  induction b using Quotient.ind with | _ b => ?_
  show toInt (Quotient.mk _ ⟨a.pos * b.pos + a.neg * b.neg, a.pos * b.neg + a.neg * b.pos⟩) = _
  simp only [toInt_mk, RGFNat.toNat_add, RGFNat.toNat_mul]; push_cast; ring

/-- The ring homomorphism `RGFInt →+* ℤ`. -/
def toIntHom : RGFInt →+* ℤ where
  toFun := toInt
  map_one' := toInt_one
  map_mul' := toInt_mul
  map_zero' := toInt_zero
  map_add' := toInt_add

theorem toInt_injective : Function.Injective toInt := by
  intro a b
  induction a using Quotient.ind with | _ a => ?_
  induction b using Quotient.ind with | _ b => ?_
  intro h
  simp only [toInt_mk] at h
  apply Quotient.sound
  show PreInt.Equiv a b
  unfold PreInt.Equiv
  apply RGFNat.toNat_injective
  rw [RGFNat.toNat_add, RGFNat.toNat_add]
  omega

theorem toInt_intCast (z : ℤ) : toInt (z : RGFInt) = z := by
  have : toIntHom.comp (Int.castRingHom RGFInt) = Int.castRingHom ℤ :=
    RingHom.ext_int _ _
  exact congrArg (fun f => f z) this

theorem toInt_surjective : Function.Surjective toInt :=
  fun z => ⟨(z : RGFInt), toInt_intCast z⟩

end RGFInt

/-! ## RGFRat → ℚ homomorphism -/

namespace RGFRat

/-- The canonical map `RGFRat → ℚ`, sending `num / (den+1)` to the rational
    `toInt num / (den+1)`. -/
def toRat : RGFRat → ℚ :=
  Quotient.lift (fun x : PreRat => (RGFInt.toInt x.num : ℚ) / ((x.den.toNat : ℚ) + 1))
    (by
      intro a b (h : PreRat.Equiv a b)
      unfold PreRat.Equiv PreRat.denomInt PreRat.denom at h
      have h2 := congrArg RGFInt.toInt h
      rw [RGFInt.toInt_mul, RGFInt.toInt_mul, RGFInt.toInt_ofRGFNat,
        RGFInt.toInt_ofRGFNat, RGFNat.toNat_succ, RGFNat.toNat_succ] at h2
      rw [div_eq_div_iff (by positivity) (by positivity)]
      exact_mod_cast h2)

@[simp] theorem toRat_mk (p : PreRat) :
    toRat (Quotient.mk _ p) = (RGFInt.toInt p.num : ℚ) / ((p.den.toNat : ℚ) + 1) := rfl

theorem toRat_ofRGFInt (n : RGFInt) : toRat (ofRGFInt n) = (RGFInt.toInt n : ℚ) := by
  show (RGFInt.toInt n : ℚ) / ((RGFNat.zero.toNat : ℚ) + 1) = _
  simp [RGFNat.toNat]

theorem toRat_zero : toRat 0 = 0 := by
  rw [show (0 : RGFRat) = ofRGFInt RGFInt.zero from rfl, toRat_ofRGFInt,
    show RGFInt.toInt RGFInt.zero = 0 from rfl]
  norm_num

theorem toRat_one : toRat 1 = 1 := by
  rw [show (1 : RGFRat) = ofRGFInt RGFInt.one from rfl, toRat_ofRGFInt,
    show RGFInt.toInt RGFInt.one = 1 from rfl]
  norm_num

theorem toRat_add (a b : RGFRat) : toRat (a + b) = toRat a + toRat b := by
  unfold RGFRat.toRat;
  induction a using Quotient.ind ; induction b using Quotient.ind ; simp_all +decide;
  erw [ Quotient.lift_mk ];
  rw [ div_add_div, div_eq_div_iff ] <;> norm_cast <;> simp_all +decide [ PreRat.denomInt, PreRat.denom ];
  rw [ RGFNat.predSuccMul ];
  simp +decide [ RGFInt.toInt_mul, RGFInt.toInt_add, RGFNat.toNat_add, RGFNat.toNat_mul, RGFNat.toNat_succ ] ; ring;
  simp +decide [ RGFInt.toInt_ofRGFNat, RGFNat.toNat_succ ] ; ring

theorem toRat_neg (a : RGFRat) : toRat (neg a) = - toRat a := by
  obtain ⟨a⟩ := a;
  convert show ( RGFInt.toInt ( -a.num ) : ℚ ) / ( a.den.toNat + 1 ) = -toRat ( Quot.mk ( PreRat.preRatSetoid ) a ) from ?_ using 1;
  rw [ show ( -a.num ).toInt = -a.num.toInt from RGFInt.toInt_neg _ ] ; push_cast ; ring!;
  erw [ toRat_mk ] ; ring

theorem toRat_mul (a b : RGFRat) : toRat (a * b) = toRat a * toRat b := by
  induction a using Quotient.ind ; induction b using Quotient.ind ; simp +decide [ * ];
  convert toRat_mk _ using 1;
  rw [ div_mul_div_comm, div_eq_div_iff ] <;> norm_cast <;> simp +decide [ RGFNat.predSuccMul ] ; ring;
  simp +decide [ RGFInt.toInt_mul, RGFNat.toNat_add, RGFNat.toNat_mul, RGFNat.toNat_succ ] ; ring

theorem toRat_sub (a b : RGFRat) : toRat (a - b) = toRat a - toRat b := by
  show toRat (a + neg b) = _
  rw [toRat_add, toRat_neg]; ring

theorem toRat_injective : Function.Injective toRat := by
  intro a b h
  induction a using Quotient.ind with | _ a => ?_
  induction b using Quotient.ind with | _ b => ?_;
  rw [ toRat_mk, toRat_mk ] at h;
  rw [ div_eq_div_iff ] at h <;> norm_cast at *;
  apply Quotient.sound;
  exact RGFInt.toInt_injective <| by simpa [ RGFInt.toInt_mul, RGFInt.toInt_ofRGFNat, PreRat.denomInt, PreRat.denom, RGFNat.toNat_succ ] using h;

theorem toRat_surjective : Function.Surjective toRat := by
  intro q
  use Quotient.mk _ ⟨(q.num : RGFInt), RGFNat.ofNat' (q.den - 1)⟩
  simp [toRat_mk, RGFInt.toInt_intCast, RGFNat.toNat_ofNat];
  rw [ Nat.cast_sub q.pos, Nat.cast_one, sub_add_cancel, q.num_div_den ]

/-- A chosen right inverse of `toRat`. -/
def ofRat (q : ℚ) : RGFRat := Quotient.mk _ ⟨(q.num : RGFInt), RGFNat.ofNat' (q.den - 1)⟩

@[simp] theorem toRat_ofRat (q : ℚ) : toRat (ofRat q) = q := by
  unfold ofRat
  simp [toRat_mk, RGFInt.toInt_intCast, RGFNat.toNat_ofNat]
  rw [ Nat.cast_sub q.pos, Nat.cast_one, sub_add_cancel, q.num_div_den ]

/-! ## Native order, absolute value and smallness -/

/-- Order on `RGFRat`, transported from `ℚ`. -/
def le (a b : RGFRat) : Prop := toRat a ≤ toRat b

instance : LE RGFRat where le := le

theorem le_def (a b : RGFRat) : a ≤ b ↔ toRat a ≤ toRat b := Iff.rfl

open Classical in
/-- Absolute value on `RGFRat`. -/
noncomputable def abs (q : RGFRat) : RGFRat := if (0 : RGFRat) ≤ q then q else neg q

theorem toRat_abs (q : RGFRat) : toRat (abs q) = |toRat q| := by
  unfold abs
  by_cases h : (0 : RGFRat) ≤ q
  · rw [if_pos h]
    rw [le_def, toRat_zero] at h
    rw [abs_of_nonneg h]
  · rw [if_neg h]
    rw [le_def, toRat_zero, not_le] at h
    rw [toRat_neg, abs_of_neg h]

/-- The rational `1 / (n + 1)` in `RGFRat`. -/
def oneDivSucc (n : RGFNat) : RGFRat := Quotient.mk _ ⟨RGFInt.one, n⟩

theorem toRat_oneDivSucc (n : RGFNat) : toRat (oneDivSucc n) = 1 / ((n.toNat : ℚ) + 1) := by
  show (RGFInt.toInt RGFInt.one : ℚ) / ((n.toNat : ℚ) + 1) = _
  rw [show RGFInt.toInt RGFInt.one = 1 from rfl]; norm_num

/-- `|q| ≤ 1 / (n + 1)`. -/
def isSmall (q : RGFRat) (n : RGFNat) : Prop := abs q ≤ oneDivSucc n

theorem isSmall_iff (q : RGFRat) (n : RGFNat) :
    isSmall q n ↔ |toRat q| ≤ 1 / ((n.toNat : ℚ) + 1) := by
  unfold isSmall
  rw [le_def, toRat_abs, toRat_oneDivSucc]

end RGFRat

end RGF