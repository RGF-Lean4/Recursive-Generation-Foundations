/-
  Foundations/RGFNat.lean

  RGF natural numbers: an inductive definition starting from zero.
  Fully independent of Lean's built-in Nat; addition, multiplication, the order relation, and their algebraic properties are all built from scratch.

  Dependency note: import Mathlib is used only for algebraic-structure type classes (CommSemiring, etc.).
  The core definitions and theorems do not depend on Mathlib's reals or analysis library.
-/
import Mathlib

namespace RGF

/-! ## Inductive definition -/

/-- RGF natural numbers: the inductive type of zero and successor. -/
inductive RGFNat where
  | zero : RGFNat
  | succ : RGFNat → RGFNat
  deriving DecidableEq

namespace RGFNat

/-! ## Addition -/

/-- Addition: recursive definition. -/
def add : RGFNat → RGFNat → RGFNat
  | a, zero => a
  | a, succ b => succ (add a b)

instance : Add RGFNat where add := add

theorem add_zero (a : RGFNat) : a + zero = a := rfl
theorem add_succ (a b : RGFNat) : a + succ b = succ (a + b) := rfl

theorem zero_add (a : RGFNat) : zero + a = a := by
  induction a with
  | zero => rfl
  | succ n ih => show succ (zero + n) = succ n; rw [ih]

theorem succ_add (a b : RGFNat) : succ a + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ n ih => show succ (succ a + n) = succ (succ (a + n)); rw [ih]

theorem add_comm (a b : RGFNat) : a + b = b + a := by
  induction b with
  | zero => show a = zero + a; rw [zero_add]
  | succ n ih => show succ (a + n) = succ n + a; rw [succ_add, ih]

theorem add_assoc (a b c : RGFNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ n ih => show succ (a + b + n) = succ (a + (b + n)); rw [ih]

/-! ## Cancellation law for addition -/

theorem succ_inj {a b : RGFNat} (h : succ a = succ b) : a = b :=
  RGFNat.succ.inj h

theorem succ_ne_zero (a : RGFNat) : succ a ≠ zero :=
  fun h => RGFNat.noConfusion h

theorem add_left_cancel (a b c : RGFNat) (h : a + b = a + c) : b = c := by
  induction a with
  | zero => rwa [zero_add, zero_add] at h
  | succ n ih => rw [succ_add, succ_add] at h; exact ih (succ_inj h)

theorem add_right_cancel (a b c : RGFNat) (h : a + c = b + c) : a = b := by
  rw [add_comm a c, add_comm b c] at h; exact add_left_cancel c a b h

theorem add_eq_zero {a b : RGFNat} (h : a + b = zero) : a = zero ∧ b = zero := by
  cases b with
  | zero => exact ⟨h, rfl⟩
  | succ n => exact absurd h (succ_ne_zero _)

/-! ## Multiplication -/

/-- Multiplication: recursive definition. -/
def mul : RGFNat → RGFNat → RGFNat
  | _, zero => zero
  | a, succ b => mul a b + a

instance : Mul RGFNat where mul := mul

theorem mul_zero (a : RGFNat) : a * zero = zero := rfl
theorem mul_succ (a b : RGFNat) : a * succ b = a * b + a := rfl

theorem zero_mul (a : RGFNat) : zero * a = zero := by
  induction a with
  | zero => rfl
  | succ n ih => show zero * n + zero = zero; rw [add_zero, ih]

theorem succ_mul (a b : RGFNat) : succ a * b = a * b + b := by
  induction b with
  | zero => rfl
  | succ n ih =>
    show succ a * n + succ a = (a * n + a) + succ n
    rw [ih, add_succ, add_succ, add_assoc, add_assoc, add_comm n a]

theorem one_mul (a : RGFNat) : succ zero * a = a := by
  rw [succ_mul, zero_mul, zero_add]

theorem mul_one (a : RGFNat) : a * succ zero = a := by
  rw [mul_succ, mul_zero, zero_add]

theorem mul_comm (a b : RGFNat) : a * b = b * a := by
  induction b with
  | zero => show a * zero = zero * a; rw [mul_zero, zero_mul]
  | succ n ih => show a * n + a = succ n * a; rw [succ_mul, ih]

theorem mul_add (a b c : RGFNat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rfl
  | succ n ih =>
    show a * (b + n) + a = a * b + (a * n + a)
    rw [ih, add_assoc]

theorem add_mul (a b c : RGFNat) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

theorem mul_assoc (a b c : RGFNat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ n ih =>
    show a * b * n + a * b = a * (b * n + b)
    rw [ih, mul_add]

/-! ## Order relation -/

/-- Less than or equal. -/
def le (a b : RGFNat) : Prop := ∃ k, a + k = b

instance : LE RGFNat where le := le

theorem le_refl (a : RGFNat) : a ≤ a := ⟨zero, rfl⟩

theorem le_antisymm {a b : RGFNat} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  have : a + (k + j) = a + zero := by
    rw [← add_assoc, hk, hj, add_zero]
  have hkj := add_left_cancel a (k + j) zero this
  have := add_eq_zero hkj
  rw [this.1] at hk; rw [add_zero] at hk; exact hk

theorem le_trans {a b c : RGFNat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨k + j, by rw [← add_assoc, hk, hj]⟩

theorem zero_le (a : RGFNat) : zero ≤ a := ⟨a, zero_add a⟩

theorem succ_le_succ {a b : RGFNat} (h : a ≤ b) : succ a ≤ succ b := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [succ_add, hk]⟩

theorem le_of_succ_le_succ {a b : RGFNat} (h : succ a ≤ succ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := h
  rw [succ_add] at hk
  exact ⟨k, succ_inj hk⟩

theorem le_succ (a : RGFNat) : a ≤ succ a := ⟨succ zero, rfl⟩

theorem not_succ_le_zero (a : RGFNat) : ¬ succ a ≤ zero := by
  intro ⟨k, hk⟩; rw [succ_add] at hk; exact absurd hk (succ_ne_zero _)

theorem le_total (a b : RGFNat) : a ≤ b ∨ b ≤ a := by
  induction a generalizing b with
  | zero => left; exact zero_le b
  | succ n ih =>
    cases b with
    | zero => right; exact zero_le (succ n)
    | succ m =>
      rcases ih m with h | h
      · left; exact succ_le_succ h
      · right; exact succ_le_succ h

/-- Strictly less than. -/
def lt (a b : RGFNat) : Prop := succ a ≤ b

instance : LT RGFNat where lt := lt

/-- Decidable ≤. -/
def decLE : (a b : RGFNat) → Decidable (a ≤ b)
  | zero, b => isTrue (zero_le b)
  | succ _, zero => isFalse (not_succ_le_zero _)
  | succ n, succ m =>
    match decLE n m with
    | .isTrue h => isTrue (succ_le_succ h)
    | .isFalse h => isFalse (fun h2 => h (le_of_succ_le_succ h2))

instance : DecidableRel (· ≤ · : RGFNat → RGFNat → Prop) := decLE

/-! ## Conversion to the standard Nat -/

/-- Conversion to the standard Nat. -/
def toNat : RGFNat → Nat
  | zero => 0
  | succ n => n.toNat + 1

/-- Conversion from the standard Nat. -/
def ofNat' : Nat → RGFNat
  | 0 => zero
  | n + 1 => succ (ofNat' n)

theorem toNat_ofNat (n : Nat) : (ofNat' n).toNat = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [ofNat', toNat, ih]

theorem ofNat_toNat (n : RGFNat) : ofNat' n.toNat = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [toNat, ofNat', ih]

/-! ## OfNat instances -/

instance : OfNat RGFNat 0 where ofNat := zero
instance : OfNat RGFNat 1 where ofNat := succ zero

/-! ## Algebraic-structure instances -/

instance : CommMonoidWithZero RGFNat where
  mul := mul
  one := succ zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  zero := zero
  zero_mul := zero_mul
  mul_zero := fun _ => rfl
  npow := npowRec

instance : AddCommMonoid RGFNat where
  add := add
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add
  add_zero := fun _ => rfl
  add_comm := add_comm
  nsmul := nsmulRec

instance : CommSemiring RGFNat where
  left_distrib := mul_add
  right_distrib := add_mul

/-! ## Other important properties -/

theorem succ_ne_self (a : RGFNat) : succ a ≠ a := by
  induction a with
  | zero => exact succ_ne_zero zero
  | succ n ih => intro h; exact ih (succ_inj h)

theorem not_lt_zero (a : RGFNat) : ¬ lt a zero := by
  intro ⟨k, hk⟩
  rw [succ_add] at hk
  exact absurd hk (succ_ne_zero _)

theorem lt_succ_self (a : RGFNat) : lt a (succ a) :=
  le_refl (succ a)

theorem le_of_lt {a b : RGFNat} (h : lt a b) : a ≤ b :=
  le_trans (le_succ a) h

/-! ## max -/

def max (a b : RGFNat) : RGFNat := if a ≤ b then b else a

theorem le_max_left (a b : RGFNat) : a ≤ max a b := by
  unfold max; split
  · assumption
  · exact le_refl a

theorem le_max_right (a b : RGFNat) : b ≤ max a b := by
  unfold max; split
  · exact le_refl b
  · rename_i h; exact (le_total a b).elim (absurd · h) id

/-! ## predSuccMul helper (used by RGFRat) -/

/-- The predecessor of succ a * succ b, used for RGFRat denominator computations. -/
def predSuccMul (a b : RGFNat) : RGFNat :=
  succ a * b + a

theorem succ_mul_succ_eq (a b : RGFNat) :
    succ a * succ b = succ (predSuccMul a b) := by
  show succ a * b + succ a = succ (succ a * b + a)
  rw [add_succ]

/-! ## Explicit verification of the Peano axioms -/

/-- Peano 3: succ is injective. -/
theorem peano_succ_injective : ∀ a b : RGFNat, succ a = succ b → a = b := fun _ _ => succ_inj

/-- Peano 4: zero is not in the range of succ. -/
theorem peano_succ_ne_zero' : ∀ a : RGFNat, succ a ≠ zero := succ_ne_zero

/-- Peano 5: the induction principle. -/
theorem peano_induction (P : RGFNat → Prop) (h0 : P zero)
    (hs : ∀ n, P n → P (succ n)) : ∀ n, P n := by
  intro n; induction n with
  | zero => exact h0
  | succ k ih => exact hs k ih

end RGFNat
end RGF
