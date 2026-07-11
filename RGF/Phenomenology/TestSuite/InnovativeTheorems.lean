import Mathlib
import RGF.Math.Algebra.A5Simple

/-!
# Innovative theorems (RGF framework): group theory and combinatorial geometry
# of the "locking number" 5

## §1 Group-theoretic essence of the locking number `k = 5`
* `alternatingGroup_five_isSimple` — `A₅` is simple.
* `alternatingGroup_five_card` — `|A₅| = 60`.
* `k5_simple_group_of_order_sixty` — `A₅` is a simple group of order 60.

## §2 Symmetric group
* `symmetricGroup_five_card` — `|S₅| = 120`.
* `symm_eq_two_mul_alt` — `120 = 2·60`.

## §3 Binary-choice numbers
* `choose_4_2`, `choose_5_2`, `choose_6_2`, `choose_8_2`, `framework_binomial_pairs`
  — `C(4,2)=6`, `C(5,2)=10`, `C(6,2)=15`, `C(8,2)=28`.

## §4 Sums of squares / cubes and Nicomachus
* `hetu_total_eq_sum_squares` — `55 = 1²+2²+3²+4²+5²`.
* `sum_cubes_1_3`, `nicomachus_six`, `nicomachus_identity`
  — `(1+2+3)² = 1³+2³+3³ = 36 = 6²`.

## §5 Icosahedron / dodecahedron and Euler characteristic
* `icosahedron_euler`, `dodecahedron_euler`, `icosa_dodeca_dual` — `V−E+F = 2`.

## §6 Primality complement for `k = 5`
* `k5_mod_four` — `5 ≡ 1 (mod 4)`.
* `k5_sum_two_squares` — `5 = 1²+2²`.
* `k5_fermat_two_squares` — `5` is a sum of two squares (Fermat two-square theorem).

## §7 Master statement
* `innovative_master`.
-/

namespace RGF.Innovative

open Equiv

/-! ### §1 Group theory of the locking number 5 -/

/-- `A₅` is a simple group. -/
theorem alternatingGroup_five_isSimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  A5_isSimpleGroup

/-- The order of `A₅` is `60`. -/
theorem alternatingGroup_five_card : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  decide

/-- `A₅` is a simple group of order `60`. -/
theorem k5_simple_group_of_order_sixty :
    IsSimpleGroup (alternatingGroup (Fin 5)) ∧ Fintype.card (alternatingGroup (Fin 5)) = 60 :=
  ⟨alternatingGroup_five_isSimple, alternatingGroup_five_card⟩

/-! ### §2 Symmetric group -/

/-- The order of `S₅` is `120`. -/
theorem symmetricGroup_five_card : Fintype.card (Equiv.Perm (Fin 5)) = 120 := by
  simp [Fintype.card_perm, Fintype.card_fin]; rfl

/-- `|S₅| = 2·|A₅|`: the alternating group has index `2` in the symmetric group. -/
theorem symm_eq_two_mul_alt :
    Fintype.card (Equiv.Perm (Fin 5)) = 2 * Fintype.card (alternatingGroup (Fin 5)) := by
  rw [symmetricGroup_five_card, alternatingGroup_five_card]

/-! ### §3 Binary-choice numbers -/

theorem choose_4_2 : Nat.choose 4 2 = 6 := by decide
theorem choose_5_2 : Nat.choose 5 2 = 10 := by decide
theorem choose_6_2 : Nat.choose 6 2 = 15 := by decide
theorem choose_8_2 : Nat.choose 8 2 = 28 := by decide

/-- The framework's characteristic pair-counts `6, 10, 15, 28 = C(n,2)`. -/
theorem framework_binomial_pairs :
    Nat.choose 4 2 = 6 ∧ Nat.choose 5 2 = 10 ∧ Nat.choose 6 2 = 15 ∧ Nat.choose 8 2 = 28 :=
  ⟨choose_4_2, choose_5_2, choose_6_2, choose_8_2⟩

/-! ### §4 Sums of squares / cubes and Nicomachus -/

/-- The "river chart" total `55 = 1²+2²+3²+4²+5²`. -/
theorem hetu_total_eq_sum_squares : (∑ k ∈ Finset.Icc 1 5, k ^ 2) = 55 := by decide

/-- `1³+2³+3³ = 36`. -/
theorem sum_cubes_1_3 : 1 ^ 3 + 2 ^ 3 + 3 ^ 3 = 36 := by norm_num

/-- `6² = 36`. -/
theorem nicomachus_six : 6 ^ 2 = 36 := by norm_num

/-- Nicomachus: `(1+2+3)² = 1³+2³+3³ = 6² = 36`. -/
theorem nicomachus_identity :
    (1 + 2 + 3) ^ 2 = 1 ^ 3 + 2 ^ 3 + 3 ^ 3 ∧ 1 ^ 3 + 2 ^ 3 + 3 ^ 3 = 36 ∧ (36 : ℕ) = 6 ^ 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### §5 Icosahedron / dodecahedron and Euler characteristic -/

/-- Euler characteristic of the icosahedron: `V−E+F = 12−30+20 = 2`. -/
theorem icosahedron_euler : (12 : ℤ) - 30 + 20 = 2 := by norm_num

/-- Euler characteristic of the dodecahedron: `V−E+F = 20−30+12 = 2`. -/
theorem dodecahedron_euler : (20 : ℤ) - 30 + 12 = 2 := by norm_num

/-- Icosahedron–dodecahedron duality: swapping `V ↔ F` (12↔20) preserves the
Euler characteristic, and both equal `2`. -/
theorem icosa_dodeca_dual :
    (12 : ℤ) - 30 + 20 = 2 ∧ (20 : ℤ) - 30 + 12 = 2
      ∧ ((12 : ℤ) - 30 + 20 = (20 : ℤ) - 30 + 12) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### §6 Primality complement for k = 5 -/

/-- `5 ≡ 1 (mod 4)`. -/
theorem k5_mod_four : 5 % 4 = 1 := by norm_num

/-- `5 = 1² + 2²`. -/
theorem k5_sum_two_squares : 5 = 1 ^ 2 + 2 ^ 2 := by norm_num

/-- By Fermat's two-square theorem (`5` prime, `5 % 4 ≠ 3`), `5` is a sum of two
squares. -/
theorem k5_fermat_two_squares : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (by decide)

/-! ### §7 Master statement -/

/-- Master statement combining the five strands. -/
theorem innovative_master :
    IsSimpleGroup (alternatingGroup (Fin 5))
    ∧ Fintype.card (alternatingGroup (Fin 5)) = 60
    ∧ Fintype.card (Equiv.Perm (Fin 5)) = 120
    ∧ (Nat.choose 4 2 = 6 ∧ Nat.choose 5 2 = 10 ∧ Nat.choose 6 2 = 15 ∧ Nat.choose 8 2 = 28)
    ∧ (∑ k ∈ Finset.Icc 1 5, k ^ 2) = 55
    ∧ ((1 + 2 + 3) ^ 2 = 1 ^ 3 + 2 ^ 3 + 3 ^ 3)
    ∧ ((12 : ℤ) - 30 + 20 = 2 ∧ (20 : ℤ) - 30 + 12 = 2)
    ∧ (∃ a b : ℕ, a ^ 2 + b ^ 2 = 5) := by
  exact ⟨alternatingGroup_five_isSimple, alternatingGroup_five_card, symmetricGroup_five_card,
    framework_binomial_pairs, hetu_total_eq_sum_squares, (nicomachus_identity).1,
    ⟨icosahedron_euler, dodecahedron_euler⟩, k5_fermat_two_squares⟩

end RGF.Innovative
