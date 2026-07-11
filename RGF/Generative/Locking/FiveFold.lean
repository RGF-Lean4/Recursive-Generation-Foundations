/-
  Layer four: cyclotomic fields and five-fold structure
  Cyclotomic Theory and Five-fold Structure
-/

import Mathlib

open scoped BigOperators Polynomial
open Finset ZMod

-- ============================================================
-- Basic properties of Z/5Z
-- ============================================================

theorem five_prime : Nat.Prime 5 := by decide

theorem zmod5_units_card : Fintype.card (ZMod 5)ˣ = 4 := by
  rw [ZMod.card_units_eq_totient]
  decide

theorem zmod5_nonzero_count :
    (Finset.univ.filter (fun x : ZMod 5 => x ≠ 0)).card = 4 := by
  decide

-- ============================================================
-- The fifth cyclotomic polynomial
-- ============================================================

noncomputable def cyclotomic5 : Polynomial ℤ := Polynomial.cyclotomic 5 ℤ

theorem cyclotomic5_degree : (Polynomial.cyclotomic 5 ℤ).natDegree = 4 := by
  rw [Polynomial.natDegree_cyclotomic]
  decide

theorem cyclotomic5_monic : (Polynomial.cyclotomic 5 ℤ).Monic :=
  Polynomial.cyclotomic.monic 5 ℤ

theorem cyclotomic5_irreducible : Irreducible (Polynomial.cyclotomic 5 ℚ) :=
  Polynomial.cyclotomic.irreducible_rat (n := 5) (by omega)

-- ============================================================
-- Algebraic connection with five-fold locking
-- ============================================================

theorem totient_5_is_power_of_two : ∃ m : ℕ, Nat.totient 5 = 2 ^ m := by
  use 2; decide

theorem cyclotomic_extension_degree_5 : Nat.totient 5 = 4 := by decide

theorem cyclotomic_extension_degree_3 : Nat.totient 3 = 2 := by decide

theorem five_minimal_totient_ge_4 :
    ∀ p : ℕ, Nat.Prime p → p % 2 = 1 → p < 5 → Nat.totient p < 4 := by
  intro p hp hodd hlt
  have : p = 3 := by
    have h2 := hp.two_le
    interval_cases p <;> simp_all
  subst this; decide

theorem totient_prime_eq (p : ℕ) (hp : Nat.Prime p) :
    Nat.totient p = p - 1 :=
  Nat.totient_prime hp

theorem five_half_dim : (5 - 1) / 2 = 2 := by decide

theorem totient_7_not_power_of_two :
    ¬ ∃ m : ℕ, m < 10 ∧ Nat.totient 7 = 2 ^ m := by decide
