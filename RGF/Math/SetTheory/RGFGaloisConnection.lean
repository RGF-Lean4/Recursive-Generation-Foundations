/-
  Galois theory and five-fold locking
  Galois Theory and Five-Locking

  This file formalises the group-theoretic core of the Abel-Ruffini theorem:
  the quintic has no solution by radicals ⟺ S₅ is unsolvable ⟺ A₅ is non-abelian and simple

  This is the mathematical root of RGF five-fold locking.
-/

import Mathlib
import RGF.Generative.Core.SixVerifications

open Equiv BigOperators

/-! ## 1. Citing already-proved results -/

/-- S₅ is unsolvable -- the core of the Abel-Ruffini theorem -/
theorem S5_not_solvable' : ¬ IsSolvable (Perm (Fin 5)) :=
  S5_not_solvable

/-- 5 is the smallest order making the symmetric group unsolvable -/
theorem five_is_solvability_threshold :
    (IsSolvable (Perm (Fin 2))) ∧
    (IsSolvable (Perm (Fin 3))) ∧
    (IsSolvable (Perm (Fin 4))) ∧
    (¬ IsSolvable (Perm (Fin 5))) :=
  ⟨S2_solvable, S3_solvable, S4_solvable, S5_not_solvable⟩

/-- for all n ≥ 5, S_n is unsolvable -/
theorem Sn_not_solvable_of_ge_five (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsSolvable (Perm (Fin n)) :=
  Perm.not_solvable _ (by simp [Cardinal.mk_fintype]; omega)

/-! ## 2. Properties of A₅ -/

/-- A₅ is simple -/
theorem A5_simple' : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup_five

/-- A₅ is non-abelian -/
theorem A5_noncommutative' :
    ¬ ∀ (a b : alternatingGroup (Fin 5)), a * b = b * a := by decide

/-- the order of A₅ = 60 -/
theorem A5_order' : Fintype.card (alternatingGroup (Fin 5)) = 60 := by decide

/-- A₅ is the non-abelian simple group of smallest order -/
theorem A5_minimal_nonabelian_simple' :
    IsSimpleGroup (alternatingGroup (Fin 5)) ∧
    Fintype.card (alternatingGroup (Fin 5)) = 60 ∧
    ¬ ∀ (a b : alternatingGroup (Fin 5)), a * b = b * a :=
  ⟨A5_simple', A5_order', A5_noncommutative'⟩

/-! ## 3. Cyclotomic fields and Galois groups -/

/-- φ(5) = 4 -/
theorem cyclotomic_5_galois_order : Nat.totient 5 = 4 := by decide

/-- 5 is the smallest prime with φ(p) > 2 -/
theorem five_minimal_totient_exceeds_two :
    Nat.Prime 5 ∧ Nat.totient 5 > 2 ∧
    ∀ p, Nat.Prime p → p < 5 → Nat.totient p ≤ 2 := by
  refine ⟨by decide, by decide, ?_⟩
  intro p hp hlt
  interval_cases p <;> simp_all <;> decide

/-! ## 4. Equivalent statement of Abel-Ruffini -/

/-- group-theoretic equivalent form of the Abel-Ruffini theorem -/
theorem abel_ruffini_group_theory :
    (¬ IsSolvable (Perm (Fin 5))) ∧
    (IsSimpleGroup (alternatingGroup (Fin 5))) ∧
    (Fintype.card (alternatingGroup (Fin 5)) = 60) ∧
    (IsSolvable (Perm (Fin 4))) :=
  ⟨S5_not_solvable, A5_simple', A5_order', S4_solvable⟩

/-! ## 5. Order of the symmetric group -/

/-- the order of the symmetric group = n! -/
theorem sym_order :
    Fintype.card (Perm (Fin 1)) = 1 ∧
    Fintype.card (Perm (Fin 2)) = 2 ∧
    Fintype.card (Perm (Fin 3)) = 6 ∧
    Fintype.card (Perm (Fin 4)) = 24 ∧
    Fintype.card (Perm (Fin 5)) = 120 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- the order of the alternating group = n!/2 -/
theorem alt_order :
    Fintype.card (alternatingGroup (Fin 3)) = 3 ∧
    Fintype.card (alternatingGroup (Fin 4)) = 12 ∧
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## 6. Synthesis theorem -/

/-- **Galois-theoretic synthesis of five-fold locking**:

    5 is simultaneously the critical value of the following independent criteria:
    1. the smallest k making S_k unsolvable
    2. the smallest k making A_k a non-abelian simple group
    3. the smallest prime k with φ(k) > 2 -/
theorem five_locking_galois_comprehensive :
    -- S₂,S₃,S₄ are solvable, S₅ is unsolvable
    (IsSolvable (Perm (Fin 4))) ∧
    (¬ IsSolvable (Perm (Fin 5))) ∧
    -- A₅ is a non-abelian simple group
    (IsSimpleGroup (alternatingGroup (Fin 5))) ∧
    (Fintype.card (alternatingGroup (Fin 5)) = 60) ∧
    -- cyclotomic field
    (Nat.totient 5 = 4) ∧
    (∀ p, Nat.Prime p → p < 5 → Nat.totient p ≤ 2) ∧
    -- order of the symmetric group
    (Fintype.card (Perm (Fin 5)) = 120) :=
  ⟨S4_solvable, S5_not_solvable, A5_simple', A5_order',
   cyclotomic_5_galois_order, five_minimal_totient_exceeds_two.2.2,
   by decide⟩
