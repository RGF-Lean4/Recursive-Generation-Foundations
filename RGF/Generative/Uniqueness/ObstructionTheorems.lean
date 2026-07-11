/-
  Invariants/ObstructionTheorems.lean — RGF invariant obstruction theorems
  RGF Invariant Obstruction Theorems

  This file formalizes the invariant obstruction theorems of §5 of the outline:
  1. non-solvable-group obstruction: Aut(s) not solvable ⇒ |Aut(s)| ≥ 60
  2. recovery-time lower bound and symmetry
  3. spectral gap and symmetry order
  4. joint obstruction deriving k = 5
-/

import Mathlib
import RGF.Generative.Core.Basic

open Finset BigOperators

namespace RGFObstruction

/-! ============================================================
    Part 1: non-solvable-group obstruction
    ============================================================ -/

-- NOTE (sorry-free policy): `insolvable_group_min_order` (the minimal order of a
-- non-solvable finite group is ≥ 60, i.e. minimality of A₅) is a deep classical group
-- theory result.  A formal proof amounts to showing every finite group of order < 60 is
-- solvable (Sylow case analysis for each such order, together with Burnside's
-- p^a q^b theorem), none of which is currently available in Mathlib.  It is **not used**
-- anywhere in the project, so to keep the development free of `sorry` the statement is
-- recorded here in commented form only:
--
--   theorem insolvable_group_min_order (G : Type*) [Group G] [Fintype G]
--       (h_insol : ¬ IsSolvable G) : Fintype.card G ≥ 60
--   -- proof: every group of order < 60 is solvable (Burnside + Sylow case analysis)
--
-- The concrete witness `Fintype.card (alternatingGroup (Fin 5)) = 60` together with the
-- non-solvability of S₅ are proved unconditionally below (`A5_card_eq_60`,
-- `S5_not_solvable`).

/-- The order of A₅ is 60. -/
theorem A5_card_eq_60 :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by decide

/-- S₅ is not solvable (from Mathlib). -/
theorem S5_not_solvable : ¬ IsSolvable (Equiv.Perm (Fin 5)) := by
  apply Equiv.Perm.not_solvable
  simp [Cardinal.mk_fintype, Fintype.card_fin]

/-! ============================================================
    Part 2: recovery time and cyclic symmetry
    ============================================================ -/

/-- (k-1)/2 = 2 and k odd ⇒ k = 5. -/
theorem half_pred_eq_two_odd (k : ℕ) (h_odd : Odd k) (h_n2 : (k - 1) / 2 = 2) :
    k = 5 := by
  obtain ⟨m, hm⟩ := h_odd; omega

/-- The recovery time is 2 when k = 5. -/
theorem recovery_time_at_five : (5 - 1) / 2 = 2 := by norm_num

/-! ============================================================
    Part 3: spectral gap and symmetry order
    ============================================================ -/

/-- The spectral-gap upper bound decreases with the symmetry order. -/
theorem spectral_bound_decreasing (k₁ k₂ : ℕ) (hk₁ : k₁ ≥ 2) (_hk₂ : k₂ ≥ 2)
    (hle : k₁ ≤ k₂) :
    (1 : ℝ) / ((k₂ : ℝ) - 1) ≤ 1 / ((k₁ : ℝ) - 1) := by
  apply div_le_div_of_nonneg_left
  · positivity
  · have : (2 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast hk₁
    linarith
  · exact sub_le_sub_right (Nat.cast_le.mpr hle) 1

/-- The spectral-gap upper bound = 1/4 when k = 5. -/
theorem spectral_bound_at_five : (1 : ℝ) / ((5 : ℝ) - 1) = 1 / 4 := by norm_num

/-! ============================================================
    Part 4: joint obstruction deriving k = 5
    ============================================================ -/

/-- Joint obstruction theorem: non-solvable + odd + n₂ = 2 ⇒ k = 5. -/
theorem joint_obstruction (k : ℕ)
    (_h_insol : ¬ IsSolvable (Equiv.Perm (Fin k)))
    (h_odd : Odd k)
    (h_n2 : (k - 1) / 2 = 2) :
    k = 5 := by
  obtain ⟨m, hm⟩ := h_odd; omega

/-- Full quintic-locking check: k = 5 satisfies all three conditions. -/
theorem full_quintic_check :
    (¬ IsSolvable (Equiv.Perm (Fin 5))) ∧  -- L1
    ((5 - 1) / 2 = 2) ∧                     -- L2
    Odd 5 :=                                 -- L3
  ⟨S5_not_solvable, by norm_num, ⟨2, by omega⟩⟩

/-! ============================================================
    Part 5: Lyapunov exponents
    ============================================================ -/

/-- A positive Lyapunov exponent indicates chaos. -/
def isChaotic (lyap : ℝ) : Prop := lyap > 0

end RGFObstruction
