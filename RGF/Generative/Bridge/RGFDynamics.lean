/-
  RGFDynamics.lean — RGF dynamics uniqueness: the three locking-membrane conditions imply k = 5
  RGF Dynamics Uniqueness: Lock Membrane Conditions Imply k = 5

  This file formalizes:
  1. the three locking-membrane conditions (L1: unsolvability, L2: number of two-dimensional irreps, L3: oddness)
  2. the uniqueness proof of k = 5
  3. the relation to the RGF axioms
-/

import Mathlib

open Equiv

/-! ============================================================
    Part 1: definition of the three locking-membrane conditions
    ============================================================ -/

/-- Locking-membrane condition L1: S_k unsolvable (Abel-Ruffini obstruction). -/
def L1 (k : ℕ) : Prop := ¬ IsSolvable (Equiv.Perm (Fin k))

/-- Locking-membrane condition L3: k odd (chirality requirement). -/
def L3 (k : ℕ) : Prop := Odd k

/-- Locking-membrane condition L2: the dihedral group D_k has exactly 2 two-dimensional irreducible representations.
    For odd k, the number of two-dimensional irreps of D_k = (k-1)/2.
    Hence L2(k) means (k-1)/2 = 2, i.e. k = 5. -/
def L2 (k : ℕ) : Prop := (k - 1) / 2 = 2

/-! ============================================================
    Part 2: the three locking-membrane conditions imply k = 5
    ============================================================ -/

/-
S_k is solvable for k ≤ 4.
-/
set_option maxHeartbeats 800000 in
theorem perm_solvable_le_4 : ∀ k ≤ 4, IsSolvable (Equiv.Perm (Fin k)) := by
  intro k hk; interval_cases k <;> simp_all +decide ;
  · infer_instance;
  · infer_instance;
  · use 1;
    simp +decide [ commutator, Subgroup.commutator_def ];
  · use 2;
    simp +decide [ commutator, Subgroup.commutator_def ];
    rintro _ x hx y hy rfl; simp_all +decide [ Subgroup.mem_closure ] ;
    specialize hx ( alternatingGroup ( Fin 3 ) ) ; specialize hy ( alternatingGroup ( Fin 3 ) ) ; simp_all +decide [ Set.subset_def ] ;
    decide +revert;
  · use 3;
    -- The derived series of $S_4$ is $S_4 \supseteq A_4 \supseteq V_4 \supseteq \{e\}$.
    have h_derived_series_S4 : derivedSeries (Perm (Fin 4)) 1 = alternatingGroup (Fin 4) := by
      simp +decide [ derivedSeries ];
      refine' le_antisymm _ _ <;> simp +decide [ Subgroup.commutator_def ];
      · intro g hg; obtain ⟨ g₁, g₂, rfl ⟩ := hg; simp +decide [ commutatorElement_def ] ;
        decide +revert;
      · intro g hg; simp_all +decide [ alternatingGroup ] ; (
        -- Since $g$ is an even permutation, it can be written as a product of commutators.
        have h_even : ∃ (g₁ g₂ : Perm (Fin 4)), ⁅g₁, g₂⁆ = g := by
          native_decide +revert
        generalize_proofs at *; (
        exact Subgroup.subset_closure h_even));
    have h_derived_series_A4 : derivedSeries (Perm (Fin 4)) 2 = (Subgroup.closure {x : Perm (Fin 4) | x ^ 2 = 1 ∧ Equiv.Perm.sign x = 1}) := by
      refine' le_antisymm _ _ <;> simp_all +decide [ derivedSeries ];
      · simp +decide [ Subgroup.commutator_def ];
        rintro _ ⟨ g₁, hg₁, g₂, hg₂, rfl ⟩;
        refine' Subgroup.subset_closure _;
        native_decide +revert;
      · intro x hx; simp_all +decide [ Subgroup.commutator_def ] ;
        refine' Subgroup.subset_closure _;
        native_decide +revert
    have h_derived_series_V4 : derivedSeries (Perm (Fin 4)) 3 = ⊥ := by
      simp_all +decide [ commutator, Subgroup.commutator_def ];
      rintro _ x hx y hy rfl; simp_all +decide [ Subgroup.mem_closure ] ;
      specialize hx ( Subgroup.centralizer { x : Perm ( Fin 4 ) | x ^ 2 = 1 ∧ Perm.sign x = 1 } ) ; specialize hy ( Subgroup.centralizer { x : Perm ( Fin 4 ) | x ^ 2 = 1 ∧ Perm.sign x = 1 } ) ; simp_all +decide [ Set.subset_def, Subgroup.mem_centralizer_iff ] ;
      native_decide +revert
    exact h_derived_series_V4

/-
S_k is unsolvable for k ≥ 5.
-/
theorem perm_not_solvable_ge_5 (k : ℕ) (hk : 5 ≤ k) :
    ¬ IsSolvable (Equiv.Perm (Fin k)) := by
  convert Equiv.Perm.not_solvable ( Fin k ) ?_;
  simpa using hk

/-
L1 holds if and only if k ≥ 5.
-/
theorem L1_iff_ge_5 (k : ℕ) : L1 k ↔ 5 ≤ k := by
  exact ⟨ fun h => le_of_not_gt fun h' => h <| perm_solvable_le_4 k <| by linarith, fun h => perm_not_solvable_ge_5 k h ⟩

/-
L2 together with L3 (oddness) implies k = 5.
-/
theorem L2_L3_implies_5 (k : ℕ) (hL2 : L2 k) (hL3 : L3 k) : k = 5 := by
  obtain ⟨ m, rfl ⟩ := hL3;
  rcases m with ( _ | _ | _ | _ | m ) <;> simp_all +arith +decide [ L2 ]

/-- **Core theorem: the three locking-membrane conditions uniquely determine k = 5**
    Starting from three independent physical/mathematical constraints:
    - L1 (unsolvability): excludes k ≤ 4
    - L2 (number of two-dimensional irreps = 2): together with L3 locks k = 5
    - L3 (oddness): excludes even k -/
theorem lock_membrane_implies_k_eq_5
    (k : ℕ) (_hL1 : L1 k) (hL2 : L2 k) (hL3 : L3 k) : k = 5 :=
  L2_L3_implies_5 k hL2 hL3

/-
Reverse verification: k = 5 satisfies all three locking-membrane conditions.
-/
theorem k5_satisfies_all_conditions :
    L1 5 ∧ L2 5 ∧ L3 5 := by
  refine' ⟨ _, _, _ ⟩;
  · -- By definition of $L1$, we need to show that $S_5$ is not solvable.
    apply perm_not_solvable_ge_5 5 (by norm_num);
  · exact rfl;
  · exact ⟨ 2, rfl ⟩

/-
Full bidirectional characterization: k satisfies the three locking-membrane conditions if and only if k = 5.
-/
theorem lock_membrane_iff_k_eq_5 (k : ℕ) :
    (L1 k ∧ L2 k ∧ L3 k) ↔ k = 5 := by
  constructor;
  · exact fun h => lock_membrane_implies_k_eq_5 k h.1 h.2.1 h.2.2;
  · rintro rfl; exact k5_satisfies_all_conditions;

/-! ============================================================
    Part 3: axiom audit
    ============================================================ -/

#print axioms lock_membrane_implies_k_eq_5
#print axioms lock_membrane_iff_k_eq_5
