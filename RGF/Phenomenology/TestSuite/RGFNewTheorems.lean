/-
  RGFNewTheorems.lean — new theorems derived from the RGF locking-membrane framework
  New Theorems Derivable from the RGF Locking-Membrane Framework

  Building on the existing `Invariants.LockingMembrane` (which defines `num2DIrreps` and the three locking-membrane conditions L1-L3),
  this file derives a batch of new theorems not previously stated. They all follow naturally by deduction
  from the established results, further enriching the RGF mathematical system.

  Main new results:
  ──────────────────────────────────────────────────────────
  A. Structural theorems for the count of two-dimensional irreducible representations
     · the "step" recursion of num2DIrreps: n₂(k+2) = n₂(k) + 1
     · complete characterization of n₂ = 2: for k ≥ 3, n₂(k) = 2 ⇔ k ∈ {5, 6}
     · for each m ≥ 1, there are exactly two k ≥ 3 with n₂(k) = m (one odd, one even)

  B. Dimension theorems of dihedral group representation theory (recovering group-theoretic facts from the counting formula)
     · sum-of-squares-of-dimensions theorem: 1²·n₁ + 2²·n₂ = 2k = |Dₖ| (k ≥ 3)
     · formula for the total number of conjugacy classes (irreps)

  C. Group-theoretic characterization of the locking value k = 5
     · k = 5 is exactly the smallest degree making the symmetric group Sₖ unsolvable
     · within the locking conditions, oddness (L3) together with L2 automatically entails L1 (unsolvability)
     · the even candidate k = 6 satisfies L2 but violates L3
  ──────────────────────────────────────────────────────────
-/

import Mathlib
import RGF.Generative.Locking.LockingMembrane

open Finset BigOperators Equiv Function

noncomputable section

/-! ============================================================
    Preliminaries: solvability of small symmetric groups (self-contained, reusing classical arguments)
    ============================================================ -/

/-- S_n is unsolvable when n ≥ 5. -/
theorem rgfnt_perm_not_solvable_of_ge_five (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsSolvable (Equiv.Perm (Fin n)) := by
  apply Equiv.Perm.not_solvable
  rw [Cardinal.mk_fin]
  exact_mod_cast hn

theorem rgfnt_S0_solvable : IsSolvable (Equiv.Perm (Fin 0)) :=
  isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)

theorem rgfnt_S1_solvable : IsSolvable (Equiv.Perm (Fin 1)) :=
  isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)

theorem rgfnt_S2_solvable : IsSolvable (Equiv.Perm (Fin 2)) := by
  use 1
  simp +decide [ commutator, Subgroup.commutator_def ]

theorem rgfnt_S3_solvable : IsSolvable (Equiv.Perm (Fin 3)) := by
  use 2
  simp +decide [ commutator, Subgroup.commutator_def ]
  simp +decide [ Subgroup.mem_closure ]
  rintro y x hx z hz rfl
  specialize hx ( alternatingGroup ( Fin 3 ) ) ; specialize hz ( alternatingGroup ( Fin 3 ) ) ; simp_all +decide [ Set.subset_def ]
  decide +revert

theorem rgfnt_S4_solvable : IsSolvable (Equiv.Perm (Fin 4)) := by
  use 3
  have h_ker : (derivedSeries (Equiv.Perm (Fin 4)) 1).map (Equiv.Perm.sign : Equiv.Perm (Fin 4) →* ℤˣ) = ⊥ := by
    simp +decide [ commutator_def ]
    simp +decide [ Subgroup.map_eq_bot_iff, Subgroup.commutator_def ]
    rintro _ ⟨ g₁, g₂, rfl ⟩ ; simp +decide [ commutatorElement ]
    decide +revert
  have h_derived1 : derivedSeries (Equiv.Perm (Fin 4)) 1 = alternatingGroup (Fin 4) := by
    refine' le_antisymm _ _ <;> simp_all +decide [ Subgroup.map_eq_bot_iff ]
    · exact h_ker
    · intro x hx; simp_all +decide [ commutator_eq_closure ]
      have h_even : ∃ (y z : Equiv.Perm (Fin 4)), x = y * z * y⁻¹ * z⁻¹ := by
        native_decide +revert
      exact h_even.elim fun y hy => hy.elim fun z hz => hz ▸ Subgroup.subset_closure ⟨ y, z, rfl ⟩
  have h_comm_A4 : derivedSeries (Equiv.Perm (Fin 4)) 2 = Subgroup.closure {σ : Equiv.Perm (Fin 4) | σ ∈ alternatingGroup (Fin 4) ∧ σ^2 = 1} := by
    refine' le_antisymm _ _ <;> simp_all +decide [ Subgroup.closure_le, Set.subset_def ]
    · simp +decide [ Subgroup.commutator_def ]
      rintro _ ⟨ g₁, hg₁, g₂, hg₂, rfl ⟩ ; simp +decide [ commutatorElement_def ]
      refine' Subgroup.subset_closure _ ; simp_all +decide
      native_decide +revert
    · intro x hx hx'; simp_all +decide [ Subgroup.commutator_def ]
      refine' Subgroup.subset_closure _
      native_decide +revert
  simp_all +decide [ Subgroup.commutator_eq_bot_iff_le_centralizer ]
  intro σ hσ τ hτ
  refine' Subgroup.closure_induction ( fun x hx => _ ) _ _ _ hτ
  · decide +revert
  · norm_num
  · grind
  · intro x hx hx'; rw [ inv_mul_eq_iff_eq_mul ]
    simp +decide [ ← mul_assoc, hx' ]

/-- **Core criterion**: S_n is solvable if and only if n ≤ 4. -/
theorem rgfnt_solvable_iff_le_four (n : ℕ) :
    IsSolvable (Equiv.Perm (Fin n)) ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    exact rgfnt_perm_not_solvable_of_ge_five n hlt h
  · intro h
    interval_cases n
    · exact rgfnt_S0_solvable
    · exact rgfnt_S1_solvable
    · exact rgfnt_S2_solvable
    · exact rgfnt_S3_solvable
    · exact rgfnt_S4_solvable

/-! ============================================================
    A. Structural theorems for the count num2DIrreps of two-dimensional irreps
    ============================================================ -/

/-
**Step recursion**: for k ≥ 3, increasing k by 2 (preserving parity) increases the number of two-dimensional irreps by exactly 1.
-/
theorem num2DIrreps_step_two (k : ℕ) (hk : k ≥ 3) :
    num2DIrreps (k + 2) = num2DIrreps k + 1 := by
  rcases Nat.even_or_odd' k with ⟨ c, rfl | rfl ⟩ <;> simp +arith +decide [ *, num2DIrreps ];
  · grind;
  · grind +splitImp

/-
**Complete characterization of n₂ = 1**: k ≥ 3 and num2DIrreps k = 1 if and only if k ∈ {3, 4}.
-/
theorem num2DIrreps_eq_one_iff (k : ℕ) (hk : k ≥ 3) :
    num2DIrreps k = 1 ↔ (k = 3 ∨ k = 4) := by
  unfold num2DIrreps;
  grind

/-
**Complete characterization of n₂ = 2**: k ≥ 3 and num2DIrreps k = 2 if and only if k ∈ {5, 6}.
-/
theorem num2DIrreps_eq_two_iff (k : ℕ) (hk : k ≥ 3) :
    num2DIrreps k = 2 ↔ (k = 5 ∨ k = 6) := by
  grind +suggestions

/-
**Layer-by-layer covering theorem**: for k ≥ 3, num2DIrreps k = m if and only if k is 2m+1 (odd) or 2m+2 (even).
    Hence for each m ≥ 1 there are exactly two k ≥ 3 with num2DIrreps k = m.
-/
theorem num2DIrreps_fiber (k m : ℕ) (hk : k ≥ 3) :
    num2DIrreps k = m ↔ (k = 2 * m + 1 ∨ k = 2 * m + 2) := by
  unfold num2DIrreps;
  grind

/-! ============================================================
    B. Dimension theorems of dihedral group representation theory
    ============================================================ -/

/-- Number of one-dimensional irreps of the dihedral group Dₖ. -/
def num1DIrreps (k : ℕ) : ℕ := if Odd k then 2 else 4

/-
**Sum-of-squares-of-dimensions theorem**: for k ≥ 3,
      1² · n₁ + 2² · n₂ = 2k = |Dₖ|.
-/
theorem dihedral_dim_sq_sum (k : ℕ) (hk : k ≥ 3) :
    num1DIrreps k * 1 + num2DIrreps k * 4 = 2 * k := by
  unfold num1DIrreps num2DIrreps;
  grind

/-
For odd k ≥ 3, the total number of irreps of Dₖ = (k + 3)/2.
-/
theorem dihedral_num_irreps_odd (k : ℕ) (hk : k ≥ 3) (hodd : Odd k) :
    num1DIrreps k + num2DIrreps k = (k + 3) / 2 := by
  unfold num1DIrreps num2DIrreps;
  grind

/-
For even k ≥ 3, the total number of irreps of Dₖ = (k + 6)/2.
-/
theorem dihedral_num_irreps_even (k : ℕ) (hk : k ≥ 3) (heven : Even k) :
    num1DIrreps k + num2DIrreps k = (k + 6) / 2 := by
  unfold num1DIrreps num2DIrreps;
  grind +locals

/-! ============================================================
    C. Group-theoretic characterization of the locking value k = 5
    ============================================================ -/

/-
**k = 5 is the smallest non-solvable symmetric group degree**.
-/
theorem five_is_min_nonsolvable_degree :
    (∀ k, k < 5 → IsSolvable (Equiv.Perm (Fin k))) ∧
      ¬ IsSolvable (Equiv.Perm (Fin 5)) := by
  exact ⟨ fun k hk => ( rgfnt_solvable_iff_le_four k ).mpr ( by linarith ), rgfnt_perm_not_solvable_of_ge_five 5 ( by decide ) ⟩

/-
**L2 ∧ L3 implies L1**:
    if k ≥ 3, num2DIrreps k = 2 (L2) and k is odd (L3), then Sₖ is unsolvable (L1).
    In other words, the three locking conditions are actually redundant: L2 ∧ L3 already forces L1.
-/
theorem L2_L3_imply_L1 (k : ℕ) (hk : k ≥ 3)
    (hL2 : num2DIrreps k = 2) (hL3 : Odd k) :
    ¬ IsSolvable (Equiv.Perm (Fin k)) := by
  convert rgfnt_perm_not_solvable_of_ge_five _ _;
  contrapose! hL2; interval_cases k <;> trivial;

/-
**Two-condition equivalent characterization of the locking conditions**:
    the complete three locking conditions (L1 ∧ L2 ∧ L3) are equivalent to just (L2 ∧ L3).
-/
theorem locking_reduces_to_two (k : ℕ) :
    LockingMembraneConditions k ↔ (num2DIrreps k = 2 ∧ Odd k) := by
  constructor;
  · exact fun h => ⟨ h.L2, h.L3 ⟩;
  · exact fun h => ⟨ h.1, h.2 ⟩

/-
**Even candidate k = 6**: satisfies L2 but not L3.
-/
theorem six_satisfies_L2_not_L3 :
    num2DIrreps 6 = 2 ∧ ¬ Odd 6 := by
  decide +revert

/-
**Refined form of uniqueness**: num2DIrreps k = 2 ∧ k odd if and only if k = 5.
-/
theorem locking_value_refined (k : ℕ) :
    (num2DIrreps k = 2 ∧ Odd k) ↔ k = 5 := by
  constructor <;> intro h <;> have := odd_n2_eq_two_implies_five k <;> simp_all +decide

/-! ============================================================
    Axiom audit
    ============================================================ -/

#print axioms num2DIrreps_step_two
#print axioms num2DIrreps_eq_two_iff
#print axioms num2DIrreps_fiber
#print axioms dihedral_dim_sq_sum
#print axioms five_is_min_nonsolvable_degree
#print axioms L2_L3_imply_L1
#print axioms locking_reduces_to_two
#print axioms locking_value_refined

end
