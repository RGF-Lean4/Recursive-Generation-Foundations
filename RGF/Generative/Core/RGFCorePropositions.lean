import Mathlib

/-!
# RGF core propositions (complete proofs)

This file contains Lean 4 formal proofs of the core propositions of Recursive Generation Formalism (RGF).

## Main content
- the locking-membrane conditions L1, L2, L3 and their uniqueness
- the dimension locking theorem
- properties of the five-fold symmetric graph C₅
-/

open Equiv

/-! ## Part 1: locking-membrane conditions -/

/-- Locking-membrane condition L1: S_k unsolvable. -/
def L1 (k : ℕ) : Prop := ¬ IsSolvable (Perm (Fin k))

/-- Locking-membrane condition L2: (k-1)/2 = 2. -/
def L2 (k : ℕ) : Prop := (k - 1) / 2 = 2

/-- Locking-membrane condition L3: k odd. -/
def L3 (k : ℕ) : Prop := k % 2 = 1

/-- Proposition 1: L2 and L3 imply k = 5. -/
theorem locking_uniqueness (k : ℕ) (hL2 : L2 k) (hL3 : L3 k) : k = 5 := by
  unfold L2 at hL2; unfold L3 at hL3; omega

/-- Proposition 2a: 5 satisfies L1 (S₅ unsolvable). -/
theorem five_satisfies_L1 : L1 5 := by
  unfold L1
  exact Perm.not_solvable _ (by simp)

/-- Proposition 2b: 5 satisfies L2. -/
theorem five_satisfies_L2 : L2 5 := by unfold L2; norm_num

/-- Proposition 2c: 5 satisfies L3. -/
theorem five_satisfies_L3 : L3 5 := by unfold L3; norm_num

/-- Proposition 3: there exists a unique k satisfying L1 ∧ L2 ∧ L3. -/
theorem unique_locking : ∃! k : ℕ, L1 k ∧ L2 k ∧ L3 k :=
  ⟨5, ⟨five_satisfies_L1, five_satisfies_L2, five_satisfies_L3⟩,
    fun k ⟨_, hL2, hL3⟩ => locking_uniqueness k hL2 hL3⟩

/-! ## Part 2: dimension locking -/

/-- Critical ratio function Γ_c(d) = 2/(d-1). -/
noncomputable def Gamma_c (d : ℕ) : ℝ := 2 / ((d : ℝ) - 1)

/-- Proposition 4: Γ_c(d) = 1 if and only if d = 3 (requires d ≥ 2). -/
theorem dimension_locking (d : ℕ) (hd : 2 ≤ d) : Gamma_c d = 1 ↔ d = 3 := by
  unfold Gamma_c
  constructor
  · intro h
    have hd1 : (d : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (d : ℝ) := Nat.ofNat_le_cast.mpr hd
      linarith
    rw [div_eq_iff hd1] at h
    have : (d : ℝ) = 3 := by linarith
    exact_mod_cast this
  · rintro rfl; norm_num

/-- Proposition 5: in the range 2 ≤ d ≤ 100, the unique d satisfying Γ_c(d)=1 is 3. -/
theorem dimension_locking_unique : ∃! d : ℕ, 2 ≤ d ∧ d ≤ 100 ∧ Gamma_c d = 1 :=
  ⟨3, ⟨by norm_num, by norm_num, by unfold Gamma_c; norm_num⟩,
    fun d ⟨hd, _, heq⟩ => (dimension_locking d hd).mp heq⟩

/-! ## Part 3: five-fold symmetric graph -/

/-- A directed graph on 5 vertices, represented as a finite set of ordered pairs. -/
abbrev Graph5 := Finset (Fin 5 × Fin 5)

/-- Adjacency relation of a graph (undirected: check both directions). -/
def adj (g : Graph5) (u v : Fin 5) : Prop := (u, v) ∈ g ∨ (v, u) ∈ g

/-- Graph automorphism: preserves the adjacency relation. -/
def IsAutomorphism (g : Graph5) (σ : Fin 5 → Fin 5) : Prop :=
  ∀ u v, adj g u v ↔ adj g (σ u) (σ v)

/-- Order-5 permutation (5-cycle): σ⁵ = id and no shorter period. -/
def Is5Cycle (σ : Fin 5 → Fin 5) : Prop :=
  ∀ x : Fin 5, (σ^[5]) x = x ∧ ∀ n, 1 ≤ n → n < 5 → (σ^[n]) x ≠ x

/-- Edge set of the 5-cycle graph C₅. -/
def C5 : Graph5 := {((0 : Fin 5), (1 : Fin 5)), (1, 2), (2, 3), (3, 4), (4, 0)}

/-- Proposition 6: C₅ has five-fold rotational symmetry (an order-5 cycle automorphism exists). -/
theorem C5_has_fivefold : ∃ σ, Is5Cycle σ ∧ IsAutomorphism C5 σ := by
  -- σ(i) = (i+1) mod 5 is the 5-cycle automorphism of C₅
  refine ⟨fun i => ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
  · -- Is5Cycle
    intro x; constructor
    · fin_cases x <;> decide
    · intro n hn1 hn5; fin_cases x <;> interval_cases n <;> decide
  · -- IsAutomorphism
    intro u v; fin_cases u <;> fin_cases v <;> simp [adj, C5]

/-
Proposition 7 (original version) claimed "any connected graph with five-fold symmetry must be C₅".

Note: this proposition is mathematically false.
Counterexample: the complete graph K₅ is also connected and has a 5-cycle automorphism, but K₅ ≠ C₅.

A more precise statement is: under the Z₅ action, the edge set of an undirected graph on 5 vertices must be
the union of two orbits (the edges of C₅ and the edges of the complement of C₅). Hence there are exactly three connected graphs
with a 5-cycle automorphism: C₅, the complement of C₅ (also isomorphic to C₅), and K₅.
-/
/-! ## Axiom check -/
#print axioms locking_uniqueness
#print axioms five_satisfies_L1
#print axioms five_satisfies_L2
#print axioms five_satisfies_L3
#print axioms unique_locking
#print axioms dimension_locking
#print axioms dimension_locking_unique
#print axioms C5_has_fivefold
