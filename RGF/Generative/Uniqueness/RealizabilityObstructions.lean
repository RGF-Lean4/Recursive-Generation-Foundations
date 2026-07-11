/-
  Invariants/RealizabilityObstructions.lean — RGF realizability obstruction theorems
  RGF Realizability Obstruction Theorems

  Core result: Z₃ cannot be realized under the degree ≤ 2 constraint

  Key insight:
  - ZMod 3 under multiplication is a ring (containing a zero element), not a group.
    Hence ≃* ZMod 3 holds for no group (in the original version it held trivially).
  - The correct mathematical statement uses Multiplicative (ZMod 3) (the cyclic group of order 3).
  - The automorphism group of a degree ≤ 2 graph cannot have order 3 (the core of the corrected version).
-/

import Mathlib
import RGF.Generative.Core.InvariantTheorems
import RGF.Generative.Locking.LockingMembrane

open RGFState Finset

noncomputable section

namespace RGFState

variable {n : ℕ}

/-! ============================================================
    Basic definitions
    ============================================================ -/

/-- The degree of vertex i in the graph s. -/
def degree (s : RGFState n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => s.adj i j = true)).card

/-- All vertices have degree ≤ d. -/
def maxDegreeLe (s : RGFState n) (d : ℕ) : Prop :=
  ∀ i : Fin n, s.degree i ≤ d

/-- The automorphism group as a type. -/
abbrev AutGroup (s : RGFState n) : Type := s.autGroup

instance (s : RGFState n) : DecidablePred (· ∈ s.autGroup) :=
  fun σ => show Decidable (s.IsAut σ) from inferInstance

instance autGroupFintype (s : RGFState n) : Fintype (AutGroup s) := inferInstance

end RGFState

open RGFState

/-! ============================================================
    Part 1: no MulEquiv exists between a group and ZMod 3 (algebraic lemma)
    ============================================================ -/

/-- No group admits a MulEquiv with ZMod 3 (the multiplicative ring). -/
theorem group_not_mul_equiv_zmod3 (G : Type*) [Group G] :
    IsEmpty (G ≃* ZMod 3) := by
  constructor
  intro e
  have : (0 : ZMod 3) = 1 := by
    obtain ⟨g, hg⟩ := e.surjective 0
    have h2 : e (g * g⁻¹) = e g * e g⁻¹ := e.map_mul g g⁻¹
    rw [mul_inv_cancel] at h2
    rw [e.map_one, hg, zero_mul] at h2
    exact h2.symm
  exact absurd this (by decide)

/-! ============================================================
    Part 2: Z₃ obstruction theorem (original version — direct from the algebraic lemma)
    ============================================================ -/

/-- Theorem (original version): ≃* ZMod 3 holds for no group. -/
theorem Z3_not_realizable_degree_two :
    ¬ ∃ (n : ℕ) (s : RGFState n) (sys : EquivariantSystem n),
      sys.toRGFIterSystem.IsFixedPoint s ∧
      Nonempty (AutGroup s ≃* ZMod 3) ∧
      maxDegreeLe s 2 := by
  intro ⟨_, s, _, _, ⟨e⟩, _⟩
  exact (group_not_mul_equiv_zmod3 (AutGroup s)).false e

/-! ============================================================
    Part 3: auxiliary lemmas for the corrected version
    ============================================================ -/

/-- The order of Multiplicative (ZMod 3) is 3. -/
lemma card_multiplicative_zmod3 :
    Fintype.card (Multiplicative (ZMod 3)) = 3 := by
  simp [Multiplicative, ZMod, Fintype.card_fin]

/-- A group isomorphism preserves order. -/
lemma card_eq_of_mulEquiv {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (e : G ≃* H) :
    Fintype.card G = Fintype.card H :=
  Fintype.card_congr e.toEquiv

/-! ============================================================
    Part 4: the automorphism group of a degree ≤ 2 graph has order ≠ 3 (core graph-theory lemma)
    ============================================================ -/

/-- The order of a subgroup divides the order of the whole group. -/
lemma aut_card_dvd_perm_card (s : RGFState n) :
    Fintype.card (AutGroup s) ∣ Fintype.card (Equiv.Perm (Fin n)) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card s.autGroup

/-- When n ≤ 2, |Aut(s)| ≤ 2. -/
lemma aut_card_le_two_of_small_n (s : RGFState n) (hn : n ≤ 2) :
    Fintype.card (AutGroup s) ≤ 2 := by
  interval_cases n <;> simp_all +decide
  · exact le_trans (Fintype.card_le_one_iff.mpr (by aesop_cat)) (by decide)
  · exact le_trans (Fintype.card_le_one_iff.mpr (by aesop_cat)) (by decide)
  · exact Nat.le_of_dvd (by decide) (aut_card_dvd_perm_card s)

/-- σ preserves adjacency ⇒ σ preserves degree. -/
lemma aut_preserves_degree (s : RGFState n) (σ : Equiv.Perm (Fin n))
    (hσ : s.IsAut σ) (i : Fin n) :
    s.degree (σ i) = s.degree i := by
  refine' Finset.card_bij (fun j hj => σ⁻¹ j) _ _ _ <;> simp_all +decide [RGFState.IsAut]
  · intro a ha; specialize hσ i (σ.symm a); aesop
  · exact fun j hj => ⟨σ j, by simpa [hσ] using hj, by simp +decide⟩

/-- Isolation of a triangle under the degree ≤ 2 constraint. -/
lemma triangle_isolated (s : RGFState n)
    (a b c : Fin n) (_hab : a ≠ b) (hbc : b ≠ c) (_hac : a ≠ c)
    (h_ab : s.adj a b = true) (_h_bc : s.adj b c = true) (h_ca : s.adj c a = true)
    (h_deg : maxDegreeLe s 2) :
    ∀ v : Fin n, v ≠ a → v ≠ b → v ≠ c → s.adj a v = false := by
  intro v hv₁ hv₂ hv₃
  by_contra h_contra
  have h_deg_a : s.degree a ≥ 3 := by
    refine' Finset.two_lt_card.mpr _
    use b, by grind +qlia, c, by simp_all +decide [RGFState.symm], v, by aesop
    grind
  linarith [h_deg a]

/-- The transposition (a ↔ b) within a triangle is an automorphism. -/
lemma triangle_swap_aut (s : RGFState n)
    (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_ab : s.adj a b = true) (h_bc : s.adj b c = true) (h_ca : s.adj c a = true)
    (h_deg : maxDegreeLe s 2) :
    s.IsAut (Equiv.swap a b) := by
  intro i j
  grind +suggestions

/-- The transposition of two isolated vertices is an automorphism. -/
lemma isolated_swap_aut (s : RGFState n)
    (a b : Fin n) (hab : a ≠ b)
    (h_iso_a : s.degree a = 0)
    (h_iso_b : s.degree b = 0) :
    s.IsAut (Equiv.swap a b) := by
  intro i j
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp_all +decide [Equiv.swap_apply_def]
  · exact s.symm _ _
  · unfold RGFState.degree at *; simp_all +decide [Finset.ext_iff]
  · simp_all +decide [Finset.ext_iff, RGFState.degree]
    grind +suggestions
  · split_ifs <;> simp_all +decide [RGFState.degree]
    have := s.symm i a; have := s.symm i b; aesop

/-
If all vertices are isolated, then Aut(s) = S_n, of order n!
-/
lemma all_isolated_aut_eq_full (s : RGFState n)
    (h_all_iso : ∀ i : Fin n, s.degree i = 0) :
    Fintype.card (AutGroup s) = Nat.factorial n := by
  -- Since all vertices are isolated, every permutation is an automorphism.
  have h_all_aut : ∀ σ : Equiv.Perm (Fin n), s.IsAut σ := by
    intro σ i j; by_cases hij : i = j <;> simp_all +decide [ RGFState.degree ] ;
  erw [ Fintype.card_of_subtype ];
  any_goals exact Finset.univ;
  · simp +decide [ Finset.card_univ, Fintype.card_perm ];
  · aesop

/-
n! ≠ 3 for all n
-/
lemma factorial_ne_three (n : ℕ) : Nat.factorial n ≠ 3 := by
  by_contra! h;
  have := Nat.factorial_dvd_factorial ( show n ≥ 3 by contrapose! h; interval_cases n <;> trivial ) ; simp_all +decide ;

/-
In a degree ≤ 2 graph, if Aut(s) contains an element of order 2,
    then |Aut(s)| is even, hence cannot equal 3
-/
lemma order_two_contradicts_card_three {n : ℕ} (s : RGFState n)
    (h_card : Fintype.card (AutGroup s) = 3)
    (σ : Equiv.Perm (Fin n)) (hσ : s.IsAut σ) (hσ_ne : σ ≠ 1)
    (hσ2 : σ * σ = 1) : False := by
  -- By Lagrange's theorem, the order of any element in a finite group divides the order of the group.
  have h_lagrange : orderOf (⟨σ, hσ⟩ : AutGroup s) ∣ Fintype.card (AutGroup s) := by
    exact orderOf_dvd_card;
  simp_all +decide [ orderOf_dvd_iff_pow_eq_one ];
  simp_all +decide [ pow_succ, Subtype.ext_iff ]

/-
Core combinatorial lemma: if σ ∈ Aut(s) has order 3, maxDeg ≤ 2,
    σ has a non-adjacent 3-cycle (a,b,c) with deg(a) ≥ 1,
    then Aut(s) contains another automorphism not in ⟨σ⟩.

    Proof idea: σ preserves connected components. σ|_C has order 3 on the component C of a.
    C is a connected graph with maxDeg ≤ 2, so C is either a path or a cycle.
    If a path: |Aut(C)| ≤ 2 < 3 = ord(σ|_C), a contradiction.
    If a cycle C_m: 3 | m, and Aut(C_m) = D_m contains a reflection (an order-2 element).
    The reflection extends to an automorphism of the whole graph.

Degree-0 neighbor lemma: if degree = 0, then adj i j = false for all j
-/
lemma adj_false_of_degree_zero (s : RGFState n) (i : Fin n)
    (h : s.degree i = 0) (j : Fin n) : s.adj i j = false := by
  contrapose! h;
  exact ne_of_gt ( Finset.card_pos.mpr ⟨ j, by aesop ⟩ )

/-
Degree-1 unique neighbor: if degree = 1, then there is exactly one neighbor
-/
lemma degree_one_unique_neighbor (s : RGFState n) (i : Fin n)
    (h : s.degree i = 1) (j : Fin n) (hj : s.adj i j = true) :
    ∀ k : Fin n, s.adj i k = true → k = j := by
  unfold RGFState.degree at h;
  rw [ Finset.card_eq_one ] at h;
  obtain ⟨ k, hk ⟩ := h; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;

-- NOTE (sorry-free policy): the genuine, non-vacuous Z₃ obstruction below
-- (`Z3_not_realizable_degree_two_corrected`, stated with the cyclic group
-- `Multiplicative (ZMod 3)`) is TRUE, but its proof needs the classical reflection
-- construction `non_adj_deg_pos_gives_order_two` (an order-3 automorphism that moves a
-- positive-degree vertex non-adjacently forces an order-2 automorphism — i.e. a
-- path/cycle reflection), which itself rests on the path/cycle classification of
-- degree-≤2 graphs not available in Mathlib.  To keep the project free of `sorry`, the
-- whole genuine chain is recorded below in commented form only.  (The vacuous version on
-- the multiplicative *monoid* `ZMod 3` is proved unconditionally in `Z3Obstruction.lean`
-- via the algebraic obstruction that no group is `MulEquiv` to `ZMod 3`.)
/-
lemma non_adj_deg_pos_gives_order_two {n : ℕ} (s : RGFState n) (h_deg : maxDegreeLe s 2)
    (σ : Equiv.Perm (Fin n)) (hσ : s.IsAut σ) (h_ord3 : orderOf σ = 3)
    (a : Fin n) (ha : σ a ≠ a)
    (h_nonadj : s.adj a (σ a) = false)
    (h_degpos : s.degree a ≥ 1) :
    ∃ τ : Equiv.Perm (Fin n), s.IsAut τ ∧ τ ≠ 1 ∧ τ * τ = 1 := by
  /- Mathematical proof idea (to be formalized):
     1. extract a neighbor x of a, prove σ x ≠ x (otherwise deg(x) ≥ 3)
     2. let y = σ x, prove adj b y = true
     3. prove C (the connected component of a) has no σ-fixed point (degree constraint) → |V(C)| = 3k
     4. prove |E(C)| ≡ 0 (mod 3); combined with 3k-1 ≤ |E(C)| ≤ 3k this gives |E(C)| = 3k
     5. so C is a connected 2-regular graph, i.e. the cycle C_{3k}
     6. a reflection of C_{3k} (an order-2 element of the dihedral group) extends to an automorphism of the whole graph -/
  (proof omitted: the classical path/cycle classification of degree-≤2 graphs is not available in Mathlib)

/-
Key lemma: the order of the automorphism group of a degree ≤ 2 graph is not equal to 3
-/
lemma aut_card_ne_three_of_degree_le_two {n : ℕ} (s : RGFState n)
    (h_deg : maxDegreeLe s 2) :
    Fintype.card (AutGroup s) ≠ 3 := by
  by_contra h_contra;
  have := Fact.mk ( show Nat.Prime 3 by decide ) ; have := exists_prime_orderOf_dvd_card 3 ( by rw [ h_contra ] ) ; obtain ⟨ g, hg ⟩ := this; simp_all +decide [ orderOf_eq_iff ] ;
  obtain ⟨a, ha⟩ : ∃ a : Fin n, g.val a ≠ a := by
    exact not_forall.mp fun h => hg.2 1 ( by decide ) ( by decide ) <| Subtype.ext <| Equiv.ext h;
  obtain ⟨b, c, hab, hbc, hac, hσ⟩ : ∃ b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ g.val a = b ∧ g.val b = c ∧ g.val c = a := by
    have h_cycle : g.val (g.val (g.val a)) = a := by
      have := congr_arg ( fun f : s.AutGroup => f.val a ) hg.1; simp +decide [ pow_succ' ] at this; aesop;
    grind +ring;
  by_cases h_adj : s.adj a b = true;
  · have h_triangle : s.adj a b = true ∧ s.adj b c = true ∧ s.adj c a = true := by
      have := g.2 a b; have := g.2 b c; have := g.2 c a; aesop;
    have h_swap : s.IsAut (Equiv.swap a b) := by
      apply triangle_swap_aut s a b c hab hbc hac h_triangle.left h_triangle.right.left h_triangle.right.right h_deg;
    exact order_two_contradicts_card_three s h_contra ( Equiv.swap a b ) h_swap ( by aesop ) ( by aesop );
  · by_cases h_degpos : s.degree a ≥ 1;
    · have := non_adj_deg_pos_gives_order_two s h_deg g.val g.2 ( by
        rw [ orderOf_eq_iff ] <;> aesop ) a ha ( by
        lia ) h_degpos; obtain ⟨ τ, hτ₁, hτ₂, hτ₃ ⟩ := this; exact order_two_contradicts_card_three s h_contra τ hτ₁ hτ₂ hτ₃;
    · have h_iso_b : s.degree b = 0 := by
        have := aut_preserves_degree s g.val g.2 a; aesop;
      have h_iso_c : s.degree c = 0 := by
        have := aut_preserves_degree s g.val g.property c; aesop;
      have h_iso_swap : s.IsAut (Equiv.swap a b) := by
        apply isolated_swap_aut s a b hab (by
        exact Nat.eq_zero_of_not_pos h_degpos) (by
        exact h_iso_b)
      exact order_two_contradicts_card_three s h_contra (Equiv.swap a b) h_iso_swap (by
      simp +decide [ Equiv.swap_apply_def, hab ]) (by
      simp +decide [ Equiv.swap_apply_def ])

/-! ============================================================
    Part 5: corrected obstruction theorem
    ============================================================ -/

/-- Corrected obstruction theorem: Z₃ (the cyclic group of order 3) cannot be realized under degree ≤ 2. -/
theorem Z3_not_realizable_degree_two_corrected :
    ¬ ∃ (n : ℕ) (s : RGFState n) (sys : EquivariantSystem n),
      sys.toRGFIterSystem.IsFixedPoint s ∧
      Nonempty (AutGroup s ≃* Multiplicative (ZMod 3)) ∧
      maxDegreeLe s 2 := by
  intro ⟨_, s, _, _, ⟨e⟩, h_deg⟩
  have h_card : Fintype.card (AutGroup s) = 3 :=
    (card_eq_of_mulEquiv e).trans card_multiplicative_zmod3
  exact aut_card_ne_three_of_degree_le_two s h_deg h_card
-/

end