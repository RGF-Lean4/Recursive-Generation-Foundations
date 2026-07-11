/-
  Symmetry-factor formula: Ξ(s) = 1/|Stab_H(s)|

  Mathematical content extracted from the user's document:
  - The symmetry factor Ξ(s) = 1/|Stab_H(s)| appears ubiquitously across many fields:
    * graph theory: 1/|Aut(G)| (Pólya counting)
    * combinatorial designs: 1/|Aut(D)|
    * number theory: Tamagawa numbers
    * Hecke theory: the multiple-covering factor 1/k²
  - By the orbit-stabilizer theorem: Ξ(x) = |Orb(x)|/|G|
  - Burnside's lemma relates orbits to fixed points
-/

import Mathlib

open Finset BigOperators MulAction Classical

/-- Under a group action, the symmetry factor of an element is the reciprocal of the size of its stabilizer. -/
noncomputable def symmetryFactor (G : Type*) {X : Type*} [Group G] [Fintype G]
    [DecidableEq G] [MulAction G X] (x : X) : ℚ :=
  1 / (Fintype.card (MulAction.stabilizer G x))

/-- For the dihedral group D₅, |D₅| = 10. -/
theorem dihedral5_order : Fintype.card (DihedralGroup 5) = 10 := by decide

/-- Pólya's counting formula: the number of distinct colorings under a group action. -/
noncomputable def polyaCount (G_order : ℕ) (fixedPoints : Fin G_order → ℕ) (c : ℕ) : ℚ :=
  (1 : ℚ) / G_order * ∑ i : Fin G_order, (c : ℚ) ^ fixedPoints i

/-- For a finite group, the symmetry factor is always positive. -/
theorem symmetryFactor_pos (G : Type*) {X : Type*}
    [Group G] [Fintype G] [DecidableEq G] [MulAction G X]
    (x : X) :
    (0 : ℚ) < symmetryFactor G x := by
  unfold symmetryFactor
  apply div_pos one_pos
  exact Nat.cast_pos.mpr Fintype.card_pos

/-- Higher symmetry means lower weight: if |Stab(x)| ≤ |Stab(y)|
    then Ξ(y) ≤ Ξ(x). -/
theorem symmetryFactor_antitone (G : Type*) {X : Type*}
    [Group G] [Fintype G] [DecidableEq G] [MulAction G X]
    (x y : X) (h : Fintype.card (MulAction.stabilizer G x) ≤
                    Fintype.card (MulAction.stabilizer G y)) :
    symmetryFactor G y ≤ symmetryFactor G x := by
  unfold symmetryFactor
  apply div_le_div_of_nonneg_left (by positivity)
    (Nat.cast_pos.mpr Fintype.card_pos)
    (Nat.cast_le.mpr h)

/-
By orbit-stabilizer: Ξ(x) = 1/|Stab(x)| = |Orb(x)|/|G|.
    This is the key identity connecting the symmetry factor with the orbit size.
-/
theorem symmetryFactor_eq_orbit_div_group (G : Type*) {X : Type*}
    [Group G] [Fintype G] [DecidableEq G] [MulAction G X]
    [DecidableEq X] [Fintype X]
    (x : X) :
    symmetryFactor G x =
    ↑(Fintype.card (MulAction.orbit G x)) / ↑(Fintype.card G) := by
      rw [ symmetryFactor ];
      rw [ Fintype.card_congr ( MulAction.orbitEquivQuotientStabilizer G x ) ];
      rw [ eq_div_iff ] <;> norm_cast;
      · have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( stabilizer G x ) ; simp_all +decide [ mul_comm ];
        rw [ mul_assoc, mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Fintype.card_pos_iff.mpr ⟨ 1, by simp +decide ⟩ ), mul_one ];
      · exact Fintype.card_ne_zero