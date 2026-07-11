/-
  Layer 2: deeper properties of the symmetry factor
  Recursive Generation Foundations (RGF)
-/

import Mathlib

open scoped BigOperators
open Finset MulAction

noncomputable def rgfSymmetryFactor {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s : S) : ℝ :=
  1 / (Nat.card (MulAction.stabilizer G s) : ℝ)

theorem rgfSymmetryFactor_pos {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s : S) :
    0 < rgfSymmetryFactor (G := G) s := by
  simp only [rgfSymmetryFactor]
  apply div_pos one_pos
  exact_mod_cast Nat.card_pos

theorem rgfSymmetryFactor_le_one {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s : S) :
    rgfSymmetryFactor (G := G) s ≤ 1 := by
  convert div_le_self zero_le_one ( Nat.one_le_cast.mpr ( Nat.card_pos ) ) using 1;
  all_goals infer_instance

theorem rgfSymmetryFactor_eq_orbit_div {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s : S) :
    rgfSymmetryFactor (G := G) s =
      (Nat.card (MulAction.orbit G s) : ℝ) / (Nat.card G : ℝ) := by
  -- By the orbit-stabilizer theorem, we have |G| = |orbit G s| * |stabilizer G s|.
  have h_orbit_stabilizer : Nat.card G = Nat.card (MulAction.orbit G s) * Nat.card (MulAction.stabilizer G s) := by
    convert Subgroup.card_eq_card_quotient_mul_card_subgroup ( MulAction.stabilizer G s );
    exact Nat.card_congr ( MulAction.orbitEquivQuotientStabilizer G s );
  unfold rgfSymmetryFactor; rw [ h_orbit_stabilizer ] ; push_cast; ring;
  rw [ mul_assoc, mul_inv_cancel₀, mul_one ] ; aesop_cat;

theorem rgfSymmetryFactor_orbit_const {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s₁ s₂ : S) (g : G)
    (h : g • s₁ = s₂) :
    rgfSymmetryFactor (G := G) s₁ = rgfSymmetryFactor (G := G) s₂ := by
  subst h;
  convert ( congr_arg ( fun x : ℝ => 1 / x ) <| Nat.cast_inj.mpr ?_ ) using 1;
  exact Nat.card_congr ( MulAction.stabilizerEquivStabilizerOfOrbitRel ( show s₁ ∈ MulAction.orbit G ( g • s₁ ) from ⟨ g⁻¹, by simp +decide ⟩ ) )

theorem rgfSymmetryFactor_eq_one {G : Type*} [Group G] [Fintype G]
    {S : Type*} [MulAction G S] (s : S)
    (h : Nat.card (MulAction.stabilizer G s) = 1) :
    rgfSymmetryFactor (G := G) s = 1 := by
  unfold rgfSymmetryFactor; rw [h]; simp

inductive SymmetryClass where
  | maximal : SymmetryClass
  | minimal : SymmetryClass
  | intermediate : SymmetryClass

theorem graph_symmetry_factor_bound (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / (Nat.factorial n : ℝ) ≤ 1 / 2 := by
  gcongr; norm_cast; exact Nat.le_trans ( by decide ) ( Nat.factorial_le hn ) ;

theorem symmetry_factor_hierarchy :
    (1 : ℝ) / 1 > 1 / 2 ∧ (1 : ℝ) / 2 > 1 / 6 ∧ (1 : ℝ) / 6 > 1 / 24 := by
  constructor <;> [norm_num; constructor <;> norm_num]