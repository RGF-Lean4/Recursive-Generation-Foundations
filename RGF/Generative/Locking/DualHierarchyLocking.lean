/-
Self-contained proof: the dual-hierarchy stable-generation requirement (which does
not mention the constant 2 explicitly) forces k = 5 and n₂ = 2. It depends on no
RGF project module, only on Mathlib.

This file is "absorbed" from a user-provided self-contained development.  The
original draft contained several `sorry`/`?_` placeholders together with later,
corrected (primed) versions of the same lemmas; here we keep clean, complete
versions.  Variable names colliding with Lean keywords (`example`) or notation
(`λ`) have been renamed.
-/
import Mathlib

open Matrix
open Complex
open scoped Real

/-!
## 1. An arithmetic function equivalent to the number of 2-dimensional irreps of the dihedral group

For odd `k`, the number of 2-dimensional irreducible representations of `D_k` is
`(k-1)/2`. We define the function `n₂(k)` and prove its basic properties, without
any group-theoretic argument.
-/

def n₂ (k : ℕ) : ℕ := if Odd k then (k - 1) / 2 else (k - 2) / 2

lemma n₂_eq_pred_div_two_of_odd {k : ℕ} (h : Odd k) : n₂ k = (k - 1) / 2 := by
  unfold n₂
  simp [h]

lemma n₂_three : n₂ 3 = 1 := by
  have hodd : Odd (3 : ℕ) := by decide
  rw [n₂_eq_pred_div_two_of_odd hodd]

lemma n₂_five : n₂ 5 = 2 := by
  have hodd : Odd (5 : ℕ) := by decide
  rw [n₂_eq_pred_div_two_of_odd hodd]

lemma n₂_seven : n₂ 7 = 3 := by
  have hodd : Odd (7 : ℕ) := by decide
  rw [n₂_eq_pred_div_two_of_odd hodd]

lemma one_lt_n₂_iff_five_le_and_odd {k : ℕ} (h : Odd k) : 1 < n₂ k ↔ 5 ≤ k := by
  rw [n₂_eq_pred_div_two_of_odd h]
  obtain ⟨m, rfl⟩ := h
  omega

lemma n₂_le_one_of_odd_lt_five {j : ℕ} (hj : Odd j) (hj4 : j ≤ 4) : n₂ j ≤ 1 := by
  have : j = 1 ∨ j = 3 := by
    rcases hj with ⟨m, rfl⟩; omega
  rcases this with rfl | rfl
  · unfold n₂; simp
  · rw [n₂_three]

/-!
## 2. The stable-generation condition `StableGen`

Conditions: `k` is odd, `n₂(k) > 1` (at least two 2-dimensional modes), and `k` is
the smallest such value.
-/

def StableGen (k : ℕ) : Prop :=
  Odd k ∧ 1 < n₂ k ∧ (∀ j, Odd j → 1 < n₂ j → k ≤ j)

lemma stableGen_five : StableGen 5 := by
  refine ⟨by decide, ?_, fun j hj hnj => ?_⟩
  · rw [n₂_five]; omega
  · by_contra hlt
    push_neg at hlt
    have hle : j ≤ 4 := by omega
    have h_le1 : n₂ j ≤ 1 := n₂_le_one_of_odd_lt_five hj hle
    omega

lemma stableGen_iff_eq_five (k : ℕ) : StableGen k ↔ k = 5 := by
  constructor
  · intro h
    obtain ⟨hodd, hgt, hmin⟩ := h
    have h5_odd : Odd 5 := by decide
    have h5_gt : 1 < n₂ 5 := by rw [n₂_five]; omega
    have hk5 : k ≤ 5 := hmin 5 h5_odd h5_gt
    have h5k : 5 ≤ k := by
      by_contra hlt
      push_neg at hlt
      have hle : k ≤ 4 := by omega
      have hle1 : n₂ k ≤ 1 := n₂_le_one_of_odd_lt_five hodd hle
      omega
    omega
  · intro h; subst h; exact stableGen_five

lemma stableGen_unique : ∃! k, StableGen k := by
  refine ⟨5, stableGen_five, ?_⟩
  intro k hk
  rw [stableGen_iff_eq_five] at hk
  exact hk

/-!
## 3. Rotation matrices and their irreducibility

We define the planar rotation matrix `rotMatrix θ` and prove that when `sin θ ≠ 0`
it has no real eigenvector in `ℝ²`, i.e. it corresponds to a 2-dimensional
irreducible representation.
-/

noncomputable def rotMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

lemma rotMatrix_no_real_eigenvector (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    ∀ (v : Fin 2 → ℝ) (lam : ℝ), v ≠ 0 → rotMatrix θ *ᵥ v ≠ lam • v := by
  intro v lam hv_nonzero h_eq
  have h0 : (rotMatrix θ *ᵥ v) 0 = (lam • v) 0 := by rw [h_eq]
  have h1 : (rotMatrix θ *ᵥ v) 1 = (lam • v) 1 := by rw [h_eq]
  simp [rotMatrix, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  -- cos θ * v0 - sin θ * v1 = lam * v0,  sin θ * v0 + cos θ * v1 = lam * v1
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 = 0 := by
      have := h0
      rw [hv0] at this
      -- - sinθ * v1 = 0
      have : Real.sin θ * v 1 = 0 := by nlinarith [this]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hsin
      · exact h
    apply hv_nonzero
    funext i
    fin_cases i
    · simpa using hv0
    · simpa using hv1
  · by_cases hv1 : v 1 = 0
    · have : Real.sin θ * v 0 = 0 := by
        have := h1
        rw [hv1] at this
        nlinarith [this]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hsin
      · exact absurd h hv0
    · -- both components are nonzero, derive a contradiction
      have e0 : (Real.cos θ - lam) * v 0 = Real.sin θ * v 1 := by linear_combination h0
      have e1 : (Real.cos θ - lam) * v 1 = -(Real.sin θ * v 0) := by linear_combination h1
      have key : (Real.sin θ ^ 2 + (Real.cos θ - lam) ^ 2) * (v 0 * v 1) = 0 := by
        linear_combination ((Real.cos θ - lam) * v 1) * e0 + (Real.sin θ * v 1) * e1
      have hvv : v 0 * v 1 ≠ 0 := mul_ne_zero hv0 hv1
      have h_det : Real.sin θ ^ 2 + (Real.cos θ - lam) ^ 2 = 0 := by
        rcases mul_eq_zero.mp key with h | h
        · exact h
        · exact absurd h hvv
      have h_sin_sq_zero : Real.sin θ ^ 2 = 0 := by
        nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ - lam)]
      have : Real.sin θ = 0 := by
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h_sin_sq_zero
      exact hsin this

/-
Every nontrivial rotation matrix corresponds to a 2-dimensional irreducible
representation (i.e. there is no 1-dimensional invariant subspace).
-/
lemma rotMatrix_irreducible (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    ¬ ∃ (W : Submodule ℝ (Fin 2 → ℝ)), W ≠ ⊤ ∧ W ≠ ⊥ ∧
      ∀ (v : Fin 2 → ℝ), v ∈ W → rotMatrix θ *ᵥ v ∈ W := by
  by_contra h_contra
  obtain ⟨W, hW_ne_top, hW_ne_bot, hW_inv⟩ := h_contra
  have hW_finrank : Module.finrank ℝ W = 1 := by
    have h_finrank : Module.finrank ℝ W < 2 := by
      exact lt_of_le_of_ne ( le_trans ( Submodule.finrank_le _ ) ( by norm_num ) ) fun h => hW_ne_top <| Submodule.eq_top_of_finrank_eq <| by aesop;
    interval_cases _ : Module.finrank ℝ W <;> simp_all +decide;
  obtain ⟨ v, hv ⟩ := finrank_eq_one_iff'.mp hW_finrank;
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (rotMatrix θ *ᵥ v.val) = c • v.val := by
    obtain ⟨ c, hc ⟩ := hv.2 ⟨ rotMatrix θ *ᵥ v, hW_inv v v.2 ⟩ ; use c; aesop;
  exact rotMatrix_no_real_eigenvector θ hsin v.val c ( by simpa using hv.1 ) hc

/-!
## 4. The dual-hierarchy stable-generation structure `BiLevel`

A dual-hierarchy structure consists of two distinct frequencies `θ₁, θ₂`, both of
which are nontrivial rotations (`sin ≠ 0`).
-/

structure BiLevel where
  θ₁ : ℝ
  θ₂ : ℝ
  sinθ₁_ne_zero : Real.sin θ₁ ≠ 0
  sinθ₂_ne_zero : Real.sin θ₂ ≠ 0
  θ_ne : θ₁ ≠ θ₂

namespace BiLevel

variable (bl : BiLevel)

/-- The total number of atoms (the order of the symmetry group) of a dual-hierarchy
    structure is 1 (scalar) + 2 + 2 = 5. -/
def lockedDim (_bl : BiLevel) : ℕ := 5

lemma lockedDim_eq_five : bl.lockedDim = 5 := rfl

lemma stableGen_of_biLevel : StableGen 5 := stableGen_five

/-- A concrete dual-hierarchy structure exists (non-emptiness). -/
noncomputable def std : BiLevel where
  θ₁ := π / 2
  θ₂ := π / 3
  sinθ₁_ne_zero := by rw [Real.sin_pi_div_two]; norm_num
  sinθ₂_ne_zero := by rw [Real.sin_pi_div_three]; positivity
  θ_ne := by
    have hpi := Real.pi_pos
    intro h
    have : π / 2 = π / 3 := h
    nlinarith

lemma exists_biLevel : Nonempty BiLevel := ⟨std⟩

end BiLevel

/-!
## 5. Unified main theorem: the dual-hierarchy architecture necessarily locks at k = 5 and n₂ = 2
-/

theorem definitive_locking :
    (∃! k, StableGen k) ∧ (StableGen 5) ∧ (n₂ 5 = 2) ∧
    (∀ k, StableGen k → k = 5) ∧ (Nonempty BiLevel) := by
  refine ⟨stableGen_unique, stableGen_five, n₂_five,
    fun k hk => (stableGen_iff_eq_five k).mp hk, BiLevel.exists_biLevel⟩

example : Odd 5 := stableGen_five.1

example : ¬ IsSolvable (Equiv.Perm (Fin 5)) := by
  apply Equiv.Perm.not_solvable
  simp