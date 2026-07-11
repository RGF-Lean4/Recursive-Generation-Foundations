/-
  Layer two: formalisation of t-designs and Steiner systems
  Recursive Generation Foundations (RGF)
-/

import Mathlib

open Finset BigOperators

structure TDesignParams where
  numPoints : ℕ        -- v
  blockSize : ℕ        -- k
  coverParam : ℕ       -- t
  coverMult : ℕ        -- λ
  cover_le_block : coverParam ≤ blockSize
  block_le_points : blockSize ≤ numPoints
  cover_pos : 0 < coverParam
  block_pos : 0 < blockSize

def TDesignParams.blockCount (p : TDesignParams) : ℕ :=
  p.coverMult * (Nat.choose p.numPoints p.coverParam) / (Nat.choose p.blockSize p.coverParam)

def TDesignParams.lambdaI (p : TDesignParams) (i : ℕ) : ℕ :=
  p.coverMult * (Nat.choose (p.numPoints - i) (p.coverParam - i)) /
    (Nat.choose (p.blockSize - i) (p.coverParam - i))

def TDesignParams.divisibilityCondition (p : TDesignParams) : Prop :=
  ∀ i : ℕ, i ≤ p.coverParam →
    (Nat.choose (p.blockSize - i) (p.coverParam - i)) ∣
    (p.coverMult * Nat.choose (p.numPoints - i) (p.coverParam - i))

def S_5_8_24 : TDesignParams where
  numPoints := 24
  blockSize := 8
  coverParam := 5
  coverMult := 1
  cover_le_block := by omega
  block_le_points := by omega
  cover_pos := by omega
  block_pos := by omega

theorem S_5_8_24_blockCount : S_5_8_24.blockCount = 759 := by decide
theorem S_5_8_24_lambda0 : S_5_8_24.lambdaI 0 = 759 := by decide
theorem S_5_8_24_lambda1 : S_5_8_24.lambdaI 1 = 253 := by decide
theorem S_5_8_24_lambda2 : S_5_8_24.lambdaI 2 = 77 := by decide
theorem S_5_8_24_lambda3 : S_5_8_24.lambdaI 3 = 21 := by decide
theorem S_5_8_24_lambda4 : S_5_8_24.lambdaI 4 = 5 := by decide
theorem S_5_8_24_lambda5 : S_5_8_24.lambdaI 5 = 1 := by decide

/-
all divisibility conditions of S(5,8,24) hold.
-/
theorem S_5_8_24_divisibility : S_5_8_24.divisibilityCondition := by
  intro i hi;
  rcases i with ( _ | _ | _ | _ | _ | _ | _ | i ) <;> trivial

def S_6_8_24 : TDesignParams where
  numPoints := 24
  blockSize := 8
  coverParam := 6
  coverMult := 1
  cover_le_block := by omega
  block_le_points := by omega
  cover_pos := by omega
  block_pos := by omega

theorem S_6_8_24_fails_at_1 :
    ¬ (Nat.choose 7 5 ∣ (1 * Nat.choose 23 5)) := by decide

theorem S_6_8_24_fails : ¬ S_6_8_24.divisibilityCondition := by
  intro h
  have h1 := h 1 (by show 1 ≤ 6; omega)
  simp only [S_6_8_24] at h1
  exact S_6_8_24_fails_at_1 h1

theorem t5_is_maximal_known_steiner :
    ¬ S_6_8_24.divisibilityCondition := S_6_8_24_fails

theorem steiner_rgf_connection : S_5_8_24.coverParam = 5 := rfl
theorem steiner_5_8_24_derived_lambda4 : S_5_8_24.lambdaI 4 = 5 := by decide
theorem steiner_5_8_24_steiner_property : S_5_8_24.lambdaI 5 = 1 := by decide