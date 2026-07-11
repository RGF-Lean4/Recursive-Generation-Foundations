import Mathlib
open Nat

/-
Proposition: uniqueness of the recovery time R=1 (emergent-structure locking version)

Given:
- d = 3 (spatial dimension, guaranteed by the RGF dimension_lock theorem)
- effective number of directions n_eff = 2d - 1_{R≥1} (no cooling when R=0, giving 6
  directions; when R≥1 the cooled site is unavailable, giving 5 directions)
- scaling exponent α = (d + 2R) / 2 (from the homogeneity of the self-energy scaling)
- emergence requirement: the numerator of α (i.e. d + 2R) equals n_eff (the number of
  poles equals the effective number of directions).
  This requirement comes from the fact that the number of poles of the propagator is
  determined by the effective number of moving directions.

Proof:
1. If R = 0 then n_eff = 6 ≠ 5, so the emergent structure does not match (hexagon vs pentagon).
2. If R ≥ 2 then the numerator of α, d + 2R ≥ 7 ≠ 5, so the number of poles ≠ 5 and the
   emergent structure does not match.
3. The unique positive-integer solution with n_eff = 5 and d + 2R = 5 is R = 1.

Note: in step 3, substituting d=3 into d + 2R = 5 gives 3 + 2R = 5 → R = 1.
A more precise statement is: we require α = n_eff/2, i.e. (d+2R)/2 = (2d - 1_{R≥1})/2.
Substituting d=3, by cases:
- R=0: LHS = (3+0)/2 = 3/2, RHS = 6/2 = 3, not equal
- R=1: LHS = (3+2)/2 = 5/2, RHS = 5/2, equal
- R≥2: LHS = (3+2R)/2 ≥ 7/2, RHS = 5/2, not equal
-/

def n_eff (R : ℕ) : ℕ :=
  if R = 0 then 6 else 5

def alpha_num (R : ℕ) : ℕ :=
  3 + 2 * R  -- d + 2R, with d=3 fixed

/-
Emergence consistency condition:
the numerator of the scaling exponent (the number of poles) must equal the effective
number of directions, i.e. alpha_num(R) = n_eff(R).
-/
def emergence_condition (R : ℕ) : Prop :=
  alpha_num R = n_eff R

/-- Main theorem: R=1 is the unique recovery time satisfying the emergence consistency
condition. --/
theorem r_equals_one_unique : ∀ (R : ℕ), emergence_condition R ↔ R = 1 := by
  intro R
  constructor
  · intro h
    -- emergence_condition R holds; we must show R = 1
    unfold emergence_condition at h
    unfold alpha_num n_eff at h
    -- case split: R=0, R=1, R≥2
    by_cases h0 : R = 0
    · -- R=0: LHS=3, RHS=6, contradiction
      subst h0
      simp at h
    · -- R ≠ 0, i.e. R ≥ 1
      have hR1 : R ≥ 1 := Nat.one_le_of_lt (Nat.pos_of_ne_zero h0)
      -- here n_eff = 5
      simp [h0] at h
      -- h: 3 + 2*R = 5
      -- hence 2*R = 2, R = 1
      have h2 : 2 * R = 2 := by omega
      omega
  · intro h
    -- R = 1; we must show emergence_condition 1 holds
    subst h
    unfold emergence_condition alpha_num n_eff
    simp

/-- Corollary: R=0 does not satisfy the emergence condition. --/
theorem r_zero_excluded : ¬ emergence_condition 0 := by
  unfold emergence_condition alpha_num n_eff
  simp

/-- Corollary: for any R ≥ 2, R does not satisfy the emergence condition. --/
theorem r_ge_two_excluded (R : ℕ) (hR : R ≥ 2) : ¬ emergence_condition R := by
  unfold emergence_condition alpha_num n_eff
  have hR0 : R ≠ 0 := by omega
  simp [hR0]
  -- must show 3 + 2*R ≠ 5
  -- since R ≥ 2, we have 3 + 2*R ≥ 7
  omega
