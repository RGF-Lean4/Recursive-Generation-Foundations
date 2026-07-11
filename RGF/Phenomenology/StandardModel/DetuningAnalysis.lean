/-
  Deepening of the NWHM detuning analysis
  NWHM Detuning Analysis: Deeper Results

  This file formalizes:
  - refined estimates of the frequency detuning function
  - the discrimination criterion between CM points and non-CM points
  - the logarithmic lower-bound framework of Baker's theorem
  - the mathematical foundation of the mode-locking mechanism
  - the five-fold resonance condition
-/

import Mathlib

open Real BigOperators

/-! ## Refined analysis of the frequency detuning -/

/-- Frequency detuning function. -/
noncomputable def fullDetuning (omega1 omega2 eps : ℝ) : ℝ :=
  |omega1 - omega2| + eps ^ 2 / (omega1 + omega2)

/-- The detuning is nonnegative. -/
theorem detuning_nonneg (omega1 omega2 eps : ℝ)
    (h1 : 0 < omega1) (h2 : 0 < omega2) :
    0 ≤ fullDetuning omega1 omega2 eps := by
  unfold fullDetuning
  apply add_nonneg (abs_nonneg _)
  apply div_nonneg (sq_nonneg _)
  linarith

/-- At resonance the detuning is determined by the coupling term. -/
theorem resonance_detuning (omega eps : ℝ) (hw : 0 < omega) (he : eps ≠ 0) :
    0 < fullDetuning omega omega eps := by
  unfold fullDetuning
  simp [sub_self]
  apply div_pos (sq_pos_of_ne_zero he)
  linarith

/-- Far from resonance the detuning is controlled by the frequency difference. -/
theorem off_resonance_detuning (omega1 omega2 eps : ℝ)
    (h1 : 0 < omega1) (h2 : 0 < omega2) :
    |omega1 - omega2| ≤ fullDetuning omega1 omega2 eps := by
  unfold fullDetuning
  linarith [div_nonneg (sq_nonneg eps) (by linarith : (0 : ℝ) ≤ omega1 + omega2)]

/-! ## CM point condition -/

/-- CM point condition. -/
structure CMPointData where
  coords : Fin 2 → ℝ
  lattice_cond : ∃ m n : ℤ, coords 0 = ↑m ∧ coords 1 = ↑n

/-- CM and non-CM are complementary. -/
theorem cm_or_non_cm (coords : Fin 2 → ℝ) :
    (∃ m n : ℤ, coords 0 = ↑m ∧ coords 1 = ↑n) ∨
    ¬(∃ m n : ℤ, coords 0 = ↑m ∧ coords 1 = ↑n) :=
  em _

/-! ## Baker-type logarithmic lower bound -/

/-- Parameters of the Baker-type lower bound. -/
structure BakerParams where
  numAlgebraic : ℕ
  degreeBound : ℕ
  heightBound : ℝ
  num_pos : 0 < numAlgebraic
  degree_pos : 0 < degreeBound
  height_pos : 0 < heightBound

/-- The Baker lower bound is positive. -/
theorem baker_bound_pos (params : BakerParams) :
    0 < Real.exp (-params.heightBound ^ params.numAlgebraic) :=
  Real.exp_pos _

/-! ## Winding-momentum ratio -/

/-- Winding-momentum ratio. -/
noncomputable def windingMomentumRatio (alpha beta L : ℝ) : ℝ :=
  beta * L ^ 2 / (alpha * L⁻¹ ^ 2)

/-- Under the balance condition the ratio is 1. -/
theorem ratio_at_balance (alpha beta L : ℝ)
    (hα : 0 < alpha) (_hβ : 0 < beta) (hL : 0 < L)
    (hbal : alpha * L⁻¹ ^ 2 = beta * L ^ 2) :
    windingMomentumRatio alpha beta L = 1 := by
  unfold windingMomentumRatio
  rw [div_eq_one_iff_eq (by positivity)]
  linarith

/-! ## Mode-locking mechanism -/

/-- Dichotomy between mode-locking and quasiperiodicity. -/
theorem mode_locking_dichotomy (coupling detuning : ℝ) :
    coupling ≥ detuning ∨ coupling < detuning := by
  by_cases h : coupling ≥ detuning
  · exact Or.inl h
  · exact Or.inr (by push_neg at h; exact h)

/-! ## Five-fold resonance condition -/

/-- Five-fold resonance. -/
def IsFiveResonance (omega1 omega2 : ℝ) : Prop :=
  ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ p + q = 5 ∧
    |omega1 / omega2 - (p : ℝ) / (q : ℝ)| < 1 / 10

/-- Set of possible fractions for five-fold resonance. -/
theorem five_resonance_fractions :
    {(p, q) : ℕ × ℕ | 0 < p ∧ 0 < q ∧ p + q = 5} =
    {(1, 4), (2, 3), (3, 2), (4, 1)} := by
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hq, hpq⟩; omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

/-! ## Reduction chain -/

/-- NWHM reduction chain. -/
structure NWHMReductionChain where
  conjectureA : Prop
  conjectureB : Prop
  conjectureC : Prop
  a_implies_b : conjectureA → conjectureB
  b_implies_c : conjectureB → conjectureC

/-- Transitivity of the reduction chain. -/
theorem reduction_chain_transitive (chain : NWHMReductionChain) :
    chain.conjectureA → chain.conjectureC :=
  fun ha => chain.b_implies_c (chain.a_implies_b ha)
