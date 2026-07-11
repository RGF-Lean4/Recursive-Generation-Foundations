/-
  RequestProject/PentagonComplete.lean — common foundation module for the pentagon / golden-ratio algebra
  Common, stable foundation module for the Pentagon / Golden-ratio algebra.

  This file provides a stable common naming layer `RGF.PentagonComplete`, collecting the most frequently
  referenced exact values of the regular pentagon — golden-ratio algebra and the basic identities of the golden conjugate `psi`,
  uniformly taking `Real.goldenRatio` (φ = (1+√5)/2) as the standard definition of the golden ratio and `psi` (= (1−√5)/2)
  as the golden conjugate, so that extension modules (PentagonNew, PentagonMore…) can build new identities on top
  without repeatedly modifying this foundation module.

  Notes:
    · `psi` is numerically equal to Mathlib's `Real.goldenConj` (both are (1−√5)/2),
      and is given here as an independent `def` to make this layer self-contained with stable naming.
    · `Real.goldenRatio_def` unfolds `Real.goldenRatio` to (1+√5)/2, convenient for `rw`.

  All propositions are rigorously machine-verifiable purely mathematical conclusions, with no `sorry`, relying only on the standard axioms.
-/
import Mathlib

open Real

/-- Unfolding of `Real.goldenRatio`: φ = (1 + √5)/2 (convenient for `rw`). -/
theorem Real.goldenRatio_def : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl

namespace RGF.PentagonComplete

/-! ## Exact cosine values -/

-- Note: cos(π/5) = (1 + √5)/4 is provided directly by Mathlib (`Real.cos_pi_div_five`),
-- so we do not re-declare a theorem of the same name here, to avoid ambiguity under `open Real`.

/-- cos(2π/5) = (√5 − 1)/4. -/
theorem cos_two_pi_div_five : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
  rw [show (2 : ℝ) * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-! ## Golden ratio and golden conjugate -/

/-- φ² = φ + 1. -/
theorem golden_sq_eq_golden_add_one : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 :=
  Real.goldenRatio_sq

/-- Golden conjugate ψ := (1 − √5)/2. -/
noncomputable def psi : ℝ := (1 - √5) / 2

/-- Bridging lemma: this module's `psi` coincides with Mathlib's `Real.goldenConj`.
    For use when old modules unify the golden-conjugate notation, to prevent old theorems from breaking. -/
theorem psi_eq_goldenConj : psi = Real.goldenConj := rfl

/-- ψ² = ψ + 1. -/
theorem psi_sq_eq_psi_add_one : psi ^ 2 = psi + 1 := by
  unfold psi
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- φ + ψ = 1. -/
theorem golden_add_psi : Real.goldenRatio + psi = 1 := by
  unfold psi; rw [Real.goldenRatio]; ring

/-- φ − ψ = √5. -/
theorem golden_sub_psi : Real.goldenRatio - psi = √5 := by
  unfold psi; rw [Real.goldenRatio]; ring

/-! ## Fibonacci power expansions -/

/-- φ^(n+1) = F(n+1)·φ + F(n). -/
theorem golden_pow_succ (n : ℕ) :
    Real.goldenRatio ^ (n + 1)
      = (Nat.fib (n + 1) : ℝ) * Real.goldenRatio + (Nat.fib n : ℝ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, Nat.fib_add_two]
    push_cast
    nlinarith [Real.goldenRatio_sq]

/-- ψ^(n+1) = F(n+1)·ψ + F(n). -/
theorem psi_pow_succ (n : ℕ) :
    psi ^ (n + 1) = (Nat.fib (n + 1) : ℝ) * psi + (Nat.fib n : ℝ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, Nat.fib_add_two]
    push_cast
    nlinarith [psi_sq_eq_psi_add_one]

end RGF.PentagonComplete
