import RGF.Generative.Locking.PentagonComplete
open RGF.PentagonComplete
open Real

/-!
# Pentagon — golden ratio: supplementary identities

Extends the module `RGF.PentagonComplete`, proving six additional exact identities.
All theorems rely only on the standard axioms, with no `sorry`.
-/

namespace RGF.PentagonNew

/-! ## Auxiliary lemmas: exact values of cos(3π/5) and cos(4π/5) -/

lemma cos_three_pi_div_five : cos (3*π/5) = (1 - √5) / 4 := by
  calc
    cos (3*π/5) = cos (π - 2*π/5) := by ring_nf
    _ = -cos (2*π/5) := by rw [cos_pi_sub]
    _ = -((√5 - 1) / 4) := by rw [cos_two_pi_div_five]
    _ = (1 - √5) / 4 := by ring

lemma cos_four_pi_div_five : cos (4*π/5) = (-1 - √5) / 4 := by
  calc
    cos (4*π/5) = cos (π - π/5) := by ring_nf
    _ = -cos (π/5) := by rw [cos_pi_sub]
    _ = -((1 + √5) / 4) := by rw [cos_pi_div_five]
    _ = (-1 - √5) / 4 := by ring

/-! ## 1. The four cosines sum to zero -/

/-- cos(π/5) + cos(2π/5) + cos(3π/5) + cos(4π/5) = 0 -/
theorem four_cos_sum_zero : cos (π/5) + cos (2*π/5) + cos (3*π/5) + cos (4*π/5) = 0 := by
  rw [cos_three_pi_div_five, cos_four_pi_div_five, cos_pi_div_five, cos_two_pi_div_five]
  ring

/-! ## 2. Golden ratio reciprocal identity -/

/-- φ⁻¹ = φ - 1 -/
theorem golden_inv_eq : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
  have h : Real.goldenRatio * (Real.goldenRatio - 1) = 1 := by
    nlinarith [golden_sq_eq_golden_add_one]
  exact inv_eq_of_mul_eq_one_right h

/-! ## 3. ψ = -φ⁻¹ -/

theorem psi_eq_neg_golden_inv : psi = -Real.goldenRatio⁻¹ := by
  rw [golden_inv_eq, Real.goldenRatio_def, psi]
  ring

/-! ## 4. ψ = 1 - φ -/

theorem psi_eq_one_sub_golden : psi = 1 - Real.goldenRatio := by
  rw [Real.goldenRatio_def, psi]
  ring

/-! ## 5. The quartic minimal polynomial of cos(π/5) -/

/-- 16·(cos(π/5))⁴ - 12·(cos(π/5))² + 1 = 0 -/
theorem cos_pi_div_five_quartic : 16 * (cos (π/5)) ^ 4 - 12 * (cos (π/5)) ^ 2 + 1 = 0 := by
  rw [cos_pi_div_five]  -- cos(π/5) = (1 + √5)/4
  have h5sq : (√5 : ℝ)^2 = 5 := Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))
  have h4 : (√5 : ℝ)^4 = 25 := by nlinarith [h5sq]
  have h3 : (√5 : ℝ)^3 = 5 * √5 := by nlinarith [h5sq]
  ring_nf
  nlinarith [h5sq, h4, h3]

/-! ## 6. Binet-type difference formula -/

/-- φⁿ⁺¹ - ψⁿ⁺¹ = F_{n+1}·√5 -/
theorem golden_sub_psi_pow (n : ℕ) : Real.goldenRatio^(n+1) - psi^(n+1) = (Nat.fib (n+1) : ℝ) * √5 := by
  induction' n with k ih
  · -- n = 0
    simp [Real.goldenRatio, psi, Nat.fib_one]
  · -- from k to k+1
    have hφpow : Real.goldenRatio^(k+1) = (Nat.fib (k+1) : ℝ) * Real.goldenRatio + (Nat.fib k : ℝ) :=
      golden_pow_succ k
    have hψpow : psi^(k+1) = (Nat.fib (k+1) : ℝ) * psi + (Nat.fib k : ℝ) :=
      psi_pow_succ k
    have hsum : Real.goldenRatio + psi = 1 := golden_add_psi
    have hdiff : Real.goldenRatio - psi = √5 := golden_sub_psi
    have hφsq_sub_ψsq : Real.goldenRatio^2 - psi^2 = √5 := by
      nlinarith [golden_sq_eq_golden_add_one, psi_sq_eq_psi_add_one, hsum, hdiff]
    have hfib : (Nat.fib (k+2) : ℝ) = (Nat.fib (k+1) : ℝ) + (Nat.fib k : ℝ) := by
      simp [Nat.fib_add_two, add_comm]
    calc
      Real.goldenRatio^(k+2) - psi^(k+2) =
          (Real.goldenRatio^(k+1) * Real.goldenRatio) - (psi^(k+1) * psi) := by
        simp [pow_succ]
      _ = ((Nat.fib (k+1) : ℝ) * Real.goldenRatio + (Nat.fib k : ℝ)) * Real.goldenRatio -
          ((Nat.fib (k+1) : ℝ) * psi + (Nat.fib k : ℝ)) * psi := by rw [hφpow, hψpow]
      _ = (Nat.fib (k+1) : ℝ) * (Real.goldenRatio^2 - psi^2) + (Nat.fib k : ℝ) * (Real.goldenRatio - psi) := by ring
      _ = (Nat.fib (k+1) : ℝ) * √5 + (Nat.fib k : ℝ) * √5 := by rw [hφsq_sub_ψsq, hdiff]
      _ = ((Nat.fib (k+1) : ℝ) + (Nat.fib k : ℝ)) * √5 := by ring
      _ = (Nat.fib (k+2) : ℝ) * √5 := by rw [hfib]

/-! ## Summary theorem -/

/-- All the content of the supplementary identities.

Note: the original manuscript wrote this summary theorem as `four_cos_sum_zero ∧ golden_inv_eq ∧ …`,
i.e. directly using each theorem's "name (proof term)" as a conjunct. This does not type-check in Lean
(`∧` expects a proposition `Prop`, while a theorem name is a proof term of some proposition), so here it is rewritten as
an explicit conjunction of each proposition itself, with unchanged meaning; the proof is still provided by the corresponding already-proved theorems one by one. -/
theorem pentagon_new_identities :
    (cos (π/5) + cos (2*π/5) + cos (3*π/5) + cos (4*π/5) = 0) ∧
    (Real.goldenRatio⁻¹ = Real.goldenRatio - 1) ∧
    (psi = -Real.goldenRatio⁻¹) ∧
    (psi = 1 - Real.goldenRatio) ∧
    (16 * (cos (π/5)) ^ 4 - 12 * (cos (π/5)) ^ 2 + 1 = 0) ∧
    (∀ n : ℕ, Real.goldenRatio^(n+1) - psi^(n+1) = (Nat.fib (n+1) : ℝ) * √5) :=
  ⟨four_cos_sum_zero, golden_inv_eq, psi_eq_neg_golden_inv, psi_eq_one_sub_golden,
    cos_pi_div_five_quartic, golden_sub_psi_pow⟩

end RGF.PentagonNew
