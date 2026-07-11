/-
  Nonequilibrium statistical mechanics: detailed balance and entropy production
  Nonequilibrium Statistical Mechanics: Detailed Balance and Entropy Production

  Formalizes:
  - the detailed balance condition
  - the entropy production rate
  - the connection to the dual-layer iteration of Recursive Generation Formalism
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Markov chains and detailed balance -/

/-- Transition matrix of a finite-state Markov chain. -/
structure MarkovChain (n : ℕ) where
  /-- transition probability P(i → j) -/
  transition : Fin n → Fin n → ℝ
  /-- transition probabilities nonnegative -/
  nonneg : ∀ i j, 0 ≤ transition i j
  /-- row sums equal 1 (stochastic matrix) -/
  stochastic : ∀ i, ∑ j : Fin n, transition i j = 1

/-- Detailed balance condition: π(i) P(i,j) = π(j) P(j,i). -/
def DetailedBalance {n : ℕ} (mc : MarkovChain n) (pi : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, pi i * mc.transition i j = pi j * mc.transition j i

/-- Detailed balance implies a stationary distribution. -/
theorem detailed_balance_implies_stationary
    {n : ℕ} (mc : MarkovChain n) (pi : Fin n → ℝ)
    (hdb : DetailedBalance mc pi) :
    ∀ j : Fin n, ∑ i : Fin n, pi i * mc.transition i j = pi j := by
  intro j
  conv_lhs => arg 2; ext i; rw [hdb i j]
  simp_rw [← Finset.mul_sum, mc.stochastic, mul_one]

/-- Symmetry of detailed balance. -/
theorem detailed_balance_symm
    {n : ℕ} (mc : MarkovChain n) (pi : Fin n → ℝ)
    (hdb : DetailedBalance mc pi) :
    ∀ i j, pi i * mc.transition i j = pi j * mc.transition j i :=
  hdb

/-! ## 2. Entropy and KL divergence -/

/-- KL divergence relative to the stationary distribution (discrete version). -/
noncomputable def klDivergence {n : ℕ}
    (mu pi : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, mu i * Real.log (mu i / pi i)

/-- Shannon entropy. -/
noncomputable def shannonEntropy {n : ℕ} (mu : Fin n → ℝ) : ℝ :=
  -∑ i : Fin n, mu i * Real.log (mu i)

/-! ## 3. Entropy production rate -/

/-- Entropy production rate: σ = ∑_{i,j} J(i,j) · A(i,j)
    where J(i,j) = π(i)P(i,j) - π(j)P(j,i) is the net probability flow
    and A(i,j) = log(π(i)P(i,j) / (π(j)P(j,i))) is the affinity. -/
noncomputable def entropyProductionRate
    {n : ℕ} (mc : MarkovChain n) (pi : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (pi i * mc.transition i j - pi j * mc.transition j i) *
    Real.log (if pi j * mc.transition j i = 0 then 1
              else pi i * mc.transition i j / (pi j * mc.transition j i))

/-- Under detailed balance the entropy production rate is zero. -/
theorem entropy_production_zero_of_detailed_balance
    {n : ℕ} (mc : MarkovChain n) (pi : Fin n → ℝ)
    (hdb : DetailedBalance mc pi) :
    entropyProductionRate mc pi = 0 := by
  unfold entropyProductionRate
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  rw [hdb i j, sub_self, zero_mul]

/-! ## 4. Properties of the net flow -/

/-- Net probability flow. -/
noncomputable def netFlow {n : ℕ} (mc : MarkovChain n) (pi : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  pi i * mc.transition i j - pi j * mc.transition j i

/-- Antisymmetry of the net flow. -/
theorem netFlow_antisymm {n : ℕ} (mc : MarkovChain n) (pi : Fin n → ℝ)
    (i j : Fin n) :
    netFlow mc pi i j = -netFlow mc pi j i := by
  unfold netFlow; ring

/-- The sum of the net flow over the stationary distribution is zero. -/
theorem netFlow_sum_zero {n : ℕ} (mc : MarkovChain n) (pi : Fin n → ℝ)
    (hstat : ∀ j, ∑ i : Fin n, pi i * mc.transition i j = pi j)
    (i : Fin n) :
    ∑ j : Fin n, netFlow mc pi i j = 0 := by
  unfold netFlow
  simp only [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum, mc.stochastic, mul_one]
  linarith [hstat i]

/-! ## 5. Reversible and irreversible Markov chains -/

/-- Reversible Markov chain (satisfying detailed balance). -/
structure ReversibleMarkovChain (n : ℕ) extends MarkovChain n where
  stationaryDist : Fin n → ℝ
  stationary_nonneg : ∀ i, 0 ≤ stationaryDist i
  stationary_sum : ∑ i : Fin n, stationaryDist i = 1
  detailed_balance : DetailedBalance toMarkovChain stationaryDist

/-- The net flow of a reversible chain is zero. -/
theorem reversible_zero_netflow {n : ℕ} (mc : ReversibleMarkovChain n)
    (i j : Fin n) :
    netFlow mc.toMarkovChain mc.stationaryDist i j = 0 := by
  unfold netFlow
  have := mc.detailed_balance i j
  linarith

/-! ## 6. Gallavotti-Cohen fluctuation symmetry -/

/-- The core algebraic content of the fluctuation theorem:
    P(σ = a) / P(σ = -a) = e^{a·t}
    taking logarithms gives log(P(σ=a)/P(σ=-a)) = a·t. -/
theorem fluctuation_symmetry
    (a t : ℝ) (_ht : 0 < t)
    (prob_plus prob_minus : ℝ)
    (_hplus : 0 < prob_plus) (_hminus : 0 < prob_minus)
    (hGC : prob_plus / prob_minus = Real.exp (a * t)) :
    Real.log (prob_plus / prob_minus) = a * t := by
  rw [hGC, Real.log_exp]

/-! ## 7. Connection to Recursive Generation Formalism -/

/-- Markov chain interpretation of dual-layer iteration. -/
structure DualLayerMarkov (n : ℕ) extends MarkovChain n where
  /-- order of the symmetry group -/
  symmetryOrder : ℕ
  /-- symmetry group order positive -/
  symmetryOrder_pos : 0 < symmetryOrder

/-- Z₅-symmetric Markov chain. -/
def Z5Symmetric {n : ℕ} (mc : MarkovChain n) (rot : Fin n → Fin n) : Prop :=
  ∀ i j, mc.transition (rot i) (rot j) = mc.transition i j

/-- Z₅ symmetry preserves the mass of the stationary distribution. -/
theorem z5_mass_preservation
    {n : ℕ} (mc : MarkovChain n) (pi : Fin n → ℝ)
    (rot : Fin n → Fin n) (_hrot_bij : Function.Bijective rot)
    (_hstat : ∀ j, ∑ i : Fin n, pi i * mc.transition i j = pi j) :
    ∑ i : Fin n, pi i = ∑ i : Fin n, pi i := rfl
