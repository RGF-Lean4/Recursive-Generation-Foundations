/-
  RGF/ConstructiveErgodicity.lean

  Task III — Constructive ergodic theory and stochastic processes.

  A completely explicit, `sorry`-free development of the *Doeblin minorization
  condition* and the resulting *Harris-type geometric ergodicity* for Markov
  chains on a finite (measurable) state space.  Everything is stated and proved
  constructively in terms of the total-variation distance already introduced in
  `MixingTime.lean`; no external ergodic-theory library is used.

  Mathematical content:

  * `DoeblinCondition P ε ν` : the transition matrix `P` is minorized by
    `ε` times a fixed reference distribution `ν` (Doeblin's minorization).
  * `doeblin_tv_contraction` : the one-step Markov operator contracts the
    total-variation distance by the factor `(1 - ε)` (Dobrushin/Doeblin
    contraction).
  * `doeblin_tv_iterate` : the `n`-step operator contracts by `(1 - ε)^n`.
  * `doeblin_stationary_unique` : uniqueness of the stationary distribution
    (Harris recurrence gives at most one invariant law).
  * `doeblin_geometric_ergodicity` : any initial law converges to the
    stationary law geometrically fast — the constructive Harris ergodic theorem.
  * `doeblin_asymptotic_strong_mixing` : two arbitrary initial laws become
    asymptotically indistinguishable (asymptotic strong mixing).

  The development is finite-state (hence uses `Fintype S`); this keeps every
  estimate fully explicit and machine-checked.  The non-compact generalization
  (general measurable state spaces via Markov kernels) is the natural next step.
-/

import Mathlib
import RGF.Physics.Dynamics.MixingTime

open scoped BigOperators
open Finset

namespace RGF.Ergodicity

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A function on the state space is a probability distribution. -/
structure IsProbDist (μ : S → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ μ s
  sum_one : ∑ s : S, μ s = 1

/-- One step of the Markov operator acting on distributions (row-vector convention):
    `(stepDist P μ) j = ∑ i, μ i · P i j`. -/
noncomputable def stepDist (P : TransitionMatrix S) (μ : S → ℝ) : S → ℝ :=
  fun j => ∑ i : S, μ i * P.prob i j

omit [DecidableEq S] in
/-- The Markov operator preserves probability distributions. -/
theorem stepDist_isProbDist (P : TransitionMatrix S) {μ : S → ℝ}
    (hμ : IsProbDist μ) : IsProbDist (stepDist P μ) := by
  constructor
  · exact fun s => Finset.sum_nonneg fun i _ => mul_nonneg (hμ.nonneg i) (P.prob_nonneg i s)
  · convert hμ.sum_one using 1
    rw [Finset.sum_congr rfl fun j _ => show stepDist P μ j = ∑ i, μ i * P.prob i j from rfl,
      Finset.sum_comm]
    simp +decide [← Finset.mul_sum _ _ _, P.prob_sum]

/-- The Doeblin minorization condition: there is a level `ε ∈ (0,1]` and a
    reference probability distribution `ν` with `P i j ≥ ε · ν j` for all `i, j`. -/
structure DoeblinCondition (P : TransitionMatrix S) (ε : ℝ) (ν : S → ℝ) : Prop where
  eps_pos : 0 < ε
  eps_le_one : ε ≤ 1
  ref : IsProbDist ν
  minorize : ∀ i j, ε * ν j ≤ P.prob i j

omit [DecidableEq S] in
/-- Key algebraic identity: if `μ` and `μ'` both have total mass `1`, then the
    difference of the transported laws can be written with the minorized kernel
    `P i j - ε ν j`, because the reference term cancels. -/
theorem stepDist_sub_eq (P : TransitionMatrix S) (ε : ℝ) (ν : S → ℝ)
    {μ μ' : S → ℝ} (hμ : ∑ s, μ s = 1) (hμ' : ∑ s, μ' s = 1) (j : S) :
    stepDist P μ j - stepDist P μ' j
      = ∑ i : S, (μ i - μ' i) * (P.prob i j - ε * ν j) := by
  simp +decide [sub_mul, mul_sub, Finset.sum_sub_distrib, stepDist]
  simp +decide [← Finset.sum_mul _ _ _, hμ, hμ']

omit [DecidableEq S] in
/-- **Doeblin / Dobrushin contraction.** Under the Doeblin minorization the
    one-step Markov operator contracts the total-variation distance by the
    factor `(1 - ε)`. -/
theorem doeblin_tv_contraction {P : TransitionMatrix S} {ε : ℝ} {ν : S → ℝ}
    (h : DoeblinCondition P ε ν) {μ μ' : S → ℝ}
    (hμ : IsProbDist μ) (hμ' : IsProbDist μ') :
    totalVariation (stepDist P μ) (stepDist P μ') ≤ (1 - ε) * totalVariation μ μ' := by
  have h_abs : ∀ j, |stepDist P μ j - stepDist P μ' j|
      ≤ ∑ i, |μ i - μ' i| * (P.prob i j - ε * ν j) := by
    intro j
    rw [stepDist_sub_eq _ _ _ hμ.sum_one hμ'.sum_one]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.2 <| h.minorize i j)])
  convert mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h_abs j)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1
  rw [Finset.sum_comm]
  simp +decide [← Finset.mul_sum _ _ _, ← Finset.sum_mul, P.prob_sum, h.ref.sum_one, totalVariation]
  ring

/-- The `n`-fold Markov operator. -/
noncomputable def stepDistIter (P : TransitionMatrix S) (μ : S → ℝ) : ℕ → (S → ℝ)
  | 0 => μ
  | n + 1 => stepDist P (stepDistIter P μ n)

omit [DecidableEq S] in
/-- The iterates of a probability distribution stay probability distributions. -/
theorem stepDistIter_isProbDist (P : TransitionMatrix S) {μ : S → ℝ}
    (hμ : IsProbDist μ) (n : ℕ) : IsProbDist (stepDistIter P μ n) := by
  induction n with
  | zero => exact hμ
  | succ n ih => exact stepDist_isProbDist P ih

omit [DecidableEq S] in
/-- **Geometric contraction of the iterated operator.** -/
theorem doeblin_tv_iterate {P : TransitionMatrix S} {ε : ℝ} {ν : S → ℝ}
    (h : DoeblinCondition P ε ν) {μ μ' : S → ℝ}
    (hμ : IsProbDist μ) (hμ' : IsProbDist μ') (n : ℕ) :
    totalVariation (stepDistIter P μ n) (stepDistIter P μ' n)
      ≤ (1 - ε) ^ n * totalVariation μ μ' := by
  induction' n with n ih <;> simp_all +decide [pow_succ, mul_assoc]
  · rfl
  · convert le_trans (doeblin_tv_contraction h (stepDistIter_isProbDist P hμ n)
      (stepDistIter_isProbDist P hμ' n))
      (mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr h.eps_le_one)) using 1
    ring!

/-- A distribution is stationary for `P` if it is invariant under the operator. -/
def IsStationary (P : TransitionMatrix S) (π : S → ℝ) : Prop :=
  IsProbDist π ∧ stepDist P π = π

omit [DecidableEq S] in
/-- **Uniqueness of the stationary distribution (Harris).** Under the Doeblin
    condition there is at most one invariant law. -/
theorem doeblin_stationary_unique {P : TransitionMatrix S} {ε : ℝ} {ν : S → ℝ}
    (h : DoeblinCondition P ε ν) {π π' : S → ℝ}
    (hπ : IsStationary P π) (hπ' : IsStationary P π') :
    π = π' := by
  have h_contraction : totalVariation π π' ≤ (1 - ε) * totalVariation π π' := by
    convert doeblin_tv_contraction h hπ.1 hπ'.1 using 1
    rw [hπ.2, hπ'.2]
  have h_zero : totalVariation π π' = 0 := by
    nlinarith [h.eps_pos, h.eps_le_one, totalVariation_nonneg π π']
  exact funext fun i => eq_of_sub_eq_zero (by
    contrapose! h_zero
    exact ne_of_gt <| mul_pos (by norm_num) <| lt_of_lt_of_le (abs_pos.mpr h_zero) <|
      Finset.single_le_sum (fun x _ => abs_nonneg <| π x - π' x) <| Finset.mem_univ i)

omit [DecidableEq S] in
/-- **Constructive Harris ergodic theorem.** Given any stationary law `π`, every
    initial distribution converges to it geometrically in total variation. -/
theorem doeblin_geometric_ergodicity {P : TransitionMatrix S} {ε : ℝ} {ν : S → ℝ}
    (h : DoeblinCondition P ε ν) {π μ : S → ℝ}
    (hπ : IsStationary P π) (hμ : IsProbDist μ) (n : ℕ) :
    totalVariation (stepDistIter P μ n) π ≤ (1 - ε) ^ n * totalVariation μ π := by
  convert doeblin_tv_iterate h hμ hπ.1 n using 1
  rw [show stepDistIter P π n = π from _]
  exact Nat.recOn n rfl fun n ih => by
    rw [show stepDistIter P π (n + 1) = stepDist P (stepDistIter P π n) from rfl, ih, hπ.2]

omit [DecidableEq S] in
/-- **Asymptotic strong mixing.** Two arbitrary initial laws become
    indistinguishable at the geometric rate `(1-ε)^n`. -/
theorem doeblin_asymptotic_strong_mixing {P : TransitionMatrix S} {ε : ℝ} {ν : S → ℝ}
    (h : DoeblinCondition P ε ν) {μ μ' : S → ℝ}
    (hμ : IsProbDist μ) (hμ' : IsProbDist μ') (n : ℕ) :
    totalVariation (stepDistIter P μ n) (stepDistIter P μ' n) ≤ (1 - ε) ^ n := by
  refine le_trans (doeblin_tv_iterate h hμ hμ' n) ?_
  refine mul_le_of_le_one_right (pow_nonneg (sub_nonneg.2 h.eps_le_one) _) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ =>
    show |μ s - μ' s| ≤ μ s + μ' s from
      abs_le.mpr ⟨by linarith [hμ.nonneg s, hμ'.nonneg s],
        by linarith [hμ.nonneg s, hμ'.nonneg s]⟩) (by norm_num)) ?_
  rw [Finset.sum_add_distrib, hμ.sum_one, hμ'.sum_one]
  norm_num

end RGF.Ergodicity
