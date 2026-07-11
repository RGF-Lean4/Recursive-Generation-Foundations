/-
  Information geometry: KL divergence and the metric structure of the emergent probability space
  Information Geometry: KL Divergence and Metric Structure of Emergence Probability Spaces

  Formalizes:
  - basic properties of probability distributions
  - the definition and properties of KL divergence (relative entropy)
  - the framework of the Fisher information matrix
  - the geometric structure of the emergent probability space
  - the information-theoretic features of the quintic structure
-/

import Mathlib

open Finset BigOperators Real

/-! ## 1. Finite probability distributions -/

structure ProbDist (n : ℕ) where
  weights : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weights i
  sum_one : ∑ i : Fin n, weights i = 1

noncomputable def uniformDist (n : ℕ) (hn : 0 < n) : ProbDist n where
  weights := fun _ => 1 / n
  nonneg := fun _ => by positivity
  sum_one := by
    simp [Finset.sum_const, nsmul_eq_mul]
    field_simp

theorem probDist_le_one {n : ℕ} (p : ProbDist n) (i : Fin n) :
    p.weights i ≤ 1 := by
  calc p.weights i ≤ ∑ j : Fin n, p.weights j :=
      Finset.single_le_sum (fun j _ => p.nonneg j) (Finset.mem_univ i)
    _ = 1 := p.sum_one

/-! ## 2. Shannon entropy -/

noncomputable def shannonEntropy {n : ℕ} (p : ProbDist n) : ℝ :=
  -∑ i : Fin n, if p.weights i = 0 then 0 else p.weights i * Real.log (p.weights i)

theorem shannonEntropy_nonneg {n : ℕ} (p : ProbDist n)
    (hpos : ∀ i, 0 < p.weights i) : 0 ≤ shannonEntropy p := by
  exact neg_nonneg_of_nonpos ( Finset.sum_nonpos fun i _ => by split_ifs <;> nlinarith [ hpos i, Real.log_nonpos ( le_of_lt ( hpos i ) ) ( probDist_le_one p i ) ] )

/-! ## 3. KL divergence -/

noncomputable def klDivergence {n : ℕ} (p q : ProbDist n) : ℝ :=
  ∑ i : Fin n, if p.weights i = 0 then 0
    else p.weights i * Real.log (p.weights i / q.weights i)

theorem kl_self {n : ℕ} (p : ProbDist n) :
    klDivergence p p = 0 := by
  simp only [klDivergence]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with h
  · rfl
  · simp [div_self h, Real.log_one]

/-! ## 4. Cross entropy -/

noncomputable def crossEntropy {n : ℕ} (p q : ProbDist n) : ℝ :=
  -∑ i : Fin n, if p.weights i = 0 then 0 else p.weights i * Real.log (q.weights i)

theorem kl_cross_entropy_relation {n : ℕ} (p q : ProbDist n)
    (hq : ∀ i, 0 < q.weights i) :
    klDivergence p q = crossEntropy p q - shannonEntropy p := by
  simp +decide [ klDivergence, crossEntropy, shannonEntropy ];
  rw [ ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib ] ; congr ; ext i ; split_ifs <;> simp +decide [ *, Real.log_div, ne_of_gt ] ; ring;

/-! ## 5. Fisher information -/

noncomputable def fisherInformationDiag {n : ℕ}
    (logLikGrad : Fin n → ℝ) (p : ProbDist n) : ℝ :=
  ∑ i : Fin n, p.weights i * logLikGrad i ^ 2

theorem fisherInformation_nonneg {n : ℕ}
    (logLikGrad : Fin n → ℝ) (p : ProbDist n) :
    0 ≤ fisherInformationDiag logLikGrad p := by
  apply Finset.sum_nonneg
  intro i _; apply mul_nonneg (p.nonneg i) (sq_nonneg _)

/-! ## 6. The emergent probability space -/

structure EmergenceProbDist extends ProbDist 5 where
  z5_symmetric : ∀ i j : Fin 5, weights i = weights j

theorem emergence_is_uniform (p : EmergenceProbDist) :
    ∀ i : Fin 5, p.weights i = 1 / 5 := by
  have := p.z5_symmetric 0; have := p.sum_one; simp_all +decide [ Fin.sum_univ_five ] ;
  grind

noncomputable def maxEntropyFive : ℝ := Real.log 5

theorem z5_symmetric_entropy (p : EmergenceProbDist)
    (_hpos : ∀ i, 0 < p.weights i) :
    shannonEntropy p.toProbDist = Real.log 5 := by
  unfold shannonEntropy;
  rw [ show p.weights = fun _ => 1 / 5 from funext fun _ => emergence_is_uniform p _ ] ; norm_num [ Real.log_div ];
  ring

/-! ## 7. Information-efficiency ratio -/

noncomputable def infoEfficiencyRatio : ℝ := Real.log 5 / Real.log 4

theorem info_efficiency_gt_one : 1 < infoEfficiencyRatio := by
  exact one_lt_div ( Real.log_pos ( by norm_num ) ) |>.2 ( Real.log_lt_log ( by norm_num ) ( by norm_num ) )

/-! ## 8. Mutual information -/

noncomputable def mutualInformation {n m : ℕ}
    (joint : ProbDist (n * m))
    (marginal1 : ProbDist n) (marginal2 : ProbDist m)
    (embed : Fin n → Fin m → Fin (n * m)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m,
    if joint.weights (embed i j) = 0 then 0
    else joint.weights (embed i j) *
      Real.log (joint.weights (embed i j) / (marginal1.weights i * marginal2.weights j))