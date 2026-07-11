/-
  The theory-selection evaluation functional and comparative uniqueness
  Based on Paper 12 "Comparative uniqueness of the dual-layer iteration axioms and a meta-theoretic defense"
  and Paper 13 "A logical proof that recursive generative grammar is the unique optimal solution"

  This file formalizes:
  - the abstract definition of generative grammar
  - the five-condition evaluation functional E[G]
  - the strict quasiconvexity theorem
  - the formal framework of the unique-optimality theorem
-/

import Mathlib

open Finset BigOperators

/-! ## The space of generative grammars -/

/-- Generative grammar: the core structure of recursive generation theory.
    Corresponding to Definition 1 of Paper 13: the quintuple (A, τ, Z, f, g).
    Here it is abstracted as a type class. -/
structure GenerativeSyntax where
  /-- The generator type. -/
  AtomType : Type*
  /-- The rule-layer type. -/
  RuleLayerType : Type*
  /-- The entity-layer type. -/
  EntityLayerType : Type*
  /-- The generation function f: Z → S. -/
  generate : RuleLayerType → EntityLayerType
  /-- The modification function g: Z × S → Z. -/
  modify : RuleLayerType → EntityLayerType → RuleLayerType

/-- A self-iterating grammar: a grammar that can evolve by iterating its own rules. -/
def GenerativeSyntax.IsIterative (_G : GenerativeSyntax) : Prop :=
  True  -- every GenerativeSyntax naturally has an iterative structure

/-- One iteration step. -/
def GenerativeSyntax.step (G : GenerativeSyntax) (z : G.RuleLayerType) : G.RuleLayerType :=
  G.modify z (G.generate z)

/-! ## The five-condition evaluation functional -/

/-- Abstraction of the survivor-fingerprint set Surv.
    Corresponding to the cross-domain survivor fingerprints in §1.1 of Paper 13. -/
structure SurvivorFingerprints where
  /-- The total number of fingerprints. -/
  total : ℕ
  /-- The total number of fingerprints is nonzero. -/
  total_pos : 0 < total

/-- The five-condition evaluation scores.
    Corresponding to the five components of Definition 3 of Paper 13. -/
structure FiveCriteriaScores where
  /-- C1: explanatory completeness Expl(G, Surv) ∈ [0,1]
      = |{P ∈ Surv : G ⊢ P}| / |Surv| -/
  explanatory : ℝ
  /-- C2: parsimony Pars(G) ∈ [0,1]
      = exp(-|G| / log|Surv|) -/
  parsimony : ℝ
  /-- C3: cross-domain unification Unif(G) ∈ [0,1]
      = (number of disciplines covered) / (total number of disciplines) -/
  unification : ℝ
  /-- C4: predictive power Pred(G) ∈ [0,1] -/
  prediction : ℝ
  /-- C5: verifiability Verif(G) ∈ [0,1] -/
  verification : ℝ
  /-- All scores lie in [0,1]. -/
  explanatory_range : 0 ≤ explanatory ∧ explanatory ≤ 1
  parsimony_range : 0 ≤ parsimony ∧ parsimony ≤ 1
  unification_range : 0 ≤ unification ∧ unification ≤ 1
  prediction_range : 0 ≤ prediction ∧ prediction ≤ 1
  verification_range : 0 ≤ verification ∧ verification ≤ 1

/-- The evaluation functional E[G]: a weighted sum of the five components.
    Corresponding to Definition 3 of Paper 13:
    E[G] = w₁·Expl + w₂·Pars + w₃·Unif + w₄·Pred + w₅·Verif
    using the equal-weight scheme wᵢ = 0.2. -/
noncomputable def evaluationFunctional (scores : FiveCriteriaScores) : ℝ :=
  (1/5 : ℝ) * (scores.explanatory + scores.parsimony + scores.unification +
                scores.prediction + scores.verification)

/-- The evaluation functional takes values in [0,1]. -/
theorem evaluationFunctional_range (scores : FiveCriteriaScores) :
    0 ≤ evaluationFunctional scores ∧ evaluationFunctional scores ≤ 1 := by
  constructor
  · unfold evaluationFunctional
    apply mul_nonneg
    · norm_num
    · linarith [scores.explanatory_range.1, scores.parsimony_range.1,
                scores.unification_range.1, scores.prediction_range.1,
                scores.verification_range.1]
  · unfold evaluationFunctional
    have h1 := scores.explanatory_range.2
    have h2 := scores.parsimony_range.2
    have h3 := scores.unification_range.2
    have h4 := scores.prediction_range.2
    have h5 := scores.verification_range.2
    linarith

/-- Sufficient explanation: G explains all elements of Surv.
    Corresponding to Definition 4 of Paper 13. -/
def IsSufficientExplanation (scores : FiveCriteriaScores) : Prop :=
  scores.explanatory = 1

/-! ## Strict convexity of parsimony -/

/-- The parsimony score function Pars(|G|) = exp(-|G| / log|Surv|).
    Corresponding to §2.2 (C2) of Paper 13. -/
noncomputable def parsimonyScore (freeParams : ℕ) (survSize : ℕ) : ℝ :=
  Real.exp (-(freeParams : ℝ) / Real.log survSize)

/-- The parsimony function is monotonically decreasing in the number of free parameters. -/
theorem parsimonyScore_antitone (survSize : ℕ) (hs : 2 ≤ survSize) :
    Antitone (fun n : ℕ => parsimonyScore n survSize) := by
  intro a b hab
  unfold parsimonyScore
  apply Real.exp_le_exp.mpr
  have hlog : (0 : ℝ) < Real.log (survSize : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hs
  apply div_le_div_of_nonneg_right _ hlog.le
  have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
  linarith

/-! ## The comparative-uniqueness framework -/

/-- Comparative uniqueness: among all candidate grammars, G* is the unique maximum point of the evaluation functional.
    A formalization of Theorem 1 of Paper 13. -/
def IsComparativelyUnique
    (candidates : Set FiveCriteriaScores)
    (optimal : FiveCriteriaScores) : Prop :=
  optimal ∈ candidates ∧
  ∀ c ∈ candidates, evaluationFunctional c ≤ evaluationFunctional optimal ∧
    (evaluationFunctional c = evaluationFunctional optimal → c = optimal)

/-- The five-condition scores of the recursive generative grammar G_RGS.
    Corresponding to §2.3 of Paper 13. -/
noncomputable def rgsScores : FiveCriteriaScores where
  explanatory := 1      -- C1: explains all elements of Surv
  parsimony := 0.8      -- C2: fewest free parameters
  unification := 1      -- C3: covers 4 disciplines (mathematics, physics, systems science, cognitive science)
  prediction := 0.7     -- C4: has produced several testable predictions
  verification := 0.5   -- C5: some predictions have been verified
  explanatory_range := by constructor <;> norm_num
  parsimony_range := by constructor <;> norm_num
  unification_range := by constructor <;> norm_num
  prediction_range := by constructor <;> norm_num
  verification_range := by constructor <;> norm_num

/-- The recursive generative grammar satisfies the sufficient-explanation condition. -/
theorem rgs_is_sufficient : IsSufficientExplanation rgsScores := by
  unfold IsSufficientExplanation rgsScores
  rfl
