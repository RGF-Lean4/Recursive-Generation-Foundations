import Mathlib
import RGF.Generative.Locking.QuinticLocking
import RGF.Generative.Locking.EmergentDimensionRelation
import RGF.Generative.Locking.DimensionThreeUnique
import RGF.Generative.Uniqueness.RecoveryTimeUnique
import RGF.Phenomenology.StandardModel.StandardModel26Parameters

/-!
# Unified locking-criterion audit suite

This file institutionalises the audit method that was first applied ad hoc to the
five-fold (membrane) locking result (`RGFInvariant.emergence_criterion_is_definitional`).
The point of the suite is to ask **the same question of every "uniqueness / necessity"
locking result in the framework**, under one uniform standard, instead of auditing one
result only when pushed by an external critique.

For each locking result we separate two independent questions.

* **(A) Is the target numeric value baked into the criterion's definition?**
  i.e. is the conclusion (`k = 5`, `d = 3`, `R = 1`, `26`) literally written into the
  `def` of the criterion, so that "uniqueness" is a tautological restatement?
  This is machine-checkable: we exhibit the criterion evaluated at *other* inputs and
  show it takes *other* values (`*_target_not_baked_in`).

* **(B) Is the criterion itself (the choice of which quantity to constrain) forced by a
  more primitive generative fact, or is it definitionally identified with the
  conclusion / stipulated as a numeric constant?**
  The extreme failure of (B) is a `Iff.rfl` identity between the physical premise and the
  mathematical criterion; the extreme success of (B) is a criterion that is a *theorem*
  proved from lattice/representation-theoretic primitives.

## Graded verdict (see the individual theorems below)

| result                              | (A) target baked in? | (B) criterion source                                   | verdict            |
|-------------------------------------|----------------------|--------------------------------------------------------|--------------------|
| membrane locking `k = 5`            | no                   | physics premise **≡** `¬Solvable Sₖ` by `Iff.rfl`      | **definitional**   |
| emergent relation `2d−1 = k`        | no                   | **theorem** from orbit–stabiliser (`relation_of_symmetry`) | **derived**    |
| dimension `d = 3` (`RecoveryTime`)  | no                   | equation between two stipulated numeric functions       | **conditional**    |
| joint `(d,R)=(3,1)`                 | no                   | intersection of two lattice/analytic forms, target `5` imported | **conditional** |
| Standard-Model `26` parameters      | no                   | closed-form count forced by `N = 3` + gauge group       | **derived**        |

Only the membrane result is *definitionally circular*: its physics→group step is an
`Iff.rfl`. The dimension / recovery results are honest conditionals — their target value
is not baked in, but they consume the numeric input `5`, whose ultimate grounding traces
back to the (still open) membrane criterion. The emergent-dimension relation and the
26-parameter count are the two genuinely *derived* results: no target is baked in and the
criterion is a theorem / a forced computation, not a stipulation.

Every statement below is machine-checked with zero `sorry` and only standard axioms.
-/

namespace RGF.LockingAudit

open RGFInvariant

/-! ## 1. Membrane locking `k = 5` — DEFINITIONAL (fails audit (B) maximally) -/

/-- **Audit (B), membrane.** The physical "emergence" premise is, *by definition*, the
statement that `S_k` is non-solvable: the proof is `Iff.rfl`. Hence the group-theoretic
criterion is not derived from a more primitive generative axiom; it is inserted as the
meaning of "emergence". This is the one result that is genuinely *definitionally circular*
at its physics→mathematics step. -/
theorem membrane_criterion_is_definitional (sys : RecursiveSystem) :
    EmergenceCondition sys ↔ ¬ IsSolvable (Equiv.Perm (Fin sys.k)) :=
  emergence_criterion_is_definitional sys

/-! ## 2. Recovery time `R = 1` — CONDITIONAL (passes (A), (B) is an equation) -/

/-- **Audit (B), recovery.** The recovery criterion is *not* a definitional restatement of
`R = 1`. It unfolds definitionally to an **equation between two independently defined
numeric functions**: the pole-order function `alpha_num R = 3 + 2R` and the
effective-direction-count function `n_eff R`. Solving that equation (not unfolding it)
gives `R = 1`; the proof of `r_equals_one_unique` requires a genuine case analysis, not
`Iff.rfl`. -/
theorem recovery_criterion_is_equation (R : ℕ) :
    emergence_condition R ↔ (alpha_num R = n_eff R) :=
  Iff.rfl

/-- **Audit (A), recovery.** The conclusion `R = 1` is not written into the criterion.
The two stipulated inputs are ordinary numeric functions (`alpha_num`, `n_eff`); the
criterion holds at `R = 1` and fails at the neighbouring values `R = 0, 2`, so `R = 1` is
solved for, not stipulated. -/
theorem recovery_target_not_baked_in :
    emergence_condition 1 ∧ ¬ emergence_condition 0 ∧ ¬ emergence_condition 2 :=
  ⟨(r_equals_one_unique 1).mpr rfl, r_zero_excluded, r_ge_two_excluded 2 (by norm_num)⟩

/-! ## 3. Dimension `d = 3` (`DimensionThreeUnique`) — CONDITIONAL (target `5` imported) -/

open FeasibilityLattice in
/-- **Audit (A), dimension.** The forward-direction criterion is the structural form
`latticeForward d = 2d − 1`; the target `5` is not baked in — it is the imported locking
value `k = 5`. The criterion selects `d = 3` because `2·3 − 1 = 5`, and takes other values
at other dimensions (`d = 2 ↦ 3`, `d = 4 ↦ 7`). Thus `d = 3` is solved for, but the
criterion inherits whatever grounding the imported number `5` has. -/
theorem dimension_target_not_baked_in :
    latticeForward 3 = 5 ∧ latticeForward 2 = 3 ∧ latticeForward 4 = 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

open FeasibilityLattice in
/-- **Audit (B), dimension.** The two criteria are genuinely *independent* forms: the
lattice count `latticeForward d = 2d − 1` does not depend on the recovery order `R`, while
the pole order `forsPoleOrder d R = d + 2R` does. Requiring both to equal `5` has the
unique solution `(d, R) = (3, 1)` — a real intersection, not a single tunable count. -/
theorem dimension_joint_unique :
    ∃! p : ℕ × ℕ, latticeForward p.1 = 5 ∧ forsPoleOrder p.1 p.2 = 5 :=
  dimension_three_unique

/-! ## 4. Emergent dimension relation `2d − 1 = k` — DERIVED (best case for (B)) -/

/-- **Audit (A), emergent relation.** The relation `2d − 1 = k` is a genuine constraint,
not a tautology: it holds at `(k, d) = (5, 3)` and fails at `(5, 2)` — so `d = 3` is forced
by `k = 5`, not written in. -/
theorem emergent_relation_target_not_baked_in :
    RGF.EmergentDimension.EmergentDimensionRelation 5 3 ∧
      ¬ RGF.EmergentDimension.EmergentDimensionRelation 5 2 := by
  unfold RGF.EmergentDimension.EmergentDimensionRelation
  refine ⟨?_, ?_⟩ <;> decide

/-- **Audit (B), emergent relation.** In contrast to the membrane case, the relation
`2d − 1 = k` is **not** asserted as a definitional identity: it is a *theorem* proved from a
critical symmetry structure via the orbit–stabiliser theorem (`relation_of_symmetry`), with
no numerical bridging hypothesis. This is the shape a locking criterion should have to pass
audit (B). -/
theorem emergent_relation_is_derived
    (k d : ℕ) [NeZero k] (incoming : LatticeToFORS.LatticeDir d)
    (Dir : Type) [MulAction (DihedralGroup k) Dir]
    [MulAction.IsPretransitive (DihedralGroup k) Dir] (base : Dir)
    (hstab : Nat.card (MulAction.stabilizer (DihedralGroup k) base) = 2)
    (realize : Dir ≃ ↥(LatticeToFORS.allowedNext incoming)) :
    RGF.EmergentDimension.EmergentDimensionRelation k d :=
  RGF.EmergentDimension.relation_of_symmetry k d incoming Dir base hstab realize

/-! ## 5. Standard-Model `26` parameters — DERIVED (forced computation) -/

/-- **Audit (A), 26 parameters.** The number `26` appears in *no* definition: it is the
value of the closed-form count `4N + 2(N−1)² + 6` at `N = 3`. At two or four generations the
same count gives `16` and `40`, so `26` is a forced consequence of `N = 3`, not a fitted
target. -/
theorem sm26_target_not_baked_in :
    RGF.StandardModel26.totalSMParams 2 = 16 ∧
      RGF.StandardModel26.totalSMParams 3 = 26 ∧
      RGF.StandardModel26.totalSMParams 4 = 40 :=
  RGF.StandardModel26.twenty_six_specific_to_three_generations

/-- **Audit (B), 26 parameters.** The count is a forced computation from the two RGF
structural inputs — generation number `N = d = 3` and the gauge group `SU(3)×SU(2)×U(1)`
from the `5 = 3 + 2` partition — via ordinary textbook parameter counting. -/
theorem sm26_is_derived :
    rgfPrediction.emergentDim = 3 ∧
      (∀ N, RGF.StandardModel26.totalSMParams N = 4 * N + 2 * (N - 1) ^ 2 + 6) ∧
      RGF.StandardModel26.totalSMParams rgfPrediction.emergentDim = 26 :=
  ⟨rfl, RGF.StandardModel26.totalSMParams_closed_form, by decide⟩

end RGF.LockingAudit
