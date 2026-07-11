/-
  RGF/Generative/Locking/CircularityMetaTheorem.lean

  Direction VII — from "try to prove the criterion is non-circular" to
  "characterise the *structural upper bound* on such bridges".

  The membrane-locking audit (`LockingAuditSuite.membrane_criterion_is_definitional`,
  `RGFInvariant.emergence_criterion_is_definitional`) established one concrete fact:
  the physical premise `EmergenceCondition` is, as a predicate, *definitionally equal*
  to the group-theoretic criterion "`S_k` is non-solvable" (proof `Iff.rfl`).

  Rather than keep trying to *prove* that this criterion is non-circular — which, in the
  present modelling, is impossible because the two sides are the same predicate — this
  file takes the more productive meta-step suggested by the audit: it states and proves,
  in full generality, **why a definitional bridge can never constitute an independent
  derivation of its criterion.**  This is a small "structural upper bound" meta-theorem:
  it does not close the open problem, it *delimits* it, by proving that a whole class of
  attempted closures (any that route the criterion through a premise defined to equal it)
  are informationally empty.

  ## What is modelled, and its limitation

  We model "the premise `P` has no independent content beyond the criterion `Q`" by the
  strongest possible form of that statement: `P = Q` as predicates (`DefinitionalBridge`).
  This is exactly the situation the framework is currently in for membrane locking.  We do
  **not** attempt the fully general informal claim "*any* way of selecting a criterion can
  be re-expressed as a definition" — that would require first formalising "an arbitrary way
  of selecting a criterion", which is itself an open research question.  What is proved here
  is the definitional-bridge case, which is the case that actually occurs, together with its
  honest instantiation on `EmergenceCondition`.

  Every statement is machine-checked with zero `sorry` and only standard axioms.
-/
import Mathlib
import RGF.Generative.Locking.QuinticLocking

namespace RGF.CircularityMeta

/-! ## 1. Definitional bridges in general -/

variable {α : Sort*}

/-- A **definitional bridge** between a "physical premise" `P` and a "mathematical
criterion" `Q`: the premise is, as a predicate, nothing more than the criterion.  This is
the strongest form of "`P` carries no independent content beyond `Q`". -/
def DefinitionalBridge (P Q : α → Prop) : Prop := P = Q

/-- A definitional bridge is, pointwise, the trivial biconditional (`Iff.rfl` when the
equality itself is `rfl`).  This is the general form of
`RGFInvariant.emergence_criterion_is_definitional`. -/
theorem bridge_iff {P Q : α → Prop} (h : DefinitionalBridge P Q) (a : α) : P a ↔ Q a := by
  rw [h]

/-- **The core structural upper bound.**  If `P` is a definitional bridge to `Q`, then for
*every* conclusion predicate `R`, the statement "`P` forces `R`" is the *identical
proposition* to "`Q` forces `R`".  Consequently:

* taking `R := Q`, "deriving the criterion `Q` from the premise `P`" is literally the same
  proposition as the trivial "`Q → Q`"; the bridge can never be an *independent* derivation
  of `Q`;
* any necessity/uniqueness theorem proved "via `P`" is, verbatim, the theorem proved "via
  `Q`" — routing a result through the physical premise adds no deductive content.

This delimits (does not close) the open problem: no closure that factors through a
definitional bridge can succeed, so an honest closure must first replace the definitional
identification by an *independent* definition of the physical premise. -/
theorem definitional_bridge_no_independent_content {P Q : α → Prop}
    (h : DefinitionalBridge P Q) :
    (∀ R : α → Prop, (∀ a, P a → R a) = (∀ a, Q a → R a)) ∧
      (∀ a, P a ↔ Q a) := by
  refine ⟨fun R => ?_, fun a => ?_⟩
  · rw [h]
  · rw [h]

/-- Specialisation to `R := Q`: "the premise forces the criterion" is the same proposition
as the trivial "the criterion forces itself".  The starkest form of the upper bound. -/
theorem forward_derivation_is_trivial {P Q : α → Prop} (h : DefinitionalBridge P Q) :
    (∀ a, P a → Q a) = (∀ a, Q a → Q a) :=
  (definitional_bridge_no_independent_content h).1 Q

/-! ## 2. Instantiation on the membrane-locking bridge

The framework's `EmergenceCondition` is a definitional bridge to non-solvability of `S_k`,
so the general upper bound applies verbatim: the "emergence ⟹ non-solvable" step is
informationally empty, which is exactly why `k = 5` remains *conditional* on the solvability
criterion (`RGFInvariant.k_five_conditional_on_solvability_criterion`). -/

/-- The membrane-locking premise is a definitional bridge: `EmergenceCondition` equals, as a
predicate, "`S_k` is non-solvable". -/
theorem emergence_is_definitional_bridge :
    DefinitionalBridge EmergenceCondition
      (fun sys : RecursiveSystem => ¬ IsSolvable (Equiv.Perm (Fin sys.k))) :=
  rfl

/-- **Instantiated upper bound.**  Because the emergence premise is a definitional bridge,
no theorem of the shape "emergence ⟹ `R`" carries content beyond "non-solvable ⟹ `R`"; in
particular the "emergence ⟹ non-solvable" bridge is informationally empty.  Hence the
necessity of the *solvability criterion itself* cannot be established by this route — the
residual open problem is genuine, not an artefact of a missing proof. -/
theorem emergence_bridge_no_independent_content :
    (∀ R : RecursiveSystem → Prop,
        (∀ sys, EmergenceCondition sys → R sys)
          = (∀ sys, (¬ IsSolvable (Equiv.Perm (Fin sys.k))) → R sys)) ∧
      (∀ sys, EmergenceCondition sys ↔ ¬ IsSolvable (Equiv.Perm (Fin sys.k))) :=
  definitional_bridge_no_independent_content emergence_is_definitional_bridge

end RGF.CircularityMeta
