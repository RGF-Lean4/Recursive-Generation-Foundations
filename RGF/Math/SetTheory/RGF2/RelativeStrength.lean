/-
  RGF2/RelativeStrength.lean   (module `RGF2.RelativeStrength`)

  **§4 — Separating object theory from metatheory, and honest strength labeling.**

  The transfinite/choice results of `RGF2/Hierarchy/Transfinite.lean`
  (`wellOrdering`, `hartogs`, `choiceFn`) and of `RGF2/Boolean/ChoiceReplacement.lean`
  (`valid_choice`) are proved using the *ambient* host axioms — Lean/Mathlib's
  `Classical.choice` and `zorn_subset_nonempty`.  Deriving "the axiom of choice holds
  internally" from the host's own axiom of choice says nothing about RGF's *own*
  consistency strength: an object theory built on Lean+Mathlib (itself of ZFC
  strength) cannot exceed its host.  The honest statement is *relative*: RGF is
  interpretable in / consistent relative to ZFC — **not** "≥ ZFC" or "beyond ZFC".

  This file makes that separation explicit and machine-checkable:

    1. **`RGFAxiomSuite`** bundles RGF's own choice-flavoured axioms (choice,
       well-ordering) as *explicit hypotheses*, so internal theorems are proved
       *from the structure* (relative interpretation) rather than silently borrowing
       the host's axioms.
    2. The **relative** internal theorems `relative_choiceFn`, `relative_wellOrdering`
       derive the internal principles from `RGFAxiomSuite`.  Their `#print axioms`
       audits show they do **not** invoke `Classical.choice`: all the choice content
       is quarantined inside the assumed suite.  (Hartogs is treated separately: its
       very *statement* is phrased with the host's ordinal/cardinal apparatus, so it
       is intrinsically host machinery and cannot be quarantined the same way.)
    3. **`rgfAxiomSuite_of_host`** exhibits the host's realization of the suite; its
       axiom audit *does* register `Classical.choice`.  This pins the honest reading:
       the suite is satisfiable *because ZFC (the host) satisfies it*, i.e. RGF is
       consistent **relative to** ZFC — it does not reach or exceed ZFC strength.
    4. Axiom audits of the ambient `RGF.RGF2.wellOrdering` / `hartogs` / `choiceFn`
       are re-run here so the `Classical.choice` dependence is on the record.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Hierarchy.Transfinite

open Ordinal Cardinal

universe u

namespace RGF
namespace RGF2

/-- **RGF's own choice-flavoured axioms, as explicit hypotheses.**  Bundling them into
a structure realizes the object-theory / metatheory separation: internal theorems are
proved *relative to* this suite (a relative interpretation), so they carry exactly
the strength of the assumed axioms — no more, no less — instead of silently
inheriting the host's `Classical.choice`. -/
structure RGFAxiomSuite where
  /-- Axiom of Choice (choice-function form) as an explicit assumption. -/
  choice : ∀ {ι : Type u} (X : ι → Type u), (∀ i, Nonempty (X i)) → Nonempty (Π i, X i)
  /-- Well-ordering theorem as an explicit assumption. -/
  wo : ∀ (α : Type u), ∃ r : α → α → Prop, IsWellOrder α r

/-! ## Relative internal theorems (proved *from* the suite, not from the host) -/

/-- **Relative AC.**  The internal choice function is derived *from* the explicit
RGF axiom suite.  Its axiom audit shows no `Classical.choice`: the choice content
lives entirely in the hypothesis `A`. -/
theorem relative_choiceFn (A : RGFAxiomSuite.{u}) {ι : Type u} (X : ι → Type u)
    (h : ∀ i, Nonempty (X i)) : Nonempty (Π i, X i) :=
  A.choice X h

/-- **Relative well-ordering.**  Derived from the suite, not from the host.  Its
axiom audit shows no `Classical.choice`. -/
theorem relative_wellOrdering (A : RGFAxiomSuite.{u}) (α : Type u) :
    ∃ r : α → α → Prop, IsWellOrder α r :=
  A.wo α

/-- **Relative interpretation, honestly stated.**  Whenever the RGF axiom suite is
realizable in the metatheory, the internal choice and well-ordering principles hold.
The strength RGF carries is therefore *bounded by* the strength needed to realize the
suite — this is a relative interpretation, the honest content behind "RGF has the
axiom of choice / well-ordering". -/
theorem rgf_internal_from_suite (A : RGFAxiomSuite.{u}) :
    (∀ {ι : Type u} (X : ι → Type u), (∀ i, Nonempty (X i)) → Nonempty (Π i, X i)) ∧
      (∀ (α : Type u), ∃ r : α → α → Prop, IsWellOrder α r) :=
  ⟨fun X h => relative_choiceFn A X h, relative_wellOrdering A⟩

/-! ## The host realizes the suite — RGF is consistent *relative to* ZFC -/

/-- **The host (Lean+Mathlib, of ZFC strength) realizes the RGF axiom suite.**  This
is where `Classical.choice` genuinely enters (see the axiom audit below).  It shows
the suite is satisfiable *because the ZFC-strength host satisfies it* — i.e. RGF is
interpretable in / consistent relative to ZFC.  It does **not** show RGF reaches or
exceeds ZFC strength; by construction it cannot, being built inside the host. -/
noncomputable def rgfAxiomSuite_of_host : RGFAxiomSuite.{u} where
  choice := fun X h => ⟨fun i => (h i).some⟩
  wo := fun α => by obtain ⟨_⟩ := exists_wellOrder α; exact ⟨(· < ·), inferInstance⟩

/-! ## Axiom audits — the honest labeling

The *relative* theorems must NOT depend on `Classical.choice` (their choice content
is in the hypothesis); the *host realization* and the ambient internal theorems DO.
-/

-- relative theorems: choice content quarantined in the hypothesis
#print axioms relative_choiceFn
#print axioms relative_wellOrdering
#print axioms rgf_internal_from_suite

-- host realization + ambient internal theorems: `Classical.choice` on the record
#print axioms rgfAxiomSuite_of_host
#print axioms RGF.RGF2.wellOrdering
#print axioms RGF.RGF2.hartogs
#print axioms RGF.RGF2.choiceFn

end RGF2
end RGF
