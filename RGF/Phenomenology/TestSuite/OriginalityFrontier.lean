/-
  RequestProject/OriginalityFrontier.lean

  Meta-mathematical diagnosis of the originality gap.

  We model a "theory" abstractly as a provability predicate on a type of
  sentences, and a *faithful translation* between two theories as a map on
  sentences that both preserves and reflects provability.

  Results:
    * `reencoding_conservative` : a faithful translation proves nothing new —
      the precise cause of the originality gap.
    * `frontier_empty`          : the *originality frontier* of a faithful
      re-encoding (sentences provable downstream but not upstream) is empty.
    * `nonempty_frontier_not_faithful` : conversely, a genuinely new theorem
      forces the translation to be *unfaithful* — the only source of new
      theorems is adding a genuinely independent statement.
-/
import Mathlib

namespace RGF.Originality

/-- A theory, abstracted as a provability predicate on a sentence type. -/
structure ProofSystem (S : Type*) where
  Provable : S → Prop

/-- A faithful translation: a map on sentences that both preserves and reflects
    provability. -/
structure Faithful {S T : Type*} (A : ProofSystem S) (B : ProofSystem T) where
  /-- The translation on sentences. -/
  t : S → T
  /-- Faithfulness: downstream provability of the translation is equivalent to
      upstream provability of the source. -/
  spec : ∀ s, B.Provable (t s) ↔ A.Provable s

/-- Re-encoding is conservative: through a faithful translation, every downstream
    theorem comes from an upstream theorem. -/
theorem reencoding_conservative {S T : Type*} {A : ProofSystem S} {B : ProofSystem T}
    (F : Faithful A B) (s : S) : B.Provable (F.t s) → A.Provable s :=
  (F.spec s).mp

/-- And conversely, every upstream theorem survives translation. -/
theorem reencoding_preserves {S T : Type*} {A : ProofSystem S} {B : ProofSystem T}
    (F : Faithful A B) (s : S) : A.Provable s → B.Provable (F.t s) :=
  (F.spec s).mpr

/-- The *originality frontier* of a translation `t`: sentences whose translation
    is provable downstream but which are not provable upstream. -/
def Frontier {S T : Type*} (A : ProofSystem S) (B : ProofSystem T) (t : S → T) : Set S :=
  {s | B.Provable (t s) ∧ ¬ A.Provable s}

/-- A faithful re-encoding has an empty originality frontier. -/
theorem frontier_empty {S T : Type*} {A : ProofSystem S} {B : ProofSystem T}
    (F : Faithful A B) : Frontier A B F.t = ∅ := by
  ext s
  simp only [Frontier, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  intro h
  exact (F.spec s).mp h

/-- Conversely, a genuinely new theorem (a point of the frontier) forces *any*
    translation realizing it to be unfaithful: the only source of new theorems is
    adding a genuinely independent statement. -/
theorem nonempty_frontier_not_faithful {S T : Type*} (A : ProofSystem S)
    (B : ProofSystem T) (t : S → T) (s : S)
    (hs : B.Provable (t s) ∧ ¬ A.Provable s) :
    ¬ ∃ F : Faithful A B, F.t = t := by
  rintro ⟨F, rfl⟩
  exact hs.2 ((F.spec s).mp hs.1)

end RGF.Originality
