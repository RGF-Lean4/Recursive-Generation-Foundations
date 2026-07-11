/-
  RGF2/Boolean/IndependenceFamilyInfinite.lean
    (module `RGF2.Boolean.IndependenceFamilyInfinite`)

  **§5 — Making the "infinite antichain" of the ¬CH backbone literal.**

  `RGF2/Boolean/IndependenceFamily.lean` builds a family `y : ℕ → V^B` of pairwise
  independent, undecided membership conditions over `B = Set ℕ`, and honestly
  documents that the *full* relative-consistency metatheorem
  `Con(ZFC) → Con(ZFC + ¬CH)` is **not** attempted (it is Flypitch-scale) — only its
  combinatorial backbone.  This file keeps that scope statement intact and merely
  strengthens the backbone so the phrase "infinite antichain" is a *literal*
  theorem rather than only "indexed by `ℕ`":

    * `independent_conditions_injective` — the assignment `n ↦ ‖bempty ∈ y n‖` is
      injective (the conditions are genuinely distinct, not just distinctly indexed);
    * `independent_conditions_range_infinite` — hence the *set* of conditions
      `{ ‖bempty ∈ y n‖ | n }` is `Set.Infinite`: an honest infinite antichain of
      nonzero, pairwise-disjoint, undecided conditions.

  Scope statement (unchanged): this is the combinatorial mechanism by which forcing
  adds unboundedly many independent Cohen bits.  It is **not** a proof of
  `Con(ZFC) → Con(ZFC + ¬CH)`, which remains research engineering.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Boolean.Model
import RGF.Math.SetTheory.RGF2.Boolean.IndependenceFamily

namespace RGF
namespace RGF2
namespace BSet

/-- The canonical independence family over `B = Set ℕ`: `y n := bsingleton {n}`,
whose membership value is `‖bempty ∈ y n‖ = {n}`. -/
def indepFamily (n : ℕ) : BSet (Set ℕ) := bsingleton {n}

theorem indepFamily_value (n : ℕ) :
    BMem bempty (indepFamily n) = ({n} : Set ℕ) := by
  rw [indepFamily, BMem_bsingleton]

/-- **The conditions are genuinely distinct.**  The map `n ↦ ‖bempty ∈ y n‖` is
injective, so the family is a true antichain of distinct conditions, not merely an
`ℕ`-indexed list with possible repeats. -/
theorem independent_conditions_injective :
    Function.Injective (fun n => BMem bempty (indepFamily n)) := by
  intro n m h
  simp only [indepFamily_value] at h
  exact Set.singleton_injective h

/-- **Literal infinite antichain.**  Over `B = Set ℕ` the set of membership
conditions `{ ‖bempty ∈ y n‖ | n : ℕ }` is genuinely infinite, each condition is
strictly between `⊥` and `⊤` (undecided) and any two are disjoint.  This upgrades the
"infinite antichain" of the ¬CH backbone from an indexed family to a literal
`Set.Infinite` statement. -/
theorem independent_conditions_range_infinite :
    (Set.range (fun n => BMem bempty (indepFamily n))).Infinite ∧
      (∀ n, ⊥ < BMem bempty (indepFamily n) ∧ BMem bempty (indepFamily n) < ⊤) ∧
      (∀ n m, n ≠ m →
        BMem bempty (indepFamily n) ⊓ BMem bempty (indepFamily m) = ⊥) := by
  refine ⟨Set.infinite_range_of_injective independent_conditions_injective, ?_, ?_⟩
  · intro n
    rw [indepFamily_value]
    constructor
    · rw [bot_lt_iff_ne_bot]; intro h; simpa using (Set.ext_iff.1 h n)
    · rw [lt_top_iff_ne_top]; intro h
      have h2 : (n + 1) ∈ ({n} : Set ℕ) := by rw [h]; trivial
      rw [Set.mem_singleton_iff] at h2; omega
  · intro n m hnm
    simp only [indepFamily_value]
    ext k
    simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_singleton_iff, Set.bot_eq_empty,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl h; exact hnm h

/-! ## Axiom audit -/

#print axioms independent_conditions_injective
#print axioms independent_conditions_range_infinite

end BSet
end RGF2
end RGF
