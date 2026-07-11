/-
  RGF2/Boolean/ForcingRelation.lean   (module `RGF2.Boolean.ForcingRelation`)
  — layer 1: the forcing relation `⊩` on the RGF 2.0 Boolean-valued model.

  **RGF 2.0 — Path 3, feasibility demonstration for the "forcing relation" task.**

  The follow-up plan for RGF asks (direction 2.1) to *define the forcing relation
  `⊩` directly on `BSet B`, taking `p ⊩ φ` to mean `p ≤ ‖φ‖`, and to prove the
  basic properties of forcing (double negation, the forcing definition of
  implication, etc.)*.  This file carries out exactly that step, on top of the
  Boolean-valued universe `V^B = BSet B` and its forcing backbone
  (`RGF2/Boolean/Model.lean`, `RGF2/Boolean/Forcing.lean`).

  Here a *Boolean truth value* of a statement is an element `φ : B` (the value
  `‖φ‖` living in the complete Boolean algebra `B`); e.g. the truth value of a
  membership statement is `BMem x y`, of an equality statement `BEq x y`.  A
  *forcing condition* is likewise an element `p : B`, and

      `p ⊩ φ   :=   p ≤ φ`.

  The results below are the standard forcing calculus:

    * `forces_top`, `forces_mono_cond`, `forces_mono_value` — `⊤` is forced,
      forcing is antitone in the condition and monotone in the value;
    * `forces_inf_iff`      — `p ⊩ φ ⊓ ψ ↔ (p ⊩ φ) ∧ (p ⊩ ψ)` (conjunction);
    * `forces_sup_left/right` — disjunction is forced by either disjunct;
    * `forces_mp`           — modus ponens: `p ⊩ φ → p ⊩ (φ ⇨ ψ) → p ⊩ ψ`;
    * `forces_himp_iff`     — the **forcing definition of implication**:
      `p ⊩ (φ ⇨ ψ) ↔ (p ⊓ φ) ⊩ ψ`;
    * `forces_dne`          — **double negation**: `p ⊩ φᶜᶜ ↔ p ⊩ φ`;
    * `top_forces_iff`      — `⊤ ⊩ φ ↔ φ = ⊤` (a statement is forced by the trivial
      condition exactly when its Boolean value is `⊤`);
    * `forces_consistent`   — a nonzero condition never forces both `φ` and `φᶜ`;
    * `forces_pairing`, `forces_pairing_self` — the forcing calculus applied to the
      Boolean-valued pairing operation of `RGF2/Boolean/Forcing.lean`;
    * `forcing_independence` — restated in forcing language: over a non-degenerate
      `B` there is a membership statement forced neither positively nor negatively
      by `⊤`, the algebraic core of every forcing independence result.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Boolean.Model
import RGF.Math.SetTheory.RGF2.Boolean.Forcing

universe u

namespace RGF
namespace RGF2
namespace BSet

variable {B : Type u} [CompleteBooleanAlgebra B]

/-- **The forcing relation.**  A forcing condition `p : B` forces a Boolean truth
value `φ : B` when `p ≤ φ`.  Following the standard Boolean-valued semantics, the
truth value `‖φ‖` of a set-theoretic statement lives in `B` (e.g. `BMem x y`,
`BEq x y`), and `Forces p φ` reads "`p ⊩ φ`". -/
def Forces (p φ : B) : Prop := p ≤ φ

@[inherit_doc] scoped notation:50 p " ⊩ᴮ " φ => Forces p φ

theorem forces_iff {p φ : B} : (p ⊩ᴮ φ) ↔ p ≤ φ := Iff.rfl

/-- The trivial value `⊤` is forced by every condition. -/
theorem forces_top (p : B) : p ⊩ᴮ (⊤ : B) := le_top

/-- Forcing is antitone in the condition: a smaller (stronger) condition still
forces whatever a larger one does. -/
theorem forces_mono_cond {p q φ : B} (hqp : q ≤ p) (h : p ⊩ᴮ φ) : q ⊩ᴮ φ :=
  le_trans hqp h

/-- Forcing is monotone in the value. -/
theorem forces_mono_value {p φ ψ : B} (hφψ : φ ≤ ψ) (h : p ⊩ᴮ φ) : p ⊩ᴮ ψ :=
  le_trans h hφψ

/-- **Conjunction.**  `p ⊩ φ ⊓ ψ` iff `p ⊩ φ` and `p ⊩ ψ`. -/
theorem forces_inf_iff {p φ ψ : B} : (p ⊩ᴮ (φ ⊓ ψ)) ↔ (p ⊩ᴮ φ) ∧ (p ⊩ᴮ ψ) :=
  le_inf_iff

/-- **Disjunction (left).**  Forcing a disjunct forces the disjunction. -/
theorem forces_sup_left {p φ ψ : B} (h : p ⊩ᴮ φ) : p ⊩ᴮ (φ ⊔ ψ) :=
  le_trans h le_sup_left

/-- **Disjunction (right).** -/
theorem forces_sup_right {p φ ψ : B} (h : p ⊩ᴮ ψ) : p ⊩ᴮ (φ ⊔ ψ) :=
  le_trans h le_sup_right

/-- **Modus ponens for forcing.** -/
theorem forces_mp {p φ ψ : B} (hφ : p ⊩ᴮ φ) (himp : p ⊩ᴮ (φ ⇨ ψ)) : p ⊩ᴮ ψ :=
  le_trans (le_inf hφ himp) inf_himp_le

/-- **The forcing definition of implication.**  `p ⊩ (φ ⇨ ψ)` exactly when the
condition `p ⊓ φ` forces `ψ` — i.e. every extension of `p` forcing `φ` forces `ψ`. -/
theorem forces_himp_iff {p φ ψ : B} : (p ⊩ᴮ (φ ⇨ ψ)) ↔ ((p ⊓ φ) ⊩ᴮ ψ) :=
  le_himp_iff

/-- **Double negation.**  `p ⊩ φᶜᶜ ↔ p ⊩ φ`.  In a Boolean algebra the value
domain is classical, so double negation elimination holds at the level of forcing. -/
theorem forces_dne {p φ : B} : (p ⊩ᴮ (φᶜᶜ)) ↔ (p ⊩ᴮ φ) := by
  rw [compl_compl]

/-- **Weak forcing / the trivial condition.**  `⊤` forces `φ` iff the Boolean value
of `φ` is `⊤` — the two-valued notion of "valid in `V^B`". -/
theorem top_forces_iff {φ : B} : ((⊤ : B) ⊩ᴮ φ) ↔ φ = ⊤ :=
  top_le_iff

/-- **Consistency of forcing.**  A nonzero condition never forces both a statement
and its negation. -/
theorem forces_consistent {p φ : B} (hp : p ≠ ⊥) : ¬ ((p ⊩ᴮ φ) ∧ (p ⊩ᴮ φᶜ)) := by
  rintro ⟨h1, h2⟩
  have hle : p ≤ φ ⊓ φᶜ := le_inf h1 h2
  rw [inf_compl_eq_bot] at hle
  exact hp (le_bot_iff.mp hle)

/-! ## The forcing calculus on the Boolean-valued pairing -/

/-- Forcing membership in the Boolean-valued pair `{x, y}ᴮ` is forcing the
equality disjunction, using `BMem_bpair`. -/
theorem forces_pairing (p : B) (z x y : BSet B) :
    (Forces p (BMem z (bpair x y))) ↔ (Forces p (BEq z x ⊔ BEq z y)) := by
  rw [Forces, Forces, BMem_bpair]

/-- `⊤` forces that `x` is a member of the Boolean-valued pair `{x, y}ᴮ`. -/
theorem forces_pairing_self (x y : BSet B) :
    (⊤ : B) ⊩ᴮ (BMem x (bpair x y)) := by
  rw [top_forces_iff, BMem_bpair, BEq_refl, top_sup_eq]

end BSet

/-- **Independence, in forcing language.**  Over the non-degenerate complete Boolean
algebra `Set (Fin 2)` there is a membership statement `⟦x ∈ᴮ y⟧` that the trivial
condition `⊤` forces neither positively (`⊤ ⊮ φ`) nor negatively (`⊤ ⊮ φᶜ`).  This
is the forcing-relation restatement of `BSet.bmem_undecided`, and the algebraic core
on which every forcing independence result (CH, AC, …) rests: changing the Boolean
algebra `B` can push the truth value of `φ` to `⊤` or to `⊥`. -/
theorem BSet.forcing_independence :
    ∃ (x y : BSet (Set (Fin 2))),
      ¬ (BSet.Forces (⊤ : Set (Fin 2)) (BSet.BMem x y)) ∧
      ¬ (BSet.Forces (⊤ : Set (Fin 2)) (BSet.BMem x y)ᶜ) := by
  obtain ⟨x, y, h1, h2⟩ := BSet.bmem_undecided
  refine ⟨x, y, ?_, ?_⟩
  · rw [BSet.Forces, top_le_iff]
    intro htop
    rw [htop] at h2
    simp at h2
  · rw [BSet.Forces, top_le_iff]
    intro htop
    have : BSet.BMem x y = ⊥ := by
      have := congrArg compl htop
      simpa using this
    rw [this] at h1
    exact (lt_irrefl _ h1)

end RGF2
end RGF
