/-
  RGF2/Boolean/IndependenceFamily.lean   (module `RGF2.Boolean.IndependenceFamily`)
  — layer 1: the combinatorial backbone of forcing ¬CH.

  **RGF 2.0 — Path 3, direction 2.2: partial progress toward
  `Con(ZFC) → Con(ZFC + ¬CH)`.**

  The full relative-consistency metatheorem `Con(ZFC) → Con(ZFC + ¬CH)` is a large
  research development (Flypitch scale): it requires a first-order deep embedding of
  ZFC together with its `Con` predicate, the Cohen complete Boolean algebra with its
  countable chain condition (to preserve cardinals), the computation `‖CH‖ ≠ ⊤`, and
  the soundness bridge from the Boolean-valued model back to relative consistency.
  That full target is **not** attempted here and is documented as remaining research
  engineering.

  What *is* clean and provable — and is the genuine **combinatorial heart** of
  forcing `¬CH` (adding many mutually independent Cohen reals) — is that the forcing
  universe over a rich enough algebra carries an **infinite antichain of mutually
  independent, undecided membership conditions**.  Over the complete Boolean algebra
  `B = Set ℕ`, this file exhibits:

    * `infinite_independent_conditions` — an infinite family of names `y : ℕ → V^B`
      whose membership truth values `‖bempty ∈ y n‖`
        (i) are each *strictly* between `⊥` and `⊤` (genuinely undecided), and
        (ii) are *pairwise disjoint* (an infinite antichain of nonzero conditions);
    * `infinite_independent_forcing` — the same, phrased in the forcing relation
      language: `⊤` forces neither `‖bempty ∈ y n‖` nor its negation, for every `n`,
      and the conditions are pairwise incompatible.

  An infinite antichain of independent nonzero conditions is exactly what lets a
  forcing notion add unboundedly many independent "generic" bits — the mechanism by
  which `2^ℵ₀` is pushed above `ℵ₁`, i.e. by which `CH` fails.  This isolates and
  verifies that mechanism inside the RGF 2.0 Boolean-valued model.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Boolean.Model
import RGF.Math.SetTheory.RGF2.Boolean.Forcing
import RGF.Math.SetTheory.RGF2.Boolean.ForcingRelation

namespace RGF
namespace RGF2
namespace BSet

/-- **Infinite antichain of independent forcing conditions.**  Over the complete
Boolean algebra `B = Set ℕ`, the names `y n := bsingleton {n}` have membership truth
values `‖bempty ∈ y n‖ = {n}`, which are each strictly between `⊥` and `⊤` (undecided)
and pairwise disjoint (an infinite antichain of nonzero conditions).  This is the
combinatorial backbone of adding infinitely many independent Cohen reals — the
mechanism forcing `¬CH`. -/
theorem infinite_independent_conditions :
    ∃ y : ℕ → BSet (Set ℕ),
      (∀ n, ⊥ < BMem bempty (y n) ∧ BMem bempty (y n) < ⊤) ∧
      (∀ n m, n ≠ m → BMem bempty (y n) ⊓ BMem bempty (y m) = ⊥) := by
  refine ⟨fun n => bsingleton {n}, fun n => ?_, fun n m hnm => ?_⟩
  · rw [BMem_bsingleton]
    constructor
    · rw [bot_lt_iff_ne_bot]; intro h; simpa using (Set.ext_iff.1 h n)
    · rw [lt_top_iff_ne_top]; intro h
      have h2 : (n + 1) ∈ ({n} : Set ℕ) := by rw [h]; trivial
      rw [Set.mem_singleton_iff] at h2; omega
  · rw [BMem_bsingleton, BMem_bsingleton]
    ext k
    simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_singleton_iff, Set.bot_eq_empty,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl h; exact hnm h

/-- **The independence family, in forcing language.**  Over `B = Set ℕ` there is an
infinite family of membership sentences that the trivial condition `⊤` forces neither
positively nor negatively, and whose forcing conditions are pairwise incompatible
(their meet is `⊥`).  This is the forcing-relation restatement of
`infinite_independent_conditions`: an infinite supply of independent generic bits. -/
theorem infinite_independent_forcing :
    ∃ y : ℕ → BSet (Set ℕ),
      (∀ n, ¬ Forces (⊤ : Set ℕ) (BMem bempty (y n)) ∧
            ¬ Forces (⊤ : Set ℕ) (BMem bempty (y n))ᶜ) ∧
      (∀ n m, n ≠ m → BMem bempty (y n) ⊓ BMem bempty (y m) = ⊥) := by
  obtain ⟨y, hy, hdisj⟩ := infinite_independent_conditions
  refine ⟨y, fun n => ⟨?_, ?_⟩, hdisj⟩
  · intro hf
    have htop : BMem bempty (y n) = ⊤ := top_le_iff.1 hf
    have := (hy n).2; rw [htop] at this; exact lt_irrefl _ this
  · intro hf
    have htop : (BMem bempty (y n))ᶜ = ⊤ := top_le_iff.1 hf
    have hbot : BMem bempty (y n) = ⊥ := by
      have := congrArg compl htop; simpa using this
    have := (hy n).1; rw [hbot] at this; exact lt_irrefl _ this

end BSet
end RGF2
end RGF
