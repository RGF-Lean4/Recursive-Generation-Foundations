import Mathlib
import RGF.Generative.Uniqueness.AssumptionMinimality

/-!
# Uniqueness of the RGF initial assumptions — what can and cannot be proven

A natural and forceful objection to the RGF program runs as follows.  The locked
constants `(k, d) = (5, 3)` are derived rigorously, but the *derivation* rests on
a specific bundle of initial assumptions (a two-layer recursion depth, an
antisymmetric / real generator, the G1/G3 "exclusivity + one-step recovery"
rules, …).  The companion development already shows that these assumptions are

* **independent** (no one follows from the others), and
* **necessary / minimal** (`RGF.AssumptionMinimality`: dropping any single one
  admits a counter-model in which `(5, 3, 6)` fails),

but it does **not** argue that they are the *most natural* or the *uniquely
reasonable* choice of generative basis.  **Can uniqueness be proven?**

## The honest answer, in two halves

**(A) Absolute "naturalness" is not a theorem.**  "Most natural" is not a
mathematical predicate.  To prove that an assumption set is *the* natural one,
one would first have to fix a formal criterion of naturalness — and that
criterion is itself a chosen assumption, so the question only regresses.  No
Lean theorem (here or anywhere) can certify a foundational choice as
"absolutely most natural"; that is a philosophical judgement, not a provable
proposition.  We do **not** claim to prove it, and we do **not** state any
theorem asserting it.

**(B) *Conditional* uniqueness, however, is a theorem — and a strong one.**
Once the *selection criteria* are written down explicitly (the eight structural
requirements bundled in `RGFCoreAssumptions`, none of which mentions the answer
`(5, 3, 6)`), the configuration that satisfies them is **unique**, not merely the
*conclusion* it produces.  This file proves exactly that, at three levels of
granularity:

1. `rgf_configuration_unique` — the *entire* generative configuration
   `(k, n₂, L)` (mode order, layer/critical-mode count, **and the lattice
   itself**) is the unique solution of the eight criteria: there is one and only
   one, namely `(5, 2, simpleCubic)`.  This is strictly stronger than the
   previously available `rgf_invariants_unique`, which fixed only the invariant
   triple `(5, 3, 6)`.

2. The three free parameters are *each* pinned uniquely by its own criterion,
   and each pin is a *parsimony* (least / minimal) statement, which is the most
   defensible formal reading of "natural = no needless complexity":
   * `least_layer_count` — `n₂ = 2` is the **least** mode count that supports
     emergence (carries both a neutral G2 mode and a contracting G3 mode); one
     layer is too few, and the depth-2 law caps it at two.
   * `unique_odd_order` — `k = 5` is the **unique** odd mode order compatible
     with the two-mode count (`num2DIrreps k = 2`).
   * `unique_dimension` — `d = 3` is the **unique** positive dimension in which
     the rotation generators are representable as vectors (`rotGen d = d`).

3. `rgf_invariants_unique'` / `cubic_unique_in_class'` re-export the invariant-
   level and candidate-class uniqueness for convenience.

So: uniqueness *of the configuration given the stated generative criteria* is
fully machine-checked here.  Uniqueness *of the criteria themselves as the
absolutely most natural choice* is, by part (A), outside the scope of any proof.
-/

open RGF.LatticeUniquenessGap

namespace RGF.AssumptionUniqueness

open RGF.AssumptionMinimality

/-! ## Part 1 — Full configuration uniqueness

The previously available result `rgf_invariants_unique` shows that any model
satisfying the eight criteria has *invariants* `(k, dim, coord) = (5, 3, 6)`.
The theorem below is strictly stronger: it shows the *whole configuration*
`(k, n₂, L)` — including the layer/critical-mode count `n₂` and the lattice `L`
as a structured object — is the **unique** solution of the criteria. -/

/-- **Configuration uniqueness.**  There is one and only one generative
    configuration `(k, n₂, L)` satisfying the eight RGF selection criteria, namely
    `(5, 2, simpleCubic)`.  None of the eight criteria mentions the answer
    `(5, 3, 6)`; uniqueness is therefore a property of the *criteria*, not of the
    conclusion read back into them. -/
theorem rgf_configuration_unique :
    ∃! p : ℕ × ℕ × LatticeCandidate, RGFCoreAssumptions p.1 p.2.1 p.2.2 := by
  refine ⟨(5, 2, simpleCubic), ?_, ?_⟩
  · exact { coupling := le_refl 2, depth2 := le_refl 2, oddk := by decide,
            repCount := by decide, lock := by decide, rot := by decide,
            dimpos := by decide, central := rfl }
  · rintro ⟨k, n₂, L⟩ h
    have hn2 : n₂ = 2 := le_antisymm h.depth2 h.coupling
    obtain ⟨hk, hd, hc⟩ := core_assumptions_conclusion h
    have hL : L = simpleCubic := by
      obtain ⟨dim, coord, invSym⟩ := L
      have hs := h.central
      simp_all [simpleCubic]
    subst hn2; subst hk; subst hL; rfl

/-! ## Part 2 — Each free parameter is pinned uniquely (parsimony reading) -/

/-- **Least layer count.**  Among all mode counts that support emergence (carry a
    neutral G2 mode and a contracting G3 mode), `n₂ = 2` is the **least**.  This is
    the precise sense in which two layers are the parsimonious minimum: one layer
    is provably insufficient. -/
theorem least_layer_count : IsLeast {n₂ : ℕ | EmergenceSupported n₂} 2 :=
  ⟨two_modes_emergence, fun _ hn => two_layer_minimal hn⟩

/-- **Unique odd mode order.**  `k = 5` is the unique odd mode order whose dihedral
    two-dimensional irrep count equals the two-mode value `n₂ = 2`. -/
theorem unique_odd_order : ∃! k : ℕ, Odd k ∧ num2DIrreps k = 2 := by
  refine ⟨5, ⟨by decide, by decide⟩, ?_⟩
  rintro k ⟨hodd, hn2⟩
  exact odd_n2_eq_two_implies_five k hodd hn2

/-- **Unique dimension.**  `d = 3` is the unique positive spatial dimension in
    which the rotation generators are representable as vectors (`rotGen d = d`,
    i.e. `d(d−1)/2 = d`). -/
theorem unique_dimension : ∃! d : ℕ, 0 < d ∧ rotGen d = d := by
  refine ⟨3, ⟨by decide, by decide⟩, ?_⟩
  rintro d ⟨hd, hrot⟩
  exact (rotGen_eq_dim_iff hd).mp hrot

/-! ## Part 3 — Re-exported invariant-level and candidate-class uniqueness -/

/-- **Invariant uniqueness (re-export).**  Any model satisfying the eight criteria
    has invariants exactly `(k, dim, coord) = (5, 3, 6)`. -/
theorem rgf_invariants_unique' {k n₂ : ℕ} {L : LatticeCandidate}
    (h : RGFCoreAssumptions k n₂ L) : (k, L.dim, L.coord) = (5, 3, 6) :=
  rgf_invariants_unique h

/-- **Candidate-class uniqueness (re-export).**  Among the standard competing
    lattices, the simple-cubic lattice is the unique one passing both geometric
    criteria. -/
theorem cubic_unique_in_class' :
    ∀ L ∈ candidates,
      (forwardCount L = 5 ∧ rotGen L.dim = L.dim) ↔ L = simpleCubic :=
  cubic_unique_in_class

end RGF.AssumptionUniqueness
