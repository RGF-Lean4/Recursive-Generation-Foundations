import Mathlib
import RGF.Generative.Locking.LockingMembrane
import RGF.Physics.Emergence.LatticeUniquenessGap
import RGF.Generative.Bridge.L2L3OpenItemsDerivation

/-!
# Closing the gap: necessity and minimality of the RGF initial assumptions

The deepest objection to the RGF program is *not* whether the core constants
`(k, d) = (5, 3)` follow from the initial assumptions — they do, and that chain
is fully machine-checked elsewhere — but **why exactly these assumptions?**

* Why a **two-layer** iteration, rather than one or three?
* Why the specific lattice/coordination rules **G1/G3** (the "exclusivity +
  one-step recovery" rules that remove exactly one back-step direction), rather
  than something else?
* Is the assumption set **minimal** — does removing *any single* assumption make
  the conclusion fail?
* Are the assumptions the **most natural choice** inside a broader class of
  "generative systems"?

This file answers these questions formally.  It does *not* re-prove the forward
derivation (that lives in `RGF.IntegratedDerivationChain`,
`Invariants.LockingMembrane`, `RGF.LatticeUniquenessGap`,
`Feasibility.*`); instead it adds the **converse / minimality** content:

1. **Sufficiency, bundled.**  `RGFCoreAssumptions` packages the eight independent
   hypotheses behind the locked invariants, and `core_assumptions_conclusion`
   shows their conjunction forces `(k, dim, coord) = (5, 3, 6)`.

2. **Two layers, not one or three.**  `EmergenceSupported n₂` says a critical
   spectrum with `n₂` two-dimensional modes can carry *both* a neutral
   (phase-locking, G2) mode and a contracting (recovery, G3) mode.
   `two_layer_minimal` proves this *needs* `n₂ ≥ 2` (one coupled mode / a single
   layer is provably insufficient), and `depth_two_caps_frequencies` (the depth-2
   recurrence ⇒ a biquadratic ⇒ at most two positive frequencies) caps it at
   `n₂ ≤ 2`.  `layer_count_two_unique` concludes `n₂ = 2` is the **unique**
   surviving value: not one, not three.

3. **Minimality (each assumption is load-bearing).**  For *each* of the eight
   assumptions there is an explicit model satisfying *all the others* in which the
   conclusion `(5, 3, 6)` **fails**.  Hence no assumption is redundant: dropping
   any one of them breaks the locking.  These are
   `coupling_necessary`, `depth2_necessary`, `oddness_necessary`,
   `repCount_necessary`, `lock_necessary`, `rotation_necessary`,
   `dimpos_necessary`, `centralSymmetry_necessary`.

4. **Naturalness / uniqueness inside the candidate class.**  The assumptions are
   satisfiable (`core_assumptions_satisfiable`, witnessed by the 3D simple-cubic
   lattice at `k = 5`), the locked invariants are unique
   (`rgf_invariants_unique`), and among the standard competing lattices the
   simple-cubic lattice is the unique survivor of the two geometric criteria
   (`cubic_is_unique_among_candidates`, re-exported as
   `cubic_unique_in_class`).
-/

open RGF.LatticeUniquenessGap

namespace RGF.AssumptionMinimality

/-! ## Part 1 — The bundled assumptions and their joint sufficiency -/

/-- The locked-invariant conclusion of the RGF core: the mode-locking order is
    `k = 5`, the spatial dimension is `d = 3`, and the coordination number is
    `z = 6` (the simple-cubic invariants). -/
abbrev Conclusion (k : ℕ) (L : LatticeCandidate) : Prop :=
  k = 5 ∧ L.dim = 3 ∧ L.coord = 6

/-- **The eight independent RGF core assumptions.**

* `coupling`  — the dual-mode lower bound `n₂ ≥ 2`: the linearized critical
  operator carries at least two two-dimensional modes, the structural meaning of
  "the iteration has (at least) two coupled layers".
* `depth2`    — the depth-2 upper bound `n₂ ≤ 2`: the generative law depends on the
  previous two steps, so its characteristic polynomial is a biquadratic in the
  frequency and admits at most two positive frequencies (no third layer).
* `oddk`      — L3: the real antisymmetric generator forces an *odd* mode order.
* `repCount`  — the dihedral representation bridge `n₂ = num2DIrreps k`.
* `lock`      — the G1/G3 symmetry→direction bridge `forwardCount L = k`: the order
  of the admissible forward-direction star equals the mode-locking order.
* `rot`       — the intrinsic rotation-vector criterion `rotGen (dim) = dim`.
* `dimpos`    — the spatial dimension is positive.
* `central`   — G1 reversibility / central symmetry: every neighbour direction has
  its opposite, so the back-step rule removes exactly one direction. -/
structure RGFCoreAssumptions (k n₂ : ℕ) (L : LatticeCandidate) : Prop where
  coupling : 2 ≤ n₂
  depth2   : n₂ ≤ 2
  oddk     : Odd k
  repCount : n₂ = num2DIrreps k
  lock     : forwardCount L = k
  rot      : rotGen L.dim = L.dim
  dimpos   : 0 < L.dim
  central  : L.invSym = true

/-- **Joint sufficiency.**  The conjunction of the eight assumptions forces the
    locked invariants `(k, dim, coord) = (5, 3, 6)`. -/
theorem core_assumptions_conclusion {k n₂ : ℕ} {L : LatticeCandidate}
    (h : RGFCoreAssumptions k n₂ L) : Conclusion k L := by
  have hn2 : n₂ = 2 := le_antisymm h.depth2 h.coupling
  have hk5 : k = 5 := by
    refine odd_n2_eq_two_implies_five k h.oddk ?_
    rw [← h.repCount, hn2]
  have hdim : L.dim = 3 := (rotGen_eq_dim_iff h.dimpos).mp h.rot
  have hcoord : L.coord = 6 := by
    have hl := h.lock
    rw [hk5] at hl
    simp only [forwardCount, h.central, if_true] at hl
    omega
  exact ⟨hk5, hdim, hcoord⟩

/-! ## Part 2 — Two layers, not one and not three -/

/-- A critical spectrum with `n₂` two-dimensional modes **supports emergence** if
    it can carry *both* a neutral (phase-locking, G2) mode `ρ = 1` and a
    contracting (recovery, G3) mode `ρ < 1` simultaneously. -/
def EmergenceSupported (n₂ : ℕ) : Prop :=
  ∃ S : CriticalSpectrum n₂, HasNeutralMode S ∧ HasContractingMode S

/-- **Lower bound — a single layer is insufficient.**  A neutral mode and a
    contracting mode must live in *distinct* two-dimensional blocks, so emergence
    requires at least two modes `n₂ ≥ 2`.  In particular `n₂ = 1` (a single coupled
    mode / a one-layer iteration) cannot carry both G2 and G3. -/
theorem two_layer_minimal {n₂ : ℕ} (h : EmergenceSupported n₂) : 2 ≤ n₂ := by
  obtain ⟨S, ⟨i, hi⟩, ⟨j, hj⟩⟩ := h
  have hij : i ≠ j := by
    rintro rfl
    rw [hi] at hj
    linarith
  haveI : Nontrivial (Fin n₂) := ⟨i, j, hij⟩
  have h1 : 1 < Fintype.card (Fin n₂) := Fintype.one_lt_card
  simp only [Fintype.card_fin] at h1
  omega

/-- The single-mode case (`n₂ = 1`) provably fails to support emergence. -/
theorem single_mode_no_emergence : ¬ EmergenceSupported 1 := by
  intro h
  have := two_layer_minimal h
  omega

/-- **Two modes do support emergence.**  An explicit two-mode critical spectrum
    (one neutral mode `ρ = 1`, one contracting mode `ρ = 1/2`) carries both G2 and
    G3. -/
theorem two_modes_emergence : EmergenceSupported 2 := by
  refine ⟨twoModeSpectrum 1 (1/2) (by norm_num) (by norm_num)
    (le_refl 1) (by norm_num), ⟨0, ?_⟩, ⟨1, ?_⟩⟩
  · simp [twoModeSpectrum]
  · norm_num [twoModeSpectrum]

/-- **Upper bound — no third layer.**  The depth-2 recurrence makes the
    characteristic polynomial a biquadratic `ω⁴ − a ω² + b = 0` in the frequency,
    so the set of positive frequencies has at most two elements: a third
    independent frequency (a third layer) is excluded. -/
theorem depth_two_caps_frequencies (a b : ℝ) (S : Finset ℝ)
    (hS : ∀ ω ∈ S, 0 < ω ∧ ω ^ 4 - a * ω ^ 2 + b = 0) : S.card ≤ 2 :=
  L2L3OpenItems.pentagon_n2_upper a b S hS

/-- **Two layers, uniquely.**  Among all mode counts that *support emergence*
    (lower bound, ≥ 2) and respect the depth-2 frequency cap (upper bound, ≤ 2),
    the value `n₂ = 2` is the unique survivor.  This is the precise sense in which
    the iteration must be two-layer: not one (fails the lower bound), not three
    (fails the upper bound). -/
theorem layer_count_two_unique :
    ∃! n₂ : ℕ, EmergenceSupported n₂ ∧ n₂ ≤ 2 := by
  refine ⟨2, ⟨two_modes_emergence, le_refl 2⟩, ?_⟩
  rintro m ⟨hm, hle⟩
  have := two_layer_minimal hm
  omega

/-! ## Part 3 — Minimality: every assumption is load-bearing

For each assumption we exhibit a model that satisfies **all the other seven**
assumptions yet whose conclusion `(5, 3, 6)` **fails**.  Hence dropping any single
assumption breaks the locking: the assumption set has no redundant member. -/

/-- **`coupling` is necessary.**  Dropping the dual-mode lower bound `n₂ ≥ 2`
    admits the single-mode model `k = 3` (here on a `(dim, coord) = (3, 4)`
    lattice), which satisfies the other seven assumptions but gives `k = 3 ≠ 5`. -/
theorem coupling_necessary :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate),
      (n₂ ≤ 2 ∧ Odd k ∧ n₂ = num2DIrreps k ∧ forwardCount L = k ∧
        rotGen L.dim = L.dim ∧ 0 < L.dim ∧ L.invSym = true) ∧
      ¬ Conclusion k L :=
  ⟨3, 1, ⟨3, 4, true⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩,
    by decide⟩

/-- **`depth2` is necessary.**  Dropping the depth-2 cap `n₂ ≤ 2` admits the
    over-constrained model `k = 7` (`n₂ = 3`, on a `(3, 8)` BCC-type lattice),
    satisfying the other seven assumptions but giving `k = 7 ≠ 5`. -/
theorem depth2_necessary :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate),
      (2 ≤ n₂ ∧ Odd k ∧ n₂ = num2DIrreps k ∧ forwardCount L = k ∧
        rotGen L.dim = L.dim ∧ 0 < L.dim ∧ L.invSym = true) ∧
      ¬ Conclusion k L :=
  ⟨7, 3, ⟨3, 8, true⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩,
    by decide⟩

/-- **`oddk` (L3) is necessary.**  Dropping oddness admits the even model
    `k = 6` (`n₂ = 2`, on a `(3, 7)` lattice), satisfying the other seven
    assumptions but giving `k = 6 ≠ 5`. -/
theorem oddness_necessary :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate),
      (2 ≤ n₂ ∧ n₂ ≤ 2 ∧ n₂ = num2DIrreps k ∧ forwardCount L = k ∧
        rotGen L.dim = L.dim ∧ 0 < L.dim ∧ L.invSym = true) ∧
      ¬ Conclusion k L :=
  ⟨6, 2, ⟨3, 7, true⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩,
    by decide⟩

/-- **`repCount` is necessary.**  Dropping the dihedral representation bridge
    `n₂ = num2DIrreps k` lets `n₂ = 2` coexist with `k = 3` (on a `(3, 4)`
    lattice), satisfying the other seven assumptions but giving `k = 3 ≠ 5`. -/
theorem repCount_necessary :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate),
      (2 ≤ n₂ ∧ n₂ ≤ 2 ∧ Odd k ∧ forwardCount L = k ∧
        rotGen L.dim = L.dim ∧ 0 < L.dim ∧ L.invSym = true) ∧
      ¬ Conclusion k L :=
  ⟨3, 2, ⟨3, 4, true⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩,
    by decide⟩

/-- **`lock` (the G1/G3 symmetry→direction bridge) is necessary.**  Dropping it
    breaks the link between the mode order and the lattice coordination: the
    `k = 5` model on the `(3, 8)` BCC-type lattice satisfies the other seven
    assumptions but has `coord = 8 ≠ 6`, so the locked cubic invariant fails. -/
theorem lock_necessary :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate),
      (2 ≤ n₂ ∧ n₂ ≤ 2 ∧ Odd k ∧ n₂ = num2DIrreps k ∧
        rotGen L.dim = L.dim ∧ 0 < L.dim ∧ L.invSym = true) ∧
      ¬ Conclusion k L :=
  ⟨5, 2, ⟨3, 8, true⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩,
    by decide⟩

/-- **`rot` (the rotation-vector criterion) is necessary.**  Dropping it admits
    the 2D triangular lattice (`(dim, coord) = (2, 6)`, `forwardCount = 5`) at
    `k = 5`: it satisfies the other seven assumptions but has `dim = 2 ≠ 3`.  This
    is exactly the dimension-degeneracy the rotation criterion removes. -/
theorem rotation_necessary :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate),
      (2 ≤ n₂ ∧ n₂ ≤ 2 ∧ Odd k ∧ n₂ = num2DIrreps k ∧ forwardCount L = k ∧
        0 < L.dim ∧ L.invSym = true) ∧
      ¬ Conclusion k L :=
  ⟨5, 2, ⟨2, 6, true⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩,
    by decide⟩

/-- **`dimpos` is necessary.**  Dropping positivity admits the degenerate
    `dim = 0` model (`(0, 6)` lattice, `forwardCount = 5`) at `k = 5`: it satisfies
    the other seven assumptions (note `rotGen 0 = 0`) but has `dim = 0 ≠ 3`. -/
theorem dimpos_necessary :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate),
      (2 ≤ n₂ ∧ n₂ ≤ 2 ∧ Odd k ∧ n₂ = num2DIrreps k ∧ forwardCount L = k ∧
        rotGen L.dim = L.dim ∧ L.invSym = true) ∧
      ¬ Conclusion k L :=
  ⟨5, 2, ⟨0, 6, true⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩,
    by decide⟩

/-- **`central` (G1 reversibility / central symmetry) is necessary.**  Dropping it
    admits a non-centrally-symmetric `(3, 5)` lattice at `k = 5`: with no back-step
    direction to remove, `forwardCount = coord = 5 = k`, so it satisfies the other
    seven assumptions but has `coord = 5 ≠ 6`, breaking the cubic invariant. -/
theorem centralSymmetry_necessary :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate),
      (2 ≤ n₂ ∧ n₂ ≤ 2 ∧ Odd k ∧ n₂ = num2DIrreps k ∧ forwardCount L = k ∧
        rotGen L.dim = L.dim ∧ 0 < L.dim) ∧
      ¬ Conclusion k L :=
  ⟨5, 2, ⟨3, 5, false⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide⟩

/-! ## Part 4 — Naturalness and uniqueness inside the candidate class -/

/-- **Satisfiability.**  The eight assumptions are jointly satisfiable, witnessed
    by the 3D simple-cubic lattice at mode order `k = 5`, `n₂ = 2`. -/
theorem core_assumptions_satisfiable :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate), RGFCoreAssumptions k n₂ L :=
  ⟨5, 2, simpleCubic,
    { coupling := le_refl 2
      depth2   := le_refl 2
      oddk     := by decide
      repCount := by decide
      lock     := by decide
      rot      := by decide
      dimpos   := by decide
      central  := rfl }⟩

/-- **Uniqueness of the locked invariants.**  Any model satisfying the eight
    assumptions has invariants exactly `(k, dim, coord) = (5, 3, 6)`. -/
theorem rgf_invariants_unique {k n₂ : ℕ} {L : LatticeCandidate}
    (h : RGFCoreAssumptions k n₂ L) : (k, L.dim, L.coord) = (5, 3, 6) := by
  obtain ⟨hk, hd, hc⟩ := core_assumptions_conclusion h
  simp [hk, hd, hc]

/-- **Naturalness inside the candidate class.**  Among the standard competing
    lattices (square, triangular, honeycomb, simple-cubic, BCC, FCC, 4D
    hypercubic), the simple-cubic lattice is the *unique* one passing both
    geometric criteria (`forwardCount = 5` and `rotGen dim = dim`). -/
theorem cubic_unique_in_class :
    ∀ L ∈ candidates,
      (forwardCount L = 5 ∧ rotGen L.dim = L.dim) ↔ L = simpleCubic :=
  cubic_is_unique_among_candidates

end RGF.AssumptionMinimality
