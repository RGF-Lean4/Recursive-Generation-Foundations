import RGF.Generative.Locking.LockingMembrane
import RGF.Generative.Core.InvariantTheorems
import RGF.Generative.Uniqueness.ComplexNecessity
import RGF.Physics.Emergence.KPZEmergence
import RGF.Physics.Emergence.IntegratedDerivationChain
import RGF.Generative.Locking.DynamicsToLocking

/-!
# RGF Verification Audit

This file performs axiom audits on all four core theorems
specified in the RGF verification protocol.

To verify, open this file in a Lean 4 IDE or run:
  lake build Audit

All core theorems should only depend on standard axioms:
  propext, Classical.choice, Quot.sound,
  Lean.ofReduceBool, Lean.trustCompiler
-/

/-! ## Core Theorem 1: locking_membrane_unique_five
    Locking-membrane uniqueness theorem: k = 5 is the unique natural number satisfying the locking-membrane conditions (now L2 ∧ L3).

    **Dependency note (after the spectral reduction).** All the hypotheses of this
    theorem and of its upstream Propositions 2 and 3 (`single_irrep_insufficient`,
    `nonsolvability_necessity`) now amount to just
      · the *existence of some concrete critical spectrum*
        `CriticalSpectrum (num2DIrreps k)` (the `spectrum` field carried by the
        `RGFDynamicalAxioms` structure), together with
      · the basic RGF axioms (the structural assumptions of fixed point,
        criticality, dihedral symmetry, etc.).
    The two bespoke assumptions of earlier versions — the abstract G2 (emergent
    stability) and G3 (exponential recovery), together with the two exclusion axiom
    fields (`single_mode_exclusion`, `solvable_exclusion`) — have been reduced to
    spectral-gap conditions of the linearized operator (`HasNeutralMode` /
    `HasContractingMode`) and **proved as theorems** from the concrete critical
    spectrum. Consequently no bespoke assumption is listed here:
    `#print axioms` should output only the standard Lean axioms.

    **Two-condition update (L2 ∧ L3).** The predicate `LockingMembraneConditions` now
    carries only the two independent conditions
      · L2 (dual-mode coupling, `num2DIrreps k = 2`), and
      · L3 (oddness, `Odd k`).
    The former third condition L1 (non-solvability of Sₖ) is **no longer a hypothesis**
    of this theorem. L2 ∧ L3 already lock k = 5 uniquely (`odd_n2_eq_two_implies_five`),
    and S₅ is non-solvable, so L1 is recovered as the derived theorem
    `LockingMembraneConditions.L1` rather than being assumed. The uniqueness statement
    `∃! k, LockingMembraneConditions k` is unchanged in content (k = 5). -/
#print axioms locking_membrane_unique_five

/-! ## Core Theorem 2: equivariant_preserves_aut
    Theorem: equivariant systems preserve automorphisms. -/
#print axioms RGFState.equivariant_preserves_aut

/-! ## Core Theorem 3: locking_implies_complex_necessity
    Theorem: the locking conditions imply the necessity of complex numbers. -/
#print axioms RGF.L2L3.ComplexNecessity.complex_necessity_master

/-! ## Core Theorem 4: KPZ_from_RGF
    Derivation of the emergence of the KPZ equation from the RGF locking-membrane conditions.

    **Dependency note.** This theorem is now completely free of any dependence on the
    abstract G2/G3. Its only hypothesis is `locking_membrane_one_dim`, i.e. the
    one-dimensional locking-membrane condition (`LockingMembraneConditions 5`)
    together with the existence of an equivariant fixed point.

    **Two-condition update (L2 ∧ L3).** `LockingMembraneConditions` is now the
    streamlined two-field predicate carrying only the independent conditions
      · L2 (dual-mode coupling, `num2DIrreps 5 = 2`), and
      · L3 (oddness, `Odd 5`).
    L1 (non-solvability of S₅) is no longer one of the hypotheses fed into the KPZ
    chain: it is the derived fact `LockingMembraneConditions.L1` (since L2 ∧ L3 force
    k = 5 and S₅ is non-solvable). Accordingly `LockingMembraneConditions 5` is
    discharged purely by concrete arithmetic decisions on L2 and L3. These are
    exactly the concrete conditions realized by the spectral reduction (Core
    Theorem 1), so the KPZ emergence chain passes only through
    `locking_membrane_unique_five` and the spectral conditions behind it, and never
    touches any abstract dynamical axiom. The entire ExclusionProcess derivation
    chain (orbit pairing, circle-map reduction) contains no G2/G3,
    `RGFDynamicalAxioms`, or `sorry`. -/
#print axioms KPZ_from_RGF

/-! ## Core Theorem 5: rgf_dynamics_to_dimension_three
    Integrated derivation chain (capstone): from the dual-layer generative dynamics
    to the spatial dimension `d = 3`.  Assembles, in one master theorem, the
    version-D frequency upper bound (depth-2 recursion), the L3 odd-dimension chiral
    axis, the squeeze to `n₂ = 2`, the locking-membrane value `k = 5`, and the
    de-modelled lattice double-criterion (`forwardCount = 5` ∧ `rotGen dim = dim`)
    that forces `dim = 3`.  Every residual top-level assumption appears as an
    explicit hypothesis, so `#print axioms` shows only the standard Lean axioms. -/
#print axioms RGF.IntegratedChain.rgf_dynamics_to_dimension_three

/-! ## Core Theorem 6: rgf_dynamics_to_dimension_three_via_ortho
    Integrated derivation chain via the orthogonal generation-axis route (Layers
    9–11).  Instead of the intrinsic rotation-vector criterion, this master theorem
    closes `dim = 3` from the explicit orthogonal step rule (`OrthoStepRule`), a
    genuine orthonormal generation-axis family in `ℝ^d`: the coordination number
    `z = 2d` and forward count `2d − 1` are *derived* (`coordination_eq_two_mul`,
    `toCandidate_forward`), so the locking condition `forwardCount = 5` forces
    `d = 3` with the cubic lattice obtained as a conclusion, not an assumption.
    Every residual top-level assumption appears as an explicit hypothesis, so
    `#print axioms` shows only the standard Lean axioms. -/
#print axioms RGF.IntegratedChain.rgf_dynamics_to_dimension_three_via_ortho

/-! ## Core Theorem 7: dynamics_to_locking_master
    Dynamics-to-locking master theorem (L2/L3 deductive closure): the core engine
    *double-layer iteration ⇒ Banach contraction ⇒ fixed point* is written out as a
    full machine-checked proof (`dual_layer_fixed_point`), and the previously
    *assumed* two-layer structure `StableTwoLayer` is upgraded to a structure
    strictly *derived* from the contraction dynamics (`toStableTwoLayer`). Feeding
    the bridge into `stable_two_layer_locks_uniquely` yields, from a single dual-layer
    locking dynamics, the unique joint fixed point of the coupled iteration together
    with the locking conditions `n₂ = 2` (L2), `Odd k` (L3), `k = 5` (unique), and
    `D₅`-consistency. Non-vacuity is certified by the explicit instance `standard`.
    `#print axioms` shows only the standard Lean axioms. -/
#print axioms RGF.L2L3.DynamicsToLocking.dynamics_to_locking_master
#print axioms RGF.L2L3.DynamicsToLocking.dual_layer_fixed_point

/-! ## Verification Summary

All four core theorems compile without sorry and depend only on
standard Lean axioms (propext, Classical.choice, Quot.sound).

In particular, after the G2/G3 → spectral-gap reduction
(see the "Spectral Reduction" section of `README.md`), neither
`locking_membrane_unique_five` nor `KPZ_from_RGF` carries any
bespoke dynamical assumption: the only inputs are the existence of a
concrete `CriticalSpectrum` and the basic structural RGF axioms.

To reproduce:
1. Clone this repository
2. Run `lake build Audit`
3. Verify the #print axioms output shows only standard axioms
-/
