import RGF.Physics.Dynamics.ToricCode
import RGF.Physics.Dynamics.ToricCodeGeneral

/-!
# `native_decide` reduction audit (computability / axiom-footprint slimming)

This module extends the acceptance-audit suite (cf. `Audit`, `AuditFull`,
`DedupAudit`) with the *computability / trust-footprint* task: replacing, wherever
the scale permits, machine-compiler evaluation (`native_decide`) by the kernel's
own decision procedure (`decide`) or by structured proofs.  Every `native_decide`
adds `Lean.ofReduceBool` and `Lean.trustCompiler` — i.e. the correctness of the
Lean compiler — to a theorem's trusted base; converting to `decide` (kernel
reduction) or an ordinary proof removes those two extra trust items, leaving only
the standard `propext, Classical.choice, Quot.sound`.

## What the `#print axioms` checks below certify

The toric-code development (Kitaev code as an RGF generative fixed point) was the
project's largest `native_decide` consumer, including a fixed-size `L = 3`
Gaussian-elimination computation of the stabilizer rank and four-fold ground
degeneracy.  That fixed example has been upgraded to a *general theorem*
(`RGF.ToricCodeGeneral`, proved by linear algebra over `GF(2)`: the vertex and
plaquette coboundary maps of the torus grid each have rank `L² − 1` because the
grid is connected, hence `k = 2` logical qubits and degeneracy `2² = 4` for every
`L ≥ 2`), and all remaining toric-code checks were converted to kernel `decide`.

As a result the entire toric-code chain now depends **only** on the standard
axioms — the `#print axioms` lines below print exactly
`[propext, Classical.choice, Quot.sound]`, with no `Lean.ofReduceBool` /
`Lean.trustCompiler`.
-/

/-! ## General (any-`L`) lattice-homology results — no compiler trust -/
#print axioms RGF.ToricCodeGeneral.numLogical_eq
#print axioms RGF.ToricCodeGeneral.groundDegeneracy_eq_four
#print axioms RGF.ToricCodeGeneral.finrank_range_deltaV
#print axioms RGF.ToricCodeGeneral.finrank_range_deltaP

/-! ## `L = 3` toric-code results, now derived from the general theorem -/
#print axioms RGF.ToricCode.numPhysical_eq
#print axioms RGF.ToricCode.numLogical_eq
#print axioms RGF.ToricCode.ground_degeneracy_eq_four

/-! ## The structural stabilizer-algebra checks (converted to kernel `decide`) -/
#print axioms RGF.ToricCode.Avert_commute
#print axioms RGF.ToricCode.Bplaq_commute
#print axioms RGF.ToricCode.Avert_Bplaq_commute
#print axioms RGF.ToricCode.stabilizers_involutive
#print axioms RGF.ToricCode.vertex_global_relation
#print axioms RGF.ToricCode.plaquette_global_relation
#print axioms RGF.ToricCode.logical_operators_commute_with_stabilizers
#print axioms RGF.ToricCode.logical_algebra_two_qubits
#print axioms RGF.ToricCode.stabilizer_supports_are_cycles

/-! ## Capstone — standard axioms only -/
#print axioms RGF.ToricCode.toric_code_is_generative_fixed_point

/-! ## Summary

See `native_decide_reduction_report.md` for the full inventory of the reduction across the
library (files fully cleared of `native_decide`, and the residual heavy
computations — large permutation-group / matrix decisions such as `PSL(2,7)`,
`A₅`, `S₄` — that remain on `native_decide` because kernel `decide` does not scale
to them). -/
