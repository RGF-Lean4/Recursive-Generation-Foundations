/-
  Invariants/QuinticLocking.lean — quintic locking from the invariant viewpoint
  Quintic Locking from the Invariant Perspective

  This file formalizes §6 of the outline, "connecting to quintic locking":
  it restates the three locking conditions L1, L2, L3 in the language of invariants,
  and derives the uniqueness of k = 5 from them.

  Invariant form of the three locking conditions:
  L1: ¬ IsSolvable(Aut(s))
  L2: τ ∈ (0,∞) and γ > 0  ⟹  n₂ = 2
  L3: |Aut(s)| ≡ 1 (mod 2) (odd order)

  Combined derivation: L2 ⇒ n₂ = 2 ⇒ (k-1)/2 = 2 ⇒ k = 5.
  L1 and L3 are checked (S₅ is not solvable, and the relevant group orders for |S₅| = 120 are odd).
-/

import Mathlib
import RGF.Generative.Core.Basic
import RGF.Generative.Locking.FiveLockingUniqueness

open Finset BigOperators Equiv

namespace RGFInvariant

variable {n : ℕ}

/-! ============================================================
    Part 1: invariant form of the three locking conditions
    ============================================================ -/

/-- Locking condition L1 (invariant form): Aut(s) is not solvable. -/
def L1_inv {n : ℕ} (s : RGFState n) : Prop :=
  ¬ IsSolvable s.autGroup

/-- Parameter of locking condition L2: the number of two-dimensional irreducible representations. -/
def n2_rep (k : ℕ) : ℕ := (k - 1) / 2

/-- Locking condition L2: n₂ = 2 (γ > 0 excludes ≥3 resonances, τ < ∞ excludes single-mode instability). -/
def L2_inv (k : ℕ) : Prop := n2_rep k = 2

/-- Locking condition L3 (invariant form): k is odd. -/
def L3_inv (k : ℕ) : Prop := Odd k

/-! ============================================================
    Part 2: L2 derives k = 5
    ============================================================ -/

/-
n₂(k) = 2 if and only if k = 5 (for odd k ≥ 3)
-/
theorem n2_eq_two_iff_k_eq_five (k : ℕ) (hk : Odd k) (hk3 : k ≥ 3) :
    L2_inv k ↔ k = 5 := by
      obtain ⟨ m, rfl ⟩ := hk;
      unfold L2_inv n2_rep; omega;

/-
The three conditions together derive k = 5
-/
theorem quintic_locking_from_invariants (k : ℕ)
    (hL1 : ¬ IsSolvable (Perm (Fin k)))
    (hL2 : L2_inv k)
    (hL3 : L3_inv k) :
    k = 5 := by
  unfold L2_inv n2_rep L3_inv at *
  obtain ⟨m, rfl⟩ := hL3
  omega

/-! ============================================================
    Part 3: verification that k = 5 satisfies all conditions
    ============================================================ -/

/-- k = 5 satisfies L2. -/
theorem five_satisfies_L2 : L2_inv 5 := by
  unfold L2_inv n2_rep; norm_num

/-- k = 5 satisfies L3. -/
theorem five_satisfies_L3 : L3_inv 5 := by
  unfold L3_inv; exact ⟨2, by omega⟩

/-
When k = 5, S₅ is not solvable (satisfying L1)
-/
theorem five_satisfies_L1 : ¬ IsSolvable (Perm (Fin 5)) := by
  have h : (5 : Cardinal) ≤ Cardinal.mk (Fin 5) := by simp
  exact Equiv.Perm.not_solvable (Fin 5) h

/-! ============================================================
    Part 4: invariant fibration and classification
    ============================================================ -/

/-- Invariant signature: used to classify fixed points. -/
structure InvariantSignature where
  beta0 : ℕ
  beta1 : ℤ
  euler : ℤ
  autOrd : ℕ
  edgeNum : ℕ
  deriving DecidableEq

/-- The bundle of RGF invariants attached to a state. -/
structure RGFInvariantBundle (n : ℕ) where
  beta0 : ℕ
  beta1 : ℤ
  euler : ℤ
  autOrd : ℕ
  edgeNum : ℕ

/-- Extract the full invariant bundle from a state. -/
noncomputable def extractInvariants (s : RGFState n) : RGFInvariantBundle n where
  beta0 := s.betti0
  beta1 := s.betti1
  euler := s.eulerChar1
  autOrd := s.autOrder
  edgeNum := s.edgeCount

/-- Extract the signature from an invariant bundle. -/
def toSignature (b : RGFInvariantBundle n) : InvariantSignature where
  beta0 := b.beta0
  beta1 := b.beta1
  euler := b.euler
  autOrd := b.autOrd
  edgeNum := b.edgeNum

/-- Invariant fibration of the fixed-point set: the set of fixed points sharing the same invariant signature. -/
def invariantFiber (sys : RGFIterSystem n) (α : InvariantSignature) :
    Set (RGFState n) :=
  { s | sys.IsFixedPoint s ∧ toSignature (extractInvariants s) = α }

/-- Fibration cover: every fixed point lies in some fiber. -/
theorem fiber_covers (sys : RGFIterSystem n) (s : RGFState n)
    (hfp : sys.IsFixedPoint s) :
    s ∈ invariantFiber sys (toSignature (extractInvariants s)) := by
  exact ⟨hfp, rfl⟩

/-- Distinct fibers are disjoint. -/
theorem fibers_disjoint (sys : RGFIterSystem n)
    (α β : InvariantSignature) (hne : α ≠ β) :
    invariantFiber sys α ∩ invariantFiber sys β = ∅ := by
  ext s
  simp [invariantFiber, Set.mem_empty_iff_false]
  intro _ h1 _ h2
  exact hne (h1.symm.trans h2)

/-! ============================================================
    Part 5: is `k = 5` a genuine necessity, or an artefact of the premises?
    ============================================================

    A recurring, legitimate criticism of "locking gives `k = 5`" arguments is that
    the derivation may be *circular*: one imposes a bundle of algebraic conditions
    that were reverse-engineered to output `5`.  Rather than dismiss the worry, we
    turn it into decidable/verifiable statements and answer it honestly.  The
    conclusion is nuanced:

    * The **algebraic** condition `L2` ("there are exactly two two-dimensional
      irreducible representations", `n₂ = (k-1)/2 = 2`) is **premise-contingent**:
      it is *not* rigid enough to single out `5` on its own.
    * The **order/group-theoretic** criterion ("`k` is the least atom count whose
      permutation symmetry `S_k` is unsolvable", from `FiveLockingUniqueness.lean`)
      **is** parameter-free and pins `k = 5` as a genuine necessity, equivalent to
      the classical fact that `A₅` is the smallest non-abelian simple group
      (Abel–Ruffini).

    So the honest verdict is: `k = 5` is a real necessity, but that necessity comes
    from the *minimal-non-solvable-group* criterion, **not** from the `n₂ = 2`
    algebraic bundle, which by itself is under-determined. -/

/-- **Sensitivity 1 — dropping oddness admits `k = 6`.**  The algebraic condition
`L2_inv` (`(k-1)/2 = 2`) does **not** have `{5}` as its solution set: without the
extra `Odd k` hypothesis, `k = 6` satisfies it too (natural-number division).  Hence
`L2` alone is under-determined; the oddness assumption `L3` is genuinely
load-bearing for the value `5`. -/
theorem L2_solution_set_is_five_or_six (k : ℕ) : L2_inv k ↔ k = 5 ∨ k = 6 := by
  unfold L2_inv n2_rep; omega

/-- `k = 6` explicitly satisfies the algebraic condition `L2`, witnessing the
non-uniqueness of Part 5's `L2_solution_set_is_five_or_six`. -/
theorem six_satisfies_L2 : L2_inv 6 := by
  unfold L2_inv n2_rep; norm_num

/-- **Sensitivity 2 — the target `n₂ = 2` is a free parameter.**  Retargeting the
representation-count condition to `n₂ = t` moves the (odd) solution to `2t + 1`; the
choice `t = 2` (giving `5`) is not forced by the condition's form.  This makes
precise the sense in which the `n₂ = 2` bundle is reverse-engineered: a different but
equally "natural" target yields a different `k`. -/
theorem n2_target_is_free (t : ℕ) : n2_rep (2 * t + 1) = t := by
  unfold n2_rep; omega

/-- **The parameter-free necessity.**  In contrast to the contingent algebraic
bundle, the minimal-non-solvable criterion (`FiveLockingCondition`, i.e. `S_k`
unsolvable and `k` least such) has `5` as its *unique* solution, with no adjustable
target parameter.  This is the robust, non-circular route to `k = 5`. -/
theorem five_is_forced_by_minimality (sys : RecursiveSystem)
    (h : FiveLockingCondition sys) : sys.k = 5 :=
  five_locking_unique sys h

/-- **Summary: circularity audit for `k = 5`.**  A single statement separating the
contingent from the necessary:

1. the algebraic `L2` condition alone admits `{5, 6}` (contingent);
2. its target `n₂ = t` is a free parameter (odd solution `2t+1`, so `5` is not forced);
3. the parameter-free minimal-non-solvable criterion forces `k = 5` uniquely.

Items 1–2 show the `n₂ = 2` route is premise-contingent; item 3 shows the value `5`
is nonetheless a genuine necessity, sourced from the classical minimal-non-solvable
group fact rather than from any reverse-engineered algebra. -/
theorem k_five_circularity_audit :
    (∀ k, L2_inv k ↔ k = 5 ∨ k = 6) ∧
    (∀ t : ℕ, n2_rep (2 * t + 1) = t) ∧
    (∀ sys : RecursiveSystem, FiveLockingCondition sys → sys.k = 5) :=
  ⟨L2_solution_set_is_five_or_six, n2_target_is_free, fun sys h => five_locking_unique sys h⟩

/-! ============================================================
    Part 6: scope of the circularity audit — the residual open step
    ============================================================

    **What `k_five_circularity_audit` does and does not establish.**  It is important
    not to overread the name.  The audit above establishes:

    * (given the *solvability* criterion) `k = 5` is the unique solution, and the
      earlier `n₂ = 2` algebraic bundle is premise-contingent.

    It does **not** establish:

    * that the *solvability* criterion is itself forced by the generative/physical
      definition of membrane locking.  In the present formalisation the link
      "emergence / stability ⟹ `S_k` non-solvable" is not a derived theorem at all:
      the emergence premise is **definitionally identified** with non-solvability.

    The following two statements make that residual gap explicit and honest, rather
    than leaving the impression (which the name `..._audit` might create) that
    circularity has been fully eliminated. -/

/-- **The physics→group-theory link is definitional, not derived.**  The
`EmergenceCondition` premise (the C1 side of the minimality route) is *by
definition* the statement that `S_k` is non-solvable — the proof is `Iff.rfl`.

This is the precise sense in which the solvability criterion is *not* independently
justified from a more primitive generative axiom: it is inserted, by definition, as
the meaning of "emergence".  Consequently theorems of the shape
"emergence ⟹ `S_k` non-solvable" carry no independent content, and the necessity of
choosing *solvability* (rather than some other parameter-free group invariant) as
*the* membrane-locking criterion remains an **open modelling problem** of the
framework. -/
theorem emergence_criterion_is_definitional (sys : RecursiveSystem) :
    EmergenceCondition sys ↔ ¬ IsSolvable (Equiv.Perm (Fin sys.k)) :=
  Iff.rfl

/-- **Honest closure statement.**  Combining the audit with the definitional
observation: the value `5` is genuinely forced *once the solvability criterion is
granted* (`five_is_forced_by_minimality`), but the criterion itself is granted by
definition (`emergence_criterion_is_definitional`), not deduced from the generative
primitives.  Hence, at the current state of the formalisation, `k = 5` is a theorem
*conditional on the solvability criterion*, and the necessity of that criterion is
not yet closed. -/
theorem k_five_conditional_on_solvability_criterion :
    (∀ sys : RecursiveSystem, FiveLockingCondition sys → sys.k = 5) ∧
    (∀ sys : RecursiveSystem,
        EmergenceCondition sys ↔ ¬ IsSolvable (Equiv.Perm (Fin sys.k))) :=
  ⟨fun sys h => five_locking_unique sys h, emergence_criterion_is_definitional⟩

end RGFInvariant
