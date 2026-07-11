/-
# RGF.FirstPrinciples — First-Principle Derivation

This file answers the deepest foundational criticism of the RGF programme — the
*ad-hoc-ness of the low-level postulates* ("the absence of first principles"):

> Why must this particular set of generative rules (double-layer iteration, the
> L2/L3 locking-membrane conditions, the G1/G3 lattice-coordination rules) be
> adopted?  Earlier work only showed the eight assumptions are the *minimal
> sufficient* condition for `(k, d, z) = (5, 3, 6)`; it never derived them from a
> single most-primitive philosophical postulate.

The resolution implemented here re-derives the whole locked tuple
`(L, k, d, z) = (2, 5, 3, 6)` from **two first principles only**, in which *no
target numeral is ever assumed*:

* **Axiom M (Minimal Emergent Order).**  `EmergentOrder k` means "the order-`k`
  recursive generation process exhibits irreducible emergence", made precise as
  "the symmetric group `S_k` is *not solvable*".  We single out the *minimal* such
  `k`.  (This is an extremal/least-action style principle, on the same
  epistemological footing as the axiom of infinity choosing the *least* inductive
  set, or the principle of least action in physics.)

* **Axiom G (Cross Product Only in Three Dimensions).**  `CP d` means the rotation
  generators of `SO(d)` are in bijection with space vectors, i.e.
  `dim 𝔰𝔬(d) = d(d-1)/2 = d` (equivalently: a nontrivial antisymmetric bilinear
  cross product satisfying Jacobi exists in `ℝ^d`).

From these two principles **every** parameter is obtained as a *theorem*:

* `k = 5`   (`minimalEmergent_iff_five`)         — minimal non-solvable order;
* `d = 3`   (`cp_iff_three`)                      — the cross-product dimension;
* `z = 6`   coordination `= 2 d`                  — simple-cubic nearest neighbours;
* `L = 2`   recursion depth `= (k-1)/2`           — number of 2D rotation planes.

The master theorem is `first_principle_forces_k_five_d_three`.

A `meta_resolution` theorem records the *honest* meta-statement: the *bare*
emergence predicate does **not** pin down a unique value (e.g. both `5` and `7`
are emergent); only the *minimality* extremal principle fixes `5`.  The foundation
can be contracted to this extremal principle, but not made to vanish entirely.
-/

import Mathlib
import RGF.Generative.Core.SixVerifications

open Equiv

namespace RGF.FirstPrinciples

/-! ## 1. First principles (stated as definitions) -/

/-- **`EmergentOrder k`** — "the order-`k` recursive generation process exhibits
    irreducible emergence", made precise as: the symmetric group `S_k` is *not*
    solvable.  (No target numeral occurs in this definition.) -/
def EmergentOrder (k : ℕ) : Prop := ¬ IsSolvable (Equiv.Perm (Fin k))

/-- **`MinimalEmergent k`** (Axiom M, Minimal Emergent Order) — `k` is emergent and
    every strictly smaller order is *not* emergent.  This is the extremal
    ("least") principle; it contains no numeral. -/
def MinimalEmergent (k : ℕ) : Prop :=
  EmergentOrder k ∧ ∀ m, m < k → ¬ EmergentOrder m

/-- **`CP d`** (Axiom G, Cross Product Only in Three Dimensions) — the rotation
    generators of `SO(d)` are in bijection with space vectors, i.e. the Lie
    algebra dimension `d(d-1)/2` equals the vector dimension `d` (and the space is
    nontrivial, `d ≠ 0`).  Written over `ℕ` as `d*(d-1) = 2*d ∧ d ≠ 0`; again no
    target numeral `3` is assumed. -/
def CP (d : ℕ) : Prop := d * (d - 1) = 2 * d ∧ d ≠ 0

/-! ## 2. Deriving the order k = 5 -/

/-- Theorem 1 (solvability bound, lower half): for `k ≤ 4`, `S_k` is
    solvable.  Together with `S_5` unsolvable this is the group-theoretic root of
    Abel–Ruffini. -/
theorem solvable_of_le_four {k : ℕ} (hk : k ≤ 4) :
    IsSolvable (Equiv.Perm (Fin k)) := by
  interval_cases k
  · infer_instance
  · infer_instance
  · exact S2_solvable
  · exact S3_solvable
  · exact S4_solvable

/-- `EmergentOrder k ↔ 5 ≤ k`: emergence (non-solvability of `S_k`) holds exactly
    from order `5` onwards. -/
theorem emergentOrder_iff_five_le {k : ℕ} : EmergentOrder k ↔ 5 ≤ k := by
  unfold EmergentOrder
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    exact h (solvable_of_le_four (by omega))
  · intro h
    exact Equiv.Perm.not_solvable _ (by simp [Cardinal.mk_fintype]; omega)

/-- Theorem 2 (the minimal genuine emergent order is 5): the unique minimal emergent order is `5`. -/
theorem minimalEmergent_iff_five {k : ℕ} : MinimalEmergent k ↔ k = 5 := by
  unfold MinimalEmergent
  constructor
  · rintro ⟨h1, h2⟩
    rw [emergentOrder_iff_five_le] at h1
    by_contra hne
    have hlt : 5 < k := lt_of_le_of_ne h1 (by omega)
    exact h2 5 hlt (emergentOrder_iff_five_le.mpr (by omega))
  · rintro rfl
    refine ⟨emergentOrder_iff_five_le.mpr (by omega), ?_⟩
    intro m hm
    rw [emergentOrder_iff_five_le]
    omega

/-- Axiom M as a *theorem*: there exists a unique minimal emergent order. -/
theorem axiom_M : ∃! k, MinimalEmergent k := by
  refine ⟨5, minimalEmergent_iff_five.mpr rfl, ?_⟩
  intro y hy
  exact minimalEmergent_iff_five.mp hy

/-! ## 3. Deriving the spatial dimension d = 3 -/

/-- Theorem 5 (the spatial dimension is locked to 3): the cross-product / "rotation = vector" equation
    `d(d-1)/2 = d` has the unique nontrivial solution `d = 3`. -/
theorem cp_iff_three {d : ℕ} : CP d ↔ d = 3 := by
  unfold CP
  constructor
  · rintro ⟨h, hne⟩
    have hd : 0 < d := Nat.pos_of_ne_zero hne
    have h2 : d * (d - 1) = d * 2 := by rw [h]; ring
    have h3 : d - 1 = 2 := Nat.eq_of_mul_eq_mul_left hd h2
    omega
  · rintro rfl; constructor <;> omega

/-! ## 4. All parameters uniquely locked -/

/-- **Core theorem (`first_principle_forces_k_five_d_three`).**  From the two first
    principles — `MinimalEmergent k` (Axiom M) and `CP d` (Axiom G) — the entire
    locked tuple is forced:

    * mode order `k = 5`,
    * spatial dimension `d = 3`,
    * coordination number `z = 2 d = 6` (simple-cubic nearest neighbours),
    * recursion depth `L = (k-1)/2 = 2` (number of 2D rotation planes).

    No target numeral is assumed anywhere: each appears only as a *conclusion*. -/
theorem first_principle_forces_k_five_d_three
    {k d : ℕ} (hk : MinimalEmergent k) (hd : CP d) :
    k = 5 ∧ d = 3 ∧ 2 * d = 6 ∧ (k - 1) / 2 = 2 := by
  have hk5 := minimalEmergent_iff_five.mp hk
  have hd3 := cp_iff_three.mp hd
  subst hk5; subst hd3
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 5. Honest meta-resolution -/

/-- **Honest meta-resolution (`meta_resolution`).**  The bare emergence predicate does *not*
    single out a unique value: e.g. both `5` and `7` are emergent (`S_5` and `S_7`
    are unsolvable) and `5 ≠ 7`.  Uniqueness of `5` arises *only* via the
    minimality extremal principle (Axiom M / `minimalEmergent_iff_five`).  Thus the
    foundation contracts to an extremal principle but cannot disappear entirely —
    this is stated transparently rather than hidden. -/
theorem meta_resolution :
    EmergentOrder 5 ∧ EmergentOrder 7 ∧ (5 : ℕ) ≠ 7 :=
  ⟨emergentOrder_iff_five_le.mpr (by omega),
   emergentOrder_iff_five_le.mpr (by omega), by omega⟩

end RGF.FirstPrinciples
