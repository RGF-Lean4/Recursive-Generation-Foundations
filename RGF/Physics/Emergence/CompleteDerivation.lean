/-
  RequestProject/CompleteDerivation.lean

  Absorbs the complete layer-by-layer derivation of the RGF framework (Layer 0 -> Layer 7).

  Starting from the single first principle, the "self-consistent fixed point",
      SelfConsistent(d) := rotGen(d) = d,  rotGen(d) := d(d-1)/2
      ∃! d, SelfConsistent(d) ∧ d ≠ 0,
  it successively locks the complete tuple `(L, k, d, coord) = (2, 5, 3, 6)`, and
  demotes Axiom G, Axiom M, the oddness condition L3, and the count of
  two-dimensional irreducible representations L2 to theorems. The bilayer duality of
  Layer 5 (fixed-point duality, layerwise recurrence bijection, recurrence rigidity)
  directly reuses the unconditional results already proved in
  `RequestProject.BilayerDuality`.

  This file contains no `sorry` and depends only on the standard axioms.
-/
import Mathlib
import RGF.Physics.Dynamics.BilayerDuality
import RGF.Physics.Emergence.FirstPrinciples

namespace RGF.CompleteDerivation

/-! ## Layer 0: Primitive setup

The bilayer system `generate : R → E`, `modify : E → R` and its two dynamical
self-maps `step = modify ∘ generate`, `costep = generate ∘ modify`, together with all
their duality theorems, are established unconditionally in
`RequestProject.BilayerDuality`. Here we only re-export them under named abbreviations. -/

/-- Rule-layer dynamics `step = modify ∘ generate` (reuses `RGF.Bilayer.step`). -/
abbrev step {R E : Type*} (generate : R → E) (modify : E → R) : R → R :=
  RGF.Bilayer.step generate modify

/-- Entity-layer mirror dynamics `costep = generate ∘ modify` (reuses `RGF.Bilayer.costep`). -/
abbrev costep {R E : Type*} (generate : R → E) (modify : E → R) : E → E :=
  RGF.Bilayer.costep generate modify

/-! ## Layer 0.2 / Layer 1: Self-consistent fixed point and the dimension lock d = 3 -/

/-- `rotGen(d) := d(d-1)/2`: the dimension of the `SO(d)` Lie algebra (rotation generators). -/
def rotGen (d : ℕ) : ℕ := d * (d - 1) / 2

/-- Self-consistency predicate: the dimension of the rotation generators equals the
dimension of the space itself. -/
def SelfConsistent (d : ℕ) : Prop := rotGen d = d

/-- Theorem 1.1 (uniqueness of the self-consistent fixed point):
`SelfConsistent d ∧ d ≠ 0 ⟹ d = 3`. -/
theorem dimension_lock {d : ℕ} (h : SelfConsistent d) (h0 : d ≠ 0) : d = 3 := by
  unfold SelfConsistent at h
  rcases d with ( _ | _ | _ | _ | d ) <;> simp_all +arith +decide [rotGen]
  nlinarith [Nat.div_add_mod ((d + 4) * (d + 3)) 2, Nat.mod_lt ((d + 4) * (d + 3)) two_pos]

/-- First principle (the unique axiom, here a theorem): there exists a unique nonzero
self-consistent dimension. -/
theorem selfConsistent_unique : ∃! d : ℕ, SelfConsistent d ∧ d ≠ 0 := by
  refine ⟨3, ⟨by rfl, by decide⟩, ?_⟩
  exact fun y hy => dimension_lock hy.1 hy.2

/-! ## Layer 2: Recursion depth and order lock -/

/-- Number of forward generation directions: in the `d`-dimensional cubic lattice each
point has `2d` nearest neighbours; forbidding the unique backward direction yields `2d - 1`. -/
def forwardCount (d : ℕ) : ℕ := 2 * d - 1

/-- Theorem 2.1 (the forward direction count is odd): for all `d ≥ 1`, `forwardCount d`
is always odd. -/
theorem forwardCount_odd {d : ℕ} (hd : 1 ≤ d) : Odd (forwardCount d) :=
  ⟨d - 1, by simp only [forwardCount]; omega⟩

/-- Theorem 2.2 (order lock): `SelfConsistent d ∧ d ≠ 0 ⟹ forwardCount d = 5`. -/
theorem order_lock {d : ℕ} (h : SelfConsistent d) (h0 : d ≠ 0) : forwardCount d = 5 := by
  rw [dimension_lock h h0]; rfl

/-- Number of two-dimensional irreducible representations of an odd `k` (dihedral group
`D_k`): `n₂(k) = (k-1)/2`. -/
def num2DIrreps (k : ℕ) : ℕ := (k - 1) / 2

/-- Theorem 2.3 (depth lock): the recursion depth `L = n₂(forwardCount d) = 2`. -/
theorem depth_lock {d : ℕ} (h : SelfConsistent d) (h0 : d ≠ 0) :
    num2DIrreps (forwardCount d) = 2 := by
  rw [order_lock h h0]; decide

/-! ## Layer 3: Coordination number and the complete locked tuple -/

/-- Coordination number (number of nearest neighbours) of the simple cubic lattice,
`coord d := 2d`. -/
def coord (d : ℕ) : ℕ := 2 * d

/-- Theorem 3.1 (coordination number): `SelfConsistent d ∧ d ≠ 0 ⟹ coord d = 6`. -/
theorem coord_lock {d : ℕ} (h : SelfConsistent d) (h0 : d ≠ 0) : coord d = 6 := by
  rw [coord, dimension_lock h h0]

/-- Main theorem (the first principle locks everything): the complete tuple
    `(L, k, d, coord) = (2, 5, 3, 6)` appears entirely as the conclusion. -/
theorem master_lock {d : ℕ} (h : SelfConsistent d) (h0 : d ≠ 0) :
    (num2DIrreps (forwardCount d), forwardCount d, d, coord d) = (2, 5, 3, 6) := by
  obtain rfl := dimension_lock h h0
  decide

/-! ## Layer 4: Demotion of Axiom M and Axiom G

Axiom G (the geometric cross product `CP(d) := d(d-1)/2 = d`) is precisely the definition
of `SelfConsistent` itself, and has been absorbed. Axiom M (minimal genuine emergence) is
demoted to a theorem using the characterization of `MinimalEmergent` in
`RGF.FirstPrinciples`. -/

/-- Axiom G is the definition of self-consistency (it agrees with `RGF.FirstPrinciples.CP`
once the ℕ division is removed). -/
theorem axiomG_is_selfConsistent {d : ℕ} (h0 : d ≠ 0) :
    SelfConsistent d ↔ RGF.FirstPrinciples.CP d := by
  unfold SelfConsistent FirstPrinciples.CP rotGen
  constructor <;> intro h <;>
    rcases d with ( _ | _ | _ | _ | _ | d ) <;>
      simp_all +arith +decide [Nat.mul_succ]
  grind

/-- Theorem 4.2 (self-consistency implies Axiom M): from `SelfConsistent`, the order `5`
is the minimal emergent order. -/
theorem axiomM_from_selfConsistent {d : ℕ} (h : SelfConsistent d) (h0 : d ≠ 0) :
    RGF.FirstPrinciples.MinimalEmergent (forwardCount d) := by
  rw [order_lock h h0]
  exact RGF.FirstPrinciples.minimalEmergent_iff_five.mpr rfl

/-! ## Layer 5: Bilayer duality (reuses `RequestProject.BilayerDuality`) -/

/-- Theorem 5.1 (semiconjugacy / intertwining law): `generate ∘ stepⁿ = costepⁿ ∘ generate`. -/
theorem intertwine {R E : Type*} (generate : R → E) (modify : E → R) (n : ℕ) :
    generate ∘ (step generate modify)^[n] = (costep generate modify)^[n] ∘ generate :=
  RGF.Bilayer.generate_intertwine generate modify n

/-- Theorem 5.2 (fixed-point duality, unconditional): `Fix(step) ≃ Fix(costep)`. -/
def fixedEquiv {R E : Type*} (generate : R → E) (modify : E → R) :
    {r : R // step generate modify r = r} ≃ {e : E // costep generate modify e = e} :=
  RGF.Bilayer.fixedEquiv generate modify

/-- Theorem 5.5 (layerwise recurrence bijection, unconditional): for every `n ≥ 1`,
`Perₙ(step) ≃ Perₙ(costep)`. -/
def perEquiv {R E : Type*} (generate : R → E) (modify : E → R) (n : ℕ) (hn : 1 ≤ n) :
    {r : R // (step generate modify)^[n] r = r} ≃
    {e : E // (costep generate modify)^[n] e = e} :=
  RGF.Bilayer.perEquiv generate modify n hn

/-- Theorem 5.6 (recurrence rigidity, unconditional): the conjugacy bijection on the set
of all periodic points. -/
noncomputable def periodicPtsEquiv {R E : Type*} (generate : R → E) (modify : E → R) :
    {r : R // r ∈ Function.periodicPts (step generate modify)} ≃
    {e : E // e ∈ Function.periodicPts (costep generate modify)} :=
  RGF.Bilayer.periodicPtsEquiv generate modify

/-! ## Layer 6: Locking conditions as theorems -/

/-- Theorem 6.1 (the locking order is odd, unconditional):
`SelfConsistent d ∧ d ≠ 0 ⟹ Odd (forwardCount d)`. -/
theorem locking_order_odd {d : ℕ} (h : SelfConsistent d) (h0 : d ≠ 0) :
    Odd (forwardCount d) := by
  rw [order_lock h h0]; decide

/-- Theorem 6.2 (count of two-dimensional irreducible representations, unconditional):
    `SelfConsistent d ∧ d ≠ 0 ⟹ num2DIrreps (forwardCount d) = 2`. -/
theorem locking_num2DIrreps {d : ℕ} (h : SelfConsistent d) (h0 : d ≠ 0) :
    num2DIrreps (forwardCount d) = 2 :=
  depth_lock h h0

/-! ## Layer 7: The honest boundary

The bare generation paradigm is underdetermined: "recursive generation" alone cannot lock
a unique value (it ranges over all odd numbers). The statement below faithfully records that
`EmergentOrder` is itself not unique (both `5` and `7` emerge); uniqueness can only be
provided by the minimality principle. -/

/-- Honest boundary: the bare emergence predicate is not unique -- both `5` and `7` emerge
and are distinct. -/
theorem honest_boundary :
    RGF.FirstPrinciples.EmergentOrder 5 ∧ RGF.FirstPrinciples.EmergentOrder 7 ∧ (5 : ℕ) ≠ 7 :=
  RGF.FirstPrinciples.meta_resolution

end RGF.CompleteDerivation
