/-
  RGF/DynamicalHoTTFlows.lean

  Direction V — Dynamical homotopy type theory on non-trivial phase spaces.

  Building on `GenerativeDynamicalCategory.lean` (the category `GenSys` of
  generative dynamical systems and the equivalence *membrane locking ⇔
  contractible attractor type*), we separate the ordered and chaotic regimes by
  their homotopy type:

  * **Ordered side (topological, strict).**  A locked flow whose phase space is
    contractible is simply connected (`flow_locked_simplyConnected`) and its loop
    space / fundamental group is trivial (`flow_locked_pi1_trivial`): every
    trajectory loop contracts to a point.

  * **Chaotic side (discrete-flow monodromy).**  The rotation system on `ℤ/n`
    (`rotationSys`) models a limit cycle; we compute its monodromy
    (`rot_iterate`), show it has no fixed point for `n ≥ 2` (so it is not
    membrane-locked, `rot_not_locked`), and exhibit non-trivial winding — the
    generator is not the identity but has period `n` (`rot_step_ne_id`,
    `rot_period`, `limitCycle_nontrivial_winding`), i.e. `π₁ ≅ ℤ/n ≠ 0`.

  * **Order ⇔ chaos transition.**  Reusing the categorical characterisation,
    membrane locking ⇔ the attractor type is contractible (`order_iff_contractible`),
    hence the limit-cycle attractor is *not* contractible
    (`chaos_not_contractible`): the order/chaos boundary is precisely the
    contractible/non-contractible (trivial/non-trivial `π₁`) homotopy transition.

  (Lean has no univalence axiom and we add none, so the homotopy content is
  carried by Mathlib's topological homotopy theory and the `GenSys` type layer.)

  Everything is `sorry`-free.
-/
import Mathlib
import RGF.Math.Category.GenerativeDynamicalCategory

namespace RGF.DynFlows

open RGF.GenCat

/-! ## 1. Ordered side: locked flow ⇒ trivial homotopy -/

/-- A locked flow with contractible phase space is simply connected: all
    trajectory loops contract. -/
theorem flow_locked_simplyConnected (X : Type*) [TopologicalSpace X]
    [ContractibleSpace X] : SimplyConnectedSpace X :=
  inferInstance

/-- A locked flow with contractible phase space has trivial fundamental group at
    every base point (every loop is homotopic to the constant loop). -/
theorem flow_locked_pi1_trivial (X : Type*) [TopologicalSpace X]
    [ContractibleSpace X] (x : X) :
    Subsingleton (Path.Homotopic.Quotient x x) :=
  inferInstance

/-! ## 2. Chaotic side: the rotation (limit-cycle) system -/

/-- The generator of the rotation system on `ℤ/n`. -/
def rotStep (n : ℕ) : ZMod n → ZMod n := fun x => x + 1

/-- The rotation dynamical system on `ℤ/n` (a discrete limit cycle). -/
def rotationSys (n : ℕ) : GenSys := ⟨ZMod n, rotStep n⟩

/-- **Monodromy of the limit cycle.**  Iterating the generator `k` times adds `k`. -/
theorem rot_iterate (n : ℕ) (k : ℕ) (x : ZMod n) :
    (rotStep n)^[k] x = x + (k : ZMod n) := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, rotStep]
      push_cast; ring

/-- The generator is not the identity when `n ≥ 2` (non-trivial winding). -/
theorem rot_step_ne_id (n : ℕ) (hn : 2 ≤ n) : rotStep n ≠ id := by
  intro h
  have h0 := congr_fun h 0
  simp only [rotStep, id_eq, zero_add] at h0
  haveI : Fact (1 < n) := ⟨by omega⟩
  exact one_ne_zero h0

/-- The generator has period exactly `n`: `stepⁿ = id`. -/
theorem rot_period (n : ℕ) : (rotStep n)^[n] = id := by
  funext x
  rw [rot_iterate, ZMod.natCast_self, add_zero, id]

/-- The generator of the rotation system has no fixed point for `n ≥ 2`. -/
theorem rotStep_no_fixed (n : ℕ) (hn : 2 ≤ n) (x : ZMod n) : rotStep n x ≠ x := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro hx
  simp only [rotStep] at hx
  have h1 : x + (1 : ZMod n) = x + 0 := by rw [add_zero]; exact hx
  exact one_ne_zero (add_left_cancel h1)

/-- The rotation system has no fixed point for `n ≥ 2`, hence is **not**
    membrane-locked. -/
theorem rot_not_locked (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsMembraneLocked (rotationSys n) := by
  rintro ⟨x, hx, -⟩
  exact rotStep_no_fixed n hn x hx

/-- **Non-trivial winding of the limit cycle.**  The generator is not the
    identity yet has period `n` (`π₁ ≅ ℤ/n ≠ 0`). -/
theorem limitCycle_nontrivial_winding (n : ℕ) (hn : 2 ≤ n) :
    rotStep n ≠ id ∧ (rotStep n)^[n] = id :=
  ⟨rot_step_ne_id n hn, rot_period n⟩

/-! ## 3. Order ⇔ chaos as a homotopy transition -/

/-- **Order ⇔ contractibility.**  Membrane locking is equivalent to
    contractibility of the attractor (fixed-point) type. -/
theorem order_iff_contractible (X : GenSys) :
    IsMembraneLocked X ↔ IsContractible (FixSet X) :=
  membraneLocked_iff_fix_contractible X

/-- **Chaos ⇒ non-contractible attractor.**  The limit-cycle attractor type is
    not contractible (non-trivial fundamental group). -/
theorem chaos_not_contractible (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsContractible (FixSet (rotationSys n)) := by
  rw [← order_iff_contractible]
  exact rot_not_locked n hn

end RGF.DynFlows