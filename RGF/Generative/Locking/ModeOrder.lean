/-
# RCDxRGF.ModeOrder — bridging the RCD mode order `k = 5` to RGF's twin criteria

Part of the optional bridge library `RCDxRGF` (sees both RGF and RCD; leaves the
standalone `RCD` library untouched).

RCD papers 3 and 5 select the symmetry / mode order `5` largely by narrative
("candidate-order screening, exclusion of `p ≥ 7`"), formalising only arithmetic
cores such as `nontrivial_chars_paired`.  RGF upgrades this to **two logically
independent characterisations** of `5`, which are moreover **unified with the
dimension lock `d = 3`**:

* the **group-theoretic** Abel–Ruffini threshold `MinimalEmergent 5`
  (`RGF.FirstPrinciples.minimalEmergent_iff_five`);
* the **crystallographic** criterion (`5` is the smallest prime rotation order
  incompatible with any lattice)
  (`RGF.CritiqueResolution.five_two_independent_characterizations`);
* the **unification** of `(k, d) = (5, 3)` as the unique pair satisfying minimal
  emergence and the cross-product condition
  (`RGF.CritiqueResolution.abelRuffini_crossProduct_unified`).
-/

import Mathlib
import RGF.Physics.Emergence.FirstPrinciples
import RGF.Phenomenology.TestSuite.CritiqueResolution

namespace RCDxRGF.ModeOrder

open RGF.FirstPrinciples

/-- Every nontrivial `Z₅` character is unequal to its conjugate: `k ≠ -k` for
    `k ∈ {1,2,3,4}` (5 is odd, so `2k ≢ 0 mod 5`). -/
theorem nontrivial_chars_paired (k : ZMod 5) (hk : k ≠ 0) : k ≠ -k := by
  decide +revert

/-- **Group-theoretic criterion.**  The RCD mode order is the unique minimal
    emergent order, i.e. `MinimalEmergent k ↔ k = 5` — the Abel–Ruffini threshold
    (`S₅` is the smallest non-solvable symmetric group). -/
theorem rcd_mode_order_iff_minimalEmergent (k : ℕ) :
    MinimalEmergent k ↔ k = 5 :=
  minimalEmergent_iff_five

/-- **Twin independent characterisations.**  The mode order `5` is singled out
    simultaneously by the group-theoretic minimal-emergence criterion *and* by the
    crystallographic criterion (`5` is the smallest prime rotation order with
    `totient > 2`, while every smaller prime order has `totient ≤ 2`). -/
theorem rcd_mode_order_two_criteria :
    MinimalEmergent 5 ∧
      (Nat.Prime 5 ∧ 2 < Nat.totient 5 ∧
        ∀ p : ℕ, Nat.Prime p → p < 5 → Nat.totient p ≤ 2) :=
  RGF.CritiqueResolution.five_two_independent_characterizations

/-- **Unification of `k = 5` and `d = 3` (the upgrade).**  The classically
    unrelated facts behind RCD's mode order (`5`) and spatial dimension (`3`) are
    two faces of a single locking principle: `(5, 3)` is the **unique** pair `(k, d)`
    satisfying minimal emergence `MinimalEmergent k` together with the
    cross-product condition `CP d`.  This is exactly the "same-origin" conclusion
    that RCD's paper-3 → paper-5 → standard-model spine aims at. -/
theorem rcd_mode_dim_unified :
    ∃! p : ℕ × ℕ, MinimalEmergent p.1 ∧ CP p.2 :=
  RGF.CritiqueResolution.abelRuffini_crossProduct_unified

/-- **Consistency of the RCD `Z₅` character-pairing core with the order lock.**
    RCD's arithmetic core `nontrivial_chars_paired` (every nontrivial `Z₅`
    character is unequal to its conjugate) holds together with the RGF
    minimal-emergence identification of the order as `5`. -/
theorem rcd_z5_pairing_with_order (k : ZMod 5) (hk : k ≠ 0) :
    k ≠ -k ∧ MinimalEmergent 5 :=
  ⟨nontrivial_chars_paired k hk, minimalEmergent_iff_five.mpr rfl⟩

end RCDxRGF.ModeOrder
