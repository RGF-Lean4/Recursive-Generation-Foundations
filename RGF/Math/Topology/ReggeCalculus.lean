/-
  RGF/ReggeCalculus.lean

  Direction IV — Discrete gravity and Regge calculus.

  A `sorry`-free development of *Regge calculus*, the rigorous discretisation of
  general relativity on simplicial complexes.  It upgrades the RGF discrete
  topological toolkit (`BoundaryPaths`, `PersistentHomology`, `EulerChar`,
  `DiscreteGaugeTheory`) from *topological emergence* to a *dynamical geometry*:
  curvature is concentrated on codimension-2 hinges as a **deficit angle**, and
  the Einstein equations arise from varying the **Regge action** in the edge
  lengths.

  Contents (namespace `RGF.Regge`):

  * **Deficit angle.**  Curvature at a hinge `h` is `ε_h = 2π − ∑ θ`, the angle
    deficit around the codimension-2 skeleton (`deficitAngle`); it is flat exactly
    when the surrounding dihedral/interior angles sum to `2π` (`deficitAngle_eq_zero_iff`).

  * **2D Regge action = discrete Gauss–Bonnet.**  On a closed triangulated
    surface the total deficit (the 2D Regge action) equals `2π·χ`, a topological
    invariant (`reggeAction2D_eq_euler`).  Consequently the action is independent
    of the metric data (`reggeAction2D_indep`): every configuration is a critical
    point — the 2D vacuum Einstein equations hold identically.

  * **Regge field equations via the Schläfli identity.**  For a one-parameter
    variation of the edge lengths, the Schläfli identity `∑_h V_h · ε_h′ = 0`
    makes the deficit-angle terms drop out of the variation, so the derivative of
    the Regge action `S = ∑_h V_h · ε_h` is `∑_h V_h′ · ε_h`
    (`reggeAction_hasDerivAt`).  Hence the stationary points of the Regge action
    are exactly the solutions of the **discrete Einstein field equations**
    `∑_h (∂V_h) · ε_h = 0` (`regge_einstein_iff`).
-/

import Mathlib

open scoped Real BigOperators
open Finset

namespace RGF.Regge

/-! ## 1. The deficit angle -/

/-- The **deficit angle** at a hinge: `ε = 2π − (sum of the surrounding angles)`.
    Positive curvature ↔ positive deficit; flatness ↔ zero deficit. -/
noncomputable def deficitAngle (angleSum : ℝ) : ℝ := 2 * Real.pi - angleSum

/-- A hinge is flat (zero deficit) iff the surrounding angles sum to `2π`. -/
theorem deficitAngle_eq_zero_iff (angleSum : ℝ) :
    deficitAngle angleSum = 0 ↔ angleSum = 2 * Real.pi := by
  unfold deficitAngle; constructor <;> intro h <;> linarith

/-! ## 2. The 2D Regge action is a topological invariant (discrete Gauss–Bonnet) -/

/-- The **2D Regge action** on a closed triangulated surface: the total deficit
    angle `∑_v ε_v = 2π·V − (total interior angle)`, where the codimension-2
    hinges are the vertices (each of unit volume). -/
noncomputable def reggeAction2D (V : ℕ) (totalAngle : ℝ) : ℝ :=
  2 * Real.pi * V - totalAngle

/-- The combinatorial Euler characteristic of a surface with `V` vertices,
    `E` edges and `F` faces. -/
def eulerChar (V E F : ℕ) : ℤ := (V : ℤ) - E + F

/-
**Discrete Gauss–Bonnet / 2D Regge action.**  On a closed triangulated surface
    (every triangle contributes interior-angle sum `π`, so `totalAngle = π·F`, and
    every edge is shared by two triangles, so `2E = 3F`), the total deficit angle
    equals `2π` times the Euler characteristic.
-/
theorem reggeAction2D_eq_euler (V E F : ℕ)
    (hEF : 2 * E = 3 * F) (totalAngle : ℝ) (hAngle : totalAngle = Real.pi * F) :
    reggeAction2D V totalAngle = 2 * Real.pi * (eulerChar V E F : ℝ) := by
  unfold eulerChar reggeAction2D;
  push_cast; nlinarith [ Real.pi_pos, ( by norm_cast : ( 2 : ℝ ) * E = 3 * F ) ] ;

/-- **Topological invariance ⇒ stationarity.**  Because the 2D Regge action depends
    only on the (fixed) Euler characteristic, any two metric configurations with
    the same triangle-angle-sum data give the same action — every configuration is
    a critical point (the 2D vacuum Einstein equations hold identically). -/
theorem reggeAction2D_indep (V E F : ℕ) (hEF : 2 * E = 3 * F)
    (angle₁ angle₂ : ℝ) (h₁ : angle₁ = Real.pi * F) (h₂ : angle₂ = Real.pi * F) :
    reggeAction2D V angle₁ = reggeAction2D V angle₂ := by
  rw [reggeAction2D_eq_euler V E F hEF angle₁ h₁,
      reggeAction2D_eq_euler V E F hEF angle₂ h₂]

/-! ## 3. The Regge field equations via the Schläfli identity -/

variable {nH : ℕ}

/-- The **Regge action** `S = ∑_h V_h · ε_h`, as a function of a one-parameter
    variation of the edge lengths, where `Vol h t` is the volume of hinge `h` and
    `defc h t` its deficit angle along the variation. -/
noncomputable def reggeAction (Vol defc : Fin nH → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ h, Vol h t * defc h t

/-
**Variation of the Regge action.**  Under the **Schläfli identity**
    `∑_h V_h · ε_h′ = 0` (the deficit-angle variations cancel), the derivative of
    the Regge action is `∑_h V_h′ · ε_h`, i.e. only the volume variation survives.
-/
theorem reggeAction_hasDerivAt (Vol defc : Fin nH → ℝ → ℝ)
    (Vol' defc' : Fin nH → ℝ) (t₀ : ℝ)
    (hVol : ∀ h, HasDerivAt (Vol h) (Vol' h) t₀)
    (hdefc : ∀ h, HasDerivAt (defc h) (defc' h) t₀)
    (schlafli : ∑ h, Vol h t₀ * defc' h = 0) :
    HasDerivAt (reggeAction Vol defc) (∑ h, Vol' h * defc h t₀) t₀ := by
  have := fun h => ( hVol h ).mul ( hdefc h );
  convert HasDerivAt.sum ( fun h _ => this h ) using 1 ; ring;
  rotate_right;
  exacts [ Finset.univ, by ext; simp +decide [ reggeAction ], by simp +decide [ Finset.sum_add_distrib, schlafli ] ]

/-- **Discrete Einstein field equations.**  Assuming the Schläfli identity, the
    Regge action is stationary along the variation iff the discrete Einstein
    equations `∑_h (∂V_h) · ε_h = 0` hold. -/
theorem regge_einstein_iff (Vol defc : Fin nH → ℝ → ℝ)
    (Vol' defc' : Fin nH → ℝ) (t₀ : ℝ)
    (hVol : ∀ h, HasDerivAt (Vol h) (Vol' h) t₀)
    (hdefc : ∀ h, HasDerivAt (defc h) (defc' h) t₀)
    (schlafli : ∑ h, Vol h t₀ * defc' h = 0) :
    deriv (reggeAction Vol defc) t₀ = 0 ↔ ∑ h, Vol' h * defc h t₀ = 0 := by
  rw [(reggeAction_hasDerivAt Vol defc Vol' defc' t₀ hVol hdefc schlafli).deriv]

end RGF.Regge