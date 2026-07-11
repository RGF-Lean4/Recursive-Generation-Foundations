/-
# RCDxRGF.Contraction — bridging the RCD P5 fixed-point core to RGF's quantitative Banach theory

Part of the optional bridge library `RCDxRGF`.

RCD's constitutive-map emergence (papers 0 and 2) formalises only the
one-dimensional linear core: `Paper0.contraction_unique_fixed`
(`|α| < 1 ∧ α·x = x ⟹ x = 0`) and the scalar stationary variance
`Paper0.stationary_variance` / `Paper2.mode_stationary_variance`
(the geometric series `Σ (α²)ᵏ = 1/(1-α²)`).

RGF provides the **general quantitative** version:

* `RGFRuleLayer.RGFContraction.fixedPoint_unique_l1` — uniqueness of the fixed
  point of an arbitrary `L¹` contraction on the rule layer;
* `RGFRuleLayer.RGFContraction.convergence_rate` / `iterate_distance_bound` —
  geometric (exponential) convergence to it.

Here we (i) re-export those general results as the upgraded P4 → P5 statements and
(ii) show that the RCD one-dimensional core is literally an *instance* of a
general real contraction principle.
-/

import Mathlib
import RGF.Math.Real.BanachContraction

namespace RCDxRGF.Contraction

open RGFRuleLayer

/-- **General real contraction principle.**  Any self-map `f : ℝ → ℝ` that is a
    `c`-Lipschitz contraction (`c < 1`) has at most one fixed point.  This is the
    one-line abstraction that subsumes RCD's scalar `Paper0.contraction_unique_fixed`. -/
theorem rgf_real_contraction_unique
    (f : ℝ → ℝ) (c : ℝ) (hc1 : c < 1)
    (hcontr : ∀ x y, |f x - f y| ≤ c * |x - y|)
    {x y : ℝ} (hx : f x = x) (hy : f y = y) : x = y := by
  have h := hcontr x y
  rw [hx, hy] at h
  have hle : |x - y| ≤ 0 := by nlinarith [abs_nonneg (x - y)]
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

/-- **RCD scalar core as an instance (the bridge).**  RCD's
    `Paper0.contraction_unique_fixed` (`|α| < 1`, `α·x = x ⟹ x = 0`) is recovered
    from the general real contraction principle applied to the linear map
    `t ↦ α·t`, whose obvious fixed point is `0`. -/
theorem rcd_contraction_unique_fixed_via_general (α x : ℝ) (hα : |α| < 1)
    (hx : α * x = x) : x = 0 :=
  rgf_real_contraction_unique (fun t => α * t) |α| hα
    (fun a b => le_of_eq (by rw [← mul_sub, abs_mul])) hx (by ring)

/-- **Upgraded P5 uniqueness.**  The unique-stationary-state claim that RCD only
    establishes in the scalar case holds for an arbitrary `L¹` contraction on the
    rule layer: any two fixed points coincide (`l1Dist = 0`). -/
theorem rcd_p5_fixed_point_unique {α : Type*} [Fintype α]
    (sys : RGFContraction α) (z₁ z₂ : RGFRuleLayer α)
    (h₁ : sys.IsFixedPoint z₁) (h₂ : sys.IsFixedPoint z₂) :
    l1Dist z₁ z₂ = 0 :=
  sys.fixedPoint_unique_l1 z₁ z₂ h₁ h₂

/-- **Upgraded P5 quantitative convergence.**  Iterating an arbitrary `L¹`
    contraction converges to its fixed point geometrically (exponential decay of
    the `L¹` distance), upgrading RCD's scalar geometric-series picture. -/
theorem rcd_p5_geometric_convergence {α : Type*} [Fintype α]
    (sys : RGFContraction α) (z zstar : RGFRuleLayer α)
    (hstar : sys.IsFixedPoint zstar) (n : ℕ) :
    l1Dist (sys.iterate z n) zstar ≤ sys.contractCoeff ^ n * l1Dist z zstar :=
  sys.convergence_rate z zstar hstar n

/-- **Stationary variance (shared geometric-series core).**  Both RCD scalar
    stationary-variance lemmas (`Paper0.stationary_variance` and
    `Paper2.mode_stationary_variance`) are the single identity
    `Σ (r)ᵏ = 1/(1-r)` for `0 ≤ r < 1`; we record the general statement that
    underlies both. -/
theorem rcd_stationary_variance_general (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ, r ^ k) = 1 / (1 - r) := by
  rw [tsum_geometric_of_lt_one hr0 hr1, one_div]

end RCDxRGF.Contraction
