/-
  Paper 11 — "Self-referential solitons and endogenization of the observer: a rigorous framework for Recursive Constitutive Dynamics"
  (Self-referential solitons and the endogenization of the observer), L. Sun 2026.

  Placed in the RGF **Generative** layer (Layer 1 / Generative spine): the observer
  is internalized as a self-referential fixed point of the recursion.

  Formalizes cleanly-statable cores of the soliton construction
  `R_G[Ψ] = K[tanh(G·Ψ)]`:

  * the saturating nonlinearity `tanh` is **bounded** (`|tanh x| < 1`) and
    **odd**, giving the exponential localization / regularization of the kernel;
  * componentwise `tanh` is **nonlinear**, which breaks the global `U(1)`/scaling
    symmetry (so the soliton manifold is phase-locked, not circularly symmetric);
  * **Lyapunov stability**: along a uniformly contracting recursion the distance
    to the soliton fixed point strictly decreases off the fixed point.
-/
import Mathlib

namespace RGF.Paper11

/-- The saturating nonlinearity `tanh` is bounded: `|tanh x| < 1`. -/
theorem abs_tanh_lt_one (x : ℝ) : |Real.tanh x| < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  refine abs_lt.mpr ⟨?_, ?_⟩
  · rw [lt_div_iff₀] <;> nlinarith [Real.sinh_sq x, Real.cosh_pos x]
  · rw [div_lt_iff₀] <;> nlinarith [Real.sinh_sq x, Real.cosh_pos x]

/-- `tanh` is odd. -/
theorem tanh_odd (x : ℝ) : Real.tanh (-x) = -Real.tanh x :=
  Real.tanh_neg x

/-- Componentwise `tanh` is nonlinear, breaking the global `U(1)`/scaling
symmetry: there is a scale `a` and point `x` with `tanh(a·x) ≠ a·tanh x`. -/
theorem tanh_breaks_scaling : ∃ a x : ℝ, Real.tanh (a * x) ≠ a * Real.tanh x := by
  refine ⟨2, Real.log 2, ?_⟩
  norm_num [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul,
    Real.sinh_log, Real.cosh_log]

/-- Lyapunov stability (Thm 4.2): along a uniformly contracting recursion the
distance to the soliton fixed point strictly decreases at any non-fixed state. -/
theorem lyapunov_strict_decrease {α : Type*} [MetricSpace α] {K : NNReal}
    {R : α → α} (h : ContractingWith K R) {x xstar : α}
    (hfix : R xstar = xstar) (hne : x ≠ xstar) :
    dist (R x) xstar < dist x xstar := by
  obtain ⟨K_lt_1, hK⟩ := h
  have hstep := hK.dist_le_mul x xstar
  rw [hfix] at hstep
  exact lt_of_le_of_lt hstep
    (mul_lt_of_lt_one_left (dist_pos.mpr hne) (mod_cast K_lt_1))

end RGF.Paper11
