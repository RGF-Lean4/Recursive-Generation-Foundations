/-
  FORS propagator and anomalous dispersion: scaling-covariant hard core

  This file collects the analysis hard core of the FORS continuum field theory that
  concerns the *propagator* and the *anomalous dispersion relation*:

  * the three-dimensional free propagator at coincident points,
    `forsPropagator3D t = (∫_ℝ e^{-t k²} dk)³`, decays as `π^{3/2}·t^{-3/2}`;
  * the anomalous dispersion `forsDispersion k = |k|^{5/2}` (the anomalous scaling forced
    by the quintic locking `k = 5`) is scaling covariant of degree `5/2`;
  * the kinetic integral `∫₀¹ t^{5/2} dt = 2/7`.

  These complement the leading-order scaling forms `propagator`/`K` of
  `FORS/AnomalousScaling.lean` with their fully-derived Gaussian-integral content.
-/

import Mathlib

open MeasureTheory intervalIntegral

namespace RGF.FORS

/-- FORS three-dimensional free propagator at coincident points:
    `P(t) = (∫_ℝ e^{-t k²} dk)³`. -/
noncomputable def forsPropagator3D (t : ℝ) : ℝ := (∫ x : ℝ, Real.exp (-t * x ^ 2)) ^ 3

/-- FORS anomalous dispersion relation `ω(k) = |k|^{5/2}` (the anomalous scaling derived
    from the quintic locking). -/
noncomputable def forsDispersion (k : ℝ) : ℝ := |k| ^ ((5 : ℝ) / 2)

/-- Gaussian integral: `∫_ℝ e^{-t x²} dx = √(π/t)`, for `t > 0`. -/
theorem gaussian_integral_eq (t : ℝ) :
    (∫ x : ℝ, Real.exp (-t * x ^ 2)) = Real.sqrt (Real.pi / t) :=
  integral_gaussian t

/-- FORS three-dimensional propagator decay: `P(t) = π^{3/2} · t^{-3/2}`, for `t > 0`. -/
theorem forsPropagator3D_decay {t : ℝ} (ht : 0 < t) :
    forsPropagator3D t = Real.pi ^ ((3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) := by
  convert congr_arg ( · ^ 3 ) ( gaussian_integral_eq t ) using 1 ; norm_num [ Real.sqrt_eq_rpow ];
  rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num;
  rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.rpow_neg ( by positivity ) ] ; ring

/-- Propagator scaling covariance: `P(s·t) = s^{-3/2}·P(t)`, for `s, t > 0`. -/
theorem forsPropagator3D_scaling {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    forsPropagator3D (s * t) = s ^ (-(3 : ℝ) / 2) * forsPropagator3D t := by
  rw [forsPropagator3D_decay (mul_pos hs ht), forsPropagator3D_decay ht,
    Real.mul_rpow hs.le ht.le]
  ring

/-- FORS anomalous-dispersion scaling covariance: `ω(s·k) = s^{5/2}·ω(k)`, for `s ≥ 0`. -/
theorem forsDispersion_scaling {s : ℝ} (hs : 0 ≤ s) (k : ℝ) :
    forsDispersion (s * k) = s ^ ((5 : ℝ) / 2) * forsDispersion k := by
  unfold forsDispersion
  rw [abs_mul, Real.mul_rpow (abs_nonneg s) (abs_nonneg k), abs_of_nonneg hs]

/-- Kinetic integral: `∫₀¹ t^{5/2} dt = 2/7`. -/
theorem kinetic_integral : (∫ t in (0:ℝ)..1, t ^ ((5 : ℝ) / 2)) = 2 / 7 := by
  rw [ integral_rpow ] <;> norm_num

end RGF.FORS
