/-
  Formalization of the two scaling laws of RST
  Formalization of the two scaling laws of Recursive Stratum-Creation Systems Theory (RST)

  This file formalizes the two scaling laws given in §6 of the paper "Recursive
  Stratum-Creation Systems Theory (RST) — a unified framework building systems from the
  locked-membrane and pan-life concepts", and integrates them into the existing RGF
  (recursive generation) system. Both scaling laws originate from the FORS five-pole
  geometry (regular pentagon) but characterize different dimensions of a system's existence:

  · Recursive Scaling Law (RSL):
        n = k + α·l − β·f          —— the "spatial stability ordering" of structures
      where α = cos(2π/5) = (√5−1)/4 ≈ 0.3090, β = 1/5 = 0.20,
      uniquely determined by the FORS five-pole geometry (not fitted parameters).

  · Spiral Scaling Law (SSL):
        ξ⁻²(L) = m₀² + α_D·L⁻² − β_wind·L^(d−1)·f(L/L_max)   —— the "temporal-trajectory
      geometry" of the evolution. The negative sign of the winding term comes from the exact
      cancellation of the Z₅ spiral phase factors in the sum over winding modes
      (Abel summation of fifth roots of unity, ∑ = 0).

  This file reuses existing modules:
  · `RGF.PentagonComplete.cos_two_pi_div_five`  (the geometric value of α)
  · `Z5_cos_sum_zero` (from AlphaBeta, the geometric origin of the SSL negative sign)
  · `xiInvSq`, `criticalLength` (from SpiralScaling, the critical length of the SSL when f≡1)
-/

import Mathlib
import RGF.Generative.Locking.PentagonComplete
import RGF.Phenomenology.StandardModel.AlphaBeta
import RGF.Physics.Dynamics.SpiralScaling

open Real

namespace RST

/-! ## Part 1: coefficients of the Recursive Scaling Law RSL (RSL coefficients) -/

/-- The angular-excitation coefficient of the RSL, α = cos(2π/5), coming from the momentum
projection loss of the FORS five poles from the real axis to the first excited state. -/
noncomputable def alphaRSL : ℝ := Real.cos (2 * π / 5)

/-- The saturation (boundary-cutoff) coefficient of the RSL, β = 1/5, coming from the a₂/a₀
coefficient of the heat-kernel expansion of the fractional Laplacian H = (−Δ)^(5/4). -/
noncomputable def betaRSL : ℝ := 1 / 5

/-- α = cos(2π/5) = (√5 − 1)/4 (deduplicated to agree with the shared module
`RGF.PentagonComplete.cos_two_pi_div_five`). -/
theorem alphaRSL_val : alphaRSL = (Real.sqrt 5 - 1) / 4 := by
  rw [alphaRSL]; exact RGF.PentagonComplete.cos_two_pi_div_five

/-- β = 0.20. -/
theorem betaRSL_val : betaRSL = 0.20 := by unfold betaRSL; norm_num

/-- α is a root of the regular-pentagon quadratic 4x² + 2x − 1 = 0. -/
theorem alphaRSL_root : 4 * alphaRSL ^ 2 + 2 * alphaRSL - 1 = 0 := by
  rw [alphaRSL_val]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- α > 0. -/
theorem alphaRSL_pos : 0 < alphaRSL := by
  rw [alphaRSL_val]
  have : (2 : ℝ) < Real.sqrt 5 := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
    nlinarith [Real.sqrt_nonneg 5, this]
  linarith

/-- β > 0. -/
theorem betaRSL_pos : 0 < betaRSL := by unfold betaRSL; norm_num

/-- Numeric localization: 0.3090 ≤ α ≤ 0.3091, i.e. α ≈ 0.3090. -/
theorem alphaRSL_approx : 0.3090 ≤ alphaRSL ∧ alphaRSL ≤ 0.3091 := by
  rw [alphaRSL_val]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hlo : (2.236 : ℝ) ≤ Real.sqrt 5 := by nlinarith [Real.sqrt_nonneg 5, h5]
  have hhi : Real.sqrt 5 ≤ (2.2361 : ℝ) := by nlinarith [Real.sqrt_nonneg 5, h5]
  constructor <;> linarith

/-! ## Part 2: the Recursive Scaling Law RSL itself (the RSL itself) -/

/-- The Recursive Scaling Law RSL: n(k, l, f) = k + α·l − β·f.
    Given a system's triple (k, l, f), the value n uniquely determines the stability level of
    that structure—the lower n, the more stable. -/
noncomputable def rsl (k l f : ℝ) : ℝ := k + alphaRSL * l - betaRSL * f

/-- The RSL is monotonically increasing in the phase-space dimension k. -/
theorem rsl_mono_k (l f : ℝ) : Monotone (fun k => rsl k l f) := by
  intro a b hab; unfold rsl; linarith

/-- The RSL is strictly increasing in the angular excitation l (since α > 0). -/
theorem rsl_strictMono_l (k f : ℝ) : StrictMono (fun l => rsl k l f) := by
  intro a b hab; unfold rsl
  have := alphaRSL_pos
  nlinarith

/-- The RSL is strictly decreasing in the filling fraction f (since β > 0): saturation lowers
the scaling exponent. -/
theorem rsl_strictAnti_f (k l : ℝ) : StrictAnti (fun f => rsl k l f) := by
  intro a b hab; unfold rsl
  have := betaRSL_pos
  nlinarith

/-- Testable prediction P1 (equal spacing of noble-gas scaling exponents): when the angular
    excitation l and filling fraction f are fixed while the phase-space dimension k increases
    in steps of 1, the RSL gives a constant adjacent difference of 1.00 for the scaling
    exponent, i.e. the scaling exponents are equally spaced. -/
theorem rsl_noble_gas_equal_spacing (k l f : ℝ) :
    rsl (k + 1) l f - rsl k l f = 1 := by unfold rsl; ring

/-- From the above: the difference of any two steps equals the difference in the number of
steps, so the whole family of scaling exponents forms an arithmetic progression. -/
theorem rsl_arithmetic (k l f : ℝ) (n : ℕ) :
    rsl (k + n) l f - rsl k l f = n := by unfold rsl; ring

/-! ## Part 3: the Spiral Scaling Law SSL (the SSL) -/

/-- The Spiral Scaling Law SSL: ξ⁻²(L) = m₀² + α_D·L⁻² − β_wind·L^(d−1)·f(L/L_max).
    `m₀` is the bare mass, `αD` the diffusion coefficient, `βwind` the winding coefficient,
    `fcut` the cutoff function, and `Lmax` the cutoff scale. -/
noncomputable def sslInvSq (m₀ αD βwind Lmax : ℝ) (d : ℕ) (fcut : ℝ → ℝ) (L : ℝ) : ℝ :=
  m₀ ^ 2 + αD / L ^ 2 - βwind * L ^ ((d : ℝ) - 1) * fcut (L / Lmax)

/-- When the cutoff function is identically f ≡ 1, the SSL degenerates to `xiInvSq` from the
    existing SpiralScaling, i.e. the simplified form ξ⁻²(L) = m₀² + α/L² − β·L^(d−1) of §6.2
    of the paper. -/
theorem sslInvSq_const_one (m₀ αD βwind Lmax : ℝ) (d : ℕ) (L : ℝ) :
    sslInvSq m₀ αD βwind Lmax d (fun _ => 1) L = xiInvSq m₀ αD βwind d L := by
  unfold sslInvSq xiInvSq; ring

/-- The negative-sign feature of the SSL winding term: when βwind > 0, the cutoff function is
    positive, and L > 0, the winding term makes ξ⁻² strictly lower than the pure-diffusion
    baseline (m₀² + α_D L⁻²). This is the key dynamical feature by which the SSL describes a
    "spiral rising/falling" evolutionary trajectory. -/
theorem sslInvSq_winding_lowers (m₀ αD βwind Lmax : ℝ) (d : ℕ) (fcut : ℝ → ℝ) (L : ℝ)
    (hβ : 0 < βwind) (hL : 0 < L) (hcut : 0 < fcut (L / Lmax)) :
    sslInvSq m₀ αD βwind Lmax d fcut L < m₀ ^ 2 + αD / L ^ 2 := by
  unfold sslInvSq
  have hpow : 0 < L ^ ((d : ℝ) - 1) := Real.rpow_pos_of_pos hL _
  have : 0 < βwind * L ^ ((d : ℝ) - 1) * fcut (L / Lmax) := by positivity
  linarith

/-- The geometric origin of the SSL negative sign: the Z₅ spiral phase factors of the FORS
    kernel cancel exactly in the sum over winding modes. Concretely, the sum of the (real
    parts of the) fifth roots of unity is zero: ∑_{j=0}^{4} cos(2πpj/5) = 0 (when 5 ∤ p).
    This cancellation is exactly the algebraic source of the negative sign of the winding
    term (Abel summation of fifth roots of unity). -/
theorem ssl_winding_sign_origin (p : ℤ) (hp : ¬ (5 : ℤ) ∣ p) :
    (Finset.range 5).sum (fun j => Real.cos (2 * Real.pi * p * j / 5)) = 0 :=
  Z5_cos_sum_zero p hp

/-! ## Part 4: the critical length of the SSL (the f ≡ 1 case, reusing SpiralScaling) -/

/-- In the simplified case where the cutoff function is f ≡ 1, the critical length of the SSL
    satisfies the balance condition L_c^(d+1) = α_D/β_wind, i.e. the momentum contribution
    and the winding contribution are equal at L_c. This follows directly from the existing
    `criticalLength_balance`. -/
theorem ssl_criticalLength_balance (αD βwind : ℝ) (d : ℕ)
    (hα : 0 < αD) (hβ : 0 < βwind) :
    (criticalLength αD βwind d) ^ ((d : ℝ) + 1) = αD / βwind :=
  criticalLength_balance αD βwind d hα hβ

/-- At d = 3, the SSL critical length is (α_D/β_wind)^(1/4). -/
theorem ssl_criticalLength_d3 (αD βwind : ℝ) (hα : 0 < αD) (hβ : 0 < βwind) :
    criticalLength αD βwind 3 = (αD / βwind) ^ (1 / 4 : ℝ) :=
  criticalLength_d3 αD βwind hα hβ

/-! ## Part 5: the common origin of the two scaling laws (common origin) -/

/-- Summary of the common origin: the RSL and SSL share the root in the FORS five-pole
    geometry (regular pentagon).
    · The angular coefficient α = cos(2π/5) of the RSL is a root of the regular-pentagon
      quadratic 4x²+2x−1=0;
    · The negative sign of the SSL winding term comes from the same Z₅ geometry, where the sum
      of the fifth roots of unity is zero.
    Both stem from a single source but head to the two dimensions of "spatial-structure
    ordering" and "temporal-trajectory geometry". -/
theorem rst_common_pentagon_origin :
    (4 * alphaRSL ^ 2 + 2 * alphaRSL - 1 = 0) ∧
    (∀ p : ℤ, ¬ (5 : ℤ) ∣ p →
      (Finset.range 5).sum (fun j => Real.cos (2 * Real.pi * p * j / 5)) = 0) :=
  ⟨alphaRSL_root, fun p hp => ssl_winding_sign_origin p hp⟩

end RST
