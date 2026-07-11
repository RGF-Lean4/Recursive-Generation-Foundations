/-
  Paper 9 — "Recursive constitutive cosmology: unified emergence of cosmological phenomena from the locked membrane"
  (Recursive-Generative Cosmology: unified emergence of cosmological phenomena
   from the locked membrane), L. Sun 2026.

  This file places the ninth input paper into the RGF `Physics/Emergence` layer.
  It formalizes the paper's cleanly-stated, checkable algebraic and analytic cores:

  * §3 dark energy: the one-loop off-diagonal topological-coherence coefficient
    `C_UV = 24π²` and the reduction `C_UV/(2π)⁴ = 3/(2π²)` giving
    `ρ_DE⁽¹⁾ = (3/2π²) Λ² H²` (eq. (3.5)).
  * §3.1 pentagon pole geometry: the exact identity that the sum over the ten
    ordered pole pairs of the inverse fourth power of the FORS pentagon chords
    equals `6` (eq. (3.4)), both in the algebraic form and via the geometric
    chord-length values `(2 sin(π/5))² = (5-√5)/2`, `(2 sin(2π/5))² = (5+√5)/2`.
  * §1.2 pole manifold: the five FORS poles `k_j = Λ e^{i2π(2j+1)/5}` and the
    corrected residues `Res = (2Λ/5) e^{-i3π(2j+1)/5}` all have modulus `2Λ/5`
    (equimodularity, eq. (1.4)).
  * §2.1.4 inflation: the Starobinsky-type slow-roll spectral predictions
    `n_s ≈ 1 - 2/N_e - 3/(2N_e²)`, `r ≈ 12/N_e²`, with the e-fold value
    `N_e = 54` giving `r = 1/243` and `n_s` consistent with the Planck 2018
    value `0.9649 ± 0.0042` (eqs. (2.8), (2.10)).
  * §2.2 baryogenesis: the recursion `B_{n+1} = tanh(βB_n)` has `B = 0` as a
    fixed point whose linearization slope is `β`, hence the symmetric state is
    unstable exactly when `β > 1` (eqs. (2.13)–(2.14)).

  All statements are internal RGF theorems; the physical constants (Λ, H, N_e …)
  enter only as the coefficients the paper derives.  The two open problems the
  paper itself flags (the exact dark-energy magnitude, the neutrino mass ratio)
  are *not* asserted here.
-/
import Mathlib
import RGF.Generative.Locking.PentagonComplete

open Real

namespace RGF.Paper9Cosmology

/-! ### §3.2 Dark-energy coefficient -/

/-- Eq. (3.5): the one-loop off-diagonal dark-energy coefficient reduces
`C_UV/(2π)⁴ = 24π²/(2π)⁴` to `3/(2π²)`. -/
theorem darkEnergy_coefficient : (24 * π ^ 2) / (2 * π) ^ 4 = 3 / (2 * π ^ 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- Eq. (3.4)→text: with the pentagon pair-sum equal to `6`, the UV coherence
coefficient is `C_UV = (2π)²·6 = 24π²`. -/
theorem C_UV_value : (2 * π) ^ 2 * 6 = 24 * π ^ 2 := by ring

/-! ### §3.1 FORS pentagon pole geometry -/

/-
Eq. (3.4), algebraic core.  Writing `a = (5-√5)/2` and `b = (5+√5)/2` for the
squared chord lengths of the regular pentagon, the paper's pair sum
`10/a² + 10/b²` is exactly `6`.
-/
theorem pentagon_pair_sum_alg :
    (10 : ℝ) / ((5 - Real.sqrt 5) / 2) ^ 2 + 10 / ((5 + Real.sqrt 5) / 2) ^ 2 = 6 := by
  grind

/-- Geometric identification: the squared length of a regular-pentagon
adjacent chord (central angle `2π/5`) is `(2 sin(π/5))² = (5-√5)/2`. -/
theorem chord_sq_adjacent : (2 * Real.sin (π / 5)) ^ 2 = (5 - Real.sqrt 5) / 2 := by
  have h : Real.cos (2 * (π / 5)) = 1 - 2 * Real.sin (π / 5) ^ 2 := by
    rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq (π / 5)]
  have hc : Real.cos (2 * (π / 5)) = (Real.sqrt 5 - 1) / 4 := by
    rw [show 2 * (π / 5) = 2 * π / 5 by ring]; exact RGF.PentagonComplete.cos_two_pi_div_five
  nlinarith [h, hc]

/-- Geometric identification: the squared length of a regular-pentagon
next-adjacent chord (central angle `4π/5`) is `(2 sin(2π/5))² = (5+√5)/2`. -/
theorem chord_sq_next : (2 * Real.sin (2 * π / 5)) ^ 2 = (5 + Real.sqrt 5) / 2 := by
  have h : Real.cos (2 * (2 * π / 5)) = 1 - 2 * Real.sin (2 * π / 5) ^ 2 := by
    rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq (2 * π / 5)]
  have hc : Real.cos (2 * (2 * π / 5)) = -Real.cos (π / 5) := by
    rw [show 2 * (2 * π / 5) = π - π / 5 by ring, Real.cos_pi_sub]
  rw [Real.cos_pi_div_five] at hc
  nlinarith [h, hc]

/-- Eq. (3.4), geometric form: the pentagon pole-pair sum
`10/(2 sin(π/5))⁴ + 10/(2 sin(2π/5))⁴ = 6`. -/
theorem pentagon_pair_sum_geo :
    (10 : ℝ) / (2 * Real.sin (π / 5)) ^ 4 + 10 / (2 * Real.sin (2 * π / 5)) ^ 4 = 6 := by
  have h1 : ((2 * Real.sin (π / 5)) ^ 2) ^ 2 = (2 * Real.sin (π / 5)) ^ 4 := by ring
  have h2 : ((2 * Real.sin (2 * π / 5)) ^ 2) ^ 2 = (2 * Real.sin (2 * π / 5)) ^ 4 := by ring
  have e1 := chord_sq_adjacent
  have e2 := chord_sq_next
  have key := pentagon_pair_sum_alg
  calc
    (10 : ℝ) / (2 * Real.sin (π / 5)) ^ 4 + 10 / (2 * Real.sin (2 * π / 5)) ^ 4
        = 10 / ((2 * Real.sin (π / 5)) ^ 2) ^ 2 + 10 / ((2 * Real.sin (2 * π / 5)) ^ 2) ^ 2 := by
          rw [h1, h2]
    _ = 10 / ((5 - Real.sqrt 5) / 2) ^ 2 + 10 / ((5 + Real.sqrt 5) / 2) ^ 2 := by rw [e1, e2]
    _ = 6 := key

/-! ### §1.2 Pole/residue equimodularity -/

/-- Eq. (1.3): each FORS pole `k_j = Λ e^{i2π(2j+1)/5}` has modulus `|Λ|`. -/
theorem pole_modulus (Λ : ℝ) (j : ℕ) :
    ‖(Λ : ℂ) * Complex.exp (Complex.I * (2 * π * (2 * j + 1) / 5))‖ = |Λ| := by
  norm_num [ Complex.norm_exp ]

/-- Eq. (1.4): the corrected residues `Res = (2Λ/5) e^{-i3π(2j+1)/5}` are all
equimodular with modulus `2|Λ|/5`. -/
theorem residue_modulus (Λ : ℝ) (j : ℕ) :
    ‖((2 * Λ / 5 : ℝ) : ℂ) * Complex.exp (Complex.I * (-(3 * π * (2 * j + 1) / 5)))‖
      = 2 * |Λ| / 5 := by
  norm_num [ Complex.norm_exp, abs_mul, abs_div ]

/-! ### §2.1.4 Starobinsky slow-roll inflation -/

/-- Scalar spectral index as a function of the e-fold number (eq. (2.8)). -/
noncomputable def specIndex (Ne : ℝ) : ℝ := 1 - 2 / Ne - 3 / (2 * Ne ^ 2)

/-- Tensor-to-scalar ratio as a function of the e-fold number (eq. (2.8)). -/
noncomputable def tensorRatio (Ne : ℝ) : ℝ := 12 / Ne ^ 2

/-- Eq. (2.10): at the self-consistently locked e-fold number `N_e = 54`, the
tensor-to-scalar ratio is exactly `r = 12/54² = 1/243 ≈ 0.00412`. -/
theorem tensorRatio_54 : tensorRatio 54 = 1 / 243 := by
  unfold tensorRatio; norm_num

/-- Eq. (2.10): at `N_e = 54` the spectral index `n_s ≈ 0.9625` lies within the
Planck 2018 `1σ` band `0.9649 ± 0.0042`. -/
theorem specIndex_54_planck_consistent :
    |specIndex 54 - 9649 / 10000| ≤ 42 / 10000 := by
  unfold specIndex; norm_num

/-! ### §2.2 Baryogenesis recursion -/

/-- The Hubble-time coarse-grained baryon recursion `B ↦ tanh(βB)` (eq. (2.13)
with vanishing bias). -/
noncomputable def baryonMap (β B : ℝ) : ℝ := Real.tanh (β * B)

/-- `B = 0` is a fixed point of the symmetric baryon recursion. -/
theorem baryon_symmetric_fixed_point (β : ℝ) : baryonMap β 0 = 0 := by
  simp [baryonMap]

/-
The linearization slope of the baryon recursion at the symmetric fixed point
`B = 0` is `β` (eq. (2.13)).
-/
theorem baryonMap_deriv_zero (β : ℝ) : deriv (baryonMap β) 0 = β := by
  unfold baryonMap;
  norm_num [ Real.tanh_eq_sinh_div_cosh, mul_comm β ]

/-- Eq. (2.14): the FORS spectral gap forces `β > 1`, so the symmetric fixed
point is linearly unstable (slope `> 1`), selecting a nonzero baryon asymmetry. -/
theorem baryon_symmetric_unstable (β : ℝ) (hβ : 1 < β) : 1 < deriv (baryonMap β) 0 := by
  rw [baryonMap_deriv_zero]; exact hβ

end RGF.Paper9Cosmology