/-
  Paper 6S — "Supplementary material: gauge-group emergence and the Standard-Model parameter spectrum in RCD"
  (Supplement: gauge-group emergence and the Standard-Model parameter spectrum),
  L. Sun 2026.

  Placed in the RGF `Phenomenology/StandardModel` layer.  Formalizes the paper's
  spectral selection of the `3+2` pole partition (§SM-01):

  * the five FORS pole phases `e^{i2π(2j+1)/5}` sum to zero (eq. (2.2)), so the
    single-block `U(5)` drift matrix is nilpotent;
  * the standard `3+2` partition drift moduli: the 3-subset effective modulus is
    `(1 + 2cos(2π/5))/3 = φ/3` and the 2-subset effective modulus is
    `cos(π/5) = (1+√5)/4`, both `< 1` (L1 satisfied);
  * the surviving anomaly-free gauge algebra `su(3) ⊕ su(2) ⊕ u(1)` has dimension
    `8 + 3 + 1 = 12`.

  The full 52-partition anomaly analysis is the paper's numerical content; here we
  machine-check the exact algebraic moduli and dimension counts that drive it.
-/
import Mathlib
import RGF.Generative.Locking.PentagonComplete

open Real

namespace RGF.Paper6S

/-- `dim su(n) = n² − 1`: the Standard-Model algebra dimensions `8` and `3`. -/
theorem su3_su2_dims : 3 ^ 2 - 1 = 8 ∧ 2 ^ 2 - 1 = 3 := by norm_num

/-- The surviving gauge algebra `su(3) ⊕ su(2) ⊕ u(1)` has dimension `12`. -/
theorem gaugeAlgebra_dim : (3 ^ 2 - 1) + (2 ^ 2 - 1) + 1 = 12 := by norm_num

/-- 3-subset effective drift modulus of the standard `3+2` partition:
`(1 + 2cos(2π/5))/3 = φ/3 = (1+√5)/6`. -/
theorem partition_3subset_modulus :
    (1 + 2 * Real.cos (2 * π / 5)) / 3 = (1 + Real.sqrt 5) / 6 := by
  rw [RGF.PentagonComplete.cos_two_pi_div_five]; ring

/-- 2-subset effective drift modulus of the standard `3+2` partition:
`cos(π/5) = (1+√5)/4`. -/
theorem partition_2subset_modulus : Real.cos (π / 5) = (1 + Real.sqrt 5) / 4 :=
  Real.cos_pi_div_five

/-
Both partition moduli are strictly `< 1`, so the L1 spectral condition holds
(with `ρ ∈ (0,1)` the block spectral radii are `ρ·(modulus) < 1`).
-/
theorem partition_moduli_lt_one :
    (1 + 2 * Real.cos (2 * π / 5)) / 3 < 1 ∧ Real.cos (π / 5) < 1 := by
  norm_num [ Real.cos_two_mul, mul_div_assoc ];
  constructor <;> nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]

/-- The `j`-th FORS pole phase (eq. (1.1)/(2.2)). -/
noncomputable def polePhase (j : ℕ) : ℂ := Complex.exp (2 * π * Complex.I * (2 * j + 1) / 5)

/-- Eq. (2.2): the five FORS pole phases sum to zero, so the one-block `U(5)`
drift matrix `Γ = (ρ/5)∑ e^{iarg k_j}·I` vanishes. -/
theorem five_pole_phases_sum_zero : ∑ j : Fin 5, polePhase j = 0 := by
  set ω : ℂ := Complex.exp (2 * π * Complex.I / 5) with hω
  set r : ℂ := Complex.exp (4 * π * Complex.I / 5) with hr
  have hfac : ∀ j : Fin 5, polePhase (j : ℕ) = ω * r ^ (j : ℕ) := by
    intro j
    rw [polePhase, hω, hr, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; ring
  have hne : r ≠ 1 :=
    ne_of_apply_ne Complex.im (by
      rw [hr, Complex.exp_im]; norm_num
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])))
  have h5 : r ^ 5 = 1 := by
    rw [hr, ← Complex.exp_nat_mul,
      show ((5 : ℕ) : ℂ) * (4 * (π : ℂ) * Complex.I / 5) = ((2 : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) by
        push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I 2
  have hgeom : ∑ j ∈ Finset.range 5, r ^ j = 0 := by
    rw [geom_sum_eq hne, h5]; simp
  calc ∑ j : Fin 5, polePhase (j : ℕ)
      = ∑ j : Fin 5, ω * r ^ (j : ℕ) := Finset.sum_congr rfl (fun j _ => hfac j)
    _ = ω * ∑ j : Fin 5, r ^ (j : ℕ) := by rw [Finset.mul_sum]
    _ = ω * ∑ j ∈ Finset.range 5, r ^ j := by rw [Fin.sum_univ_eq_sum_range (fun j => r ^ j) 5]
    _ = 0 := by rw [hgeom, mul_zero]

end RGF.Paper6S