/-
# L2L3.ComplexNecessity — the contrapositive argument for the necessity of a complex base field

This module completes the comparison argument for the "necessity of a complex base field":
from "only a conjugate complex eigenpair is observed" to "the real field is impossible while
the complex field works".

* `real_fifth_root_unique`: over the reals, `x⁵ = 1` has only the trivial solution `x = 1`
  (so no nontrivial one-dimensional real representation of `Z₅` exists).
* `omega` / `omega_not_real`: the eigenvalue selected by the system, `ω = e^{2πi/5}`, is not real.
* `omega_conj_pair_distinct`: `ω⁴ = conj ω`, and `ω` together with its conjugate forms a
  distinct conjugate pair.
* `rotation_no_real_eigenvector`: the two-dimensional real rotation matrix by angle `2π/5` has
  no real eigenvalue / real eigenvector whatsoever.
* `complex_necessity_master`: combining the above, a system carrying the `Z₅`-locked phase
  cannot be built over the pure real field; a complex base field is necessary.
-/

import Mathlib
import RGF.Generative.Bridge.L2L3RemainingGaps

open scoped BigOperators
open Complex

namespace RGF.L2L3.ComplexNecessity

noncomputable section

/-! ## Uniqueness of the fifth root of unity over the reals -/

/-
**`real_fifth_root_unique`.** Over the reals, `x⁵ = 1` has only the trivial solution `x = 1`.
    Hence `Z₅` has no nontrivial one-dimensional real representation.
-/
theorem real_fifth_root_unique (x : ℝ) (hx : x ^ 5 = 1) : x = 1 := by
  nlinarith [ sq_nonneg ( x^2 - 1 ), sq_nonneg ( x^2 ) ]

/-! ## The complex eigenvalue selected by the system, ω = e^{2πi/5} -/

/-- The eigenvalue selected by the system, `ω = e^{2πi/5}`. -/
def omega : ℂ := Complex.exp (2 * Real.pi / 5 * Complex.I)

/-
`ω⁵ = 1`: it is a fifth root of unity.
-/
theorem omega_pow_five : omega ^ 5 = 1 := by
  rw [ show omega = Complex.exp ( 2 * Real.pi / 5 * Complex.I ) by rfl, ← Complex.exp_nat_mul, mul_comm ] ; norm_num;
  exact Complex.exp_eq_one_iff.mpr ⟨ 1, by ring ⟩

/-
**`omega_not_real`.** `ω` is not real (its imaginary part is nonzero).
-/
theorem omega_not_real : omega.im ≠ 0 := by
  unfold omega; norm_num [ Complex.exp_re, Complex.exp_im ] ; exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith [ Real.pi_pos ] ) ) ;

/-
**`omega_conj_pair_distinct`.** `ω⁴ = conj ω`, and `ω` differs from its conjugate;
    that is, the system selects a distinct pair of non-real conjugate eigenvalues.
-/
theorem omega_conj_pair_distinct :
    omega ^ 4 = (starRingEnd ℂ) omega ∧ (starRingEnd ℂ) omega ≠ omega := by
  unfold omega;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, ← Complex.exp_nat_mul ];
  exact ⟨ ⟨ by rw [ ← Real.cos_two_pi_sub ] ; ring_nf, by rw [ ← Real.sin_two_pi_sub ] ; ring_nf ⟩, by linarith [ Real.sin_pos_of_pos_of_lt_pi ( show 0 < 2 * Real.pi / 5 by positivity ) ( by linarith [ Real.pi_pos ] ) ] ⟩

/-! ## The two-dimensional real rotation has no real eigenvector -/

/-- **`rotation_no_real_eigenvector`.** The two-dimensional real rotation matrix by angle
    `2π/5` has no eigenvector over the reals (discriminant `(cosθ−μ)²+sin²θ > 0`). This
    directly reuses `RGF.L2L3Gaps.z5Rot_no_real_eigenvector`. -/
theorem rotation_no_real_eigenvector (μ : ℝ) (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    (RGF.L2L3Gaps.z5RotMatrix).mulVec v ≠ μ • v :=
  RGF.L2L3Gaps.z5Rot_no_real_eigenvector μ v hv

/-! ## Synthesis: necessity of a complex base field -/

/-- **`complex_necessity_master`.** A combined argument for the necessity of a complex base
    field:
    1. over the reals, `x⁵ = 1` has only the trivial root, so there is no nontrivial
       one-dimensional real representation;
    2. the two-dimensional real rotation matrix carrying the `Z₅` phase locking has no
       eigenvector over the reals;
    3. after complexification the system selects a distinct pair of non-real conjugate fifth
       roots of unity `ω, conj ω` (`ω⁵ = 1`).
    Together these show that a system carrying the `Z₅`-locked phase cannot be built over the
    pure real field; a complex base field is necessary. -/
theorem complex_necessity_master :
    (∀ x : ℝ, x ^ 5 = 1 → x = 1) ∧
    (∀ (μ : ℝ) (v : Fin 2 → ℝ), v ≠ 0 →
      (RGF.L2L3Gaps.z5RotMatrix).mulVec v ≠ μ • v) ∧
    (∃ ω : ℂ, ω ^ 5 = 1 ∧ ω.im ≠ 0 ∧
      ω ^ 4 = (starRingEnd ℂ) ω ∧ (starRingEnd ℂ) ω ≠ ω) := by
  refine ⟨real_fifth_root_unique, rotation_no_real_eigenvector, omega, omega_pow_five,
    omega_not_real, omega_conj_pair_distinct.1, omega_conj_pair_distinct.2⟩

end

end RGF.L2L3.ComplexNecessity