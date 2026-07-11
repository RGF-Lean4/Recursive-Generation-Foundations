import Mathlib

/-!
# Path B · Route 1: Non-Hermitian transition-amplitude candidate model

This file is a self-contained, machine-verified formalization of the
"non-Hermitian transition-amplitude" candidate for the lepton Koide phase.

## Construction

We take the fifth root of unity `ω = exp(2πi/5)` and the complex-phase
`5 × 5` transition-amplitude matrix
`A i j = (2/5) · ω^(i·j)` for `i ≠ j`, with zero diagonal.  Restricting to the
lepton "pole" subspace with indices `{0, 1, 4}` gives a `3 × 3` matrix
`lepton_matrix_nh = (2/5) · [[0,1,1],[1,0,ω⁴],[1,ω⁴,0]]`.

## What is proved

* `lepton_matrix_nh_entries` — the explicit `3 × 3` form (with `w = ω⁴`).
* `lepton_matrix_nh_not_isHermitian` — the matrix is genuinely non-Hermitian
  (since `conj(ω⁴) = ω ≠ ω⁴`), which is the prerequisite for complex
  eigenvalues.
* `lepton_matrix_nh_trace` — the trace is `0`.
* `lepton_matrix_nh_det` — the determinant is `(16/125)·ω⁴`.
* `lepton_charpoly_factored` — the characteristic polynomial factors exactly:
  `det(c·I − M) = (c + (2/5)ω⁴)(c² − (2/5)ω⁴ c − 8/25)`, a purely algebraic
  identity valid for every `ω`.
* `lepton_eigenvector` — `(0, 1, −1)` is an eigenvector with eigenvalue
  `λ₀ = −(2/5)ω⁴`.
* `arg_lepton_eigenvalue` — `arg(λ₀) = 3π/5`.

## Honest conclusion on the physical target `2π/9`

The eigen-phase that can be locked analytically here is `3π/5 ≈ 1.885`, while
the Koide target phase is `2π/9 ≈ 0.698`.  These are not equal
(`koide_target_ne_eigen_phase`).  Hence this non-Hermitian candidate on the
`{0,1,4}` subspace does **not** naturally produce `2π/9`; reproducing `2π/9`
would require a different subspace / weight convention, or treating the phase
as a free parameter.  We record this faithfully rather than reverse-engineering
a definition to hit the target.
-/

namespace LeptonPhaseNonHermitian

open Complex Matrix

/-- The fifth root of unity `ω = exp(2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- `ω⁵ = 1`. -/
lemma omega_pow_five : omega ^ 5 = 1 := by
  unfold omega
  rw [← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = 2 * (Real.pi : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_eq_one_iff]
  exact ⟨1, by push_cast; ring⟩

/-- The complex-phase `5 × 5` transition-amplitude matrix
`A i j = (2/5)·ω^(i·j)` for `i ≠ j`, with zero diagonal. -/
noncomputable def transition_amplitude_nh : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => if i = j then 0 else (2 / 5 : ℂ) * omega ^ (i.val * j.val)

/-- The lepton "pole" indices `{0, 1, 4}`. -/
def leptonIdx : Fin 3 → Fin 5 := ![0, 1, 4]

/-- The reduced `3 × 3` lepton matrix on the subspace `{0, 1, 4}`. -/
noncomputable def lepton_matrix_nh : Matrix (Fin 3) (Fin 3) ℂ :=
  transition_amplitude_nh.submatrix leptonIdx leptonIdx

/-- Abbreviation `w = ω⁴`, the only complex-phase entry of `lepton_matrix_nh`. -/
noncomputable def w : ℂ := omega ^ 4

/-- `-ω⁴ = exp(3πi/5)`: a clean closed form for the relevant phase. -/
lemma neg_omega_pow_four : -(omega ^ 4) = Complex.exp (3 * Real.pi * Complex.I / 5) := by
  have h2pi : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
    rw [Complex.exp_eq_one_iff]; exact ⟨1, by push_cast; ring⟩
  unfold omega
  rw [← Complex.exp_nat_mul]
  have hstep : -Complex.exp ((4 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 5))
      = Complex.exp ((Real.pi : ℂ) * Complex.I)
        * Complex.exp ((4 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 5)) := by
    rw [Complex.exp_mul_I]; simp
  rw [hstep, ← Complex.exp_add]
  rw [show (Real.pi : ℂ) * Complex.I + (4 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 5)
       = 3 * (Real.pi : ℂ) * Complex.I / 5 + 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_add, h2pi, mul_one]

/-- The imaginary part of `ω⁴` is nonzero (it equals `-sin(3π/5) < 0`). -/
lemma omega_pow_four_im_ne : (omega ^ 4).im ≠ 0 := by
  have him : (omega ^ 4).im = -Real.sin (3 * Real.pi / 5) := by
    have h := congrArg Complex.im neg_omega_pow_four
    rw [show (3 * (Real.pi : ℂ) * Complex.I / 5) = ((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I by
      push_cast; ring] at h
    rw [Complex.exp_ofReal_mul_I_im] at h
    simp at h; linarith [h]
  rw [him]
  have hpos : Real.sin (3 * Real.pi / 5) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  linarith

/-- Explicit `3 × 3` form: `lepton_matrix_nh = (2/5)·[[0,1,1],[1,0,w],[1,w,0]]`. -/
lemma lepton_matrix_nh_entries :
    lepton_matrix_nh = !![0, 2 / 5, 2 / 5; 2 / 5, 0, (2 / 5) * w; 2 / 5, (2 / 5) * w, 0] := by
  unfold lepton_matrix_nh transition_amplitude_nh leptonIdx w
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.submatrix]

/-- The reduced matrix is genuinely non-Hermitian: `M ≠ Mᴴ`.  This is the
prerequisite for complex eigenvalues, in contrast to the naive real-amplitude
(Hermitian) model. -/
lemma lepton_matrix_nh_not_isHermitian : lepton_matrix_nh ≠ lepton_matrix_nhᴴ := by
  rw [lepton_matrix_nh_entries]
  intro h
  have h21 := congrFun (congrFun h 2) 1
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_fin_one, Matrix.head_fin_const, map_mul, map_div₀, map_ofNat, star_def] at h21
  apply omega_pow_four_im_ne
  have hconj : (starRingEnd ℂ) w = w := by
    have h2 : (2 / 5 : ℂ) * w = (2 / 5 : ℂ) * (starRingEnd ℂ) w := by
      convert h21 using 2
    exact (mul_left_cancel₀ (by norm_num : (2 / 5 : ℂ) ≠ 0) h2).symm
  rw [Complex.conj_eq_iff_im] at hconj
  exact hconj

/-- The trace of the reduced matrix is `0`. -/
lemma lepton_matrix_nh_trace : lepton_matrix_nh.trace = 0 := by
  rw [lepton_matrix_nh_entries]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three]

/-- The determinant of the reduced matrix is `(16/125)·ω⁴`. -/
lemma lepton_matrix_nh_det : lepton_matrix_nh.det = (16 / 125) * omega ^ 4 := by
  rw [lepton_matrix_nh_entries]
  simp only [w, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

/-- The characteristic polynomial factors exactly:
`det(c·I − M) = (c + (2/5)ω⁴)(c² − (2/5)ω⁴ c − 8/25)`. -/
lemma lepton_charpoly_factored (c : ℂ) :
    (c • (1 : Matrix (Fin 3) (Fin 3) ℂ) - lepton_matrix_nh).det
      = (c + (2 / 5) * omega ^ 4) * (c ^ 2 - (2 / 5) * omega ^ 4 * c - 8 / 25) := by
  rw [lepton_matrix_nh_entries]
  simp only [w]
  simp [Matrix.det_fin_three]
  ring

/-- `(0, 1, −1)` is an eigenvector of the reduced matrix with eigenvalue
`λ₀ = −(2/5)ω⁴`. -/
lemma lepton_eigenvector :
    lepton_matrix_nh.mulVec ![0, 1, -1] = (-(2 / 5) * omega ^ 4) • ![0, 1, -1] := by
  rw [lepton_matrix_nh_entries]
  funext i
  fin_cases i <;>
    simp [w, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The eigenvalue `λ₀ = −(2/5)ω⁴` has argument exactly `3π/5`. -/
lemma arg_lepton_eigenvalue : Complex.arg (-(2 / 5 : ℂ) * omega ^ 4) = 3 * Real.pi / 5 := by
  have heq : -(2 / 5 : ℂ) * omega ^ 4
      = ((2 / 5 : ℝ) : ℂ)
        * (Complex.cos ((3 * Real.pi / 5 : ℝ) : ℂ)
          + Complex.sin ((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_mul_I]
    rw [show ((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I = 3 * (Real.pi : ℂ) * Complex.I / 5 by
      push_cast; ring]
    rw [← neg_omega_pow_four]; push_cast; ring
  rw [heq, Complex.arg_mul_cos_add_sin_mul_I (by norm_num)]
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- Honest numerical comparison: the Koide target phase `2π/9` is **not** equal
to the analytically locked eigen-phase `3π/5`. -/
theorem koide_target_ne_eigen_phase : 2 * Real.pi / 9 ≠ 3 * Real.pi / 5 := by
  intro h
  have hpi : Real.pi > 0 := Real.pi_pos
  nlinarith [h]

/-- Summary of the rigorously established facts about the Route-1 non-Hermitian
candidate model. -/
theorem route1_nonhermitian_facts :
    lepton_matrix_nh ≠ lepton_matrix_nhᴴ
    ∧ lepton_matrix_nh.trace = 0
    ∧ lepton_matrix_nh.det = (16 / 125) * omega ^ 4
    ∧ (∀ c : ℂ, (c • (1 : Matrix (Fin 3) (Fin 3) ℂ) - lepton_matrix_nh).det
        = (c + (2 / 5) * omega ^ 4) * (c ^ 2 - (2 / 5) * omega ^ 4 * c - 8 / 25))
    ∧ lepton_matrix_nh.mulVec ![0, 1, -1] = (-(2 / 5) * omega ^ 4) • ![0, 1, -1]
    ∧ Complex.arg (-(2 / 5 : ℂ) * omega ^ 4) = 3 * Real.pi / 5
    ∧ 2 * Real.pi / 9 ≠ 3 * Real.pi / 5 :=
  ⟨lepton_matrix_nh_not_isHermitian, lepton_matrix_nh_trace, lepton_matrix_nh_det,
    lepton_charpoly_factored, lepton_eigenvector, arg_lepton_eigenvalue,
    koide_target_ne_eigen_phase⟩

/-!
## Open problem (recorded honestly, not left as a false `sorry`)

Find an amplitude / pole-subspace convention within this non-Hermitian
transition-amplitude framework that yields exactly the Koide phase `2π/9`, or
prove rigorously that no such convention exists within the framework.  The
specific candidate analyzed here — amplitude `(2/5)·ω^(i·j)` on the subspace
`{0,1,4}` — produces the eigen-phase `3π/5`, which differs from `2π/9`.
-/

end LeptonPhaseNonHermitian
