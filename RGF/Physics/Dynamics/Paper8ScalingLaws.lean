/-
  Paper 8 (+ 8S) — "Recursive and spiral scaling laws: a cross-scale unified theoretical framework from elementary particles to the cosmos"
  (Recursive and spiral scaling laws), L. Sun 2026.

  Placed in the RGF `Physics/Dynamics` layer.  Formalizes the exact coefficients
  and the sign mechanism of the two scaling laws:

  * Recursive Scaling Law `n = k + α·l − β·f` with `α = cos(2π/5) = (√5−1)/4`
    (angular-excitation coefficient) and `β = 1/5` (recovery coefficient), both
    fixed by the FORS five-pole (regular-pentagon) geometry, not fitted;
  * Spiral Scaling Law `ξ⁻²(L) = m₀² + α_D·L⁻² − β_wind·L^{d−1}·f`: the *negative*
    sign of the winding term comes from the exact cancellation of the Z₅ spiral
    phases, i.e. the five fifth-roots of unity sum to zero.
-/
import Mathlib
import RGF.Generative.Locking.PentagonComplete

open Real

namespace RGF.Paper8

/-- RSL angular-excitation coefficient `α = cos(2π/5) = (√5−1)/4`. -/
theorem rsl_alpha : Real.cos (2 * π / 5) = (Real.sqrt 5 - 1) / 4 :=
  RGF.PentagonComplete.cos_two_pi_div_five

/-- RSL recovery coefficient `β = 1/5`. -/
theorem rsl_beta : (1 : ℝ) / 5 = 0.2 := by norm_num

/-- `k`-th Z₅ spiral phase `e^{2πik/5}`. -/
noncomputable def spiralPhase (k : ℕ) : ℂ := Complex.exp (2 * π * Complex.I * k / 5)

/-- SSL winding-sign mechanism: the five Z₅ spiral phases sum to zero, giving the
exact cancellation responsible for the negative winding term. -/
theorem spiral_phase_sum_zero : ∑ k : Fin 5, spiralPhase k = 0 := by
  set ω : ℂ := Complex.exp (2 * π * Complex.I / 5) with hω
  have hpow : ∀ k : Fin 5, spiralPhase (k : ℕ) = ω ^ (k : ℕ) := by
    intro k; rw [spiralPhase, hω, ← Complex.exp_nat_mul]; congr 1; ring
  have hne : ω ≠ 1 :=
    ne_of_apply_ne Complex.im (by
      rw [hω, Complex.exp_im]; norm_num
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])))
  have h5 : ω ^ 5 = 1 := by
    rw [hω, ← Complex.exp_nat_mul,
      show ((5 : ℕ) : ℂ) * (2 * (π : ℂ) * Complex.I / 5) = 2 * (π : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  have hgeom : ∑ k ∈ Finset.range 5, ω ^ k = 0 := by
    rw [geom_sum_eq hne, h5]; simp
  calc ∑ k : Fin 5, spiralPhase (k : ℕ)
      = ∑ k : Fin 5, ω ^ (k : ℕ) := Finset.sum_congr rfl (fun k _ => hpow k)
    _ = ∑ k ∈ Finset.range 5, ω ^ k := Fin.sum_univ_eq_sum_range (fun k => ω ^ k) 5
    _ = 0 := hgeom

end RGF.Paper8