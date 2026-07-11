/-
  Foundations/RGFTransport.lean

  Unified interface: transporting results between ℝ and the generative reals.

  The ordered ring isomorphism `RGFReal'.orderedRingEquivReal : RGFReal' ≃+*o ℝ`
  means every statement about the additive, multiplicative and order structure of
  `ℝ` can be re-expressed for `RGFReal'`.  This file packages that as reusable
  transport lemmas and gives sample "downstream" theorems (order density and a
  scaling-limit statement) phrased directly for the generative reals — the same
  pattern any RGF analysis/physics module would follow to switch from Mathlib's
  `ℝ` to `RGFReal'`.
-/
import Mathlib
import RGF.Math.Real.RGFRealExamples

namespace RGF

open RGFNat RGFInt

namespace RGFReal'

/-! ## Generic transport principle -/

/-- Any predicate proven for a standard real holds for its generated RGF real
    (read through the canonical map). -/
theorem transport_pred (P : ℝ → Prop) (r : ℝ) (h : P r) : P (toReal (ofReal r)) := by
  rw [toReal_ofReal]; exact h

/-! ## Sample downstream results, phrased for the generative reals -/

/-- **Order density**, transported: between any two RGF reals (compared through
    `toReal`) lies a third generative real. -/
theorem rgf_dense (a b : RGFReal') (h : toReal a < toReal b) :
    ∃ c : RGFReal', toReal a < toReal c ∧ toReal c < toReal b := by
  obtain ⟨x, hx1, hx2⟩ := exists_between h
  exact ⟨ofReal x, by rw [toReal_ofReal]; exact hx1, by rw [toReal_ofReal]; exact hx2⟩

/-- **A scaling limit, transported.**  The generative reals `c · 1/(n+1)` tend to
    `0` (measured through the canonical map), exactly as in `ℝ`.  This is the
    template a scaling-limit theorem (e.g. a height-field limit) would use to run
    entirely inside `RGFReal'`. -/
theorem rgf_scaling_limit (c : ℝ) :
    Filter.Tendsto (fun n : ℕ => toReal (ofReal (c / (n + 1)))) Filter.atTop (nhds 0) := by
  simp only [toReal_ofReal]
  have h0 : (0 : ℝ) = c * 0 := by ring
  rw [h0]
  exact (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c).congr (by intro n; ring)

end RGFReal'
end RGF
