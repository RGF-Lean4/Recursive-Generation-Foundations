/-
  RGF/Phenomenology/StandardModel/RGFRealConstantTransport.lean

  A "one-way pull-back" demonstration of the final locked constants (Transport of the
  final locked constants).

  This file demonstrates the **compromise approach** recommended in the review comments:
  rather than rewriting the entire physics layer, we only pull the final locked core
  constants back onto the internal generative reals `RGFReal'`, via the proven ordered-ring
  isomorphism `RGFReal'.orderedRingEquivReal : RGFReal' ≃+*o ℝ` (and its underlying
  `ringEquivReal`/`ofReal`/`toReal`), and then verify the axiom footprint of these
  **final conclusions**.

  In this way the leading gauge-prediction constants land entirely inside the RGF
  "internal real-number sandbox" at the level of the type signature:

    * weak mixing angle       `sin²θ_W = 3/8`   —— `weinberg_transported`
    * parameter count (3 gen) `26`              —— `params_internal`
    * emergent spatial dim    `d = 3`           —— `dim_internal`

  Remark (a factual addition to the review): in the original formalization these three
  leading constants are in fact valued in `ℚ` (`sin²θ_W`) and `ℕ` (parameter count,
  dimension) respectively, and do not themselves depend on the external `ℝ`. So for them,
  "landing in the internal reals" *embeds* these rational/natural values into `RGFReal'`
  rather than eliminating an `ℝ` dependency. What genuinely retains `ℝ` is the intermediate
  analytic derivation (limits, ODEs, measures, …), which is exactly the part the review
  suggests *not* rewriting but keeping on Mathlib's `ℝ`. This file only handles the
  "final conclusion" layer.
-/
import Mathlib
import RGF.Math.Real.RealInstances
import RGF.Math.Real.RGFRealExamples
import RGF.Math.Real.RGFOrderReal
import RGF.Phenomenology.StandardModel.RGFGaugeRatios
import RGF.Phenomenology.StandardModel.StandardModel26Parameters

namespace RGF.RealConstantTransport

open RGF RGF.GaugeRatios RGF.StandardModel26

/-! ## 1. Consistency of the constant values on the internal reals via the isomorphism -/

/-- After pulling the external real `3/8` back to `RGFReal'` via the canonical map `ofReal`,
it is exactly the fraction `3/8` of the internal real field itself. This is the numeric
meaning of the "internal real sandbox closure": the pulled-back result contains no trace
of any external `ℝ`, but is precisely the `3/8` written using `RGFReal'`'s own field
operations. -/
theorem weinberg_internal_value :
    RGFReal'.ofReal ((3 : ℝ) / 8) = (3 : RGFReal') / 8 := by
  apply RGFReal'.toReal_injective
  rw [RGFReal'.toReal_ofReal, ← RGFReal'.ringEquivReal_apply, map_div₀, map_ofNat, map_ofNat]

/-! ## 2. One-way pull-back of the proven physical theorems onto the internal reals -/

/-- **Weak mixing angle, pulled back to the internal reals.** The proven gauge prediction
`sinSqWeinberg fullGeneration = 3/8` (`RGF.GaugeRatios.weinberg_fullGeneration`, valued in
`ℚ`), after being pulled back via the isomorphism, equals the internal fraction `3/8` as an
element of `RGFReal'`. -/
theorem weinberg_transported :
    RGFReal'.ofReal ((sinSqWeinberg fullGeneration : ℚ) : ℝ) = (3 : RGFReal') / 8 := by
  rw [weinberg_fullGeneration]; push_cast; exact weinberg_internal_value

/-- **Parameter count, landing in the internal reals.** The count of free parameters of the
three-generation Standard Model `totalSMParams 3 = 26`
(`RGF.StandardModel26.totalSMParams_three`) equals `26` as an element of `RGFReal'`. -/
theorem params_internal : ((totalSMParams 3 : ℕ) : RGFReal') = 26 := by
  rw [totalSMParams_three]; norm_num

/-- **Emergent spatial dimension, landing in the internal reals.**
`rgfPrediction.emergentDim = 3` (`RGF.StandardModel26.rgf_generation_number`) equals `3` as
an element of `RGFReal'`. -/
theorem dim_internal : ((rgfPrediction.emergentDim : ℕ) : RGFReal') = 3 := by
  rw [rgf_generation_number]; norm_num

/-! ## 3. The order structure of the internal reals is available for the pulled-back
constants as well -/

/-- The weak mixing angle is an element of the internal real field strictly between `0` and
`1`—the *order* part of the isomorphism (`orderedRingEquivReal`) guarantees that this
physically required constraint is decidable within `RGFReal'`. -/
theorem weinberg_between_zero_one :
    (0 : RGFReal') < (3 : RGFReal') / 8 ∧ (3 : RGFReal') / 8 < 1 :=
  ⟨by positivity, by norm_num⟩

/-! ## 4. Packaging: the final locked predictions inside the internal real sandbox -/

/-- **Capstone theorem: all three leading locked constants land inside the RGF internal
reals `RGFReal'`.** This is the concrete realization of the compromise approach recommended
in the review: the analytic derivation stays on Mathlib's `ℝ`, and only the final
conclusions are pulled back one-way via the proven isomorphism `RGFReal' ≃+*o ℝ`, giving a
closed loop that is self-contained at the level of type signatures. -/
theorem final_constants_internal :
    RGFReal'.ofReal ((sinSqWeinberg fullGeneration : ℚ) : ℝ) = (3 : RGFReal') / 8 ∧
    ((totalSMParams 3 : ℕ) : RGFReal') = 26 ∧
    ((rgfPrediction.emergentDim : ℕ) : RGFReal') = 3 ∧
    (0 : RGFReal') < (3 : RGFReal') / 8 ∧ (3 : RGFReal') / 8 < 1 :=
  ⟨weinberg_transported, params_internal, dim_internal,
    weinberg_between_zero_one.1, weinberg_between_zero_one.2⟩

end RGF.RealConstantTransport
