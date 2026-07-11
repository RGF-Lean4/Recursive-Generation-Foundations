/-
  RGF/Phenomenology/StandardModel/RGFRealConclusionLayer.lean

  A unified "internal-real conclusion layer" (Unified internal-real conclusion layer).

  Following the **compromise approach** recommended in the review and confirmed by the user,
  this file systematically pulls **all final locked predictions** of the RGF
  physics/phenomenology layer back onto the internal generative reals `RGFReal'` via the
  proven ordered-ring isomorphism

      `RGFReal'.orderedRingEquivReal : RGFReal' ≃+*o ℝ`

  (and its underlying `ringEquivReal` / `ofReal` / `toReal`). In this way, all leading numeric
  predictions land in the RGF "internal real sandbox" at the level of type signatures, while
  the analytic derivations (limits, ODEs, measures, ζ functions, etc.) still **remain** on
  Mathlib's `ℝ`—this is the core of the compromise: the heavy analytic ecosystem does not
  move, while the light final-conclusion layer is internalized as a whole.

  Sectors covered (sectors):
    A. gauge sector      weak mixing angle `sin²θ_W = 3/8`, `Tr T₃²`, `Tr Q²`, charge ratio `q_e/q_d = -3`
    B. parameter count   Standard Model 26 parameters, dimension `d = 3`, CKM angle/phase counts
    C. neutrino sector   `sin²θ₁₃ = 0`, `sin²θ₁₂ = 1/3`, `sin²θ₂₃ = 1/2`, Jarlskog `J = 0`, Koide sum `= 3`
    D. gauge-group dims   `dim SU(3)=8`, `dim SU(2)=3`, `dim SU(5)=24`, SM gauge dim `12`, `φ(5)=4`
    E. spectral regularization  ζ-regularized sum of the naturals `= -1/12`
    F. phase transition/threshold  `K_r` phase-transition order `1/2` (K₃), `3/4` (K₅)
    G. analytic constants  `√2`, golden ratio `φ` (irrational, internalized via `ofReal` while
       preserving the algebraic relation)

  Remark (faithfulness): the leading constants of A–F are valued in `ℚ`/`ℕ`/`ℝ` (with rational
  value) in the original formalization, so for them "landing in the internal reals" *embeds*
  these rational/natural values into `RGFReal'`; only `√2`, `φ` of sector G are genuinely
  irrational analytic constants, whose internalization preserves their respective algebraic
  relations (`x² = 2`, `x² = x + 1`), showing that the isomorphism transport is lossless for
  irrationals as well. The axiom footprint of all conclusions agrees with that of the existing
  `RGFReal'` machinery (`propext, Classical.choice, Quot.sound`, plus `Lean.ofReduceBool,
  Lean.trustCompiler` coming from the underlying `decide` dependency of `RGFReal'`).
-/
import Mathlib
import RGF.Math.Real.RealInstances
import RGF.Math.Real.RGFRealExamples
import RGF.Math.Real.RGFOrderReal
import RGF.Phenomenology.StandardModel.RGFGaugeRatios
import RGF.Phenomenology.StandardModel.StandardModel26Parameters
import RGF.Phenomenology.StandardModel.NeutrinoPrediction
import RGF.Phenomenology.StandardModel.RGFToStandardModel
import RGF.Phenomenology.StandardModel.RGFThreshold
import RGF.Phenomenology.StandardModel.RGFZetaRegularization
import RGF.Phenomenology.StandardModel.KoideExt

namespace RGF.RealConclusionLayer

open RGF RGF.GaugeRatios RGF.StandardModel26 RGF.Neutrino RGF.ZetaRegularization
  TRS.LeptonKoideExt

/-! ## 0. Transport bridges (transport bridges)

`ofReal` is the inverse direction of the isomorphism `RGFReal' ≃+*o ℝ`. The three lemmas
below show that it sends rational/integer/natural constants from the external number field
back to the corresponding constants of `RGFReal'` **without a trace**. -/

/-- `ofReal` sends an external rational constant back to the internal rational constant. -/
theorem ofReal_ratCast (q : ℚ) : RGFReal'.ofReal (q : ℝ) = (q : RGFReal') := by
  apply RGFReal'.toReal_injective
  rw [RGFReal'.toReal_ofReal, ← RGFReal'.ringEquivReal_apply, map_ratCast]

/-- `ofReal` sends an external integer constant back to the internal integer constant. -/
theorem ofReal_intCast (n : ℤ) : RGFReal'.ofReal (n : ℝ) = (n : RGFReal') := by
  apply RGFReal'.toReal_injective
  rw [RGFReal'.toReal_ofReal, ← RGFReal'.ringEquivReal_apply, map_intCast]

/-- `ofReal` sends an external natural constant back to the internal natural constant. -/
theorem ofReal_natCast (n : ℕ) : RGFReal'.ofReal (n : ℝ) = (n : RGFReal') := by
  apply RGFReal'.toReal_injective
  rw [RGFReal'.toReal_ofReal, ← RGFReal'.ringEquivReal_apply, map_natCast]

/-- Convenience wrapper: if an external real `r` equals the real embedding of some rational
`q`, then `ofReal r` is the internal rational `q`. -/
theorem ofReal_of_eq_ratCast {r : ℝ} {q : ℚ} (h : r = (q : ℝ)) :
    RGFReal'.ofReal r = (q : RGFReal') := by rw [h, ofReal_ratCast]

/-! ## A. Gauge sector: weak mixing angle, traces and charge ratio -/

/-- **Weak mixing angle `sin²θ_W = 3/8`, internal-real version.** -/
theorem weinberg_internal :
    RGFReal'.ofReal ((sinSqWeinberg fullGeneration : ℚ) : ℝ) = (3 : RGFReal') / 8 := by
  rw [weinberg_fullGeneration, ofReal_ratCast]; norm_num

/-- `Tr(T₃²) = 1/2` (`5̄`), internal-real version. -/
theorem fivebar_sumT3sq_internal :
    RGFReal'.ofReal ((sumT3sq fivebar : ℚ) : ℝ) = (1 : RGFReal') / 2 := by
  rw [fivebar_sumT3sq, ofReal_ratCast]; norm_num

/-- `Tr(Q²) = 4/3` (`5̄`), internal-real version. -/
theorem fivebar_sumQsq_internal :
    RGFReal'.ofReal ((sumQsq fivebar : ℚ) : ℝ) = (4 : RGFReal') / 3 := by
  rw [fivebar_sumQsq, ofReal_ratCast]; norm_num

/-- `Tr(T₃²) = 3/2` (`10`), internal-real version. -/
theorem ten_sumT3sq_internal :
    RGFReal'.ofReal ((sumT3sq ten : ℚ) : ℝ) = (3 : RGFReal') / 2 := by
  rw [ten_sumT3sq, ofReal_ratCast]; norm_num

/-- `Tr(Q²) = 4` (`10`), internal-real version. -/
theorem ten_sumQsq_internal :
    RGFReal'.ofReal ((sumQsq ten : ℚ) : ℝ) = (4 : RGFReal') := by
  rw [ten_sumQsq, ofReal_ratCast]; norm_num

/-- **Charge ratio `q_e / q_d = -3`, internal-real version.** The integer ratio `-3` forced
by anomaly freedom `3 q_d + q_e = 0` lands in the internal reals. -/
theorem charge_ratio_internal : RGFReal'.ofReal ((-3 : ℤ) : ℝ) = (-3 : RGFReal') :=
  ofReal_intCast (-3)

/-! ## B. Parameter counts: 26 parameters, dimension, CKM counts (valued in ℕ, embedded
directly) -/

/-- **The 26 free parameters of the three-generation Standard Model, internal-real version.** -/
theorem params_internal : ((totalSMParams 3 : ℕ) : RGFReal') = 26 := by
  rw [totalSMParams_three]; norm_num

/-- **Emergent spatial dimension `d = 3`, internal-real version.** -/
theorem dim_internal : ((rgfPrediction.emergentDim : ℕ) : RGFReal') = 3 := by
  rw [rgf_generation_number]; norm_num

/-- CKM mixing-parameter count `= 4`, internal-real version. -/
theorem mixingParams_internal : ((numMixingParams 3 : ℕ) : RGFReal') = 4 := by
  rw [mixing_params_three]; norm_num

/-- CKM mixing-angle count `= 3`, internal-real version. -/
theorem mixingAngles_internal : ((numMixingAngles 3 : ℕ) : RGFReal') = 3 := by
  rw [ckm_breakdown.1]; norm_num

/-- CKM Dirac-phase count `= 1`, internal-real version. -/
theorem diracPhases_internal : ((numDiracPhases 3 : ℕ) : RGFReal') = 1 := by
  rw [ckm_breakdown.2]; norm_num

/-! ## C. Neutrino sector: tri-bimaximal mixing angles, CP conservation, Koide sum -/

/-- **`sin²θ₁₃ = 0` (reactor angle), internal-real version.** -/
theorem theta13_internal :
    RGFReal'.ofReal ((Utbm 0 2) ^ 2) = (0 : RGFReal') := by
  rw [sinSq_theta13, ofReal_of_eq_ratCast (q := 0) (by norm_num)]; norm_num

/-- **`sin²θ₁₂ = 1/3` (solar angle), internal-real version.** -/
theorem theta12_internal :
    RGFReal'.ofReal ((Utbm 0 1) ^ 2 / (1 - (Utbm 0 2) ^ 2)) = (1 : RGFReal') / 3 := by
  rw [sinSq_theta12, ofReal_of_eq_ratCast (q := 1 / 3) (by norm_num)]; norm_num

/-- **`sin²θ₂₃ = 1/2` (atmospheric angle, maximal), internal-real version.** -/
theorem theta23_internal :
    RGFReal'.ofReal ((Utbm 1 2) ^ 2 / (1 - (Utbm 0 2) ^ 2)) = (1 : RGFReal') / 2 := by
  rw [sinSq_theta23, ofReal_of_eq_ratCast (q := 1 / 2) (by norm_num)]; norm_num

/-- **Jarlskog invariant `J = 0` (leading-order CP conservation), internal-real version.** -/
theorem jarlskog_internal : RGFReal'.ofReal (jarlskog Utbm) = (0 : RGFReal') := by
  rw [jarlskog_tbm_zero, ofReal_of_eq_ratCast (q := 0) (by norm_num)]; norm_num

/-- **Sum of Koide values `v₀ + v₁ + v₂ = 3`, internal-real version.** Holds for any phase
`δ`. -/
theorem koide_sum_internal (δ : ℝ) :
    RGFReal'.ofReal (v 0 δ + v 1 δ + v 2 δ) = (3 : RGFReal') := by
  rw [koide_val_sum_explicit, ofReal_of_eq_ratCast (q := 3) (by norm_num)]; norm_num

/-! ## D. Gauge-group dimensions (valued in ℕ) -/

/-- `dim SU(3) = 8`, internal-real version. -/
theorem su3_dim_internal : ((lie_dim_su 3 : ℕ) : RGFReal') = 8 := by
  rw [step3_su3_dim]; norm_num

/-- `dim SU(2) = 3`, internal-real version. -/
theorem su2_dim_internal : ((lie_dim_su 2 : ℕ) : RGFReal') = 3 := by
  rw [step3_su2_dim]; norm_num

/-- `dim SU(5) = 24`, internal-real version. -/
theorem su5_dim_internal : ((lie_dim_su 5 : ℕ) : RGFReal') = 24 := by
  rw [step4_su5_dim]; norm_num

/-- Total dimension of the Standard Model gauge group `1 + 3 + 8 = 12`, internal-real
version. -/
theorem sm_gauge_dim_internal :
    ((lie_dim_su 3 + lie_dim_su 2 + lie_dim_u1 : ℕ) : RGFReal') = 12 := by
  rw [step3_sm_total_dim]; norm_num

/-! ## E. Spectral ζ-regularization: sum of the naturals `= -1/12` -/

/-- **ζ-regularized sum of the naturals `= -1/12`, internal-real version.** The source theorem
`rgf_naturalNumbers_regularized_eq_neg_one_twelfth` gives `ζ(-1) = -1/12` (valued in `ℂ`); its
real part `-1/12`, after being pulled back to `RGFReal'` via the isomorphism, equals the
internal fraction `-1/12`. -/
theorem zeta_reg_internal :
    RGFReal'.ofReal (rgfRegularizedSum (-1)).re = -(1 : RGFReal') / 12 := by
  rw [rgf_naturalNumbers_regularized_eq_neg_one_twelfth,
    ofReal_of_eq_ratCast (q := -1 / 12) (by norm_num)]
  norm_num

/-! ## F. Phase-transition order / threshold exponent (valued in ℚ) -/

/-- `K₃` cluster phase-transition order `= 1/2`, internal-real version. -/
theorem K3_phase_internal :
    RGFReal'.ofReal ((phaseTransitionOrder 3 : ℚ) : ℝ) = (1 : RGFReal') / 2 := by
  rw [K3_phase_order, ofReal_ratCast]; norm_num

/-- `K₅` cluster phase-transition order `= 3/4`, internal-real version. -/
theorem K5_phase_internal :
    RGFReal'.ofReal ((phaseTransitionOrder 5 : ℚ) : ℝ) = (3 : RGFReal') / 4 := by
  rw [K5_phase_order, ofReal_ratCast]; norm_num

/-! ## G. Analytic (irrational) constants: internalized while preserving algebraic relations

The leading constants of the previous sectors are valued in `ℚ`/`ℕ`, so their internalization
is merely embedding. Below we internalize two genuinely **irrational** analytic constants `√2`
and the golden ratio `φ = (1+√5)/2` via `ofReal`, and prove that their respective **algebraic
relations** are preserved losslessly inside `RGFReal'`—this shows the isomorphism transport is
effective for irrationals as well. -/

/-- The internally generated `√2` (pulled back from the external `Real.sqrt 2` via the
isomorphism). -/
noncomputable def rgfSqrt2' : RGFReal' := RGFReal'.ofReal (Real.sqrt 2)

/-- The internal `√2` preserves the defining equation `x² = 2`. -/
theorem rgfSqrt2'_sq : rgfSqrt2' ^ 2 = (2 : RGFReal') := by
  apply RGFReal'.ringEquivReal.injective
  simp only [map_pow, map_ofNat, rgfSqrt2', RGFReal'.ringEquivReal_apply, RGFReal'.toReal_ofReal]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- The internal `√2` is positive. -/
theorem rgfSqrt2'_pos : (0 : RGFReal') < rgfSqrt2' := by
  rw [← RGFReal'.toReal_lt_iff]
  simp only [rgfSqrt2', RGFReal'.toReal_ofReal, RGFReal'.toReal_zero]
  exact Real.sqrt_pos.mpr (by norm_num)

/-- The internally generated golden ratio `φ = (1+√5)/2` (pulled back via the isomorphism). -/
noncomputable def rgfGolden : RGFReal' := RGFReal'.ofReal ((1 + Real.sqrt 5) / 2)

/-- **The internal golden ratio preserves its defining equation `φ² = φ + 1`.** -/
theorem rgfGolden_sq : rgfGolden ^ 2 = rgfGolden + 1 := by
  apply RGFReal'.ringEquivReal.injective
  simp only [map_pow, map_add, map_one, rgfGolden, RGFReal'.ringEquivReal_apply,
    RGFReal'.toReal_ofReal]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- The internal golden ratio is greater than `1`. -/
theorem rgfGolden_gt_one : (1 : RGFReal') < rgfGolden := by
  rw [← RGFReal'.toReal_lt_iff]
  simp only [rgfGolden, RGFReal'.toReal_ofReal, RGFReal'.toReal_one]
  have : (1:ℝ) < Real.sqrt 5 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-! ## H. Order structure: the physical constraints on the pulled-back constants are decidable
inside `RGFReal'` -/

/-- The weak mixing angle is an element of the internal real field strictly between `0` and
`1`. -/
theorem weinberg_between_zero_one :
    (0 : RGFReal') < (3 : RGFReal') / 8 ∧ (3 : RGFReal') / 8 < 1 :=
  ⟨by positivity, by norm_num⟩

/-! ## I. Capstone theorem: the internal-real conclusion layer -/

/-- **Capstone theorem: all leading locked predictions of the RGF physics/phenomenology layer
land inside the internal reals `RGFReal'`.**

This is the full realization of the compromise approach: the analytic derivations stay on
Mathlib's `ℝ`, while all final conclusions are pulled back as a whole via the proven
isomorphism `RGFReal' ≃+*o ℝ`, giving an "internal-real conclusion layer" that is
self-contained at the level of type signatures. The irrational analytic constants `√2`, `φ`
are internalized together with their algebraic relations. -/
theorem rgf_internal_conclusion_layer :
    -- A gauge sector
    RGFReal'.ofReal ((sinSqWeinberg fullGeneration : ℚ) : ℝ) = (3 : RGFReal') / 8 ∧
    RGFReal'.ofReal ((-3 : ℤ) : ℝ) = (-3 : RGFReal') ∧
    -- B parameter counts
    ((totalSMParams 3 : ℕ) : RGFReal') = 26 ∧
    ((rgfPrediction.emergentDim : ℕ) : RGFReal') = 3 ∧
    -- C neutrino sector
    RGFReal'.ofReal ((Utbm 0 1) ^ 2 / (1 - (Utbm 0 2) ^ 2)) = (1 : RGFReal') / 3 ∧
    RGFReal'.ofReal ((Utbm 1 2) ^ 2 / (1 - (Utbm 0 2) ^ 2)) = (1 : RGFReal') / 2 ∧
    RGFReal'.ofReal (jarlskog Utbm) = (0 : RGFReal') ∧
    -- D gauge-group dimensions
    ((lie_dim_su 5 : ℕ) : RGFReal') = 24 ∧
    ((lie_dim_su 3 + lie_dim_su 2 + lie_dim_u1 : ℕ) : RGFReal') = 12 ∧
    -- E spectral ζ-regularization
    RGFReal'.ofReal (rgfRegularizedSum (-1)).re = -(1 : RGFReal') / 12 ∧
    -- F phase-transition order
    RGFReal'.ofReal ((phaseTransitionOrder 5 : ℚ) : ℝ) = (3 : RGFReal') / 4 ∧
    -- G irrational analytic constants preserving algebraic relations
    rgfSqrt2' ^ 2 = (2 : RGFReal') ∧
    rgfGolden ^ 2 = rgfGolden + 1 ∧
    -- H order constraints
    (0 : RGFReal') < (3 : RGFReal') / 8 ∧ (3 : RGFReal') / 8 < 1 :=
  ⟨weinberg_internal, charge_ratio_internal, params_internal, dim_internal,
    theta12_internal, theta23_internal, jarlskog_internal, su5_dim_internal,
    sm_gauge_dim_internal, zeta_reg_internal, K5_phase_internal, rgfSqrt2'_sq,
    rgfGolden_sq, weinberg_between_zero_one.1, weinberg_between_zero_one.2⟩

end RGF.RealConclusionLayer
