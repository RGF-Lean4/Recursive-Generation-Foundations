/-
  RGF/Phenomenology/StandardModel/NeutrinoSigmaDeviation.lean

  Direction V — **quantitative statistical honesty** for the leading-order neutrino
  mixing-angle predictions of `NeutrinoPrediction.lean`.

  `NeutrinoPrediction.lean` proves the *exact algebraic* tribimaximal values
    `sin²θ₁₂ = 1/3`,  `sin²θ₂₃ = 1/2`,  `sin²θ₁₃ = 0`
  and labels their physical standing verbally ("falsified", "good leading-order
  approximation", ...).  A recurring, correct critique is that a *verbal* label such
  as "good leading-order approximation" is not enough: one must state **how many
  standard deviations** each prediction sits away from the current global fit, so that
  "leading-order approximation, higher-order corrections pending" cannot silently
  absorb an arbitrary tension.

  This file makes that quantitative.  All numbers are rationals (predicted value,
  experimental central value, 1σ uncertainty), and every claim is a `norm_num`-checked
  inequality — a machine-backed statement of the tension in units of σ.

  ## Experimental inputs (global fit, Normal Ordering)

  The central values and 1σ uncertainties below are *experimental inputs*, of the
  order of the current global three-flavour fits (NuFIT-class analyses, PDG neutrino
  review), rounded to the precision that matters for a σ-level statement:

  * solar        `sin²θ₁₂ = 0.307 ± 0.012`
  * reactor      `sin²θ₁₃ = 0.0220 ± 0.0007`
  * atmospheric  `sin²θ₂₃`: octant-ambiguous; 3σ allowed interval `≈ [0.41, 0.62]`.

  These are inputs from experiment, **not** framework outputs; the point of the file
  is precisely to compare framework outputs against them numerically.

  ## Graded, quantified verdict (each line is a proved theorem)

  * **reactor `sin²θ₁₃ = 0`** — deviates by **more than 30σ**: definitively falsified,
    not a "small correction" (`reactor_falsified_over_30_sigma`).  This upgrades the
    qualitative `tribimaximal_theta13_falsified` to a quantitative statement.
  * **solar `sin²θ₁₂ = 1/3`** — sits at a **mild `2σ–3σ` tension** (`solar_tension_2_to_3_sigma`):
    a genuine but modest discrepancy, honestly *not* negligible, plausibly absorbable
    by known higher-order corrections of the right size.
  * **atmospheric `sin²θ₂₃ = 1/2`** — lies **inside the 3σ allowed interval**
    (`atmospheric_within_3sigma`): maximal mixing is consistent with data, the
    framework's most defensible mixing-angle statement.

  The contrast is the whole point: the three tribimaximal angles are *not*
  interchangeable "approximations".  One is excluded at >30σ, one is a ~2σ tension,
  and one is fine — and now that grading is a set of machine-checked numbers rather
  than adjectives.
-/
import Mathlib

namespace RGF.NeutrinoSigma

/-! ## 1. Deviation in units of σ -/

/-- Tension of a prediction against an experimental central value, in units of the
experimental 1σ uncertainty: `|pred − exp| / σ`. -/
def nSigma (pred exp sigma : ℚ) : ℚ := |pred - exp| / sigma

/-! ## 2. Experimental inputs (global-fit central values and 1σ, Normal Ordering) -/

/-- Solar angle central value `sin²θ₁₂ ≈ 0.307`. -/
def solarExp : ℚ := 307 / 1000
/-- Solar angle 1σ uncertainty `≈ 0.012`. -/
def solarSigma : ℚ := 12 / 1000

/-- Reactor angle central value `sin²θ₁₃ ≈ 0.0220`. -/
def reactorExp : ℚ := 220 / 10000
/-- Reactor angle 1σ uncertainty `≈ 0.0007`. -/
def reactorSigma : ℚ := 7 / 10000

/-- Atmospheric angle 3σ allowed interval, lower end `≈ 0.41`. -/
def atmLow : ℚ := 41 / 100
/-- Atmospheric angle 3σ allowed interval, upper end `≈ 0.62`. -/
def atmHigh : ℚ := 62 / 100

/-! ## 3. Framework (tribimaximal) predictions, as rationals -/

/-- Predicted `sin²θ₁₂ = 1/3` (matches `RGF.Neutrino.sinSq_theta12`). -/
def solarPred : ℚ := 1 / 3
/-- Predicted `sin²θ₂₃ = 1/2` (matches `RGF.Neutrino.sinSq_theta23`). -/
def atmPred : ℚ := 1 / 2
/-- Predicted `sin²θ₁₃ = 0` (matches `RGF.Neutrino.sinSq_theta13`). -/
def reactorPred : ℚ := 0

/-! ## 4. Quantified verdicts -/

/-- **Reactor: falsified at more than 30σ.**  The tribimaximal value `sin²θ₁₃ = 0`
is not a small correction away from the measured nonzero value: it is more than
thirty standard deviations off.  This is the quantitative form of
`RGF.Neutrino.tribimaximal_theta13_falsified`. -/
theorem reactor_falsified_over_30_sigma :
    nSigma reactorPred reactorExp reactorSigma > 30 := by
  unfold nSigma reactorPred reactorExp reactorSigma; norm_num

/-- **Solar: a mild `2σ–3σ` tension.**  `sin²θ₁₂ = 1/3` sits between two and three
standard deviations from the global-fit central value — a real but modest
discrepancy, honestly recorded rather than waved away as "approximate". -/
theorem solar_tension_2_to_3_sigma :
    2 < nSigma solarPred solarExp solarSigma ∧
      nSigma solarPred solarExp solarSigma < 3 := by
  unfold nSigma solarPred solarExp solarSigma
  constructor <;> norm_num

/-- **Atmospheric: consistent within 3σ.**  Maximal mixing `sin²θ₂₃ = 1/2` lies inside
the 3σ allowed interval `[0.41, 0.62]`, independently of the (currently unresolved)
octant.  This is the framework's most defensible mixing-angle statement. -/
theorem atmospheric_within_3sigma :
    atmLow ≤ atmPred ∧ atmPred ≤ atmHigh := by
  unfold atmLow atmPred atmHigh
  constructor <;> norm_num

/-- **The three angles are not interchangeable.**  A single statement collecting the
graded, quantified verdict: reactor is excluded at >30σ, solar is a 2σ–3σ tension,
atmospheric is consistent within 3σ.  "Leading-order approximation" means three very
different things here, and each is now a machine-checked number. -/
theorem quantified_neutrino_verdict :
    nSigma reactorPred reactorExp reactorSigma > 30 ∧
      (2 < nSigma solarPred solarExp solarSigma ∧
        nSigma solarPred solarExp solarSigma < 3) ∧
      (atmLow ≤ atmPred ∧ atmPred ≤ atmHigh) :=
  ⟨reactor_falsified_over_30_sigma, solar_tension_2_to_3_sigma, atmospheric_within_3sigma⟩

end RGF.NeutrinoSigma
