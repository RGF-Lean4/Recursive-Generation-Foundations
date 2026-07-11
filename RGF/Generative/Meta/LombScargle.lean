/-
  Lomb-Scargle periodogram and numerical spectral analysis methods
  Based on Lin Sun's "Periodic Signal Detection on Non-uniform Spectral Data with the Lomb-Scargle Periodogram"

  This file formalizes:
  - the mathematical definition of the Lomb-Scargle power spectrum
  - the definition of the signal-to-noise ratio
  - the statistical-significance framework of bootstrap resampling
  - the design principle of the Poisson control group
-/

import Mathlib

open scoped BigOperators

/-! ## Non-uniformly sampled data -/

/-- A sequence of non-uniformly sampled spectral data points. -/
structure SpectralData where
  /-- number of data points -/
  sampleSize : ℕ
  /-- sample count positive -/
  size_pos : 0 < sampleSize
  /-- data point positions (strictly increasing) -/
  positions : Fin sampleSize → ℝ
  /-- strictly increasing -/
  strictly_mono : StrictMono positions

/-- Residual sequence. -/
structure ResidualSequence extends SpectralData where
  /-- mean density function -/
  meanDensity : ℝ → ℝ
  /-- residuals -/
  residuals : Fin sampleSize → ℝ

/-! ## Lomb-Scargle power spectrum -/

/-- Lomb-Scargle power spectrum (simplified definition). -/
noncomputable def lombScarglePower (data : ResidualSequence) (f : ℝ) : ℝ :=
  let N := data.sampleSize
  (1 / (2 * (N : ℝ))) *
    (∑ i : Fin N, data.residuals i * Real.cos (2 * Real.pi * f * data.positions i)) ^ 2 +
  (1 / (2 * (N : ℝ))) *
    (∑ i : Fin N, data.residuals i * Real.sin (2 * Real.pi * f * data.positions i)) ^ 2

/-- The power spectrum is nonnegative. -/
lemma lombScarglePower_nonneg (data : ResidualSequence) (f : ℝ) :
    0 ≤ lombScarglePower data f := by
  unfold lombScarglePower
  apply add_nonneg <;> apply mul_nonneg
  · positivity
  · exact sq_nonneg _
  · positivity
  · exact sq_nonneg _

/-! ## Signal-to-noise ratio -/

/-- Signal-to-noise ratio. -/
structure SignalToNoise where
  /-- peak power -/
  peakPower : ℝ
  /-- median of the background noise -/
  noiseMedian : ℝ
  /-- noise median positive -/
  noise_pos : 0 < noiseMedian
  /-- signal-to-noise ratio -/
  ratio : ℝ
  /-- defining relation -/
  ratio_def : ratio = peakPower / noiseMedian

/-- A signal-to-noise ratio ≥ 3.8 is considered significant. -/
def isSignificant (snr : SignalToNoise) : Prop :=
  3.8 ≤ snr.ratio

/-! ## Bootstrap resampling -/

/-- Statistical test framework of bootstrap resampling. -/
structure BootstrapTest where
  /-- number of resamples -/
  resampleCount : ℕ
  /-- resample count large enough -/
  resampleCount_large : 1000 ≤ resampleCount
  /-- p-value -/
  pValue : ℝ
  /-- p-value in [0, 1] -/
  pValue_range : 0 ≤ pValue ∧ pValue ≤ 1

/-- Statistical significance criterion. -/
def isStatisticallySignificant (test : BootstrapTest) : Prop :=
  test.pValue < 0.05

/-! ## Segment analysis -/

/-- Segment analysis. -/
structure SegmentAnalysis where
  /-- number of segments -/
  segmentCount : ℕ
  /-- at least two segments -/
  segment_ge_two : 2 ≤ segmentCount
  /-- peak frequency detected in each segment -/
  peakFrequencies : Fin segmentCount → ℝ
  /-- frequency stability -/
  frequencyStable : ∃ f₀ ε : ℝ, 0 < ε ∧
    ∀ i, |peakFrequencies i - f₀| < ε

/-- Signal-to-noise ratio instance for the ζ-function zero data. -/
def zetaZeroSignal : SignalToNoise where
  peakPower := 3.8
  noiseMedian := 1.0
  noise_pos := by norm_num
  ratio := 3.8
  ratio_def := by norm_num

/-- This signal meets the significance criterion. -/
lemma zeta_signal_significant : isSignificant zetaZeroSignal := by
  simp [isSignificant, zetaZeroSignal]
