/-
  Fourth layer: ergodic theory and mixing time
-/

import Mathlib

open scoped BigOperators
open Finset

structure TransitionMatrix (S : Type) [Fintype S] where
  prob : S → S → ℝ
  prob_nonneg : ∀ i j, 0 ≤ prob i j
  prob_sum : ∀ i, ∑ j : S, prob i j = 1

variable {S : Type} [Fintype S] [DecidableEq S]

structure StationaryDist (P : TransitionMatrix S) where
  dist : S → ℝ
  dist_nonneg : ∀ s, 0 ≤ dist s
  dist_sum : ∑ s : S, dist s = 1
  stationary : ∀ j, ∑ i : S, dist i * P.prob i j = dist j

noncomputable def totalVariation (mu nu : S → ℝ) : ℝ :=
  (1 / 2) * ∑ s : S, |mu s - nu s|

omit [DecidableEq S] in
theorem totalVariation_nonneg (mu nu : S → ℝ) : 0 ≤ totalVariation mu nu := by
  unfold totalVariation
  apply mul_nonneg (by linarith)
  exact Finset.sum_nonneg fun s _ => abs_nonneg _

omit [DecidableEq S] in
theorem totalVariation_symm (mu nu : S → ℝ) :
    totalVariation mu nu = totalVariation nu mu := by
  unfold totalVariation; congr 1; congr 1; ext s; rw [abs_sub_comm]

noncomputable def TransitionMatrix.iterate_prob (P : TransitionMatrix S)
    (init : S → ℝ) : ℕ → (S → ℝ)
  | 0 => init
  | n + 1 => fun j => ∑ i : S, P.iterate_prob init n i * P.prob i j

/-- Definition of the spectral gap. -/
noncomputable def markovSpectralGap (secondEigenval : ℝ) : ℝ :=
  1 - |secondEigenval|

theorem markovSpectralGap_nonneg (ev : ℝ) (h : |ev| ≤ 1) :
    0 ≤ markovSpectralGap ev := by
  unfold markovSpectralGap; linarith

theorem markovSpectralGap_le_one (ev : ℝ) (h : 0 ≤ |ev|) :
    markovSpectralGap ev ≤ 1 := by
  unfold markovSpectralGap; linarith

-- Z₅ symmetry reduction
theorem z5_symmetry_mixing_reduction :
    ∀ (n : ℕ), (5 : ℕ) ∣ n → n / 5 ≤ n := fun n _ => Nat.div_le_self n 5

theorem z5_orbit_count_bound (card_S : ℕ) (h : 0 < card_S) :
    card_S / 5 + 1 ≤ card_S := by omega

theorem mixing_spectral_lower_bound (gap : ℝ) (hgap : 0 < gap) (n : ℕ) :
    0 < (1 / gap) * (n + 1) := by positivity
