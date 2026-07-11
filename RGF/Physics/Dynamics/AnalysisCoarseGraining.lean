/-
  Coarse-graining weak-convergence engine (pure analysis).

  This module was lost during an earlier file reorganization (two distinct files were
  both named `CoarseGraining.lean`, one under `Analysis/` and one under `FORS/`, and the
  flattening collapsed them, dropping the `Analysis` one).  It is reconstructed here under
  the unique module name `AnalysisCoarseGraining` while keeping the original namespace
  `RGF.Analysis` and the original public names (`coarseAvg`, `contInt`,
  `coarseGraining_weak_convergence_antitone`) so that the downstream files
  `CoarseGraining.lean` (`RGF.FORS`) and `PropositionC.lean` continue to type-check.

  Mathematical content: for an observable `f` that is antitone on `[0,∞)`, the left
  Riemann average over `[0,a]` with `n` equal cells converges to the interval integral
  `∫₀ᵃ f`.  The proof is the classical squeeze between the left and right Riemann sums,
  whose difference is `(a/n)·(f 0 - f a) → 0`.
-/

import Mathlib

open Filter Topology intervalIntegral MeasureTheory

namespace RGF.Analysis

/-- The coarse-grained (left Riemann) average of `f` over `[0,a]` with `n` equal cells. -/
noncomputable def coarseAvg (f : ℝ → ℝ) (a : ℝ) (n : ℕ) : ℝ :=
  (a / n) * ∑ i ∈ Finset.range n, f (a * i / n)

/-- The continuous integral of `f` over `[0,a]`. -/
noncomputable def contInt (f : ℝ → ℝ) (a : ℝ) : ℝ := ∫ s in (0:ℝ)..a, f s

/-
**Coarse-graining weak convergence for antitone observables.**
    If `f` is antitone on `[0,∞)` and `a > 0`, the left Riemann average converges to the
    interval integral.
-/
theorem coarseGraining_weak_convergence_antitone {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Ici 0)) :
    Tendsto (fun n => coarseAvg f a n) atTop (𝓝 (contInt f a)) := by
  -- By definition of $coarseAvg$, we have
  have h_coarseAvg : ∀ n ≥ 1, (a / n) * ∑ i ∈ Finset.range n, f (a * i / n) ≤ (contInt f a) + (a / n) * (f 0 - f a) := by
    -- By definition of $contInt$, we have
    intro n hn
    have h_contInt : ∑ i ∈ Finset.range n, ∫ s in (a * i / n).. (a * (i + 1) / n), f s ≥ ∑ i ∈ Finset.range n, (a / n) * f (a * (i + 1) / n) := by
      have h_integral_bound : ∀ i ∈ Finset.range n, ∫ s in (a * i / n).. (a * (i + 1) / n), f s ≥ (a / n) * f (a * (i + 1) / n) := by
        -- Since $f$ is antitone on $[0, a]$, we have $f(s) \geq f(a * (i + 1) / n)$ for all $s \in [a * i / n, a * (i + 1) / n]$.
        have h_antitone : ∀ i ∈ Finset.range n, ∀ s ∈ Set.Icc (a * i / n) (a * (i + 1) / n), f s ≥ f (a * (i + 1) / n) := by
          exact fun i hi s hs => hf ( show 0 ≤ s by exact le_trans ( by positivity ) hs.1 ) ( show 0 ≤ a * ( i + 1 ) / n by positivity ) hs.2;
        intro i hi; rw [ intervalIntegral.integral_of_le ( by gcongr ; linarith ) ] ; refine' le_trans _ ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun x hx => h_antitone i hi x <| Set.Ioc_subset_Icc_self hx ) ; ring_nf; norm_num [ ha.ne', show n ≠ 0 by linarith ] ;
        · rw [ max_eq_left ( by positivity ) ];
        · norm_num;
        · exact ( hf.mono ( Set.Icc_subset_Ici_self.trans ( Set.Ici_subset_Ici.2 <| by positivity ) ) ) |> fun h => h.integrableOn_isCompact ( CompactIccSpace.isCompact_Icc ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
      exact Finset.sum_le_sum h_integral_bound;
    -- By definition of $contInt$, we can rewrite the integral as a sum of integrals over subintervals.
    have h_contInt_sum : ∑ i ∈ Finset.range n, ∫ s in (a * i / n).. (a * (i + 1) / n), f s = ∫ s in (0:ℝ)..a, f s := by
      convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num [ mul_div_cancel₀, show n ≠ 0 by linarith ];
      intro k hk; apply_rules [ AntitoneOn.intervalIntegrable, hf.mono ];
      exact fun x hx => by rw [ Set.uIcc_of_le ( by gcongr ; linarith ) ] at hx; exact hx.1.trans' ( by positivity ) ;
    have := Finset.sum_range_sub ( fun x => a / n * f ( a * x / n ) ) n; simp_all +decide [ mul_div_assoc, Finset.mul_sum _ _ _ ] ;
    by_cases hn : n = 0 <;> simp_all +decide [ mul_sub ] ; linarith!;
  -- Similarly, by definition of $coarseAvg$, we have
  have h_coarseAvg' : ∀ n ≥ 1, (contInt f a) ≤ (a / n) * ∑ i ∈ Finset.range n, f (a * i / n) := by
    -- By definition of $contInt$, we have
    have h_contInt : ∀ n ≥ 1, (contInt f a) = ∑ i ∈ Finset.range n, ∫ s in (a * i / n).. (a * (i + 1) / n), f s := by
      intro n hn;
      symm;
      convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
      · rw [ mul_div_cancel_right₀ _ ( by positivity ) ] ; rfl;
      · intro k hk; apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
        exact ( hf.mono ( Set.Icc_subset_Ici_self.trans ( Set.Ici_subset_Ici.2 <| by positivity ) ) ) |> fun h => h.integrableOn_isCompact ( CompactIccSpace.isCompact_Icc );
    -- By definition of $f$ being antitone, we have
    have h_antitone : ∀ n ≥ 1, ∀ i ∈ Finset.range n, ∫ s in (a * i / n).. (a * (i + 1) / n), f s ≤ (a / n) * f (a * i / n) := by
      intros n hn i hi
      have h_integral_le : ∫ s in (a * i / n).. (a * (i + 1) / n), f s ≤ ∫ s in (a * i / n).. (a * (i + 1) / n), f (a * i / n) := by
        apply_rules [ intervalIntegral.integral_mono_on ];
        · bound;
        · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
          exact ( hf.mono ( Set.Icc_subset_Ici_self.trans ( Set.Ici_subset_Ici.2 <| by positivity ) ) ) |> fun h => h.integrableOn_isCompact ( CompactIccSpace.isCompact_Icc );
        · norm_num;
        · exact fun x hx => hf ( show 0 ≤ a * i / n by positivity ) ( show 0 ≤ x by exact le_trans ( by positivity ) hx.1 ) hx.1;
      convert h_integral_le using 1 ; norm_num ; ring;
      norm_num;
    exact fun n hn => by rw [ h_contInt n hn, Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => h_antitone n hn i hi;
  -- Using the bounds obtained, we can apply the squeeze theorem.
  have h_squeeze : Filter.Tendsto (fun n : ℕ => (a / n) * (f 0 - f a)) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul ( tendsto_inv_atTop_nhds_zero_nat ) |> Filter.Tendsto.mul_const ( f 0 - f a );
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ( by simpa using h_squeeze.const_add ( contInt f a ) ) ( Filter.eventually_atTop.mpr ⟨ 1, fun n hn => h_coarseAvg' n hn ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 1, fun n hn => h_coarseAvg n hn ⟩ )

end RGF.Analysis