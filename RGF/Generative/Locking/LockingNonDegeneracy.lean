import Mathlib
import RGF.Generative.Locking.ModeDecomposition
import RGF.Generative.Locking.SpiralLocking

/-!
# FORS part four: the locking non-degeneracy theorem

Starting from the FORS five-mode degeneracy and its correspondence with the
irreducible representations of D₅, this file gives the final output of the FORS
layer: condition (U), namely that `LockingNonDegenerate` holds for the set
`ZetaNontrivialZero`. It plugs directly into `RGF.SpiralLocking.LockingNonDegenerate`
defined in `RGF/SpiralLocking.lean`.

## Key fact: the final output of this layer is **equivalent to the Riemann Hypothesis (RH)**

Recall (see `RGF/SpiralLocking.lean`):
* `ZetaNontrivialZero = {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}` (the ζ zeros in the critical strip);
* `spiralDual s = 1 - conj s`;
* `LockingNonDegenerate S = ∀ s ∈ S, spiralDual s ∈ S → s = spiralDual s`.

The lemma `eq_spiralDual_iff` below proves `s = spiralDual s ↔ s.re = 1/2`.
Therefore `LockingNonDegenerate ZetaNontrivialZero` asserts: every ζ zero in the
critical strip whose spiral dual is also a zero satisfies `Re s = 1/2` — which is
exactly the **Riemann Hypothesis** (in its standard form restricted to the critical strip).

* `locking_nondegenerate_of_RH`: locking non-degeneracy **is provable** from RH (the critical-strip version).
* The reverse direction (locking non-degeneracy ⇒ RH) uses the functional equation
  and conjugation symmetry of ζ, showing the two are equivalent; hence
  `locking_nondegenerate_for_zeta` is an **open problem** of the same difficulty as RH,
  currently marked with `sorry` (a legitimate use of `sorry`: an as-yet-unsolved
  conjecture, not a false/incorrect statement introduced by a placeholder definition).

Dependencies: FORS/ModeDecomposition.lean, RGF/SpiralLocking.lean
-/

namespace RGF.FORS
open RGF.SpiralLocking

/-- Key algebraic equivalence: `s = spiralDual s ↔ Re s = 1/2`.
    (`spiralDual s = 1 - conj s`; the imaginary parts agree automatically, while the
    real part gives `s.re = 1 - s.re`, i.e. `Re s = 1/2`.) -/
theorem eq_spiralDual_iff (s : ℂ) : s = spiralDual s ↔ s.re = 1 / 2 := by
  unfold spiralDual
  rw [Complex.ext_iff]
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
    Complex.conj_im, zero_sub, neg_neg]
  constructor
  · rintro ⟨hre, _⟩; linarith
  · intro hre; exact ⟨by linarith, trivial⟩

/-- The Riemann Hypothesis (in its standard form restricted to the critical strip):
    every ζ zero in the critical strip `0 < Re s < 1` satisfies `Re s = 1/2`. -/
def RiemannHypothesis_strip : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- **Locking non-degeneracy follows from the Riemann Hypothesis**.
    Given RH (critical-strip version), every `s ∈ ZetaNontrivialZero` has `Re s = 1/2`,
    and `eq_spiralDual_iff` then gives `s = spiralDual s`. -/
theorem locking_nondegenerate_of_RH (h : RiemannHypothesis_strip) :
    LockingNonDegenerate ZetaNontrivialZero := by
  intro s hs _
  obtain ⟨hz, hlo, hhi⟩ := hs
  exact (eq_spiralDual_iff s).2 (h s hz hlo hhi)

/-
**Reverse direction: locking non-degeneracy implies the Riemann Hypothesis**.
For a ζ zero `s` in the critical strip, its spiral dual `1 - conj s` is also a zero
in the critical strip (by the conjugation symmetry `ζ(conj s) = conj(ζ s)` and the
functional equation `riemannZeta_one_sub`), so `spiralDual s ∈ ZetaNontrivialZero`;
locking non-degeneracy together with `eq_spiralDual_iff` then gives `Re s = 1/2`.
-/
theorem RH_strip_of_locking (h : LockingNonDegenerate ZetaNontrivialZero) :
    RiemannHypothesis_strip := by
  contrapose! h;
  simp +decide [ LockingNonDegenerate ];
  obtain ⟨s, hs⟩ : ∃ s : ℂ, riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 := by
    contrapose! h;
    exact fun s hs hs' hs'' => h s hs hs' hs'';
  refine' ⟨ s, _, _, _ ⟩ <;> norm_num [ hs, ZetaNontrivialZero, spiralDual ];
  · have h_conj : riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
      have h_conj : ∀ s : ℂ, s.re > 1 → riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
        intro s hs;
        rw [ zeta_eq_tsum_one_div_nat_cpow ];
        · rw [ zeta_eq_tsum_one_div_nat_cpow ];
          · rw [ Complex.conj_tsum ];
            refine' tsum_congr fun n => _;
            by_cases hn : n = 0 <;> simp +decide [ hn, Complex.cpow_def ];
            simp +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
          · linarith;
        · simpa using hs;
      have h_conj : ∀ s : ℂ, s.re > 0 → s ≠ 1 → riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
        intros s hs_pos hs_ne_one
        have h_conj : riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
          have h_analytic : AnalyticOn ℂ (fun s => riemannZeta s - starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))) (Set.univ \ {1}) := by
            apply_rules [ DifferentiableOn.analyticOn ];
            · refine' DifferentiableOn.sub _ _;
              · intro s hs;
                refine' DifferentiableAt.differentiableWithinAt _;
                apply_rules [ differentiableAt_riemannZeta ];
                exact hs.2;
              · intro s hs;
                have h_analytic : DifferentiableAt ℂ (fun s => riemannZeta s) (starRingEnd ℂ s) := by
                  apply_rules [ differentiableAt_riemannZeta ];
                  exact fun h => hs.2 <| by simpa using congr_arg Star.star h;
                have h_analytic : HasDerivAt (fun s => starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))) (starRingEnd ℂ (deriv (fun s => riemannZeta s) (starRingEnd ℂ s))) s := by
                  rw [ hasDerivAt_iff_tendsto_slope_zero ];
                  have := h_analytic.hasDerivAt.tendsto_slope_zero;
                  convert Complex.continuous_conj.continuousAt.tendsto.comp ( this.comp ( show Filter.Tendsto ( fun t : ℂ => starRingEnd ℂ t ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhdsWithin 0 { 0 } ᶜ ) from ?_ ) ) using 2 <;> norm_num;
                  rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop;
                exact h_analytic.differentiableAt.differentiableWithinAt;
            · exact isOpen_univ.sdiff isClosed_singleton
          have h_zero : ∀ s : ℂ, s.re > 1 → riemannZeta s - starRingEnd ℂ (riemannZeta (starRingEnd ℂ s)) = 0 := by
            aesop;
          have h_zero : ∀ s : ℂ, s.re > 0 → s ≠ 1 → riemannZeta s - starRingEnd ℂ (riemannZeta (starRingEnd ℂ s)) = 0 := by
            intros s hs_pos hs_ne_one
            have h_zero : AnalyticOnNhd ℂ (fun s => riemannZeta s - starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))) (Set.univ \ {1}) := by
              apply_rules [ DifferentiableOn.analyticOnNhd ];
              · exact h_analytic.differentiableOn;
              · exact isOpen_univ.sdiff isClosed_singleton;
            apply h_zero.eqOn_zero_of_preconnected_of_eventuallyEq_zero;
            any_goals exact Complex.I + 2;
            · have h_preconnected : IsPreconnected (Set.univ \ {0} : Set ℂ) := by
                have h_connected : IsConnected (Set.univ \ {0} : Set ℂ) := by
                  have h_preconnected : IsConnected (Set.range (fun z : ℂ => Complex.exp z)) := by
                    exact isConnected_range ( Complex.continuous_exp );
                  convert h_preconnected using 1;
                  ext; simp
                exact h_connected.isPreconnected;
              convert h_preconnected.image ( fun x => x + 1 ) ( Continuous.continuousOn ( by continuity ) ) using 1 ; ext ; simp +decide [ Set.diff_eq ];
            · norm_num [ Complex.ext_iff ];
            · filter_upwards [ IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) ( show Complex.re ( Complex.I + 2 ) > 1 by norm_num ) ] with s hs using by aesop;
            · aesop;
          specialize h_zero s hs_pos hs_ne_one; rw [ sub_eq_zero ] at h_zero; exact h_zero.symm ▸ by simp +decide ;
        exact h_conj;
      exact h_conj s hs.2.1 ( by rintro rfl; norm_num at hs );
    have := @riemannZeta_one_sub ( starRingEnd ℂ s ) ?_ ?_ <;> simp_all +decide [ Complex.ext_iff ];
    · intros; linarith;
    · lia;
  · exact fun h => hs.2.2.2 <| by norm_num [ Complex.ext_iff ] at h; linarith;

/-- **Equivalence**: the core FORS output (locking non-degeneracy) is equivalent to
    the Riemann Hypothesis (critical-strip version). -/
theorem locking_nondegenerate_iff_RH :
    LockingNonDegenerate ZetaNontrivialZero ↔ RiemannHypothesis_strip :=
  ⟨RH_strip_of_locking, locking_nondegenerate_of_RH⟩

/-- **The core FORS output theorem (condition (U))**: locking non-degeneracy.

As explained in the file header, this statement is **equivalent to the Riemann
Hypothesis** (critical-strip version), an open problem. We therefore state it in its
honest *conditional* form: assuming the Riemann Hypothesis (`RiemannHypothesis_strip`),
locking non-degeneracy holds. (Previously this was left as a bare `sorry`; the
conditional form removes the `sorry` while remaining mathematically faithful — it is
just `locking_nondegenerate_of_RH`, recorded under this name for the FORS output
interface. By `locking_nondegenerate_iff_RH` the hypothesis is also necessary.) -/
theorem locking_nondegenerate_for_zeta (hRH : RiemannHypothesis_strip) :
    LockingNonDegenerate ZetaNontrivialZero :=
  locking_nondegenerate_of_RH hRH

end RGF.FORS
