import Mathlib

/-!
# Further RCG theorems: phase/stage periodicity, policy asymptotics,
# critical ratio, and super-period synchronization

Self-contained development of a few "recursive-cycle geometry" (RCG) gadgets and
their structural theorems.

* `phase t = Int.fract t` — the normalized phase in `[0,1)` of a unit-period cycle.
* `stageOfPhase t = ⌊5·fract t⌋ + 1` — the ℤ₅ five-stage label `1..5`.
* `policyEffectiveness lam initial n = initial·e^{-λ n}` — geometric decay.
* `criticalRatio κ = 1/(1+κ)` — intercalation critical ratio.
* `lcmList l` — least common multiple of a list of periods (super-period).

## Main results
* `phase_periodic`, `phase_add_nat_period`, `phase_add_int_period`,
  `stage_add_int_period` — integer-period translation invariance.
* `stageOfPhase_surjective` — every stage label `1..5` is realized in `[0,1)`.
* `policyEffectiveness_tendsto_zero`, `policyEffectiveness_tsum` — asymptotics
  and the geometric total `initial/(1-e^{-λ})`.
* `criticalRatio_tendsto_zero` — `κ → ∞ ⇒ 1/(1+κ) → 0`.
* `lcmList_dvd` — each list member divides the super-period `lcmList`.
-/

namespace RCG.Further

open scoped BigOperators

/-- The normalized phase in `[0,1)` of a unit-period cyclic process. -/
noncomputable def phase (t : ℝ) : ℝ := Int.fract t

/-- The ℤ₅ five-stage label `1..5` attached to a phase. -/
noncomputable def stageOfPhase (t : ℝ) : ℤ := ⌊5 * Int.fract t⌋ + 1

/-
Single-period invariance of the phase.
-/
lemma phase_periodic (t : ℝ) : phase (t + 1) = phase t := by
  unfold phase; norm_num;

/-
Natural-number-period invariance of the phase.
-/
lemma phase_add_nat_period (t : ℝ) (n : ℕ) : phase (t + n) = phase t := by
  unfold phase; norm_num [ Int.fract_eq_fract ] ;

/-
Integer-period invariance of the phase (forward or backward).
-/
lemma phase_add_int_period (t : ℝ) (n : ℤ) : phase (t + n) = phase t := by
  unfold phase; norm_num [ Int.fract_eq_fract ] ;

/-
Integer-period invariance of the stage function.
-/
lemma stage_add_int_period (t : ℝ) (n : ℤ) : stageOfPhase (t + n) = stageOfPhase t := by
  unfold stageOfPhase; rw [ Int.fract_add_intCast ] ;

/-
Surjectivity of the five-stage division: every label `s ∈ {1,2,3,4,5}` is
attained by some phase in `[0,1)`.
-/
lemma stageOfPhase_surjective (s : ℤ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ stageOfPhase p = s := by
  interval_cases s <;> simp_all +decide [ stageOfPhase ];
  · exact ⟨ 0, by norm_num ⟩;
  · exact ⟨ 1 / 5, by norm_num ⟩;
  · exact ⟨ 2 / 5, by norm_num ⟩;
  · exact ⟨ 3 / 5, by norm_num ⟩;
  · exact ⟨ 4 / 5, by norm_num ⟩

/-- Policy effectiveness after `n` repetitions: geometric decay. -/
noncomputable def policyEffectiveness (lam initial : ℝ) (n : ℕ) : ℝ :=
  initial * Real.exp (-lam * n)

/-
Policy effectiveness tends to `0` as the number of repetitions grows (`λ>0`).
-/
lemma policyEffectiveness_tendsto_zero (lam initial : ℝ) (hlam : 0 < lam) :
    Filter.Tendsto (fun n => policyEffectiveness lam initial n) Filter.atTop (nhds 0) := by
  unfold policyEffectiveness;
  simpa using tendsto_const_nhds.mul ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| tendsto_natCast_atTop_atTop.const_mul_atTop hlam )

/-
The whole-horizon geometric total `∑ₖ initial·e^{-λk} = initial/(1-e^{-λ})`.
-/
lemma policyEffectiveness_tsum (lam initial : ℝ) (hlam : 0 < lam) :
    ∑' k : ℕ, policyEffectiveness lam initial k = initial / (1 - Real.exp (-lam)) := by
  convert HasSum.tsum_eq ( HasSum.mul_left initial <| hasSum_geometric_of_lt_one ( by positivity ) <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hlam ) using 1 ; ring!;
  unfold policyEffectiveness; congr; ext; rw [ ← Real.exp_nat_mul ] ; ring;

/-- The intercalation critical ratio `1/(1+κ)`. -/
noncomputable def criticalRatio (kappa : ℝ) : ℝ := 1 / (1 + kappa)

/-
As the coupling strength `κ → ∞`, the critical ratio tends to `0`.
-/
lemma criticalRatio_tendsto_zero :
    Filter.Tendsto criticalRatio Filter.atTop (nhds 0) := by
  convert tendsto_const_nhds.div_atTop ( tendsto_const_nhds.add_atTop Filter.tendsto_id ) using 1;
  all_goals infer_instance;

/-- The least common multiple (super-period) of a list of periods. -/
def lcmList (l : List ℕ) : ℕ := l.foldr Nat.lcm 1

/-
Every member period divides the super-period `lcmList`.
-/
lemma lcmList_dvd (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ∣ lcmList l := by
  induction' l with hd tl ih;
  · contradiction;
  · by_cases h : x ∈ tl <;> simp_all +decide [ lcmList ];
    · exact Nat.dvd_trans ih ( Nat.dvd_lcm_right _ _ );
    · exact Nat.dvd_lcm_left _ _

/-- Unified summary of the further RCG theorems. -/
theorem further_theorems_summary (t : ℝ) (n : ℤ) (l : List ℕ) (x : ℕ) (hx : x ∈ l) :
    phase (t + n) = phase t
    ∧ Filter.Tendsto criticalRatio Filter.atTop (nhds 0)
    ∧ x ∣ lcmList l :=
  ⟨phase_add_int_period t n, criticalRatio_tendsto_zero, lcmList_dvd l x hx⟩

end RCG.Further