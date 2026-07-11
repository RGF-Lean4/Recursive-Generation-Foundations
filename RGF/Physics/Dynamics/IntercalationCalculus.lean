/-
  RequestProject/IntercalationCalculus.lean

  Original Mathematics III — the recursive intercalation system, a genuine
  extension of classical synchronization theory.

  We couple a pure phase rotation (a `Z₅` cycle) with a threshold reset
  (integrate-and-fire): the intercalation action not only resets the
  "anti-phase tension debt", it also pushes the phase one extra step.
  In classical mathematics each piece exists independently; this *coupling*
  has no off-the-shelf counterpart.

  Parameters: input `δ`, threshold `θ`, rotation rate `r` (all `ℕ`).

  Core theorems:
    1. Conservation law:   `debt n + θ · fires n = n · δ`  (unconditional).
    2. Intercalation shortens the synchronization period (signature phenomenon):
       with `r=1, δ=1, θ=3`, pure `Z₅` rotation has sync period 5, while the
       intercalation-coupled phase reaches zero at step 4 (`naive_period_five`
       confirms the period returns to 5 when intercalation is off).
    3. Long-run asymptotic law: the intercalation frequency tends to `δ/θ`.
-/
import Mathlib

namespace RGF.Intercalation

open Filter Topology

/-- The accumulated "anti-phase tension debt": integrate `δ` each step, fire
    (subtract `θ`) when the threshold is reached. -/
def debt (δ θ : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if θ ≤ debt δ θ n + δ then debt δ θ n + δ - θ else debt δ θ n + δ

/-- The number of intercalation (fire) events up to step `n`. -/
def fires (δ θ : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => fires δ θ n + (if θ ≤ debt δ θ n + δ then 1 else 0)

/-- The coupled phase: pure rotation `r·n` plus one extra step per intercalation,
    taken modulo `5`. -/
def phase (r δ θ : ℕ) (n : ℕ) : ℕ := (r * n + fires δ θ n) % 5

/-- The pure `Z₅` rotation phase, with intercalation switched off. -/
def purePhase (r : ℕ) (n : ℕ) : ℕ := (r * n) % 5

/-! ### 1. Conservation law -/

/--
The exact conservation identity `debt n + θ · fires n = n · δ`.
-/
theorem conservation (δ θ : ℕ) (n : ℕ) :
    debt δ θ n + θ * fires δ θ n = n * δ := by
  induction' n with n ih <;> simp +arith +decide [ * ] at *;
  · exact ⟨ rfl, Or.inr rfl ⟩;
  · by_cases h : θ ≤ debt δ θ n + δ <;> simp_all +decide [ debt, fires ]; all_goals grind

/-! ### 2. Intercalation shortens the synchronization period -/

/--
With `r=1, δ=1, θ=3` the coupled phase reaches zero at step 4.
-/
theorem intercalation_period_four : phase 1 1 3 4 = 0 := by
  decide

/--
... and is nonzero strictly before then.
-/
theorem intercalation_not_before :
    phase 1 1 3 1 ≠ 0 ∧ phase 1 1 3 2 ≠ 0 ∧ phase 1 1 3 3 ≠ 0 := by
  decide

/--
The pure `Z₅` rotation (`r=1`) only returns to zero at step 5.
-/
theorem naive_period_five :
    purePhase 1 5 = 0 ∧
    purePhase 1 1 ≠ 0 ∧ purePhase 1 2 ≠ 0 ∧
    purePhase 1 3 ≠ 0 ∧ purePhase 1 4 ≠ 0 := by
  decide +revert

/-! ### 3. Long-run asymptotic law -/

/--
The debt stays below the threshold when the input is sub-threshold.
-/
theorem debt_lt_threshold (δ θ : ℕ) (hδθ : δ < θ) (n : ℕ) : debt δ θ n < θ := by
  induction' n with n ih <;> simp +decide [ *, debt ];
  · linarith;
  · grind

/--
Long-run intercalation frequency: `fires n / n → δ/θ`.
-/
theorem fires_freq_tendsto (δ θ : ℕ) (hθ : 0 < θ) (hδθ : δ < θ) :
    Tendsto (fun n => (fires δ θ n : ℝ) / n) atTop (𝓝 ((δ : ℝ) / θ)) := by
  -- By the conservation law, we have that $θ * fires δ θ n + debt δ θ n = n * δ$.
  have h_conservation : ∀ n : ℕ, (θ : ℝ) * (fires δ θ n : ℝ) + (debt δ θ n : ℝ) = (n : ℝ) * δ := by
    exact fun n => mod_cast by linarith [ conservation δ θ n ] ;
  -- We'll use the fact that $0 \leq debt δ θ n < θ$ to bound the error term.
  have h_error_bound : ∀ n : ℕ, 0 ≤ (debt δ θ n : ℝ) ∧ (debt δ θ n : ℝ) < θ := by
    exact fun n => ⟨ Nat.cast_nonneg _, mod_cast debt_lt_threshold δ θ hδθ n ⟩;
  -- Using the conservation law and the error bound, we can show that the error term tends to zero.
  have h_error_zero : Filter.Tendsto (fun n => ((debt δ θ n : ℝ) / (θ * n))) Filter.atTop (nhds 0) := by
    refine' squeeze_zero_norm' _ _;
    exacts [ fun n => 1 / ( n : ℝ ), Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_le_div_iff₀ ] <;> nlinarith [ h_error_bound n, show ( n : ℝ ) ≥ 1 by norm_cast, show ( θ : ℝ ) ≥ 1 by norm_cast ] ⟩, tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ];
  convert h_error_zero.const_sub ( δ / θ : ℝ ) |> Filter.Tendsto.congr' _ using 2;
  · ring;
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
    field_simp;
    linarith [ h_conservation n ]

end RGF.Intercalation