/-
  RGF/RenormalizationGroup.lean

  Direction II — Wilsonian renormalization-group flow and running couplings.

  A `sorry`-free development bridging the RGF high-energy algebraic prediction
  `sin²θ_W = 3/8` (locked at the grand-unification scale) with the low-energy
  electroweak value `≈ 0.231` measured at the `Z` pole, via the one-loop
  renormalization-group (RG) running of the gauge couplings.

  Contents (namespace `RGF.RG`):

  * **One-loop running.**  A `RunningCoupling` records the inverse-square coupling
    `u₀ = 1/g²` at a reference scale together with the one-loop slope `c`.  The
    inverse square runs linearly in `t = ln μ` (`invSq`), and the coupling square
    `α = g²` therefore satisfies the one-loop β-function ODE
    `dα/dt = c·α²` (`alpha_beta_ode`) — the closed-form solution of the
    Picard–Lindelöf machinery of `ConstructiveODE.lean`.

  * **RG semigroup.**  `flow s` shifts the reference scale by `s`; it satisfies the
    one-parameter semigroup laws `flow 0 = id` (`flow_zero`) and
    `flow s₂ ∘ flow s₁ = flow (s₁+s₂)` (`flow_add`).

  * **Grand unification.**  Two couplings with distinct one-loop slopes cross at a
    unique scale (`unification_scale_unique`), and any two inverse-square couplings
    asymptotically converge as `t → t★` (`invSq_diff_tendsto`).

  * **Weinberg angle at unification.**  Under the `SU(5)` normalization
    `g_Y² = (3/5) g₁²` together with unification `g₁ = g₂`, the weak mixing angle
    is exactly `sin²θ_W = 3/8` (`weinberg_at_unification`), and this is the
    `t → t★` limit of the running mixing angle (`weinberg_tendsto`).
-/

import Mathlib

open scoped Topology
open Filter

namespace RGF.RG

/-! ## 1. One-loop running couplings -/

/-- A one-loop running coupling: the inverse square `u₀ = 1/g²` at the reference
    scale `t = 0`, together with the one-loop slope `c` (so that `1/g²` runs
    linearly in `t = ln μ`). -/
structure RunningCoupling where
  /-- Inverse square coupling `1/g²` at the reference scale. -/
  u0 : ℝ
  /-- One-loop slope: `d(1/g²)/dt = -c`. -/
  c : ℝ

namespace RunningCoupling

/-- The inverse square coupling `1/g²(t)` at RG-time `t = ln μ`. -/
def invSq (rc : RunningCoupling) (t : ℝ) : ℝ := rc.u0 - rc.c * t

/-- The running coupling *square* `α(t) = g²(t) = 1/(u₀ - c·t)`. -/
noncomputable def alpha (rc : RunningCoupling) (t : ℝ) : ℝ := 1 / rc.invSq t

@[simp] theorem invSq_zero (rc : RunningCoupling) : rc.invSq 0 = rc.u0 := by
  simp [invSq]

/-- The inverse square coupling runs linearly with constant slope `-c`. -/
theorem invSq_hasDerivAt (rc : RunningCoupling) (t : ℝ) :
    HasDerivAt rc.invSq (-rc.c) t := by
  have : HasDerivAt rc.invSq (0 - rc.c * 1) t :=
    (hasDerivAt_const _ _).sub ((hasDerivAt_id t).const_mul rc.c)
  simpa [invSq] using this

/-
**One-loop β-function ODE.** The coupling square `α = g²` satisfies
    `dα/dt = c·α²`, the closed-form one-loop renormalization-group equation.
-/
theorem alpha_beta_ode (rc : RunningCoupling) (t : ℝ) (ht : rc.invSq t ≠ 0) :
    HasDerivAt rc.alpha (rc.c * (rc.alpha t) ^ 2) t := by
  convert HasDerivAt.div ( hasDerivAt_const _ _ ) ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id t ) ) ) ht using 1 ; norm_num ; ring;
  unfold RunningCoupling.alpha RunningCoupling.invSq; ring;
  rw [ inv_pow ] ; ring;

end RunningCoupling

/-! ## 2. The renormalization-group semigroup -/

/-- The RG flow `flow s`: shift the reference scale by `s`, i.e. re-expand the
    running coupling about the new base point `t = s`. -/
def flow (s : ℝ) (rc : RunningCoupling) : RunningCoupling :=
  ⟨rc.invSq s, rc.c⟩

/-- The flow is defined so that evaluating the flowed coupling at `t` equals
    evaluating the original coupling at `s + t`. -/
theorem flow_invSq (s : ℝ) (rc : RunningCoupling) (t : ℝ) :
    (flow s rc).invSq t = rc.invSq (s + t) := by
  simp [flow, RunningCoupling.invSq]; ring

/-- Identity element of the RG semigroup. -/
@[simp] theorem flow_zero (rc : RunningCoupling) : flow 0 rc = rc := by
  simp [flow, RunningCoupling.invSq]

/-- **Semigroup law** of the renormalization-group flow. -/
theorem flow_add (s₁ s₂ : ℝ) (rc : RunningCoupling) :
    flow s₂ (flow s₁ rc) = flow (s₁ + s₂) rc := by
  simp only [flow, RunningCoupling.invSq, sub_sub]
  norm_num
  ring

/-! ## 3. Grand unification: convergence of the running couplings -/

/-
Two running couplings with distinct one-loop slopes cross at a unique scale
    `t★` where their inverse-square couplings agree.
-/
theorem unification_scale_unique (rc₁ rc₂ : RunningCoupling) (hslope : rc₁.c ≠ rc₂.c) :
    ∃! t : ℝ, rc₁.invSq t = rc₂.invSq t := by
  refine' ⟨ ( rc₂.u0 - rc₁.u0 ) / ( rc₂.c - rc₁.c ), _, _ ⟩ <;> simp_all +decide [RunningCoupling.invSq]; all_goals grind +extAll

/-
**Asymptotic unification.** As `t → t★` (any common scale), the difference of
    the two inverse-square couplings tends to `0`.
-/
theorem invSq_diff_tendsto (rc₁ rc₂ : RunningCoupling) (tstar : ℝ)
    (hstar : rc₁.invSq tstar = rc₂.invSq tstar) :
    Tendsto (fun t => rc₁.invSq t - rc₂.invSq t) (𝓝 tstar) (𝓝 0) := by
  convert Filter.Tendsto.sub ( rc₁.invSq_hasDerivAt tstar |> HasDerivAt.continuousAt ) ( rc₂.invSq_hasDerivAt tstar |> HasDerivAt.continuousAt ) using 1 ; aesop

/-! ## 4. The Weinberg angle at grand unification -/

/-- The weak mixing angle `sin²θ_W = g_Y² / (g₂² + g_Y²)` written in terms of the
    inverse-square couplings `u₂ = 1/g₂²`, `u_Y = 1/g_Y²`. -/
noncomputable def sinSqWeinberg (u2 uY : ℝ) : ℝ :=
  (1 / uY) / (1 / u2 + 1 / uY)

/-
**Weinberg angle at grand unification.** With the `SU(5)` normalization
    `g_Y² = (3/5) g₁²` (equivalently `u_Y = (5/3) u₁`) and unification `g₁ = g₂`
    (equivalently `u₁ = u₂`), the weak mixing angle is exactly `3/8`.
-/
theorem weinberg_at_unification (u1 u2 uY : ℝ)
    (hu1 : 0 < u1) (hunif : u1 = u2) (hnorm : uY = (5/3) * u1) :
    sinSqWeinberg u2 uY = 3 / 8 := by
  unfold sinSqWeinberg; subst_vars; ring_nf; norm_num [ hu1.ne' ] ;

/-
**Running Weinberg angle limit.** If the `SU(5)`-normalized couplings unify at
    `t★` (`u₁(t★) = u₂(t★)` and `u_Y = (5/3)u₁` throughout), then the running
    mixing angle tends to `3/8` as `t → t★`.
-/
theorem weinberg_tendsto (rc1 rc2 rcY : RunningCoupling) (tstar : ℝ)
    (hpos : 0 < rc1.invSq tstar)
    (hunif : rc1.invSq tstar = rc2.invSq tstar)
    (hnorm : ∀ t, rcY.invSq t = (5/3) * rc1.invSq t) :
    Tendsto (fun t => sinSqWeinberg (rc2.invSq t) (rcY.invSq t)) (𝓝 tstar) (𝓝 (3/8)) := by
  -- By step 1, the value at tstar is 3/8.
  have h_val : (sinSqWeinberg (rc2.invSq tstar) (rcY.invSq tstar)) = 3 / 8 := by
    convert weinberg_at_unification ( rc1.invSq tstar ) ( rc2.invSq tstar ) ( rcY.invSq tstar ) hpos hunif ( hnorm tstar ) using 1
  generalize_proofs at *; (
  -- By step 2, the map `g t := sinSqWeinberg (rc2.invSq t) (rcY.invSq t)` is continuous at `tstar`.
  have h_cont : ContinuousAt (fun t => sinSqWeinberg (rc2.invSq t) (rcY.invSq t)) tstar := by
    refine' ContinuousAt.div _ _ _ <;> norm_num [ sinSqWeinberg ];
    · exact ContinuousAt.inv₀ ( show ContinuousAt ( fun t => rcY.invSq t ) tstar from by rw [ show ( fun t => rcY.invSq t ) = fun t => 5 / 3 * rc1.invSq t from funext hnorm ] ; exact ContinuousAt.mul continuousAt_const <| by exact ( show ContinuousAt ( fun t => rc1.invSq t ) tstar from by exact ( show ContinuousAt ( fun t => rc1.u0 - rc1.c * t ) tstar from by exact ContinuousAt.sub continuousAt_const <| ContinuousAt.mul continuousAt_const continuousAt_id ) ) ) <| by aesop;
    · exact ContinuousAt.add ( ContinuousAt.inv₀ ( by exact ( RunningCoupling.invSq_hasDerivAt rc2 tstar |> HasDerivAt.continuousAt ) ) ( by linarith ) ) ( ContinuousAt.inv₀ ( by exact ( show ContinuousAt ( fun t => rcY.invSq t ) tstar from by rw [ show rcY.invSq = _ from funext hnorm ] ; exact ContinuousAt.mul continuousAt_const ( by exact ( RunningCoupling.invSq_hasDerivAt rc1 tstar |> HasDerivAt.continuousAt ) ) ) ) ( by linarith [ hnorm tstar ] ) );
    · exact ne_of_gt ( add_pos ( inv_pos.mpr ( by linarith ) ) ( inv_pos.mpr ( by linarith [ hnorm tstar ] ) ) )
  generalize_proofs at *; (
  exact h_val ▸ h_cont.tendsto))

/-! ## 5. The running Weinberg angle away from unification (math layer)

  The results above compute the mixing angle *at* the unification scale (`3/8`) and
  its limit there.  This section adds the honest **math layer** of direction 4.1: the
  closed-form of `sin²θ_W`, its strict monotonicity in the couplings, and the fact
  that running the hypercharge coupling *away* from its `SU(5)`-normalized value
  drives `sin²θ_W` strictly below the locked `3/8`.

  **Scope caveat (honest boundary).**  That the *physical* low-energy value
  `sin²θ_W ≈ 0.231` at the `Z` pole is exactly the RG image of `3/8` is an
  *empirical / modelling* statement (it depends on the actual Standard-Model
  β-function coefficients, threshold matching, and experimental inputs); it is **not**
  a pure mathematical theorem and is deliberately *not* asserted here.  What is proved
  is only the conditional mathematics: *given* couplings, the angle has this value /
  monotonic behaviour. -/

/-- **Closed form of the mixing angle.**  For positive inverse-square couplings,
`sin²θ_W = u₂ / (u₂ + u_Y)`. -/
theorem sinSqWeinberg_eq (u2 uY : ℝ) (h2 : 0 < u2) (hY : 0 < uY) :
    sinSqWeinberg u2 uY = u2 / (u2 + uY) := by
  have hsum : (0:ℝ) < u2 + uY := by positivity
  have hden : (0:ℝ) < 1 / u2 + 1 / uY := by positivity
  unfold sinSqWeinberg
  rw [div_eq_div_iff (ne_of_gt hden) (ne_of_gt hsum)]
  field_simp
  ring

/-- **Strict antitonicity in the hypercharge coupling.**  For fixed positive `u₂`,
the mixing angle strictly decreases as `u_Y` increases: a larger hypercharge
inverse-square coupling (weaker hypercharge) means a smaller `sin²θ_W`. -/
theorem sinSqWeinberg_strictAnti_uY (u2 : ℝ) (h2 : 0 < u2) :
    StrictAntiOn (fun uY => sinSqWeinberg u2 uY) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  show sinSqWeinberg u2 b < sinSqWeinberg u2 a
  rw [sinSqWeinberg_eq u2 a h2 ha, sinSqWeinberg_eq u2 b h2 hb]
  apply div_lt_div_of_pos_left h2 (by positivity)
  linarith

/-- **Running away from unification lowers the angle.**  If the hypercharge
inverse-square coupling exceeds its `SU(5)`-normalized value `(5/3)·u₂` (i.e. the
system is *below* the grand-unification scale, where hypercharge has run weaker),
then the weak mixing angle is strictly below the locked prediction `3/8`. -/
theorem sinSqWeinberg_lt_three_eighths (u2 uY : ℝ) (h2 : 0 < u2) (hY : 0 < uY)
    (hrun : (5/3) * u2 < uY) :
    sinSqWeinberg u2 uY < 3 / 8 := by
  rw [sinSqWeinberg_eq u2 uY h2 hY, div_lt_iff₀ (by positivity)]
  linarith

/-- Symmetrically, *above* the `SU(5)`-normalized value the angle exceeds `3/8`;
together with the previous lemma this pins `3/8` as the exact value attained
precisely at the normalization `u_Y = (5/3)·u₂`. -/
theorem sinSqWeinberg_gt_three_eighths (u2 uY : ℝ) (h2 : 0 < u2) (hY : 0 < uY)
    (hrun : uY < (5/3) * u2) :
    3 / 8 < sinSqWeinberg u2 uY := by
  rw [sinSqWeinberg_eq u2 uY h2 hY, lt_div_iff₀ (by positivity)]
  linarith

end RGF.RG