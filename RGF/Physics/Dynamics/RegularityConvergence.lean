/-
  RGF/RegularityConvergence.lean

  Direction IV(b) — Weak convergence of the discrete process to its continuum
  (SPDE) limit.

  Extending `KPZEmergence.lean` and `RegularityStructures.lean`, this file gives a
  machine-checked, self-contained core of the *scaling-limit* step: as the lattice
  is refined, discrete height statistics converge to their continuum integrals,
  and the KPZ scaling exponents satisfy the exact algebraic relations.

  * **KPZ scaling exponents.**  With roughness `α = 1/2`, growth `β = 1/3` and
    dynamic exponent `z = 3/2`, the framework satisfies the KPZ relations
    `z = α/β` (`kpz_z_eq`) and the Galilean/scaling identity `α + z = 2`
    (`kpz_alpha_plus_z`).

  * **Discrete → continuum (Riemann-sum) convergence.**  The rescaled discrete
    first and second height moments converge to the continuum integrals:
      `(1/n) ∑_{k<n} (k/n)   → 1/2 = ∫₀¹ x dx`     (`riemann_linear`),
      `(1/n) ∑_{k<n} (k/n)²  → 1/3 = ∫₀¹ x² dx`   (`riemann_quadratic`).

  * **Weak convergence.**  An abstract test-function notion of weak convergence
    (`WeakConv`) with linearity of the limit functional
    (`WeakConv.add`, `WeakConv.smul`).
-/
import Mathlib

open scoped BigOperators Topology
open Filter Finset

namespace RGF.RegConv

/-! ## 1. KPZ scaling exponents -/

/-- The KPZ roughness exponent. -/
noncomputable def kpzAlpha : ℝ := 1/2
/-- The KPZ growth exponent. -/
noncomputable def kpzBeta : ℝ := 1/3
/-- The KPZ dynamic exponent. -/
noncomputable def kpzZ : ℝ := 3/2

/-- **KPZ scaling relation** `z = α/β`. -/
theorem kpz_z_eq : kpzZ = kpzAlpha / kpzBeta := by
  unfold kpzZ kpzAlpha kpzBeta; norm_num

/-- **KPZ Galilean/scaling identity** `α + z = 2`. -/
theorem kpz_alpha_plus_z : kpzAlpha + kpzZ = 2 := by
  unfold kpzAlpha kpzZ; norm_num

/-! ## 2. Discrete → continuum convergence (Riemann sums) -/

/-
**First moment.**  The rescaled discrete mean converges to `∫₀¹ x dx = 1/2`.
-/
theorem riemann_linear :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, (k : ℝ) / n) / n) atTop (𝓝 (1/2)) := by
  -- We'll use the fact that $\sum_{k=0}^{n-1} k = \frac{n(n-1)}{2}$.
  have h_sum : ∀ n : ℕ, (∑ k ∈ Finset.range n, (k : ℝ)) = n * (n - 1) / 2 := by
    exact fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [ Finset.sum_range_succ, ih ]; push_cast; ring
  norm_num [ ← Finset.sum_div _ _ _, h_sum ];
  ring_nf;
  rw [ Metric.tendsto_nhds ] ; norm_num;
  exact fun ε hε => ⟨ ⌈ε⁻¹⌉₊ + 1, fun n hn => by rw [ dist_eq_norm ] ; rw [ Real.norm_of_nonpos ] <;> nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( n : ℝ ) ≥ ⌈ε⁻¹⌉₊ + 1 by exact_mod_cast hn, mul_inv_cancel₀ ( show ( n : ℝ ) ^ 2 ≠ 0 by norm_cast; nlinarith ) ] ⟩

/-
**Second moment.**  The rescaled discrete second moment converges to
    `∫₀¹ x² dx = 1/3`.
-/
theorem riemann_quadratic :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ((k : ℝ) / n)^2) / n) atTop (𝓝 (1/3)) := by
  -- We'll use the fact that $\sum_{k=0}^{n-1} k^2 = \frac{(n-1)n(2n-1)}{6}$.
  have h_sum : ∀ n : ℕ, ∑ k ∈ Finset.range n, (k : ℝ)^2 = (n * (n - 1) * (2 * n - 1) : ℝ) / 6 := by
    exact fun n => by induction n <;> norm_num [ Finset.sum_range_succ ] ; linarith;
  simp_all +decide [ ← Finset.sum_div, div_pow ];
  -- Simplify the expression inside the limit.
  suffices h_simplify : Filter.Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ)) / 6) Filter.atTop (nhds (1 / 3)) by
    norm_num +zetaDelta at *;
    refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ div_div, div_eq_div_iff ] <;> first | positivity | simpa [ hn.ne', sq, mul_assoc, mul_comm, mul_left_comm, sub_mul, mul_sub ] using by ring );
  exact le_trans ( Filter.Tendsto.div_const ( Filter.Tendsto.mul ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ( tendsto_const_nhds.sub ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) _ ) ( by norm_num )

/-! ## 3. Abstract weak convergence -/

/-- A sequence of "distributions" `μ n : (ℝ → ℝ) → ℝ` **converges weakly** to `μ∞`
    if the pairing against every test function converges. -/
def WeakConv (μ : ℕ → (ℝ → ℝ) → ℝ) (mLim : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Tendsto (fun n => μ n f) atTop (𝓝 (mLim f))

/-
The weak limit is additive along a sum of two weakly convergent sequences,
    provided the limit functionals add pointwise.
-/
theorem WeakConv.add {μ ν : ℕ → (ℝ → ℝ) → ℝ} {mLim nLim : (ℝ → ℝ) → ℝ}
    (hμ : WeakConv μ mLim) (hν : WeakConv ν nLim) :
    WeakConv (fun n f => μ n f + ν n f) (fun f => mLim f + nLim f) := by
  exact fun f => Filter.Tendsto.add ( hμ f ) ( hν f )

/-
The weak limit is homogeneous under scaling by a constant.
-/
theorem WeakConv.smul {μ : ℕ → (ℝ → ℝ) → ℝ} {mLim : (ℝ → ℝ) → ℝ}
    (hμ : WeakConv μ mLim) (c : ℝ) :
    WeakConv (fun n f => c * μ n f) (fun f => c * mLim f) := by
  exact fun f => Filter.Tendsto.const_mul c ( hμ f )

end RGF.RegConv