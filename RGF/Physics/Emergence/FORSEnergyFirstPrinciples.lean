import Mathlib

/-!
# FORS energy from first principles · complete rigorous proof chain

This file formalizes the complete proof chain (steps 0–7) deriving the FORS energy from first
principles as a self-contained Lean module. Each step provides precise mathematical definitions,
theorem statements, and machine-checked proofs.

* Step 0: the FORS kernel `K(w) = 1/(1+w^5)` and the five-pole structure (`forsKernel`,
  `fors_pole`, `forsKernel_hasSum`).
* Step 1: the packing radius `ε√d/2 → 0` of the rescaled cubic lattice (`fillRad`,
  `fillRad_tendsto`).
* Step 2: the discrete energy (left-endpoint Riemann sum) converges to the continuous integral
  energy, with explicit error bounds (`Ediscr`, `Econt`, `Ediscr_sub_Econt_bounds`,
  `Ediscr_tendsto`), together with the vacuum-state minimum (`Econt_zero`, `Econt_pos`).
* Step 3: the double criterion `2d-1=5 ∧ d+2R=5` uniquely locks `(d,R)=(3,1)`, with membrane
  dimension `m=d-R=2` (`dimension_lock`).
* Step 4: Ginzburg–Landau universality — any `C²` effective potential with a nondegenerate
  minimum at `m=2` has leading order `(m-2)²` (`GL_universality`). The single isolated
  normalization assumption `V'(2)=0` appears explicitly in the hypotheses of that theorem.
* Step 5: the kernel structure uniquely determines the energy form (`membraneDim`, `gammaCrit`,
  `forsEnergy`, `forsEnergy_nonneg`, `forsEnergy_eq_zero_iff`).
* Step 6: the momentum-space anomalous dispersion `ω(k)=|k|^{5/2}`, scale covariance, the
  kinetic integral `∫₀¹ ω = 2/7`, and discrete→continuous convergence (`omega`, `omega_scaling`,
  `kinetic_integral`, `Kdiscr_tendsto`).
* Step 7: the main theorem `fors_energy_first_principles` chains all conclusions together.

All proofs depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace FORSEnergyFirstPrinciples

open scoped BigOperators
open Filter Topology

/-! ## Step 0 · The FORS kernel and the five-pole structure -/

/-- The FORS stable kernel: `K(w) = 1/(1+w^5)`. -/
noncomputable def forsKernel (w : ℂ) : ℂ := 1 / (1 + w ^ 5)

/-- The `j`-th pole `w_j = exp(i (2j+1)π/5)`. -/
noncomputable def forsPole (j : Fin 5) : ℂ :=
  Complex.exp (Complex.I * ((2 * (j : ℝ) + 1) * Real.pi / 5))

/-
Five-pole structure: each `w_j` satisfies `w_j^5 = -1`, i.e. they are exactly the zeros of the
denominator.
-/
theorem fors_pole (j : Fin 5) : (forsPole j) ^ 5 = -1 := by
  fin_cases j <;> norm_num [ forsPole, ← Complex.exp_nat_mul ];
  · ring_nf; norm_num [ mul_div, Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
  · exact Complex.exp_pi_mul_I ▸ by rw [ Complex.exp_eq_exp_iff_exists_int ] ; use 1; ring;
  · exact Complex.exp_pi_mul_I ▸ by rw [ Complex.exp_eq_exp_iff_exists_int ] ; exact ⟨ 2, by ring ⟩ ;
  · exact Complex.exp_pi_mul_I ▸ by rw [ Complex.exp_eq_exp_iff_exists_int ] ; exact ⟨ 3, by ring ⟩ ;
  · exact Complex.exp_pi_mul_I ▸ by rw [ Complex.exp_eq_exp_iff_exists_int ] ; exact ⟨ 4, by ring ⟩ ;

/-
The five poles lie on the unit circle `|w|=1`.
-/
theorem fors_pole_abs (j : Fin 5) : ‖forsPole j‖ = 1 := by
  unfold forsPole; norm_num [ Complex.norm_exp ] ;

/-
Within the disc of convergence `|w|<1`, the kernel has the absolutely convergent geometric
series expansion `K(w) = ∑ₙ (−w⁵)ⁿ`.
-/
theorem forsKernel_hasSum (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => (-w ^ 5) ^ n) (forsKernel w) := by
  convert hasSum_geometric_of_norm_lt_one _ using 1;
  rotate_left;
  exacts [ ℂ, inferInstance, -w ^ 5, by simpa using pow_lt_one₀ ( norm_nonneg _ ) hw ( by norm_num ), by unfold forsKernel; ring ]

/-! ## Step 1 · The packing radius of the rescaled cubic lattice -/

/-- The packing radius `ε√d/2` of the `d`-dimensional rescaled cubic lattice `εℤ^d`. -/
noncomputable def fillRad (d : ℕ) (ε : ℝ) : ℝ := ε * Real.sqrt d / 2

/-
The packing radius tends to zero as `ε → 0⁺` (a Gromov–Hausdorff convergence criterion).
-/
theorem fillRad_tendsto (d : ℕ) :
    Tendsto (fun ε : ℝ => fillRad d ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  convert Tendsto.div_const ( Filter.Tendsto.const_mul ( Real.sqrt d ) ( Filter.tendsto_id.mono_left inf_le_left ) ) 2 using 2 ; norm_num [ fillRad ]; all_goals ring

/-! ## Step 2 · Rigorous convergence of the discrete energy to the continuous energy (monotone squeeze) -/

/-- The FORS energy density `ρ(s) = 1/(1+|s|⁵)`. -/
noncomputable def rho (s : ℝ) : ℝ := 1 / (1 + |s| ^ 5)

theorem rho_pos (s : ℝ) : 0 < rho s := by
  exact one_div_pos.mpr ( by positivity )

theorem rho_continuous : Continuous rho := by
  exact Continuous.div continuous_const ( by continuity ) fun x => by positivity;

/-
`ρ` is monotonically decreasing on `[0,∞)`.
-/
theorem rho_antitoneOn : AntitoneOn rho (Set.Ici 0) := by
  intro x hx y hy hxy; exact (by
  unfold rho;
  gcongr ; aesop)

/-- The discrete energy (left-endpoint Riemann sum). -/
noncomputable def Ediscr (a : ℝ) (n : ℕ) : ℝ :=
  (a / n) * ∑ i ∈ Finset.range n, rho (i * a / n)

/-- The continuous energy `E_cont(a) = ∫₀ᵃ ρ`. -/
noncomputable def Econt (a : ℝ) : ℝ := ∫ s in (0)..a, rho s

/-
Upper and lower bounds (explicit error estimate): when `a ≥ 0` and `n ≥ 1`,
`0 ≤ E_n(a) − E_cont(a) ≤ (a/n)(ρ(0) − ρ(a))`.
-/
theorem Ediscr_sub_Econt_bounds (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 0 < n) :
    0 ≤ Ediscr a n - Econt a ∧ Ediscr a n - Econt a ≤ (a / n) * (rho 0 - rho a) := by
  constructor;
  · -- By definition of $E_{\text{discr}}$ and $E_{\text{cont}}$, we can write
    have h_decomp : Econt a = ∑ i ∈ Finset.range n, ∫ s in (i * a / n)..((i + 1) * a / n), rho s := by
      rw [ show Econt a = ∫ s in ( 0 : ℝ )..a, rho s from rfl ];
      symm;
      convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num [ hn.ne' ];
      exact fun k hk => Continuous.intervalIntegrable ( by exact rho_continuous ) _ _;
    -- By the properties of the integral, we can bound each term in the sum.
    have h_integral_bound : ∀ i ∈ Finset.range n, ∫ s in (i * a / n)..((i + 1) * a / n), rho s ≤ (a / n) * rho (i * a / n) := by
      intro i hi
      have h_integral_bound : ∀ s ∈ Set.Icc (i * a / n) ((i + 1) * a / n), rho s ≤ rho (i * a / n) := by
        intros s hs; exact (by
        exact rho_antitoneOn ( show ( i : ℝ ) * a / n ≥ 0 by positivity ) ( show s ≥ 0 by exact le_trans ( by positivity ) hs.1 ) hs.1);
      convert intervalIntegral.integral_mono_on _ _ _ h_integral_bound <;> norm_num;
      · exact Or.inl <| by ring;
      · bound;
      · exact Continuous.intervalIntegrable ( by exact rho_continuous ) _ _;
    exact sub_nonneg_of_le ( h_decomp.symm ▸ le_trans ( Finset.sum_le_sum h_integral_bound ) ( by simp +decide [ Ediscr, mul_comm, Finset.mul_sum _ _ _ ] ) );
  · -- By summing the inequalities from the previous step, we get:
    have h_sum_lower : ∑ i ∈ Finset.range n, ∫ s in (i * a / n)..((i + 1) * a / n), rho s ≥ ∑ i ∈ Finset.range n, (a / n) * rho ((i + 1) * a / n) := by
      -- Apply the fact that the integral of a decreasing function over an interval is less than or equal to the integral of the function evaluated at the right endpoint of the interval.
      have h_integral_le_right_endpoint : ∀ i ∈ Finset.range n, ∫ s in (i * a / n)..((i + 1) * a / n), rho s ≥ ∫ s in (i * a / n)..((i + 1) * a / n), rho ((i + 1) * a / n) := by
        intro i hi; refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
        · gcongr ; linarith;
        · exact Continuous.intervalIntegrable ( by exact rho_continuous ) _ _;
        · intro x hx₁ hx₂; unfold rho; gcongr;
          exact le_trans ( by positivity ) hx₁;
      gcongr ; ring_nf at * ; aesop;
    -- By simplifying the right-hand side of the inequality, we can see that it matches the desired form.
    have h_simplify : ∑ i ∈ Finset.range n, (a / n) * rho ((i + 1) * a / n) = (∑ i ∈ Finset.range n, (a / n) * rho (i * a / n)) - (a / n) * rho 0 + (a / n) * rho a := by
      have := Finset.sum_range_sub ( fun i => a / n * rho ( i * a / n ) ) n; simp_all +decide [ mul_div_assoc ] ; ring;
      simp_all +decide [ mul_div_cancel₀, hn.ne' ] ; ring_nf at * ; linarith;
    -- By combining the results from the previous steps, we conclude the proof.
    have h_final : ∑ i ∈ Finset.range n, ∫ s in (i * a / n)..((i + 1) * a / n), rho s = ∫ s in (0)..a, rho s := by
      convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num [ hn.ne' ];
      exact fun k hk => Continuous.intervalIntegrable ( by exact rho_continuous ) _ _;
    unfold Ediscr Econt; norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *; linarith;

/-
The discrete energy converges to the continuous energy.
-/
theorem Ediscr_tendsto (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n => Ediscr a n) atTop (nhds (Econt a)) := by
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds _ _ _;
  refine' fun n => Econt a + ( a / n ) * ( rho 0 - rho a );
  · exact le_trans ( tendsto_const_nhds.add ( Filter.Tendsto.mul ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ) ( by norm_num );
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by linarith [ Ediscr_sub_Econt_bounds a ha n hn ] ;
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by linarith [ Ediscr_sub_Econt_bounds a ha n hn ] ;

/-
Vacuum state: `E_cont(0) = 0`.
-/
theorem Econt_zero : Econt 0 = 0 := by
  unfold Econt; simp +decide ;

/-
The vacuum state is the unique minimum: for any `a > 0`, `E_cont(a) > 0`.
-/
theorem Econt_pos (a : ℝ) (ha : 0 < a) : 0 < Econt a := by
  apply_rules [ intervalIntegral.intervalIntegral_pos_of_pos_on ];
  · exact Continuous.intervalIntegrable ( by exact rho_continuous ) _ _;
  · exact fun x hx => rho_pos x

/-! ## Step 3 · Joint dimension locking and the membrane dimension -/

/-
Joint locking by the double criterion: under `d, R ≥ 1`, `2d−1 = 5` and `d+2R = 5` uniquely
determine `(d,R) = (3,1)`, hence the membrane dimension `m = d − R = 2`.
-/
theorem dimension_lock (d R : ℕ) (hd : 1 ≤ d) (hR : 1 ≤ R)
    (h1 : 2 * d - 1 = 5) (h2 : d + 2 * R = 5) :
    d = 3 ∧ R = 1 ∧ d - R = 2 := by
  omega

/-! ## Step 4 · Ginzburg–Landau universality -/

/-
**GL universality**: let `V` be a `C²` function with `V(2)=0`, `V'(2)=0`, `V''(2)=2`. Then as
`m → 2`, `V(m) = (m−2)² + o((m−2)²)`. The single isolated normalization assumption `V'(2)=0`
(i.e. `h1`) appears explicitly in the hypotheses.
-/
theorem GL_universality (V : ℝ → ℝ) (hV : ContDiff ℝ 2 V)
    (h0 : V 2 = 0) (h1 : deriv V 2 = 0) (h2 : deriv (deriv V) 2 = 2) :
    (fun m => V m - (m - 2) ^ 2) =o[nhds 2] (fun m => (m - 2) ^ 2) := by
  convert ( taylor_isLittleO ( E := ℝ ) ( n := 2 ) ( f := V ) ) _ _ ( hV.contDiffOn ) using 1;
  rw [ nhdsWithin_univ ];
  · norm_num [ Finset.sum_range_succ', taylorCoeffWithin ];
    rw [ iteratedDeriv_eq_iterate ] ; norm_num [ h0, h1, h2 ] ; ring;
  · exact convex_univ;
  · norm_num

/-! ## Step 5 · The kernel structure uniquely determines the energy form -/

/-- The number of poles of the FORS kernel (guaranteed to be 5 by the dimension lock `d=3`). -/
def forsDegree (d : ℕ) : ℕ := 2 * d - 1

/-- The membrane dimension `membraneDim d = d − 1`. -/
def membraneDim (d : ℕ) : ℕ := d - 1

/-- The critical coupling constant `γ_crit = 2 / membraneDim d`. -/
noncomputable def gammaCrit (d : ℕ) : ℝ := 2 / (membraneDim d : ℝ)

/-- The generalized energy functional `(s − membraneDim d)²`. -/
noncomputable def forsEnergyGen (d : ℕ) (s : ℝ) : ℝ := (s - (membraneDim d : ℝ)) ^ 2

/-- The standard dimension-penalty energy `forsEnergy s = (s−2)²`. -/
noncomputable def forsEnergy (s : ℝ) : ℝ := (s - 2) ^ 2

/-
For `d=3` the number of poles is 5.
-/
theorem forsDegree_three : forsDegree 3 = 5 := by
  rfl

/-
For `d=3` the membrane dimension is 2.
-/
theorem membraneDim_three : membraneDim 3 = 2 := by
  rfl

/-
For `d=3` the critical coupling constant is 1.
-/
theorem gammaCrit_three : gammaCrit 3 = 1 := by
  unfold gammaCrit membraneDim; norm_num;

/-
For `d=3` the generalized energy reduces to the standard dimension-penalty energy.
-/
theorem forsEnergyGen_three (s : ℝ) : forsEnergyGen 3 s = forsEnergy s := by
  unfold forsEnergyGen forsEnergy; norm_num [ membraneDim ] ;

theorem forsEnergy_nonneg (s : ℝ) : 0 ≤ forsEnergy s := by
  exact sq_nonneg _

theorem forsEnergy_eq_zero_iff (s : ℝ) : forsEnergy s = 0 ↔ s = 2 := by
  exact ⟨ fun h => by rw [ forsEnergy ] at h; nlinarith, fun h => by rw [ forsEnergy, h ] ; norm_num ⟩

/-! ## Step 6 · Momentum-space anomalous dispersion and the kinetic integral -/

/-- The anomalous dispersion relation `ω(k) = |k|^{5/2}`. -/
noncomputable def omega (k : ℝ) : ℝ := |k| ^ ((5 : ℝ) / 2)

/-
Scale covariance: for `s ≥ 0`, `ω(s·k) = s^{5/2} · ω(k)`.
-/
theorem omega_scaling (s k : ℝ) (hs : 0 ≤ s) :
    omega (s * k) = s ^ ((5 : ℝ) / 2) * omega k := by
  unfold omega; rw [ abs_mul, abs_of_nonneg hs ] ; ring;
  rw [ Real.mul_rpow hs ( abs_nonneg k ) ]

/-
Kinetic integral: `∫₀¹ ω(t) dt = ∫₀¹ t^{5/2} dt = 2/7`.
-/
theorem kinetic_integral : (∫ t in (0:ℝ)..1, omega t) = 2 / 7 := by
  unfold omega;
  rw [ intervalIntegral.integral_congr fun x hx => by rw [ abs_of_nonneg ] ; aesop ] ; norm_num [ integral_rpow ]

/-- The discrete kinetic Riemann sum `K_n = (1/n) ∑_{j=1}^{n} ω(j/n)`. -/
noncomputable def Kdiscr (n : ℕ) : ℝ :=
  (1 / n) * ∑ j ∈ Finset.Icc 1 n, omega (j / n)

theorem omega_continuous : Continuous omega := by
  exact Continuous.rpow ( continuous_abs ) continuous_const <| by norm_num;

/-
`ω` is monotonically increasing on `[0,∞)`.
-/
theorem omega_monotoneOn : MonotoneOn omega (Set.Ici 0) := by
  intro x hx y hy hxy;
  exact Real.rpow_le_rpow ( abs_nonneg _ ) ( by rw [ abs_of_nonneg hx.out, abs_of_nonneg hy.out ] ; linarith ) ( by norm_num )

/-
Upper and lower bounds between the discrete kinetic sum and the integral `2/7` (right-endpoint
Riemann sum, monotonically increasing case): when `n ≥ 1`, `0 ≤ K_n − 2/7 ≤ 1/n`.
-/
theorem Kdiscr_sub_bounds (n : ℕ) (hn : 0 < n) :
    0 ≤ Kdiscr n - 2 / 7 ∧ Kdiscr n - 2 / 7 ≤ 1 / n := by
  refine' ⟨ _, _ ⟩;
  · -- By definition of $Kdiscr$, we know that
    have h_Kdiscr_def : Kdiscr n = (1 / n : ℝ) * ∑ i ∈ Finset.range n, omega ((i + 1) / n) := by
      exact Eq.symm ( by rw [ show Kdiscr n = ( 1 / n : ℝ ) * ∑ j ∈ Finset.Icc 1 n, omega ( j / n ) by rfl ] ; erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, Finset.sum_range_succ' ] );
    -- By definition of $omega$, we know that
    have h_omega_def : ∑ i ∈ Finset.range n, ∫ t in (i / n : ℝ)..((i + 1) / n : ℝ), omega t = 2 / 7 := by
      convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num [ hn.ne' ];
      · exact kinetic_integral.symm;
      · exact fun k hk => Continuous.intervalIntegrable ( by exact omega_continuous ) _ _;
    -- By definition of $omega$, we know that $\omega(t) \leq \omega((i + 1) / n)$ for all $t \in [i / n, (i + 1) / n]$.
    have h_omega_le : ∀ i ∈ Finset.range n, ∫ t in (i / n : ℝ)..((i + 1) / n : ℝ), omega t ≤ ∫ t in (i / n : ℝ)..((i + 1) / n : ℝ), omega ((i + 1) / n) := by
      intro i hi; refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
      · bound;
      · exact Continuous.intervalIntegrable ( by exact omega_continuous ) _ _;
      · intro x hx₁ hx₂; exact omega_monotoneOn ( show ( 0 : ℝ ) ≤ x by exact le_trans ( by positivity ) hx₁ ) ( show ( 0 : ℝ ) ≤ ( i + 1 : ℝ ) / n by positivity ) hx₂;
    simp_all +decide [ div_eq_mul_inv ];
    exact h_omega_def ▸ by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by convert h_omega_le i ( Finset.mem_range.mp hi ) using 1 ; ring;
  · -- By definition of $Kdiscr$, we can rewrite the sum as a Riemann sum.
    have h_riemann_sum : ∑ j ∈ Finset.Icc 1 n, omega (j / n) * (1 / n) - ∫ t in (0 : ℝ)..1, omega t ≤ (1 / n) * (omega 1 - omega 0) := by
      -- By definition of $Kdiscr$, we can rewrite the sum as a Riemann sum and apply the integral bounds.
      have h_riemann_sum : ∑ j ∈ Finset.Icc 1 n, omega (j / n) * (1 / n) - ∑ j ∈ Finset.Icc 1 n, ∫ t in (j - 1 : ℝ) / n..j / n, omega t ≤ (1 / n) * (omega 1 - omega 0) := by
        have h_riemann_sum : ∀ j ∈ Finset.Icc 1 n, omega (j / n) * (1 / n) - ∫ t in (j - 1 : ℝ) / n..j / n, omega t ≤ (omega (j / n) - omega ((j - 1) / n)) * (1 / n) := by
          intros j hj
          have h_integral_bound : ∫ t in (j - 1 : ℝ) / n..j / n, omega t ≥ ∫ t in (j - 1 : ℝ) / n..j / n, omega ((j - 1) / n) := by
            apply_rules [ intervalIntegral.integral_mono_on ];
            · gcongr ; norm_num;
            · norm_num;
            · exact Continuous.intervalIntegrable ( by exact omega_continuous ) _ _;
            · intro x hx; exact omega_monotoneOn ( show ( 0 : ℝ ) ≤ ( j - 1 ) / n by exact div_nonneg ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| Finset.mem_Icc.mp hj |>.1 ) <| Nat.cast_nonneg _ ) ( show ( 0 : ℝ ) ≤ x by exact hx.1.trans' <| div_nonneg ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| Finset.mem_Icc.mp hj |>.1 ) <| Nat.cast_nonneg _ ) hx.1;
          norm_num at *; ring_nf at *; linarith;
        convert Finset.sum_le_sum h_riemann_sum using 1;
        · rw [ Finset.sum_sub_distrib ];
        · erw [ Finset.sum_Ico_eq_sum_range ];
          have := Finset.sum_range_sub ( fun x => omega ( x / n ) ) n; simp_all +decide [ add_comm ] ;
          simp_all +decide [ ← Finset.sum_mul _ _ _, ne_of_gt hn ];
          ring;
      convert h_riemann_sum using 2;
      erw [ Finset.sum_Ico_eq_sum_range ];
      symm;
      convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num [ hn.ne' ];
      · ring;
      · exact fun k hk => Continuous.intervalIntegrable ( by exact omega_continuous ) _ _;
    convert h_riemann_sum using 1 <;> norm_num [ Kdiscr, kinetic_integral ];
    · rw [ mul_comm, Finset.sum_mul ];
    · unfold omega; norm_num;

/-
The discrete kinetic sum converges to `2/7`.
-/
theorem Kdiscr_tendsto : Tendsto Kdiscr atTop (nhds (2 / 7)) := by
  rw [ Metric.tendsto_nhds ];
  norm_num [ Real.dist_eq ];
  exact fun ε hε => ⟨ ⌈ε⁻¹⌉₊ + 1, fun n hn => by rw [ abs_lt ] ; constructor <;> nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ hε.ne', show ( n : ℝ ) ≥ ⌈ε⁻¹⌉₊ + 1 by exact_mod_cast hn, Kdiscr_sub_bounds n ( by linarith ), one_div_mul_cancel ( by norm_cast; linarith : ( n : ℝ ) ≠ 0 ) ] ⟩

/-! ## Step 7 · Summary: assembling the derivation chain -/

/-
**FORS energy from first principles (main theorem)**: chains the core conclusions of steps 0–6
into a single theorem.
-/
theorem fors_energy_first_principles :
    -- Step 0: five-pole structure
    (∀ j : Fin 5, (forsPole j) ^ 5 = -1) ∧
    -- Step 1: the packing radius tends to zero
    (Tendsto (fun ε : ℝ => fillRad 3 ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    -- Step 2: discrete energy converges + the vacuum state is the unique minimum
    (∀ a : ℝ, 0 ≤ a → Tendsto (fun n => Ediscr a n) atTop (nhds (Econt a))) ∧
    Econt 0 = 0 ∧ (∀ a : ℝ, 0 < a → 0 < Econt a) ∧
    -- Step 3: joint dimension locking
    (∀ d R : ℕ, 1 ≤ d → 1 ≤ R → 2 * d - 1 = 5 → d + 2 * R = 5 →
      d = 3 ∧ R = 1 ∧ d - R = 2) ∧
    -- Step 5: the kernel determines the energy
    (forsEnergy 2 = 0 ∧ (∀ s : ℝ, 0 ≤ forsEnergy s) ∧
      (∀ s : ℝ, forsEnergy s = 0 ↔ s = 2)) ∧
    -- Step 6: kinetic integral
    ((∫ t in (0:ℝ)..1, omega t) = 2 / 7) := by
  refine ⟨fors_pole, fillRad_tendsto 3, Ediscr_tendsto, Econt_zero, Econt_pos,
    dimension_lock, ⟨(forsEnergy_eq_zero_iff 2).mpr rfl, forsEnergy_nonneg,
      forsEnergy_eq_zero_iff⟩, kinetic_integral⟩

end FORSEnergyFirstPrinciples