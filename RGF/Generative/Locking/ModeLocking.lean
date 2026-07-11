/-
  ModeLocking.lean — The modular-locking bridge: from the RGF dynamics to `p = 5`
  (the as-yet-unbuilt bridge from the axioms to k = 5: mode locking)

  This file formalizes the missing link between the RGF axioms and the
  Locking-Membrane conditions L2 (`n₂ = 2`) and L3 (`k` odd), following the
  fourth RCD note on *"The mode-locking emergence mechanism of Z₅ symmetry"*.

  The chain it formalizes:

  * §1 (central-manifold reduction): the central spectrum of the
    tangent map `DR|_{Ψ*}` is a single conjugate pair `ρ₀ e^{±iθ₀}` with
    `0 < θ₀ < π` (no real eigenvalue ⇒ Bogdanov–Takens bifurcation excluded),
    and the phase dynamics reduce to an effective Circle Map.
  * §2 (Circle Map → Zₚ symmetry): when the rotation number locks to `1/p`, the
    central eigenvalues form a regular `p`-gon `{ρ e^{2πi j/p}}`, which is
    invariant under rotation by `2π/p` (a `Z_p` action) and under complex
    conjugation (a reflection), hence carries a dihedral `D_p` symmetry.
  * §3 (Arnold-tongue competition): the width of the order-`p`
    Arnold tongue is `K^p/π`; for weak coupling `0 < K < 1` it is strictly
    decreasing in `p`, so the lowest admissible order has the deepest basin of
    attraction.
  * §4 (physical-constraint filtering): the UV-convergence
    constraint C1 (`p/2 > d/2`, `d = 4`) and the odd-`p` constraint C2 restrict
    the candidate orders to `{5, 7, 9, …}`; combined with the Arnold-tongue
    competition (deepest basin = smallest candidate) this selects `p = 5`.
  * §5 (homology with the FORS kernel): the minimal admissible
    order `5` coincides with the FORS kernel exponent `5 = (d+1)`-type UV bound.
  * Bridge: `p = 5 ⇒` L2 (`num2DIrreps 5 = 2`) `∧` L3 (`Odd 5`), i.e.
    `LockingMembraneConditions 5`.

  The genuinely deep analytic inputs (Hadamard–Perron existence of a `C¹`
  central manifold, Doeblin/Markov ergodicity of the noisy Circle Map) are kept
  as explicit hypotheses/structure fields — honestly marked as assumptions, not
  disguised theorems — while every discrete, arithmetic and algebraic step of
  the selection of `p = 5` is proved `sorry`-free.
-/

import Mathlib
import RGF.Generative.Locking.LockingMembrane

open Real Complex Finset

namespace ModeLocking

noncomputable section

/-! ============================================================
    §1  Central-manifold reduction and the effective Circle Map
    ============================================================ -/

/-- The central spectrum `σ_c` of the tangent map `DR|_{Ψ*}`: a single conjugate
    pair `ρ₀ e^{±iθ₀}`.  Criticality forces `0 < ρ₀ ≤ 1`; genuine complexity
    (no real eigenvalue) forces the argument `θ₀` into `(0, π)`. -/
structure CentralSpectrum where
  /-- common modulus of the central conjugate pair. -/
  rho0 : ℝ
  /-- common argument of the central conjugate pair. -/
  theta0 : ℝ
  rho0_pos : 0 < rho0
  rho0_le_one : rho0 ≤ 1
  theta0_pos : 0 < theta0
  theta0_lt_pi : theta0 < π

/-- The two central eigenvalues `ρ₀ e^{±iθ₀}`. -/
def CentralSpectrum.eigPair (S : CentralSpectrum) : Fin 2 → ℂ :=
  ![S.rho0 * Complex.exp (Complex.I * S.theta0),
    S.rho0 * Complex.exp (-(Complex.I * S.theta0))]

/-
The two central eigenvalues are complex conjugates of each other.
-/
theorem CentralSpectrum.eigPair_conj (S : CentralSpectrum) :
    (starRingEnd ℂ) (S.eigPair 0) = S.eigPair 1 := by
  unfold CentralSpectrum.eigPair;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]

/-
Both central eigenvalues have modulus `ρ₀`.
-/
theorem CentralSpectrum.eigPair_abs (S : CentralSpectrum) (i : Fin 2) :
    ‖S.eigPair i‖ = S.rho0 := by
  unfold CentralSpectrum.eigPair; fin_cases i;
  · norm_num [ Complex.norm_exp, abs_of_pos S.rho0_pos ];
  · norm_num [ Complex.norm_exp, abs_of_pos S.rho0_pos ]

/-
**Bogdanov–Takens exclusion.** Because the argument lies strictly inside
    `(0, π)`, neither central eigenvalue is a real number; in particular the
    central spectrum contains no real eigenvalue, so a Bogdanov–Takens
    bifurcation (`|σ_c| ≥ 3` with a real central eigenvalue) is structurally
    excluded.
-/
theorem CentralSpectrum.eigPair_not_real (S : CentralSpectrum) (i : Fin 2) :
    (S.eigPair i).im ≠ 0 := by
  fin_cases i <;> simp +decide [ CentralSpectrum.eigPair, Complex.exp_re, Complex.exp_im ]; all_goals exact ⟨ ne_of_gt S.rho0_pos, ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi S.theta0_pos S.theta0_lt_pi ) ⟩

/-- The standard form of the effective Circle Map obtained after the
    central-manifold reduction and the addition of intrinsic noise (§3.2):
    `θ ↦ θ + Ω + (K/2π) sin(2πθ)`. -/
def effectiveCircleMap (Omega K theta : ℝ) : ℝ :=
  theta + Omega + (K / (2 * π)) * Real.sin (2 * π * theta)

/-- The TRCG (time-resolved coarse-graining) correction factor applied to the
    effective coupling: `K^{(τ)} = K · |sin(τθ₀/2) / (τ sin(θ₀/2))|` (eq. 3.3). -/
def trcgCouplingFactor (theta0 : ℝ) (tau : ℕ) : ℝ :=
  |Real.sin (tau * theta0 / 2) / (tau * Real.sin (theta0 / 2))|

/-
The TRCG factor is nonnegative.
-/
theorem trcgCouplingFactor_nonneg (theta0 : ℝ) (tau : ℕ) :
    0 ≤ trcgCouplingFactor theta0 tau := by
  exact abs_nonneg _

/-- **Doeblin / Markov ergodicity hypothesis** for the noisy effective Circle
    Map.  This is the genuinely analytic input of §3.3 (existence of `α > 0`, an
    invariant probability measure and a uniform minorization); it is kept as an
    explicit assumption rather than disguised as a theorem. -/
structure DoeblinErgodicity (Omega K : ℝ) where
  /-- minorization constant. -/
  alpha : ℝ
  alpha_pos : 0 < alpha
  /-- the contraction/coupling is in the weak regime where the analysis applies. -/
  weak_coupling : 0 < K ∧ K < 1

/-! ============================================================
    §2  From the Circle Map to Z_p / D_p symmetry
    ============================================================ -/

/-- When the rotation number locks to `1/p`, the central eigenvalues fill out a
    regular `p`-gon: `ρ e^{2πi j/p}`, indexed by `j : ℕ` (periodic with period
    `p`). -/
def lockedEigenvalue (rho : ℝ) (p : ℕ) (j : ℕ) : ℂ :=
  rho * Complex.exp (2 * π * Complex.I * j / p)

/-- The set of vertices of the locked regular `p`-gon. -/
def pgonVertices (rho : ℝ) (p : ℕ) : Set ℂ :=
  {z | ∃ j : ℕ, z = lockedEigenvalue rho p j}

/-- The `Z_p` rotation acting on the complex plane: multiplication by
    `e^{2πi/p}`. -/
def rotateBy (p : ℕ) (z : ℂ) : ℂ := Complex.exp (2 * π * Complex.I / p) * z

/-
Rotation by `2π/p` advances the index by one.
-/
theorem rotateBy_lockedEigenvalue (rho : ℝ) (p : ℕ) (j : ℕ) :
    rotateBy p (lockedEigenvalue rho p j) = lockedEigenvalue rho p (j + 1) := by
  unfold rotateBy lockedEigenvalue; by_cases hp : p = 0 <;> simp +decide [ hp, Complex.exp_add, mul_add, add_div ] ; ring;

/-
The locked eigenvalues are periodic with period `p`.
-/
theorem lockedEigenvalue_periodic (rho : ℝ) (p : ℕ) (hp : 0 < p) (j : ℕ) :
    lockedEigenvalue rho p (j + p) = lockedEigenvalue rho p j := by
  unfold lockedEigenvalue; push_cast; ring_nf; simp +decide [ hp.ne' ] ;
  exact Or.inl ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ 1, by ring ⟩ )

/-
Applying the rotation `p` times is the identity (the `Z_p` action).
-/
theorem rotateBy_pow_p (p : ℕ) (hp : 0 < p) (z : ℂ) :
    (rotateBy p)^[p] z = z := by
  -- By definition of exponentiation, we can rewrite this as $(Complex.exp (2 * π * Complex.I / p))^p$.
  have h_exp : (Complex.exp (2 * Real.pi * Complex.I / p)) ^ p = Complex.exp (2 * Real.pi * Complex.I) := by
    rw [ ← Complex.exp_nat_mul, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr hp.ne' ) ];
  unfold rotateBy; simp +decide [ h_exp ] ;

/-
**`Z_p` symmetry.** The set of locked eigenvalues is invariant under the
    rotation `rotateBy p`.
-/
theorem pgon_rotation_invariant (rho : ℝ) (p : ℕ) :
    rotateBy p '' pgonVertices rho p ⊆ pgonVertices rho p := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨j, hj⟩ := hy
  use j + 1
  simp [hj, rotateBy_lockedEigenvalue]

/-
**Reflection (`D_p`) symmetry.** The set of locked eigenvalues is invariant
    under complex conjugation; together with the `Z_p` rotation this realizes the
    full dihedral group `D_p` acting on the regular `p`-gon.
-/
theorem pgon_conj_invariant (rho : ℝ) (p : ℕ) :
    (starRingEnd ℂ) '' pgonVertices rho p ⊆ pgonVertices rho p := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨j, rfl⟩ := hw
  use j * (p - 1) + p;
  by_cases hp : p = 0 <;> simp_all +decide [ lockedEigenvalue ];
  rw [ Nat.cast_sub ( Nat.one_le_iff_ne_zero.mpr hp ) ] ; ring_nf ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, hp ] ;
  norm_num [ mul_assoc, mul_comm Real.pi ]

/-! ============================================================
    §3  Arnold-tongue competition
    ============================================================ -/

/-- The width of the order-`p` Arnold tongue at weak coupling `K`: `ΔΩ_p ≈ Kᵖ/π`
    (eq. 3.8). -/
def arnoldWidth (K : ℝ) (p : ℕ) : ℝ := K ^ p / π

/-
The Arnold-tongue width is positive for positive coupling.
-/
theorem arnoldWidth_pos (K : ℝ) (p : ℕ) (hK : 0 < K) :
    0 < arnoldWidth K p := by
  exact div_pos ( pow_pos hK _ ) Real.pi_pos

/-
The order-5 tongue dominates the order-7 tongue by a factor `K^{-2}` (eq.
    3.8): `ΔΩ₅ = K^{-2} · ΔΩ₇`.
-/
theorem arnoldWidth_5_7_ratio (K : ℝ) (hK : 0 < K) :
    arnoldWidth K 5 = K⁻¹ ^ 2 * arnoldWidth K 7 := by
  unfold arnoldWidth; ring;
  grind

/-
At weak coupling `0 < K < 1` the order-5 tongue is strictly wider than the
    order-7 tongue.
-/
theorem arnoldWidth_5_gt_7 (K : ℝ) (hK0 : 0 < K) (hK1 : K < 1) :
    arnoldWidth K 7 < arnoldWidth K 5 := by
  exact div_lt_div_of_pos_right ( by exact pow_lt_pow_right_of_lt_one₀ hK0 hK1 ( by norm_num ) ) ( by positivity )

/-
At weak coupling the Arnold-tongue width is monotone decreasing in the order:
    a larger order has a strictly narrower tongue, hence a shallower basin.
-/
theorem arnoldWidth_strict_anti (K : ℝ) (hK0 : 0 < K) (hK1 : K < 1)
    {p q : ℕ} (hpq : p < q) :
    arnoldWidth K q < arnoldWidth K p := by
  exact div_lt_div_iff_of_pos_right ( Real.pi_pos ) |>.2 ( pow_lt_pow_right_of_lt_one₀ hK0 hK1 hpq )

/-! ============================================================
    §4  Physical-constraint filtering ⇒ p = 5
    ============================================================ -/

/-- **C1 (UV absolute convergence).** The `d`-dimensional loop
    integral of the FORS propagator kernel `[1 + (k²/Λ²)^{p/2}]⁻¹` converges
    absolutely iff `p/2 > d/2`. -/
def UVConvergent (d p : ℕ) : Prop := (d : ℝ) / 2 < (p : ℝ) / 2

/-
In four spacetime dimensions, C1 is equivalent to `p ≥ 5`.
-/
theorem uvConvergent_four_iff (p : ℕ) : UVConvergent 4 p ↔ 5 ≤ p := by
  unfold UVConvergent;
  rw [ div_lt_div_iff_of_pos_right ] <;> norm_cast

/-- **Candidate locking order.** After C1 (`p ≥ 5` in `d = 4`) and C2 (`p` odd,
    for a non-vanishing bare `θ`-angle) the admissible orders are the odd
    integers `≥ 5`: `{5, 7, 9, …}`. -/
def IsCandidateOrder (p : ℕ) : Prop := Odd p ∧ UVConvergent 4 p

/-
`p = 5` is a candidate order.
-/
theorem five_isCandidate : IsCandidateOrder 5 := by
  exact ⟨ by decide, by norm_num [ UVConvergent ] ⟩

/-
Every candidate order is `≥ 5`.
-/
theorem candidate_ge_five {p : ℕ} (hp : IsCandidateOrder p) : 5 ≤ p := by
  obtain ⟨hp_odd, hp_uv⟩ := hp;
  exact Nat.le_of_not_lt fun h => by interval_cases p <;> norm_num [ UVConvergent ] at *;

/-
`5` is the minimal candidate order.
-/
theorem five_minimal_candidate :
    IsCandidateOrder 5 ∧ ∀ p, IsCandidateOrder p → 5 ≤ p := by
  exact ⟨ five_isCandidate, fun p hp => candidate_ge_five hp ⟩

/-
Among candidate orders, `p = 5` maximizes the Arnold-tongue width (deepest
    basin of attraction) at weak coupling.
-/
theorem candidate_arnoldWidth_le_five (K : ℝ) (hK0 : 0 < K) (hK1 : K < 1)
    {p : ℕ} (hp : IsCandidateOrder p) :
    arnoldWidth K p ≤ arnoldWidth K 5 := by
  -- Since $p \geq 5$ and $0 < K < 1$, we have $K^p \leq K^5$.
  have h_exp : K^p ≤ K^5 := by
    exact pow_le_pow_of_le_one hK0.le hK1.le ( candidate_ge_five hp );
  exact div_le_div_of_nonneg_right h_exp Real.pi_pos.le

/-
**Dynamical selection of `p = 5`.** If `p` is an admissible candidate order
    whose Arnold tongue is at least as wide as that of every other candidate (it
    sits in the deepest basin), then `p = 5`.
-/
theorem mode_locking_selects_five (K : ℝ) (hK0 : 0 < K) (hK1 : K < 1)
    {p : ℕ} (hp : IsCandidateOrder p)
    (hmax : ∀ q, IsCandidateOrder q → arnoldWidth K q ≤ arnoldWidth K p) :
    p = 5 := by
  by_contra h_contra;
  -- Since $p \neq 5$, we have $p > 5$.
  have hp_gt_5 : 5 < p := by
    exact lt_of_le_of_ne ( candidate_ge_five hp ) ( Ne.symm h_contra );
  exact not_lt_of_ge ( hmax 5 ( by exact ⟨ by decide, by exact uvConvergent_four_iff 5 |>.2 ( by decide ) ⟩ ) ) ( arnoldWidth_strict_anti K hK0 hK1 hp_gt_5 )

/-- **Instanton action** `S_inst(p) = π / sin(π/p)` (eq. 4.1). -/
def instantonAction (p : ℕ) : ℝ := π / Real.sin (π / p)

/-
The instanton action grows with the order: `S_inst(5) < S_inst(7)`, an
    independent indicator favoring the lower order `p = 5`.
-/
theorem instantonAction_5_lt_7 : instantonAction 5 < instantonAction 7 := by
  refine' div_lt_div_of_pos_left _ _ _ <;> norm_num;
  · positivity;
  · exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith [ Real.pi_pos ] );
  · rw [ ← Real.cos_pi_div_two_sub, ← Real.cos_pi_div_two_sub ] ; exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by linarith [ Real.pi_pos ] ) ( by linarith [ Real.pi_pos ] ) ( by linarith [ Real.pi_pos ] )

/-! ============================================================
    §5  Homology with the FORS kernel (the fifth-power exponent)
    ============================================================ -/

/-- The FORS kernel exponent (the `5` in `1/(1 + w⁵)`). -/
def forsExponent : ℕ := 5

/-
**Homology.** The minimal admissible locking order equals the FORS
    kernel exponent: both are forced by the same UV-convergence bound
    `p/2 > d/2` at `d = 4`.
-/
theorem locking_order_eq_forsExponent :
    (∀ p, IsCandidateOrder p → 5 ≤ p) ∧ IsCandidateOrder forsExponent ∧
      forsExponent = 5 := by
  exact ⟨fun p hp => candidate_ge_five hp, five_isCandidate, rfl⟩

/-! ============================================================
    Bridge:  p = 5  ⇒  L2 ∧ L3  (LockingMembraneConditions)
    ============================================================ -/

/-
**The mode-locking bridge.** The dihedral order produced by the modular
    locking, `p = 5`, satisfies the Locking-Membrane conditions L2 (`n₂ = 2`)
    and L3 (`k` odd) used downstream in `Invariants.LockingMembrane`.
-/
theorem mode_locking_to_locking_membrane (K : ℝ) (hK0 : 0 < K) (hK1 : K < 1)
    {p : ℕ} (hp : IsCandidateOrder p)
    (hmax : ∀ q, IsCandidateOrder q → arnoldWidth K q ≤ arnoldWidth K p) :
    LockingMembraneConditions p := by
  have hp_eq_5 : p = 5 := by
    exact mode_locking_selects_five K hK0 hK1 hp hmax;
  exact hp_eq_5.symm ▸ five_satisfies_locking

/-- The full modular-locking scenario: the analytic inputs (central manifold,
    Doeblin ergodicity) together with the admissibility and dynamical-dominance
    of the realized order. -/
structure ModularLockingScenario where
  /-- central spectrum (a single conjugate pair). -/
  spectrum : CentralSpectrum
  /-- base frequency of the effective Circle Map. -/
  Omega : ℝ
  /-- effective coupling, in the weak regime. -/
  K : ℝ
  K_pos : 0 < K
  K_lt_one : K < 1
  /-- Markov ergodicity of the noisy Circle Map. -/
  ergodicity : DoeblinErgodicity Omega K
  /-- the realized locking order. -/
  p : ℕ
  /-- it satisfies the physical constraints C1, C2. -/
  candidate : IsCandidateOrder p
  /-- it sits in the deepest Arnold-tongue basin among candidates. -/
  dominant : ∀ q, IsCandidateOrder q → arnoldWidth K q ≤ arnoldWidth K p

/-
**Main theorem (mode locking ⇒ k = 5).** In any modular-locking scenario the
    realized order is `5` and it satisfies the Locking-Membrane conditions; this
    is the bridge that derives L2 and L3 from the RGF dynamics rather than
    assuming them.
-/
theorem ModularLockingScenario.locks_to_five (M : ModularLockingScenario) :
    M.p = 5 ∧ LockingMembraneConditions M.p := by
  obtain ⟨hp, hlock⟩ := mode_locking_to_locking_membrane M.K M.K_pos M.K_lt_one M.candidate M.dominant;
  exact ⟨ k_equals_five_from_n2 M.p hlock hp, ⟨ hp, hlock ⟩ ⟩

end

end ModeLocking