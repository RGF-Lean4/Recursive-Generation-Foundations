/-
# L2L3.AnalyticInputs — internalizing two analytic conditions from exogenous assumptions

`RGF.L2L3Gaps.ModularLockingScenario` treats "Doeblin ergodicity" and "existence of a `C¹`
Hadamard–Perron central manifold" as exogenous inputs. This file downgrades them, as far as
possible, to **machine-checkable consequences** of more primitive structural properties of RGF
(transition-kernel positivity, contraction rate / spectral gap), giving concrete
finite-dimensional / contraction-mapping versions.

## (1) Doeblin ergodicity ⇐ transition-kernel positivity
* `Dist` / `Stochastic`: probability distributions and (column-)stochastic matrices on a
  finite state space.
* `tv`: the ℓ¹ total variation.
* `Doeblin`: the Doeblin minorization condition.
* `doeblin_contraction_diff` / `doeblin_contraction`: minorization directly gives an ℓ¹
  contraction (with rate `1−ε`).
* `stationary_unique`: the invariant distribution is unique.
* `geometric_convergence`: any initial distribution converges geometrically to the invariant one.
* `stationary_exists`: the invariant distribution exists (as the Cauchy limit from contraction).
* `posKernel_doeblin`: a strictly positive stochastic kernel automatically satisfies Doeblin
  (so ergodicity becomes a consequence of kernel positivity).

## (2) Hadamard–Perron central manifold ⇐ normal contraction rate (spectral gap)
* `graphTransform`: the graph transform `(Ψh)(x) = λ·h(φ⁻¹x) + g(φ⁻¹x)`.
* `graphTransform_contracting`: when `|λ| < 1` the graph transform is a contraction mapping.
* `center_manifold_exists_unique`: the invariant manifold (fixed point of the graph transform)
  exists and is unique.
* `center_manifold_invariance`: the fixed point satisfies the invariance equation
  `h(φx) = λ·h(x) + g(x)`.
-/

import Mathlib

open scoped BigOperators
open Matrix

namespace RGF.L2L3.AnalyticInputs

noncomputable section

/-! ============================================================
    (1) Doeblin ergodicity ⇐ transition-kernel positivity
    ============================================================ -/

/-- A probability distribution on the finite state space `Fin n`. -/
structure Dist (n : ℕ) where
  /-- Probability mass function. -/
  p : Fin n → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ i, 0 ≤ p i
  /-- Normalization. -/
  sum_one : ∑ i, p i = 1

/-- A (column-)stochastic matrix: each column is nonnegative and sums to 1, so its action on a
    distribution stays a distribution. -/
structure Stochastic (n : ℕ) where
  /-- Transition-kernel matrix. -/
  P : Matrix (Fin n) (Fin n) ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ i j, 0 ≤ P i j
  /-- Column sums equal 1. -/
  col_sum_one : ∀ j, ∑ i, P i j = 1

/-- The ℓ¹ total-variation distance. -/
def tv {n : ℕ} (μ ν : Fin n → ℝ) : ℝ := ∑ i, |μ i - ν i|

/-- Total variation is nonnegative. -/
theorem tv_nonneg {n : ℕ} (μ ν : Fin n → ℝ) : 0 ≤ tv μ ν :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-
Total variation is zero if and only if the two distributions are equal.
-/
theorem tv_eq_zero_iff {n : ℕ} (μ ν : Fin n → ℝ) : tv μ ν = 0 ↔ μ = ν := by
  constructor <;> intro h <;> simp_all +decide [ funext_iff, tv ];
  exact fun i => sub_eq_zero.mp ( abs_eq_zero.mp ( by rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _ ] at h; aesop ) )

/-
The action of a stochastic matrix on a distribution preserves nonnegativity.
-/
theorem stochastic_mulVec_nonneg {n : ℕ} (S : Stochastic n) (μ : Dist n) (i : Fin n) :
    0 ≤ S.P.mulVec μ.p i := by
  simpa only [ zero_le, Matrix.mulVec, dotProduct ] using Finset.sum_nonneg fun j _ => mul_nonneg ( S.nonneg i j ) ( μ.nonneg j )

/-
The action of a stochastic matrix on a distribution preserves normalization.
-/
theorem stochastic_mulVec_sum_one {n : ℕ} (S : Stochastic n) (μ : Dist n) :
    ∑ i, S.P.mulVec μ.p i = 1 := by
  simp +decide [ Matrix.mulVec, dotProduct ];
  rw [ Finset.sum_comm ];
  simp +decide [ ← Finset.sum_mul, S.col_sum_one, μ.sum_one ]

/-- The action of a stochastic matrix on a distribution is again a distribution. -/
def Stochastic.apply {n : ℕ} (S : Stochastic n) (μ : Dist n) : Dist n where
  p := S.P.mulVec μ.p
  nonneg := stochastic_mulVec_nonneg S μ
  sum_one := stochastic_mulVec_sum_one S μ

/-- The Doeblin minorization condition: there exist `ε > 0` and a distribution `q` such that the
    kernel is everywhere bounded below by `ε·q`. -/
def Doeblin {n : ℕ} (S : Stochastic n) (ε : ℝ) (q : Fin n → ℝ) : Prop :=
  0 < ε ∧ (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧ ∀ i j, ε * q i ≤ S.P i j

/-
The Doeblin constant automatically satisfies `ε ≤ 1`.
-/
theorem Doeblin.eps_le_one {n : ℕ} {S : Stochastic n} {ε : ℝ} {q : Fin n → ℝ}
    (hn : 0 < n) (hD : Doeblin S ε q) : ε ≤ 1 := by
  cases hD;
  rename_i h₁ h₂; have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h₂.2.2 i ⟨ 0, hn ⟩ ; simp_all +decide [ ← Finset.mul_sum _ _ _, S.col_sum_one ] ;

/-
**`doeblin_contraction_diff`.** For any zero-mass perturbation `δ` (`∑ δ = 0`), the action of
    the kernel contracts in ℓ¹ with rate `1 − ε`.
-/
theorem doeblin_contraction_diff {n : ℕ} (S : Stochastic n) {ε : ℝ} {q : Fin n → ℝ}
    (hD : Doeblin S ε q) (δ : Fin n → ℝ) (hδ : ∑ i, δ i = 0) :
    ∑ i, |S.P.mulVec δ i| ≤ (1 - ε) * ∑ i, |δ i| := by
  -- For any fixed i, we can apply the Doeblin condition to get:
  have h_bound : ∀ i, |(S.P.mulVec δ) i| ≤ ∑ j, (S.P i j - ε * q i) * |δ j| := by
    intros i
    have h_bound_i : |(S.P.mulVec δ) i| ≤ ∑ j, (S.P i j - ε * q i) * |δ j| := by
      have h_sum : (S.P.mulVec δ) i = ∑ j, (S.P i j - ε * q i) * δ j := by
        simp +decide [ sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum _ _ _, hδ ];
        rfl
      rw [ h_sum ];
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun j _ => by rw [ abs_mul, abs_of_nonneg ( sub_nonneg.mpr <| hD.2.2.2 i j ) ] );
    exact h_bound_i;
  refine' le_trans ( Finset.sum_le_sum fun i _ => h_bound i ) _;
  rw [ Finset.sum_comm ];
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hD.2.2.1 ];
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by rw [ S.col_sum_one ] ;

/-
**`doeblin_contraction`.** Minorization directly gives an ℓ¹ contraction:
    `tv(Pμ, Pν) ≤ (1−ε)·tv(μ, ν)`.
-/
theorem doeblin_contraction {n : ℕ} (S : Stochastic n) {ε : ℝ} {q : Fin n → ℝ}
    (hD : Doeblin S ε q) (μ ν : Dist n) :
    tv (S.apply μ).p (S.apply ν).p ≤ (1 - ε) * tv μ.p ν.p := by
  -- Apply the Doeblin contraction theorem to the difference of the distributions.
  have h_diff : ∑ i, |(S.P.mulVec (μ.p - ν.p)) i| ≤ (1 - ε) * ∑ i, |μ.p i - ν.p i| := by
    convert doeblin_contraction_diff S hD ( μ.p - ν.p ) _ using 1;
    simp +decide [ μ.sum_one, ν.sum_one ];
  unfold tv;
  unfold Stochastic.apply; simp_all +decide [ Matrix.mulVec_sub ] ;

/-- An invariant (stationary) distribution: preserved by the action of the kernel. -/
def IsStationary {n : ℕ} (S : Stochastic n) (π : Dist n) : Prop := S.apply π = π

/-
**`stationary_unique`.** Under the Doeblin condition the invariant distribution is unique.
-/
theorem stationary_unique {n : ℕ} (S : Stochastic n) {ε : ℝ} {q : Fin n → ℝ}
    (hD : Doeblin S ε q) (π₁ π₂ : Dist n)
    (h1 : IsStationary S π₁) (h2 : IsStationary S π₂) : π₁.p = π₂.p := by
  convert tv_eq_zero_iff _ _ |>.1 _;
  have h_contraction : tv (S.apply π₁).p (S.apply π₂).p ≤ (1 - ε) * tv π₁.p π₂.p :=
    doeblin_contraction S hD π₁ π₂
  rw [ h1, h2 ] at h_contraction;
  nlinarith [ hD.1, tv_nonneg π₁.p π₂.p ]

/-
**`geometric_convergence`.** Any initial distribution converges geometrically to the invariant
    distribution under iteration of the kernel: `tv(Pᵐμ, π) ≤ (1−ε)ᵐ·tv(μ, π)`.
-/
theorem geometric_convergence {n : ℕ} (hn : 0 < n) (S : Stochastic n) {ε : ℝ}
    {q : Fin n → ℝ} (hD : Doeblin S ε q) (μ π : Dist n) (hπ : IsStationary S π)
    (m : ℕ) :
    tv ((S.apply)^[m] μ).p π.p ≤ (1 - ε) ^ m * tv μ.p π.p := by
  induction' m with m ih generalizing μ;
  · norm_num;
  · convert le_trans _ ( mul_le_mul_of_nonneg_left ( ih μ ) ( sub_nonneg.mpr ( Doeblin.eps_le_one hn hD ) ) ) using 1;
    · ring;
    · convert doeblin_contraction S hD ( S.apply^[m] μ ) π using 1;
      rw [ Function.iterate_succ_apply', hπ ]

/-
**`stationary_exists`.** Under the Doeblin condition the invariant distribution exists (as the
    Cauchy limit obtained from contraction).
-/
theorem stationary_exists {n : ℕ} (hn : 0 < n) (S : Stochastic n) {ε : ℝ}
    {q : Fin n → ℝ} (hD : Doeblin S ε q) : ∃ π : Dist n, IsStationary S π := by
  -- Let μ₀ : Dist n be the uniform distribution: p i = (n:ℝ)⁻¹ (nonneg; sum = n·n⁻¹ = 1 since n>0).
  set μ₀ : Dist n := ⟨fun _ => (n : ℝ)⁻¹, by
    exact fun _ => by positivity;, by
    simp +decide [ hn.ne' ]⟩
  generalize_proofs at *; (
  -- For the uniform distribution μ₀, the ℓ¹ distance between consecutive iterates is bounded by a geometric series.
  have h_bound : ∀ m, tv ((S.apply)^[m] μ₀).p ((S.apply)^[m+1] μ₀).p ≤ (1 - ε) ^ m * tv μ₀.p (S.apply μ₀).p := by
    intro m; induction' m with m ih <;> simp_all +decide [ pow_succ', mul_assoc, Function.iterate_succ_apply' ] ;
    refine' le_trans ( doeblin_contraction S hD _ _ ) ( mul_le_mul_of_nonneg_left ih _ );
    linarith [ Doeblin.eps_le_one hn hD ]
  generalize_proofs at *; (
  -- By the properties of the ℓ¹ norm and the geometric series, the sequence of iterates converges to a limit L.
  obtain ⟨L, hL⟩ : ∃ L : Fin n → ℝ, Filter.Tendsto (fun m => (S.apply)^[m] μ₀ |>.p) Filter.atTop (nhds L) := by
    refine' cauchySeq_tendsto_of_complete _;
    fapply cauchySeq_of_le_geometric;
    exact 1 - ε
    exact tv μ₀.p ( S.apply μ₀ ).p
    exact sub_lt_self _ hD.1
    intro m
    have := h_bound m
    simp_all +decide [ dist_eq_norm, Pi.norm_def ];
    refine' le_trans _ ( h_bound m ) |> le_trans <| by rw [ mul_comm ] ;
    rcases n with ( _ | _ | n ) <;> norm_num [ Finset.sup_const ] at *;
    · simp +decide [ Fin.eq_zero, tv ];
    · rw [ show ( Finset.univ.sup fun b => ‖ ( S.apply^[m] μ₀ ).p b - ( S.apply^[m] ( S.apply μ₀ ) ).p b‖₊ ) = ‖ ( S.apply^[m] μ₀ ).p ( Classical.choose ( Finset.exists_max_image Finset.univ ( fun b => ‖ ( S.apply^[m] μ₀ ).p b - ( S.apply^[m] ( S.apply μ₀ ) ).p b‖₊ ) ⟨ 0, Finset.mem_univ 0 ⟩ ) ) - ( S.apply^[m] ( S.apply μ₀ ) ).p ( Classical.choose ( Finset.exists_max_image Finset.univ ( fun b => ‖ ( S.apply^[m] μ₀ ).p b - ( S.apply^[m] ( S.apply μ₀ ) ).p b‖₊ ) ⟨ 0, Finset.mem_univ 0 ⟩ ) )‖₊ from ?_ ];
      · exact Finset.single_le_sum ( fun i _ => abs_nonneg ( ( S.apply^[m] μ₀ ).p i - ( S.apply^[m] ( S.apply μ₀ ) ).p i ) ) ( Finset.mem_univ _ );
      · exact le_antisymm ( Finset.sup_le fun i _ => Classical.choose_spec ( Finset.exists_max_image Finset.univ ( fun b => ‖ ( S.apply^[m] μ₀ ).p b - ( S.apply^[m] ( S.apply μ₀ ) ).p b‖₊ ) ⟨ 0, Finset.mem_univ 0 ⟩ ) |>.2 i ( Finset.mem_univ i ) ) ( Finset.le_sup ( f := fun b => ‖ ( S.apply^[m] μ₀ ).p b - ( S.apply^[m] ( S.apply μ₀ ) ).p b‖₊ ) ( Finset.mem_univ _ ) )
  generalize_proofs at *; (
  -- The limit L is a distribution since it is the limit of distributions.
  have hL_dist : ∃ π : Dist n, π.p = L := by
    refine' ⟨ ⟨ L, _, _ ⟩, rfl ⟩;
    · exact fun i => le_of_tendsto_of_tendsto' tendsto_const_nhds ( tendsto_pi_nhds.mp hL i ) fun m => ( S.apply^[m] μ₀ ).nonneg i;
    · refine' tendsto_nhds_unique ( tendsto_finset_sum _ fun i _ => tendsto_pi_nhds.mp hL i ) _;
      exact tendsto_const_nhds.congr fun m => by rw [ show ∑ c : Fin n, ( S.apply^[m] μ₀ |> Dist.p ) c = 1 from by exact Nat.recOn m ( by aesop ) fun m ih => by simpa [ Function.iterate_succ_apply' ] using stochastic_mulVec_sum_one S ( S.apply^[m] μ₀ ) ] ;
  generalize_proofs at *; (
  obtain ⟨ π, hπ ⟩ := hL_dist; use π; simp_all +decide [ IsStationary ] ;
  -- By the continuity of the map $y \mapsto S.P.mulVec y$, we have $S.P.mulVec L = L$.
  have h_cont : S.P.mulVec L = L := by
    refine' tendsto_nhds_unique _ hL
    generalize_proofs at *; (
    rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ] ; convert Filter.Tendsto.comp ( Continuous.tendsto ( show Continuous fun x : Fin n → ℝ => S.P.mulVec x from continuous_const.matrix_mulVec continuous_id' ) _ ) hL using 2 ; simp +decide [ Function.iterate_succ_apply', Stochastic.apply ] ;)
  generalize_proofs at *; (
  unfold Stochastic.apply; aesop;)))))

/-
**`posKernel_doeblin`.** A strictly positive (column-)stochastic kernel automatically satisfies
    the Doeblin condition (taking the uniform distribution `q` and `ε = n·(minimum entry)`); thus
    "ergodicity" becomes a consequence of "kernel positivity".
-/
theorem posKernel_doeblin {n : ℕ} (hn : 0 < n) (S : Stochastic n)
    (hpos : ∀ i j, 0 < S.P i j) : ∃ (ε : ℝ) (q : Fin n → ℝ), Doeblin S ε q := by
  -- Let $m$ be the minimum of $S.P$ over all pairs $(i, j)$.
  obtain ⟨m, hm⟩ : ∃ m, m ∈ Set.range (fun p : Fin n × Fin n => S.P p.1 p.2) ∧ ∀ p ∈ Set.range (fun p : Fin n × Fin n => S.P p.1 p.2), m ≤ p := by
    exact ⟨ Finset.min' ( Set.toFinset ( Set.range fun p : Fin n × Fin n => S.P p.1 p.2 ) ) ⟨ _, Set.mem_toFinset.mpr ( Set.mem_range_self ( ⟨ ⟨ 0, hn ⟩, ⟨ 0, hn ⟩ ⟩ : Fin n × Fin n ) ) ⟩, Set.mem_toFinset.mp ( Finset.min'_mem _ _ ), fun p hp => Finset.min'_le _ _ ( Set.mem_toFinset.mpr hp ) ⟩;
  refine' ⟨ n * m, fun _ => 1 / n, _, _, _, _ ⟩ <;> simp_all +decide [ hn.ne', mul_comm ];
  · exact hm.1.choose_spec.choose_spec ▸ hpos _ _;
  · exact fun i j => hm.2 _ _ _ rfl

/-! ============================================================
    (2) Hadamard–Perron central manifold ⇐ normal contraction rate (spectral gap)
    ============================================================

    Take a finite state space `X`, an invertible dynamics `φ : Equiv.Perm X` on it, normal fiber
    `ℝ`, and normal contraction rate `λ` (`|λ| < 1`, i.e. a spectral gap). The central manifold
    `h : X → ℝ` is the fixed point of the graph transform. `X → ℝ` is a complete metric space
    under the supremum norm, the graph transform is a contraction mapping, hence the fixed point
    exists and is unique. -/

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The graph transform `(Ψh)(x) = λ·h(φ⁻¹x) + g(φ⁻¹x)`. -/
def graphTransform (lam : ℝ) (φ : Equiv.Perm X) (g : X → ℝ) (h : X → ℝ) : X → ℝ :=
  fun x => lam * h (φ.symm x) + g (φ.symm x)

/-
Precomposition with a bijection preserves the supremum norm.
-/
omit [DecidableEq X] [Nonempty X] in
theorem norm_comp_perm (φ : Equiv.Perm X) (f : X → ℝ) :
    ‖fun x => f (φ.symm x)‖ = ‖f‖ := by
  refine' le_antisymm ( _ ) ( _ );
  · exact pi_norm_le_iff_of_nonneg ( norm_nonneg _ ) |>.2 fun x => pi_norm_le_iff_of_nonneg ( norm_nonneg _ ) |>.1 ( le_rfl ) ( φ.symm x );
  · convert pi_norm_le_iff_of_nonneg ( norm_nonneg _ ) |>.2 _;
    exact fun x => norm_le_pi_norm ( fun x => f ( φ.symm x ) ) ( φ x ) |> le_trans ( by simp +decide )

/-
**`graphTransform_contracting`.** When `|λ| < 1` the graph transform is a contraction mapping
    (with contraction constant `|λ|`).
-/
omit [DecidableEq X] [Nonempty X] in
theorem graphTransform_contracting (lam : ℝ) (hlam : |lam| < 1) (φ : Equiv.Perm X)
    (g : X → ℝ) :
    ContractingWith (Real.toNNReal |lam|) (graphTransform lam φ g) := by
  refine' ⟨ _, _ ⟩;
  · rw [ ← NNReal.coe_lt_coe ] ; aesop;
  · rw [ lipschitzWith_iff_dist_le_mul ];
    intro x y; simp +decide [ dist_eq_norm ] ; ring_nf;
    convert norm_smul_le lam ( fun i => ( x - y ) ( φ.symm i ) ) |> le_trans <| mul_le_mul_of_nonneg_left ( norm_comp_perm φ ( x - y ) |> le_of_eq ) ( abs_nonneg lam ) using 1 ; simp +decide ; ring!;
    exact congr_arg Norm.norm ( by ext; simp +decide [ graphTransform ] ; ring )

/-
**`center_manifold_exists_unique`.** The central manifold (fixed point of the graph transform)
    exists and is unique.
-/
omit [DecidableEq X] [Nonempty X] in
theorem center_manifold_exists_unique (lam : ℝ) (hlam : |lam| < 1)
    (φ : Equiv.Perm X) (g : X → ℝ) :
    ∃! h : X → ℝ, graphTransform lam φ g h = h := by
  have h_contracting : ContractingWith (Real.toNNReal |lam|) (graphTransform lam φ g) :=
    graphTransform_contracting lam hlam φ g
  refine ⟨h_contracting.fixedPoint _, h_contracting.fixedPoint_isFixedPt, ?_⟩
  exact fun y hy => h_contracting.fixedPoint_unique' hy h_contracting.fixedPoint_isFixedPt

/-
**`center_manifold_invariance`.** The central-manifold fixed point satisfies the invariance
    equation `h(φx) = λ·h(x) + g(x)`.
-/
omit [Fintype X] [DecidableEq X] [Nonempty X] in
theorem center_manifold_invariance (lam : ℝ) (φ : Equiv.Perm X) (g h : X → ℝ)
    (hfix : graphTransform lam φ g h = h) (x : X) :
    h (φ x) = lam * h x + g x := by
  have := congr_fun hfix ( φ x ) ; simp_all +decide [ graphTransform ] ;

end

end RGF.L2L3.AnalyticInputs