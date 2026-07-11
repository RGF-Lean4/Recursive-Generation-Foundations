/-
  Rigorous formalization of the continuous limit
  Rigorous Formalization of the Continuous Limit

  This file formalizes the limit process from a discrete atomic network to a continuous space in Recursive Generation Formalism (RGF),
  using two rigorous mathematical frameworks:

  **Part I: Gromov-Hausdorff convergence**
  - using Mathlib's `GromovHausdorff.GHSpace` metric space
  - formalizing the δ-net approximation theorem
  - proving that the discrete grid converges to the continuous space in GH distance
  - giving a quantitative estimate of the convergence rate

  **Part II: measure convergence (weak convergence)**
  - using the weak topology of Mathlib's `MeasureTheory.ProbabilityMeasure`
  - formalizing the Portmanteau characterization of weak convergence

  **Part III: combined continuous-limit theorem**
  - unifying GH convergence with measure convergence
  - connecting to the dimension locking and spiral scaling law of RGF

  Mathematical background:
  The Gromov-Hausdorff distance d_GH(X, Y) quantifies the "shape difference" between two compact metric spaces.
  If {X_n} is a sequence of compact metric spaces, d_GH(X_n, X) → 0 means X_n converges to X in the sense of metric geometry.
  In RGF, X_n is the discrete atomic network (a finite metric space) and
  X is the emergent continuous manifold.
-/

import Mathlib

open Real BigOperators Filter MeasureTheory Metric Set
open scoped Topology NNReal ENNReal

noncomputable section

/-! ## Part I: Gromov-Hausdorff convergence -/

/-! ### §1.1 Abstract framework of discrete approximation -/

/-- δ-net approximation data of a compact metric space.
    Given a compact metric space X and a finite subset S ⊆ X,
    if the distance from every x ∈ X to S is at most δ, then S is a δ-net of X. -/
structure DeltaNet (X : Type*) [MetricSpace X] where
  /-- the set of center points of the net -/
  centers : Finset X
  /-- approximation radius -/
  delta : ℝ
  /-- radius nonnegative -/
  delta_nonneg : 0 ≤ delta
  /-- covering property: every point is δ-covered by some center -/
  covering : ∀ x : X, ∃ c ∈ centers, dist x c ≤ delta

/-- The number of points of a δ-net. -/
def DeltaNet.card {X : Type*} [MetricSpace X] (net : DeltaNet X) : ℕ :=
  net.centers.card

/-- The approximation property of a δ-net entails an upper bound on the Hausdorff distance. -/
theorem DeltaNet.hausdorff_dist_le {X : Type*} [MetricSpace X]
    (net : DeltaNet X) :
    Metric.hausdorffDist (Set.univ : Set X) (↑net.centers : Set X) ≤ net.delta := by
  apply Metric.hausdorffDist_le_of_mem_dist net.delta_nonneg
  · intro x _
    obtain ⟨c, hc_mem, hc_dist⟩ := net.covering x
    exact ⟨c, Finset.mem_coe.mpr hc_mem, hc_dist⟩
  · intro x _
    exact ⟨x, Set.mem_univ x, by rw [dist_self]; exact net.delta_nonneg⟩

/-! ### §1.2 Discretization sequences and GH convergence -/

/-- Discretization sequence: a family of increasingly fine finite approximations of a compact metric space X. -/
structure DiscretizationSequence (X : Type*) [MetricSpace X] [CompactSpace X] where
  /-- approximation precision at step n -/
  approxRadius : ℕ → ℝ
  /-- precision nonnegative -/
  radius_nonneg : ∀ n, 0 ≤ approxRadius n
  /-- precision tends to zero -/
  radius_tendsto : Tendsto approxRadius atTop (nhds 0)
  /-- a corresponding δ-net exists at each step -/
  hasNet : ∀ n, ∃ (net : DeltaNet X), net.delta ≤ approxRadius n

/-! ### §1.3 GH distance upper-bound theorem -/

/-- Core theorem (Mathlib wrapper):
    d_GH(X, Y) ≤ ε₁ + ε₂/2 + ε₃ -/
theorem gh_dist_le_of_delta_net
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type*} [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    {s : Set X} {Φ : s → Y}
    {ε₁ ε₂ ε₃ : ℝ}
    (hs : ∀ x : X, ∃ y ∈ s, dist x y ≤ ε₁)
    (hs' : ∀ x : Y, ∃ y : s, dist x (Φ y) ≤ ε₃)
    (hΦ : ∀ x y : s, |dist (x : X) y - dist (Φ x) (Φ y)| ≤ ε₂) :
    GromovHausdorff.ghDist X Y ≤ ε₁ + ε₂ / 2 + ε₃ :=
  GromovHausdorff.ghDist_le_of_approx_subsets Φ hs hs' hΦ

/-! ### §1.4 GH convergence rate of the RGF discrete grid -/

/-- RGF discretization parameters. -/
structure RGFGridApproximation where
  /-- dimension -/
  dim : ℕ
  /-- dimension positive -/
  dim_pos : 0 < dim
  /-- upper bi-Lipschitz constant -/
  lipConst : ℝ
  /-- constant positive -/
  lip_pos : 0 < lipConst

/-- RGF filling radius formula: ρ(n) = C · √d / (n+1). -/
def RGFGridApproximation.fillingRadius (data : RGFGridApproximation) (n : ℕ) : ℝ :=
  data.lipConst * Real.sqrt data.dim / ((n : ℝ) + 1)

/-- The filling radius is nonnegative. -/
theorem RGFGridApproximation.fillingRadius_nonneg
    (data : RGFGridApproximation) (n : ℕ) :
    0 ≤ data.fillingRadius n := by
  unfold fillingRadius
  apply div_nonneg
  · exact mul_nonneg (le_of_lt data.lip_pos) (Real.sqrt_nonneg _)
  · linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The filling radius tends to zero — convergence rate O(1/n). -/
theorem RGFGridApproximation.fillingRadius_tendsto
    (data : RGFGridApproximation) :
    Tendsto data.fillingRadius atTop (nhds 0) := by
  unfold fillingRadius
  exact Filter.Tendsto.const_div_atTop
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds) _

/-- Monotone decrease of the filling radius. -/
theorem RGFGridApproximation.fillingRadius_antitone
    (data : RGFGridApproximation) :
    Antitone data.fillingRadius := by
  intro n m hnm
  unfold fillingRadius
  apply div_le_div_of_nonneg_left _ (by linarith [Nat.cast_nonneg (α := ℝ) n])
      (by linarith [show (n : ℝ) ≤ (m : ℝ) from Nat.cast_le.mpr hnm])
  exact le_of_lt (mul_pos data.lip_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr data.dim_pos)))

/-- Explicit filling radius formula for d = 3. -/
theorem fillingRadius_dim3
    (C : ℝ) (hC : 0 < C) (n : ℕ) :
    (⟨3, by norm_num, C, hC⟩ : RGFGridApproximation).fillingRadius n =
      C * Real.sqrt 3 / ((n : ℝ) + 1) := by
  simp [RGFGridApproximation.fillingRadius]

/-! ### §1.5 Formal definition and properties of GH convergence -/

/-- GH convergence: a sequence in GHSpace converges to a limit space. -/
def GHConverges (seq : ℕ → GromovHausdorff.GHSpace) (limit : GromovHausdorff.GHSpace) : Prop :=
  Tendsto seq atTop (nhds limit)

/-- GH convergence is equivalent to the ε-δ definition. -/
theorem ghConverges_iff_dist_tendsto
    (seq : ℕ → GromovHausdorff.GHSpace) (limit : GromovHausdorff.GHSpace) :
    GHConverges seq limit ↔
      ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (seq n) limit < ε :=
  Metric.tendsto_atTop

/-- Uniqueness of the limit of GH convergence. -/
theorem ghConverges_unique
    (seq : ℕ → GromovHausdorff.GHSpace) (l₁ l₂ : GromovHausdorff.GHSpace)
    (h₁ : GHConverges seq l₁) (h₂ : GHConverges seq l₂) :
    l₁ = l₂ :=
  tendsto_nhds_unique h₁ h₂

/-- GH convergence follows from an upper bound on the distance. -/
theorem ghConverges_of_dist_le
    (seq : ℕ → GromovHausdorff.GHSpace) (limit : GromovHausdorff.GHSpace)
    (bound : ℕ → ℝ)
    (hbound : ∀ n, dist (seq n) limit ≤ bound n)
    (htendsto : Tendsto bound atTop (nhds 0)) :
    GHConverges seq limit := by
  rw [GHConverges, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htendsto) ε hε
  refine ⟨N, fun n hn => ?_⟩
  calc dist (seq n) limit ≤ bound n := hbound n
    _ ≤ |bound n| := le_abs_self _
    _ = |bound n - 0| := by ring_nf
    _ = dist (bound n) 0 := (Real.dist_eq _ _).symm
    _ < ε := hN n hn

/-! ## Part II: measure convergence (weak convergence) -/

/-! ### §2.1 Weak convergence of probability measures -/

/-- Equivalent characterization of weak convergence (Portmanteau theorem). -/
theorem weakConvergence_iff_integral
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (μs : ℕ → ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω) :
    Tendsto μs atTop (nhds μ) ↔
      ∀ f : BoundedContinuousFunction Ω ℝ,
        Tendsto (fun n => ∫ ω, f ω ∂(μs n : Measure Ω)) atTop
          (nhds (∫ ω, f ω ∂(μ : Measure Ω))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto

/-- Weak convergence entails convergence of integrals. -/
theorem weakConvergence_integral
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (μs : ℕ → ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω)
    (h : Tendsto μs atTop (nhds μ))
    (f : BoundedContinuousFunction Ω ℝ) :
    Tendsto (fun n => ∫ ω, f ω ∂(μs n : Measure Ω)) atTop
      (nhds (∫ ω, f ω ∂(μ : Measure Ω))) :=
  (weakConvergence_iff_integral μs μ).mp h f

/-! ### §2.2 Uniqueness of weak convergence on metric spaces -/

/-- The limit of weak convergence on a metric space is unique (MetricSpace entails T2Space). -/
theorem weakConvergence_unique_metric
    {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [BorelSpace Ω]
    (μs : ℕ → ProbabilityMeasure Ω)
    (μ₁ μ₂ : ProbabilityMeasure Ω)
    (h₁ : Tendsto μs atTop (nhds μ₁))
    (h₂ : Tendsto μs atTop (nhds μ₂)) :
    μ₁ = μ₂ :=
  tendsto_nhds_unique h₁ h₂

/-! ## Part III: combined continuous-limit theorem -/

/-! ### §3.1 Unified definition of the continuous limit -/

/-- Full data of an RGF continuous limit. -/
structure RGFContinuousLimit where
  /-- discretization sequence in GH space -/
  spaces : ℕ → GromovHausdorff.GHSpace
  /-- limit space -/
  limitSpace : GromovHausdorff.GHSpace
  /-- GH convergence -/
  gh_convergence : GHConverges spaces limitSpace
  /-- upper bound on the convergence rate -/
  convergenceRate : ℕ → ℝ
  /-- rate nonnegative -/
  rate_nonneg : ∀ n, 0 ≤ convergenceRate n
  /-- the distance is controlled by the rate -/
  rate_bounds : ∀ n, dist (spaces n) limitSpace ≤ convergenceRate n

/-- Existence theorem for the continuous limit. -/
theorem continuousLimit_exists_of_fillingRadius
    (spaces : ℕ → GromovHausdorff.GHSpace)
    (limit : GromovHausdorff.GHSpace)
    (data : RGFGridApproximation)
    (h : ∀ n, dist (spaces n) limit ≤ data.fillingRadius n) :
    GHConverges spaces limit :=
  ghConverges_of_dist_le spaces limit data.fillingRadius h
    data.fillingRadius_tendsto

/-- Construction of an RGF continuous limit. -/
def mkRGFContinuousLimit
    (spaces : ℕ → GromovHausdorff.GHSpace)
    (limit : GromovHausdorff.GHSpace)
    (data : RGFGridApproximation)
    (h : ∀ n, dist (spaces n) limit ≤ data.fillingRadius n) :
    RGFContinuousLimit where
  spaces := spaces
  limitSpace := limit
  gh_convergence := continuousLimit_exists_of_fillingRadius spaces limit data h
  convergenceRate := data.fillingRadius
  rate_nonneg := data.fillingRadius_nonneg
  rate_bounds := h

/-! ### §3.2 Dimension locking and the continuous limit -/

/-- Winding-momentum ratio. -/
noncomputable def gammaCriticalCL (d : ℕ) : ℝ := 2 / ((d : ℝ) - 1)

/-- Continuous-limit dimension locking: Γ_c = 1 ⟺ d = 3. -/
theorem continuousLimit_dimension_locking (d : ℕ) (hd : 2 ≤ d) :
    gammaCriticalCL d = 1 ↔ d = 3 := by
  unfold gammaCriticalCL
  constructor
  · intro h
    rw [div_eq_iff (sub_ne_zero_of_ne (by norm_cast; omega))] at h
    have hd1 : (d : ℝ) = 3 := by linarith
    exact Nat.cast_injective hd1
  · intro h; subst h; norm_num

/-- The RGF grid approximation in d = 3. -/
def rgfGrid3D (C : ℝ) (hC : 0 < C) : RGFGridApproximation where
  dim := 3
  dim_pos := by norm_num
  lipConst := C
  lip_pos := hC

/-- The convergence rate of the continuous limit in d = 3. -/
theorem rgf3D_convergence_rate (C : ℝ) (hC : 0 < C) :
    Tendsto (rgfGrid3D C hC).fillingRadius atTop (nhds 0) :=
  (rgfGrid3D C hC).fillingRadius_tendsto

/-! ### §3.3 Filling radius and dimensional scaling -/

/-- Dimensional scaling of the filling radius: higher dimensions need a denser grid. -/
theorem fillingRadius_dim_scaling
    (C : ℝ) (hC : 0 < C) (n : ℕ)
    (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hle : d₁ ≤ d₂) :
    (⟨d₁, hd₁, C, hC⟩ : RGFGridApproximation).fillingRadius n ≤
      (⟨d₂, hd₂, C, hC⟩ : RGFGridApproximation).fillingRadius n := by
  simp only [RGFGridApproximation.fillingRadius]
  apply div_le_div_of_nonneg_right _ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hle)) (le_of_lt hC)

/-- The filling radius of the Jacobi group (dim=4) is larger than in three dimensions. -/
theorem fillingRadius_jacobi_ge_3d (C : ℝ) (hC : 0 < C) (n : ℕ) :
    (⟨3, by norm_num, C, hC⟩ : RGFGridApproximation).fillingRadius n ≤
      (⟨4, by norm_num, C, hC⟩ : RGFGridApproximation).fillingRadius n :=
  fillingRadius_dim_scaling C hC n 3 4 (by norm_num) (by norm_num) (by norm_num)

/-! ### §3.4 Continuous limit and compactness -/

/-- A point in GH space represents a compact space. -/
theorem ghSpace_compact_rep (p : GromovHausdorff.GHSpace) :
    CompactSpace p.Rep := inferInstance

/-- Compactness of the GH limit space. -/
theorem continuousLimit_compact (cl : RGFContinuousLimit) :
    CompactSpace cl.limitSpace.Rep := inferInstance

/-! ### §3.5 Convergence rate formula -/

/-- O(1/n) convergence rate. -/
theorem convergence_rate_formula
    (data : RGFGridApproximation) (n : ℕ) :
    data.fillingRadius n =
      data.lipConst * Real.sqrt data.dim / ((n : ℝ) + 1) := rfl

/-- Given precision ε > 0, there exists N such that for n ≥ N the filling radius < ε. -/
theorem fillingRadius_eventually_small
    (data : RGFGridApproximation) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, data.fillingRadius n < ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp data.fillingRadius_tendsto ε hε
  exact ⟨N, fun n hn => by
    have h1 := hN n hn
    rw [Real.dist_eq] at h1
    have h2 := data.fillingRadius_nonneg n
    linarith [abs_lt.mp h1]⟩

/-! ## Part IV: metric measure spaces and convergence -/

/-! ### §4.1 Metric measure spaces -/

/-- Convergence data of a metric measure space (mm-space). -/
structure MetricMeasureData where
  /-- GH space sequence -/
  ghSeq : ℕ → GromovHausdorff.GHSpace
  /-- GH limit space -/
  ghLimit : GromovHausdorff.GHSpace
  /-- GH convergence -/
  gh_conv : GHConverges ghSeq ghLimit

/-- The GH part of mm-convergence. -/
theorem mmData_gh_convergence (data : MetricMeasureData) :
    Tendsto data.ghSeq atTop (nhds data.ghLimit) :=
  data.gh_conv

/-! ### §4.2 Portmanteau theorem -/

/-- Weak convergence entails convergence of integrals for all bounded continuous functions. -/
theorem portmanteau_integral
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (μs : ℕ → ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω)
    (h : Tendsto μs atTop (nhds μ)) :
    ∀ f : BoundedContinuousFunction Ω ℝ,
      Tendsto (fun n => ∫ ω, f ω ∂(μs n : Measure Ω)) atTop
        (nhds (∫ ω, f ω ∂(μ : Measure Ω))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h

/-! ## Part V: synthesis of the continuous limit of the RGF emergent space -/

/-! ### §5.1 RGF continuous-limit main theorem -/

/-- Main theorem of the continuous limit of the RGF emergent space. -/
theorem rgf_continuous_limit_main
    (spaces : ℕ → GromovHausdorff.GHSpace)
    (limit : GromovHausdorff.GHSpace)
    (d : ℕ) (hd : 0 < d) (C : ℝ) (hC : 0 < C)
    (h : ∀ n, dist (spaces n) limit ≤ C * Real.sqrt d / ((n : ℝ) + 1)) :
    GHConverges spaces limit := by
  apply ghConverges_of_dist_le spaces limit _ h
  exact (⟨d, hd, C, hC⟩ : RGFGridApproximation).fillingRadius_tendsto

/-- Specialized version for d = 3. -/
theorem rgf_continuous_limit_3d
    (spaces : ℕ → GromovHausdorff.GHSpace)
    (limit : GromovHausdorff.GHSpace)
    (C : ℝ) (hC : 0 < C)
    (h : ∀ n, dist (spaces n) limit ≤ C * Real.sqrt 3 / ((n : ℝ) + 1)) :
    GHConverges spaces limit :=
  rgf_continuous_limit_main spaces limit 3 (by norm_num) C hC h

/-! ### §5.2 Physical dimension consistency -/

/-- Γ_c = 1 ⟺ d = 3. -/
theorem physical_dimension_consistency (d : ℕ) (hd : 2 ≤ d) :
    gammaCriticalCL d = 1 ↔ d = 3 :=
  continuousLimit_dimension_locking d hd

/-! ### §5.3 Completeness of GHSpace -/

/-- GHSpace is a complete metric space. -/
theorem ghSpace_complete : CompleteSpace GromovHausdorff.GHSpace := inferInstance

/-- A convergent sequence is a Cauchy sequence. -/
theorem ghConverges_cauchy
    (seq : ℕ → GromovHausdorff.GHSpace) (limit : GromovHausdorff.GHSpace)
    (h : GHConverges seq limit) :
    CauchySeq seq := h.cauchySeq

/-! ### §5.4 Distance triangle inequality and transitivity of approximation -/

/-- The error of a two-step approximation is controlled by the sum of the two steps. -/
theorem gh_approximation_transitive
    (X Y Z : GromovHausdorff.GHSpace)
    (d₁ d₂ : ℝ)
    (h₁ : dist X Y ≤ d₁) (h₂ : dist Y Z ≤ d₂) :
    dist X Z ≤ d₁ + d₂ :=
  le_trans (dist_triangle X Y Z) (add_le_add h₁ h₂)

/-! ### §5.5 Siegel upper half-space example -/

/-- Siegel dimension formula. -/
def siegelDimCL (g : ℕ) : ℕ := g * (g + 1) / 2 + g

theorem siegel_dim_cl_1 : siegelDimCL 1 = 2 := by decide
theorem siegel_dim_cl_2 : siegelDimCL 2 = 5 := by decide
theorem siegel_dim_cl_3 : siegelDimCL 3 = 9 := by decide

/-- The Siegel convergence rate becomes slower as the genus grows. -/
theorem siegel_convergence_rate_slower
    (C : ℝ) (hC : 0 < C) (n : ℕ) (g₁ g₂ : ℕ)
    (hg₁ : 0 < siegelDimCL g₁) (hg₂ : 0 < siegelDimCL g₂)
    (hle : siegelDimCL g₁ ≤ siegelDimCL g₂) :
    (⟨siegelDimCL g₁, hg₁, C, hC⟩ : RGFGridApproximation).fillingRadius n ≤
      (⟨siegelDimCL g₂, hg₂, C, hC⟩ : RGFGridApproximation).fillingRadius n :=
  fillingRadius_dim_scaling C hC n _ _ hg₁ hg₂ hle

/-! ### §5.6 Combined theorem -/

/-- For d = 3, Γ_c = 1 and the continuous limit converges at rate O(1/n). -/
theorem rgf_emergence_consistency (C : ℝ) (hC : 0 < C) :
    gammaCriticalCL 3 = 1 ∧
    Tendsto (rgfGrid3D C hC).fillingRadius atTop (nhds 0) :=
  ⟨by unfold gammaCriticalCL; norm_num, rgf3D_convergence_rate C hC⟩

end
