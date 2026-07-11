/-
  RGF/ConformalFieldTheory.lean

  Task V — Conformal field theory and the central charge: the Virasoro central
  extension, the (super)conformal anomaly of the Polyakov path integral, and the
  categorical *locking* of the critical dimension `D = 10`.

  ## What is proved here (all `sorry`-free)

  1. **The Virasoro algebra as the central extension of the Witt algebra.**
     We record the Witt structure constants `[L m, L n] = (m - n) L (m+n)` and
     prove the Jacobi identity for them (`witt_jacobi`).  We then define the
     Gelfand–Fuks 2-cocycle
     `ω(L m, L n) = (c/12) (m³ - m) δ_{m+n,0}`,
     prove it is antisymmetric (`virCocycle_antisymm`), that it satisfies the
     Lie-algebra **2-cocycle condition** (`virCocycle_cocycle`) — so it really
     defines a central extension — and that for `c ≠ 0` it is **not a
     coboundary** (`virCocycle_not_coboundary`).  The last fact is the
     Gelfand–Fuks statement that the Virasoro algebra is a *nontrivial* central
     extension of the Witt algebra: the central charge is a genuine cohomology
     invariant, not an artefact of a change of basis.

  2. **ζ-function regularization of functional determinants.**  A fully rigorous
     `det Δ = exp(-ζ'_Δ(0))` for an unbounded Laplacian on a curved worldsheet
     requires analytic continuation of the spectral zeta series and the
     Seeley–DeWitt heat-kernel expansion, which are open frontier problems for
     Lean.  What *is* rigorous — and what we prove — is the identity in the
     convergent (finite-spectrum) case: for a positive spectrum `λs`,
     `zetaLogDet λs = Σ log λ = log (∏ λ)` (`zetaLogDet_eq`,
     `zetaLogDet_eq_log_prod`).  This is the honest core of the
     ζ-regularization prescription (the analytic backbone it needs in the
     divergent case is the constructive analysis of `ConstructiveODE.lean`).

  3. **The (super)conformal Weyl anomaly and the critical dimension.**  The
     central charge is additive over the decoupled sectors of the path integral
     (`totalCharge_append`).  Assembling the superstring Polyakov sectors
     — `D` free bosons `(+D)`, `D` worldsheet Majorana fermions `(+D/2)`, the
     reparametrization `b,c` ghosts `(-26)` and the superconformal `β,γ` ghosts
     `(+11)` — gives the total conformal anomaly `cTotal D = 3/2·D − 15`
     (`polyakov_totalCharge`, `cTotal_eq`).  Weyl invariance at the quantum level
     is the vanishing of this anomaly, which forces exactly `D = 10`
     (`weyl_anomaly_cancellation`).

  4. **Categorical locking of `D = 10`.**  The Weyl renormalization flow
     `weylStep D = D − (2/3)·cTotal D` is a generative dynamical system
     (`weylFlowSys : RGF.GenCat.GenSys`) whose *only* fixed point — its locked
     membrane / categorical limit — is `D = 10` (`weylFlow_membraneLocked`,
     `membraneLocked_dimension_eq_ten`).  Thus the categorical *membrane locking*
     of `GenerativeDynamicalCategory.lean` pins the matter dimension to `10`.

  ## A note on the originally proposed formula (reference opinion adopted)

  The task originally proposed proving
  `total_central_charge = D_matter * (1 + 1/2) - 26`.
  As spelled out in the reference opinion, that expression is arithmetically
  inconsistent with `D = 10`: its unique root is `D = 52/3 ≈ 17.33`, *not* `10`
  (see `totalChargeNaive` and `naive_root` below, which we keep and prove so the
  discrepancy is documented rather than hidden).  The reason is that it omits the
  `+11` contribution of the superconformal `β,γ` ghosts required by a genuine
  super-Weyl-invariant Polyakov path integral.  Forcing a `10` out of the naive
  expression would be "number fudging".  We therefore *adopt the reference
  opinion*: the honest accounting `cTotal D = c_matter + c_ghost =
  (D + D/2) + (−26 + 11) = 3/2·D − 15` is used throughout, and it is this
  physically correct anomaly that vanishes precisely at `D = 10`.
-/

import Mathlib
import RGF.Math.Category.GenerativeDynamicalCategory
import RGF.Math.Analysis.ConstructiveODE

namespace RGF.CFT

open RGF.GenCat

/-! ## 1. The Witt algebra structure constants and the Jacobi identity -/

/-- Structure constant of the Witt algebra (Lie algebra of polynomial vector
    fields on the circle): `[L m, L n] = wittCoeff m n • L (m + n)` with
    `wittCoeff m n = m - n`. -/
def wittCoeff (m n : ℤ) : ℤ := m - n

@[simp] theorem wittCoeff_def (m n : ℤ) : wittCoeff m n = m - n := rfl

/-- The Witt bracket is antisymmetric. -/
theorem witt_antisymm (m n : ℤ) : wittCoeff m n = - wittCoeff n m := by
  simp [wittCoeff]

/-- **Jacobi identity for the Witt structure constants.**  The `L (m+n+p)`
    coefficient of `[[L m, L n], L p] + [[L n, L p], L m] + [[L p, L m], L n]`
    vanishes. -/
theorem witt_jacobi (m n p : ℤ) :
    wittCoeff m n * wittCoeff (m + n) p
      + wittCoeff n p * wittCoeff (n + p) m
      + wittCoeff p m * wittCoeff (p + m) n = 0 := by
  simp only [wittCoeff]; ring

/-! ## 2. The Virasoro central extension (the Gelfand–Fuks 2-cocycle) -/

/-- The Gelfand–Fuks 2-cocycle defining the Virasoro central extension of the
    Witt algebra with central charge `c`:
    `ω(L m, L n) = (c / 12) · (m³ − m) · δ_{m+n,0}`. -/
def virCocycle (c : ℚ) (m n : ℤ) : ℚ :=
  (c / 12) * ((m ^ 3 - m : ℤ) : ℚ) * (if m + n = 0 then 1 else 0)

/-- **Antisymmetry of the Virasoro cocycle**: `ω(L m, L n) = − ω(L n, L m)`. -/
theorem virCocycle_antisymm (c : ℚ) (m n : ℤ) :
    virCocycle c m n = - virCocycle c n m := by
  unfold virCocycle
  by_cases h : m + n = 0
  · have hn : n = -m := by omega
    subst hn
    have h2 : (-m) + m = 0 := by omega
    simp only [h, h2, if_true]
    push_cast
    ring
  · have h' : n + m ≠ 0 := by omega
    simp [h, h']

/-- **The Virasoro cocycle satisfies the Lie-algebra 2-cocycle condition**, so it
    defines a central extension: the central coefficient of the Jacobiator
    vanishes,
    `(m−n)·ω(m+n,p) + (n−p)·ω(n+p,m) + (p−m)·ω(p+m,n) = 0`. -/
theorem virCocycle_cocycle (c : ℚ) (m n p : ℤ) :
    (wittCoeff m n : ℚ) * virCocycle c (m + n) p
      + (wittCoeff n p : ℚ) * virCocycle c (n + p) m
      + (wittCoeff p m : ℚ) * virCocycle c (p + m) n = 0 := by
  unfold virCocycle wittCoeff
  by_cases h : m + n + p = 0
  · have h1 : (m + n) + p = 0 := by omega
    have h2 : (n + p) + m = 0 := by omega
    have h3 : (p + m) + n = 0 := by omega
    have hp : p = -(m + n) := by omega
    subst hp
    simp only [h1, h2, h3, if_true]
    push_cast
    ring
  · have h1 : (m + n) + p ≠ 0 := by omega
    have h2 : (n + p) + m ≠ 0 := by omega
    have h3 : (p + m) + n ≠ 0 := by omega
    simp [h1, h2, h3]

/-- A 2-cochain `β` on the Witt algebra is a **coboundary** if it is the
    Lie-algebra differential of a 1-cochain `φ : ℤ → ℚ`, i.e.
    `β m n = (m − n) · φ (m + n)`. -/
def IsCoboundary (β : ℤ → ℤ → ℚ) : Prop :=
  ∃ φ : ℤ → ℚ, ∀ m n, β m n = (wittCoeff m n : ℚ) * φ (m + n)

/-- **The Virasoro cocycle is nontrivial** (Gelfand–Fuks): for `c ≠ 0` it is not
    a coboundary, so the central charge is a genuine cohomology invariant. -/
theorem virCocycle_not_coboundary {c : ℚ} (hc : c ≠ 0) :
    ¬ IsCoboundary (virCocycle c) := by
  rintro ⟨φ, hφ⟩
  have e1 := hφ 1 (-1)
  have e2 := hφ 2 (-2)
  simp only [virCocycle, wittCoeff] at e1 e2
  norm_num at e1 e2
  -- e1 : φ 0 = 0 (up to arrangement); e2 : c / 2 = 4 * φ 0
  rw [e1] at e2
  norm_num at e2
  exact hc e2

/-! ## 3. ζ-function regularization of functional determinants

The Polyakov path integral quantizes the two-dimensional worldsheet metric; the
one-loop measure is a ratio of functional determinants of Laplace-type operators
(the reparametrization ghost operator over the scalar Laplacian).  The rigorous
definition of such a determinant is via ζ-regularization,
`log det Δ = − ζ'_Δ(0)`.  For a genuinely infinite spectrum this needs analytic
continuation of `ζ_Δ(s) = Σ λ⁻ˢ` and the Seeley–DeWitt heat-kernel expansion.
Here we establish the identity in the convergent case (a finite spectrum), which
is the honest content of the prescription; the divergent case rests on the
constructive-analysis backbone of `ConstructiveODE.lean`. -/

/-- One spectral term `λ⁻ˢ = exp(−s · log λ)`. -/
noncomputable def zetaTerm (l s : ℝ) : ℝ := Real.exp (-s * Real.log l)

/-- Spectral zeta function of a finite spectrum `λs`: `ζ(s) = Σ λ⁻ˢ`. -/
noncomputable def specZeta (ls : List ℝ) (s : ℝ) : ℝ :=
  (ls.map (fun l => zetaTerm l s)).sum

/-- The ζ-regularized log-determinant `log det = − ζ'(0)`. -/
noncomputable def zetaLogDet (ls : List ℝ) : ℝ := - deriv (specZeta ls) 0

/-- Derivative of a single spectral term. -/
theorem zetaTerm_hasDerivAt (l s : ℝ) :
    HasDerivAt (zetaTerm l) (-(Real.log l) * Real.exp (-s * Real.log l)) s := by
  have h : HasDerivAt (fun s : ℝ => -s * Real.log l) (-(Real.log l)) s := by
    simpa using ((hasDerivAt_id s).neg.mul_const (Real.log l))
  have h2 : HasDerivAt (zetaTerm l)
      (Real.exp (-s * Real.log l) * -(Real.log l)) s := h.exp
  rw [mul_comm] at h2
  exact h2

/-- Derivative of the (finite) spectral zeta function. -/
theorem specZeta_hasDerivAt (ls : List ℝ) (s : ℝ) :
    HasDerivAt (specZeta ls)
      ((ls.map (fun l => -(Real.log l) * Real.exp (-s * Real.log l))).sum) s := by
  induction ls with
  | nil => simpa [specZeta] using (hasDerivAt_const s (0 : ℝ))
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (zetaTerm_hasDerivAt a s).add ih

/-- **ζ-regularization gives the sum of the log-eigenvalues** (finite spectrum):
    `zetaLogDet λs = Σ log λ`. -/
theorem zetaLogDet_eq (ls : List ℝ) :
    zetaLogDet ls = (ls.map Real.log).sum := by
  rw [zetaLogDet, (specZeta_hasDerivAt ls 0).deriv]
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  induction ls with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [neg_add, ih]; ring

/-- For a positive spectrum, the ζ-regularized log-determinant is the log of the
    product of the eigenvalues — i.e. the honest `log det`. -/
theorem zetaLogDet_eq_log_prod (ls : List ℝ) (hpos : ∀ l ∈ ls, 0 < l) :
    zetaLogDet ls = Real.log ls.prod := by
  rw [zetaLogDet_eq]
  induction ls with
  | nil => simp
  | cons a t ih =>
      have ha : 0 < a := hpos a (by simp)
      have ht : ∀ l ∈ t, 0 < l := fun l hl => hpos l (by simp [hl])
      have htp : 0 < t.prod := List.prod_pos ht
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [ih ht, Real.log_mul (ne_of_gt ha) (ne_of_gt htp)]

/-! ## 4. The (super)conformal Weyl anomaly and the critical dimension -/

/-- Matter central charge of `D` bosonic string coordinates (each free boson
    contributes `+1`). -/
def cMatterBoson (D : ℚ) : ℚ := D

/-- Matter central charge of the `D` worldsheet Majorana fermions (the
    superpartners): each free fermion contributes `+1/2`. -/
def cMatterFermion (D : ℚ) : ℚ := D / 2

/-- Reparametrization (`b, c`) ghost central charge. -/
def cGhostBC : ℚ := -26

/-- Superconformal (`β, γ`) ghost central charge. -/
def cGhostBetaGamma : ℚ := 11

/-- **Total (super)conformal central charge** = matter + ghosts. -/
def cTotal (D : ℚ) : ℚ :=
  cMatterBoson D + cMatterFermion D + cGhostBC + cGhostBetaGamma

/-- The honest anomaly is `cTotal D = 3/2·D − 15`. -/
theorem cTotal_eq (D : ℚ) : cTotal D = 3 / 2 * D - 15 := by
  unfold cTotal cMatterBoson cMatterFermion cGhostBC cGhostBetaGamma
  ring

/-- **Weyl anomaly cancellation locks the critical dimension.**  The quantum
    Weyl (conformal) anomaly `cTotal D` vanishes if and only if `D = 10`. -/
theorem weyl_anomaly_cancellation (D : ℚ) : cTotal D = 0 ↔ D = 10 := by
  rw [cTotal_eq]; constructor <;> intro h <;> linarith

/-- The critical dimension of the superstring. -/
def criticalDimension : ℚ := 10

/-- The anomaly vanishes at the critical dimension. -/
theorem criticalDimension_spec : cTotal criticalDimension = 0 := by
  rw [cTotal_eq]; norm_num [criticalDimension]

/-! ### Additivity over path-integral sectors -/

/-- A conformal sector, recorded abstractly by its central charge. -/
structure CFTSector where
  /-- The central charge of the sector. -/
  c : ℚ

/-- The total central charge of a list of decoupled sectors: since the path
    integral factorizes over decoupled sectors, the conformal anomaly is
    additive. -/
def totalCharge (sectors : List CFTSector) : ℚ := (sectors.map CFTSector.c).sum

/-- **Additivity of the central charge** over decoupled sectors. -/
theorem totalCharge_append (s t : List CFTSector) :
    totalCharge (s ++ t) = totalCharge s + totalCharge t := by
  simp [totalCharge]

/-- The sectors of the superstring Polyakov path integral: `D` bosons, `D`
    worldsheet fermions, the reparametrization ghosts and the superconformal
    ghosts. -/
def polyakovSectors (D : ℚ) : List CFTSector :=
  [⟨cMatterBoson D⟩, ⟨cMatterFermion D⟩, ⟨cGhostBC⟩, ⟨cGhostBetaGamma⟩]

/-- **The Polyakov path integral assembles to the total anomaly** `cTotal D`. -/
theorem polyakov_totalCharge (D : ℚ) :
    totalCharge (polyakovSectors D) = cTotal D := by
  simp only [totalCharge, polyakovSectors, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, cTotal, cMatterBoson, cMatterFermion, cGhostBC,
    cGhostBetaGamma]
  ring

/-! ### The originally proposed formula (kept for transparency, reference
opinion adopted)

The task originally proposed `total_central_charge = D_matter * (1 + 1/2) - 26`.
We keep it as `totalChargeNaive` and prove (`naive_root`) that its unique root is
`52/3`, not `10`.  It omits the `+11` superconformal-ghost contribution, so it is
*not* the physically correct anomaly; `cTotal` above is used instead. -/

/-- The originally proposed (physically incomplete) expression, kept verbatim for
    documentation.  **Not** used to derive `D = 10`; see `naive_root`. -/
def totalChargeNaive (D : ℚ) : ℚ := D * (1 + 1 / 2) - 26

/-- The naive expression's root is `52/3`, demonstrating why it cannot be the
    correct anomaly (whose root is `10`). -/
theorem naive_root (D : ℚ) : totalChargeNaive D = 0 ↔ D = 52 / 3 := by
  unfold totalChargeNaive; constructor <;> intro h <;> linarith

/-! ## 5. Categorical locking of `D = 10` via membrane locking -/

/-- The Weyl renormalization flow on the matter dimension: a generative step
    whose fixed points are exactly the anomaly-free (Weyl-consistent) dimensions.
    The factor `2/3` inverts the slope of `cTotal`. -/
def weylStep (D : ℚ) : ℚ := D - (2 / 3) * cTotal D

/-- A fixed point of the Weyl flow is precisely the critical dimension. -/
theorem weylStep_fixed_iff (D : ℚ) : weylStep D = D ↔ D = 10 := by
  unfold weylStep
  rw [cTotal_eq]
  constructor <;> intro h <;> linarith

/-- The Weyl flow packaged as a generative dynamical system (an object of the
    category `GenSys` from `GenerativeDynamicalCategory.lean`). -/
def weylFlowSys : GenSys := ⟨ℚ, weylStep⟩

/-- **Membrane locking of the critical dimension.**  The Weyl-flow system has a
    unique locked state (fixed point): the anomaly-free dimension.  This is the
    categorical *limit* / *locked membrane* of the flow. -/
theorem weylFlow_membraneLocked : IsMembraneLocked weylFlowSys := by
  show ∃! x : ℚ, weylStep x = x
  refine ⟨10, ?_, ?_⟩
  · exact (weylStep_fixed_iff 10).mpr rfl
  · intro y hy
    exact (weylStep_fixed_iff y).mp hy

/-- **When the membrane locks, the matter dimension is `10`.**  Every locked
    state (fixed point / categorical limit) of the Weyl flow equals `D = 10`, so
    the categorical membrane locking of `GenerativeDynamicalCategory.lean` pins
    the matter dimension to the critical value. -/
theorem membraneLocked_dimension_eq_ten :
    ∀ D : ℚ, weylFlowSys.step D = D → D = 10 :=
  fun D h => (weylStep_fixed_iff D).mp h

/-- The locked-state (fixed-point) type of the Weyl flow is contractible: the
    critical dimension is the unique locked membrane. -/
theorem weylFlow_fix_contractible : IsContractible (FixSet weylFlowSys) :=
  (membraneLocked_iff_fix_contractible weylFlowSys).mp weylFlow_membraneLocked

end RGF.CFT
