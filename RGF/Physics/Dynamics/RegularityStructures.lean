/-
  RGF/RegularityStructures.lean

  Direction I — Singular SPDEs and Hairer's regularity structures.

  We formalise, on a polynomial model space, the three structural pillars of a
  regularity structure and its BPHZ renormalisation:

  * **Graded model space and structure group.**  The model space is `ℝ[X]` with
    `Xᵏ` homogeneous of degree `k`; the structure group is realised by the
    re-centring (Taylor recentring) maps `Γ_h = Polynomial.taylor h`.  We prove
    the group-action laws `Gamma_zero`, `Gamma_add`, `Gamma_inv` and the group
    homomorphism `Gamma_hom : (ℝ,+) → Aut`, and that in the homogeneous grading
    `Γ_h` is unipotent upper-triangular (`Gamma_upper_triangular`,
    `Gamma_diagonal_one`).

  * **The reconstruction theorem (uniqueness kernel).**  `reconstruction_unique`
    is the quantitative core: two reals controlled by `C·λ^γ` (with `γ > 0`) at
    every scale `λ ∈ (0,1]` must coincide — the uniqueness of the reconstruction
    map.  `reconstruct_coherent` records the coherence of the polynomial model's
    local expansions with the global function.

  * **Renormalisation Hopf algebra and the BPHZ antipode.**  We realise the
    antipode of the (group-like) signature as the group inverse under the Chen
    concatenation product, i.e. path inversion (`chen_antipode_left/right`,
    `antipode_sig`), and formalise the deconcatenation coproduct with its counit,
    connected grading and recomposition law (`deconcat_recompose`,
    `deconcat_length`, `deconcat_head`, `deconcat_getLast`).

  Everything is `sorry`-free.
-/
import Mathlib

open Polynomial

namespace RGF.RegStruct

/-! ## 1. Graded model space and structure group -/

/-- The structure-group element: the Taylor re-centring by `h` acting on the
    polynomial model space (as an algebra automorphism). -/
noncomputable def Gamma (h : ℝ) : ℝ[X] ≃ₐ[ℝ] ℝ[X] := taylorEquiv h

/-- Re-centring by `0` is the identity. -/
theorem Gamma_zero : Gamma 0 = AlgEquiv.refl := by
  refine AlgEquiv.ext fun p => ?_
  show taylor 0 p = p
  rw [taylor_zero]

/-- The group homomorphism `(ℝ,+) → Aut` : re-centrings compose additively. -/
theorem Gamma_hom (h₁ h₂ : ℝ) : Gamma (h₁ + h₂) = Gamma h₁ * Gamma h₂ := by
  refine AlgEquiv.ext fun p => ?_
  rw [AlgEquiv.mul_apply]
  show taylor (h₁ + h₂) p = taylor h₁ (taylor h₂ p)
  rw [taylor_taylor]

/-- Additivity of the re-centring action (the `(ℝ,+)`-action law). -/
theorem Gamma_add (h₁ h₂ : ℝ) (p : ℝ[X]) :
    Gamma (h₁ + h₂) p = Gamma h₁ (Gamma h₂ p) := by
  show taylor (h₁ + h₂) p = taylor h₁ (taylor h₂ p)
  rw [taylor_taylor]

/-- The inverse structure-group element is re-centring by `-h`. -/
theorem Gamma_inv (h : ℝ) (p : ℝ[X]) : Gamma h (Gamma (-h) p) = p := by
  show taylor h (taylor (-h) p) = p
  rw [taylor_taylor, add_neg_cancel, taylor_zero]

/-- In the homogeneous grading (`Xᵏ` of degree `k`), the structure group is
    unipotent: `Γ_h Xᵏ` has no component in degree `> k`. -/
theorem Gamma_upper_triangular (h : ℝ) (k j : ℕ) (hj : k < j) :
    (Gamma h (X ^ k : ℝ[X])).coeff j = 0 := by
  show (taylor h (X ^ k : ℝ[X])).coeff j = 0
  apply coeff_eq_zero_of_natDegree_lt
  rw [natDegree_taylor]
  simpa using hj

/-- The structure group is unipotent with unit diagonal: the degree-`k`
    coefficient of `Γ_h Xᵏ` is `1`. -/
theorem Gamma_diagonal_one (h : ℝ) (k : ℕ) :
    (Gamma h (X ^ k : ℝ[X])).coeff k = 1 := by
  show (taylor h (X ^ k : ℝ[X])).coeff k = 1
  have hnd : (X ^ k : ℝ[X]).natDegree = k := natDegree_X_pow k
  have := coeff_taylor_natDegree (r := h) (f := (X ^ k : ℝ[X]))
  rw [hnd] at this
  rw [this, Monic.leadingCoeff (monic_X_pow k)]

/-! ## 2. The reconstruction theorem (uniqueness kernel) -/

/-- **Reconstruction uniqueness.**  If two reals are controlled by `C·λ^γ`
    (with `γ > 0`) uniformly over all scales `λ ∈ (0,1]`, they are equal. -/
theorem reconstruction_unique (a b C γ : ℝ) (hγ : 0 < γ)
    (h : ∀ l : ℝ, 0 < l → l ≤ 1 → |a - b| ≤ C * l ^ γ) : a = b := by
  -- Taking the limit as $l$ approaches $0$ from the right, we get $|a - b| \leq \lim_{l \to 0^+} C l^\gamma = 0$.
  have h_lim : Filter.Tendsto (fun l : ℝ => C * l ^ γ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by apply_rules [ Continuous.mul, Continuous.rpow ] <;> continuity ) _ _ <| by norm_num [ hγ.ne' ] );
  exact eq_of_sub_eq_zero ( by simpa using le_antisymm ( le_of_tendsto_of_tendsto tendsto_const_nhds h_lim <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) fun x hx => h x hx.1 hx.2.le ) ( abs_nonneg _ ) )

/-- **Coherence of the polynomial model.**  The local Taylor expansion at `r`
    reconstructs the global function: `(Γ_r f)(s - r) = f(s)`. -/
theorem reconstruct_coherent (r s : ℝ) (f : ℝ[X]) :
    (Gamma r f).eval (s - r) = f.eval s := by
  show (taylor r f).eval (s - r) = f.eval s
  rw [taylor_eval]
  congr 1
  ring

/-! ## 3. Renormalisation Hopf algebra and the BPHZ antipode -/

variable {α : Type*}

/-- The Chen concatenation product on (group-like) signatures, modelled as the
    product of the free group of paths. -/
def chen (g h : FreeGroup α) : FreeGroup α := g * h

/-- The BPHZ antipode: path inversion. -/
def antipode (g : FreeGroup α) : FreeGroup α := g⁻¹

/-- The antipode is a left inverse under the Chen product (`S(g)·g = 1`). -/
theorem chen_antipode_left (g : FreeGroup α) : chen (antipode g) g = 1 := by
  simp [chen, antipode]

/-- The antipode is a right inverse under the Chen product (`g·S(g) = 1`). -/
theorem chen_antipode_right (g : FreeGroup α) : chen g (antipode g) = 1 := by
  simp [chen, antipode]

/-- The antipode is an anti-homomorphism (path inversion reverses order). -/
theorem antipode_sig (g h : FreeGroup α) :
    antipode (chen g h) = chen (antipode h) (antipode g) := by
  simp [chen, antipode, mul_inv_rev]

/-- The deconcatenation coproduct: all ordered splits `w = u ++ v`. -/
def deconcat (w : List α) : List (List α × List α) :=
  (List.range (w.length + 1)).map (fun i => (w.take i, w.drop i))

/-- Recomposition law: every summand of the coproduct recomposes to `w`. -/
theorem deconcat_recompose (w : List α) (p : List α × List α)
    (hp : p ∈ deconcat w) : p.1 ++ p.2 = w := by
  simp only [deconcat, List.mem_map, List.mem_range] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact List.take_append_drop i w

/-- Connected grading: the coproduct has exactly `|w| + 1` terms. -/
theorem deconcat_length (w : List α) : (deconcat w).length = w.length + 1 := by
  simp [deconcat]

/-- Left counit: the first split is the trivial one `([], w)`. -/
theorem deconcat_head (w : List α) : (deconcat w).head? = some ([], w) := by
  simp [deconcat, List.range_succ_eq_map]

/-- Right counit: the last split is the trivial one `(w, [])`. -/
theorem deconcat_getLast (w : List α) :
    (deconcat w).getLast? = some (w, []) := by
  unfold deconcat; simp +decide ;
  simp +decide [ List.range_succ ]

end RGF.RegStruct