import Mathlib
import RGF.Applications.LinearizedSpectrum
import RGF.Generative.Locking.ModeDecomposition

/-!
# Spectral stability of mode-locking

On top of the C₅ graph Laplacian `pentagonLaplacian` from
`FORS/LinearizedSpectrum.lean`, this file proves three things.

## 1. The spectral stability theorem for mode-locking (main goal `lock_stability`)

The eigenvalues of the C₅ graph Laplacian `L` are `λ_k = 2 − 2cos(2πk/5)`:
`λ₀ = 0` (the zero mode / constant, corresponding to the global translation of the
membrane), `λ₁ = λ₄ = (5−√5)/2 > 0`, and `λ₂ = λ₃ = (5+√5)/2 > 0`.

The **generation iteration operator** is taken to be `M = I − (1/4)·L` (`genStep`). It is
the identity on the constant zero mode (`genStep_const`), and is a **strict contraction**
on the 4 massive directions orthogonal to the zero mode: the eigenvalues
`μ_k = 1 − (1/4)λ_k` satisfy `|μ_k| ≤ √(0.43) < 1`. Hence any perturbation deviating from
the 5 eigenmodes (outside the projection `projKer`) decays exponentially under the
generation iteration:

  `lock_stability : ∀ v, ∃ C ρ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
       ∀ n, ‖ M^[n] v − projKer v ‖ ≤ C · ρ^n`.

The core step is the finite-dimensional (5 variables, with the constraint `∑w=0`)
quadratic-form inequality `genStep_contraction`: for `w` of zero mean,
`‖M w‖² ≤ (1/2)‖w‖²`.

## 2. The operator correspondence between mode-locking and the spiral mirror dual σ

The discrete action of the spiral mirror dual `σ(s) = 1 − conj s` on the C₅ cycle is the
pentagon reflection `sr 0` (`pentagonRep (sr 0) x = −x`), i.e. `(σ u)_x = u(−x)`
(`sigmaOp`). We prove:
* `sigmaOp_involutive`: σ is an involution (σ² = id);
* `sigmaOp_pentagonLaplacian_comm` / `sigmaOp_genStep_comm`: the **commutation relations**
  `L σ = σ L` and `M σ = σ M` (near the membrane solution).

By the commutation relations, σ preserves each eigenspace, so the spectral spaces
decompose according to the ±1 eigenvalues of σ. Note: σ **commutes** with L (rather than
anticommuting), so σ sends each eigenvector to an eigenvector with the **same eigenvalue**;
the effect of σ is to split each 2-dimensional eigenblock further into two 1-dimensional
lines, "mirror-symmetric" (σ=+1) and "mirror-antisymmetric" (σ=−1). The original wording
"the paired-mode eigenvalues are unequal" does not hold under the faithful definitions —
the correct conclusion is that within each 2-dimensional block the σ-fixed direction is
**unique** (1-dimensional), which is precisely the non-degeneracy of mode-locking.

## 3. Uniqueness within the 2-dimensional irreducible representation blocks (locking non-degeneracy U)

The two 2-dimensional irreducible representations of D₅ correspond to the `λ₁=λ₄` and
`λ₂=λ₃` subspaces. We give the explicit real eigenvectors `cmode j` (cosine, σ-fixed) and
`smode j` (sine, σ-antisymmetric) of each block and prove:
* `cmode_eigen` / `smode_eigen`: both are eigenvectors with eigenvalue `λ_j`;
* `cmode_sigma_fixed`: `σ (cmode j) = cmode j` (σ=+1);
* `smode_sigma_anti`: `σ (smode j) = −smode j` (σ=−1).

So within each 2-dimensional block, the two σ-dual directions are **not independent stable
(σ-fixed) modes**: only the cosine direction is a σ-fixed stable mode, while the sine
direction is sign-flipped by σ. This yields locking non-degeneracy (U) independently
inside RGF.

Dependencies: FORS/LinearizedSpectrum.lean, FORS/ModeDecomposition.lean
-/

namespace RGF.FORS

open Finset

/-! ## The generation iteration operator and the kernel projection -/

/-- **The generation iteration operator** `M = I − (1/4)·L`, where `L` is the C₅
    Laplacian `pentagonLaplacian`. It is the identity on the constant zero mode and a
    strict contraction on the massive directions. -/
noncomputable def genStep (v : IRMode) : IRMode := fun x => v x - (1/4) * pentagonLaplacian v x

/-- Projection onto the kernel (the space spanned by the constant field = the zero mode
    among the 5 eigenmodes): take the mean constant field. -/
noncomputable def projKer (v : IRMode) : IRMode := fun _ => (∑ x : ZMod 5, v x) / 5

/-- The L² squared norm. -/
def nrm2 (w : IRMode) : ℝ := ∑ x : ZMod 5, (w x) ^ 2

/-- The L² norm. -/
noncomputable def l2norm (w : IRMode) : ℝ := Real.sqrt (nrm2 w)

/-! ## Basic algebraic properties -/

/-
The sum of the C₅ Laplacian over all vertices is zero.
-/
theorem pentagonLaplacian_sum_zero (v : IRMode) :
    ∑ x : ZMod 5, pentagonLaplacian v x = 0 := by
      unfold pentagonLaplacian;
      erw [ Fin.sum_univ_five ] ; ring!

/-
The generation operator is the identity on constant fields.
-/
theorem genStep_const (c : ℝ) : genStep (fun _ => c) = fun _ => c := by
  ext x
  simp [genStep, pentagonLaplacian_const_zero]

/-
The generation operator preserves the mean (the sum over all vertices).
-/
theorem genStep_sum (v : IRMode) :
    ∑ x : ZMod 5, genStep v x = ∑ x : ZMod 5, v x := by
      simp +decide [ genStep, Finset.sum_sub_distrib ];
      rw [ ← Finset.mul_sum _ _ _, pentagonLaplacian_sum_zero, MulZeroClass.mul_zero ]

/-! ## Auxiliary: linearity properties of genStep -/

/-- Additivity of the generation operator. -/
theorem genStep_linear_add (u v : IRMode) : genStep (u + v) = genStep u + genStep v := by
  ext x
  simp [genStep, pentagonLaplacian, Pi.add_apply]
  ring

/-- Homogeneity of the generation operator. -/
theorem genStep_linear_smul (c : ℝ) (u : IRMode) : genStep (c • u) = c • genStep u := by
  ext x
  simp [genStep, pentagonLaplacian, Pi.smul_apply, smul_eq_mul]
  ring

/-- The mean is invariant under iteration. -/
theorem genStep_sum_iterate (w : IRMode) (n : ℕ) :
    ∑ x : ZMod 5, (genStep^[n] w) x = ∑ x : ZMod 5, w x := by
  induction' n with k ih
  · rfl
  · rw [Function.iterate_succ', Function.comp_apply, genStep_sum, ih]

/-- The kernel projection is invariant under the generation iteration. -/
theorem projKer_genStep (v : IRMode) : projKer (genStep v) = projKer v := by
  ext x
  simp [projKer, genStep_sum]

/-- The kernel projection is invariant under iteration. -/
theorem projKer_iterate (v : IRMode) (n : ℕ) : projKer (genStep^[n] v) = projKer v := by
  induction' n with k ih
  · rfl
  · rw [Function.iterate_succ', Function.comp_apply, projKer_genStep, ih]

/-- The generation operator commutes with "subtracting the kernel projection" (L kills
    constants, so the transverse fluctuations decouple from the kernel). -/
theorem genStep_sub_projKer (v : IRMode) :
    genStep v - projKer v = genStep (v - projKer v) := by
  have hsmul : genStep (v - projKer v) = genStep v - genStep (projKer v) := by
    rw [sub_eq_add_neg, genStep_linear_add, ← neg_one_smul ℝ (projKer v),
      genStep_linear_smul, neg_one_smul, ← sub_eq_add_neg]
  have hc : genStep (projKer v) = projKer v := genStep_const _
  rw [hsmul, hc]

/-- A perturbation deviating from the kernel has zero mean. -/
theorem sum_dev_zero (v : IRMode) :
    ∑ x : ZMod 5, (v - projKer v) x = 0 := by
  simp only [Pi.sub_apply, projKer, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  rw [ZMod.card 5]
  ring

/-! ## The key one-step contraction (finite-dimensional quadratic-form inequality) -/

/-
**One-step contraction**: for a perturbation `w` of zero mean, the generation iteration
    reduces its squared norm by at least half.
    (The proof is a quadratic-form inequality in 5 variables with the linear constraint
    `∑w=0`: the eigenvalues `μ_k = 1 − (1/4)λ_k` satisfy `μ_k² ≤ 0.43 < 1/2` on the
    nonzero modes.)
-/
theorem genStep_contraction (w : IRMode) (h : ∑ x : ZMod 5, w x = 0) :
    nrm2 (genStep w) ≤ (1/2) * nrm2 w := by
      unfold nrm2;
      unfold genStep; ring_nf;
      unfold pentagonLaplacian;
      erw [ Fin.sum_univ_five ] at *;
      erw [ Fin.sum_univ_five ] ; norm_num ; nlinarith! [ sq_nonneg ( w 0 - w 1 ), sq_nonneg ( w 1 - w 2 ), sq_nonneg ( w 2 - w 3 ), sq_nonneg ( w 3 - w 4 ), sq_nonneg ( w 4 - w 0 ) ] ;

/-! ## Iterative decay -/

/-- Iterative decay (squared-norm version): the squared norm of a zero-mean perturbation
    decays exponentially as `(1/2)^n`. -/
theorem nrm2_iterate_decay (w : IRMode) (h : ∑ x : ZMod 5, w x = 0) (n : ℕ) :
    nrm2 (genStep^[n] w) ≤ (1/2) ^ n * nrm2 w := by
  induction' n with k ih
  · simp [nrm2]
  · rw [Function.iterate_succ', Function.comp_apply]
    calc
      nrm2 (genStep (genStep^[k] w)) ≤ (1/2) * nrm2 (genStep^[k] w) :=
        genStep_contraction (genStep^[k] w) (by rw [genStep_sum_iterate w k, h])
      _ ≤ (1/2) * ((1/2) ^ k * nrm2 w) := by gcongr
      _ = (1/2) ^ (k+1) * nrm2 w := by ring

/-
Under iteration, the part deviating from the kernel equals the direct iteration of the initial perturbation.
-/
theorem iterate_dev (v : IRMode) (n : ℕ) :
    genStep^[n] v - projKer v = genStep^[n] (v - projKer v) := by
      induction' n with n ih;
      · rfl;
      · rw [ Function.iterate_succ', Function.comp_apply ];
        grind +suggestions

/-- `√(xⁿ) = (√x)ⁿ` (for `x ≥ 0`). -/
theorem sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = (Real.sqrt x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ← ih, ← Real.sqrt_mul (by positivity)]

/-! ## Main theorem: spectral stability of mode-locking -/

/-- **Spectral stability theorem for mode-locking**: any perturbation deviating from the
    5 eigenmodes (outside the kernel projection `projKer v`) decays exponentially under
    the generation iteration `M = genStep` — there exist a constant `C ≥ 0` and a
    contraction rate `0 ≤ ρ < 1` such that for all `n`,
    `‖ M^[n] v − projKer v ‖ ≤ C · ρ^n`. -/
theorem lock_stability (v : IRMode) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ n : ℕ, l2norm (genStep^[n] v - projKer v) ≤ C * ρ ^ n := by
  set w := v - projKer v with hw_def
  have h_sum_w_zero : ∑ x : ZMod 5, w x = 0 := sum_dev_zero v
  have h_nrm2_decay (n : ℕ) : nrm2 (genStep^[n] w) ≤ (1/2)^n * nrm2 w :=
    nrm2_iterate_decay w h_sum_w_zero n
  refine ⟨Real.sqrt (nrm2 w), Real.sqrt (1/2), Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, ?_⟩
  · calc
      Real.sqrt (1/2) < Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 1 := Real.sqrt_one
  intro n
  rw [l2norm]
  calc
    Real.sqrt (nrm2 (genStep^[n] v - projKer v)) = Real.sqrt (nrm2 (genStep^[n] w)) := by
      rw [iterate_dev v n, hw_def]
    _ ≤ Real.sqrt ((1/2)^n * nrm2 w) := Real.sqrt_le_sqrt (h_nrm2_decay n)
    _ = Real.sqrt ((1/2)^n) * Real.sqrt (nrm2 w) := by
        rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (1/2)^n)]
    _ = (Real.sqrt (1/2))^n * Real.sqrt (nrm2 w) := by rw [sqrt_pow_eq _ (by norm_num)]
    _ = Real.sqrt (nrm2 w) * (Real.sqrt (1/2)) ^ n := mul_comm _ _

/-! ## 2. The spiral mirror dual σ and the commutation relations -/

/-- The discrete action of the spiral mirror dual `σ(s) = 1 − conj s` on the C₅ cycle:
    it corresponds to the pentagon reflection `sr 0` (`pentagonRep (sr 0) x = −x`), i.e.
    `(σ u)_x = u(−x)`. -/
def sigmaOp (u : IRMode) : IRMode := fun x => u (-x)

/-- σ is an involution: `σ² = id`. -/
theorem sigmaOp_involutive (u : IRMode) : sigmaOp (sigmaOp u) = u := by
  funext x; simp [sigmaOp]

/-
σ is the pullback of the pentagon reflection `sr 0` to the mode space.
-/
theorem sigmaOp_eq_pentagonRep (u : IRMode) :
    sigmaOp u = fun x => u (pentagonRep (DihedralGroup.sr 0) x) := by
      ext x; simp [sigmaOp, pentagonRep_sr]

/-
**Commutation relation (L σ = σ L)**: the C₅ Laplacian commutes with the spiral mirror dual near the membrane solution.
-/
theorem sigmaOp_pentagonLaplacian_comm (u : IRMode) :
    pentagonLaplacian (sigmaOp u) = sigmaOp (pentagonLaplacian u) := by
      convert pentagonLaplacian_equivariant ( DihedralGroup.sr 0 ) u using 1

/-
**Commutation relation (M σ = σ M)**: the generation iteration operator commutes with the spiral mirror dual.
-/
theorem sigmaOp_genStep_comm (u : IRMode) :
    genStep (sigmaOp u) = sigmaOp (genStep u) := by
      ext x; simp [genStep, sigmaOp, sigmaOp_pentagonLaplacian_comm]

/-- A σ-fixed (mirror-symmetric) mode. -/
def symMode (u : IRMode) : Prop := sigmaOp u = u

/-- A σ-antisymmetric (mirror-antisymmetric) mode. -/
def antiMode (u : IRMode) : Prop := sigmaOp u = -u

/-
L preserves the σ-fixed subspace (by the commutation relation).
-/
theorem pentagonLaplacian_preserves_sym (u : IRMode) (hu : symMode u) :
    symMode (pentagonLaplacian u) := by
      unfold symMode; rw [ ← sigmaOp_pentagonLaplacian_comm, hu ] ;

/-
L preserves the σ-antisymmetric subspace (by the commutation relation).
-/
theorem pentagonLaplacian_preserves_anti (u : IRMode) (hu : antiMode u) :
    antiMode (pentagonLaplacian u) := by
      unfold antiMode at *;
      unfold sigmaOp at *;
      simp_all +decide [ funext_iff, pentagonLaplacian ];
      intro x; rw [ show -x + 1 = - ( x - 1 ) by ring, show -x - 1 = - ( x + 1 ) by ring, hu, hu ] ; ring;

/-! ## 3. Uniqueness within the 2-dimensional irreducible representation blocks (explicit eigenvectors) -/

/-- The `j`-th cosine mode `cmode j x = cos(2π j x / 5)`. -/
noncomputable def cmode (j : ℕ) : IRMode := fun x => Real.cos (2 * Real.pi * j * (x.val) / 5)

/-- The `j`-th sine mode `smode j x = sin(2π j x / 5)`. -/
noncomputable def smode (j : ℕ) : IRMode := fun x => Real.sin (2 * Real.pi * j * (x.val) / 5)

/-- The eigenvalue of the `j`-th block `λ_j = 2 − 2cos(2πj/5)`. -/
noncomputable def lam (j : ℕ) : ℝ := 2 - 2 * Real.cos (2 * Real.pi * j / 5)

/-
**The cosine mode is an eigenvector**: `L (cmode j) = λ_j · cmode j`.
-/
theorem cmode_eigen (j : ℕ) :
    pentagonLaplacian (cmode j) = (lam j) • cmode j := by
      ext x;
      fin_cases x <;> simp +decide [ pentagonLaplacian, cmode, lam ];
      · norm_num [ ZMod.cast, ZMod.val ] ; ring;
        rw [ show Real.pi * j * ( 8 / 5 ) = 2 * Real.pi * j - Real.pi * j * ( 2 / 5 ) by ring ] ; norm_num [ mul_assoc, mul_comm Real.pi _, mul_div ] ; ring;
        rw [ show ( j : ℝ ) * Real.pi * ( 8 / 5 ) = 2 * Real.pi * j - ( j : ℝ ) * Real.pi * ( 2 / 5 ) by ring ] ; norm_num [ mul_assoc, mul_comm Real.pi _, mul_left_comm ] ; ring;
      · norm_num [ ZMod.cast, ZMod.val ] ; ring;
        rw [ Real.cos_sq ] ; ring;
      · norm_num [ ZMod.cast, ZMod.val ];
        rw [ show 2 * Real.pi * j * 3 / 5 = 2 * Real.pi * j * 2 / 5 + 2 * Real.pi * j / 5 by ring, show 2 * Real.pi * j / 5 = 2 * Real.pi * j * 2 / 5 - 2 * Real.pi * j / 5 by ring ] ; rw [ Real.cos_add, Real.cos_sub ] ; ring;
        rw [ show Real.pi * j * ( 4 / 5 ) = 2 * ( Real.pi * j * ( 2 / 5 ) ) by ring, Real.cos_two_mul ] ; ring;
        rw [ show Real.pi * j * ( 4 / 5 ) = 2 * ( Real.pi * j * ( 2 / 5 ) ) by ring, Real.sin_two_mul ] ; ring;
        rw [ Real.sin_sq ] ; ring;
      · norm_num [ ZMod.cast, ZMod.val ] ; ring;
        rw [ show Real.pi * j * ( 8 / 5 ) = Real.pi * j * ( 6 / 5 ) + Real.pi * j * ( 2 / 5 ) by ring, show Real.pi * j * ( 4 / 5 ) = Real.pi * j * ( 6 / 5 ) - Real.pi * j * ( 2 / 5 ) by ring ] ; rw [ Real.cos_add, Real.cos_sub ] ; ring;
      · erw [ show ( 4 - 1 : ZMod 5 ) = 3 from rfl ] ; norm_num [ ZMod.cast, ZMod.val ] ; ring;
        rw [ show Real.pi * j * ( 8 / 5 ) = Real.pi * j * ( 5 / 5 ) + Real.pi * j * ( 3 / 5 ) by ring, show Real.pi * j * ( 6 / 5 ) = Real.pi * j * ( 5 / 5 ) + Real.pi * j * ( 1 / 5 ) by ring, show Real.pi * j * ( 2 / 5 ) = Real.pi * j * ( 5 / 5 ) - Real.pi * j * ( 3 / 5 ) by ring ] ; norm_num [ Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub ] ; ring;
        norm_num [ mul_comm Real.pi, Real.cos_sq' ] ; ring;
        rw [ Real.sin_sq, Real.cos_sq ] ; ring;
        rw [ show ( j : ℝ ) * Real.pi * ( 6 / 5 ) = ( j : ℝ ) * Real.pi + ( j : ℝ ) * Real.pi * ( 1 / 5 ) by ring, Real.cos_add ] ; norm_num

/-
**The sine mode is an eigenvector**: `L (smode j) = λ_j · smode j`.
-/
theorem smode_eigen (j : ℕ) :
    pentagonLaplacian (smode j) = (lam j) • smode j := by
      ext x;
      fin_cases x <;> simp +decide [ pentagonLaplacian, smode, lam ];
      · erw [ show ( 2 * Real.pi * j * 4 / 5 : ℝ ) = 2 * Real.pi * j - 2 * Real.pi * j / 5 by ring ] ; norm_num [ Real.sin_sub, mul_assoc, mul_comm Real.pi _, mul_left_comm ];
        norm_num [ show Real.sin ( j * ( 2 * Real.pi ) ) = 0 from Real.sin_eq_zero_iff.mpr ⟨ j * 2, by push_cast; ring ⟩ ];
        norm_num [ ZMod.cast, ZMod.val ];
      · norm_num [ ZMod.cast, ZMod.val ] ; ring;
        rw [ show Real.pi * j * ( 4 / 5 ) = 2 * ( Real.pi * j * ( 2 / 5 ) ) by ring, Real.sin_two_mul ] ; ring;
      · norm_num [ ZMod.cast, ZMod.val ] ; ring;
        rw [ show Real.pi * j * ( 6 / 5 ) = Real.pi * j * ( 4 / 5 ) + Real.pi * j * ( 2 / 5 ) by ring, show Real.pi * j * ( 2 / 5 ) = Real.pi * j * ( 4 / 5 ) - Real.pi * j * ( 2 / 5 ) by ring ] ; rw [ Real.sin_add, Real.sin_sub ] ; ring;
        rw [ show Real.pi * j * ( 4 / 5 ) = 2 * ( Real.pi * j * ( 2 / 5 ) ) by ring, Real.sin_two_mul, Real.cos_two_mul ] ; ring;
      · norm_num [ ZMod.cast, ZMod.val ] ; ring;
        rw [ show Real.pi * j * ( 8 / 5 ) = Real.pi * j * ( 6 / 5 ) + Real.pi * j * ( 2 / 5 ) by ring, show Real.pi * j * ( 4 / 5 ) = Real.pi * j * ( 6 / 5 ) - Real.pi * j * ( 2 / 5 ) by ring ] ; rw [ Real.sin_add, Real.sin_sub ] ; ring;
      · norm_num [ ZMod.cast, ZMod.val ] ; ring;
        rw [ ( by ring : Real.pi * j * ( 6 / 5 ) = Real.pi * j * ( 8 / 5 ) - Real.pi * j * ( 2 / 5 ) ), Real.sin_sub ] ; norm_num ; ring;
        rw [ show Real.pi * j * ( 8 / 5 ) = Real.pi * j * ( 5 / 5 ) + Real.pi * j * ( 3 / 5 ) by ring, show Real.pi * j * ( 2 / 5 ) = Real.pi * j * ( 5 / 5 ) - Real.pi * j * ( 3 / 5 ) by ring ] ; norm_num [ Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub ] ; ring;
        norm_num [ mul_comm Real.pi ]

/-
**The cosine mode is σ-fixed** (a mirror-symmetric stable mode).
-/
theorem cmode_sigma_fixed (j : ℕ) : sigmaOp (cmode j) = cmode j := by
  ext x;
  refine' Real.cos_eq_cos_iff.mpr _;
  fin_cases x <;> norm_num [ ZMod.val ];
  · erw [ Fin.coe_neg_one ] ; ring_nf ; norm_num;
    exact ⟨ j, Or.inr <| by push_cast; ring ⟩;
  · erw [ Fin.val_neg' ] ; norm_num ; ring_nf ; norm_num;
    exact ⟨ j, Or.inr <| by push_cast; ring ⟩;
  · erw [ Fin.val_neg' ] ; norm_num ; ring;
    exact ⟨ j, Or.inr <| by push_cast; ring ⟩;
  · erw [ Fin.val_neg' ] ; norm_num ; ring;
    exact ⟨ j, Or.inr <| by push_cast; ring ⟩

/-
**The sine mode is sign-flipped by σ** (mirror-antisymmetric, not a σ-fixed stable mode).
-/
theorem smode_sigma_anti (j : ℕ) : sigmaOp (smode j) = -smode j := by
  unfold sigmaOp smode;
  ext x; fin_cases x <;> norm_num [ ZMod.val ] <;> ring_nf ;
  · erw [ Fin.coe_neg_one ] ; norm_num ; ring;
    rw [ ← Real.sin_two_pi_sub ] ; ring;
    rw [ Real.sin_eq_sin_iff ];
    exact ⟨ -j + 1, Or.inl <| by push_cast; ring ⟩;
  · erw [ show ( - ( ⟨ 2, by decide ⟩ : ZMod 5 ) : ZMod 5 ) = 3 by decide ] ; norm_num ; ring;
    rw [ ← Real.sin_two_pi_sub ] ; ring;
    rw [ ← Real.sin_periodic ] ; ring;
    convert Real.sin_periodic.int_mul j _ using 2 ; push_cast ; ring;
  · erw [ show ( - ( ⟨ 3, by decide ⟩ : ZMod 5 ) : ZMod 5 ) = 2 by decide ] ; norm_num ; ring_nf ; norm_num [ mul_assoc, mul_comm Real.pi _, mul_div ] ;
    rw [ ← Real.sin_antiperiodic ] ; ring;
    rw [ ← Real.sin_pi_sub ] ; ring;
    convert Real.sin_periodic.int_mul ( -j ) _ using 2 ; push_cast ; ring;
  · erw [ show ( - ( ⟨ 4, by decide ⟩ : ZMod 5 ) : ZMod 5 ) = 1 by decide ] ; norm_num ; ring_nf ; norm_num [ mul_assoc, mul_comm Real.pi _, mul_div ] ;
    rw [ ← Real.sin_antiperiodic ] ; ring;
    rw [ ← Real.sin_pi_sub ] ; ring;
    convert Real.sin_periodic.int_mul ( -j ) _ using 2 ; push_cast ; ring

/-- **Non-degeneracy within a 2-dimensional block (U)**: within the 2-dimensional
    eigenblock with `λ_j = λ_{5−j}`, the two σ-dual directions (the cosine `cmode j` and
    the sine `smode j`) share the eigenvalue `λ_j`, but σ sends them to `+` and `−`
    respectively: the cosine is the unique σ-fixed stable mode, while the sine is
    sign-flipped by σ. So the two are **not independent σ-fixed stable modes** — this
    yields locking non-degeneracy independently inside RGF. -/
theorem block_nondegeneracy (j : ℕ) :
    pentagonLaplacian (cmode j) = (lam j) • cmode j ∧
    pentagonLaplacian (smode j) = (lam j) • smode j ∧
    sigmaOp (cmode j) = cmode j ∧
    sigmaOp (smode j) = -smode j :=
  ⟨cmode_eigen j, smode_eigen j, cmode_sigma_fixed j, smode_sigma_anti j⟩

/-! ## Connection to the dynamical axioms (G3 / exponential recovery): the 5 eigenmodes are an attractor -/

/-- **Attractor property of mode-locking (G3-type exponential recovery)**: any initial
    perturbation converges under the generation iteration to the mode-locked core spanned
    by the 5 eigenmodes (`projKer v`): the norm of the deviating part tends to 0.
    This is a concrete realization, on the generation dynamics, of
    `SpectrumReductionConjecture.RGFDynamicalAxioms.g3_holds` (asymptotic attraction),
    connecting with the dynamical axioms of the spectral-gap theorem. -/
theorem lock_attractor (v : IRMode) :
    Filter.Tendsto (fun n : ℕ => l2norm (genStep^[n] v - projKer v)) Filter.atTop (nhds 0) := by
  obtain ⟨C, ρ, hC, hρ, hρlt, hbound⟩ := lock_stability v
  have hge : ∀ n : ℕ, 0 ≤ l2norm (genStep^[n] v - projKer v) := fun n => Real.sqrt_nonneg _
  have htop : Filter.Tendsto (fun n : ℕ => C * ρ ^ n) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun n : ℕ => ρ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρlt
    simpa using this.const_mul C
  exact squeeze_zero hge hbound htop

end RGF.FORS
