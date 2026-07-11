/-
  RequestProject/SpectrumReductionConjecture.lean

  Spectrum reduction (forward direction):
    From emergent stability (G2) and exponential recovery (G3) of the linearized
    operator one can deduce that its spectral gap is positive.

  This file gives a faithful, self-contained and machine-checkable formalization
  of the statement together with a complete proof.

  Mathematical content.  For a real square matrix `A`, the complexification
  `A.map (algebraMap ℝ ℂ)` describes the linearized dynamics on the complexified
  state space.  We say that the spectral gap is positive when every eigenvalue
  `μ` of the complexification satisfies `‖μ‖ < 1`.  The two dynamical axioms are

    * `g2_holds` (emergent stability / Lyapunov stability): orbits are uniformly
      bounded, `∃ C ≥ 0, ∀ x m, ‖(Aᵐ).mulVec x‖ ≤ C * ‖x‖`;
    * `g3_holds` (exponential recovery / asymptotic attraction): every orbit
      converges to the fixed point, `∀ x, (Aᵐ).mulVec x ⟶ 0`.

  The main theorem `g2_g3_imply_spectral_gap` states `g2_holds ∧ g3_holds →
  spectral_gap_positive A`.  This is the forward direction of the equivalence
  "asymptotic attraction ⇔ spectral radius < 1"; in the linear case `g2` is a
  consequence of `g3` and is not needed for the conclusion, but it is kept as a
  hypothesis because the dynamical axioms come as a pair.
-/

import Mathlib

open scoped Matrix
open Filter Topology

namespace SpectrumReductionConjecture

variable {n : ℕ}

/-- The set of eigenvalues of a complex matrix `M`: those `μ` admitting a nonzero
complex eigenvector `v` with `M.mulVec v = μ • v`. -/
def eigenvalues (M : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {μ | ∃ v : Fin n → ℂ, v ≠ 0 ∧ M.mulVec v = μ • v}

/-- The spectral gap of a real matrix `A` is positive when every eigenvalue of its
complexification `A.map (algebraMap ℝ ℂ)` has norm strictly less than `1`. -/
def spectral_gap_positive (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ μ ∈ eigenvalues (A.map (algebraMap ℝ ℂ)), ‖μ‖ < 1

/-- The two dynamical axioms attached to a linearized operator `A`. -/
structure RGFDynamicalAxioms (A : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- G2 (emergent stability / Lyapunov stability): the orbits are uniformly bounded. -/
  g2_holds : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin n → ℝ) (m : ℕ), ‖(A ^ m).mulVec x‖ ≤ C * ‖x‖
  /-- G3 (exponential recovery / asymptotic attraction): every orbit converges to `0`. -/
  g3_holds : ∀ (x : Fin n → ℝ), Tendsto (fun m : ℕ => (A ^ m).mulVec x) atTop (𝓝 0)

/-
Powers commute with the complexification map.
-/
theorem map_ofReal_pow (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    (A.map (algebraMap ℝ ℂ)) ^ m = (A ^ m).map (algebraMap ℝ ℂ) := by
  convert ( map_pow ( algebraMap ℝ ℂ ).mapMatrix A m ) |> Eq.symm

/-
An eigenvector of `M` for `μ` is an eigenvector of `Mᵐ` for `μᵐ`.
-/
theorem eig_pow (M : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (v : Fin n → ℂ)
    (h : M.mulVec v = μ • v) (m : ℕ) : (M ^ m).mulVec v = (μ ^ m) • v := by
  induction' m with m ih;
  · norm_num;
  · simp_all +decide [ pow_succ, ← Matrix.mulVec_mulVec ];
    rw [ Matrix.mulVec_smul, ih, smul_smul, mul_comm ]

/-
Real part of a complexified matrix-vector product.
-/
theorem re_complexified_mulVec (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℂ) (j : Fin n) :
    (((B.map (algebraMap ℝ ℂ)).mulVec v) j).re = (B.mulVec (fun k => (v k).re)) j := by
  simp +decide [ Matrix.mulVec, dotProduct ]

/-
Imaginary part of a complexified matrix-vector product.
-/
theorem im_complexified_mulVec (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℂ) (j : Fin n) :
    (((B.map (algebraMap ℝ ℂ)).mulVec v) j).im = (B.mulVec (fun k => (v k).im)) j := by
  simp +decide [ Matrix.mulVec, dotProduct ]

/-
**Main theorem.**  Emergent stability (G2) and exponential recovery (G3) imply that
the spectral gap of the linearized operator is positive.
-/
theorem g2_g3_imply_spectral_gap (A : Matrix (Fin n) (Fin n) ℝ)
    (hax : RGFDynamicalAxioms A) : spectral_gap_positive A := by
  intro μ hμ
  obtain ⟨v, hv₀, hv⟩ := hμ
  have h_seq : ∀ m : ℕ, (((A ^ m).map (algebraMap ℝ ℂ)).mulVec v) = (μ ^ m) • v := by
    convert eig_pow _ _ _ hv using 1;
    rw [ map_ofReal_pow ];
  -- Componentwise convergence to 0: the real and imaginary parts of `μ^m * v j` both
  -- tend to `0` by `g3_holds` applied to `Re v` and `Im v`, hence `μ^m * v j → 0`.
  have h_comp : ∀ j : Fin n, Filter.Tendsto (fun m : ℕ => (μ ^ m * v j)) Filter.atTop (nhds 0) := by
    intro j
    have h_real : Filter.Tendsto (fun m : ℕ => ((A ^ m).mulVec (fun k => (v k).re)) j) Filter.atTop (nhds 0) := by
      have := hax.g3_holds ( fun k => ( v k |> Complex.re ) );
      exact tendsto_pi_nhds.mp this j
    have h_imag : Filter.Tendsto (fun m : ℕ => ((A ^ m).mulVec (fun k => (v k).im)) j) Filter.atTop (nhds 0) := by
      have := hax.g3_holds ( fun k => ( v k |> Complex.im ) );
      exact tendsto_pi_nhds.mp this j;
    convert Complex.continuous_ofReal.continuousAt.tendsto.comp h_real |> Filter.Tendsto.add <| Complex.continuous_ofReal.continuousAt.tendsto.comp h_imag |> Filter.Tendsto.mul_const Complex.I using 2 ; norm_num [ Complex.ext_iff ];
    · have := congr_fun ( h_seq ‹_› ) j; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
      simp_all +decide [ Complex.ext_iff ];
    · norm_num;
  -- Since $v \neq 0$, choose $j$ with $v j \neq 0$.
  obtain ⟨j, hj⟩ : ∃ j : Fin n, v j ≠ 0 := by
    exact Function.ne_iff.mp hv₀;
  have := h_comp j;
  have := this.norm.div_const ( ‖v j‖ ) ; simp_all +decide

end SpectrumReductionConjecture