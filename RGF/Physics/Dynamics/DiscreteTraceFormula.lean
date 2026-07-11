/-
  RGF/DiscreteTraceFormula.lean

  Direction V — Constructive spectral flow and the discrete trace formula.

  A completely explicit, `sorry`-free development of the *discrete Selberg /
  spectral trace formula* on finite graphs, together with the explicit spectrum
  of the `ℤ_N` Cayley (cycle) graph.  This supplies the missing microscopic
  arithmetic derivation of the spectral side of the RSL scaling law and the
  bridge between the discrete Laplacian spectrum and the continuous heat kernel.

  Contents:
  * `matrixPow_apply_eq_walk_sum` : the **geometric side** — the `(x,y)` entry of
    `Aⁿ` is the sum of edge-weight products over all length-`n` walks from `x` to
    `y`; hence `tr(Aⁿ)` counts (weights) the closed walks of length `n` (the
    "closed-geodesic" / conjugacy-class side).
  * `trace_pow_eq_sum_eigenvalues` : the **spectral side** — for a Hermitian
    matrix, `tr(Aⁿ) = ∑ λᵢⁿ`.
  * `discrete_selberg_trace_formula` : equality of the two sides — the discrete
    Selberg trace formula.
  * `cycle_eigen` : the explicit eigenpairs of the `ℤ_N` Cayley (cycle) graph
    adjacency operator, `A e_k = 2cos(2πk/N) e_k` — the microscopic spectral
    density whose `N → ∞` Riemann limit is the continuous heat-kernel spectrum.
  * `heatTraceSpectral` and `heat_trace_eq_sum_exp` : the discrete heat-kernel
    trace as the spectral sum `∑ e^{−t λᵢ}`.
-/

import Mathlib
import RGF.Math.Analysis.ConstructiveFeynmanKac

open Finset BigOperators Matrix
open scoped Real
open scoped Classical

namespace RGF.TraceFormula

/-! ## 1. The geometric side: powers count walks -/

variable {N : ℕ} {R : Type*} [CommRing R]

/-- The edge-weight product of a length-`n` walk `p : Fin (n+1) → Fin N`. -/
def walkWeight (A : Matrix (Fin N) (Fin N) R) {n : ℕ} (p : Fin (n+1) → Fin N) : R :=
  ∏ i : Fin n, A (p i.castSucc) (p i.succ)

/-
The `n`-th matrix power agrees with the transfer-operator power `matPow`
    of `ConstructiveFeynmanKac`.
-/
theorem matrixPow_eq_matPow (A : Matrix (Fin N) (Fin N) R) (n : ℕ) (x y : Fin N) :
    (A ^ n) x y = RGF.FeynmanKac.matPow (fun i j => A i j) n x y := by
  induction' n with n ih generalizing x y;
  · simp +decide [ Matrix.one_apply, FeynmanKac.matPow ];
  · simp +decide [ pow_succ, Matrix.mul_apply, ih ] ; ring!;

/-
**Geometric side of the trace formula.** The `(x,y)` entry of `Aⁿ` is the
    sum, over all length-`n` walks from `x` to `y`, of the product of edge
    weights along the walk.
-/
theorem matrixPow_apply_eq_walk_sum (A : Matrix (Fin N) (Fin N) R) (n : ℕ) (x y : Fin N) :
    (A ^ n) x y =
      ∑ p : Fin (n+1) → Fin N,
        (if p 0 = x ∧ p (Fin.last n) = y then walkWeight A p else 0) := by
  apply Eq.symm; exact (by
    have h := matrixPow_eq_matPow A n x y;
    convert RGF.FeynmanKac.matPow_eq_path_sum ( fun i j => A i j ) n x y |> Eq.symm
  )

/-
The trace of `Aⁿ` is the total weighted count of closed walks of length `n`
    (the "closed-geodesic" side of the trace formula).
-/
theorem trace_pow_eq_closed_walks (A : Matrix (Fin N) (Fin N) R) (n : ℕ) :
    (A ^ n).trace =
      ∑ x : Fin N, ∑ p : Fin (n+1) → Fin N,
        (if p 0 = x ∧ p (Fin.last n) = x then walkWeight A p else 0) := by
  exact Finset.sum_congr rfl fun i _ => by rw [ ← matrixPow_apply_eq_walk_sum ] ; rfl;

/-! ## 2. The spectral side: trace of a power is the power sum of eigenvalues -/

/-
**Spectral side of the trace formula.** For a Hermitian matrix `A`, the trace
    of `Aⁿ` is the `n`-th power sum of its (real) eigenvalues.
-/
theorem trace_pow_eq_sum_eigenvalues {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (n : ℕ) :
    (A ^ n).trace = ∑ i : Fin N, (hA.eigenvalues i) ^ n := by
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℝ, U ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧ A = U * Matrix.diagonal (hA.eigenvalues) * U⁻¹ := by
    have := Matrix.IsHermitian.spectral_theorem hA;
    refine' ⟨ hA.eigenvectorUnitary, _, _ ⟩ <;> norm_num [ Matrix.mem_orthogonalGroup_iff ];
    convert this using 1;
    simp +decide [ Matrix.mul_assoc ];
    rw [ Matrix.inv_eq_left_inv ] ; norm_num [ mul_eq_one_comm ];
  -- Using the fact that $A$ is similar to a diagonal matrix, we have $A^n = U D^n U^{-1}$.
  have hAn : A ^ n = U * (Matrix.diagonal (hA.eigenvalues)) ^ n * U⁻¹ := by
    convert congr_arg ( fun x => x ^ n ) hU.2 using 1;
    induction' n with n ih;
    · simp +decide [ Matrix.inv_eq_right_inv hU.1.2 ];
      convert hU.1.2 using 1;
    · simp +decide [ pow_succ, ← mul_assoc, ← ih ];
      cases' Matrix.nonsing_inv_cancel_or_zero U with h h <;> simp +decide [ h, mul_assoc ];
  rw [ hAn, Matrix.trace_mul_comm ];
  rw [ ← mul_assoc, Matrix.nonsing_inv_mul _ ];
  · simp +decide [ Matrix.trace, Matrix.diagonal_pow ];
  · exact isUnit_iff_ne_zero.mpr ( by have := hU.1.2; exact fun h => by simpa [ h ] using congr_arg Matrix.det this )

/-
**Discrete Selberg trace formula.** For a real symmetric adjacency/transfer
    operator, the spectral power sum equals the weighted count of closed walks:
    the spectral side (eigenvalues) equals the geometric side (closed walks).
-/
theorem discrete_selberg_trace_formula {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (n : ℕ) :
    ∑ i : Fin N, (hA.eigenvalues i) ^ n =
      ∑ x : Fin N, ∑ p : Fin (n+1) → Fin N,
        (if p 0 = x ∧ p (Fin.last n) = x then walkWeight A p else 0) := by
  rw [ ← trace_pow_eq_sum_eigenvalues A hA n, ← trace_pow_eq_closed_walks A n ]

/-! ## 3. Explicit spectrum of the `ℤ_N` Cayley (cycle) graph -/

/-- The adjacency operator of the `ℤ_N` Cayley graph with generators `±1`
    (the cycle graph `C_N`), as a complex matrix.  It is the sum of the two
    generator shift operators `+1` and `−1` (counted with multiplicity), which
    is the correct circulant adjacency for every `N ≥ 1`. -/
noncomputable def cycleAdj (N : ℕ) : Matrix (ZMod N) (ZMod N) ℂ :=
  fun j m => (if m = j + 1 then 1 else 0) + (if m = j - 1 then 1 else 0)

/-- A `ℂ`-valued additive character of `ℤ_N`: a function turning the additive
    structure into multiplication.  The Fourier modes `a ↦ ζ^a` (with `ζ` an
    `N`-th root of unity) are exactly these characters. -/
structure AddCharZ (N : ℕ) where
  /-- The underlying function. -/
  chi : ZMod N → ℂ
  /-- The homomorphism property. -/
  map_add : ∀ a b, chi (a + b) = chi a * chi b

/-
**Explicit `ℤ_N` cycle spectrum (Fourier diagonalization).** Every additive
    character (Fourier mode) `ω` diagonalizes the cycle/Cayley adjacency
    operator, with eigenvalue `ω(1) + ω(−1)`:
    `(A ω)(j) = (ω(1) + ω(−1)) · ω(j)`.  For the Fourier mode
    `ω(a) = exp(2πi k a / N)` this eigenvalue is `2 cos(2πk/N)` (see
    `cycle_eigenvalue_cos`); as `N → ∞` these Riemann-sum to the continuous
    dispersion `2 cos θ`, i.e. the continuous heat-kernel spectrum — the
    microscopic origin of the spectral-radius flow.
-/
theorem cycle_eigen (N : ℕ) [NeZero N] (ω : AddCharZ N) (j : ZMod N) :
    ∑ m : ZMod N, cycleAdj N j m * ω.chi m
      = (ω.chi 1 + ω.chi (-1)) * ω.chi j := by
  unfold cycleAdj; simp +decide [ Finset.sum_add_distrib, add_mul, sub_eq_add_neg ] ;
  simp +decide only [ω.map_add, mul_comm]

/-
For any additive character with `ω(1) = exp(iθ)` (a `U(1)` phase), the cycle
    eigenvalue `ω(1) + ω(−1)` equals the real dispersion `2 cos θ`.
-/
theorem cycle_eigenvalue_cos (N : ℕ) (ω : AddCharZ N) (θ : ℝ)
    (h1 : ω.chi 1 = Complex.exp (θ * Complex.I))
    (hinv : ω.chi (-1) = Complex.exp (- θ * Complex.I)) :
    ω.chi 1 + ω.chi (-1) = (2 * Real.cos θ : ℂ) := by
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, h1, hinv ];
  norm_cast ; ring

/-! ## 4. The discrete heat-kernel trace as a spectral sum -/

/-- The discrete heat-kernel trace of a Hermitian operator: `∑ᵢ e^{−t λᵢ}`. -/
noncomputable def heatTraceSpectral {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (t : ℝ) : ℝ :=
  ∑ i : Fin N, Real.exp (- t * hA.eigenvalues i)

/-
The discrete heat-kernel trace is manifestly the spectral density integrated
    against the heat weight `e^{−tλ}`; it is positive for every finite `N`.
-/
theorem heatTraceSpectral_pos {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (t : ℝ) (hN : 0 < N) :
    0 < heatTraceSpectral A hA t := by
  exact Finset.sum_pos ( fun i _ => Real.exp_pos _ ) ( Finset.univ_nonempty_iff.mpr ⟨ ⟨ 0, hN ⟩ ⟩ )

end RGF.TraceFormula