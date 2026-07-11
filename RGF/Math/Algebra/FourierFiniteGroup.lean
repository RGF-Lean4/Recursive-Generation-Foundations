/-
  Harmonic analysis: Fourier transform on finite groups and convolution algebra
  Harmonic Analysis: Fourier Transform on Finite Groups and Convolution Algebra

  Formalizes:
  - the function space and inner product on a finite group
  - basic properties of convolution
  - explicit Fourier analysis on Z₅
  - the connection to spectral methods
-/

import Mathlib

open Finset BigOperators Complex

/-! ## 1. Function space on a finite group -/

noncomputable def groupInnerProduct {G : Type*} [Fintype G]
    (f g : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ x : G, f x * starRingEnd ℂ (g x)

theorem groupInnerProduct_conj {G : Type*} [Fintype G]
    (f g : G → ℂ) :
    starRingEnd ℂ (groupInnerProduct f g) = groupInnerProduct g f := by
  simp only [groupInnerProduct, map_mul, map_sum, map_inv₀, map_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp
  ring

/-! ## 2. Convolution -/

noncomputable def groupConvolution {G : Type*} [Fintype G] [DecidableEq G] [Group G]
    (f g : G → ℂ) : G → ℂ :=
  fun x => ∑ y : G, f y * g (y⁻¹ * x)

theorem convolution_delta_right {G : Type*} [Fintype G] [DecidableEq G] [Group G]
    (f : G → ℂ) :
    groupConvolution f (fun g => if g = 1 then 1 else 0) = f := by
  funext x; simp +decide [ groupConvolution ] ;
  simp +decide [ inv_mul_eq_one ]

/-! ## 3. Fourier analysis on Z₅ -/

theorem ZMod5_card : Fintype.card (ZMod 5) = 5 := by simp [ZMod.card]

noncomputable def omega5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

noncomputable def zmod5Char (k : ZMod 5) : ZMod 5 → ℂ :=
  fun n => omega5 ^ (k.val * n.val)

/-! ## 4. Discrete Fourier transform -/

noncomputable def discreteFourier {n : ℕ} [NeZero n]
    (f : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  ∑ x : ZMod n, f x * Complex.exp (-2 * Real.pi * Complex.I * (k.val * x.val) / n)

theorem discreteFourier_add {n : ℕ} [NeZero n]
    (f g : ZMod n → ℂ) (k : ZMod n) :
    discreteFourier (f + g) k = discreteFourier f k + discreteFourier g k := by
  simp [discreteFourier, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem discreteFourier_smul {n : ℕ} [NeZero n]
    (c : ℂ) (f : ZMod n → ℂ) (k : ZMod n) :
    discreteFourier (c • f) k = c * discreteFourier f k := by
  simp [discreteFourier, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _; ring

/-! ## 5. L² norm -/

noncomputable def l2NormSq {G : Type*} [Fintype G]
    (f : G → ℂ) : ℝ :=
  ∑ x : G, Complex.normSq (f x)

theorem l2NormSq_nonneg {G : Type*} [Fintype G]
    (f : G → ℂ) : 0 ≤ l2NormSq f := by
  apply Finset.sum_nonneg; intro x _
  exact Complex.normSq_nonneg (f x)

theorem l2NormSq_zero {G : Type*} [Fintype G] :
    l2NormSq (0 : G → ℂ) = 0 := by
  simp [l2NormSq, Complex.normSq_zero]

theorem l2NormSq_const {G : Type*} [Fintype G]
    (c : ℂ) : l2NormSq (fun _ : G => c) = Fintype.card G * Complex.normSq c := by
  simp [l2NormSq, Finset.sum_const, nsmul_eq_mul]

/-! ## 6. Circulant matrices and spectral methods -/

noncomputable def circularTransfer {n : ℕ} [NeZero n]
    (weights : ZMod n → ℝ) : ZMod n → ℂ :=
  fun k => ∑ x : ZMod n, (weights x : ℂ) *
    Complex.exp (-2 * Real.pi * Complex.I * (k.val * x.val) / n)

theorem circular_eigenvalues_are_fourier {n : ℕ} [NeZero n]
    (weights : ZMod n → ℝ) :
    circularTransfer weights = discreteFourier (fun x => (weights x : ℂ)) := by
  ext k; simp [circularTransfer, discreteFourier]

noncomputable def spectralGapFromFourier {n : ℕ} [NeZero n]
    (weights : ZMod n → ℝ) : ℝ :=
  1 - ‖circularTransfer weights 1‖

/-! ## 7. Fifth harmonic -/

noncomputable def fifthHarmonic (k : Fin 5) : ZMod 5 → ℂ :=
  fun n => Complex.exp (2 * Real.pi * Complex.I * (k.val * n.val) / 5)

theorem fifthHarmonic_count : Fintype.card (Fin 5) = 5 := by simp

theorem fifthHarmonic_zero :
    fifthHarmonic 0 = fun _ => 1 := by
  ext n; simp [fifthHarmonic]
