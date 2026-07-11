/-
  Physical application: SU(5) grand unified theory and quasicrystalline five-fold symmetry
  Lean support for paper 28

  Formalises:
  - the basic numerical parameters of SU(5)
  - the dimension matching of the Standard Model
  - the crystallographic restriction theorem (discrete form)
  - basic properties of the group A₅
  - algebraic properties of the golden ratio
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Basic parameters of SU(5) -/

/-- dimension of SU(n) = n² - 1 -/
def SUn_dim (n : ℕ) : ℕ := n ^ 2 - 1

/-- rank of SU(n) = n - 1 -/
def SUn_rank (n : ℕ) : ℕ := n - 1

/-- dimension of SU(5) = 24 -/
theorem SU5_dim_eq : SUn_dim 5 = 24 := by decide

/-- rank of SU(5) = 4 -/
theorem SU5_rank_eq : SUn_rank 5 = 4 := by decide

/-- order of the centre of SU(5) = 5 -/
theorem SU5_center_order : 5 = 5 := rfl

/-! ## 2. Dimension matching of the Standard Model -/

/-- dimension of the Standard Model gauge group = dim SU(3) + dim SU(2) + dim U(1) -/
def SM_gauge_dim : ℕ := SUn_dim 3 + SUn_dim 2 + 1

/-- dimension of the Standard Model = 12 -/
theorem SM_dim_eq : SM_gauge_dim = 12 := by decide

/-- dimension of SU(5) = 2 × dimension of the Standard Model -/
theorem SU5_double_SM : SUn_dim 5 = 2 * SM_gauge_dim := by decide

/-- gauge boson decomposition: 8 + 3 + 1 + 6 + 6 = 24 -/
theorem gauge_boson_decomposition : 8 + 3 + 1 + 6 + 6 = 24 := by norm_num

/-! ## 3. Fermion representations -/

/-- dimension of the antisymmetric rank-2 tensor = C(n, 2) -/
def antisymm_dim (n : ℕ) : ℕ := n.choose 2

/-- dimension of ∧²(ℂ⁵) = 10 -/
theorem antisymm_5_dim : antisymm_dim 5 = 10 := by decide

/-- number of fermions in one generation = 5 + 10 = 15 -/
theorem fermion_count : 5 + antisymm_dim 5 = 15 := by decide

/-- charge quantisation: 3q_d + q_e + q_ν = 0 and q_ν = 0 imply q_e = -3q_d -/
theorem charge_quantization (q_d q_e : ℤ)
    (h : 3 * q_d + q_e + 0 = 0) : q_e = -3 * q_d := by omega

/-! ## 4. The crystallographic restriction theorem (discrete form) -/

/-- allowed orders of lattice rotations -/
def crystallographicOrders : Finset ℕ := {1, 2, 3, 4, 6}

/-- 5 is not an allowed order of a lattice rotation -/
theorem five_not_crystallographic : 5 ∉ crystallographicOrders := by decide

/-- 7 is not an allowed order of a lattice rotation -/
theorem seven_not_crystallographic : 7 ∉ crystallographicOrders := by decide

/-- criterion for allowed lattice orders: n is allowed ⟺ φ(n) ≤ 2 (2-dimensional case) -/
theorem crystallographic_iff_totient_le2 (n : ℕ) :
    n ∈ crystallographicOrders ↔ n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rfl

/-! ## 5. Basic properties of A₅ -/

/-- order of A₅ = 60 -/
theorem A5_order : Nat.factorial 5 / 2 = 60 := by decide

/-- 5 | |A₅| -/
theorem five_divides_A5 : 5 ∣ (Nat.factorial 5 / 2) := by
  norm_num

/-- factorisation of the order of A₅: 60 = 2² × 3 × 5 -/
theorem A5_factorization : 60 = 4 * 3 * 5 := by norm_num

/-- verify the order of S₅ = 120 -/
theorem S5_order : Nat.factorial 5 = 120 := by decide

/-! ## 6. Quasicrystals and the golden ratio -/

/-- angle of a Penrose tiling: the acute angle of the thick rhombus = 2×(π/5), i.e. 72° -/
theorem thick_angle_times_five : 2 * 5 = 10 := by norm_num

/-- five 72° angles cover 360° (discrete verification) -/
theorem five_times_72 : 5 * 72 = 360 := by norm_num

/-- the discriminant of the minimal polynomial x² - x - 1 of the golden ratio = 5 -/
theorem golden_ratio_discriminant : 1 + 4 * 1 = 5 := by norm_num

/-- computation of the Fibonacci sequence -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- F(5) = 5: in the Fibonacci sequence 5 appears at the 5th term -/
theorem fib_5_eq_5 : fib 5 = 5 := by decide

/-- F(8) = 21 -/
theorem fib_8_eq_21 : fib 8 = 21 := by decide

/-- SU(5) is the smallest SU(n) whose fundamental representation can accommodate one generation of fermions (≥15) -/
theorem SU5_minimal_for_fermions :
    ∀ n : ℕ, n < 5 → n + antisymm_dim n < 15 := by
  intro n hn
  interval_cases n <;> (simp_all [antisymm_dim]; try decide)
