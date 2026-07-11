/-
  RequestProject/RecursiveGenerativeConstant.lean

  Original Mathematics V — the pentagonal recursive constant `ρ`.

  We fuse the two RGF core ingredients:
    * the pentagonal locking constant `α = cos(2π/5)`,
    * a recursive generation mechanism.

  Define the pentagon-weighted recursion
      x₀ = 0,  x₁ = 1,  xₙ₊₂ = xₙ₊₁ + α · xₙ
  (the weight is `α`, not the ordinary Fibonacci weight `1`).

  Its characteristic equation `x² = x + α` has principal root
      ρ = (1 + ⁴√5) / 2,
  a genuinely new constant: not the golden ratio `φ`, not `α`, not any
  pre-existing constant — a new level that grows naturally when recursion acts
  on the pentagonal constant.

  Core theorems:
    * `tower_relation`  : `(2ρ - 1)² = 2φ - 1`   (ρ sits one level below φ)
    * Vieta system      : `ρ + ρ' = 1`, `ρ·ρ' = -α`, `ρ - ρ' = ⁴√5`
    * `rho_minpoly`     : `4ρ⁴ - 8ρ³ + 6ρ² - 2ρ - 1 = 0`
    * `alpha_pentagon`  : `4α² + 2α - 1 = 0`     (the pentagon kernel)
    * `binet`           : `Pₙ = (ρⁿ - ρ'ⁿ)/⁴√5`  (closed form)
    * `alpha_eq_cos`    : `α = cos(2π/5)`
-/
import Mathlib

namespace RGF.PentRho

open Real

/-- The fourth root of `5`, written `⁴√5`. -/
noncomputable def q5 : ℝ := Real.sqrt (Real.sqrt 5)

/-- The pentagonal locking constant `α = cos(2π/5) = (√5 - 1)/4`. -/
noncomputable def palpha : ℝ := (Real.sqrt 5 - 1) / 4

/-- The principal root `ρ = (1 + ⁴√5)/2`. -/
noncomputable def rho : ℝ := (1 + q5) / 2

/-- The conjugate root `ρ' = (1 - ⁴√5)/2`. -/
noncomputable def rho' : ℝ := (1 - q5) / 2

/-- The golden ratio `φ = (1 + √5)/2`. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-! ### Basic radical identities -/

theorem sqrt5_nonneg : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem q5_nonneg : (0 : ℝ) ≤ q5 := Real.sqrt_nonneg _

/-- `(⁴√5)² = √5`. -/
theorem q5_sq : q5 ^ 2 = Real.sqrt 5 := by
  unfold q5; exact Real.sq_sqrt sqrt5_nonneg

/-- `(⁴√5)⁴ = 5`. -/
theorem q5_pow4 : q5 ^ 4 = 5 := by
  have : q5 ^ 4 = (q5 ^ 2) ^ 2 := by ring
  rw [this, q5_sq, sqrt5_sq]

/-! ### The pentagon kernel and the characteristic equation -/

/-- The pentagonal constant satisfies the pentagon kernel `4α² + 2α - 1 = 0`. -/
theorem alpha_pentagon : 4 * palpha ^ 2 + 2 * palpha - 1 = 0 := by
  unfold palpha
  have h := sqrt5_sq
  nlinarith [h]

/-- `ρ` satisfies the characteristic equation `ρ² = ρ + α`. -/
theorem rho_char : rho ^ 2 = rho + palpha := by
  unfold rho palpha
  have h := q5_sq
  nlinarith [h]

/-- `ρ'` satisfies the characteristic equation `ρ'² = ρ' + α`. -/
theorem rho'_char : rho' ^ 2 = rho' + palpha := by
  unfold rho' palpha
  have h := q5_sq
  nlinarith [h]

/-! ### Vieta system -/

theorem vieta_sum : rho + rho' = 1 := by unfold rho rho'; ring

theorem vieta_prod : rho * rho' = -palpha := by
  unfold rho rho' palpha
  have h := q5_sq
  nlinarith [h]

theorem vieta_diff : rho - rho' = q5 := by unfold rho rho'; ring

/-! ### Tower relation -/

/-- The signature identity: `(2ρ - 1)² = 2φ - 1` (both equal `√5`). -/
theorem tower_relation : (2 * rho - 1) ^ 2 = 2 * phi - 1 := by
  unfold rho phi
  have h := q5_sq
  nlinarith [h]

/-! ### Minimal polynomial -/

/-- `ρ` is a root of `4x⁴ - 8x³ + 6x² - 2x - 1`, whose kernel is the pentagon
    equation. -/
theorem rho_minpoly : 4 * rho ^ 4 - 8 * rho ^ 3 + 6 * rho ^ 2 - 2 * rho - 1 = 0 := by
  have hchar : rho ^ 2 = rho + palpha := rho_char
  have hpent : 4 * palpha ^ 2 + 2 * palpha - 1 = 0 := alpha_pentagon
  nlinarith [hchar, hpent, sq_nonneg rho]

/-! ### The pentagon-weighted recursion and its Binet closed form -/

/-- The pentagon-weighted recursion `P₀=0, P₁=1, Pₙ₊₂ = Pₙ₊₁ + α·Pₙ`. -/
noncomputable def P : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | (n + 2) => P (n + 1) + palpha * P n

@[simp] theorem P_zero : P 0 = 0 := rfl
@[simp] theorem P_one : P 1 = 1 := rfl
theorem P_succ_succ (n : ℕ) : P (n + 2) = P (n + 1) + palpha * P n := rfl

theorem q5_pos : 0 < q5 := by
  unfold q5
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

/--
Binet closed form: `Pₙ = (ρⁿ - ρ'ⁿ)/⁴√5`.
-/
theorem binet (n : ℕ) : P n = (rho ^ n - rho' ^ n) / q5 := by
  induction' n using Nat.strongRecOn with n ih;
  rcases n with ( _ | _ | n ) <;> simp_all +decide;
  · grind +suggestions;
  · rw [ P_succ_succ, ih _ <| Nat.le_succ _, ih _ <| Nat.le_refl _ ] ; ring;
    rw [ show rho ^ 2 = rho + palpha by exact rho_char, show rho' ^ 2 = rho' + palpha by exact rho'_char ] ; ring

/-! ### Trigonometric identification -/

/--
`α = cos(2π/5)`.
-/
theorem alpha_eq_cos : palpha = Real.cos (2 * Real.pi / 5) := by
  rw [ show 2 * Real.pi / 5 = 2 * ( Real.pi / 5 ) by ring, Real.cos_two_mul, Real.cos_pi_div_five ] ; ring ; norm_num [ Real.sqrt_nonneg ] ; ring;
  unfold palpha; ring;

end RGF.PentRho