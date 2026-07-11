import Mathlib

/-!
# Independence test of the KAM / Diophantine criterion (a machine-verified negative result)

This file formalizes and tests the "KAM/Diophantine stability criterion" proposed
by the user. The idea of the criterion is: map each `k` to
`cosVal k = 2·cos(2π/k)`; if this value lies in the "golden-ratio equivalence
class" `IsGoldenClass` (i.e. satisfies some integer-coefficient quadratic equation
whose discriminant is exactly `5`), then `k` is called "stable".

## Exact algebraic relations (basic lemmas)

* `cos_2pi_div_5_min_poly`: `2cos(2π/5)` satisfies `x² + x − 1 = 0`;
* `cos_2pi_div_10_min_poly`: `2cos(2π/10)` satisfies `x² − x − 1 = 0` (the
  defining equation of the golden ratio φ);
* `golden_equivalence_5_10`: their product is exactly `1` (an exact identity, not
  an approximation).

These use Mathlib's `Real.cos_pi_div_five : cos(π/5) = (1 + √5)/4` together with
the double-angle formula.

## Core test result (negative result)

The discriminant criterion cannot uniquely single out the "stable" `k` as `k = 5`:
both `5` and `10` satisfy the criterion (the discriminants of the corresponding
quadratic equations both equal `5`). Hence the proposition `KAMStable k ↔ k = 5`
is false.

* `kam_stable_five`: `5` is stable (`x²+x−1=0`, discriminant `1−4·1·(−1)=5`);
* `kam_stable_ten_too`: `10` is also stable (`x²−x−1=0`, discriminant `1+4=5`);
* `kam_stable_not_unique` / `kam_criterion_selects_five_and_ten_not_uniquely`:
  formally refute the uniqueness claim `∀ k ≥ 3, (KAMStable k ↔ k = 5)`.

This is a **clean, machine-verified negative result**: alongside the Laplacian
spectrum's `lock_stability`, it helps delineate the boundary of "which criteria
independent of group theory have already been ruled out" — this criterion selects
`{5, 10}` rather than the unique `{5}`.
-/

namespace RGF.KAMDiophantine

open Real

/-- Algebraic characterization of the stability criterion: `x` belongs to the
"golden-ratio equivalence class" if and only if it satisfies some
integer-coefficient quadratic equation whose discriminant is exactly `5`. -/
def IsGoldenClass (x : ℝ) : Prop :=
  ∃ a b c : ℤ, a ≠ 0 ∧ b ^ 2 - 4 * a * c = 5 ∧ (a : ℝ) * x ^ 2 + b * x + c = 0

/-- The value `2·cos(2π/k)` to which the criterion maps `k`. -/
noncomputable def cosVal (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi / k)

/-- KAM/Diophantine stability criterion: `k` is stable if and only if `cosVal k`
lies in the golden-ratio equivalence class. -/
def KAMStable (k : ℕ) : Prop := IsGoldenClass (cosVal k)

/-- Basic algebraic relation: `2cos(2π/5)` satisfies `x² + x − 1 = 0`. -/
theorem cos_2pi_div_5_min_poly :
    (2 * Real.cos (2 * Real.pi / 5)) ^ 2 + (2 * Real.cos (2 * Real.pi / 5)) - 1 = 0 := by
  have h : (2 : ℝ) * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h5, Real.sqrt_nonneg 5]

/-- Basic algebraic relation: `2cos(2π/10)` satisfies `x² − x − 1 = 0` (i.e. the
defining equation of the golden ratio φ). -/
theorem cos_2pi_div_10_min_poly :
    (2 * Real.cos (2 * Real.pi / 10)) ^ 2 - (2 * Real.cos (2 * Real.pi / 10)) - 1 = 0 := by
  have h : (2 : ℝ) * Real.pi / 10 = Real.pi / 5 := by ring
  rw [h, Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h5, Real.sqrt_nonneg 5]

/-- Exact algebraic identity: `2cos(2π/5) · 2cos(2π/10) = 1` (not an approximate
coincidence). -/
theorem golden_equivalence_5_10 :
    (2 * Real.cos (2 * Real.pi / 5)) * (2 * Real.cos (2 * Real.pi / 10)) = 1 := by
  have ha : (2 : ℝ) * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  have hb : (2 : ℝ) * Real.pi / 10 = Real.pi / 5 := by ring
  rw [ha, hb, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h5, Real.sqrt_nonneg 5]

/-- `5` satisfies the criterion: `2cos(2π/5)` satisfies `x² + x − 1 = 0`, with
discriminant `1² − 4·1·(−1) = 5`. -/
theorem kam_stable_five : KAMStable 5 := by
  refine ⟨1, 1, -1, by norm_num, by norm_num, ?_⟩
  have := cos_2pi_div_5_min_poly
  simp only [cosVal, Nat.cast_ofNat]
  push_cast
  nlinarith [this]

/-- `10` also satisfies the criterion: `2cos(2π/10)` satisfies `x² − x − 1 = 0`,
with discriminant `(−1)² + 4 = 5`. -/
theorem kam_stable_ten_too : KAMStable 10 := by
  refine ⟨1, -1, -1, by norm_num, by norm_num, ?_⟩
  have := cos_2pi_div_10_min_poly
  simp only [cosVal, Nat.cast_ofNat]
  push_cast
  nlinarith [this]

/-- The key exclusivity test (negative result): the uniqueness claim
`∀ k ≥ 3, (KAMStable k ↔ k = 5)` is false, because `10 ≠ 5` yet also satisfies the
criterion. -/
theorem kam_stable_not_unique :
    ¬ (∀ k : ℕ, k ≥ 3 → (KAMStable k ↔ k = 5)) := by
  intro h
  have h10 := (h 10 (by norm_num)).mp kam_stable_ten_too
  norm_num at h10

/-- The formal negative conclusion recorded on the "criteria already tried" audit
list: this discriminant criterion, independent of group theory, selects `{5, 10}`
rather than the unique `{5}`. It stands alongside `lock_stability` (the Laplacian
spectrum negative result). -/
theorem kam_criterion_selects_five_and_ten_not_uniquely :
    KAMStable 5 ∧ KAMStable 10 ∧ ¬ (∀ k : ℕ, k ≥ 3 → (KAMStable k ↔ k = 5)) :=
  ⟨kam_stable_five, kam_stable_ten_too, kam_stable_not_unique⟩

end RGF.KAMDiophantine
