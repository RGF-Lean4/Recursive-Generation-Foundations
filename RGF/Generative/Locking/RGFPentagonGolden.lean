/-
  RGFPentagonGolden.lean — absorbing the pentagon / golden-ratio / Fibonacci / ℤ₅ algebra into the RGF theory
  Absorbing the Pentagon / Golden-ratio / Fibonacci / ℤ₅ algebra into the RGF theory.

  This file systematically absorbs the new "regular pentagon — golden ratio — Fibonacci — ℤ₅" theorems developed in the sister work
  into the RGF locking-membrane framework, providing an algebro-geometric foundation for "why the locking value k = 5".

  The core of the RGF framework is the k = 5 locking membrane (num2DIrreps, D₅, A₅, PSL(2,7)). The regular pentagon is
  the only regular polygon directly linking "five-fold symmetry" with the "golden ratio", and its cosine algebra precisely encodes
  the structure of the five-fold symmetry group D₅ and the cyclic structure of ℤ₅. This file proves:

    · §1: cosine algebra of the regular pentagon (cos π/5, cos 2π/5 and their quadratic equation and Vieta relations)
    · §2: the precise connection between the golden ratio φ and the pentagon and Fibonacci sequence
    · §3: the field structure of ℤ₅ (five-element cycle)
    · §4: bridging the five-fold symmetry groups D₅ (order 10), A₅ (order 60) with the RGF locking value k = 5

  All propositions are rigorously verifiable purely mathematical conclusions, absorbed from the "new theorems" of the sister project and connected to
  the existing num2DIrreps / locking-membrane structure of this project.
-/
import Mathlib
import RGF.Generative.Locking.LockingMembrane
-- Unified deduplication: reference the authoritative shared module (pentagon — golden-ratio algebra).
-- To avoid clashing with theorems of the same name in this file's local namespace `RGFPentagonGolden`,
-- we do not `open` the shared namespace here, but use fully qualified names at the reference sites:
-- `RGF.PentagonComplete.*` / `RGF.PentagonNew.*`.
import RGF.Generative.Locking.PentagonComplete
import RGF.Generative.Locking.PentagonNew

open Real

namespace RGFPentagonGolden

/-! ============================================================
    §1: cosine algebra of the regular pentagon
    ============================================================ -/

/-- α := cos(2π/5), the "angular-momentum coefficient" of the regular pentagon. -/
noncomputable def alpha : ℝ := Real.cos (2 * π / 5)

/-- cos(π/5) = (1 + √5)/4 (taken from Mathlib, recorded here as a reference). -/
lemma cos_pi_div_five_val : Real.cos (π / 5) = (1 + Real.sqrt 5) / 4 :=
  Real.cos_pi_div_five

/-- α = cos(2π/5) = (√5 − 1)/4.
    Unified deduplication: equivalent to the shared module `RGF.PentagonComplete.cos_two_pi_div_five`. -/
lemma alpha_val : alpha = (Real.sqrt 5 - 1) / 4 := by
  rw [alpha]; exact RGF.PentagonComplete.cos_two_pi_div_five

/-- α is a root of the pentagon's quadratic equation 4x² + 2x − 1 = 0. -/
lemma alpha_root : 4 * alpha ^ 2 + 2 * alpha - 1 = 0 := by
  rw [alpha_val]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- cos(4π/5) = (−1 − √5)/4.
    Unified deduplication: directly reference the shared module `RGF.PentagonNew.cos_four_pi_div_five`. -/
lemma cos_four_pi_div_five_val :
    Real.cos (4 * π / 5) = (-1 - Real.sqrt 5) / 4 :=
  RGF.PentagonNew.cos_four_pi_div_five

/-- cos(4π/5) is the second root of the same quadratic equation 4x² + 2x − 1 = 0. -/
lemma cos_four_pi_div_five_root :
    4 * (Real.cos (4 * π / 5)) ^ 2 + 2 * (Real.cos (4 * π / 5)) - 1 = 0 := by
  rw [cos_four_pi_div_five_val]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- Vieta relation: sum of the two roots = −1/2. -/
lemma pentagon_roots_sum : alpha + Real.cos (4 * π / 5) = -1 / 2 := by
  rw [alpha_val, cos_four_pi_div_five_val]; ring

/-- Vieta relation: product of the two roots = −1/4. -/
lemma pentagon_roots_prod : alpha * Real.cos (4 * π / 5) = -1 / 4 := by
  rw [alpha_val, cos_four_pi_div_five_val]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-! ============================================================
    §2: the golden ratio with the regular pentagon and Fibonacci
    ============================================================ -/

/-- 2·cos(π/5) = φ: the ratio diagonal/side of the regular pentagon is exactly the golden ratio. -/
lemma two_cos_pi_div_five_eq_golden :
    2 * Real.cos (π / 5) = goldenRatio := by
  rw [Real.cos_pi_div_five, Real.goldenRatio]; ring

/-- φ = 1 + 2α: the golden ratio is linearly determined by the angular-momentum coefficient α. -/
lemma golden_eq_one_add_two_alpha : goldenRatio = 1 + 2 * alpha := by
  rw [alpha_val, Real.goldenRatio]; ring

/-- α·φ = 1/2. -/
lemma alpha_mul_golden : alpha * goldenRatio = 1 / 2 := by
  rw [alpha_val, Real.goldenRatio]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- φ² = φ + 1.
    Unified deduplication: directly reference the shared module `RGF.PentagonComplete.golden_sq_eq_golden_add_one`. -/
lemma golden_sq : goldenRatio ^ 2 = goldenRatio + 1 :=
  RGF.PentagonComplete.golden_sq_eq_golden_add_one

/-- Fibonacci power formula of the golden ratio: φ^(n+1) = F(n+1)·φ + F(n).
    Unified deduplication: directly reference the shared module `RGF.PentagonComplete.golden_pow_succ`. -/
lemma golden_pow_succ (n : ℕ) :
    goldenRatio ^ (n + 1) = (Nat.fib (n + 1) : ℝ) * goldenRatio + (Nat.fib n : ℝ) :=
  RGF.PentagonComplete.golden_pow_succ n

/-! ============================================================
    §3: field structure of ℤ₅ (five-element cycle)
    ============================================================ -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- ℤ/5 is a field. -/
example : Field (ZMod 5) := inferInstance

/-- |ℤ/5| = 5. -/
lemma zmod5_card : Fintype.card (ZMod 5) = 5 := by simp

/-- The order of the multiplicative unit group of ℤ/5 = 4 = φ(5). -/
lemma zmod5_units_card : Fintype.card (ZMod 5)ˣ = 4 := by decide

/-! ============================================================
    §4: bridging the five-fold symmetry groups with the RGF locking k = 5
    ============================================================ -/

/-- The order of the dihedral group D₅ = 10 = 2·5 (the symmetry group of the regular pentagon). -/
lemma dihedral_five_card : Fintype.card (DihedralGroup 5) = 10 := by
  rw [DihedralGroup.card]

/-- The order of A₅ = 60. -/
lemma A5_card : Fintype.card (alternatingGroup (Fin 5)) = 60 := by decide

/-- The order of A₅ = 5!/2. -/
lemma A5_card_eq_factorial_div :
    Fintype.card (alternatingGroup (Fin 5)) = Nat.factorial 5 / 2 := by decide

/-- At the RGF locking value k = 5, the number of two-dimensional irreps n₂(5) = 2,
    exactly equal to the number of roots of the pentagon's quadratic 4x²+2x−1. -/
lemma num2DIrreps_five : num2DIrreps 5 = 2 := by decide

/-- **Bridging main theorem**: the regular pentagon — golden ratio — ℤ₅ — five-fold symmetry groups converge at the RGF locking value k = 5.
    (i) n₂(5) = 2, exactly the number of roots of the pentagon's quadratic;
    (ii) the symmetry group D₅ of the regular pentagon has order 10;
    (iii) the five-element cyclic field ℤ₅ has cardinality 5;
    (iv) α = cos(2π/5) satisfies the pentagon's quadratic 4α²+2α−1 = 0;
    (v) the golden ratio is linearly determined by α: φ = 1 + 2α. -/
theorem pentagon_locking_unification :
    num2DIrreps 5 = 2 ∧
    Fintype.card (DihedralGroup 5) = 10 ∧
    Fintype.card (ZMod 5) = 5 ∧
    4 * alpha ^ 2 + 2 * alpha - 1 = 0 ∧
    goldenRatio = 1 + 2 * alpha :=
  ⟨num2DIrreps_five, dihedral_five_card, zmod5_card, alpha_root,
    golden_eq_one_add_two_alpha⟩

end RGFPentagonGolden
