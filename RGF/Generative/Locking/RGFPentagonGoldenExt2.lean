/-
  RGFPentagonGoldenExt2.lean — further absorption of the pentagon / golden-ratio algebra (third batch of new theorems)
  Further absorption of the Pentagon / Golden-ratio algebra (third batch).

  Building on RGFPentagonGolden.lean and RGFPentagonGoldenExt.lean, this file
  digests and absorbs the given "Pentagon-Golden Complete Algebra" paper, extracting the "new theorems"
  not yet covered by the two preceding files, including:

    · §1: the golden-ratio reciprocal bridge (2·cos(2π/5) = φ⁻¹, and φ⁻¹ = φ − 1)
    · §2: the sine proportionality identity sin(2π/5) = φ · sin(π/5)
    · §3: sine/cosine product identities of the regular pentagon
              (∏ sin(kπ/5) = 5/16, ∏ cos(kπ/5) = 1/16)
    · §4: Binet's formula φ^(n+1) − ψ^(n+1) = √5 · F(n+1)
    · §5: summary theorem

  All propositions are rigorously machine-verifiable purely mathematical conclusions, free of physical-modeling assumptions.
-/
import Mathlib
import RGF.Generative.Locking.RGFPentagonGolden
import RGF.Generative.Locking.RGFPentagonGoldenExt
-- Unified deduplication: reference the authoritative shared module (pentagon — golden-ratio algebra).
-- To avoid clashing with theorems of the same name in the already-`open`ed local namespaces,
-- we do not `open` the shared namespace here and use fully qualified names at the reference sites.
import RGF.Generative.Locking.PentagonComplete
import RGF.Generative.Locking.PentagonNew

open Real

namespace RGFPentagonGoldenExt2

open RGFPentagonGolden RGFPentagonGoldenExt

/-! ============================================================
    §1: the golden-ratio reciprocal bridge
    ============================================================ -/

/-
φ⁻¹ = φ − 1.
-/
lemma golden_inv_eq_golden_sub_one : goldenRatio⁻¹ = goldenRatio - 1 :=
  -- Unified deduplication: directly reference the shared module `RGF.PentagonNew.golden_inv_eq`.
  RGF.PentagonNew.golden_inv_eq

/-
Golden-ratio reciprocal bridge: 2·cos(2π/5) = φ⁻¹.
    (Together with 2·cos(π/5) = φ, the regular pentagon encodes both φ and φ⁻¹ simultaneously.)
-/
lemma two_cos_two_pi_div_five_eq_golden_inv :
    2 * Real.cos (2 * π / 5) = goldenRatio⁻¹ := by
  have := RGFPentagonGolden.alpha_val;
  unfold alpha at this;
  grind +suggestions

/-
cos(2π/5) = φ⁻¹ / 2.
-/
lemma cos_two_pi_div_five_eq_half_golden_inv :
    Real.cos (2 * π / 5) = goldenRatio⁻¹ / 2 := by
  have := two_cos_two_pi_div_five_eq_golden_inv
  field_simp [this] at *;
  exact this

/-
cos(π/5) = φ / 2.
-/
lemma cos_pi_div_five_eq_half_golden :
    Real.cos (π / 5) = goldenRatio / 2 := by
  linarith [ two_cos_pi_div_five_eq_golden ]

/-! ============================================================
    §2: sine proportionality identity
    ============================================================ -/

/-
Sine proportionality identity: sin(2π/5) = φ · sin(π/5).
    (Obtained directly from the double-angle formula sin 2θ = 2 sinθ cosθ and 2 cos(π/5) = φ.)
-/
lemma sin_two_pi_div_five_eq_golden_mul_sin :
    Real.sin (2 * π / 5) = goldenRatio * Real.sin (π / 5) := by
  rw [show (2:ℝ) * π / 5 = 2 * (π/5) by ring, Real.sin_two_mul,
      ← RGFPentagonGolden.two_cos_pi_div_five_eq_golden]; ring

/-! ============================================================
    §3: sine/cosine product identities of the regular pentagon
    ============================================================ -/

/-
sin(3π/5) = sin(2π/5).
-/
lemma sin_three_pi_div_five_eq :
    Real.sin (3 * π / 5) = Real.sin (2 * π / 5) := by
  convert Real.sin_pi_sub _ using 2 ; ring

/-
sin(4π/5) = sin(π/5).
-/
lemma sin_four_pi_div_five_eq :
    Real.sin (4 * π / 5) = Real.sin (π / 5) := by
  convert Real.sin_pi_sub _ using 2 ; ring

/-
Pentagon sine product: ∏_{k=1}^{4} sin(kπ/5) = 5/16
    (this is the special case n = 5 of the classical formula ∏_{k=1}^{n-1} sin(kπ/n) = n / 2^(n-1)).
-/
lemma pentagon_sin_product :
    Real.sin (π / 5) * Real.sin (2 * π / 5) *
      Real.sin (3 * π / 5) * Real.sin (4 * π / 5) = 5 / 16 := by
  convert congr_arg₂ ( · * · ) RGFPentagonGoldenExt.sin_sq_pi_div_five RGFPentagonGoldenExt.sin_sq_two_pi_div_five using 1 <;> ring_nf at *;
  · rw [ show Real.pi * ( 3 / 5 ) = Real.pi - Real.pi * ( 2 / 5 ) by ring, show Real.pi * ( 4 / 5 ) = Real.pi - Real.pi * ( 1 / 5 ) by ring, Real.sin_pi_sub, Real.sin_pi_sub ] ; ring;
  · norm_num

/-
Pentagon cosine product: ∏_{k=1}^{4} cos(kπ/5) = 1/16.
-/
lemma pentagon_cos_product :
    Real.cos (π / 5) * Real.cos (2 * π / 5) *
      Real.cos (3 * π / 5) * Real.cos (4 * π / 5) = 1 / 16 := by
  grind +suggestions

/-! ============================================================
    §4: Binet's formula
    ============================================================ -/

/-
Binet's formula (difference form): φ^(n+1) − ψ^(n+1) = √5 · F(n+1).
    (Subtract φ^(n+1) = F(n+1)·φ + F(n) and ψ^(n+1) = F(n+1)·ψ + F(n),
      then use φ − ψ = √5.)
-/
lemma binet_identity (n : ℕ) :
    goldenRatio ^ (n + 1) - goldenConj ^ (n + 1) = Real.sqrt 5 * (Nat.fib (n + 1) : ℝ) := by
  -- Unified deduplication: the shared module's `psi` is definitionally equal (defeq) to Mathlib's `goldenConj`,
  -- so it can be derived directly from `RGF.PentagonNew.golden_sub_psi_pow` (only commuting multiplication).
  have h := RGF.PentagonNew.golden_sub_psi_pow n
  rw [show (Real.goldenConj) = RGF.PentagonComplete.psi from rfl, h]; ring

/-! ============================================================
    §5: summary theorem
    ============================================================ -/

/-- **Third-batch summary theorem**: further closure of the pentagon — golden-ratio algebra.
    (i) the golden-ratio reciprocal bridge 2·cos(2π/5) = φ⁻¹, and φ⁻¹ = φ − 1;
    (ii) the sine proportionality identity sin(2π/5) = φ · sin(π/5);
    (iii) the pentagon sine product ∏ sin(kπ/5) = 5/16;
    (iv) the pentagon cosine product ∏ cos(kπ/5) = 1/16;
    (v) Binet's formula φ^(n+1) − ψ^(n+1) = √5 · F(n+1). -/
theorem pentagon_golden_ext2_complete :
    (2 * Real.cos (2 * π / 5) = goldenRatio⁻¹ ∧ goldenRatio⁻¹ = goldenRatio - 1) ∧
    (Real.sin (2 * π / 5) = goldenRatio * Real.sin (π / 5)) ∧
    (Real.sin (π / 5) * Real.sin (2 * π / 5) *
      Real.sin (3 * π / 5) * Real.sin (4 * π / 5) = 5 / 16) ∧
    (Real.cos (π / 5) * Real.cos (2 * π / 5) *
      Real.cos (3 * π / 5) * Real.cos (4 * π / 5) = 1 / 16) ∧
    (∀ n : ℕ, goldenRatio ^ (n + 1) - goldenConj ^ (n + 1)
        = Real.sqrt 5 * (Nat.fib (n + 1) : ℝ)) :=
  ⟨⟨two_cos_two_pi_div_five_eq_golden_inv, golden_inv_eq_golden_sub_one⟩,
    sin_two_pi_div_five_eq_golden_mul_sin,
    pentagon_sin_product, pentagon_cos_product, binet_identity⟩

end RGFPentagonGoldenExt2
