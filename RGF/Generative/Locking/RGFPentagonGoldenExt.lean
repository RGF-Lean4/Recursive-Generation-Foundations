/-
  RGFPentagonGoldenExt.lean — extended absorption of the pentagon / golden-ratio algebra (second batch of new theorems)
  Extended absorption of the Pentagon / Golden-ratio algebra (second batch).

  Building on RGFPentagonGolden.lean, this file continues to absorb the new "regular pentagon — golden ratio — Fibonacci — ℤ₅" theorems
  derived in the sister work (RCD / RFD / RST), systematically completing the cosine/sine/tangent algebra, the golden-conjugate ψ algebra,
  and higher-order Fibonacci power towers that the project previously only touched on sporadically, so that the
  pentagon — golden-ratio algebra behind the RGF locking value k = 5 closes more completely within this project.

    · §1: completion of the pentagon cosine algebra (cos 3π/5, the conjugate quadratic equation, classical identities, cos² values)
    · §2: sine algebra (exact sin² values, products, Pythagorean-type sums, positivity)
    · §3: tangent algebra (exact tan² values, products, positivity)
    · §4: algebra of the golden conjugate ψ = (1−√5)/2 and Fibonacci/Lucas expansions
    · §5: higher-order Fibonacci power towers (φ⁸, φ⁹)
    · §6: summary theorem

  All propositions are rigorously machine-verifiable purely mathematical conclusions, free of physical-modeling assumptions.
-/
import Mathlib
import RGF.Generative.Locking.RGFPentagonGolden
-- Unified deduplication: reference the authoritative shared module (pentagon — golden-ratio algebra).
-- To avoid clashing with theorems of the same name in the already-`open`ed `RGFPentagonGolden`,
-- we do not `open` the shared namespace here and use fully qualified names at the reference sites.
import RGF.Generative.Locking.PentagonComplete
import RGF.Generative.Locking.PentagonNew

open Real

namespace RGFPentagonGoldenExt

open RGFPentagonGolden

/-! ============================================================
    §1: completion of the pentagon cosine algebra
    ============================================================ -/

/-
cos(3π/5) = (1 − √5)/4.
-/
lemma cos_three_pi_div_five_val :
    Real.cos (3 * π / 5) = (1 - Real.sqrt 5) / 4 :=
  -- Unified deduplication: directly reference the shared module `RGF.PentagonNew.cos_three_pi_div_five`.
  RGF.PentagonNew.cos_three_pi_div_five

/-
cos(π/5) is a root of the conjugate quadratic equation 4x² − 2x − 1 = 0.
-/
lemma cos_pi_div_five_conj_root :
    4 * (Real.cos (π / 5)) ^ 2 - 2 * (Real.cos (π / 5)) - 1 = 0 := by
      have := Real.cos_three_mul ( Real.pi / 5 ) ; rw [ ( by ring : 3 * ( Real.pi / 5 ) = Real.pi - 2 * ( Real.pi / 5 ) ), Real.cos_pi_sub, Real.cos_two_mul ] at this ; nlinarith [ show 0 < Real.cos ( Real.pi / 5 ) from Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ] ;

/-
cos(3π/5) is the second root of the same conjugate quadratic equation 4x² − 2x − 1 = 0.
-/
lemma cos_three_pi_div_five_conj_root :
    4 * (Real.cos (3 * π / 5)) ^ 2 - 2 * (Real.cos (3 * π / 5)) - 1 = 0 := by
      norm_num [ show 3 * Real.pi / 5 = Real.pi - 2 * Real.pi / 5 by ring, Real.cos_pi_sub ];
      convert alpha_root using 1

/-
Conjugate Vieta relation: sum of the two roots = 1/2.
-/
lemma conj_roots_sum :
    Real.cos (π / 5) + Real.cos (3 * π / 5) = 1 / 2 := by
      convert congr_arg₂ ( · + · ) cos_pi_div_five_val cos_three_pi_div_five_val using 1 ; ring

/-
Conjugate Vieta relation: product of the two roots = −1/4.
-/
lemma conj_roots_prod :
    Real.cos (π / 5) * Real.cos (3 * π / 5) = -1 / 4 := by
      grind +suggestions

/-
Classical identity: cos(π/5)·cos(2π/5) = 1/4.
-/
lemma cos_pi_mul_cos_two_pi : Real.cos (π / 5) * alpha = 1 / 4 := by
  rw [RGFPentagonGolden.alpha_val, Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-
Classical identity: cos(π/5) − cos(2π/5) = 1/2.
-/
lemma cos_pi_sub_cos_two_pi : Real.cos (π / 5) - alpha = 1 / 2 := by
  rw [Real.cos_pi_div_five, RGFPentagonGolden.alpha_val]; ring

/-
cos²(π/5) = (3 + √5)/8.
-/
lemma cos_sq_pi_div_five : (Real.cos (π / 5)) ^ 2 = (3 + Real.sqrt 5) / 8 := by
  rw [Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-
cos²(2π/5) = (3 − √5)/8.
-/
lemma cos_sq_two_pi_div_five : alpha ^ 2 = (3 - Real.sqrt 5) / 8 := by
  rw [RGFPentagonGolden.alpha_val]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-! ============================================================
    §2: sine algebra
    ============================================================ -/

/-
sin²(π/5) = (5 − √5)/8.
-/
lemma sin_sq_pi_div_five : (Real.sin (π / 5)) ^ 2 = (5 - Real.sqrt 5) / 8 := by
  have h := Real.sin_sq_add_cos_sq (π/5)
  rw [cos_sq_pi_div_five] at h; linarith

/-
sin²(2π/5) = (5 + √5)/8.
-/
lemma sin_sq_two_pi_div_five : (Real.sin (2 * π / 5)) ^ 2 = (5 + Real.sqrt 5) / 8 := by
  have h := Real.sin_sq_add_cos_sq (2*π/5)
  have hc : (Real.cos (2*π/5))^2 = (3 - Real.sqrt 5)/8 := cos_sq_two_pi_div_five
  rw [hc] at h; linarith

/-
Pythagorean-type sum: sin²(π/5) + sin²(2π/5) = 5/4.
-/
lemma sin_sq_sum : (Real.sin (π / 5)) ^ 2 + (Real.sin (2 * π / 5)) ^ 2 = 5 / 4 := by
  rw [sin_sq_pi_div_five, sin_sq_two_pi_div_five]; ring

/-
sin(π/5) > 0.
-/
lemma sin_pi_div_five_pos : 0 < Real.sin (π / 5) := by
  exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith [ Real.pi_pos ] )

/-
sin(2π/5) > 0.
-/
lemma sin_two_pi_div_five_pos : 0 < Real.sin (2 * π / 5) := by
  exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith [ Real.pi_pos ] )

/-
sin(π/5)·sin(2π/5) = √5/4.
-/
lemma sin_mul_sin : Real.sin (π / 5) * Real.sin (2 * π / 5) = Real.sqrt 5 / 4 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h1 : (0:ℝ) ≤ Real.sin (π/5) * Real.sin (2*π/5) :=
    mul_nonneg sin_pi_div_five_pos.le sin_two_pi_div_five_pos.le
  have h2 : (0:ℝ) ≤ Real.sqrt 5 / 4 := by positivity
  have key : (Real.sin (π/5) * Real.sin (2*π/5))^2 = (Real.sqrt 5/4)^2 := by
    rw [mul_pow, sin_sq_pi_div_five, sin_sq_two_pi_div_five]; nlinarith [h5]
  nlinarith [key, h1, h2, sq_nonneg (Real.sin (π/5) * Real.sin (2*π/5) - Real.sqrt 5/4)]

/-! ============================================================
    §3: tangent algebra
    ============================================================ -/

/-
tan²(π/5) = 5 − 2√5.
-/
lemma tan_sq_pi_div_five : (Real.tan (π / 5)) ^ 2 = 5 - 2 * Real.sqrt 5 := by
  rw [ Real.tan_eq_sin_div_cos, div_pow, sin_sq_pi_div_five, cos_sq_pi_div_five ];
  grind

/-
tan²(2π/5) = 5 + 2√5.
-/
lemma tan_sq_two_pi_div_five : (Real.tan (2 * π / 5)) ^ 2 = 5 + 2 * Real.sqrt 5 := by
  rw [ Real.tan_eq_sin_div_cos, div_pow, sin_sq_two_pi_div_five, show ( Real.cos ( 2 * Real.pi / 5 ) ) ^ 2 = ( ( Real.sqrt 5 - 1 ) / 4 ) ^ 2 by
                                                                  convert congr_arg ( · ^ 2 ) ( alpha_val ) using 1 ] ; ring_nf ; norm_num;
  grind +qlia

/-
tan(π/5) > 0.
-/
lemma tan_pi_div_five_pos : 0 < Real.tan (π / 5) := by
  exact Real.tan_pos_of_pos_of_lt_pi_div_two ( by positivity ) ( by linarith [ Real.pi_pos ] )

/-
tan(2π/5) > 0.
-/
lemma tan_two_pi_div_five_pos : 0 < Real.tan (2 * π / 5) := by
  exact Real.tan_pos_of_pos_of_lt_pi_div_two ( by positivity ) ( by linarith [ Real.pi_pos ] )

/-
tan(π/5)·tan(2π/5) = √5.
-/
lemma tan_mul_tan : Real.tan (π / 5) * Real.tan (2 * π / 5) = Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h1 : (0:ℝ) ≤ Real.tan (π/5) * Real.tan (2*π/5) :=
    mul_nonneg tan_pi_div_five_pos.le tan_two_pi_div_five_pos.le
  have h2 : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have key : (Real.tan (π/5) * Real.tan (2*π/5))^2 = (Real.sqrt 5)^2 := by
    rw [mul_pow, tan_sq_pi_div_five, tan_sq_two_pi_div_five]; nlinarith [h5]
  nlinarith [key, h1, h2, sq_nonneg (Real.tan (π/5) * Real.tan (2*π/5) - Real.sqrt 5)]

/-! ============================================================
    §4: golden conjugate ψ = (1 − √5)/2
    ============================================================ -/

/-
ψ = goldenConj = (1 − √5)/2.
-/
lemma psi_val : goldenConj = (1 - Real.sqrt 5) / 2 := by
  rw [Real.goldenConj]

/-
ψ = −2α = −2·cos(2π/5).
-/
lemma psi_eq_neg_two_alpha : goldenConj = -(2 * alpha) := by
  rw [psi_val, RGFPentagonGolden.alpha_val]; ring

/-- ψ² = ψ + 1 (taken from Mathlib, recorded here as a reference). -/
lemma psi_sq : goldenConj ^ 2 = goldenConj + 1 := Real.goldenConj_sq

/-
φ + ψ = 1.
-/
lemma golden_add_conj : goldenRatio + goldenConj = 1 := by
  ring

/-
φ · ψ = −1.
-/
lemma golden_mul_conj : goldenRatio * goldenConj = -1 := by
  ring_nf; norm_num;

/-
φ − ψ = √5.
-/
lemma golden_sub_conj : goldenRatio - goldenConj = Real.sqrt 5 := by
  ring

/-
Fibonacci power formula of the golden conjugate: ψ^(n+1) = F(n+1)·ψ + F(n).
-/
lemma conj_pow_succ (n : ℕ) :
    goldenConj ^ (n + 1) = (Nat.fib (n + 1) : ℝ) * goldenConj + (Nat.fib n : ℝ) :=
  -- Unified deduplication: the shared module's `psi` is definitionally equal (defeq) to Mathlib's `goldenConj`,
  -- so we can directly reference `RGF.PentagonComplete.psi_pow_succ`.
  RGF.PentagonComplete.psi_pow_succ n

/-
Lucas identity: φ^(n+1) + ψ^(n+1) = F(n+1) + 2·F(n).
-/
lemma lucas_identity (n : ℕ) :
    goldenRatio ^ (n + 1) + goldenConj ^ (n + 1)
      = (Nat.fib (n + 1) : ℝ) + 2 * (Nat.fib n : ℝ) := by
        convert congr_arg₂ ( · + · ) ( RGFPentagonGolden.golden_pow_succ n ) ( conj_pow_succ n ) using 1 ; ring

/-! ============================================================
    §5: higher-order Fibonacci power towers
    ============================================================ -/

/-
φ⁸ = 21φ + 13 (F(8)=21, F(7)=13).
-/
lemma golden_pow_eight : goldenRatio ^ 8 = 21 * goldenRatio + 13 := by
  grind

/-
φ⁹ = 34φ + 21 (F(9)=34, F(8)=21).
-/
lemma golden_pow_nine : goldenRatio ^ 9 = 34 * goldenRatio + 21 := by
  grind +extAll

/-! ============================================================
    §6: summary theorem
    ============================================================ -/

/-- **Extended summary theorem**: complete closure of the pentagon — golden-ratio algebra (second batch).
    (i) the conjugate quadratic equation 4·cos²(π/5) − 2·cos(π/5) − 1 = 0;
    (ii) the sine Pythagorean-type sum sin²(π/5) + sin²(2π/5) = 5/4;
    (iii) the tangent product tan(π/5)·tan(2π/5) = √5;
    (iv) the golden conjugate satisfies φ + ψ = 1 and φ · ψ = −1;
    (v) the Lucas identity φ^(n+1) + ψ^(n+1) = F(n+1) + 2·F(n). -/
theorem pentagon_golden_ext_complete :
    (4 * (Real.cos (π / 5)) ^ 2 - 2 * (Real.cos (π / 5)) - 1 = 0) ∧
    ((Real.sin (π / 5)) ^ 2 + (Real.sin (2 * π / 5)) ^ 2 = 5 / 4) ∧
    (Real.tan (π / 5) * Real.tan (2 * π / 5) = Real.sqrt 5) ∧
    (goldenRatio + goldenConj = 1 ∧ goldenRatio * goldenConj = -1) ∧
    (∀ n : ℕ, goldenRatio ^ (n + 1) + goldenConj ^ (n + 1)
        = (Nat.fib (n + 1) : ℝ) + 2 * (Nat.fib n : ℝ)) :=
  ⟨cos_pi_div_five_conj_root, sin_sq_sum, tan_mul_tan,
    ⟨golden_add_conj, golden_mul_conj⟩, lucas_identity⟩

end RGFPentagonGoldenExt
