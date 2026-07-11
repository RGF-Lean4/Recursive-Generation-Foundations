/-
  Foundations/RGFRealExamples.lean

  Generative demonstration: concrete real numbers produced as RGF reals.

  We show that the RGF reals are not merely "something isomorphic to ℝ": every
  real number is *generated* by an explicit rational approximation process.  The
  uniform generating process used here is the decimal expansion
  `decSeq r n = ⌊r · 10ⁿ⌋ / 10ⁿ`, an explicit sequence of rationals whose `n`-th
  term is within `10⁻ⁿ` of `r`.  Feeding this rational Cauchy sequence through the
  RGF Cauchy-sequence quotient produces an RGF real whose canonical image is `r`.

  As concrete instances we generate `√2`, `π` and `e`, prove that they map under
  `toReal` to the standard `Real.sqrt 2`, `Real.pi` and `Real.exp 1`, and that the
  generated `√2` squares to `2` inside `RGFReal'`.
-/
import Mathlib
import RGF.Math.Real.RGFOrderReal

namespace RGF

open RGFNat RGFInt

namespace RGFReal'

/-! ## A general constructor from standard `ℚ`-Cauchy sequences -/

/-- Generate an RGF real from a standard `ℚ`-Cauchy sequence by re-indexing it
    over `RGFNat` and taking the equivalence class. -/
noncomputable def ofRatCauSeq (f : CauSeq ℚ abs) : RGFReal' :=
  Quotient.mk _ ⟨fun m => RGFRat.ofRat (f m.toNat), isRGFCauchy_ofRat_comp f⟩

/-
The generated RGF real has the expected standard real as its canonical image.
-/
theorem toReal_ofRatCauSeq (f : CauSeq ℚ abs) : toReal (ofRatCauSeq f) = Real.mk f := by
  convert congrArg Real.mk ( CauSeq.ext _ ) using 1;
  simp +decide [ cauSeqOf_apply, RGFRat.toRat_ofRat, RGFNat.toNat_ofNat ]

/-! ## The uniform decimal-expansion generating process -/

/-- The decimal-expansion approximation `⌊r · 10ⁿ⌋ / 10ⁿ ∈ ℚ`. -/
noncomputable def decSeq (r : ℝ) (n : ℕ) : ℚ := (⌊r * (10 : ℝ) ^ n⌋ : ℚ) / (10 : ℚ) ^ n

/-
The `n`-th decimal approximation is within `10⁻ⁿ` of `r`.
-/
theorem decSeq_dist (r : ℝ) (n : ℕ) : |(decSeq r n : ℝ) - r| ≤ 1 / 10 ^ n := by
  unfold decSeq; norm_num;
  rw [ abs_le ] ; constructor <;> nlinarith [ Int.floor_le ( r * 10 ^ n ), Int.lt_floor_add_one ( r * 10 ^ n ), show ( 0 : ℝ ) < 10 ^ n by positivity, div_mul_cancel₀ ( ⌊r * 10 ^ n⌋ : ℝ ) ( by positivity : ( 10 : ℝ ) ^ n ≠ 0 ), inv_mul_cancel₀ ( by positivity : ( 10 : ℝ ) ^ n ≠ 0 ) ]

theorem isCauSeq_decSeq (r : ℝ) : IsCauSeq abs (decSeq r) := by
  intro ε hε
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (2 : ℝ) / ε < 10 ^ i := by
    exact pow_unbounded_of_one_lt _ <| by norm_num;
  refine' ⟨ i, fun j hj => _ ⟩;
  -- By the triangle inequality and `decSeq_dist`, we have:
  have h_triangle : |(decSeq r j : ℝ) - (decSeq r i : ℝ)| ≤ 1 / 10 ^ j + 1 / 10 ^ i := by
    have h_triangle : |(decSeq r j : ℝ) - r| ≤ 1 / 10 ^ j ∧ |(decSeq r i : ℝ) - r| ≤ 1 / 10 ^ i := by
      exact ⟨ by simpa using decSeq_dist r j, by simpa using decSeq_dist r i ⟩;
    exact abs_sub_le_iff.mpr ⟨ by linarith [ abs_le.mp h_triangle.1, abs_le.mp h_triangle.2 ], by linarith [ abs_le.mp h_triangle.1, abs_le.mp h_triangle.2 ] ⟩;
  -- Since $j \geq i$, we have $1 / 10^j \leq 1 / 10^i$.
  have h_le : 1 / (10 : ℝ) ^ j ≤ 1 / (10 : ℝ) ^ i := by
    gcongr ; norm_num;
  rw [ div_lt_iff₀ ( by positivity ) ] at hi;
  exact_mod_cast ( by nlinarith [ show ( 10 : ℝ ) ^ i > 0 by positivity, show ( 10 : ℝ ) ^ j > 0 by positivity, one_div_mul_cancel ( show ( 10 : ℝ ) ^ i ≠ 0 by positivity ), one_div_mul_cancel ( show ( 10 : ℝ ) ^ j ≠ 0 by positivity ) ] : ( |decSeq r j - decSeq r i| : ℝ ) < ε )

/-- The decimal expansion of `r`, packaged as a `ℚ`-Cauchy sequence. -/
noncomputable def decCauSeq (r : ℝ) : CauSeq ℚ abs := ⟨decSeq r, isCauSeq_decSeq r⟩

theorem mk_decCauSeq (r : ℝ) : Real.mk (decCauSeq r) = r := by
  refine' le_antisymm ( le_of_forall_pos_le_add fun ε hε => _ ) ( le_of_forall_pos_le_add fun ε hε => _ );
  · have := Real.mk_near_of_forall_near ( show ∃ i, ∀ j ≥ i, |(decCauSeq r).1 j - r| ≤ ε from ?_ );
    · linarith [ abs_le.mp this ];
    · -- Choose $i$ such that $1/10^i \leq \epsilon$.
      obtain ⟨i, hi⟩ : ∃ i : ℕ, 1 / 10 ^ i ≤ ε := by
        simpa using exists_pow_lt_of_lt_one hε ( by norm_num : ( 1 : ℝ ) / 10 < 1 ) |> fun ⟨ i, hi ⟩ => ⟨ i, by simpa using hi.le ⟩;
      use i;
      exact fun j hj => le_trans ( decSeq_dist r j ) ( by exact le_trans ( by gcongr ; norm_num ) hi );
  · -- By definition of `Real.mk`, we know that for any `ε > 0`, there exists an `i` such that for all `j ≥ i`, `|(decCauSeq r) j - r| ≤ ε`.
    have h_mk : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(decCauSeq r) j - r| ≤ ε := by
      intro ε hε
      obtain ⟨i, hi⟩ : ∃ i : ℕ, ∀ j ≥ i, |(decSeq r j : ℝ) - r| ≤ ε := by
        exact ⟨ ⌈ε⁻¹⌉₊, fun j hj => le_trans ( decSeq_dist r j ) ( by simpa using inv_le_of_inv_le₀ hε <| le_trans ( Nat.le_ceil _ ) <| mod_cast hj.trans <| le_of_lt <| Nat.recOn j ( by norm_num ) fun n ihn => by norm_num [ pow_succ' ] at * ; linarith ) ⟩;
      exact ⟨ i, fun j hj => hi j hj ⟩;
    obtain ⟨ i, hi ⟩ := h_mk ε hε;
    have := @Real.mk_near_of_forall_near ( decCauSeq r ) r ε ?_;
    · linarith [ abs_le.mp this ];
    · use i

/-! ## The generative embedding `ℝ → RGFReal'` -/

/-- Generate the RGF real corresponding to `r` from its decimal expansion. -/
noncomputable def ofReal (r : ℝ) : RGFReal' := ofRatCauSeq (decCauSeq r)

@[simp] theorem toReal_ofReal (r : ℝ) : toReal (ofReal r) = r := by
  rw [ofReal, toReal_ofRatCauSeq, mk_decCauSeq]

/-! ## Concrete generated numbers

  The original demonstration generated `√2`, `π` and `e` through `ofReal`, i.e. by
  reading off the decimal expansion of the *already given* standard real.  This
  imports the value from the outside instead of generating it from within the RGF
  framework, a small blemish in "generative purity".  The fully internal
  constructions — Newton iteration for `√2`, the factorial series for `e`, and the
  Leibniz series for `π`, none of which mention the target real in their
  definitions — now live in `Foundations/RGFGenerativeConstants.lean`, where
  `rgfSqrt2`, `rgfPi`, `rgfE`, `toReal_rgfSqrt2`, `toReal_rgfPi`, `toReal_rgfE`
  and `rgfSqrt2_sq` are re-established.  The old `ofReal`-based definitions are
  retained here only as comments for historical reference. -/

-- /-- `√2` generated as an RGF real. -/
-- noncomputable def rgfSqrt2 : RGFReal' := ofReal (Real.sqrt 2)
--
-- /-- `π` generated as an RGF real. -/
-- noncomputable def rgfPi : RGFReal' := ofReal Real.pi
--
-- /-- `e` generated as an RGF real. -/
-- noncomputable def rgfE : RGFReal' := ofReal (Real.exp 1)
--
-- @[simp] theorem toReal_rgfSqrt2 : toReal rgfSqrt2 = Real.sqrt 2 := toReal_ofReal _
-- @[simp] theorem toReal_rgfPi : toReal rgfPi = Real.pi := toReal_ofReal _
-- @[simp] theorem toReal_rgfE : toReal rgfE = Real.exp 1 := toReal_ofReal _
--
-- /-- The generated `√2` squares to `2` inside `RGFReal'`. -/
-- theorem rgfSqrt2_sq : rgfSqrt2 * rgfSqrt2 = (1 + 1 : RGFReal') := by
--   apply toReal_injective
--   rw [toReal_mul, toReal_add, toReal_one, toReal_rgfSqrt2]
--   rw [Real.mul_self_sqrt (by norm_num)]
--   norm_num

end RGFReal'
end RGF