/-
  Modern/RealInstances.lean

  **The analytic instance stack for the RGF reals.**

  The foundations establish an *ordered ring isomorphism* `RGFReal' ≃+*o ℝ`
  (`RGFReal'.orderedRingEquivReal`), built from the bijective, order-preserving
  ring map `RGFReal'.toReal`.  By itself that already shows `RGFReal'` *is* the
  real field; but to actually *use* the modern-mathematics machinery of Mathlib
  on `RGFReal'` we must register the corresponding type-class instances.

  This file does exactly that, equipping `RGFReal'` with:

  * `LinearOrder` (refining the native `≤`),
  * `IsStrictOrderedRing` (so `RGFReal'` is an ordered field),
  * `Archimedean`,
  * `NormedField` (hence `MetricSpace`, `UniformSpace`, `TopologicalSpace`,
    `NormedAddCommGroup`, ...),
  * `CompleteSpace` (the RGF reals are Cauchy-complete as a metric space),
  * `NontriviallyNormedField`.

  Every instance is *transported* through `toReal`, which is a bijective
  ring/order isomorphism onto `ℝ`.  Once these are in place, the entire analytic
  edifice of Mathlib — measure theory, integration, functional analysis,
  differential geometry, ... — becomes directly available over `RGFReal'`, as
  demonstrated in the sibling `Modern/*` files.
-/
import Mathlib
import RGF.Math.Real.RGFNativeField
import RGF.Math.Real.RGFOrderReal

namespace RGF
namespace RGFReal'

open scoped Classical

/-! ## Linear order -/

theorem le_refl' (a : RGFReal') : a ≤ a := toReal_le_iff.mp le_rfl

theorem le_trans' {a b c : RGFReal'} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  toReal_le_iff.mp (le_trans (toReal_le_iff.mpr hab) (toReal_le_iff.mpr hbc))

theorem le_antisymm' {a b : RGFReal'} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  toReal_injective (le_antisymm (toReal_le_iff.mpr hab) (toReal_le_iff.mpr hba))

theorem le_total' (a b : RGFReal') : a ≤ b ∨ b ≤ a :=
  (le_total (toReal a) (toReal b)).imp toReal_le_iff.mp toReal_le_iff.mp

/-- The RGF reals form a linear order, refining the native `≤`.  The order is the
    native pointwise order `leRel`, shown to be linear by transport through the
    order-preserving bijection `toReal`. -/
noncomputable instance instLinearOrder : LinearOrder RGFReal' where
  le := (· ≤ ·)
  le_refl := le_refl'
  le_trans := fun _ _ _ => le_trans'
  le_antisymm := fun _ _ => le_antisymm'
  le_total := le_total'
  toDecidableLE := Classical.decRel _

/-
`toReal` reflects and preserves the strict order.
-/
theorem toReal_lt_iff {a b : RGFReal'} : toReal a < toReal b ↔ a < b := by
  simp +decide only [lt_iff_le_not_ge, ← toReal_le_iff]

/-! ## Ordered ring structure -/

/-- The RGF reals form a strict ordered ring (hence, with the field structure
    from `Foundations.RGFNativeField`, an ordered field). -/
instance instIsStrictOrderedRing : IsStrictOrderedRing RGFReal' :=
  Function.Injective.isStrictOrderedRing toReal toReal_zero toReal_one toReal_add toReal_mul
    (fun {_ _} => toReal_le_iff) (fun {_ _} => toReal_lt_iff)

/-
The RGF reals are Archimedean.
-/
instance instArchimedean : Archimedean RGFReal' := by
  constructor;
  intro x y hy;
  -- By the Archimedean property of the real numbers, there exists a natural number $n$ such that $toReal x < n * toReal y$.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, toReal x < n * toReal y := by
    exact exists_nat_gt ( x.toReal / y.toReal ) |> fun ⟨ n, hn ⟩ => ⟨ n, by rwa [ div_lt_iff₀ ( show 0 < y.toReal from by simpa [ toReal_zero ] using toReal_lt_iff.mpr hy ) ] at hn ⟩;
  contrapose! hn;
  convert toReal_le_iff.mpr ( le_of_lt ( hn n ) ) |> le_trans _ using 1;
  induction n <;> simp_all +decide [ add_mul, nsmul_eq_mul ];
  · convert toReal_zero.ge;
  · rw [ RGFReal'.toReal_add ];
    linarith

/-! ## Normed field structure -/

/-- The RGF reals as a normed field: the norm is transported from `ℝ` through the
    ring isomorphism `ringEquivReal`, i.e. `‖a‖ = |toReal a|`. -/
noncomputable instance instNormedField : NormedField RGFReal' :=
  NormedField.induced RGFReal' ℝ (ringEquivReal : RGFReal' →+* ℝ) ringEquivReal.injective

/-- The transported norm is the real norm of `toReal`. -/
theorem norm_toReal_eq (a : RGFReal') : ‖a‖ = ‖toReal a‖ := rfl

/-- The transported norm is `|toReal ·|`. -/
@[simp] theorem norm_eq (a : RGFReal') : ‖a‖ = |toReal a| := Real.norm_eq_abs _

/-
`toReal` is an isometry from the RGF reals to `ℝ`.
-/
theorem isometry_toReal : Isometry (toReal) := by
  refine' Isometry.of_dist_eq fun x y => _;
  convert rfl

/-
The RGF reals are Cauchy-complete as a metric space: every Cauchy sequence
    converges.  This is the precise topological statement of completeness,
    transported along the surjective isometry `toReal`.
-/
instance instCompleteSpace : CompleteSpace RGFReal' := by
  convert ( isometry_toReal.isUniformInducing.completeSpace_congr toReal_surjective ).mpr inferInstance

/-
The RGF reals form a nontrivially normed field (there is an element of norm
    greater than one), so all of Mathlib's normed-field analysis applies.
-/
noncomputable instance instNontriviallyNormedField : NontriviallyNormedField RGFReal' where
  non_trivial := by
    use 2; norm_num;
    erw [ show ( 2 : RGFReal' ) = ( 1 + 1 ) by rfl, toReal_add ] ; norm_num [ toReal_one ]

/-! ## The packaged isometric order isomorphism with `ℝ` -/

/-- `toReal`, packaged as an isometry equivalence `RGFReal' ≃ᵢ ℝ`: the RGF reals
    are isometric, order-isomorphic and ring-isomorphic to the standard reals. -/
noncomputable def isometryEquivReal : RGFReal' ≃ᵢ ℝ where
  toEquiv := equivReal
  isometry_toFun := isometry_toReal

@[simp] theorem isometryEquivReal_apply (a : RGFReal') : isometryEquivReal a = toReal a := rfl

end RGFReal'
end RGF