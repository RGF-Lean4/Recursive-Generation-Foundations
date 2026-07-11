/-
  Modern/FunctionalAnalysis.lean

  **Functional analysis over the RGF reals.**

  Using the normed-field and completeness instances from `Modern.RealInstances`,
  we exhibit genuine functional analysis carried out *with the RGF reals as the
  scalar field*:

  * `RGFReal'` is itself a complete normed field (a one-dimensional Banach
    space over itself);
  * the sequence space `ℓ²(RGFReal')` is an **infinite-dimensional Banach space**
    over `RGFReal'` (complete normed `RGFReal'`-vector space), directly
    addressing the criticism that no infinite-dimensional functional spaces were
    constructed;
  * the **Banach fixed-point theorem** holds over `RGFReal'`: every contraction
    of the (nonempty, complete) metric space `RGFReal'` has a unique fixed point.
-/
import Mathlib
import RGF.Math.Real.RealInstances

namespace RGF
namespace RGFReal'

open scoped ENNReal

/-! ## The RGF reals are a complete normed field -/

/-- `RGFReal'` is a complete normed field: a Banach algebra over itself. -/
noncomputable example : CompleteSpace RGFReal' := inferInstance
noncomputable example : NormedField RGFReal' := inferInstance

/-! ## An infinite-dimensional Banach space over the RGF reals

`ℓ²(RGFReal')`, the space of square-summable sequences of RGF reals, is the
canonical infinite-dimensional Banach space over the RGF reals. -/

/-- The RGF `ℓ²` space: square-summable sequences of RGF reals. -/
abbrev RGFlp2 : Type := lp (fun _ : ℕ => RGFReal') 2

/-- `ℓ²(RGFReal')` is a normed `RGFReal'`-vector space. -/
noncomputable example : NormedSpace RGFReal' RGFlp2 := inferInstance

/-- `ℓ²(RGFReal')` is **complete**, i.e. a Banach space over the RGF reals. -/
theorem rgf_lp2_complete : CompleteSpace RGFlp2 := inferInstance

/-
`ℓ²(RGFReal')` is **infinite-dimensional** over the RGF reals: the standard
    unit vectors `eₙ = δₙ` form an infinite linearly independent family.
-/
theorem rgf_lp2_infinite_dim :
    ∃ v : ℕ → RGFlp2, LinearIndependent RGFReal' v := by
  refine' ⟨ _, linearIndependent_iff'.mpr _ ⟩;
  exact fun n => lp.single 2 n 1;
  intro s g hg i hi; replace hg := congr_arg ( fun f => f i ) hg; simp_all +decide [ lp.single_apply ] ;
  rw [ Finset.sum_eq_single i ] at hg <;> aesop

/-
Hence `ℓ²(RGFReal')` is not finite-dimensional over the RGF reals.
-/
theorem rgf_lp2_not_finiteDimensional :
    ¬ FiniteDimensional RGFReal' RGFlp2 := by
  intro h;
  obtain ⟨ v, hv ⟩ := rgf_lp2_infinite_dim;
  have := hv.finite;
  exact this.false

/-! ## The Banach fixed-point theorem over the RGF reals -/

/-
**Banach fixed-point theorem, over the RGF reals.** Any contraction of the
    complete metric space `RGFReal'` has a unique fixed point.
-/
theorem rgf_banach_fixedPoint {K : NNReal} {f : RGFReal' → RGFReal'}
    (hf : ContractingWith K f) : ∃! x : RGFReal', f x = x := by
  apply_rules [ existsUnique_of_exists_of_unique ];
  · convert hf.exists_fixedPoint;
    constructor;
    · intro h x hx;
      convert hf.exists_fixedPoint x hx using 1;
    · intro h;
      exact Exists.elim ( h 0 ( by simp +decide [ edist_dist ] ) ) fun x hx => ⟨ x, hx.1 ⟩;
  · intro y₁ y₂ hy₁ hy₂;
    have := hf.dist_le_mul y₁ y₂;
    contrapose! this;
    simpa [ hy₁, hy₂, this ] using hf.1

end RGFReal'
end RGF