/-
  Modern/AnalyticNumberTheory.lean

  **Analytic number theory over the RGF reals.**

  With the ordered-field, normed and completeness instances from
  `Modern.RealInstances`, infinite series and their convergence make sense over
  the RGF reals.  We transport two landmark analytic-number-theory results so
  that they are stated and proved *for series valued in the RGF reals*:

  * the **harmonic series diverges** over `RGFReal'`;
  * **Euler's theorem**: the sum of the reciprocals of the primes diverges over
    `RGFReal'` (it is not summable).

  This addresses the criticism that analytic number theory was untouched, and
  illustrates infinite-series analysis valued in the self-built reals.
-/
import Mathlib
import RGF.Math.Real.RealInstances

namespace RGF
namespace RGFReal'

open Filter Finset
open scoped Topology

/-! ## `toReal` as a continuous additive/ring homomorphism -/

/-
`toReal` sends RGF natural-number literals to real natural-number literals.
-/
theorem toReal_natCast (n : ℕ) : toReal (n : RGFReal') = (n : ℝ) := by
  induction n <;> simp_all +decide [ Nat.cast_succ ];
  · convert RGFReal'.toReal_zero;
  · rw [ RGFReal'.toReal_add, RGFReal'.toReal_one ] ; aesop

/-
`toReal` of an RGF harmonic partial sum is the real harmonic partial sum.
-/
theorem toReal_harmonic_sum (n : ℕ) :
    toReal (∑ k ∈ Finset.range n, (1 / (k + 1) : RGFReal'))
      = ∑ k ∈ Finset.range n, (1 / (k + 1) : ℝ) := by
  -- Apply the lemma toReal_natCast to each term in the sum.
  have h_term : ∀ k : ℕ, toReal (1 / (k + 1 : RGFReal')) = 1 / (k + 1 : ℝ) := by
    grind +suggestions;
  induction' n with n ih;
  · convert RGFReal'.toReal_zero;
  · rw [ Finset.sum_range_succ, RGFReal'.toReal_add, ih, h_term ];
    rw [ Finset.sum_range_succ ]

/-
A sequence of RGF reals tends to `+∞` iff its image under `toReal` does
    (transport along the order isomorphism with `ℝ`).
-/
theorem tendsto_atTop_toReal {f : ℕ → RGFReal'} :
    Tendsto (fun n => toReal (f n)) atTop atTop ↔ Tendsto f atTop atTop := by
  -- Apply the monotone convergence theorem to conclude the proof.
  have h_monotone_convergence : ∀ {f : ℕ → RGFReal'}, Tendsto (fun n => (f n).toReal) atTop atTop ↔ Tendsto f atTop atTop := by
    intro f;
    convert ( RGF.RGFReal'.orderedRingEquivReal.toOrderIso.tendsto_atTop_iff ) using 1;
  exact h_monotone_convergence

/-! ## The harmonic series diverges over the RGF reals -/

/-- **The harmonic series diverges over the RGF reals.** The partial sums
    `∑_{k<n} 1/(k+1)` tend to `+∞` in `RGFReal'`. -/
theorem rgf_harmonic_diverges :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (1 / (k + 1) : RGFReal')) atTop atTop := by
  rw [← tendsto_atTop_toReal]
  have h : (fun n => toReal (∑ k ∈ Finset.range n, (1 / (k + 1) : RGFReal')))
      = fun n => ∑ k ∈ Finset.range n, (1 / (k + 1) : ℝ) := funext toReal_harmonic_sum
  rw [h]
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

/-! ## Euler's theorem on prime reciprocals over the RGF reals -/

/-
**Euler's theorem, over the RGF reals.** The sum of the reciprocals of the
    primes is not summable in `RGFReal'`.
-/
theorem rgf_not_summable_one_div_primes :
    ¬ Summable (fun p : Nat.Primes => (1 / (p : RGFReal'))) := by
  convert Nat.Primes.not_summable_one_div using 1;
  constructor <;> rintro ⟨ a, ha ⟩;
  · convert ha.summable.map ( ringEquivReal.toAddMonoidHom ) isometry_toReal.continuous using 1;
    ext; simp +decide;
  · contrapose! ha;
    intro H;
    convert ha <| .of_norm ?_;
    convert H.summable.norm using 1;
    norm_num [ Norm.norm ]

end RGFReal'
end RGF