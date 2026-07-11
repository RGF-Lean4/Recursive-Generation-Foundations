/-
  Spectral-gap recursive dynamics (G2/G3)

  The lattice repulsion side of the RGF dynamics: a linear affine recursion operator
  `recOp A b : x ↦ A x + b` whose linear part has a spectral gap (`‖A‖ < 1`) is a Banach
  contraction (G2), hence has a unique fixed point to which every orbit converges
  exponentially fast at geometric rate `‖A‖` (G3).

  This generalises the rule-layer Banach contraction of `BanachContraction.lean` to an
  arbitrary complete normed space and a continuous-linear affine map.
-/

import Mathlib

open Filter Topology
open scoped NNReal

namespace RGF.Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Linear affine recursion operator `x ↦ A x + b`. -/
def recOp (A : E →L[ℝ] E) (b : E) : E → E := fun x => A x + b

/-- Spectral gap: the operator norm is strictly less than 1 (guaranteeing that the
    recursion operator is a Banach contraction). -/
def SpectralGap (A : E →L[ℝ] E) : Prop := ‖A‖ < 1

omit [CompleteSpace E] in
/-- Spectral gap ⇒ the recursion operator is a Banach contraction (G2: repulsion /
    contraction dynamics). -/
theorem spectralGap_imp_contracting (A : E →L[ℝ] E) (b : E) (hGap : SpectralGap A) :
    ContractingWith ‖A‖₊ (recOp A b) := by
  refine' ⟨ by rw [ ← NNReal.coe_lt_one ] ; exact hGap, _ ⟩;
  unfold recOp;
  rw [ lipschitzWith_iff_norm_sub_le ];
  simpa [ add_sub_add_right_eq_sub ] using fun x y => A.le_opNorm ( x - y )

/-- Spectral gap ⇒ unique fixed point and exponential recovery (G3: exponential
    convergence with geometric rate). -/
theorem spectralGap_imp_exponential_recovery (A : E →L[ℝ] E) (b : E) (hGap : SpectralGap A) :
    ∃ x₀, Function.IsFixedPt (recOp A b) x₀ ∧
      ∀ x, Tendsto (fun n => (recOp A b)^[n] x) atTop (𝓝 x₀) ∧
        ∀ n, ‖(recOp A b)^[n] x - x₀‖ ≤ ‖A‖ ^ n * ‖x - x₀‖ := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Function.IsFixedPt (recOp A b) x₀ := by
    have := spectralGap_imp_contracting A b hGap;
    exact ⟨ this.fixedPoint _, this.fixedPoint_isFixedPt ⟩;
  refine' ⟨ x₀, hx₀, fun x => ⟨ _, _ ⟩ ⟩;
  · have := spectralGap_imp_contracting A b hGap;
    convert this.tendsto_iterate_fixedPoint _;
    exact this.fixedPoint_unique hx₀;
  · intro n;
    induction' n with n ih generalizing x <;> simp_all +decide [ Function.iterate_succ_apply', pow_succ', mul_assoc ];
    -- By definition of $recOp$, we have $recOp A b y - x₀ = A (y - x₀)$.
    have h_recOp_sub : ∀ y : E, recOp A b y - x₀ = A (y - x₀) := by
      simp_all +decide [ recOp, Function.IsFixedPt ];
      grind +extAll;
    simpa only [ h_recOp_sub, norm_smul, mul_assoc ] using mul_le_mul_of_nonneg_left ( ih x ) ( norm_nonneg A ) |> le_trans ( ContinuousLinearMap.le_opNorm _ _ )

end RGF.Dynamics
