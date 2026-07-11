import RGF.Generative.Bridge.L2L3OpenItemsDerivation
import RGF.Generative.Locking.LockingMembrane
import RGF.Physics.Emergence.LatticeUniquenessGap
import RGF.Generative.Locking.OrthogonalStepRule
import RGF.Generative.Bridge.DualLayer

/-!
# Integrated derivation chain: from the dual-layer generative axioms to `d = 3`

This capstone file *absorbs* the consolidated, self-contained derivation chain that
runs from the lowest-level RGF setting (the dual-layer iteration dynamics) up to the
spatial dimension `d = 3`, honestly annotating the dependency of every step.  Each
layer below is **not re-proved from scratch**: it is assembled from results already
formalised elsewhere in the project, and only the *links* between layers (and the
final master theorem) are new here.

The structure mirrors the ten-layer chain:

* **Layer 0** — generative axioms and the dual-layer iteration `step = modify ∘ generate`,
  with Banach-contraction uniqueness of the fixed point
  (`AbstractDualLayer`, `ContractingDualLayer.fixedPoint_unique`, from `Axioms.DualLayer`).
* **Layer 1 (version D upper bound)** — the depth-2 / second-order generative recurrence
  forces the solution space to be at most two-dimensional, hence at most two independent
  frequencies.  Realised here through the antisymmetric `5×5` characteristic polynomial,
  whose nonzero eigenfrequencies solve a biquadratic and therefore number at most two
  (`L2L3OpenItems.skew5_charpoly_form`, `L2L3OpenItems.pentagon_n2_upper`).
* **Layer 2 (L3, odd dimension)** — the antisymmetric generator in odd dimension has a
  zero eigenvalue (a real chiral axis), forcing oddness
  (`L2L3OpenItems.skew_odd_det_zero`).
* **Layers 3–4 (L2, frequency count `= 2`)** — the genuine dual-layer lower bound
  `n₂ ≥ 2` together with the depth-2 upper bound `n₂ ≤ 2` squeezes `n₂ = 2`.
* **Layer 5 (locking-membrane, `k = 5`)** — combining `L2` (`n₂ = 2`) with `L3`
  (`k` odd) and the dihedral irrep count `n₂(k) = (k−1)/2` forces `k = 5`
  (`odd_n2_eq_two_implies_five`, `locking_membrane_unique_five`).
* **Layers 6–10 (de-modelled lattice, `d = 3`)** — the `D₅` direction count gives
  `forwardCount = 5`, and intersecting it with the intrinsic rotation-vector criterion
  `rotGen d = d` forces `d = 3`, with competing lattices excluded
  (`RGF.LatticeUniquenessGap`).

## Honest boundary

The residual *top-level* assumptions are exactly the ones flagged in the source
derivation, and they appear here as explicit hypotheses, never as axioms:

1. **depth-2 recursion** (Layer 1): the generative law is determined by the previous
   two steps — encoded as the second-order/antisymmetric `5×5` structure.
2. **antisymmetric generator** (Layer 2): the linearised generator is real
   antisymmetric — encoded as the hypothesis `Mᵀ = -M`.
3. **rotation-vector reasonableness** (Layer 9): `rotGen d = d` — kept as an explicit
   intrinsic criterion (`hrot`), not derived from the dynamics.

The master theorem `rgf_dynamics_to_dimension_three` records the whole chain with
these hypotheses made fully explicit.
-/

open RGF.LatticeUniquenessGap
open scoped Matrix

namespace RGF.IntegratedChain

/-! ## Layer 0 — dual-layer dynamics: uniqueness of the stable structure -/

/-- **Layer 0.** Restatement: in a contracting dual-layer system the stable
    structure (fixed point of `step = modify ∘ generate`) is unique. -/
theorem layer0_fixed_point_unique {R E : Type}
    (sys : ContractingDualLayer R E) (r₁ r₂ : R)
    (h₁ : sys.toAbstractDualLayer.FixedPoint r₁)
    (h₂ : sys.toAbstractDualLayer.FixedPoint r₂) : r₁ = r₂ :=
  sys.fixedPoint_unique r₁ r₂ h₁ h₂

/-! ## Layer 1 — depth-2 recursion ⇒ at most two frequencies (version D) -/

/-- **Layer 1 (version D upper bound).**  The antisymmetric `5×5` linearised
    generator has characteristic polynomial of the depth-2 form `X⁵ + a X³ + b X`
    (the even-degree coefficients vanish), so its positive eigenfrequencies solve a
    biquadratic and therefore number at most two. -/
theorem layer1_charpoly_form (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : Mᵀ = -M) :
    ∃ a b : ℝ, M.charpoly = Polynomial.X ^ 5 + Polynomial.C a * Polynomial.X ^ 3
      + Polynomial.C b * Polynomial.X :=
  L2L3OpenItems.skew5_charpoly_form M hM

/-- **Layer 1, clean arithmetic core.**  Any finite set of positive frequencies
    obeying a biquadratic relation `ω⁴ − a ω² + b = 0` has at most two elements. -/
theorem layer1_n2_upper (a b : ℝ) (S : Finset ℝ)
    (hS : ∀ ω ∈ S, 0 < ω ∧ ω ^ 4 - a * ω ^ 2 + b = 0) : S.card ≤ 2 :=
  L2L3OpenItems.pentagon_n2_upper a b S hS

/-! ## Layer 2 — antisymmetric generator ⇒ odd dimension (L3) -/

/-- **Layer 2 (L3).**  An odd-dimensional real antisymmetric generator has a zero
    eigenvalue (`det = 0`), i.e. a stable real chiral axis exists precisely because
    the dimension is odd. -/
theorem layer2_chiral_axis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = -M) (hn : Odd n) : M.det = 0 :=
  L2L3OpenItems.skew_odd_det_zero M hM hn

/-! ## Layers 3–4 — squeezing the frequency count to `n₂ = 2` (L2) -/

/-- **Layers 3–4 (L2).**  The genuine dual-layer lower bound `n₂ ≥ 2` and the
    depth-2 upper bound `n₂ ≤ 2` squeeze the frequency count to exactly two. -/
theorem layer4_frequency_count_two (n₂ : ℕ) (hlow : 2 ≤ n₂) (hup : n₂ ≤ 2) :
    n₂ = 2 := le_antisymm hup hlow

/-! ## Layer 5 — the locking membrane: `k = 5` -/

/-- **Layer 5.**  Combining `L2` (`n₂ = 2`) with `L3` (`k` odd) and the dihedral
    two-dimensional irrep count `n₂(k) = (k−1)/2` forces `k = 5`. -/
theorem layer5_k_eq_five (k : ℕ) (hodd : Odd k) (hn2 : num2DIrreps k = 2) :
    k = 5 :=
  odd_n2_eq_two_implies_five k hodd hn2

/-- **Layer 5, uniqueness.**  `k = 5` is the unique solution of the locking-membrane
    conditions (`n₂ = 2` and odd). -/
theorem layer5_unique : ∃! k : ℕ, LockingMembraneConditions k :=
  locking_membrane_unique_five

/-! ## Layers 6–10 — de-modelled lattice and the rotation-vector criterion: `d = 3` -/

/-- **Layer 8.**  The intrinsic rotation-vector criterion: for any positive
    dimension, `rotGen d = d` iff `d = 3`. -/
theorem layer8_rot_iff (d : ℕ) (hd : 0 < d) : rotGen d = d ↔ d = 3 :=
  rotGen_eq_dim_iff hd

/-- **Layer 7.**  Honest exposure of the gap: the locking count `= 5` alone does
    not fix the dimension (a 2D and a 3D candidate both give 5 forward channels). -/
theorem layer7_gap :
    ∃ L₁ L₂ : LatticeCandidate,
      forwardCount L₁ = 5 ∧ forwardCount L₂ = 5 ∧ L₁.dim ≠ L₂.dim :=
  z5_locking_dimension_degenerate

/-- **Layer 9.**  The double-criterion intersection: for any candidate lattice,
    `forwardCount = 5` together with `rotGen dim = dim` forces `dim = 3`. -/
theorem layer9_dim_three (L : LatticeCandidate) (hdim : 0 < L.dim)
    (hlock : forwardCount L = 5) (hrot : rotGen L.dim = L.dim) : L.dim = 3 :=
  joint_criteria_force_dim_three L hdim hlock hrot

/-- **Layer 10.**  Among the standard competing lattices the simple-cubic lattice is
    the unique one passing both criteria. -/
theorem layer10_unique_cubic :
    ∀ L ∈ candidates,
      (forwardCount L = 5 ∧ rotGen L.dim = L.dim) ↔ L = simpleCubic :=
  cubic_is_unique_among_candidates

/-! ## Layers 9–11 (orthogonal-axis route) — the second, independent path to `d = 3` -/

open RGF.OrthogonalStepRule

/-- **Layer 9 (orthogonal step rule).**  The `d` orthonormal generation axes span
    the whole space, and the signed neighbour directions `{±eᵢ}` number exactly
    `2d` — i.e. the coordination number is `z = 2d`, derived (not assumed). -/
theorem layer9_ortho_axes {d : ℕ} (R : OrthoStepRule d) (hd : 0 < d) :
    Submodule.span ℝ (Set.range R.e) = ⊤ ∧
      (Finset.univ.image (OrthoStepRule.signedAxis R)).card = 2 * d :=
  ⟨OrthoStepRule.axes_span R hd, OrthoStepRule.coordination_eq_two_mul R⟩

/-- **Layer 10 (orthogonal route).**  Under the orthogonal step rule, the locking
    condition `forwardCount = 5` forces `d = 3` with no cubic lattice presupposed;
    the cubic invariant `z = 6` is an output, and the rotation-vector criterion is
    automatically consistent at the locked dimension. -/
theorem layer10_ortho_dim_three {d : ℕ} (R : OrthoStepRule d) (hd : 0 < d)
    (hlock : forwardCount (OrthoStepRule.toCandidate R) = 5) :
    d = 3 ∧ (OrthoStepRule.toCandidate R).coord = 6 ∧
      rotGen (OrthoStepRule.toCandidate R).dim = (OrthoStepRule.toCandidate R).dim :=
  ⟨OrthoStepRule.ortho_locking_forces_three R hd hlock,
   (OrthoStepRule.ortho_locking_forces_cubic R hd hlock).2,
   OrthoStepRule.ortho_locking_rot_consistent R hd hlock⟩

/-- **Layer 11 (orthogonal route).**  The triangular lattice is excluded: it cannot
    arise from any orthogonal step rule (its coordination `6 ≠ 2·2`). -/
theorem layer11_triangular_excluded :
    ¬ ∃ R : OrthoStepRule triangular.dim, OrthoStepRule.toCandidate R = triangular :=
  triangular_not_orthogonal

/-- **Master theorem (orthogonal route).**  From the dynamical inputs (`L3` odd
    mode order, the dual-layer frequency lower/upper bounds), the symmetry
    → direction bridge `forwardCount = k`, and the orthogonal step rule, the chain
    concludes `k = 5`, `forwardCount = 5`, and the spatial dimension `d = 3` — with
    the cubic lattice obtained as a conclusion rather than an assumption. -/
theorem rgf_dynamics_to_dimension_three_via_ortho
    (k : ℕ) (n₂ : ℕ)
    (hodd : Odd k) (hn2def : n₂ = num2DIrreps k)
    (hlow : 2 ≤ n₂) (hup : n₂ ≤ 2)
    {d : ℕ} (R : OrthoStepRule d) (hd : 0 < d)
    (hbridge : forwardCount (OrthoStepRule.toCandidate R) = k) :
    k = 5 ∧ forwardCount (OrthoStepRule.toCandidate R) = 5 ∧ d = 3 := by
  have hn2 : n₂ = 2 := layer4_frequency_count_two n₂ hlow hup
  have hk5 : k = 5 := layer5_k_eq_five k hodd (by rw [← hn2def, hn2])
  have hlock : forwardCount (OrthoStepRule.toCandidate R) = 5 := by rw [hbridge, hk5]
  exact ⟨hk5, hlock, OrthoStepRule.ortho_locking_forces_three R hd hlock⟩

/-! ## Master theorem: the full chain, with honest hypotheses -/

/-- **Master theorem — the integrated derivation chain.**

From the dynamical inputs
* `hodd`  : `L3` — the antisymmetric generator forces an odd mode order `k`,
* `hlow`  : the genuine dual-layer lower bound on the frequency count `n₂ ≥ 2`,
* `hup`   : the depth-2 / version-D upper bound on the frequency count `n₂ ≤ 2`,

together with the geometric inputs
* `hbridge` : the `Dₖ` symmetry produces exactly `k` admissible forward directions
              (`forwardCount L = k`),
* `hrot`    : the intrinsic rotation-vector criterion `rotGen (dim) = dim`,

the chain concludes that the mode order is `k = 5`, the resulting direction count is
`5`, and the spatial dimension is `d = 3`.

Every residual assumption (depth-2 recursion via `hup`, antisymmetric generator via
`hodd`, rotation-vector reasonableness via `hrot`, and the symmetry→direction bridge
via `hbridge`) is an explicit hypothesis, in keeping with the honest-boundary
discipline of the derivation. -/
theorem rgf_dynamics_to_dimension_three
    (k : ℕ) (n₂ : ℕ)
    (hodd : Odd k) (hn2def : n₂ = num2DIrreps k)
    (hlow : 2 ≤ n₂) (hup : n₂ ≤ 2)
    (L : LatticeCandidate) (hdim : 0 < L.dim)
    (hbridge : forwardCount L = k) (hrot : rotGen L.dim = L.dim) :
    k = 5 ∧ forwardCount L = 5 ∧ L.dim = 3 := by
  have hn2 : n₂ = 2 := layer4_frequency_count_two n₂ hlow hup
  have hk5 : k = 5 := layer5_k_eq_five k hodd (by rw [← hn2def, hn2])
  have hlock : forwardCount L = 5 := by rw [hbridge, hk5]
  exact ⟨hk5, hlock, layer9_dim_three L hdim hlock hrot⟩

end RGF.IntegratedChain
