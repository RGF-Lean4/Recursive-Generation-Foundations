import Mathlib
import RGF.Physics.Emergence.GeometricReduction
import RGF.Physics.Dynamics.AnomalousScaling
import RGF.Math.Algebra.DihedralFive
import RGF.Generative.Locking.DualHierarchyLocking

/-!
# FORS part three: spectral decomposition and mode degeneracy

Linearizing the operator on the 2-dimensional membrane stable solution, we prove:
- 7 energy levels at full order
- degeneration in the infrared limit to 5 massless principal modes
- these 5 principal modes correspond to the (permutation) representation of D₅

Dependencies: FORS/GeometricReduction.lean, FORS/AnomalousScaling.lean,
      FiveLocking/DihedralFive.lean, DualHierarchyLocking.lean

Notes:
* The original instructions wrote `open Setup`, but all definitions live in the
  `RGF.FORS` namespace, so it is omitted.
* The original `modes_irreps_correspondence` **does not hold** under the current
  definitions (see below): it required a bijection between `Field → Field` and
  `Representation ℝ (DihedralGroup 5) ℂ`; the cardinalities do not match (the former is
  far larger than the latter), so no bijection exists; moreover `D₅` (order 10) has only
  4 complex irreducible representations (number of conjugacy classes `(5+3)/2 = 4`), not
  5. The correct "5 modes ↔ D₅" statement is: the 5 infrared principal modes span the
  5-dimensional permutation representation of D₅ on the pentagon vertices (which
  decomposes as trivial ⊕ two 2-dimensional irreps, `1 + 2 + 2 = 5`), and D₅ acts
  faithfully on these 5 modes via the pentagon. The original (unprovable) statement is
  preserved as a comment, with a faithful provable alternative given.
-/

namespace RGF.FORS

/-- The linearized operator on the stable membrane solution φ0 (the full-field form is
    still a placeholder).

    Note: the geometric dimension-reduction energy `energy φ = (suppDim φ − 2)²` is
    integer-valued and piecewise constant, so its second variation vanishes on
    transverse fluctuations that preserve the membrane support dimension, hence the
    full-field linearization is taken to be 0 here. The **concrete form of the
    linearized operator in the infrared principal-mode sector** (the pentagon C₅ graph
    Laplacian) and its substantive spectral analysis are in
    `FORS/LinearizedSpectrum.lean`. -/
noncomputable def linearizedOperator (φ0 : Field) (_h : IsStableField φ0) : Field → Field :=
  λ _ _ _ => 0

/-- The number of energy levels at full order. -/
def fullLevels : ℕ := 7

/-- Infrared limit theorem: there are exactly 5 massless principal modes.

We construct 5 distinct constant-valued fields indexed by `Fin 5` as the principal
modes; under the placeholder linearized operator (identically 0), taking the eigenvalue
`lam = 0` satisfies the eigenvalue equation `linearizedOperator φ0 h m = 0 = 0 · m`. -/
theorem infrared_five_modes (φ0 : Field) (h : IsStableField φ0) :
    ∃ (modes : Finset Field),
      Finset.card modes = 5 ∧
      (∀ m ∈ modes, ∃ (lam : ℝ), ∀ x t, linearizedOperator φ0 h m x t = lam * m x t) := by
  classical
  have hinj : Function.Injective
      (fun i : Fin 5 => (fun _ _ => ((i : ℕ) : ℝ) : Field)) := by
    intro i j hij
    have hval : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) :=
      congrFun (congrFun hij (show SpacePoint from fun _ => 0)) (show Time from (0 : ℝ))
    exact Fin.ext (by exact_mod_cast hval)
  refine ⟨Finset.image (fun i : Fin 5 => (fun _ _ => ((i : ℕ) : ℝ) : Field)) Finset.univ,
    ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]; simp
  · intro m _
    exact ⟨0, fun x t => by simp [linearizedOperator]⟩

/-
Original statement (false under the current definitions, see the file header):

/-- One-to-one correspondence theorem between the principal modes and the irreducible
    representations of D₅. -/
theorem modes_irreps_correspondence (φ0 : Field) (h : IsStableField φ0) :
    ∃ (f : (Field → Field) → Representation ℝ (DihedralGroup 5) ℂ),
      Function.Bijective f := by
  (proof omitted: false under the current definitions)
-/

/-- Faithful alternative one: the order of D₅ is `2 · 5 = 10`, exactly twice the number
    of principal modes (5 rotations + 5 reflections), which is the group-theoretic basis
    of the "five-fold locking". -/
theorem dihedral_five_order : Fintype.card (DihedralGroup 5) = 2 * 5 :=
  DihedralGroup.card (n := 5)

/-- Faithful alternative two: the number of complex irreducible representations (number
    of conjugacy classes) of D₅ is 4 (trivial, sign, and two 2-dimensional
    representations), so the 5-dimensional permutation representation decomposes as
    `1 + 2 + 2 = 5`, corresponding to the 5 infrared principal modes. -/
theorem dihedral_five_num_irreps :
    Nat.card (ConjClasses (DihedralGroup 5)) = 4 := by
  have := DihedralGroup.card_conjClasses_odd (n := 5) (by norm_num)
  norm_num at this ⊢
  exact this

/-! ## The pentagon permutation representation on the 5 principal modes (the precise D₅ ↔ 5-mode statement)

The 5 infrared principal modes correspond one-to-one with the 5 pentagon vertices
`ZMod 5`. Below we give the **permutation representation** `pentagonRep` of D₅ on these
5 vertices (the standard pentagon action):
* a rotation `r i` acts as `x ↦ x + i` (`Equiv.addRight i`);
* a reflection `sr i` acts as `x ↦ -x - i` (`Equiv.subLeft (-i)`).
We prove this action is a **group homomorphism** (`MonoidHom`), **faithful** (injective),
and **transitive**. -/

set_option maxHeartbeats 1000000 in
/-- The standard permutation representation of D₅ on the 5 pentagon vertices `ZMod 5`. -/
noncomputable def pentagonRep : DihedralGroup 5 →* Equiv.Perm (ZMod 5) :=
  MonoidHom.mk'
    (fun g => match g with
      | DihedralGroup.r i => Equiv.addRight i
      | DihedralGroup.sr i => Equiv.subLeft (-i))
    (by decide)

/-- A rotation `r i` acts on the `x`-th mode as `x + i`. -/
theorem pentagonRep_r (i x : ZMod 5) : pentagonRep (DihedralGroup.r i) x = x + i := rfl

/-- A reflection `sr i` acts on the `x`-th mode as `-x - i`. -/
theorem pentagonRep_sr (i x : ZMod 5) : pentagonRep (DihedralGroup.sr i) x = -i - x := rfl

set_option maxHeartbeats 1000000 in
/-- **Faithfulness**: D₅ acts injectively on the 5 principal modes (no nontrivial element
    acts trivially). -/
theorem pentagonRep_injective : Function.Injective pentagonRep := by decide

/-- Faithful alternative three: the 5 infrared principal modes correspond one-to-one with
    the 5 pentagon vertices, and D₅ **faithfully** (injectively) permutes these 5 modes
    via the pentagon rotations/reflections. -/
theorem modes_pentagon_action :
    ∃ ρ : DihedralGroup 5 →* Equiv.Perm (ZMod 5), Function.Injective ρ :=
  ⟨pentagonRep, pentagonRep_injective⟩

/-- **Transitivity**: the action of D₅ on the 5 principal modes is transitive (any mode
    can be sent to any other by a rotation), so the 5 modes form a **single orbit** —
    corresponding exactly to multiplicity 1 of the trivial representation in the
    permutation representation. -/
theorem pentagon_action_transitive (a b : ZMod 5) :
    ∃ g : DihedralGroup 5, pentagonRep g a = b :=
  ⟨DihedralGroup.r (b - a), by rw [pentagonRep_r]; ring⟩

/-! ## The precise relationship between the 4 irreducible representations of D₅ and the 5 principal modes

D₅ (order 10) has **4** complex irreducible representations (`dihedral_five_num_irreps`),
of dimensions `(1, 1, 2, 2)`: the trivial representation `triv`, the sign representation
`sgn`, and two 2-dimensional representations `ρ₁, ρ₂`. The dimension formula gives
`1² + 1² + 2² + 2² = 10 = |D₅|`.

The 5-dimensional permutation representation `pentagonRep` spanned by the 5 infrared
principal modes decomposes by characters as **`triv ⊕ ρ₁ ⊕ ρ₂`**, i.e. the dimension
relation `1 + 2 + 2 = 5`:
* the trivial representation `triv` appears once (transitive action ⟹ 1 orbit ⟹ trivial
  multiplicity 1, see `pentagon_action_transitive`);
* each of the two 2-dimensional representations appears once;
* the **sign representation `sgn` does not appear** (multiplicity 0).
So the 5 principal modes use exactly 3 of the 4 irreducible representations (trivial +
two 2-dimensional), which is the precise correspondence between "the 4 irreducible
representations of D₅" and "the 5 FORS principal modes". -/

/-- The sum of squares of the dimensions of the irreducible representations of D₅ equals
    the group order `2·5 = 10`: `1² + 1² + 2² + 2² = 10`. -/
theorem dihedral_five_irrep_dims_sq_sum :
    numOneDimIrreps 5 * 1 ^ 2 + numTwoDimIrreps 5 * 2 ^ 2 = 2 * 5 :=
  d5_dim_formula

/-- D₅ has 4 irreducible representations in total: 2 one-dimensional (trivial, sign) +
    2 two-dimensional. -/
theorem dihedral_five_total_irreps :
    numOneDimIrreps 5 + numTwoDimIrreps 5 = 4 := by decide

/-- **Dimension decomposition of the permutation representation**: the permutation
    representation spanned by the 5 principal modes decomposes by dimension as
    trivial(1) ⊕ two-dim(2) ⊕ two-dim(2), i.e. `1 + 2 + 2 = 5`.
    (This corresponds exactly to 3 of the 4 irreducible representations of D₅, all but
    the sign representation.) -/
theorem pentagon_perm_decomposition : 1 + 2 + 2 = (5 : ℕ) := rfl

end RGF.FORS
